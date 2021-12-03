// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Garbage collector: sweeping

// The sweeper consists of two different algorithms:
//
// * The object reclaimer finds and frees unmarked slots in spans. It
//   can free a whole span if none of the objects are marked, but that
//   isn't its goal. This can be driven either synchronously by
//   mcentral.cacheSpan for mcentral spans, or asynchronously by
//   sweepone from the list of all in-use spans in mheap_.sweepSpans.
//
// * The span reclaimer looks for spans that contain no marked objects
//   and frees whole spans. This is a separate algorithm because
//   freeing whole spans is the hardest task for the object reclaimer,
//   but is critical when allocating new spans. The entry point for
//   this is mheap_.reclaim and it's driven by a sequential scan of
//   the page marks bitmap in the heap arenas.
//
// Both algorithms ultimately call mspan.sweep, which sweeps a single
// heap span.

package runtime

import (
	"runtime/internal/atomic"
	"unsafe"
)

var sweep sweepdata

// State of background sweep.
type sweepdata struct {
	lock    mutex
	g       *g
	parked  bool
	started bool

	nbgsweep    uint32
	npausesweep uint32
}

// finishsweep_m ensures that all spans are swept.
//
// The world must be stopped. This ensures there are no sweeps in
// progress.
//
//go:nowritebarrier
/*
清扫上一轮GC未清扫的span, 确保上一轮GC已完成
*/
func finishsweep_m() {
	// Sweeping must be complete before marking commences, so
	// sweep any unswept spans. If this is a concurrent GC, there
	// shouldn't be any spans left to sweep, so this should finish
	// instantly. If GC was forced before the concurrent sweep
	// finished, there may be spans to sweep.
	// sweepone会取出一个未sweep的span然后执行sweep
	// 详细将在下面sweep阶段时分析
	for sweepone() != ^uintptr(0) {
		sweep.npausesweep++
	}

	// 所有span都sweep完成后, 启动一个新的markbit时代
	// 这个函数是实现span的gcmarkBits和allocBits的分配和复用的关键, 流程如下
	// - span分配gcmarkBits和allocBits
	// - span完成sweep
	//   - 原allocBits不再被使用
	//   - gcmarkBits变为allocBits
	//   - 分配新的gcmarkBits
	// - 开启新的markbit时代
	// - span完成sweep, 同上
	// - 开启新的markbit时代
	//   - 2个时代之前的bitmap将不再被使用, 可以复用这些bitmap
	nextMarkBitArenaEpoch()
}

// 后台清扫任务的函数
func bgsweep(c chan int) {
	sweep.g = getg()

	// 等待唤醒
	lock(&sweep.lock)
	sweep.parked = true
	c <- 1
	goparkunlock(&sweep.lock, waitReasonGCSweepWait, traceEvGoBlock, 1)

	// 循环清扫
	for {
		// 清扫一个span, 然后进入调度(一次只做少量工作)
		for sweepone() != ^uintptr(0) {
			sweep.nbgsweep++
			Gosched()
		}
		// 释放一些未使用的标记队列缓冲区到heap
		for freeSomeWbufs(true) {
			Gosched()
		}
		// 如果清扫未完成则继续循环
		lock(&sweep.lock)
		if !isSweepDone() {
			// This can happen if a GC runs between
			// gosweepone returning ^0 above
			// and the lock being acquired.
			unlock(&sweep.lock)
			continue
		}
		// 否则让后台清扫任务进入休眠, 当前M继续调度
		sweep.parked = true
		goparkunlock(&sweep.lock, waitReasonGCSweepWait, traceEvGoBlock, 1)
	}
}

// sweepone sweeps some unswept heap span and returns the number of pages returned
// to the heap, or ^uintptr(0) if there was nothing to sweep.
// sweepone 清扫的流程
func sweepone() uintptr {
	_g_ := getg()
	sweepRatio := mheap_.sweepPagesPerByte // For debugging

	// increment locks to ensure that the goroutine is not preempted
	// in the middle of sweep thus leaving the span in an inconsistent state for next GC
	// 禁止G被抢占
	_g_.m.locks++
	// 检查是否已经完成了清扫
	if atomic.Load(&mheap_.sweepdone) != 0 {
		_g_.m.locks--
		return ^uintptr(0)
	}
	// 增加清扫的worker数量.更新同时执行sweep的任务数量
	atomic.Xadd(&mheap_.sweepers, +1)

	// Find a span to sweep.
	var s *mspan
	sg := mheap_.sweepgen
	for {
		// 循环获取需要清扫的span
		s = mheap_.sweepSpans[1-sg/2%2].pop()
		// 全部清扫完毕时跳出循环
		if s == nil {
			atomic.Store(&mheap_.sweepdone, 1)
			break
		}
		// 其他M已经在清扫这个span时跳过
		if s.state != mSpanInUse {
			// This can happen if direct sweeping already
			// swept this span, but in that case the sweep
			// generation should always be up-to-date.
			if !(s.sweepgen == sg || s.sweepgen == sg+3) {
				print("runtime: bad span s.state=", s.state, " s.sweepgen=", s.sweepgen, " sweepgen=", sg, "\n")
				throw("non in-use span in unswept list")
			}
			continue
		}
		// sweepgen == h->sweepgen - 2, 表示这个span需要清扫
		// sweepgen == h->sweepgen - 1, 表示这个span正在被清扫
		// 这是里确定span的状态及尝试转换span的状态
		// 原子增加span的sweepgen, 失败表示其他M已经开始清扫这个span, 跳过
		if s.sweepgen == sg-2 && atomic.Cas(&s.sweepgen, sg-2, sg-1) {
			break
		}
	}

	// Sweep the span we found.
	npages := ^uintptr(0)
	if s != nil {
		// 清扫这个span, 然后跳出循环
		npages = s.npages
		// 单个span的清扫
		if s.sweep(false) {
			// Whole span was freed. Count it toward the
			// page reclaimer credit since these pages can
			// now be used for span allocation.
			atomic.Xadduintptr(&mheap_.reclaimCredit, npages)
		} else {
			// Span is still in-use, so this returned no
			// pages to the heap and the span needs to
			// move to the swept in-use list.
			npages = 0
		}
	}

	// Decrement the number of active sweepers and if this is the
	// last one print trace information.
	// 当前worker清扫任务完成，更新同时执行sweep的任务数量
	if atomic.Xadd(&mheap_.sweepers, -1) == 0 && atomic.Load(&mheap_.sweepdone) != 0 {
		if debug.gcpacertrace > 0 {
			print("pacer: sweep done at heap size ", memstats.heap_live>>20, "MB; allocated ", (memstats.heap_live-mheap_.sweepHeapLiveBasis)>>20, "MB during sweep; swept ", mheap_.pagesSwept, " pages at ", sweepRatio, " pages/byte\n")
		}
	}
	// 允许G被抢占
	_g_.m.locks--
	// 返回清扫的页数
	return npages
}

// isSweepDone reports whether all spans are swept or currently being swept.
//
// Note that this condition may transition from false to true at any
// time as the sweeper runs. It may transition from true to false if a
// GC runs; to prevent that the caller must be non-preemptible or must
// somehow block GC progress.
func isSweepDone() bool {
	return mheap_.sweepdone != 0
}

// Returns only when span s has been swept.
//go:nowritebarrier
func (s *mspan) ensureSwept() {
	// Caller must disable preemption.
	// Otherwise when this function returns the span can become unswept again
	// (if GC is triggered on another goroutine).
	_g_ := getg()
	if _g_.m.locks == 0 && _g_.m.mallocing == 0 && _g_ != _g_.m.g0 {
		throw("mspan.ensureSwept: m is not locked")
	}

	sg := mheap_.sweepgen
	spangen := atomic.Load(&s.sweepgen)
	if spangen == sg || spangen == sg+3 {
		return
	}
	// The caller must be sure that the span is a mSpanInUse span.
	if atomic.Cas(&s.sweepgen, sg-2, sg-1) {
		s.sweep(false)
		return
	}
	// unfortunate condition, and we don't have efficient means to wait
	for {
		spangen := atomic.Load(&s.sweepgen)
		if spangen == sg || spangen == sg+3 {
			break
		}
		osyield()
	}
}

// Sweep frees or collects finalizers for blocks not marked in the mark phase.
// It clears the mark bits in preparation for the next GC round.
// Returns true if the span was returned to heap.
// If preserve=true, don't return it to heap nor relink in mcentral lists;
// caller takes care of it.
//TODO go:nowritebarrier
/*
从bgsweep和前面的分配器可以看出扫描阶段的工作是十分懒惰(lazy)的,
实际可能会出现前一阶段的扫描还未完成, 就需要开始新一轮的GC的情况,
所以每一轮GC开始之前都需要完成前一轮GC的扫描工作(Sweep Termination阶段).
*/
// span的sweep函数用于清扫单个span
func (s *mspan) sweep(preserve bool) bool {
	// It's critical that we enter this function with preemption disabled,
	// GC must not start while we are in the middle of this function.
	_g_ := getg()
	if _g_.m.locks == 0 && _g_.m.mallocing == 0 && _g_ != _g_.m.g0 {
		throw("mspan.sweep: m is not locked")
	}
	sweepgen := mheap_.sweepgen
	// 只有正在清扫中状态的span才可以正常执行
	if s.state != mSpanInUse || s.sweepgen != sweepgen-1 {
		print("mspan.sweep: state=", s.state, " sweepgen=", s.sweepgen, " mheap.sweepgen=", sweepgen, "\n")
		throw("mspan.sweep: bad span state")
	}

	if trace.enabled {
		traceGCSweepSpan(s.npages * _PageSize)
	}
	// 先更新清扫的page数
	atomic.Xadd64(&mheap_.pagesSwept, int64(s.npages))

	spc := s.spanclass
	size := s.elemsize
	res := false

	c := _g_.m.mcache
	freeToHeap := false

	// The allocBits indicate which unmarked objects don't need to be
	// processed since they were free at the end of the last GC cycle
	// and were not allocated since then.
	// If the allocBits index is >= s.freeindex and the bit
	// is not marked then the object remains unallocated
	// since the last GC.
	// This situation is analogous to being on a freelist.

	// Unlink & free special records for any objects we're about to free.
	// Two complications here:
	// 1. An object can have both finalizer and profile special records.
	//    In such case we need to queue finalizer for execution,
	//    mark the object as live and preserve the profile special.
	// 2. A tiny object can have several finalizers setup for different offsets.
	//    If such object is not marked, we need to queue all finalizers at once.
	// Both 1 and 2 are possible at the same time.
	// 判断在special中的析构器, 如果对应的对象已经不再存活则标记对象存活防止回收, 然后把析构器移到运行队列
	specialp := &s.specials
	special := *specialp
	// 判断在special中的对象是否存活，是否至少有一个finalizer，释放没有finalizer的对象，把有finalizer的对象组成队列
	for special != nil {
		// A finalizer can be set for an inner byte of an object, find object beginning.
		objIndex := uintptr(special.offset) / size
		p := s.base() + objIndex*size
		mbits := s.markBitsForIndex(objIndex)
		if !mbits.isMarked() {
			// This object is not marked and has at least one special record.
			// Pass 1: see if it has at least one finalizer.
			hasFin := false
			endOffset := p - s.base() + size
			for tmp := special; tmp != nil && uintptr(tmp.offset) < endOffset; tmp = tmp.next {
				if tmp.kind == _KindSpecialFinalizer {
					// Stop freeing of object if it has a finalizer.
					mbits.setMarkedNonAtomic()
					hasFin = true
					break
				}
			}
			// Pass 2: queue all finalizers _or_ handle profile record.
			for special != nil && uintptr(special.offset) < endOffset {
				// Find the exact byte for which the special was setup
				// (as opposed to object beginning).
				p := s.base() + uintptr(special.offset)
				if special.kind == _KindSpecialFinalizer || !hasFin {
					// Splice out special record.
					y := special
					special = special.next
					*specialp = special
					freespecial(y, unsafe.Pointer(p), size)
				} else {
					// This is profile record, but the object has finalizers (so kept alive).
					// Keep special record.
					specialp = &special.next
					special = *specialp
				}
			}
		} else {
			// object is still live: keep special record
			specialp = &special.next
			special = *specialp
		}
	}

	// 除错用
	if debug.allocfreetrace != 0 || debug.clobberfree != 0 || raceenabled || msanenabled {
		// Find all newly freed objects. This doesn't have to
		// efficient; allocfreetrace has massive overhead.
		mbits := s.markBitsForBase()
		abits := s.allocBitsForIndex(0)
		for i := uintptr(0); i < s.nelems; i++ {
			if !mbits.isMarked() && (abits.index < s.freeindex || abits.isMarked()) {
				x := s.base() + i*s.elemsize
				if debug.allocfreetrace != 0 {
					tracefree(unsafe.Pointer(x), size)
				}
				if debug.clobberfree != 0 {
					clobberfree(unsafe.Pointer(x), size)
				}
				if raceenabled {
					racefree(unsafe.Pointer(x), size)
				}
				if msanenabled {
					msanfree(unsafe.Pointer(x), size)
				}
			}
			mbits.advance()
			abits.advance()
		}
	}

	// Count the number of free objects in this span.
	// 获取需要释放的alloc对象的总数.计算释放的对象数量
	nalloc := uint16(s.countAlloc())
	// 如果sizeclass为0，却分配的总数量为0，则释放到mheap
	if spc.sizeclass() == 0 && nalloc == 0 {
		// 如果span的类型是0(大对象)并且其中的对象已经不存活则释放到heap
		s.needzero = 1
		freeToHeap = true
	}
	nfreed := s.allocCount - nalloc
	if nalloc > s.allocCount {
		print("runtime: nelems=", s.nelems, " nalloc=", nalloc, " previous allocCount=", s.allocCount, " nfreed=", nfreed, "\n")
		throw("sweep increased allocation count")
	}

	// 设置新的allocCount
	s.allocCount = nalloc
	// 判断span是否empty.判断span是否无未分配的对象
	wasempty := s.nextFreeIndex() == s.nelems
	// 重置freeindex.下次分配从0开始搜索
	s.freeindex = 0 // reset allocation index to start of span.
	if trace.enabled {
		getg().m.p.ptr().traceReclaimed += uintptr(nfreed) * s.elemsize
	}

	// gcmarkBits becomes the allocBits.
	// get a fresh cleared gcmarkBits in preparation for next GC
	// 重置 allocBits为 gcMarkBits
	// gcmarkBits变为新的allocBits
	// 然后重新分配一块全部为0的gcmarkBits
	// 下次分配对象时可以根据allocBits得知哪些元素是未分配的
	s.allocBits = s.gcmarkBits
	// 重置 gcMarkBits
	s.gcmarkBits = newMarkBits(s.nelems)

	// Initialize alloc bits cache.
	// 更新freeindex开始的allocCache
	s.refillAllocCache(0)

	// We need to set s.sweepgen = h.sweepgen only when all blocks are swept,
	// because of the potential for a concurrent free/SetFinalizer.
	// But we need to set it before we make the span available for allocation
	// (return it to heap or mcentral), because allocation code assumes that a
	// span is already swept if available for allocation.
	// 如果span中已经无存活的对象则更新sweepgen到最新
	// 下面会把span加到mcentral或者mheap
	if freeToHeap || nfreed == 0 {
		// The span must be in our exclusive ownership until we update sweepgen,
		// check for potential races.
		if s.state != mSpanInUse || s.sweepgen != sweepgen-1 {
			print("mspan.sweep: state=", s.state, " sweepgen=", s.sweepgen, " mheap.sweepgen=", sweepgen, "\n")
			throw("mspan.sweep: bad span state after sweep")
		}
		// Serialization point.
		// At this point the mark bits are cleared and allocation ready
		// to go so release the span.
		atomic.Store(&s.sweepgen, sweepgen)
	}

	if nfreed > 0 && spc.sizeclass() != 0 {
		// 把span释放到mcentral上.res等于是否添加成功
		c.local_nsmallfree[spc.sizeclass()] += uintptr(nfreed)
		res = mheap_.central[spc].mcentral.freeSpan(s, preserve, wasempty)
		// mcentral.freeSpan updates sweepgen
		// freeSpan会更新sweepgen
	} else if freeToHeap {
		// 把span释放到mheap
		// Free large span to heap

		// NOTE(rsc,dvyukov): The original implementation of efence
		// in CL 22060046 used sysFree instead of sysFault, so that
		// the operating system would eventually give the memory
		// back to us again, so that an efence program could run
		// longer without running out of memory. Unfortunately,
		// calling sysFree here without any kind of adjustment of the
		// heap data structures means that when the memory does
		// come back to us, we have the wrong metadata for it, either in
		// the mspan structures or in the garbage collection bitmap.
		// Using sysFault here means that the program will run out of
		// memory fairly quickly in efence mode, but at least it won't
		// have mysterious crashes due to confused memory reuse.
		// It should be possible to switch back to sysFree if we also
		// implement and then call some kind of mheap.deleteSpan.
		// 这里是大对象的span释放，与117行呼应.
		if debug.efence > 0 {
			s.limit = 0 // prevent mlookup from finding this span
			sysFault(unsafe.Pointer(s.base()), size)
		} else {
			// 把sapn释放到mheap上
			mheap_.freeSpan(s, true)
		}
		c.local_nlargefree++
		c.local_largefree += size
		res = true
	}
	// 如果span未释放到mcentral或mheap，表示span仍然处于in-use状态
	if !res {
		// The span has been swept and is still in-use, so put
		// it on the swept in-use list.
		// 把仍在使用的span加到sweepSpans的"已清扫"队列中
		mheap_.sweepSpans[sweepgen/2%2].push(s)
	}
	return res
}

// deductSweepCredit deducts sweep credit for allocating a span of
// size spanBytes. This must be performed *before* the span is
// allocated to ensure the system has enough credit. If necessary, it
// performs sweeping to prevent going in to debt. If the caller will
// also sweep pages (e.g., for a large allocation), it can pass a
// non-zero callerSweepPages to leave that many pages unswept.
//
// deductSweepCredit makes a worst-case assumption that all spanBytes
// bytes of the ultimately allocated span will be available for object
// allocation.
//
// deductSweepCredit is the core of the "proportional sweep" system.
// It uses statistics gathered by the garbage collector to perform
// enough sweeping so that all pages are swept during the concurrent
// sweep phase between GC cycles.
//
// mheap_ must NOT be locked.
func deductSweepCredit(spanBytes uintptr, callerSweepPages uintptr) {
	if mheap_.sweepPagesPerByte == 0 {
		// Proportional sweep is done or disabled.
		return
	}

	if trace.enabled {
		traceGCSweepStart()
	}

retry:
	sweptBasis := atomic.Load64(&mheap_.pagesSweptBasis)

	// Fix debt if necessary.
	newHeapLive := uintptr(atomic.Load64(&memstats.heap_live)-mheap_.sweepHeapLiveBasis) + spanBytes
	pagesTarget := int64(mheap_.sweepPagesPerByte*float64(newHeapLive)) - int64(callerSweepPages)
	for pagesTarget > int64(atomic.Load64(&mheap_.pagesSwept)-sweptBasis) {
		if sweepone() == ^uintptr(0) {
			mheap_.sweepPagesPerByte = 0
			break
		}
		if atomic.Load64(&mheap_.pagesSweptBasis) != sweptBasis {
			// Sweep pacing changed. Recompute debt.
			goto retry
		}
	}

	if trace.enabled {
		traceGCSweepDone()
	}
}

// clobberfree sets the memory content at x to bad content, for debugging
// purposes.
func clobberfree(x unsafe.Pointer, size uintptr) {
	// size (span.elemsize) is always a multiple of 4.
	for i := uintptr(0); i < size; i += 4 {
		*(*uint32)(add(x, i)) = 0xdeadbeef
	}
}
