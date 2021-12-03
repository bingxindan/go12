// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Garbage collector: marking and scanning

package runtime

import (
	"runtime/internal/atomic"
	"runtime/internal/sys"
	"unsafe"
)

const (
	// 扫描析构器队列
	fixedRootFinalizers = iota
	fixedRootFreeGStacks
	fixedRootCount

	// rootBlockBytes is the number of bytes to scan per data or
	// BSS root.
	rootBlockBytes = 256 << 10

	// rootBlockSpans is the number of spans to scan per span
	// root.
	rootBlockSpans = 8 * 1024 // 64MB worth of spans

	// maxObletBytes is the maximum bytes of an object to scan at once. 
	// Larger objects will be split up into "oblets" of at most this size. 
	// Since we can scan 1–2 MB/ms, 128 KB bounds scan preemption at ~100 µs.
	// This must be > _MaxSmallSize so that the object base is the span base.
	// MaxObjetBytes是一次要扫描的对象的最大字节数。 较大的对象将被拆分为最多此大小的“小对象”。
	// 因为我们可以扫描1–2 MB/ms，128 KB的边界扫描抢占速度约为100µs。
	// 这必须是 > MaxSmallSize，以便对象基础是跨度基础。
	// 128 << 10 = 131072 == 128KB
	maxObletBytes = 128 << 10

	// drainCheckThreshold specifies how many units of work to do
	// between self-preemption checks in gcDrain. Assuming a scan
	// rate of 1 MB/ms, this is ~100 µs. Lower values have higher
	// overhead in the scan loop (the scheduler check may perform
	// a syscall, so its overhead is nontrivial). Higher values
	// make the system less responsive to incoming work.
	drainCheckThreshold = 100000
)

// gcMarkRootPrepare queues root scanning jobs (stacks, globals, and
// some miscellany) and initializes scanning-related state.
//
// The caller must have call gcCopySpans().
//
// The world must be stopped.
//
//go:nowritebarrier
// 函数会计算扫描根对象的任务数量
func gcMarkRootPrepare() {
	// 释放mcache中的所有span的任务, 只在完成标记阶段(mark termination)中执行
	work.nFlushCacheRoots = 0

	// Compute how many data and BSS root blocks there are.
	// 计算block数量的函数, rootBlockBytes是256KB
	nBlocks := func(bytes uintptr) int {
		return int((bytes + rootBlockBytes - 1) / rootBlockBytes)
	}

	work.nDataRoots = 0
	work.nBSSRoots = 0

	// data和bss每一轮GC只扫描一次
	// 并行GC中会在后台标记任务中扫描, 完成标记阶段(mark termination)中不扫描
	// 非并行GC会在完成标记阶段(mark termination)中扫描

	// Scan globals.
	// 计算扫描可读写的全局变量的任务数量
	for _, datap := range activeModules() {
		nDataRoots := nBlocks(datap.edata - datap.data)
		if nDataRoots > work.nDataRoots {
			work.nDataRoots = nDataRoots
		}
	}

	// 计算扫描只读的全局变量的任务数量
	for _, datap := range activeModules() {
		nBSSRoots := nBlocks(datap.ebss - datap.bss)
		if nBSSRoots > work.nBSSRoots {
			work.nBSSRoots = nBSSRoots
		}
	}

	// Scan span roots for finalizer specials.
	// We depend on addfinalizer to mark objects that get finalizers after root marking.
	// We're only interested in scanning the in-use spans, which will all be swept at this point.
	// More spans may be added to this list during concurrent GC, but we only care about spans that were allocated before this mark phase.
	// 计算扫描span中的finalizer的任务数量
	work.nSpanRoots = mheap_.sweepSpans[mheap_.sweepgen/2%2].numBlocks()

	// Scan stacks.
	//
	// Gs may be created after this point, but it's okay that we
	// ignore them because they begin life without any roots, so
	// there's nothing to scan, and any roots they create during
	// the concurrent phase will be scanned during mark termination.
	// 计算扫描各个G的栈的任务数量
	work.nStackRoots = int(atomic.Loaduintptr(&allglen))

	// 计算总任务数量
	// 后台标记任务会对markrootNext进行原子递增, 来决定做哪个任务
	// 这种用数值来实现锁自由队列的办法挺聪明的, 尽管google工程师觉得不好(看后面markroot函数的分析)
	work.markrootNext = 0
	work.markrootJobs = uint32(fixedRootCount + work.nFlushCacheRoots + work.nDataRoots + work.nBSSRoots + work.nSpanRoots + work.nStackRoots)
}

// gcMarkRootCheck checks that all roots have been scanned. It is
// purely for debugging.
func gcMarkRootCheck() {
	if work.markrootNext < work.markrootJobs {
		print(work.markrootNext, " of ", work.markrootJobs, " markroot jobs done\n")
		throw("left over markroot jobs")
	}

	lock(&allglock)
	// Check that stacks have been scanned.
	var gp *g
	for i := 0; i < work.nStackRoots; i++ {
		gp = allgs[i]
		if !gp.gcscandone {
			goto fail
		}
	}
	unlock(&allglock)
	return

fail:
	println("gp", gp, "goid", gp.goid,
		"status", readgstatus(gp),
		"gcscandone", gp.gcscandone,
		"gcscanvalid", gp.gcscanvalid)
	unlock(&allglock) // Avoid self-deadlock with traceback.
	throw("scan missed a g")
}

// ptrmask for an allocation containing a single pointer.
var oneptrmask = [...]uint8{1}

// markroot scans the i'th root.
// Preemption must be disabled (because this uses a gcWork).
// nowritebarrier is only advisory here.
//go:nowritebarrier
// 用于执行根对象扫描工作
func markroot(gcw *gcWork, i uint32) {
	// TODO(austin): This is a bit ridiculous.
	// Compute and store the bases in gcMarkRootPrepare instead of the counts.
	// 判断取出的数值对应哪种任务
	// 计算并存储gcMarkRootPrepare中的基数，而不是计数。
	baseFlushCache := uint32(fixedRootCount)
	baseData := baseFlushCache + uint32(work.nFlushCacheRoots)
	baseBSS := baseData + uint32(work.nDataRoots)
	baseSpans := baseBSS + uint32(work.nBSSRoots)
	baseStacks := baseSpans + uint32(work.nSpanRoots)
	end := baseStacks + uint32(work.nStackRoots)

	// Note: if you add a case here, please also update heapdump.go:dumproots.
	switch {
	// 释放mcache中的所有span, 要求STW
	case baseFlushCache <= i && i < baseData:
		// 归还span，释放堆的栈内存
		flushmcache(int(i - baseFlushCache))

	// 这里只会扫描i对应的block, 扫描时传入包含哪里有指针的bitmap数据
	case baseData <= i && i < baseBSS:
		// 扫描可读写的全局变量
		for _, datap := range activeModules() {
			markrootBlock(datap.data, datap.edata-datap.data, datap.gcdatamask.bytedata, gcw, int(i-baseData))
		}

	// 这里只会扫描i对应的block, 扫描时传入包含哪里有指针的bitmap数据
	case baseBSS <= i && i < baseSpans:
		// 扫描只读的全局队列
		for _, datap := range activeModules() {
			markrootBlock(datap.bss, datap.ebss-datap.bss, datap.gcbssmask.bytedata, gcw, int(i-baseBSS))
		}

	case i == fixedRootFinalizers:
		// 扫描Finalizer队列，扫描析构器队列
		for fb := allfin; fb != nil; fb = fb.alllink {
			cnt := uintptr(atomic.Load(&fb.cnt))
			scanblock(uintptr(unsafe.Pointer(&fb.fin[0])), cnt*unsafe.Sizeof(fb.fin[0]), &finptrmask[0], gcw, nil)
		}

	case i == fixedRootFreeGStacks:
		// Switch to the system stack so we can call stackfree.
		// 释放已经终止的stack
		// 已中止的G的栈(_Gdead), 但不会释放已缓存中的G, 这里指的是 sched.gFree.stack 中的g, 非 sched.gFree.noStack 列表
		systemstack(markrootFreeGStacks)

	case baseSpans <= i && i < baseStacks:
		// mark mspan.specials
		// 扫描MSpan.specials
		markrootSpans(gcw, int(i-baseSpans))

	default:
		// the rest is scanning goroutine stacks
		// 获取需要扫描的g
		var gp *g
		if baseStacks <= i && i < end {
			gp = allgs[i-baseStacks]
		} else {
			throw("markroot: bad index")
		}

		// remember when we've first observed the G blocked
		// needed only to output in traceback
		status := readgstatus(gp) // We are not in a scan state
		if (status == _Gwaiting || status == _Gsyscall) && gp.waitsince == 0 {
			gp.waitsince = work.tstart
		}

		// scang must be done on the system stack in case
		// we're trying to scan our own stack.
		// 转交给g0进行扫描
		systemstack(func() {
			// If this is a self-scan, put the user G in
			// _Gwaiting to prevent self-deadlock. It may
			// already be in _Gwaiting if this is a mark
			// worker or we're in mark termination.
			userG := getg().m.curg
			selfScan := gp == userG && readgstatus(userG) == _Grunning
			// 如果是扫描自己的，则转换自己的g的状态
			if selfScan {
				casgstatus(userG, _Grunning, _Gwaiting)
				userG.waitreason = waitReasonGarbageCollectionScan
			}

			// TODO: scang blocks until gp's stack has been scanned, which may take a while for running goroutines. 
			// Consider doing this in two phases where the first is non-blocking:
			// we scan the stacks we can and ask running goroutines to scan themselves; and the second blocks.
			// 扫描g的栈
			scang(gp, gcw)

			// 如果正在扫描自己的栈则把状态切换回运行中
			if selfScan {
				casgstatus(userG, _Gwaiting, _Grunning)
			}
		})
	}
}

// markrootBlock scans the shard'th shard of the block of memory [b0, b0+n0), with the given pointer mask.
// markrootBlock使用给定的指针掩码扫描内存块[b0，b0+n0]的第个碎片。
//
//go:nowritebarrier
// 根据 ptrmask0，来扫描[b0, b0+n0)区域
func markrootBlock(b0, n0 uintptr, ptrmask0 *uint8, gcw *gcWork, shard int) {
	if rootBlockBytes%(8*sys.PtrSize) != 0 {
		// This is necessary to pick byte offsets in ptrmask0.
		throw("rootBlockBytes must be a multiple of 8*ptrSize")
	}

	// 如果需扫描的block区域，超出b0+n0的区域，直接返回
	b := b0 + uintptr(shard)*rootBlockBytes
	if b >= b0+n0 {
		return
	}
	ptrmask := (*uint8)(add(unsafe.Pointer(ptrmask0), uintptr(shard)*(rootBlockBytes/(8*sys.PtrSize))))
	n := uintptr(rootBlockBytes)
	if b+n > b0+n0 {
		n = b0 + n0 - b
	}

	// Scan this shard.
	// 扫描给定block的shard
	scanblock(b, n, ptrmask, gcw, nil)
}

// markrootFreeGStacks frees stacks of dead Gs.
//
// This does not free stacks of dead Gs cached on Ps, but having a few
// cached stacks around isn't a problem.
//
//TODO go:nowritebarrier
/*
收缩栈是在mgcmark.go中触发的，主要是在scanstack和markrootFreeGStacks函数中，也就是垃圾回收的时候会根据情况收缩栈
shrinkstack 收缩栈在必要的时候：
1、如果这个g是Gdead状态，则会释放栈空间
2、如果已经使用的栈空间大于总栈空间的1/4，则不进行栈收缩，如果是在正在进行系统调用也不能进行栈缩放，因为system使用的参数可能在栈上面。
3、缩小栈的空间为原来的一半

在系统栈调用函数 markrootFreeGStacks()，释放所有包含stack的G，然后再将这些G放在 noStack 的空闲列表中。
*/
func markrootFreeGStacks() {
	// Take list of dead Gs with stacks.
	// 调度器中包含栈的全局空闲g列表
	lock(&sched.gFree.lock)
	list := sched.gFree.stack
	sched.gFree.stack = gList{}
	unlock(&sched.gFree.lock)
	if list.empty() {
		return
	}

	// Free stacks.
	// 从head遍历gList,调用 shrinkstack() 函数释放g的stacks信息,直到处理完所有g
	q := gQueue{list.head, list.head}
	for gp := list.head.ptr(); gp != nil; gp = gp.schedlink.ptr() {
		shrinkstack(gp)
		// Manipulate the queue directly since the Gs are
		// already all linked the right way.
		q.tail.set(gp)
	}

	// Put Gs back on the free list.
	// 将原来包含statck的g放到 noStack 的 g 空闲队列中
	lock(&sched.gFree.lock)
	sched.gFree.noStack.pushAll(q)
	unlock(&sched.gFree.lock)
}

// markrootSpans marks roots for one shard of work.spans.
//
//go:nowritebarrier
func markrootSpans(gcw *gcWork, shard int) {
	// Objects with finalizers have two GC-related invariants:
	//
	// 1) Everything reachable from the object must be marked.
	// This ensures that when we pass the object to its finalizer,
	// everything the finalizer can reach will be retained.
	//
	// 2) Finalizer specials (which are not in the garbage
	// collected heap) are roots. In practice, this means the fn
	// field must be scanned.
	//
	// TODO(austin): There are several ideas for making this more
	// efficient in issue #11485.

	sg := mheap_.sweepgen
	spans := mheap_.sweepSpans[mheap_.sweepgen/2%2].block(shard)
	// Note that work.spans may not include spans that were
	// allocated between entering the scan phase and now. This is
	// okay because any objects with finalizers in those spans
	// must have been allocated and given finalizers after we
	// entered the scan phase, so addfinalizer will have ensured
	// the above invariants for them.
	for _, s := range spans {
		if s.state != mSpanInUse {
			continue
		}
		// Check that this span was swept (it may be cached or uncached).
		if !useCheckmark && !(s.sweepgen == sg || s.sweepgen == sg+3) {
			// sweepgen was updated (+2) during non-checkmark GC pass
			print("sweep ", s.sweepgen, " ", sg, "\n")
			throw("gc: unswept span")
		}

		// Speculatively check if there are any specials
		// without acquiring the span lock. This may race with
		// adding the first special to a span, but in that
		// case addfinalizer will observe that the GC is
		// active (which is globally synchronized) and ensure
		// the above invariants. We may also ensure the
		// invariants, but it's okay to scan an object twice.
		if s.specials == nil {
			continue
		}

		// Lock the specials to prevent a special from being
		// removed from the list while we're traversing it.
		lock(&s.speciallock)

		for sp := s.specials; sp != nil; sp = sp.next {
			if sp.kind != _KindSpecialFinalizer {
				continue
			}
			// don't mark finalized object, but scan it so we
			// retain everything it points to.
			spf := (*specialfinalizer)(unsafe.Pointer(sp))
			// A finalizer can be set for an inner byte of an object, find object beginning.
			p := s.base() + uintptr(spf.special.offset)/s.elemsize*s.elemsize

			// Mark everything that can be reached from
			// the object (but *not* the object itself or
			// we'll never collect it).
			scanobject(p, gcw)

			// The special itself is a root.
			scanblock(uintptr(unsafe.Pointer(&spf.fn)), sys.PtrSize, &oneptrmask[0], gcw, nil)
		}

		unlock(&s.speciallock)
	}
}

// gcAssistAlloc performs GC work to make gp's assist debt positive.
// gp must be the calling user gorountine.
//
// This must be called with preemption enabled.
func gcAssistAlloc(gp *g) {
	// Don't assist in non-preemptible contexts. These are
	// generally fragile and won't allow the assist to block.
	if getg() == gp.m.g0 {
		return
	}
	if mp := getg().m; mp.locks > 0 || mp.preemptoff != "" {
		return
	}

	traced := false
retry:
	// Compute the amount of scan work we need to do to make the
	// balance positive. When the required amount of work is low,
	// we over-assist to build up credit for future allocations
	// and amortize the cost of assisting.
	debtBytes := -gp.gcAssistBytes
	scanWork := int64(gcController.assistWorkPerByte * float64(debtBytes))
	if scanWork < gcOverAssistWork {
		scanWork = gcOverAssistWork
		debtBytes = int64(gcController.assistBytesPerWork * float64(scanWork))
	}

	// Steal as much credit as we can from the background GC's
	// scan credit. This is racy and may drop the background
	// credit below 0 if two mutators steal at the same time. This
	// will just cause steals to fail until credit is accumulated
	// again, so in the long run it doesn't really matter, but we
	// do have to handle the negative credit case.
	bgScanCredit := atomic.Loadint64(&gcController.bgScanCredit)
	stolen := int64(0)
	if bgScanCredit > 0 {
		if bgScanCredit < scanWork {
			stolen = bgScanCredit
			gp.gcAssistBytes += 1 + int64(gcController.assistBytesPerWork*float64(stolen))
		} else {
			stolen = scanWork
			gp.gcAssistBytes += debtBytes
		}
		atomic.Xaddint64(&gcController.bgScanCredit, -stolen)

		scanWork -= stolen

		if scanWork == 0 {
			// We were able to steal all of the credit we
			// needed.
			if traced {
				traceGCMarkAssistDone()
			}
			return
		}
	}

	if trace.enabled && !traced {
		traced = true
		traceGCMarkAssistStart()
	}

	// Perform assist work
	systemstack(func() {
		gcAssistAlloc1(gp, scanWork)
		// The user stack may have moved, so this can't touch
		// anything on it until it returns from systemstack.
	})

	completed := gp.param != nil
	gp.param = nil
	if completed {
		gcMarkDone()
	}

	if gp.gcAssistBytes < 0 {
		// We were unable steal enough credit or perform
		// enough work to pay off the assist debt. We need to
		// do one of these before letting the mutator allocate
		// more to prevent over-allocation.
		//
		// If this is because we were preempted, reschedule
		// and try some more.
		if gp.preempt {
			Gosched()
			goto retry
		}

		// Add this G to an assist queue and park. When the GC
		// has more background credit, it will satisfy queued
		// assists before flushing to the global credit pool.
		//
		// Note that this does *not* get woken up when more
		// work is added to the work list. The theory is that
		// there wasn't enough work to do anyway, so we might
		// as well let background marking take care of the
		// work that is available.
		if !gcParkAssist() {
			goto retry
		}

		// At this point either background GC has satisfied
		// this G's assist debt, or the GC cycle is over.
	}
	if traced {
		traceGCMarkAssistDone()
	}
}

// gcAssistAlloc1 is the part of gcAssistAlloc that runs on the system
// stack. This is a separate function to make it easier to see that
// we're not capturing anything from the user stack, since the user
// stack may move while we're in this function.
//
// gcAssistAlloc1 indicates whether this assist completed the mark
// phase by setting gp.param to non-nil. This can't be communicated on
// the stack since it may move.
//
//go:systemstack
func gcAssistAlloc1(gp *g, scanWork int64) {
	// Clear the flag indicating that this assist completed the
	// mark phase.
	gp.param = nil

	if atomic.Load(&gcBlackenEnabled) == 0 {
		// The gcBlackenEnabled check in malloc races with the
		// store that clears it but an atomic check in every malloc
		// would be a performance hit.
		// Instead we recheck it here on the non-preemptable system
		// stack to determine if we should perform an assist.

		// GC is done, so ignore any remaining debt.
		gp.gcAssistBytes = 0
		return
	}
	// Track time spent in this assist. Since we're on the
	// system stack, this is non-preemptible, so we can
	// just measure start and end time.
	startTime := nanotime()

	decnwait := atomic.Xadd(&work.nwait, -1)
	if decnwait == work.nproc {
		println("runtime: work.nwait =", decnwait, "work.nproc=", work.nproc)
		throw("nwait > work.nprocs")
	}

	// gcDrainN requires the caller to be preemptible.
	casgstatus(gp, _Grunning, _Gwaiting)
	gp.waitreason = waitReasonGCAssistMarking

	// drain own cached work first in the hopes that it
	// will be more cache friendly.
	gcw := &getg().m.p.ptr().gcw
	workDone := gcDrainN(gcw, scanWork)

	casgstatus(gp, _Gwaiting, _Grunning)

	// Record that we did this much scan work.
	//
	// Back out the number of bytes of assist credit that
	// this scan work counts for. The "1+" is a poor man's
	// round-up, to ensure this adds credit even if
	// assistBytesPerWork is very low.
	gp.gcAssistBytes += 1 + int64(gcController.assistBytesPerWork*float64(workDone))

	// If this is the last worker and we ran out of work,
	// signal a completion point.
	incnwait := atomic.Xadd(&work.nwait, +1)
	if incnwait > work.nproc {
		println("runtime: work.nwait=", incnwait,
			"work.nproc=", work.nproc)
		throw("work.nwait > work.nproc")
	}

	if incnwait == work.nproc && !gcMarkWorkAvailable(nil) {
		// This has reached a background completion point. Set
		// gp.param to a non-nil value to indicate this. It
		// doesn't matter what we set it to (it just has to be
		// a valid pointer).
		gp.param = unsafe.Pointer(gp)
	}
	duration := nanotime() - startTime
	_p_ := gp.m.p.ptr()
	_p_.gcAssistTime += duration
	if _p_.gcAssistTime > gcAssistTimeSlack {
		atomic.Xaddint64(&gcController.assistTime, _p_.gcAssistTime)
		_p_.gcAssistTime = 0
	}
}

// gcWakeAllAssists wakes all currently blocked assists. This is used
// at the end of a GC cycle. gcBlackenEnabled must be false to prevent
// new assists from going to sleep after this point.
func gcWakeAllAssists() {
	lock(&work.assistQueue.lock)
	list := work.assistQueue.q.popList()
	injectglist(&list)
	unlock(&work.assistQueue.lock)
}

// gcParkAssist puts the current goroutine on the assist queue and parks.
//
// gcParkAssist reports whether the assist is now satisfied. If it
// returns false, the caller must retry the assist.
//
//go:nowritebarrier
func gcParkAssist() bool {
	lock(&work.assistQueue.lock)
	// If the GC cycle finished while we were getting the lock,
	// exit the assist. The cycle can't finish while we hold the
	// lock.
	if atomic.Load(&gcBlackenEnabled) == 0 {
		unlock(&work.assistQueue.lock)
		return true
	}

	gp := getg()
	oldList := work.assistQueue.q
	work.assistQueue.q.pushBack(gp)

	// Recheck for background credit now that this G is in
	// the queue, but can still back out. This avoids a
	// race in case background marking has flushed more
	// credit since we checked above.
	if atomic.Loadint64(&gcController.bgScanCredit) > 0 {
		work.assistQueue.q = oldList
		if oldList.tail != 0 {
			oldList.tail.ptr().schedlink.set(nil)
		}
		unlock(&work.assistQueue.lock)
		return false
	}
	// Park.
	goparkunlock(&work.assistQueue.lock, waitReasonGCAssistWait, traceEvGoBlockGC, 2)
	return true
}

// gcFlushBgCredit flushes scanWork units of background scan work
// credit. This first satisfies blocked assists on the
// work.assistQueue and then flushes any remaining credit to
// gcController.bgScanCredit.
//
// Write barriers are disallowed because this is used by gcDrain after
// it has ensured that all work is drained and this must preserve that
// condition.
//
//go:nowritebarrierrec
func gcFlushBgCredit(scanWork int64) {
	if work.assistQueue.q.empty() {
		// Fast path; there are no blocked assists. There's a
		// small window here where an assist may add itself to
		// the blocked queue and park. If that happens, we'll
		// just get it on the next flush.
		atomic.Xaddint64(&gcController.bgScanCredit, scanWork)
		return
	}

	scanBytes := int64(float64(scanWork) * gcController.assistBytesPerWork)

	lock(&work.assistQueue.lock)
	for !work.assistQueue.q.empty() && scanBytes > 0 {
		gp := work.assistQueue.q.pop()
		// Note that gp.gcAssistBytes is negative because gp
		// is in debt. Think carefully about the signs below.
		if scanBytes+gp.gcAssistBytes >= 0 {
			// Satisfy this entire assist debt.
			scanBytes += gp.gcAssistBytes
			gp.gcAssistBytes = 0
			// It's important that we *not* put gp in
			// runnext. Otherwise, it's possible for user
			// code to exploit the GC worker's high
			// scheduler priority to get itself always run
			// before other goroutines and always in the
			// fresh quantum started by GC.
			ready(gp, 0, false)
		} else {
			// Partially satisfy this assist.
			gp.gcAssistBytes += scanBytes
			scanBytes = 0
			// As a heuristic, we move this assist to the
			// back of the queue so that large assists
			// can't clog up the assist queue and
			// substantially delay small assists.
			work.assistQueue.q.pushBack(gp)
			break
		}
	}

	if scanBytes > 0 {
		// Convert from scan bytes back to work.
		scanWork = int64(float64(scanBytes) * gcController.assistWorkPerByte)
		atomic.Xaddint64(&gcController.bgScanCredit, scanWork)
	}
	unlock(&work.assistQueue.lock)
}

// scanstack scans gp's stack, greying all pointers found on the stack.
//
// scanstack is marked go:systemstack because it must not be preempted
// while using a workbuf.
//
//go:nowritebarrier
//go:systemstack
// 设置preemptscan后, 在抢占G成功时会调用scanstack扫描它自己的栈, 具体代码在这里.
// 扫描栈用的函数
func scanstack(gp *g, gcw *gcWork) {
	if gp.gcscanvalid {
		return
	}

	if readgstatus(gp)&_Gscan == 0 {
		print("runtime:scanstack: gp=", gp, ", goid=", gp.goid, ", gp->atomicstatus=", hex(readgstatus(gp)), "\n")
		throw("scanstack - bad status")
	}

	switch readgstatus(gp) &^ _Gscan {
	default:
		print("runtime: gp=", gp, ", goid=", gp.goid, ", gp->atomicstatus=", readgstatus(gp), "\n")
		throw("mark - bad status")
	case _Gdead:
		return
	case _Grunning:
		print("runtime: gp=", gp, ", goid=", gp.goid, ", gp->atomicstatus=", readgstatus(gp), "\n")
		throw("scanstack: goroutine not stopped")
	case _Grunnable, _Gsyscall, _Gwaiting:
		// ok
	}

	if gp == getg() {
		throw("can't scan our own stack")
	}

	// Shrink the stack if not much of it is being used.
	shrinkstack(gp)

	var state stackScanState
	state.stack = gp.stack

	if stackTraceDebug {
		println("stack trace goroutine", gp.goid)
	}

	// Scan the saved context register. This is effectively a live
	// register that gets moved back and forth between the
	// register and sched.ctxt without a write barrier.
	if gp.sched.ctxt != nil {
		scanblock(uintptr(unsafe.Pointer(&gp.sched.ctxt)), sys.PtrSize, &oneptrmask[0], gcw, &state)
	}

	// Scan the stack. Accumulate a list of stack objects.
	scanframe := func(frame *stkframe, unused unsafe.Pointer) bool {
		// scanframeworker会根据代码地址(pc)获取函数信息
		// 然后找到函数信息中的stackmap.bytedata, 它保存了函数的栈上哪些地方有指针
		// 再调用scanblock来扫描函数的栈空间, 同时函数的参数也会这样扫描
		scanframeworker(frame, &state, gcw)
		return true
	}
	// 枚举所有调用帧, 分别调用scanframe函数
	gentraceback(^uintptr(0), ^uintptr(0), 0, gp, 0, nil, 0x7fffffff, scanframe, nil, 0)

	// Find additional pointers that point into the stack from the heap.
	// Currently this includes defers and panics. See also function copystack.
	// 枚举所有defer的调用帧, 分别调用scanframe函数
	tracebackdefers(gp, scanframe, nil)
	for d := gp._defer; d != nil; d = d.link {
		// tracebackdefers above does not scan the func value, which could
		// be a stack allocated closure. See issue 30453.
		if d.fn != nil {
			scanblock(uintptr(unsafe.Pointer(&d.fn)), sys.PtrSize, &oneptrmask[0], gcw, &state)
		}
	}
	if gp._panic != nil {
		state.putPtr(uintptr(unsafe.Pointer(gp._panic)))
	}

	// Find and scan all reachable stack objects.
	state.buildIndex()
	for {
		p := state.getPtr()
		if p == 0 {
			break
		}
		obj := state.findObject(p)
		if obj == nil {
			continue
		}
		t := obj.typ
		if t == nil {
			// We've already scanned this object.
			continue
		}
		obj.setType(nil) // Don't scan it again.
		if stackTraceDebug {
			println("  live stkobj at", hex(state.stack.lo+uintptr(obj.off)), "of type", t.string())
		}
		gcdata := t.gcdata
		var s *mspan
		if t.kind&kindGCProg != 0 {
			// This path is pretty unlikely, an object large enough
			// to have a GC program allocated on the stack.
			// We need some space to unpack the program into a straight
			// bitmask, which we allocate/free here.
			// TODO: it would be nice if there were a way to run a GC
			// program without having to store all its bits. We'd have
			// to change from a Lempel-Ziv style program to something else.
			// Or we can forbid putting objects on stacks if they require
			// a gc program (see issue 27447).
			s = materializeGCProg(t.ptrdata, gcdata)
			gcdata = (*byte)(unsafe.Pointer(s.startAddr))
		}

		scanblock(state.stack.lo+uintptr(obj.off), t.ptrdata, gcdata, gcw, &state)

		if s != nil {
			dematerializeGCProg(s)
		}
	}

	// Deallocate object buffers.
	// (Pointer buffers were all deallocated in the loop above.)
	for state.head != nil {
		x := state.head
		state.head = x.next
		if stackTraceDebug {
			for _, obj := range x.obj[:x.nobj] {
				if obj.typ == nil { // reachable
					continue
				}
				println("  dead stkobj at", hex(gp.stack.lo+uintptr(obj.off)), "of type", obj.typ.string())
				// Note: not necessarily really dead - only reachable-from-ptr dead.
			}
		}
		x.nobj = 0
		putempty((*workbuf)(unsafe.Pointer(x)))
	}
	if state.buf != nil || state.freeBuf != nil {
		throw("remaining pointer buffers")
	}

	gp.gcscanvalid = true
}

// Scan a stack frame: local variables and function arguments/results.
//go:nowritebarrier
func scanframeworker(frame *stkframe, state *stackScanState, gcw *gcWork) {
	if _DebugGC > 1 && frame.continpc != 0 {
		print("scanframe ", funcname(frame.fn), "\n")
	}

	locals, args, objs := getStackMap(frame, &state.cache, false)

	// Scan local variables if stack frame has been allocated.
	if locals.n > 0 {
		size := uintptr(locals.n) * sys.PtrSize
		scanblock(frame.varp-size, size, locals.bytedata, gcw, state)
	}

	// Scan arguments.
	if args.n > 0 {
		scanblock(frame.argp, uintptr(args.n)*sys.PtrSize, args.bytedata, gcw, state)
	}

	// Add all stack objects to the stack object list.
	if frame.varp != 0 {
		// varp is 0 for defers, where there are no locals.
		// In that case, there can't be a pointer to its args, either.
		// (And all args would be scanned above anyway.)
		for _, obj := range objs {
			off := obj.off
			base := frame.varp // locals base pointer
			if off >= 0 {
				base = frame.argp // arguments and return values base pointer
			}
			ptr := base + uintptr(off)
			if ptr < frame.sp {
				// object hasn't been allocated in the frame yet.
				continue
			}
			if stackTraceDebug {
				println("stkobj at", hex(ptr), "of type", obj.typ.string())
			}
			state.addObject(ptr, obj.typ)
		}
	}
}

type gcDrainFlags int

const (
	gcDrainUntilPreempt gcDrainFlags = 1 << iota
	gcDrainFlushBgCredit
	gcDrainIdle
	gcDrainFractional
)

// gcDrain scans roots and objects in work buffers, blackening grey objects until it is unable to get more work. It may return before
// GC is done; it's the caller's responsibility to balance work from
// other Ps.
//
// If flags&gcDrainUntilPreempt != 0, gcDrain returns when g.preempt
// is set.
//
// If flags&gcDrainIdle != 0, gcDrain returns when there is other work
// to do.
//
// If flags&gcDrainFractional != 0, gcDrain self-preempts when
// pollFractionalWorkerExit() returns true. This implies
// gcDrainNoBlock.
//
// If flags&gcDrainFlushBgCredit != 0, gcDrain flushes scan work
// credit to gcController.bgScanCredit every gcCreditSlack units of
// scan work.
//
//go:nowritebarrier
// 用于执行标记
func gcDrain(gcw *gcWork, flags gcDrainFlags) {
	if !writeBarrier.needed {
		throw("gcDrain phase incorrect")
	}

	gp := getg().m.curg
	// 看到抢占标志时是否要返回。当 G 被抢占时返回；
	preemptible := flags&gcDrainUntilPreempt != 0
	// 是否计算后台的扫描量来减少协助线程和唤醒等待中的G。
	flushBgCredit := flags&gcDrainFlushBgCredit != 0
	// 是否只执行一定量的工作。调用 runtime.pollWork，当 P 上包含其他待执行 G 时返回；
	idle := flags&gcDrainIdle != 0
	// 记录初始的已扫描数量
	initScanWork := gcw.scanWork

	// checkWork is the scan work before performing the next self-preempt check.
	// checkWork是执行下一次自抢占检查之前的扫描工作。
	checkWork := int64(1<<63 - 1)
	/*
	设置完 check 变量后就可以执行 runtime.markroot进行根对象扫描，每次扫描完毕都会调用 check 函数校验是否应该退出标记任务，
	如果是那么就跳到 done 代码块中退出标记。
	*/
	var check func() bool
	if flags&(gcDrainIdle|gcDrainFractional) != 0 {
		// drainCheckThreshold 默认 100000
		checkWork = initScanWork + drainCheckThreshold
		if idle {
			check = pollWork
		} else if flags&gcDrainFractional != 0 {
			// 调用 runtime.pollFractionalWorkerExit，当 CPU 的占用率超过 fractionalUtilizationGoal 的 20% 时返回；
			check = pollFractionalWorkerExit
		}
	}

	// Drain root marking jobs.
	// 如果根对象未扫描完, 则先扫描根对象
	if work.markrootNext < work.markrootJobs {
		// 一直循环直到被抢占或 STW
		for !(preemptible && gp.preempt) {
			// 从根对象扫描队列取出一个值
			job := atomic.Xadd(&work.markrootNext, +1) - 1
			if job >= work.markrootJobs {
				break
			}
			// 执行根对象扫描工作
			markroot(gcw, job)
			if check != nil && check() {
				goto done
			}
		}
	}

	// Drain heap marking jobs.
	// 排出堆标记作业。

	// 根对象已经在标记队列中, 消费标记队列
	// 一直循环直到被抢占或 STW
	for !(preemptible && gp.preempt) {
		// Try to keep work available on the global queue. We used to
		// check if there were waiting workers, but it's better to
		// just keep work available than to make workers wait. In the
		// worst case, we'll do O(log(_WorkbufSize)) unnecessary balances.
		// 将本地一部分工作放回全局队列中
		if work.full == 0 {
			gcw.balance()
		}

		// 获取任务，先从wbuf1取，没有在从wbuf2取
		b := gcw.tryGetFast()
		if b == 0 {
			// 从wbuf2取
			b = gcw.tryGet()
			if b == 0 {
				// Flush the write barrier buffer; this may create more work.
				// 刷新写屏障缓冲区；这可能会产生更多的工作。
				wbBufFlush(nil, 0)
				b = gcw.tryGet()
			}
		}
		// 获取不到对象, 标记队列已为空, 跳出循环
		if b == 0 {
			// Unable to get work.
			break
		}
		// 扫描获取到的对象
		scanobject(b, gcw)

		// Flush background scan work credit to the global
		// account if we've accumulated enough locally so
		// mutator assists can draw on it.
		// 如果已经扫描了一定数量的对象，gcCreditSlack值是2000
		if gcw.scanWork >= gcCreditSlack {
			// 把扫描的对象数量添加到全局
			atomic.Xaddint64(&gcController.scanWork, gcw.scanWork)
			if flushBgCredit {
				// 记录这次扫描的内存字节数用于减少辅助标记的工作量
				gcFlushBgCredit(gcw.scanWork - initScanWork)
				initScanWork = 0
			}
			checkWork -= gcw.scanWork
			gcw.scanWork = 0

			if checkWork <= 0 {
				checkWork += drainCheckThreshold
				if check != nil && check() {
					break
				}
			}
		}
	}

done:
	// Flush remaining scan work credit.
	// 把扫描的对象数量添加到全局
	if gcw.scanWork > 0 {
		atomic.Xaddint64(&gcController.scanWork, gcw.scanWork)
		if flushBgCredit {
			// 记录这次扫描的内存字节数用于减少辅助标记的工作量
			gcFlushBgCredit(gcw.scanWork - initScanWork)
		}
		gcw.scanWork = 0
	}
}

// gcDrainN blackens grey objects until it has performed roughly
// scanWork units of scan work or the G is preempted. This is
// best-effort, so it may perform less work if it fails to get a work
// buffer. Otherwise, it will perform at least n units of work, but
// may perform more because scanning is always done in whole object
// increments. It returns the amount of scan work performed.
//
// The caller goroutine must be in a preemptible state (e.g.,
// _Gwaiting) to prevent deadlocks during stack scanning. As a
// consequence, this must be called on the system stack.
//
//go:nowritebarrier
//go:systemstack
func gcDrainN(gcw *gcWork, scanWork int64) int64 {
	if !writeBarrier.needed {
		throw("gcDrainN phase incorrect")
	}

	// There may already be scan work on the gcw, which we don't
	// want to claim was done by this call.
	workFlushed := -gcw.scanWork

	gp := getg().m.curg
	for !gp.preempt && workFlushed+gcw.scanWork < scanWork {
		// See gcDrain comment.
		if work.full == 0 {
			gcw.balance()
		}

		// This might be a good place to add prefetch code...
		// if(wbuf.nobj > 4) {
		//         PREFETCH(wbuf->obj[wbuf.nobj - 3];
		//  }
		//
		b := gcw.tryGetFast()
		if b == 0 {
			b = gcw.tryGet()
			if b == 0 {
				// Flush the write barrier buffer;
				// this may create more work.
				wbBufFlush(nil, 0)
				b = gcw.tryGet()
			}
		}

		if b == 0 {
			// Try to do a root job.
			//
			// TODO: Assists should get credit for this
			// work.
			if work.markrootNext < work.markrootJobs {
				job := atomic.Xadd(&work.markrootNext, +1) - 1
				if job < work.markrootJobs {
					markroot(gcw, job)
					continue
				}
			}
			// No heap or root jobs.
			break
		}
		scanobject(b, gcw)

		// Flush background scan work credit.
		if gcw.scanWork >= gcCreditSlack {
			atomic.Xaddint64(&gcController.scanWork, gcw.scanWork)
			workFlushed += gcw.scanWork
			gcw.scanWork = 0
		}
	}

	// Unlike gcDrain, there's no need to flush remaining work
	// here because this never flushes to bgScanCredit and
	// gcw.dispose will flush any remaining work to scanWork.

	return workFlushed + gcw.scanWork
}

// scanblock scans b as scanobject would, but using an explicit
// pointer bitmap instead of the heap bitmap.
//
// This is used to scan non-heap roots, so it does not update
// gcw.bytesMarked or gcw.scanWork.
//
// If stk != nil, possible stack pointers are also reported to stk.putPtr.
//go:nowritebarrier
// 扫描给定block的shard
// 函数是一个通用的扫描函数, 扫描全局变量和栈空间都会用它, 和scanobject不同的是bitmap需要手动传入
func scanblock(b0, n0 uintptr, ptrmask *uint8, gcw *gcWork, stk *stackScanState) {
	// Use local copies of original parameters, so that a stack trace
	// due to one of the throws below shows the original block
	// base and extent.
	b := b0
	n := n0

	// 枚举扫描的地址
	for i := uintptr(0); i < n; {
		// Find bits for the next word.
		// 找到bitmap中对应的bits
		bits := uint32(*addb(ptrmask, i/(sys.PtrSize*8)))
		if bits == 0 {
			i += sys.PtrSize * 8
			continue
		}
		// 枚举byte
		for j := 0; j < 8 && i < n; j++ {
			if bits&1 != 0 {
				// Same work as in scanobject; see comments there.
				// 如果该地址包含指针。标记在该地址的对象存活, 并把它加到标记队列(该对象变为灰色)
				p := *(*uintptr)(unsafe.Pointer(b + i))
				if p != 0 {
					// 如果该地址下找到了对应的对象，标灰
					// 找到该对象对应的span和bitmap
					if obj, span, objIndex := findObject(p, b, i); obj != 0 {
						// 标记一个对象存活, 并把它加到标记队列(该对象变为灰色)
						greyobject(obj, b, i, span, gcw, objIndex)
					} else if stk != nil && p >= stk.stack.lo && p < stk.stack.hi {
						stk.putPtr(p)
					}
				}
			}
			// 处理下一个指针下一个bit
			bits >>= 1
			i += sys.PtrSize
		}
	}
}

// scanobject scans the object starting at b, adding pointers to gcw.
// b must point to the beginning of a heap object or an oblet.
// scanobject consults the GC bitmap for the pointer mask and the spans for the size of the object.
//go:nowritebarrier
/*
标灰就是标记并放进队列，标黑就是标记，所以当灰色对象从队列中取出后，我们就可以认为这个对象是黑色对象了
gcDrain函数扫描完根对象, 就会开始消费标记队列, 对从标记队列中取出的对象调用scanobject函数
*/
func scanobject(b uintptr, gcw *gcWork) {
	// Find the bits for b and the size of the object at b.
	//
	// b is either the beginning of an object, in which case this
	// is the size of the object to scan, or it points to an
	// oblet, in which case we compute the size to scan below.
	// 获取b对应的bits
	hbits := heapBitsForAddr(b)
	// 获取b所在的span
	s := spanOfUnchecked(b)
	// 获取对象的大小
	n := s.elemsize
	if n == 0 {
		throw("scanobject n == 0")
	}
	// 对象过大，则切割后再扫描，maxObletBytes为128k。每次最多只扫描128KB
	if n > maxObletBytes {
		// Large object. Break into oblets for better parallelism and lower latency.
		if b == s.base() {
			// It's possible this is a noscan object (not from greyobject, but from other code paths), 
			// in which case we must *not* enqueue oblets since their bitmaps will be uninitialized.
			// 如果不是指针，直接标记返回，相当于标黑了
			if s.spanclass.noscan() {
				// Bypass the whole scan.
				gcw.bytesMarked += uint64(n)
				return
			}

			// Enqueue the other oblets to scan later.
			// Some oblets may be in b's scalar tail, but
			// these will be marked as "no more pointers",
			// so we'll drop out immediately when we go to
			// scan those.
			// 按maxObletBytes切割后放入到队列
			for oblet := b + maxObletBytes; oblet < s.base()+s.elemsize; oblet += maxObletBytes {
				if !gcw.putFast(oblet) {
					gcw.put(oblet)
				}
			}
		}

		// Compute the size of the oblet. Since this object
		// must be a large object, s.base() is the beginning
		// of the object.
		n = s.base() + s.elemsize - b
		if n > maxObletBytes {
			n = maxObletBytes
		}
	}

	// 扫描对象中的指针
	var i uintptr
	for i = 0; i < n; i += sys.PtrSize {
		// Find bits for this word.
		// 获取到对应的bits
		if i != 0 {
			// Avoid needless hbits.next() on last iteration.
			hbits = hbits.next()
		}
		// Load bits once. See CL 22712 and issue 16973 for discussion.
		bits := hbits.bits()
		// During checkmarking, 1-word objects store the checkmark
		// in the type bit for the one word. The only one-word objects
		// are pointers, or else they'd be merged with other non-pointer
		// data into larger allocations.
		// 检查scan bit判断是否继续扫描, 注意第二个scan bit是checkmark
		if i != 1*sys.PtrSize && bits&bitScan == 0 {
			break // no more pointers in this object
		}
		// 不是指针，继续。检查pointer bit, 不是指针则继续
		if bits&bitPointer == 0 {
			continue // not a pointer
		}

		// Work here is duplicated in scanblock and above.
		// If you make changes here, make changes there too.
		// 取出指针的值
		obj := *(*uintptr)(unsafe.Pointer(b + i))

		// At this point we have extracted the next potential pointer.
		// Quickly filter out nil and pointers back to the current object.
		// 如果指针在arena区域中, 则调用greyobject标记对象并把对象放到标记队列中
		if obj != 0 && obj-b >= n {
			// Test if obj points into the Go heap and, if so,
			// mark the object.
			//
			// Note that it's possible for findObject to
			// fail if obj points to a just-allocated heap
			// object because of a race with growing the
			// heap. In this case, we know the object was
			// just allocated and hence will be marked by
			// allocation itself.
			// 找到指针对应的对象，并标灰
			if obj, span, objIndex := findObject(obj, b, i); obj != 0 {
				greyobject(obj, b, i, span, gcw, objIndex)
			}
		}
	}
	// 统计扫描过的大小和对象数量
	gcw.bytesMarked += uint64(n)
	gcw.scanWork += int64(i)
}

// Shade the object if it isn't already.
// The object is not nil and known to be in the heap.
// Preemption must be disabled.
//go:nowritebarrier
/*
shade(*slot)是删除写屏障的变形，例如，一个堆上的灰色对象B，引用白色对象C，在GC并发运行的过程中，
如果栈已扫描置黑，而赋值器将指向C的唯一指针从B中删除，并让栈上其他对象引用它，
这时，写屏障会在删除指向白色对象C的指针的时候就将C对象置灰，就可以保护下来了，且它下游的所有对象都处于被保护状态。
如果对象B在栈上，引用堆上的白色对象C，将其引用关系删除，且新增一个黑色对象到对象C的引用，那么就需要通过shade(ptr)来保护了，
在指针插入黑色对象时会触发对对象C的置灰操作。 如果栈已经被扫描过了，那么栈上引用的对象都是灰色或受灰色保护的白色对象了，
所以就没有必要再进行这步操作。
*/
func shade(b uintptr) {
	if obj, span, objIndex := findObject(b, 0, 0); obj != 0 {
		gcw := &getg().m.p.ptr().gcw
		// 标记一个对象存活, 并把它加到标记队列(该对象变为灰色)
		greyobject(obj, 0, 0, span, gcw, objIndex)
		// 如果标记了禁止本地标记队列则flush到全局标记队列
	}
}

// obj is the start of an object with mark mbits.
// If it isn't already marked, mark it and enqueue into gcw.
// base and off are for debugging only and could be removed.
//
// See also wbBufFlush1, which partially duplicates this logic.
//
//go:nowritebarrierrec
// 标灰操作。标灰对象其实就是找到对应bitmap，标记存活并扔进队列
func greyobject(obj, base, off uintptr, span *mspan, gcw *gcWork, objIndex uintptr) {
	// obj should be start of allocation, and so must be at least pointer-aligned.
	if obj&(sys.PtrSize-1) != 0 {
		throw("greyobject: obj not pointer-aligned")
	}
	mbits := span.markBitsForIndex(objIndex)

	if useCheckmark {
		// 这里是用来debug，确保所有的对象都被正确标识
		// checkmark是用于检查是否所有可到达的对象都被正确标记的机制, 仅除错使用
		if !mbits.isMarked() {
			printlock()
			print("runtime:greyobject: checkmarks finds unexpected unmarked object obj=", hex(obj), "\n")
			print("runtime: found obj at *(", hex(base), "+", hex(off), ")\n")

			// Dump the source (base) object
			gcDumpObject("base", base, off)

			// Dump the object
			gcDumpObject("obj", obj, ^uintptr(0))

			getg().m.traceback = 2
			throw("checkmark found unmarked object")
		}
		hbits := heapBitsForAddr(obj)
		if hbits.isCheckmarked(span.elemsize) {
			return
		}
		hbits.setCheckmarked(span.elemsize)
		if !hbits.isCheckmarked(span.elemsize) {
			throw("setCheckmarked and isCheckmarked disagree")
		}
	} else {
		if debug.gccheckmark > 0 && span.isFree(objIndex) {
			print("runtime: marking free object ", hex(obj), " found at *(", hex(base), "+", hex(off), ")\n")
			gcDumpObject("base", base, off)
			gcDumpObject("obj", obj, ^uintptr(0))
			getg().m.traceback = 2
			throw("marking free object")
		}

		// If marked we have nothing to do.
		// 对象被正确标记了，无需做其他的操作
		// 如果对象所在的span中的gcmarkBits对应的bit已经设置为1则可以跳过处理
		if mbits.isMarked() {
			return
		}
		mbits.setMarked()

		// Mark span.
		arena, pageIdx, pageMask := pageIndexOf(span.base())
		if arena.pageMarks[pageIdx]&pageMask == 0 {
			// 标记对象。设置对象所在的span中的gcmarkBits对应的bit为1
			atomic.Or8(&arena.pageMarks[pageIdx], pageMask)
		}

		// If this is a noscan object, fast-track it to black instead of greying it.
		// 如果对象不是指针，则只需要标记，不需要放进队列，相当于直接标黑
		// 如果确定对象不包含指针(所在span的类型是noscan), 则不需要把对象放入标记队列
		if span.spanclass.noscan() {
			gcw.bytesMarked += uint64(span.elemsize)
			return
		}
	}

	// Queue the obj for scanning. The PREFETCH(obj) logic has been removed but
	// seems like a nice optimization that can be added back in.
	// There needs to be time between the PREFETCH and the use.
	// Previously we put the obj in an 8 element buffer that is drained at a rate
	// to give the PREFETCH time to do its work.
	// Use of PREFETCHNTA might be more appropriate than PREFETCH
	// 判断对象是否被放进队列，没有则放入，标灰步骤完成
	// 先放入本地标记队列, 失败时把本地标记队列中的部分工作转移到全局标记队列, 再放入本地标记队列
	if !gcw.putFast(obj) {
		gcw.put(obj)
	}
}

// gcDumpObject dumps the contents of obj for debugging and marks the
// field at byte offset off in obj.
func gcDumpObject(label string, obj, off uintptr) {
	s := spanOf(obj)
	print(label, "=", hex(obj))
	if s == nil {
		print(" s=nil\n")
		return
	}
	print(" s.base()=", hex(s.base()), " s.limit=", hex(s.limit), " s.spanclass=", s.spanclass, " s.elemsize=", s.elemsize, " s.state=")
	if 0 <= s.state && int(s.state) < len(mSpanStateNames) {
		print(mSpanStateNames[s.state], "\n")
	} else {
		print("unknown(", s.state, ")\n")
	}

	skipped := false
	size := s.elemsize
	if s.state == mSpanManual && size == 0 {
		// We're printing something from a stack frame. We
		// don't know how big it is, so just show up to an
		// including off.
		size = off + sys.PtrSize
	}
	for i := uintptr(0); i < size; i += sys.PtrSize {
		// For big objects, just print the beginning (because
		// that usually hints at the object's type) and the
		// fields around off.
		if !(i < 128*sys.PtrSize || off-16*sys.PtrSize < i && i < off+16*sys.PtrSize) {
			skipped = true
			continue
		}
		if skipped {
			print(" ...\n")
			skipped = false
		}
		print(" *(", label, "+", i, ") = ", hex(*(*uintptr)(unsafe.Pointer(obj + i))))
		if i == off {
			print(" <==")
		}
		print("\n")
	}
	if skipped {
		print(" ...\n")
	}
}

// gcmarknewobject marks a newly allocated object black. obj must
// not contain any non-nil pointers.
//
// This is nosplit so it can manipulate a gcWork without preemption.
//
//go:nowritebarrier
//go:nosplit
func gcmarknewobject(obj, size, scanSize uintptr) {
	if useCheckmark { // The world should be stopped so this should not happen.
		throw("gcmarknewobject called while doing checkmark")
	}
	markBitsForAddr(obj).setMarked()
	gcw := &getg().m.p.ptr().gcw
	gcw.bytesMarked += uint64(size)
	gcw.scanWork += int64(scanSize)
}

// gcMarkTinyAllocs greys all active tiny alloc blocks.
// The world must be stopped.
// 函数会标记所有tiny alloc等待合并的对象
func gcMarkTinyAllocs() {
	for _, p := range allp {
		c := p.mcache
		if c == nil || c.tiny == 0 {
			continue
		}
		// 标记各个P中的mcache中的tiny
		// 在上面的mallocgc函数中可以看到tiny是当前等待合并的对象
		_, span, objIndex := findObject(c.tiny, 0, 0)
		gcw := &p.gcw
		// 标记一个对象存活, 并把它加到标记队列(该对象变为灰色)x
		greyobject(c.tiny, 0, 0, span, gcw, objIndex)
	}
}

// Checkmarking

// To help debug the concurrent GC we remark with the world
// stopped ensuring that any object encountered has their normal
// mark bit set. To do this we use an orthogonal bit
// pattern to indicate the object is marked. The following pattern
// uses the upper two bits in the object's boundary nibble.
// 01: scalar  not marked
// 10: pointer not marked
// 11: pointer     marked
// 00: scalar      marked
// Xoring with 01 will flip the pattern from marked to unmarked and vica versa.
// The higher bit is 1 for pointers and 0 for scalars, whether the object
// is marked or not.
// The first nibble no longer holds the typeDead pattern indicating that the
// there are no more pointers in the object. This information is held
// in the second nibble.

// If useCheckmark is true, marking of an object uses the
// checkmark bits (encoding above) instead of the standard
// mark bits.
var useCheckmark = false

//go:nowritebarrier
func initCheckmarks() {
	useCheckmark = true
	for _, s := range mheap_.allspans {
		if s.state == mSpanInUse {
			heapBitsForAddr(s.base()).initCheckmarkSpan(s.layout())
		}
	}
}

func clearCheckmarks() {
	useCheckmark = false
	for _, s := range mheap_.allspans {
		if s.state == mSpanInUse {
			heapBitsForAddr(s.base()).clearCheckmarkSpan(s.layout())
		}
	}
}
