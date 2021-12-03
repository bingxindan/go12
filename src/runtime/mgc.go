// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Garbage collector (GC).
//
// The GC runs concurrently with mutator threads, is type accurate (aka precise), allows multiple
// GC thread to run in parallel. It is a concurrent mark and sweep that uses a write barrier. It is
// non-generational and non-compacting. Allocation is done using size segregated per P allocation
// areas to minimize fragmentation while eliminating locks in the common case.
//
// The algorithm decomposes into several steps.
// This is a high level description of the algorithm being used. For an overview of GC a good
// place to start is Richard Jones' gchandbook.org.
//
// The algorithm's intellectual heritage includes Dijkstra's on-the-fly algorithm, see
// Edsger W. Dijkstra, Leslie Lamport, A. J. Martin, C. S. Scholten, and E. F. M. Steffens. 1978.
// On-the-fly garbage collection: an exercise in cooperation. Commun. ACM 21, 11 (November 1978),
// 966-975.
// For journal quality proofs that these steps are complete, correct, and terminate see
// Hudson, R., and Moss, J.E.B. Copying Garbage Collection without stopping the world.
// Concurrency and Computation: Practice and Experience 15(3-5), 2003.
//
// 1. GC performs sweep termination.
//
//    a. Stop the world. This causes all Ps to reach a GC safe-point.
//
//    b. Sweep any unswept spans. There will only be unswept spans if
//    this GC cycle was forced before the expected time.
//
// 2. GC performs the mark phase.
//
//    a. Prepare for the mark phase by setting gcphase to _GCmark
//    (from _GCoff), enabling the write barrier, enabling mutator
//    assists, and enqueueing root mark jobs. No objects may be
//    scanned until all Ps have enabled the write barrier, which is
//    accomplished using STW.
//
//    b. Start the world. From this point, GC work is done by mark
//    workers started by the scheduler and by assists performed as
//    part of allocation. The write barrier shades both the
//    overwritten pointer and the new pointer value for any pointer
//    writes (see mbarrier.go for details). Newly allocated objects
//    are immediately marked black.
//
//    c. GC performs root marking jobs. This includes scanning all
//    stacks, shading all globals, and shading any heap pointers in
//    off-heap runtime data structures. Scanning a stack stops a
//    goroutine, shades any pointers found on its stack, and then
//    resumes the goroutine.
//
//    d. GC drains the work queue of grey objects, scanning each grey
//    object to black and shading all pointers found in the object
//    (which in turn may add those pointers to the work queue).
//
//    e. Because GC work is spread across local caches, GC uses a
//    distributed termination algorithm to detect when there are no
//    more root marking jobs or grey objects (see gcMarkDone). At this
//    point, GC transitions to mark termination.
//
// 3. GC performs mark termination.
//
//    a. Stop the world.
//
//    b. Set gcphase to _GCmarktermination, and disable workers and
//    assists.
//
//    c. Perform housekeeping like flushing mcaches.
//
// 4. GC performs the sweep phase.
//
//    a. Prepare for the sweep phase by setting gcphase to _GCoff,
//    setting up sweep state and disabling the write barrier.
//
//    b. Start the world. From this point on, newly allocated objects
//    are white, and allocating sweeps spans before use if necessary.
//
//    c. GC does concurrent sweeping in the background and in response
//    to allocation. See description below.
//
// 5. When sufficient allocation has taken place, replay the sequence
// starting with 1 above. See discussion of GC rate below.

// Concurrent sweep.
//
// The sweep phase proceeds concurrently with normal program execution.
// The heap is swept span-by-span both lazily (when a goroutine needs another span)
// and concurrently in a background goroutine (this helps programs that are not CPU bound).
// At the end of STW mark termination all spans are marked as "needs sweeping".
//
// The background sweeper goroutine simply sweeps spans one-by-one.
//
// To avoid requesting more OS memory while there are unswept spans, when a
// goroutine needs another span, it first attempts to reclaim that much memory
// by sweeping. When a goroutine needs to allocate a new small-object span, it
// sweeps small-object spans for the same object size until it frees at least
// one object. When a goroutine needs to allocate large-object span from heap,
// it sweeps spans until it frees at least that many pages into heap. There is
// one case where this may not suffice: if a goroutine sweeps and frees two
// nonadjacent one-page spans to the heap, it will allocate a new two-page
// span, but there can still be other one-page unswept spans which could be
// combined into a two-page span.
//
// It's critical to ensure that no operations proceed on unswept spans (that would corrupt
// mark bits in GC bitmap). During GC all mcaches are flushed into the central cache,
// so they are empty. When a goroutine grabs a new span into mcache, it sweeps it.
// When a goroutine explicitly frees an object or sets a finalizer, it ensures that
// the span is swept (either by sweeping it, or by waiting for the concurrent sweep to finish).
// The finalizer goroutine is kicked off only when all spans are swept.
// When the next GC starts, it sweeps all not-yet-swept spans (if any).

// GC rate.
// Next GC is after we've allocated an extra amount of memory proportional to
// the amount already in use. The proportion is controlled by GOGC environment variable
// (100 by default). If GOGC=100 and we're using 4M, we'll GC again when we get to 8M
// (this mark is tracked in next_gc variable). This keeps the GC cost in linear
// proportion to the allocation cost. Adjusting GOGC just changes the linear constant
// (and also the amount of extra memory used).

// Oblets
//
// In order to prevent long pauses while scanning large objects and to
// improve parallelism, the garbage collector breaks up scan jobs for
// objects larger than maxObletBytes into "oblets" of at most
// maxObletBytes. When scanning encounters the beginning of a large
// object, it scans only the first oblet and enqueues the remaining
// oblets as new scan jobs.

package runtime

import (
	"internal/cpu"
	"runtime/internal/atomic"
	"unsafe"
)

const (
	_DebugGC         = 0
	_ConcurrentSweep = true
	_FinBlockSize    = 4 * 1024

	// sweepMinHeapDistance is a lower bound on the heap distance
	// (in bytes) reserved for concurrent sweeping between GC
	// cycles. This will be scaled by gcpercent/100.
	sweepMinHeapDistance = 1024 * 1024
)

// heapminimum is the minimum heap size at which to trigger GC.
// For small heaps, this overrides the usual GOGC*live set rule.
//
// When there is a very small live set but a lot of allocation, simply
// collecting when the heap reaches GOGC*live results in many GC
// cycles and high total per-GC overhead. This minimum amortizes this
// per-GC overhead while keeping the heap reasonably small.
//
// During initialization this is set to 4MB*GOGC/100. In the case of
// GOGC==0, this will set heapminimum to 0, resulting in constant
// collection even when the heap size is small, which is useful for
// debugging.
var heapminimum uint64 = defaultHeapMinimum

// defaultHeapMinimum is the value of heapminimum for GOGC==100.
const defaultHeapMinimum = 4 << 20

// Initialized from $GOGC.  GOGC=off means no GC.
var gcpercent int32

func gcinit() {
	if unsafe.Sizeof(workbuf{}) != _WorkbufSize {
		throw("size of Workbuf is suboptimal")
	}

	// No sweep on the first cycle.
	mheap_.sweepdone = 1

	// Set a reasonable initial GC trigger.
	memstats.triggerRatio = 7 / 8.0

	// Fake a heap_marked value so it looks like a trigger at
	// heapminimum is the appropriate growth from heap_marked.
	// This will go into computing the initial GC goal.
	memstats.heap_marked = uint64(float64(heapminimum) / (1 + memstats.triggerRatio))

	// Set gcpercent from the environment. This will also compute
	// and set the GC trigger and goal.
	_ = setGCPercent(readgogc())

	work.startSema = 1
	work.markDoneSema = 1
}

func readgogc() int32 {
	p := gogetenv("GOGC")
	if p == "off" {
		return -1
	}
	if n, ok := atoi32(p); ok {
		return n
	}
	return 100
}

// gcenable is called after the bulk of the runtime initialization,
// just before we're about to start letting user code run.
// It kicks off the background sweeper goroutine and enables GC.
func gcenable() {
	c := make(chan int, 1)
	go bgsweep(c)
	<-c
	memstats.enablegc = true // now that runtime is initialized, GC is okay
}

//go:linkname setGCPercent runtime/debug.setGCPercent
func setGCPercent(in int32) (out int32) {
	lock(&mheap_.lock)
	out = gcpercent
	if in < 0 {
		in = -1
	}
	gcpercent = in
	heapminimum = defaultHeapMinimum * uint64(gcpercent) / 100
	// Update pacing in response to gcpercent change.
	gcSetTriggerRatio(memstats.triggerRatio)
	unlock(&mheap_.lock)

	// If we just disabled GC, wait for any concurrent GC mark to
	// finish so we always return with no GC running.
	if in < 0 {
		gcWaitOnMark(atomic.Load(&work.cycles))
	}

	return out
}

// Garbage collector phase.
// Indicates to write barrier and synchronization task to perform.
var gcphase uint32

// The compiler knows about this variable.
// If you change it, you must change builtin/runtime.go, too.
// If you change the first four bytes, you must also change the write
// barrier insertion code.
var writeBarrier struct {
	enabled bool    // compiler emits a check of this before calling write barrier
	pad     [3]byte // compiler uses 32-bit load for "enabled" field
	needed  bool    // whether we need a write barrier for current GC phase
	cgo     bool    // whether we need a write barrier for a cgo check
	alignme uint64  // guarantee alignment so that compiler can use a 32 or 64-bit load
}

// gcBlackenEnabled is 1 if mutator assists and background mark
// workers are allowed to blacken objects. This must only be set when
// gcphase == _GCmark.
var gcBlackenEnabled uint32

const (
	// GC未运行；在后台扫描，禁用写屏障
	_GCoff             = iota // GC not running; sweeping in background, write barrier disabled
	// GC标记根和工作区：分配黑色，启用写屏障
	_GCmark                   // GC marking roots and workbufs: allocate black, write barrier ENABLED
	// GC标记终止：分配黑色，P的帮助GC，启用写屏障
	_GCmarktermination        // GC mark termination: allocate black, P's help GC, write barrier ENABLED
)

//go:nosplit
// 函数会修改表示当前GC阶段的全局变量和是否开启写屏障的全局变量
func setGCPhase(x uint32) {
	atomic.Store(&gcphase, x)
	writeBarrier.needed = gcphase == _GCmark || gcphase == _GCmarktermination
	writeBarrier.enabled = writeBarrier.needed || writeBarrier.cgo
}

// gcMarkWorkerMode represents the mode that a concurrent mark worker
// should operate in.
//
// Concurrent marking happens through four different mechanisms. One
// is mutator assists, which happen in response to allocations and are
// not scheduled. The other three are variations in the per-P mark
// workers and are distinguished by gcMarkWorkerMode.
// 标记工作模式，目前来说有三种，这三种是为了保证后台的标记线程的利用率。
type gcMarkWorkerMode int

const (
	// gcMarkWorkerDedicatedMode indicates that the P of a mark
	// worker is dedicated to running that mark worker. The mark
	// worker should run without preemption.
	// P 专门负责标记对象，不会被调度器抢占；
	gcMarkWorkerDedicatedMode gcMarkWorkerMode = iota

	// gcMarkWorkerFractionalMode indicates that a P is currently
	// running the "fractional" mark worker. The fractional worker
	// is necessary when GOMAXPROCS*gcBackgroundUtilization is not
	// an integer. The fractional worker should run until it is
	// preempted and will be scheduled to pick up the fractional
	// part of GOMAXPROCS*gcBackgroundUtilization.
	// 主要是由于现在默认标记线程的占用率要为 25%，所以如果 CPU 核数不是4的倍数，就无法除得整数，
	// 启动该类型的工作模式帮助垃圾收集达到利用率的目标；
	gcMarkWorkerFractionalMode

	// gcMarkWorkerIdleMode indicates that a P is running the mark
	// worker because it has nothing else to do. The idle worker
	// should run until it is preempted and account its time
	// against gcController.idleMarkTime.
	// 表示 P 当前只有标记线程在跑，没有其他可以执行的 G ，它会运行垃圾收集的标记任务直到被抢占；
	gcMarkWorkerIdleMode
)

// gcMarkWorkerModeStrings are the strings labels of gcMarkWorkerModes
// to use in execution traces.
var gcMarkWorkerModeStrings = [...]string{
	"GC (dedicated)",
	"GC (fractional)",
	"GC (idle)",
}

// gcController implements the GC pacing controller that determines
// when to trigger concurrent garbage collection and how much marking
// work to do in mutator assists and background marking.
//
// It uses a feedback control algorithm to adjust the memstats.gc_trigger
// trigger based on the heap growth and GC CPU utilization each cycle.
// This algorithm optimizes for heap growth to match GOGC and for CPU
// utilization between assist and background marking to be 25% of
// GOMAXPROCS. The high-level design of this algorithm is documented
// at https://golang.org/s/go15gcpacing.
//
// All fields of gcController are used only during a single mark
// cycle.
var gcController gcControllerState

type gcControllerState struct {
	// scanWork is the total scan work performed this cycle. This
	// is updated atomically during the cycle. Updates occur in
	// bounded batches, since it is both written and read
	// throughout the cycle. At the end of the cycle, this is how
	// much of the retained heap is scannable.
	//
	// Currently this is the bytes of heap scanned. For most uses,
	// this is an opaque unit of work, but for estimation the
	// definition is important.
	scanWork int64

	// bgScanCredit is the scan work credit accumulated by the
	// concurrent background scan. This credit is accumulated by
	// the background scan and stolen by mutator assists. This is
	// updated atomically. Updates occur in bounded batches, since
	// it is both written and read throughout the cycle.
	bgScanCredit int64

	// assistTime is the nanoseconds spent in mutator assists
	// during this cycle. This is updated atomically. Updates
	// occur in bounded batches, since it is both written and read
	// throughout the cycle.
	assistTime int64

	// dedicatedMarkTime is the nanoseconds spent in dedicated
	// mark workers during this cycle. This is updated atomically
	// at the end of the concurrent mark phase.
	dedicatedMarkTime int64

	// fractionalMarkTime is the nanoseconds spent in the
	// fractional mark worker during this cycle. This is updated
	// atomically throughout the cycle and will be up-to-date if
	// the fractional mark worker is not currently running.
	fractionalMarkTime int64

	// idleMarkTime is the nanoseconds spent in idle marking
	// during this cycle. This is updated atomically throughout
	// the cycle.
	idleMarkTime int64

	// markStartTime is the absolute start time in nanoseconds
	// that assists and background mark workers started.
	markStartTime int64

	// dedicatedMarkWorkersNeeded is the number of dedicated mark
	// workers that need to be started. This is computed at the
	// beginning of each cycle and decremented atomically as
	// dedicated mark workers get started.
	dedicatedMarkWorkersNeeded int64

	// assistWorkPerByte is the ratio of scan work to allocated
	// bytes that should be performed by mutator assists. This is
	// computed at the beginning of each cycle and updated every
	// time heap_scan is updated.
	assistWorkPerByte float64

	// assistBytesPerWork is 1/assistWorkPerByte.
	assistBytesPerWork float64

	// fractionalUtilizationGoal is the fraction of wall clock
	// time that should be spent in the fractional mark worker on
	// each P that isn't running a dedicated worker.
	//
	// For example, if the utilization goal is 25% and there are
	// no dedicated workers, this will be 0.25. If the goal is
	// 25%, there is one dedicated worker, and GOMAXPROCS is 5,
	// this will be 0.05 to make up the missing 5%.
	//
	// If this is zero, no fractional workers are needed.
	fractionalUtilizationGoal float64

	_ cpu.CacheLinePad
}

// startCycle resets the GC controller's state and computes estimates
// for a new GC cycle. The caller must hold worldsema.
// 标记开始了新一轮的GC
func (c *gcControllerState) startCycle() {
	c.scanWork = 0
	c.bgScanCredit = 0
	c.assistTime = 0
	c.dedicatedMarkTime = 0
	c.fractionalMarkTime = 0
	c.idleMarkTime = 0

	// If this is the first GC cycle or we're operating on a very
	// small heap, fake heap_marked so it looks like gc_trigger is
	// the appropriate growth from heap_marked, even though the
	// real heap_marked may not have a meaningful value (on the
	// first cycle) or may be much smaller (resulting in a large
	// error response).
	// 伪装heap_marked的值如果gc_trigger的值很小, 防止后面对triggerRatio做出错误的调整
	if memstats.gc_trigger <= heapminimum {
		memstats.heap_marked = uint64(float64(memstats.gc_trigger) / (1 + memstats.triggerRatio))
	}

	// Re-compute the heap goal for this cycle in case something
	// changed. This is the same calculation we use elsewhere.
	// 重新计算next_gc, 注意next_gc的计算跟gc_trigger不一样
	memstats.next_gc = memstats.heap_marked + memstats.heap_marked*uint64(gcpercent)/100
	if gcpercent < 0 {
		memstats.next_gc = ^uint64(0)
	}

	// Ensure that the heap goal is at least a little larger than
	// the current live heap size. This may not be the case if GC
	// start is delayed or if the allocation that pushed heap_live
	// over gc_trigger is large or if the trigger is really close to
	// GOGC. Assist is proportional to this distance, so enforce a
	// minimum distance, even if it means going over the GOGC goal
	// by a tiny bit.
	// 确保next_gc和heap_live之间最少有1MB
	if memstats.next_gc < memstats.heap_live+1024*1024 {
		memstats.next_gc = memstats.heap_live + 1024*1024
	}

	// Compute the background mark utilization goal. In general,
	// this may not come out exactly. We round the number of
	// dedicated workers so that the utilization is closest to
	// 25%. For small GOMAXPROCS, this would introduce too much
	// error, so we add fractional workers in that case.
	// 计算可以同时执行的后台标记任务的数量
	// dedicatedMarkWorkersNeeded等于P的数量的25%去除小数点
	// 如果可以整除则fractionalMarkWorkersNeeded等于0否则等于1
	// totalUtilizationGoal是GC所占的P的目标值(例如P一共有5个时目标是1.25个P)
	// fractionalUtilizationGoal是Fractiona模式的任务所占的P的目标值(例如P一共有5个时目标是0.25个P)
	totalUtilizationGoal := float64(gomaxprocs) * gcBackgroundUtilization
	c.dedicatedMarkWorkersNeeded = int64(totalUtilizationGoal + 0.5)
	utilError := float64(c.dedicatedMarkWorkersNeeded)/totalUtilizationGoal - 1
	const maxUtilError = 0.3
	if utilError < -maxUtilError || utilError > maxUtilError {
		// Rounding put us more than 30% off our goal. With
		// gcBackgroundUtilization of 25%, this happens for
		// GOMAXPROCS<=3 or GOMAXPROCS=6. Enable fractional
		// workers to compensate.
		if float64(c.dedicatedMarkWorkersNeeded) > totalUtilizationGoal {
			// Too many dedicated workers.
			c.dedicatedMarkWorkersNeeded--
		}
		c.fractionalUtilizationGoal = (totalUtilizationGoal - float64(c.dedicatedMarkWorkersNeeded)) / float64(gomaxprocs)
	} else {
		c.fractionalUtilizationGoal = 0
	}

	// In STW mode, we just want dedicated workers.
	if debug.gcstoptheworld > 0 {
		c.dedicatedMarkWorkersNeeded = int64(gomaxprocs)
		c.fractionalUtilizationGoal = 0
	}

	// Clear per-P state
	// 重置P中的辅助GC所用的时间统计
	for _, p := range allp {
		p.gcAssistTime = 0
		p.gcFractionalMarkTime = 0
	}

	// Compute initial values for controls that are updated
	// throughout the cycle.
	// 计算辅助GC的参数
	// 参考上面对计算assistWorkPerByte的公式的分析
	c.revise()

	if debug.gcpacertrace > 0 {
		print("pacer: assist ratio=", c.assistWorkPerByte,
			" (scan ", memstats.heap_scan>>20, " MB in ",
			work.initialHeapLive>>20, "->",
			memstats.next_gc>>20, " MB)",
			" workers=", c.dedicatedMarkWorkersNeeded,
			"+", c.fractionalUtilizationGoal, "\n")
	}
}

// revise updates the assist ratio during the GC cycle to account for
// improved estimates. This should be called either under STW or
// whenever memstats.heap_scan, memstats.heap_live, or
// memstats.next_gc is updated (with mheap_.lock held).
//
// It should only be called when gcBlackenEnabled != 0 (because this
// is when assists are enabled and the necessary statistics are
// available).
func (c *gcControllerState) revise() {
	gcpercent := gcpercent
	if gcpercent < 0 {
		// If GC is disabled but we're running a forced GC,
		// act like GOGC is huge for the below calculations.
		gcpercent = 100000
	}
	live := atomic.Load64(&memstats.heap_live)

	var heapGoal, scanWorkExpected int64
	if live <= memstats.next_gc {
		// We're under the soft goal. Pace GC to complete at
		// next_gc assuming the heap is in steady-state.
		heapGoal = int64(memstats.next_gc)

		// Compute the expected scan work remaining.
		//
		// This is estimated based on the expected
		// steady-state scannable heap. For example, with
		// GOGC=100, only half of the scannable heap is
		// expected to be live, so that's what we target.
		//
		// (This is a float calculation to avoid overflowing on
		// 100*heap_scan.)
		scanWorkExpected = int64(float64(memstats.heap_scan) * 100 / float64(100+gcpercent))
	} else {
		// We're past the soft goal. Pace GC so that in the
		// worst case it will complete by the hard goal.
		const maxOvershoot = 1.1
		heapGoal = int64(float64(memstats.next_gc) * maxOvershoot)

		// Compute the upper bound on the scan work remaining.
		scanWorkExpected = int64(memstats.heap_scan)
	}

	// Compute the remaining scan work estimate.
	//
	// Note that we currently count allocations during GC as both
	// scannable heap (heap_scan) and scan work completed
	// (scanWork), so allocation will change this difference will
	// slowly in the soft regime and not at all in the hard
	// regime.
	scanWorkRemaining := scanWorkExpected - c.scanWork
	if scanWorkRemaining < 1000 {
		// We set a somewhat arbitrary lower bound on
		// remaining scan work since if we aim a little high,
		// we can miss by a little.
		//
		// We *do* need to enforce that this is at least 1,
		// since marking is racy and double-scanning objects
		// may legitimately make the remaining scan work
		// negative, even in the hard goal regime.
		scanWorkRemaining = 1000
	}

	// Compute the heap distance remaining.
	heapRemaining := heapGoal - int64(live)
	if heapRemaining <= 0 {
		// This shouldn't happen, but if it does, avoid
		// dividing by zero or setting the assist negative.
		heapRemaining = 1
	}

	// Compute the mutator assist ratio so by the time the mutator
	// allocates the remaining heap bytes up to next_gc, it will
	// have done (or stolen) the remaining amount of scan work.
	c.assistWorkPerByte = float64(scanWorkRemaining) / float64(heapRemaining)
	c.assistBytesPerWork = float64(heapRemaining) / float64(scanWorkRemaining)
}

// endCycle computes the trigger ratio for the next cycle.
func (c *gcControllerState) endCycle() float64 {
	if work.userForced {
		// Forced GC means this cycle didn't start at the
		// trigger, so where it finished isn't good
		// information about how to adjust the trigger.
		// Just leave it where it is.
		return memstats.triggerRatio
	}

	// Proportional response gain for the trigger controller. Must
	// be in [0, 1]. Lower values smooth out transient effects but
	// take longer to respond to phase changes. Higher values
	// react to phase changes quickly, but are more affected by
	// transient changes. Values near 1 may be unstable.
	const triggerGain = 0.5

	// Compute next cycle trigger ratio. First, this computes the
	// "error" for this cycle; that is, how far off the trigger
	// was from what it should have been, accounting for both heap
	// growth and GC CPU utilization. We compute the actual heap
	// growth during this cycle and scale that by how far off from
	// the goal CPU utilization we were (to estimate the heap
	// growth if we had the desired CPU utilization). The
	// difference between this estimate and the GOGC-based goal
	// heap growth is the error.
	goalGrowthRatio := float64(gcpercent) / 100
	actualGrowthRatio := float64(memstats.heap_live)/float64(memstats.heap_marked) - 1
	assistDuration := nanotime() - c.markStartTime

	// Assume background mark hit its utilization goal.
	utilization := gcBackgroundUtilization
	// Add assist utilization; avoid divide by zero.
	if assistDuration > 0 {
		utilization += float64(c.assistTime) / float64(assistDuration*int64(gomaxprocs))
	}

	triggerError := goalGrowthRatio - memstats.triggerRatio - utilization/gcGoalUtilization*(actualGrowthRatio-memstats.triggerRatio)

	// Finally, we adjust the trigger for next time by this error,
	// damped by the proportional gain.
	triggerRatio := memstats.triggerRatio + triggerGain*triggerError

	if debug.gcpacertrace > 0 {
		// Print controller state in terms of the design
		// document.
		H_m_prev := memstats.heap_marked
		h_t := memstats.triggerRatio
		H_T := memstats.gc_trigger
		h_a := actualGrowthRatio
		H_a := memstats.heap_live
		h_g := goalGrowthRatio
		H_g := int64(float64(H_m_prev) * (1 + h_g))
		u_a := utilization
		u_g := gcGoalUtilization
		W_a := c.scanWork
		print("pacer: H_m_prev=", H_m_prev,
			" h_t=", h_t, " H_T=", H_T,
			" h_a=", h_a, " H_a=", H_a,
			" h_g=", h_g, " H_g=", H_g,
			" u_a=", u_a, " u_g=", u_g,
			" W_a=", W_a,
			" goalΔ=", goalGrowthRatio-h_t,
			" actualΔ=", h_a-h_t,
			" u_a/u_g=", u_a/u_g,
			"\n")
	}

	return triggerRatio
}

// enlistWorker encourages another dedicated mark worker to start on
// another P if there are spare worker slots. It is used by putfull
// when more work is made available.
//
//go:nowritebarrier
func (c *gcControllerState) enlistWorker() {
	// If there are idle Ps, wake one so it will run an idle worker.
	// NOTE: This is suspected of causing deadlocks. See golang.org/issue/19112.
	//
	//	if atomic.Load(&sched.npidle) != 0 && atomic.Load(&sched.nmspinning) == 0 {
	//		wakep()
	//		return
	//	}

	// There are no idle Ps. If we need more dedicated workers,
	// try to preempt a running P so it will switch to a worker.
	if c.dedicatedMarkWorkersNeeded <= 0 {
		return
	}
	// Pick a random other P to preempt.
	if gomaxprocs <= 1 {
		return
	}
	gp := getg()
	if gp == nil || gp.m == nil || gp.m.p == 0 {
		return
	}
	myID := gp.m.p.ptr().id
	for tries := 0; tries < 5; tries++ {
		id := int32(fastrandn(uint32(gomaxprocs - 1)))
		if id >= myID {
			id++
		}
		p := allp[id]
		if p.status != _Prunning {
			continue
		}
		if preemptone(p) {
			return
		}
	}
}

// findRunnableGCWorker returns the background mark worker for _p_ if it
// should be run. This must only be called when gcBlackenEnabled != 0.
/*
每个P启动了一个后台标记任务, 但是可以同时工作的只有25%, 这个逻辑在协程M获取G时调用的findRunnableGCWorker中
*/
func (c *gcControllerState) findRunnableGCWorker(_p_ *p) *g {
	if gcBlackenEnabled == 0 {
		throw("gcControllerState.findRunnable: blackening not enabled")
	}
	if _p_.gcBgMarkWorker == 0 {
		// The mark worker associated with this P is blocked
		// performing a mark transition. We can't run it
		// because it may be on some other run or wait queue.
		return nil
	}

	if !gcMarkWorkAvailable(_p_) {
		// No work to be done right now. This can happen at
		// the end of the mark phase when there are still
		// assists tapering off. Don't bother running a worker
		// now because it'll just return immediately.
		return nil
	}

	// 原子减少对应的值, 如果减少后大于等于0则返回true, 否则返回false
	decIfPositive := func(ptr *int64) bool {
		if *ptr > 0 {
			if atomic.Xaddint64(ptr, -1) >= 0 {
				return true
			}
			// We lost a race
			atomic.Xaddint64(ptr, +1)
		}
		return false
	}

	// 减少dedicatedMarkWorkersNeeded, 成功时后台标记任务的模式是Dedicated
	// dedicatedMarkWorkersNeeded是当前P的数量的25%去除小数点。详见startCycle函数
	if decIfPositive(&c.dedicatedMarkWorkersNeeded) {
		// This P is now dedicated to marking until the end of
		// the concurrent mark phase.
		_p_.gcMarkWorkerMode = gcMarkWorkerDedicatedMode
	} else if c.fractionalUtilizationGoal == 0 {
		// No need for fractional workers.
		// 不需要零工。
		// 减少fractionalMarkWorkersNeeded, 成功是后台标记任务的模式是Fractional
		// 上面的计算如果小数点后有数值(不能够整除)则fractionalMarkWorkersNeeded为1, 否则为0
		// 详见startCycle函数
		// 举例来说, 4个P时会执行1个Dedicated模式的任务, 5个P时会执行1个Dedicated模式和1个Fractional模式的任务
		return nil
	} else {
		// Is this P behind on the fractional utilization
		// goal?
		// This should be kept in sync with pollFractionalWorkerExit.
		// 按Dedicated模式的任务的执行时间判断cpu占用率是否超过预算值, 超过时不启动
		delta := nanotime() - gcController.markStartTime
		if delta > 0 && float64(_p_.gcFractionalMarkTime)/float64(delta) > c.fractionalUtilizationGoal {
			// Nope. No need to run a fractional worker.
			return nil
		}
		// Run a fractional worker.
		_p_.gcMarkWorkerMode = gcMarkWorkerFractionalMode
	}

	// Run the background mark worker
	// 安排后台标记任务执行
	gp := _p_.gcBgMarkWorker.ptr()
	casgstatus(gp, _Gwaiting, _Grunnable)
	if trace.enabled {
		traceGoUnpark(gp, 0)
	}
	return gp
}

// pollFractionalWorkerExit reports whether a fractional mark worker
// should self-preempt. It assumes it is called from the fractional
// worker.
func pollFractionalWorkerExit() bool {
	// This should be kept in sync with the fractional worker
	// scheduler logic in findRunnableGCWorker.
	now := nanotime()
	delta := now - gcController.markStartTime
	if delta <= 0 {
		return true
	}
	p := getg().m.p.ptr()
	selfTime := p.gcFractionalMarkTime + (now - p.gcMarkWorkerStartTime)
	// Add some slack to the utilization goal so that the
	// fractional worker isn't behind again the instant it exits.
	return float64(selfTime)/float64(delta) > 1.2*gcController.fractionalUtilizationGoal
}

// gcSetTriggerRatio sets the trigger ratio and updates everything
// derived from it: the absolute trigger, the heap goal, mark pacing,
// and sweep pacing.
//
// This can be called any time. If GC is the in the middle of a
// concurrent phase, it will adjust the pacing of that phase.
//
// This depends on gcpercent, memstats.heap_marked, and
// memstats.heap_live. These must be up to date.
//
// mheap_.lock must be held or the world must be stopped.
func gcSetTriggerRatio(triggerRatio float64) {
	// Set the trigger ratio, capped to reasonable bounds.
	if triggerRatio < 0 {
		// This can happen if the mutator is allocating very
		// quickly or the GC is scanning very slowly.
		triggerRatio = 0
	} else if gcpercent >= 0 {
		// Ensure there's always a little margin so that the
		// mutator assist ratio isn't infinity.
		maxTriggerRatio := 0.95 * float64(gcpercent) / 100
		if triggerRatio > maxTriggerRatio {
			triggerRatio = maxTriggerRatio
		}
	}
	memstats.triggerRatio = triggerRatio

	// Compute the absolute GC trigger from the trigger ratio.
	//
	// We trigger the next GC cycle when the allocated heap has
	// grown by the trigger ratio over the marked heap size.
	trigger := ^uint64(0)
	if gcpercent >= 0 {
		trigger = uint64(float64(memstats.heap_marked) * (1 + triggerRatio))
		// Don't trigger below the minimum heap size.
		minTrigger := heapminimum
		if !isSweepDone() {
			// Concurrent sweep happens in the heap growth
			// from heap_live to gc_trigger, so ensure
			// that concurrent sweep has some heap growth
			// in which to perform sweeping before we
			// start the next GC cycle.
			sweepMin := atomic.Load64(&memstats.heap_live) + sweepMinHeapDistance*uint64(gcpercent)/100
			if sweepMin > minTrigger {
				minTrigger = sweepMin
			}
		}
		if trigger < minTrigger {
			trigger = minTrigger
		}
		if int64(trigger) < 0 {
			print("runtime: next_gc=", memstats.next_gc, " heap_marked=", memstats.heap_marked, " heap_live=", memstats.heap_live, " initialHeapLive=", work.initialHeapLive, "triggerRatio=", triggerRatio, " minTrigger=", minTrigger, "\n")
			throw("gc_trigger underflow")
		}
	}
	memstats.gc_trigger = trigger

	// Compute the next GC goal, which is when the allocated heap
	// has grown by GOGC/100 over the heap marked by the last
	// cycle.
	goal := ^uint64(0)
	if gcpercent >= 0 {
		goal = memstats.heap_marked + memstats.heap_marked*uint64(gcpercent)/100
		if goal < trigger {
			// The trigger ratio is always less than GOGC/100, but
			// other bounds on the trigger may have raised it.
			// Push up the goal, too.
			goal = trigger
		}
	}
	memstats.next_gc = goal
	if trace.enabled {
		traceNextGC()
	}

	// Update mark pacing.
	if gcphase != _GCoff {
		gcController.revise()
	}

	// Update sweep pacing.
	if isSweepDone() {
		mheap_.sweepPagesPerByte = 0
	} else {
		// Concurrent sweep needs to sweep all of the in-use
		// pages by the time the allocated heap reaches the GC
		// trigger. Compute the ratio of in-use pages to sweep
		// per byte allocated, accounting for the fact that
		// some might already be swept.
		heapLiveBasis := atomic.Load64(&memstats.heap_live)
		heapDistance := int64(trigger) - int64(heapLiveBasis)
		// Add a little margin so rounding errors and
		// concurrent sweep are less likely to leave pages
		// unswept when GC starts.
		heapDistance -= 1024 * 1024
		if heapDistance < _PageSize {
			// Avoid setting the sweep ratio extremely high
			heapDistance = _PageSize
		}
		pagesSwept := atomic.Load64(&mheap_.pagesSwept)
		sweepDistancePages := int64(mheap_.pagesInUse) - int64(pagesSwept)
		if sweepDistancePages <= 0 {
			mheap_.sweepPagesPerByte = 0
		} else {
			mheap_.sweepPagesPerByte = float64(sweepDistancePages) / float64(heapDistance)
			mheap_.sweepHeapLiveBasis = heapLiveBasis
			// Write pagesSweptBasis last, since this
			// signals concurrent sweeps to recompute
			// their debt.
			atomic.Store64(&mheap_.pagesSweptBasis, pagesSwept)
		}
	}
}

// gcGoalUtilization is the goal CPU utilization for
// marking as a fraction of GOMAXPROCS.
const gcGoalUtilization = 0.30

// gcBackgroundUtilization is the fixed CPU utilization for background
// marking. It must be <= gcGoalUtilization. The difference between
// gcGoalUtilization and gcBackgroundUtilization will be made up by
// mark assists. The scheduler will aim to use within 50% of this
// goal.
//
// Setting this to < gcGoalUtilization avoids saturating the trigger
// feedback controller when there are no assists, which allows it to
// better control CPU and heap growth. However, the larger the gap,
// the more mutator assists are expected to happen, which impact
// mutator latency.
const gcBackgroundUtilization = 0.25

// gcCreditSlack is the amount of scan work credit that can
// accumulate locally before updating gcController.scanWork and,
// optionally, gcController.bgScanCredit. Lower values give a more
// accurate assist ratio and make it more likely that assists will
// successfully steal background credit. Higher values reduce memory
// contention.
const gcCreditSlack = 2000

// gcAssistTimeSlack is the nanoseconds of mutator assist time that
// can accumulate on a P before updating gcController.assistTime.
const gcAssistTimeSlack = 5000

// gcOverAssistWork determines how many extra units of scan work a GC
// assist does when an assist happens. This amortizes the cost of an
// assist by pre-paying for this many bytes of future allocations.
const gcOverAssistWork = 64 << 10

var work struct {
	full  lfstack          // lock-free list of full blocks workbuf
	empty lfstack          // lock-free list of empty blocks workbuf
	pad0  cpu.CacheLinePad // prevents false-sharing between full/empty and nproc/nwait

	wbufSpans struct {
		lock mutex
		// free is a list of spans dedicated to workbufs, but
		// that don't currently contain any workbufs.
		free mSpanList
		// busy is a list of all spans containing workbufs on
		// one of the workbuf lists.
		busy mSpanList
	}

	// Restore 64-bit alignment on 32-bit.
	_ uint32

	// bytesMarked is the number of bytes marked this cycle. This
	// includes bytes blackened in scanned objects, noscan objects
	// that go straight to black, and permagrey objects scanned by
	// markroot during the concurrent scan phase. This is updated
	// atomically during the cycle. Updates may be batched
	// arbitrarily, since the value is only read at the end of the
	// cycle.
	//
	// Because of benign races during marking, this number may not
	// be the exact number of marked bytes, but it should be very
	// close.
	//
	// Put this field here because it needs 64-bit atomic access
	// (and thus 8-byte alignment even on 32-bit architectures).
	// 周期内已标记的字节大小，包含多种对象，见源码注释。由于标记过程中存在竞争，所以这个数字不是太准确，但也很接近
	bytesMarked uint64

	// work.markrootNext 会原子的增加，这是因为可能会有多个后台标记协程同时访问该变量。
	// 而这也保证了多个后台标记协程会执行不同的任务。
	markrootNext uint32 // next markroot job
	// 标记根作业数
	markrootJobs uint32 // number of markroot jobs

	// P的总个数，也就是系统CPU核数
	nproc  uint32
	tstart int64
	// 已经工作的work数
	nwait  uint32
	ndone  uint32

	// Number of roots of various root types. Set by gcMarkRootPrepare.
	// 各种根类型的根数。由gcMarkRootPrepare设置。
	nFlushCacheRoots                               int
	nDataRoots, nBSSRoots, nSpanRoots, nStackRoots int

	// Each type of GC state transition is protected by a lock.
	// Since multiple threads can simultaneously detect the state
	// transition condition, any thread that detects a transition
	// condition must acquire the appropriate transition lock,
	// re-check the transition condition and return if it no
	// longer holds or perform the transition if it does.
	// Likewise, any transition must invalidate the transition
	// condition before releasing the lock. This ensures that each
	// transition is performed by exactly one thread and threads
	// that need the transition to happen block until it has
	// happened.
	//
	// startSema protects the transition from "off" to mark or
	// mark termination.
	startSema uint32
	// markDoneSema protects transitions from mark to mark termination.
	markDoneSema uint32

	// 信号标记工作程序已启动
	bgMarkReady note   // signal background mark worker has started
	bgMarkDone  uint32 // cas to 1 when at a background mark completion point
	// Background mark completion signaling

	// mode is the concurrency mode of the current GC cycle.
	mode gcMode

	// userForced indicates the current GC cycle was forced by an
	// explicit user call.
	userForced bool

	// totaltime is the CPU nanoseconds spent in GC since the
	// program started if debug.gctrace > 0.
	totaltime int64

	// initialHeapLive is the value of memstats.heap_live at the
	// beginning of this GC cycle.
	initialHeapLive uint64

	// assistQueue is a queue of assists that are blocked because
	// there was neither enough credit to steal or enough work to
	// do.
	assistQueue struct {
		lock mutex
		q    gQueue
	}

	// sweepWaiters is a list of blocked goroutines to wake when
	// we transition from mark termination to sweep.
	sweepWaiters struct {
		lock mutex
		list gList
	}

	// cycles is the number of completed GC cycles, where a GC
	// cycle is sweep termination, mark, mark termination, and
	// sweep. This differs from memstats.numgc, which is
	// incremented at mark termination.
	cycles uint32

	// Timing/utilization stats for this cycle.
	stwprocs, maxprocs                 int32
	tSweepTerm, tMark, tMarkTerm, tEnd int64 // nanotime() of phase start

	pauseNS    int64 // total STW time this cycle
	pauseStart int64 // nanotime() of last STW

	// debug.gctrace heap sizes for this cycle.
	heap0, heap1, heap2, heapGoal uint64
}

// GC runs a garbage collection and blocks the caller until the
// garbage collection is complete. It may also block the entire
// program.
func GC() {
	// We consider a cycle to be: sweep termination, mark, mark
	// termination, and sweep. This function shouldn't return
	// until a full cycle has been completed, from beginning to
	// end. Hence, we always want to finish up the current cycle
	// and start a new one. That means:
	//
	// 1. In sweep termination, mark, or mark termination of cycle
	// N, wait until mark termination N completes and transitions
	// to sweep N.
	//
	// 2. In sweep N, help with sweep N.
	//
	// At this point we can begin a full cycle N+1.
	//
	// 3. Trigger cycle N+1 by starting sweep termination N+1.
	//
	// 4. Wait for mark termination N+1 to complete.
	//
	// 5. Help with sweep N+1 until it's done.
	//
	// This all has to be written to deal with the fact that the
	// GC may move ahead on its own. For example, when we block
	// until mark termination N, we may wake up in cycle N+2.

	// Wait until the current sweep termination, mark, and mark
	// termination complete.
	n := atomic.Load(&work.cycles)
	gcWaitOnMark(n)

	// We're now in sweep N or later. Trigger GC cycle N+1, which
	// will first finish sweep N if necessary and then enter sweep
	// termination N+1.
	gcStart(gcTrigger{kind: gcTriggerCycle, n: n + 1})

	// Wait for mark termination N+1 to complete.
	gcWaitOnMark(n + 1)

	// Finish sweep N+1 before returning. We do this both to
	// complete the cycle and because runtime.GC() is often used
	// as part of tests and benchmarks to get the system into a
	// relatively stable and isolated state.
	for atomic.Load(&work.cycles) == n+1 && sweepone() != ^uintptr(0) {
		sweep.nbgsweep++
		Gosched()
	}

	// Callers may assume that the heap profile reflects the
	// just-completed cycle when this returns (historically this
	// happened because this was a STW GC), but right now the
	// profile still reflects mark termination N, not N+1.
	//
	// As soon as all of the sweep frees from cycle N+1 are done,
	// we can go ahead and publish the heap profile.
	//
	// First, wait for sweeping to finish. (We know there are no
	// more spans on the sweep queue, but we may be concurrently
	// sweeping spans, so we have to wait.)
	for atomic.Load(&work.cycles) == n+1 && atomic.Load(&mheap_.sweepers) != 0 {
		Gosched()
	}

	// Now we're really done with sweeping, so we can publish the
	// stable heap profile. Only do this if we haven't already hit
	// another mark termination.
	mp := acquirem()
	cycle := atomic.Load(&work.cycles)
	if cycle == n+1 || (gcphase == _GCmark && cycle == n+2) {
		mProf_PostSweep()
	}
	releasem(mp)
}

// gcWaitOnMark blocks until GC finishes the Nth mark phase. If GC has
// already completed this mark phase, it returns immediately.
func gcWaitOnMark(n uint32) {
	for {
		// Disable phase transitions.
		lock(&work.sweepWaiters.lock)
		nMarks := atomic.Load(&work.cycles)
		if gcphase != _GCmark {
			// We've already completed this cycle's mark.
			nMarks++
		}
		if nMarks > n {
			// We're done.
			unlock(&work.sweepWaiters.lock)
			return
		}

		// Wait until sweep termination, mark, and mark
		// termination of cycle N complete.
		work.sweepWaiters.list.push(getg())
		goparkunlock(&work.sweepWaiters.lock, waitReasonWaitForGCCycle, traceEvGoBlock, 1)
	}
}

// gcMode indicates how concurrent a GC cycle should be.
type gcMode int

const (
	gcBackgroundMode gcMode = iota // concurrent GC and sweep
	gcForceMode                    // stop-the-world GC now, concurrent sweep
	gcForceBlockMode               // stop-the-world GC now and STW sweep (forced by user)
)

// A gcTrigger is a predicate for starting a GC cycle. Specifically,
// it is an exit condition for the _GCoff phase.
type gcTrigger struct {
	kind gcTriggerKind
	now  int64  // gcTriggerTime: current time
	n    uint32 // gcTriggerCycle: cycle number to start
}

type gcTriggerKind int

const (
	// gcTriggerAlways indicates that a cycle should be started
	// unconditionally, even if GOGC is off or we're in a cycle
	// right now. This cannot be consolidated with other cycles.
	gcTriggerAlways gcTriggerKind = iota

	// gcTriggerHeap indicates that a cycle should be started when
	// the heap size reaches the trigger heap size computed by the
	// controller.
	gcTriggerHeap

	// gcTriggerTime indicates that a cycle should be started when
	// it's been more than forcegcperiod nanoseconds since the
	// previous GC cycle.
	gcTriggerTime

	// gcTriggerCycle indicates that a cycle should be started if
	// we have not yet started cycle number gcTrigger.n (relative
	// to work.cycles).
	gcTriggerCycle
)

// test reports whether the trigger condition is satisfied, meaning
// that the exit condition for the _GCoff phase has been met. The exit
// condition should be tested when allocating.
func (t gcTrigger) test() bool {
	if !memstats.enablegc || panicking != 0 {
		return false
	}
	if t.kind == gcTriggerAlways {
		return true
	}
	if gcphase != _GCoff {
		return false
	}
	switch t.kind {
	case gcTriggerHeap:
		// Non-atomic access to heap_live for performance. If
		// we are going to trigger on this, this thread just
		// atomically wrote heap_live anyway and we'll see our
		// own write.
		return memstats.heap_live >= memstats.gc_trigger
	case gcTriggerTime:
		if gcpercent < 0 {
			return false
		}
		lastgc := int64(atomic.Load64(&memstats.last_gc_nanotime))
		return lastgc != 0 && t.now-lastgc > forcegcperiod
	case gcTriggerCycle:
		// t.n > work.cycles, but accounting for wraparound.
		return int32(t.n-work.cycles) > 0
	}
	return true
}

// gcStart starts the GC. It transitions from _GCoff to _GCmark (if debug.gcstoptheworld == 0) or performs all of GC (if debug.gcstoptheworld != 0).
// This may return without performing this transition in some cases, such as when called on a system stack or with locks held.
// gcStart启动GC。它从_GCoff转换到_GCmark（如果debug.gcstoptheworld==0）或执行所有GC（如果debug.gcstoptheworld！=0）。
// 在某些情况下，这可能会返回而不执行此转换，例如在系统堆栈上调用或持有锁时。
func gcStart(trigger gcTrigger) {
	// Since this is called from malloc and malloc is called in
	// the guts of a number of libraries that might be holding
	// locks, don't attempt to start GC in non-preemptible or
	// potentially unstable situations.
	// 判断当前G是否可抢占, 不可抢占时不触发GC
	mp := acquirem()
	if gp := getg(); gp == mp.g0 || mp.locks > 1 || mp.preemptoff != "" {
		releasem(mp)
		return
	}
	releasem(mp)
	mp = nil

	// Pick up the remaining unswept/not being swept spans concurrently
	//
	// This shouldn't happen if we're being invoked in background
	// mode since proportional sweep should have just finished
	// sweeping everything, but rounding errors, etc, may leave a
	// few spans unswept. In forced mode, this is necessary since
	// GC can be forced at any point in the sweeping cycle.
	//
	// We check the transition condition continuously here in case
	// this G gets delayed in to the next GC cycle.
	// 并行清扫上一轮GC未清扫的span
	for trigger.test() && sweepone() != ^uintptr(0) {
		sweep.nbgsweep++
	}

	// Perform GC initialization and the sweep termination
	// transition.
	// 上锁, 然后重新检查gcTrigger的条件是否成立, 不成立时不触发GC
	semacquire(&work.startSema)
	// Re-check transition condition under transition lock.
	if !trigger.test() {
		semrelease(&work.startSema)
		return
	}

	// For stats, check if this GC was forced by the user.
	// 记录是否强制触发, gcTriggerCycle是runtime.GC用的
	work.userForced = trigger.kind == gcTriggerAlways || trigger.kind == gcTriggerCycle

	// In gcstoptheworld debug mode, upgrade the mode accordingly.
	// We do this after re-checking the transition condition so
	// that multiple goroutines that detect the heap trigger don't
	// start multiple STW GCs.
	// 判断是否指定了禁止并行GC的参数
	mode := gcBackgroundMode
	if debug.gcstoptheworld == 1 {
		mode = gcForceMode
	} else if debug.gcstoptheworld == 2 {
		mode = gcForceBlockMode
	}

	// Ok, we're doing it! Stop everybody else
	semacquire(&worldsema)

	// 跟踪处理
	if trace.enabled {
		traceGCStart()
	}

	// Check that all Ps have finished deferred mcache flushes.
	for _, p := range allp {
		if fg := atomic.Load(&p.mcache.flushGen); fg != mheap_.sweepgen {
			println("runtime: p", p.id, "flushGen", fg, "!= sweepgen", mheap_.sweepgen)
			throw("p mcache not flushed")
		}
	}

	// 标记，启动后台扫描任务(G)
	gcBgMarkStartWorkers()

	// 重置标记相关的状态
	gcResetMarkState()

	// 重置参数
	work.stwprocs, work.maxprocs = gomaxprocs, gomaxprocs
	if work.stwprocs > ncpu {
		// This is used to compute CPU time of the STW phases,
		// so it can't be more than ncpu, even if GOMAXPROCS is.
		work.stwprocs = ncpu
	}
	work.heap0 = atomic.Load64(&memstats.heap_live)
	work.pauseNS = 0
	work.mode = mode

	// 记录开始时间
	now := nanotime()
	work.tSweepTerm = now
	work.pauseStart = now
	if trace.enabled {
		traceGCSTWStart(1)
	}
	// 停止所有运行中的G, 并禁止它们运行
	systemstack(stopTheWorldWithSema)

	// !!!!!!!!!!!!!!!!
	// 世界已停止(STW)...
	// !!!!!!!!!!!!!!!!

	// Finish sweep before we start concurrent scan.
	// 清扫上一轮GC未清扫的span, 确保上一轮GC已完成
	systemstack(func() {
		finishsweep_m()
	})
	// clearpools before we start the GC. If we wait they memory will not be
	// reclaimed until the next GC cycle.
	// 清扫sched.sudogcache和sched.deferpool
	clearpools()

	// 增加GC计数
	work.cycles++

	// 标记新一轮GC已开始
	gcController.startCycle()
	work.heapGoal = memstats.next_gc

	// In STW mode, disable scheduling of user Gs.
	// This may also disable scheduling of this goroutine, so it may block as soon as we start the world again.
	//在STW模式下，禁止用户G的调度。
	//这也可能会禁用此goroutine的调度，因此它可能会在我们再次启动时被阻止。
	if mode != gcBackgroundMode {
		schedEnableUser(false)
	}

	// Enter concurrent mark phase and enable
	// write barriers.
	//
	// Because the world is stopped, all Ps will
	// observe that write barriers are enabled by
	// the time we start the world and begin
	// scanning.
	//
	// Write barriers must be enabled before assists are
	// enabled because they must be enabled before
	// any non-leaf heap objects are marked. Since
	// allocations are blocked until assists can
	// happen, we want enable assists as early as
	// possible.
	// 设置全局变量中的GC状态为_GCmark，然后启用写屏障
	setGCPhase(_GCmark)

	// 重置后台标记任务的计数
	gcBgMarkPrepare() // Must happen before assist enable.
	// 计算扫描根对象的任务数量
	gcMarkRootPrepare()

	// Mark all active tinyalloc blocks. Since we're
	// allocating from these, they need to be black like
	// other allocations. The alternative is to blacken
	// the tiny block on every allocation from it, which
	// would slow down the tiny allocator.
	// 标记所有tiny-alloc等待合并的对象
	gcMarkTinyAllocs()

	// At this point all Ps have enabled the write
	// barrier, thus maintaining the no white to
	// black invariant. Enable mutator assists to
	// put back-pressure on fast allocating
	// mutators.
	// 启用辅助GC
	atomic.Store(&gcBlackenEnabled, 1)

	// Assists and workers can start the moment we start the world.
	// 记录标记开始的时间
	gcController.markStartTime = now

	// Concurrent mark.
	// 重新启动世界，前面创建的后台标记任务会开始工作, 所有后台标记任务都完成工作后, 进入完成标记阶段
	systemstack(func() {
		now = startTheWorldWithSema(trace.enabled)
		work.pauseNS += now - work.pauseStart
		work.tMark = now
	})

	// !!!!!!!!!!!!!!!
	// 世界已重新启动...
	// !!!!!!!!!!!!!!!

	// In STW mode, we could block the instant systemstack returns, so don't do anything important here.
	// Make sure we block rather than returning to user code.
	// 在STW模式下，我们可以阻止即时systemstack返回，所以这里不要做任何重要的事情。
	// 确保我们阻止而不是返回到用户代码。
	if mode != gcBackgroundMode {
		Gosched()
	}

	semrelease(&work.startSema)
}

// gcMarkDoneFlushed counts the number of P's with flushed work.
//
// Ideally this would be a captured local in gcMarkDone, but forEachP
// escapes its callback closure, so it can't capture anything.
//
// This is protected by markDoneSema.
var gcMarkDoneFlushed uint32

// debugCachedWork enables extra checks for debugging premature mark
// termination.
//
// For debugging issue #27993.
const debugCachedWork = false

// gcWorkPauseGen is for debugging the mark completion algorithm.
// gcWork put operations spin while gcWork.pauseGen == gcWorkPauseGen.
// Only used if debugCachedWork is true.
//
// For debugging issue #27993.
var gcWorkPauseGen uint32 = 1

// gcMarkDone transitions the GC from mark to mark termination if all
// reachable objects have been marked (that is, there are no grey
// objects and can be no more in the future). Otherwise, it flushes
// all local work to the global queues where it can be discovered by
// other workers.
//
// This should be called when all local mark work has been drained and
// there are no remaining workers. Specifically, when
//
//   work.nwait == work.nproc && !gcMarkWorkAvailable(p)
//
// The calling context must be preemptible.
//
// Flushing local work is important because idle Ps may have local
// work queued. This is the only way to make that work visible and
// drive GC to completion.
//
// It is explicitly okay to have write barriers in this function. If
// it does transition to mark termination, then all reachable objects
// have been marked, so the write barrier cannot shade any more
// objects.
/*
gcMarkDone会将mark1阶段进入到mark2阶段， mark2阶段进入到mark termination阶段
mark1阶段：包括所有root标记，全局缓存队列和本地缓存队列
mark2阶段：本地缓存队列会被禁用

在所有后台标记任务都把标记队列消费完毕时, 会执行gcMarkDone函数准备进入完成标记阶段(mark termination):
在并行GC中gcMarkDone会被执行两次, 第一次会禁止本地标记队列然后重新开始后台标记任务, 第二次会进入完成标记阶段(mark termination)。
*/
func gcMarkDone() {
	// Ensure only one thread is running the ragged barrier at a
	// time.
	semacquire(&work.markDoneSema)

top:
	// Re-check transition condition under transition lock.
	//
	// It's critical that this checks the global work queues are
	// empty before performing the ragged barrier. Otherwise,
	// there could be global work that a P could take after the P
	// has passed the ragged barrier.
	if !(gcphase == _GCmark && work.nwait == work.nproc && !gcMarkWorkAvailable(nil)) {
		semrelease(&work.markDoneSema)
		return
	}

	// Flush all local buffers and collect flushedWork flags.
	gcMarkDoneFlushed = 0
	// 切换到g0执行，本地缓存上传到全局的操作
	systemstack(func() {
		gp := getg().m.curg
		// Mark the user stack as preemptible so that it may be scanned.
		// Otherwise, our attempt to force all P's to a safepoint could
		// result in a deadlock as we attempt to preempt a worker that's
		// trying to preempt us (e.g. for a stack scan).
		// 切换状态，从工作到等待
		casgstatus(gp, _Grunning, _Gwaiting)
		forEachP(func(_p_ *p) {
			// Flush the write barrier buffer, since this may add work to the gcWork.
			// 刷新写屏障缓冲区，因为这可能会向gcWork添加功。
			wbBufFlush1(_p_)
			// For debugging, shrink the write barrier
			// buffer so it flushes immediately.
			// wbBuf.reset will keep it at this size as
			// long as throwOnGCWork is set.
			if debugCachedWork {
				b := &_p_.wbBuf
				b.end = uintptr(unsafe.Pointer(&b.buf[wbBufEntryPointers]))
				b.debugGen = gcWorkPauseGen
			}
			// Flush the gcWork, since this may create global work
			// and set the flushedWork flag.
			//
			// TODO(austin): Break up these workbufs to
			// better distribute work.
			_p_.gcw.dispose()
			// Collect the flushedWork flag.
			if _p_.gcw.flushedWork {
				atomic.Xadd(&gcMarkDoneFlushed, 1)
				_p_.gcw.flushedWork = false
			} else if debugCachedWork {
				// For debugging, freeze the gcWork
				// until we know whether we've reached
				// completion or not. If we think
				// we've reached completion, but
				// there's a paused gcWork, then
				// that's a bug.
				_p_.gcw.pauseGen = gcWorkPauseGen
				// Capture the G's stack.
				for i := range _p_.gcw.pauseStack {
					_p_.gcw.pauseStack[i] = 0
				}
				callers(1, _p_.gcw.pauseStack[:])
			}
		})
		casgstatus(gp, _Gwaiting, _Grunning)
	})

	if gcMarkDoneFlushed != 0 {
		if debugCachedWork {
			// Release paused gcWorks.
			atomic.Xadd(&gcWorkPauseGen, 1)
		}
		// More grey objects were discovered since the
		// previous termination check, so there may be more
		// work to do. Keep going. It's possible the
		// transition condition became true again during the
		// ragged barrier, so re-check it.
		goto top
	}

	if debugCachedWork {
		throwOnGCWork = true
		// Release paused gcWorks. If there are any, they
		// should now observe throwOnGCWork and panic.
		atomic.Xadd(&gcWorkPauseGen, 1)
	}

	// There was no global work, no local work, and no Ps
	// communicated work since we took markDoneSema. Therefore
	// there are no grey objects and no more objects can be
	// shaded. Transition to mark termination.
	// 记录完成标记阶段开始的时间和STW开始的时间
	now := nanotime()
	work.tMarkTerm = now
	work.pauseStart = now
	// 禁止G被抢占
	getg().m.preemptoff = "gcing"
	if trace.enabled {
		traceGCSTWStart(0)
	}
	// 停止所有运行中的G, 并禁止它们运行
	systemstack(stopTheWorldWithSema)
	// The gcphase is _GCmark, it will transition to _GCmarktermination
	// below. The important thing is that the wb remains active until
	// all marking is complete. This includes writes made by the GC.

	if debugCachedWork {
		// For debugging, double check that no work was added after we
		// went around above and disable write barrier buffering.
		for _, p := range allp {
			gcw := &p.gcw
			if !gcw.empty() {
				printlock()
				print("runtime: P ", p.id, " flushedWork ", gcw.flushedWork)
				if gcw.wbuf1 == nil {
					print(" wbuf1=<nil>")
				} else {
					print(" wbuf1.n=", gcw.wbuf1.nobj)
				}
				if gcw.wbuf2 == nil {
					print(" wbuf2=<nil>")
				} else {
					print(" wbuf2.n=", gcw.wbuf2.nobj)
				}
				print("\n")
				if gcw.pauseGen == gcw.putGen {
					println("runtime: checkPut already failed at this generation")
				}
				throw("throwOnGCWork")
			}
		}
	} else {
		// For unknown reasons (see issue #27993), there is
		// sometimes work left over when we enter mark
		// termination. Detect this and resume concurrent
		// mark. This is obviously unfortunate.
		//
		// Switch to the system stack to call wbBufFlush1,
		// though in this case it doesn't matter because we're
		// non-preemptible anyway.
		restart := false
		systemstack(func() {
			for _, p := range allp {
				wbBufFlush1(p)
				if !p.gcw.empty() {
					restart = true
					break
				}
			}
		})
		if restart {
			getg().m.preemptoff = ""
			systemstack(func() {
				now := startTheWorldWithSema(true)
				work.pauseNS += now - work.pauseStart
			})
			goto top
		}
	}

	// Disable assists and background workers. We must do this before waking blocked assists.
	// 禁止辅助GC和后台标记任务的运行
	atomic.Store(&gcBlackenEnabled, 0)

	// Wake all blocked assists. These will run when we start the world again.
	// 唤醒所有因为辅助GC而休眠的G
	gcWakeAllAssists()

	// Likewise, release the transition lock. Blocked
	// workers and assists will run when we start the
	// world again.
	semrelease(&work.markDoneSema)

	// In STW mode, re-enable user goroutines. These will be
	// queued to run after we start the world.
	schedEnableUser(true)

	// endCycle depends on all gcWork cache stats being flushed.
	// The termination algorithm above ensured that up to
	// allocations since the ragged barrier.
	// 计算下一次触发gc需要的heap大小
	nextTriggerRatio := gcController.endCycle()

	// Perform mark termination. This will restart the world.
	// 进入完成标记阶段, 会重新启动世界
	gcMarkTermination(nextTriggerRatio)
}

// 结束标记，并进行清扫等工作
func gcMarkTermination(nextTriggerRatio float64) {
	// World is stopped.
	// Start marktermination which includes enabling the write barrier.
	// 禁止辅助GC和后台标记任务的运行
	atomic.Store(&gcBlackenEnabled, 0)
	// 设置当前GC阶段到完成标记阶段, 并启用写屏障
	setGCPhase(_GCmarktermination)

	// 记录开始时间
	work.heap1 = memstats.heap_live
	startTime := nanotime()

	// 禁止G被抢占
	mp := acquirem()
	mp.preemptoff = "gcing"
	_g_ := getg()
	_g_.m.traceback = 2
	// 设置G的状态为等待中这样它的栈可以被扫描
	gp := _g_.m.curg
	// 设置当前g的状态为waiting状态
	casgstatus(gp, _Grunning, _Gwaiting)
	gp.waitreason = waitReasonGarbageCollection

	// Run gc on the g0 stack. We do this so that the g stack
	// we're currently running on will no longer change. Cuts
	// the root set down a bit (g0 stacks are not scanned, and
	// we don't need to scan gc's internal state).  We also
	// need to switch to g0 so we can shrink the stack.
	// 切换到g0运行
	systemstack(func() {
		// 通过g0扫描当前g的栈。开始STW中的标记
		gcMark(startTime)
		// 必须立刻返回, 因为外面的G的栈有可能被移动, 不能在这之后访问外面的变量
		// Must return immediately.
		// The outer function's stack may have moved
		// during gcMark (it shrinks stacks, including the
		// outer function's stack), so we must not refer
		// to any of its variables. Return back to the
		// non-system stack to pick up the new addresses
		// before continuing.
	})

	// 重新切换到g0运行
	systemstack(func() {
		work.heap2 = work.bytesMarked
		// 如果启用了checkmark则执行检查, 检查是否所有可到达的对象都有标记
		if debug.gccheckmark > 0 {
			// Run a full non-parallel, stop-the-world
			// mark using checkmark bits, to check that we
			// didn't forget to mark anything during the
			// concurrent mark process.
			// 如果启用了gccheckmark，则检查所有可达对象是否都有标记
			gcResetMarkState()
			initCheckmarks()
			gcw := &getg().m.p.ptr().gcw
			gcDrain(gcw, 0)
			wbBufFlush1(getg().m.p.ptr())
			gcw.dispose()
			clearCheckmarks()
		}

		// marking is complete so we can turn the write barrier off
		// 设置gc的阶段标识，GCoff时会关闭写屏障
		setGCPhase(_GCoff)
		// 开始清扫.唤醒后台清扫任务, 将在STW结束后开始运行
		gcSweep(work.mode)
	})

	// 设置G的状态为运行中
	_g_.m.traceback = 0
	casgstatus(gp, _Gwaiting, _Grunning)

	// 跟踪处理
	if trace.enabled {
		traceGCDone()
	}

	// all done
	mp.preemptoff = ""

	if gcphase != _GCoff {
		throw("gc done but gcphase != _GCoff")
	}

	// Update GC trigger and pacing for the next cycle.
	// 更新下次出发gc的增长比。更新下一次触发gc需要的heap大小(gc_trigger)
	gcSetTriggerRatio(nextTriggerRatio)

	// Update timing memstats
	// 更新用时
	now := nanotime()
	sec, nsec, _ := time_now()
	unixNow := sec*1e9 + int64(nsec)
	work.pauseNS += now - work.pauseStart
	work.tEnd = now
	atomic.Store64(&memstats.last_gc_unix, uint64(unixNow)) // must be Unix time to make sense to user
	atomic.Store64(&memstats.last_gc_nanotime, uint64(now)) // monotonic time for us
	memstats.pause_ns[memstats.numgc%uint32(len(memstats.pause_ns))] = uint64(work.pauseNS)
	memstats.pause_end[memstats.numgc%uint32(len(memstats.pause_end))] = uint64(unixNow)
	memstats.pause_total_ns += uint64(work.pauseNS)

	// Update work.totaltime.
	// 更新所用cpu记录
	sweepTermCpu := int64(work.stwprocs) * (work.tMark - work.tSweepTerm)
	// We report idle marking time below, but omit it from the
	// overall utilization here since it's "free".
	markCpu := gcController.assistTime + gcController.dedicatedMarkTime + gcController.fractionalMarkTime
	markTermCpu := int64(work.stwprocs) * (work.tEnd - work.tMarkTerm)
	cycleCpu := sweepTermCpu + markCpu + markTermCpu
	work.totaltime += cycleCpu

	// Compute overall GC CPU utilization.
	totalCpu := sched.totaltime + (now-sched.procresizetime)*int64(gomaxprocs)
	memstats.gc_cpu_fraction = float64(work.totaltime) / float64(totalCpu)

	// Reset sweep state.
	// 重置清扫的状态
	sweep.nbgsweep = 0
	sweep.npausesweep = 0

	// 如果是强制开启的gc，标识增加。统计强制开始GC的次数
	if work.userForced {
		memstats.numforcedgc++
	}

	// Bump GC cycle count and wake goroutines waiting on sweep.
	// 统计执行GC的次数然后唤醒等待清扫的G
	lock(&work.sweepWaiters.lock)
	memstats.numgc++
	injectglist(&work.sweepWaiters.list)
	unlock(&work.sweepWaiters.lock)

	// Finish the current heap profiling cycle and start a new
	// heap profiling cycle. We do this before starting the world
	// so events don't leak into the wrong cycle.
	// 性能统计用
	mProf_NextCycle()

	// 重新启动世界
	systemstack(func() { startTheWorldWithSema(true) })

	// !!!!!!!!!!!!!!!
	// 世界已重新启动...
	// !!!!!!!!!!!!!!!

	// Flush the heap profile so we can start a new cycle next GC.
	// This is relatively expensive, so we don't do it with the
	// world stopped.
	// 性能统计用
	mProf_Flush()

	// Prepare workbufs for freeing by the sweeper. We do this
	// asynchronously because it can take non-trivial time.
	// 移动标记队列使用的缓冲区到自由列表, 使得它们可以被回收
	prepareFreeWorkbufs()

	// Free stack spans. This must be done between GC cycles.
	// 释放未使用的栈
	systemstack(freeStackSpans)

	// Ensure all mcaches are flushed. Each P will flush its own
	// mcache before allocating, but idle Ps may not. Since this
	// is necessary to sweep all spans, we need to ensure all
	// mcaches are flushed before we start the next GC cycle.
	systemstack(func() {
		forEachP(func(_p_ *p) {
			_p_.mcache.prepareForSweep()
		})
	})

	// Print gctrace before dropping worldsema. As soon as we drop
	// worldsema another cycle could start and smash the stats
	// we're trying to print.
	// 除错用
	if debug.gctrace > 0 {
		util := int(memstats.gc_cpu_fraction * 100)

		var sbuf [24]byte
		printlock()
		print("gc ", memstats.numgc,
			" @", string(itoaDiv(sbuf[:], uint64(work.tSweepTerm-runtimeInitTime)/1e6, 3)), "s ",
			util, "%: ")
		prev := work.tSweepTerm
		for i, ns := range []int64{work.tMark, work.tMarkTerm, work.tEnd} {
			if i != 0 {
				print("+")
			}
			print(string(fmtNSAsMS(sbuf[:], uint64(ns-prev))))
			prev = ns
		}
		print(" ms clock, ")
		for i, ns := range []int64{sweepTermCpu, gcController.assistTime, gcController.dedicatedMarkTime + gcController.fractionalMarkTime, gcController.idleMarkTime, markTermCpu} {
			if i == 2 || i == 3 {
				// Separate mark time components with /.
				print("/")
			} else if i != 0 {
				print("+")
			}
			print(string(fmtNSAsMS(sbuf[:], uint64(ns))))
		}
		print(" ms cpu, ",
			work.heap0>>20, "->", work.heap1>>20, "->", work.heap2>>20, " MB, ",
			work.heapGoal>>20, " MB goal, ",
			work.maxprocs, " P")
		if work.userForced {
			print(" (forced)")
		}
		print("\n")
		printunlock()
	}

	semrelease(&worldsema)
	// Careful: another GC cycle may start now.

	// 重新允许当前的G被抢占
	releasem(mp)
	mp = nil

	// now that gc is done, kick off finalizer thread if needed
	// 如果是并行GC, 让当前M继续运行(会回到gcBgMarkWorker然后休眠)
	// 如果不是并行GC, 则让当前M开始调度
	if !concurrentSweep {
		// give the queued finalizers, if any, a chance to run
		Gosched()
	}
}

// gcBgMarkStartWorkers prepares background mark worker goroutines.
// These goroutines will not run until the mark phase, but they must
// be started while the work is not stopped and from a regular G
// stack. The caller must hold worldsema.
// 函数gcBgMarkStartWorkers用于启动后台标记任务, 先分别对每个P启动一个
func gcBgMarkStartWorkers() {
	// Background marking is performed by per-P G's. Ensure that
	// each P has a background GC G.
	for _, p := range allp {
		// 如果已启动则不重复启动
		if p.gcBgMarkWorker == 0 {
			go gcBgMarkWorker(p)
			// 启动后等待该任务通知信号量bgMarkReady再继续
			notetsleepg(&work.bgMarkReady, -1)
			noteclear(&work.bgMarkReady)
		}
	}
}

// gcBgMarkPrepare sets up state for background marking.
// Mutator assists must not yet be enabled.
// 函数会重置后台标记任务的计数
func gcBgMarkPrepare() {
	// Background marking will stop when the work queues are empty
	// and there are no more workers (note that, since this is
	// concurrent, this may be a transient state, but mark
	// termination will clean it up). Between background workers
	// and assists, we don't really know how many workers there
	// will be, so we pretend to have an arbitrarily large number
	// of workers, almost all of which are "waiting". While a
	// worker is working it decrements nwait. If nproc == nwait,
	// there are no workers.
	work.nproc = ^uint32(0)
	work.nwait = ^uint32(0)
}

/*
在 gcBgMarkStartWorkers 中我们看到，它会遍历所有的 P ，然后为每个 P 创建一个负责 Mark Work 的 G，
这里虽然为每个 P 启动了一个后台标记任务, 但是不可能每个 P 都会去执行标记任务，后台标记任务默认资源占用率是 25%，
所以 gcBgMarkWorker 中会初始化 park 并将 G 和 P 的 gcBgMarkWorker 进行绑定后进行休眠。
*/
func gcBgMarkWorker(_p_ *p) {
	gp := getg()

	// 用于休眠后重新获取P的构造体
	type parkInfo struct {
		m      muintptr // Release this m on park.
		attach puintptr // If non-nil, attach to this p on park.
	}
	// We pass park to a gopark unlock function, so it can't be on
	// the stack (see gopark). Prevent deadlock from recursively
	// starting GC by disabling preemption.
	gp.m.preemptoff = "GC worker init"
	park := new(parkInfo)
	gp.m.preemptoff = ""

	// 设置当前的M并禁止抢占
	park.m.set(acquirem())
	// 设置当前的P(需要关联到的P)
	park.attach.set(_p_)
	// Inform gcBgMarkStartWorkers that this worker is ready.
	// After this point, the background mark worker is scheduled
	// cooperatively by gcController.findRunnable. Hence, it must
	// never be preempted, as this would put it into _Grunnable
	// and put it on a run queue. Instead, when the preempt flag
	// is set, this puts itself into _Gwaiting to be woken up by
	// gcController.findRunnable at the appropriate time.
	/*
	通知gcBgMarkStartWorkers此工作人员已准备就绪。
	在此之后，背景标记工作进程由gcController.findRunnable协同调度。
	因此，它决不能被抢占，因为这会将它放入_Grunnable并放入运行队列。
	相反，当设置了preempt标志时，这会将自身置于等待gcController.findRunnable在适当的时间唤醒的状态。

	调度过程中调用stopm()睡眠后，通过 notewakeup(&mp.park)恢复m的执行，并从stopm()的位置开始执行，重新调度。
	*/
	notewakeup(&work.bgMarkReady)

	for {
		// Go to sleep until woken by gcController.findRunnable.
		// We can't releasem yet since even the call to gopark may be preempted.
		/*
		//进入睡眠状态，直到被gcController.findRunnable唤醒。
		//我们还不能释放，因为gopark可能被抢占。

		让当前 G 进入休眠
		将当前传入的 P 打包成 parkInfo ，然后调用 gopark 让当前 G 进入休眠，在休眠前会将 P 的 gcBgMarkWorker 与 G 进行绑定，等待唤醒；
		*/
		gopark(func(g *g, parkp unsafe.Pointer) bool {
			park := (*parkInfo)(parkp)

			// The worker G is no longer running, so it's now safe to allow preemption.
			// worker G不再运行，因此现在允许抢占是安全的。重新允许抢占
			releasem(park.m.ptr())

			// If the worker isn't attached to its P,
			// attach now. During initialization and after
			// a phase change, the worker may have been
			// running on a different P. As soon as we
			// attach, the owner P may schedule the
			// worker, so this must be done after the G is
			// stopped.
			// 设置关联的 P
			// 把当前的G设到P的gcBgMarkWorker成员, 下次findRunnableGCWorker会使用
			// 设置失败时不休眠
			if park.attach != 0 {
				p := park.attach.ptr()
				park.attach.set(nil)
				// cas the worker because we may be racing with a new worker starting on this P.
				// 把当前的G设到P的gcBgMarkWorker成员，这步主要是为每个P启动一个G做后台标记任务
				if !p.gcBgMarkWorker.cas(0, guintptr(unsafe.Pointer(g))) {
					// The P got a new worker.
					// Exit this worker.
					return false
				}
			}
			return true
		}, unsafe.Pointer(park), waitReasonGCWorkerIdle, traceEvGoBlock, 0)

		// Loop until the P dies and disassociates this
		// worker (the P may later be reused, in which case
		// it will get a new worker) or we failed to associate.
		// 循环，直到P死亡并解除此辅助进程的关联（P稍后可能会被重用，在这种情况下，它将获得一个新的辅助进程），或者我们无法关联。
		// 检查P的gcBgMarkWorker是否和当前的G一致, 不一致时结束当前的任务
		if _p_.gcBgMarkWorker.ptr() != gp {
			break
		}

		// Disable preemption so we can use the gcw. If the
		// scheduler wants to preempt us, we'll stop draining,
		// dispose the gcw, and then preempt.
		// 禁止G被抢占
		park.m.set(acquirem())

		if gcBlackenEnabled == 0 {
			throw("gcBgMarkWorker: blackening not enabled")
		}

		// 记录开始时间
		startTime := nanotime()
		_p_.gcMarkWorkerStartTime = startTime

		// incnwait 来检查是否是最后一个 worker
		decnwait := atomic.Xadd(&work.nwait, -1)
		if decnwait == work.nproc {
			println("runtime: work.nwait=", decnwait, "work.nproc=", work.nproc)
			throw("work.nwait was > work.nproc")
		}

		// 切换到g0运行
		systemstack(func() {
			// Mark our goroutine preemptible so its stack
			// can be scanned. This lets two mark workers
			// scan each other (otherwise, they would
			// deadlock). We must not modify anything on
			// the G stack. However, stack shrinking is
			// disabled for mark workers, so it is safe to
			// read from the G stack.
			// 设置G的状态为等待中这样它的栈可以被扫描
			casgstatus(gp, _Grunning, _Gwaiting)
			// 判断后台标记任务的模式
			switch _p_.gcMarkWorkerMode {
			default:
				throw("gcBgMarkWorker: unexpected gcMarkWorkerMode")
			case gcMarkWorkerDedicatedMode:
				// P 专门负责标记对象，不会被调度器抢占；
				gcDrain(&_p_.gcw, gcDrainUntilPreempt|gcDrainFlushBgCredit)
				if gp.preempt {
					// This is a useful signal to kick everything out of the run queue so it can run somewhere else.
					// 这是一个有用的信号，可以将所有内容从运行队列中踢出，以便它可以在其他地方运行。
					lock(&sched.lock)
					for {
						gp, _ := runqget(_p_)
						if gp == nil {
							break
						}
						globrunqput(gp)
					}
					unlock(&sched.lock)
				}
				// Go back to draining, this time without preemption.
				// 继续执行标记
				gcDrain(&_p_.gcw, gcDrainFlushBgCredit)
			case gcMarkWorkerFractionalMode:
				gcDrain(&_p_.gcw, gcDrainFractional|gcDrainUntilPreempt|gcDrainFlushBgCredit)
			case gcMarkWorkerIdleMode:
				// 执行标记, 直到被抢占或者达到一定的量
				gcDrain(&_p_.gcw, gcDrainIdle|gcDrainUntilPreempt|gcDrainFlushBgCredit)
			}
			// 恢复G的状态到运行中
			casgstatus(gp, _Gwaiting, _Grunning)
		})

		// Account for time.
		// 累加所用时间
		duration := nanotime() - startTime
		switch _p_.gcMarkWorkerMode {
		case gcMarkWorkerDedicatedMode:
			atomic.Xaddint64(&gcController.dedicatedMarkTime, duration)
			atomic.Xaddint64(&gcController.dedicatedMarkWorkersNeeded, 1)
		case gcMarkWorkerFractionalMode:
			atomic.Xaddint64(&gcController.fractionalMarkTime, duration)
			atomic.Xaddint64(&_p_.gcFractionalMarkTime, duration)
		case gcMarkWorkerIdleMode:
			atomic.Xaddint64(&gcController.idleMarkTime, duration)
		}

		// Was this the last worker and did we run out of work?
		// 这是最后一个工人吗？我们失业了吗？
		incnwait := atomic.Xadd(&work.nwait, +1)
		if incnwait > work.nproc {
			println("runtime: p.gcMarkWorkerMode=", _p_.gcMarkWorkerMode,
				"work.nwait=", incnwait, "work.nproc=", work.nproc)
			throw("work.nwait > work.nproc")
		}

		// If this worker reached a background mark completion point, signal the main GC goroutine.
		/*
		gcBgMarkWorker 会根据 incnwait 来检查是否是最后一个 worker，
		然后调用 gcMarkWorkAvailable 函数来校验 gcwork的任务和全局任务是否已经全部都处理完了，
		如果都确认没问题，那么调用 gcMarkDone 进入完成标记阶段。
		*/
		// 判断是否所有后台标记任务都完成, 并且没有更多的任务
		if incnwait == work.nproc && !gcMarkWorkAvailable(nil) {
			// Make this G preemptible and disassociate it as the worker for this P so
			// findRunnableGCWorker doesn't try to schedule it.
			// 取消和P的关联
			_p_.gcBgMarkWorker.set(nil)
			// 允许G被抢占
			releasem(park.m.ptr())
			// 准备进入完成标记阶段
			gcMarkDone()

			// Disable preemption and prepare to reattach to the P.
			// We may be running on a different P at this point, so we can't reattach until this G is parked.
			// 休眠之前会重新关联P
			// 因为上面允许被抢占, 到这里的时候可能就会变成其他P
			// 如果重新关联P失败则这个任务会结束
			park.m.set(acquirem())
			park.attach.set(_p_)
		}
	}
}

// gcMarkWorkAvailable reports whether executing a mark worker
// on p is potentially useful. p may be nil, in which case it only
// checks the global sources of work.
// gcwork的任务和全局任务是否已经全部都处理完了
func gcMarkWorkAvailable(p *p) bool {
	if p != nil && !p.gcw.empty() {
		return true
	}
	if !work.full.empty() {
		return true // global work available
	}
	if work.markrootNext < work.markrootJobs {
		return true // root scan work available
	}
	return false
}

// gcMark runs the mark (or, for concurrent GC, mark termination)
// All gcWork caches must be empty.
// STW is in effect at this point.
//TODO go:nowritebarrier
func gcMark(start_time int64) {
	if debug.allocfreetrace > 0 {
		tracegc()
	}

	if gcphase != _GCmarktermination {
		throw("in gcMark expecting to see gcphase as _GCmarktermination")
	}
	work.tstart = start_time

	// Check that there's no marking work remaining.
	if work.full != 0 || work.markrootNext < work.markrootJobs {
		print("runtime: full=", hex(work.full), " next=", work.markrootNext, " jobs=", work.markrootJobs, " nDataRoots=", work.nDataRoots, " nBSSRoots=", work.nBSSRoots, " nSpanRoots=", work.nSpanRoots, " nStackRoots=", work.nStackRoots, "\n")
		panic("non-empty mark queue after concurrent mark")
	}

	if debug.gccheckmark > 0 {
		// This is expensive when there's a large number of
		// Gs, so only do it if checkmark is also enabled.
		gcMarkRootCheck()
	}
	if work.full != 0 {
		throw("work.full != 0")
	}

	// Clear out buffers and double-check that all gcWork caches
	// are empty. This should be ensured by gcMarkDone before we
	// enter mark termination.
	//
	// TODO: We could clear out buffers just before mark if this
	// has a non-negligible impact on STW time.
	for _, p := range allp {
		// The write barrier may have buffered pointers since
		// the gcMarkDone barrier. However, since the barrier
		// ensured all reachable objects were marked, all of
		// these must be pointers to black objects. Hence we
		// can just discard the write barrier buffer.
		if debug.gccheckmark > 0 || throwOnGCWork {
			// For debugging, flush the buffer and make
			// sure it really was all marked.
			wbBufFlush1(p)
		} else {
			p.wbBuf.reset()
		}

		gcw := &p.gcw
		if !gcw.empty() {
			printlock()
			print("runtime: P ", p.id, " flushedWork ", gcw.flushedWork)
			if gcw.wbuf1 == nil {
				print(" wbuf1=<nil>")
			} else {
				print(" wbuf1.n=", gcw.wbuf1.nobj)
			}
			if gcw.wbuf2 == nil {
				print(" wbuf2=<nil>")
			} else {
				print(" wbuf2.n=", gcw.wbuf2.nobj)
			}
			print("\n")
			throw("P has cached GC work at end of mark termination")
		}
		// There may still be cached empty buffers, which we
		// need to flush since we're going to free them. Also,
		// there may be non-zero stats because we allocated
		// black after the gcMarkDone barrier.
		gcw.dispose()
	}

	throwOnGCWork = false

	cachestats()

	// Update the marked heap stat.
	memstats.heap_marked = work.bytesMarked

	// Update other GC heap size stats. This must happen after
	// cachestats (which flushes local statistics to these) and
	// flushallmcaches (which modifies heap_live).
	memstats.heap_live = work.bytesMarked
	memstats.heap_scan = uint64(gcController.scanWork)

	if trace.enabled {
		traceHeapAlloc()
	}
}

// 清扫任务.gcSweep函数会唤醒后台清扫任务:
// 后台清扫任务会在程序启动时调用的gcenable函数中启动.
func gcSweep(mode gcMode) {
	if gcphase != _GCoff {
		throw("gcSweep being done but phase is not GCoff")
	}

	// 增加sweepgen, 这样sweepSpans中两个队列角色会交换, 所有span都会变为"待清扫"的span
	lock(&mheap_.lock)
	// sweepgen在每次GC之后都会增长2，每次GC之后sweepSpans的角色都会互换
	mheap_.sweepgen += 2
	mheap_.sweepdone = 0
	if mheap_.sweepSpans[mheap_.sweepgen/2%2].index != 0 {
		// We should have drained this list during the last
		// sweep phase. We certainly need to start this phase
		// with an empty swept list.
		throw("non-empty swept list")
	}
	mheap_.pagesSwept = 0
	mheap_.sweepArenas = mheap_.allArenas
	mheap_.reclaimIndex = 0
	mheap_.reclaimCredit = 0
	unlock(&mheap_.lock)
	// 如果不是并行GC，或者强制GC
	// 如果非并行GC则在这里完成所有工作(STW中)
	if !_ConcurrentSweep || mode == gcForceBlockMode {
		// Special case synchronous sweep.
		// Record that no proportional sweeping has to happen.
		lock(&mheap_.lock)
		mheap_.sweepPagesPerByte = 0
		unlock(&mheap_.lock)
		// Sweep all spans eagerly.
		// 清扫所有的span
		for sweepone() != ^uintptr(0) {
			sweep.npausesweep++
		}
		// Free workbufs eagerly.
		// 释放所有的 workbufs
		prepareFreeWorkbufs()
		for freeSomeWbufs(false) {
		}
		// All "free" events for this mark/sweep cycle have
		// now happened, so we can make this profile cycle
		// available immediately.
		mProf_NextCycle()
		mProf_Flush()
		return
	}

	// Background sweep.
	lock(&sweep.lock)
	// 唤醒后台清扫任务,也就是 bgsweep 函数，清扫流程跟上面非并行清扫差不多
	if sweep.parked {
		sweep.parked = false
		ready(sweep.g, 0, true)
	}
	unlock(&sweep.lock)
}

// gcResetMarkState resets global state prior to marking (concurrent
// or STW) and resets the stack scan state of all Gs.
//
// This is safe to do without the world stopped because any Gs created
// during or after this will start out in the reset state.
// 重置标记相关的状态
func gcResetMarkState() {
	// This may be called during a concurrent phase, so make sure
	// allgs doesn't change.
	lock(&allglock)
	for _, gp := range allgs {
		gp.gcscandone = false  // set to true in gcphasework
		gp.gcscanvalid = false // stack has not been scanned
		gp.gcAssistBytes = 0
	}
	unlock(&allglock)

	// Clear page marks. This is just 1MB per 64GB of heap, so the
	// time here is pretty trivial.
	lock(&mheap_.lock)
	arenas := mheap_.allArenas
	unlock(&mheap_.lock)
	for _, ai := range arenas {
		ha := mheap_.arenas[ai.l1()][ai.l2()]
		for i := range ha.pageMarks {
			ha.pageMarks[i] = 0
		}
	}

	work.bytesMarked = 0
	work.initialHeapLive = atomic.Load64(&memstats.heap_live)
}

// Hooks for other packages

var poolcleanup func()

//go:linkname sync_runtime_registerPoolCleanup sync.runtime_registerPoolCleanup
func sync_runtime_registerPoolCleanup(f func()) {
	poolcleanup = f
}

// 清理sched.sudogcache和sched.deferpool, 让它们的内存可以被回收
func clearpools() {
	// clear sync.Pools
	if poolcleanup != nil {
		poolcleanup()
	}

	// Clear central sudog cache.
	// Leave per-P caches alone, they have strictly bounded size.
	// Disconnect cached list before dropping it on the floor,
	// so that a dangling ref to one entry does not pin all of them.
	lock(&sched.sudoglock)
	var sg, sgnext *sudog
	for sg = sched.sudogcache; sg != nil; sg = sgnext {
		sgnext = sg.next
		sg.next = nil
	}
	sched.sudogcache = nil
	unlock(&sched.sudoglock)

	// Clear central defer pools.
	// Leave per-P pools alone, they have strictly bounded size.
	lock(&sched.deferlock)
	for i := range sched.deferpool {
		// disconnect cached list before dropping it on the floor,
		// so that a dangling ref to one entry does not pin all of them.
		var d, dlink *_defer
		for d = sched.deferpool[i]; d != nil; d = dlink {
			dlink = d.link
			d.link = nil
		}
		sched.deferpool[i] = nil
	}
	unlock(&sched.deferlock)
}

// Timing

// itoaDiv formats val/(10**dec) into buf.
func itoaDiv(buf []byte, val uint64, dec int) []byte {
	i := len(buf) - 1
	idec := i - dec
	for val >= 10 || i >= idec {
		buf[i] = byte(val%10 + '0')
		i--
		if i == idec {
			buf[i] = '.'
			i--
		}
		val /= 10
	}
	buf[i] = byte(val + '0')
	return buf[i:]
}

// fmtNSAsMS nicely formats ns nanoseconds as milliseconds.
func fmtNSAsMS(buf []byte, ns uint64) []byte {
	if ns >= 10e6 {
		// Format as whole milliseconds.
		return itoaDiv(buf, ns/1e6, 0)
	}
	// Format two digits of precision, with at most three decimal places.
	x := ns / 1e3
	if x == 0 {
		buf[0] = '0'
		return buf[:1]
	}
	dec := 3
	for x >= 100 {
		x /= 10
		dec--
	}
	return itoaDiv(buf, x, dec)
}
