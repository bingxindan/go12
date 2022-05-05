// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Time-related runtime and pieces of package time.

package runtime

import (
	"internal/cpu"
	"unsafe"
)

// Package time knows the layout of this structure.
// If this struct changes, adjust ../time/sleep.go:/runtimeTimer.
// For GOOS=nacl, package syscall knows the layout of this structure.
// If this struct changes, adjust ../syscall/net_nacl.go:/runtimeTimer.
type timer struct {
	tb *timersBucket // the bucket the timer lives in
	i  int           // heap index

	// Timer wakes up at when, and then at when+period, ... (period > 0 only)
	// each time calling f(arg, now) in the timer goroutine, so f must be
	// a well-behaved function and not block.
	when   int64
	period int64
	f      func(interface{}, uintptr)
	arg    interface{}
	seq    uintptr
}

// timersLen is the length of timers array.
//
// Ideally, this would be set to GOMAXPROCS, but that would require
// dynamic reallocation
//
// The current value is a compromise between memory usage and performance
// that should cover the majority of GOMAXPROCS values used in the wild.
const timersLen = 64

// timers contains "per-P" timer heaps.
//
// Timers are queued into timersBucket associated with the current P,
// so each P may work with its own timers independently of other P instances.
//
// Each timersBucket may be associated with multiple P
// if GOMAXPROCS > timersLen.
var timers [timersLen]struct {
	timersBucket

	// The padding should eliminate false sharing
	// between timersBucket values.
	pad [cpu.CacheLinePadSize - unsafe.Sizeof(timersBucket{})%cpu.CacheLinePadSize]byte
}

func (t *timer) assignBucket() *timersBucket {
	id := uint8(getg().m.p.ptr().id) % timersLen
	t.tb = &timers[id].timersBucket
	return t.tb
}

//go:notinheap
type timersBucket struct {
	// 锁，多个P绑定一个tb时生效
	lock         mutex
	// 定时器检查协程
	gp           *g
	// 桶协程是否已创建
	created      bool
	// 桶内包含timer，线程休眠
	sleeping     bool
	// 桶内没有timer，协程被挂起
	rescheduling bool
	// 线程休眠超时唤醒时间
	sleepUntil   int64
	// 线程休眠信号量
	waitnote     note
	// 定时器，最小四叉堆
	t            []*timer
}

// nacl fake time support - time in nanoseconds since 1970
var faketime int64

// Package time APIs.
// Godoc uses the comments in package time, not these.

// time.now is implemented in assembly.

// timeSleep puts the current goroutine to sleep for at least ns nanoseconds.
//go:linkname timeSleep time.Sleep
func timeSleep(ns int64) {
	if ns <= 0 {
		return
	}

	gp := getg()
	t := gp.timer
	if t == nil {
		t = new(timer)
		gp.timer = t
	}
	*t = timer{}
	t.when = nanotime() + ns
	t.f = goroutineReady
	t.arg = gp
	tb := t.assignBucket()
	lock(&tb.lock)
	if !tb.addtimerLocked(t) {
		unlock(&tb.lock)
		badTimer()
	}
	goparkunlock(&tb.lock, waitReasonSleep, traceEvGoSleep, 2)
}

// startTimer adds t to the timer heap.
//go:linkname startTimer time.startTimer
func startTimer(t *timer) {
	if raceenabled {
		racerelease(unsafe.Pointer(t))
	}
	addtimer(t)
}

// stopTimer removes t from the timer heap if it is there.
// It returns true if t was removed, false if t wasn't even there.
//go:linkname stopTimer time.stopTimer
func stopTimer(t *timer) bool {
	return deltimer(t)
}

// Go runtime.

// Ready the goroutine arg.
func goroutineReady(arg interface{}, seq uintptr) {
	goready(arg.(*g), 0)
}

// 每个定时器桶都会包含一个专用于检查定时器过期的协程，这个协程是懒加载的，在第一次向桶中添加timer时创建。
// 我们先看下timer的添加过程

/**
整个定时器的实现过程会触发协程调度的地方比较多，概括起来如下

1. 添加定时器：
	a. 如果是第一次添加定时器到桶中，则会创建新的桶协程，并加入p的本地待运行g队列中，等待调度
	b. 如果加入新定时器前桶协程为挂起状态，则通过方法`goready`唤醒桶
	c. 如果加入新定时器前线程处于休眠状态，则唤醒线程

2. 桶协程循环:
	 a. 如果桶中不包含定时器，则通过`goparkunlock`将桶协程挂起。
	 b. 如果堆顶的定时器未触发，则将当前线程休眠。休眠过程通过系统调用实现，可能会被剥离P
	 c. 如果堆顶的定时器已触发，则向定时器持有的Channel发送数据。Channel的调度过程参考上节。
 */
func addtimer(t *timer) {
	// 获取P关联的桶（根据p.id取模）
	tb := t.assignBucket()
	lock(&tb.lock)
	// 将新的timer添加到桶中
	ok := tb.addtimerLocked(t)
	unlock(&tb.lock)
	if !ok {
		badTimer()
	}
}

// Add a timer to the heap and start or kick timerproc if the new timer is
// earlier than any of the others.
// Timers are locked.
// Returns whether all is well: false if the data structure is corrupt
// due to user-level races.
func (tb *timersBucket) addtimerLocked(t *timer) bool {
	// when must never be negative; otherwise timerproc will overflow
	// during its delta calculation and never expire other runtime timers.
	// 负值保护
	if t.when < 0 {
		t.when = 1<<63 - 1
	}
	// 获取当前堆的长度并将新创建的timer放入队尾
	t.i = len(tb.t)
	tb.t = append(tb.t, t)
	// 重新构建堆，最小堆
	if !siftupTimer(tb.t, t.i) {
		return false
	}
	// 如果添加前桶内没有定时器
	if t.i == 0 {
		// siftup moved to top: new earliest deadline.
		// 如果当前线程处于休眠中，且到了需要唤醒的时间，则唤醒线程
		if tb.sleeping && tb.sleepUntil > t.when {
			tb.sleeping = false
			notewakeup(&tb.waitnote)
		}
		// 如果当前协程处于挂起状态，则唤醒，加入全局待运行队列，等待调度
		if tb.rescheduling {
			tb.rescheduling = false
			goready(tb.gp, 0)
		}
		// 如果是第一次添加timer 则创建调度协程
		if !tb.created {
			tb.created = true
			go timerproc(tb)
		}
	}
	return true
}

// Delete timer t from the heap.
// Do not need to update the timerproc: if it wakes up early, no big deal.
func deltimer(t *timer) bool {
	if t.tb == nil {
		// t.tb can be nil if the user created a timer
		// directly, without invoking startTimer e.g
		//    time.Ticker{C: c}
		// In this case, return early without any deletion.
		// See Issue 21874.
		return false
	}

	tb := t.tb

	lock(&tb.lock)
	removed, ok := tb.deltimerLocked(t)
	unlock(&tb.lock)
	if !ok {
		badTimer()
	}
	return removed
}

func (tb *timersBucket) deltimerLocked(t *timer) (removed, ok bool) {
	// t may not be registered anymore and may have
	// a bogus i (typically 0, if generated by Go).
	// Verify it before proceeding.
	i := t.i
	last := len(tb.t) - 1
	if i < 0 || i > last || tb.t[i] != t {
		return false, true
	}
	if i != last {
		tb.t[i] = tb.t[last]
		tb.t[i].i = i
	}
	tb.t[last] = nil
	tb.t = tb.t[:last]
	ok = true
	if i != last {
		if !siftupTimer(tb.t, i) {
			ok = false
		}
		if !siftdownTimer(tb.t, i) {
			ok = false
		}
	}
	return true, ok
}

func modtimer(t *timer, when, period int64, f func(interface{}, uintptr), arg interface{}, seq uintptr) {
	tb := t.tb

	lock(&tb.lock)
	_, ok := tb.deltimerLocked(t)
	if ok {
		t.when = when
		t.period = period
		t.f = f
		t.arg = arg
		t.seq = seq
		ok = tb.addtimerLocked(t)
	}
	unlock(&tb.lock)
	if !ok {
		badTimer()
	}
}

// Timerproc runs the time-driven events.
// It sleeps until the next event in the tb heap.
// If addtimer inserts a new earlier event, it wakes timerproc early.
// 定时器桶协程的实现逻辑
func timerproc(tb *timersBucket) {
	tb.gp = getg()
	for {
		lock(&tb.lock)
		// 重置线程休眠标识
		tb.sleeping = false
		now := nanotime()
		// 第一个到期的定时器时间和当前时间的差值
		delta := int64(-1)
		for {
			// 桶中不包含定时器
			if len(tb.t) == 0 {
				delta = -1
				break
			}
			// 获取桶中最快到期的定时器，计算差值
			t := tb.t[0]
			delta = t.when - now
			// 如果未到期，则执行当前for循环外流程，将当前线程休眠
			if delta > 0 {
				break
			}
			ok := true
			// 如果是timer，则计算下次触发时间并重新调整桶
			if t.period > 0 {
				// leave in heap but adjust next time to fire
				t.when += t.period * (1 + -delta/t.period)
				if !siftdownTimer(tb.t, 0) {
					ok = false
				}
			} else {
				// remove from heap
				// 将定时器在当前桶中删除
				last := len(tb.t) - 1
				if last > 0 {
					tb.t[0] = tb.t[last]
					tb.t[0].i = 0
				}
				tb.t[last] = nil
				tb.t = tb.t[:last]
				if last > 0 {
					if !siftdownTimer(tb.t, 0) {
						ok = false
					}
				}
				t.i = -1 // mark as removed
			}
			// 执行定时器的回调函数
			f := t.f
			// 如果是NewTimer创建的定时器，则f为sendTime
			arg := t.arg
			seq := t.seq
			unlock(&tb.lock)
			if !ok {
				badTimer()
			}
			if raceenabled {
				raceacquire(unsafe.Pointer(t))
			}
			f(arg, seq)
			lock(&tb.lock)
		}
		// 当前桶中不包含定时器，将桶协程挂起
		if delta < 0 || faketime > 0 {
			// No timers left - put goroutine to sleep.
			tb.rescheduling = true
			goparkunlock(&tb.lock, waitReasonTimerGoroutineIdle, traceEvGoBlock, 1)
			continue
		}
		// At least one timer pending. Sleep until then.
		// 如果至少存在一个待到期的定时器，则将当前线程休眠，直到定时器到期
		// 休眠过程中，g和m不解绑
		tb.sleeping = true
		tb.sleepUntil = now + delta
		noteclear(&tb.waitnote)
		unlock(&tb.lock)
		notetsleepg(&tb.waitnote, delta)
	}
}

func timejump() *g {
	if faketime == 0 {
		return nil
	}

	for i := range timers {
		lock(&timers[i].lock)
	}
	gp := timejumpLocked()
	for i := range timers {
		unlock(&timers[i].lock)
	}

	return gp
}

func timejumpLocked() *g {
	// Determine a timer bucket with minimum when.
	var minT *timer
	for i := range timers {
		tb := &timers[i]
		if !tb.created || len(tb.t) == 0 {
			continue
		}
		t := tb.t[0]
		if minT == nil || t.when < minT.when {
			minT = t
		}
	}
	if minT == nil || minT.when <= faketime {
		return nil
	}

	faketime = minT.when
	tb := minT.tb
	if !tb.rescheduling {
		return nil
	}
	tb.rescheduling = false
	return tb.gp
}

func timeSleepUntil() int64 {
	next := int64(1<<63 - 1)

	// Determine minimum sleepUntil across all the timer buckets.
	//
	// The function can not return a precise answer,
	// as another timer may pop in as soon as timers have been unlocked.
	// So lock the timers one by one instead of all at once.
	for i := range timers {
		tb := &timers[i]

		lock(&tb.lock)
		if tb.sleeping && tb.sleepUntil < next {
			next = tb.sleepUntil
		}
		unlock(&tb.lock)
	}

	return next
}

// Heap maintenance algorithms.
// These algorithms check for slice index errors manually.
// Slice index error can happen if the program is using racy
// access to timers. We don't want to panic here, because
// it will cause the program to crash with a mysterious
// "panic holding locks" message. Instead, we panic while not
// holding a lock.
// The races can occur despite the bucket locks because assignBucket
// itself is called without locks, so racy calls can cause a timer to
// change buckets while executing these functions.

func siftupTimer(t []*timer, i int) bool {
	if i >= len(t) {
		return false
	}
	when := t[i].when
	tmp := t[i]
	for i > 0 {
		p := (i - 1) / 4 // parent
		if when >= t[p].when {
			break
		}
		t[i] = t[p]
		t[i].i = i
		i = p
	}
	if tmp != t[i] {
		t[i] = tmp
		t[i].i = i
	}
	return true
}

func siftdownTimer(t []*timer, i int) bool {
	n := len(t)
	if i >= n {
		return false
	}
	when := t[i].when
	tmp := t[i]
	for {
		c := i*4 + 1 // left child
		c3 := c + 2  // mid child
		if c >= n {
			break
		}
		w := t[c].when
		if c+1 < n && t[c+1].when < w {
			w = t[c+1].when
			c++
		}
		if c3 < n {
			w3 := t[c3].when
			if c3+1 < n && t[c3+1].when < w3 {
				w3 = t[c3+1].when
				c3++
			}
			if w3 < w {
				w = w3
				c = c3
			}
		}
		if w >= when {
			break
		}
		t[i] = t[c]
		t[i].i = i
		i = c
	}
	if tmp != t[i] {
		t[i] = tmp
		t[i].i = i
	}
	return true
}

// badTimer is called if the timer data structures have been corrupted,
// presumably due to racy use by the program. We panic here rather than
// panicing due to invalid slice access while holding locks.
// See issue #25686.
func badTimer() {
	panic(errorString("racy use of timers"))
}
