// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package runtime

import (
	"runtime/internal/sys"
	"unsafe"
)

type m0Stack struct {
	_ [8192 * sys.StackGuardMultiplier]byte
}

var wasmStack m0Stack

func wasmMove()

func wasmZero()

func wasmDiv()

func wasmTruncS()
func wasmTruncU()

func wasmExit(code int32)

// adjust Gobuf as it if executed a call to fn with context ctxt
// and then did an immediate gosave.
func gostartcall(buf *gobuf, fn, ctxt unsafe.Pointer) {
	sp := buf.sp
	if sys.RegSize > sys.PtrSize {
		// sp的位置向下移一个空间
		sp -= sys.PtrSize
		*(*uintptr)(unsafe.Pointer(sp)) = 0
	}
	// sp的位置向下移一个空间
	sp -= sys.PtrSize
	// 将记录中的buf.pc(goexit)的值写入此位置。
	*(*uintptr)(unsafe.Pointer(sp)) = buf.pc
	// 记录sp位置
	buf.sp = sp
	// 记录该协程启动方法的真实位置
	buf.pc = uintptr(fn)
	// 记录fn参数在栈上的位置
	buf.ctxt = ctxt
}
