// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package runtime

import "unsafe"

// adjust Gobuf as if it executed a call to fn with context ctxt and then did an immediate Gosave.
// 调整Gobuf，就像它用上下文ctxt执行对fn的调用，然后立即进行Gosave。
// gostartcallfn最终通过gostartcall实现了调用栈的模拟
func gostartcall(buf *gobuf, fn, ctxt unsafe.Pointer) {
	if buf.lr != 0 {
		throw("invalid use of gostartcall")
	}
	// 将记录中的buf.pc(goexit)的值写入此位置。
	buf.lr = buf.pc
	// 记录该协程启动方法的真实位置
	buf.pc = uintptr(fn)
	// 记录fn参数在栈上的位置
	buf.ctxt = ctxt
}
