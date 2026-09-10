
; Shared C-layout execution limits and execution-domain resident operations.
%G1Context = type { i64, i64, i64, i64, i32, i32, i32, i32, i64, ptr, ptr, i64, ptr, ptr, i32, ptr, ptr, ptr }
declare void @llvm.memmove.p0.p0.i64(ptr, ptr, i64, i1)

define internal void @g1_residents(ptr %ctx, i32 %op, ptr %dst, ptr %src, i64 %bytes) {
entry:
  %at = getelementptr %G1Context, ptr %ctx, i32 0, i32 17
  %callback = load ptr, ptr %at, align 8
  call void %callback(ptr %ctx, i32 %op, ptr %dst, ptr %src, i64 %bytes)
  ret void
}

define internal i32 @g1_callable(ptr %ctx, i32 %op, i32 %function, i32 %pc, i32 %register, ptr %slots, ptr %result) {
entry:
  %at = getelementptr %G1Context, ptr %ctx, i32 0, i32 16
  %callback = load ptr, ptr %at, align 8
  %status = call i32 %callback(ptr %ctx, i32 %op, i32 %function, i32 %pc, i32 %register, ptr %slots, ptr %result)
  ret i32 %status
}

define internal i32 @g1_fault(ptr %ctx, i32 %code) {
entry:
  %at = getelementptr %G1Context, ptr %ctx, i32 0, i32 7
  %previous = load i32, ptr %at, align 4
  %empty = icmp eq i32 %previous, 0
  %fault = select i1 %empty, i32 %code, i32 %previous
  store i32 %fault, ptr %at, align 4
  ret i32 1
}

define internal i1 @g1_step(ptr %ctx) {
entry:
  %at = getelementptr %G1Context, ptr %ctx, i32 0, i32 0
  %cap_at = getelementptr %G1Context, ptr %ctx, i32 0, i32 1
  %used = load i64, ptr %at, align 8
  %limit = load i64, ptr %cap_at, align 8
  %available = icmp ult i64 %used, %limit
  br i1 %available, label %accept, label %reject
accept:
  %next = add i64 %used, 1
  store i64 %next, ptr %at, align 8
  ret i1 true
reject:
  %status = call i32 @g1_fault(ptr %ctx, i32 3)
  ret i1 false
}

define internal i1 @g1_enter(ptr %ctx, i64 %bytes) {
entry:
  %depth_at = getelementptr %G1Context, ptr %ctx, i32 0, i32 4
  %depth_limit_at = getelementptr %G1Context, ptr %ctx, i32 0, i32 5
  %peak_at = getelementptr %G1Context, ptr %ctx, i32 0, i32 6
  %depth = load i32, ptr %depth_at, align 4
  %depth_limit = load i32, ptr %depth_limit_at, align 4
  %depth_ok = icmp ult i32 %depth, %depth_limit
  br i1 %depth_ok, label %memory, label %depth_reject
depth_reject:
  %depth_status = call i32 @g1_fault(ptr %ctx, i32 4)
  ret i1 false
memory:
  %bytes_at = getelementptr %G1Context, ptr %ctx, i32 0, i32 2
  %byte_limit_at = getelementptr %G1Context, ptr %ctx, i32 0, i32 3
  %used = load i64, ptr %bytes_at, align 8
  %byte_limit = load i64, ptr %byte_limit_at, align 8
  %remaining = sub i64 %byte_limit, %used
  %already_within = icmp ule i64 %used, %byte_limit
  %room = icmp ule i64 %bytes, %remaining
  %allocation_at = getelementptr %G1Context, ptr %ctx, i32 0, i32 11
  %allocation_limit = load i64, ptr %allocation_at, align 8
  %allocation_ok = icmp ule i64 %bytes, %allocation_limit
  %room_ok = and i1 %already_within, %room
  %memory_ok = and i1 %room_ok, %allocation_ok
  br i1 %memory_ok, label %accept, label %memory_reject
memory_reject:
  %memory_status = call i32 @g1_fault(ptr %ctx, i32 5)
  ret i1 false
accept:
  %new_used = add i64 %used, %bytes
  %new_depth = add i32 %depth, 1
  store i64 %new_used, ptr %bytes_at, align 8
  store i32 %new_depth, ptr %depth_at, align 4
  %peak = load i32, ptr %peak_at, align 4
  %deeper = icmp ugt i32 %new_depth, %peak
  %new_peak = select i1 %deeper, i32 %new_depth, i32 %peak
  store i32 %new_peak, ptr %peak_at, align 4
  ret i1 true
}

define internal void @g1_exit(ptr %ctx, i64 %bytes) {
entry:
  %depth_at = getelementptr %G1Context, ptr %ctx, i32 0, i32 4
  %bytes_at = getelementptr %G1Context, ptr %ctx, i32 0, i32 2
  %depth = load i32, ptr %depth_at, align 4
  %used = load i64, ptr %bytes_at, align 8
  %new_depth = sub i32 %depth, 1
  %new_used = sub i64 %used, %bytes
  store i32 %new_depth, ptr %depth_at, align 4
  store i64 %new_used, ptr %bytes_at, align 8
  ret void
}

define internal void @g1_tail_count(ptr %ctx) {
entry:
  %at = getelementptr %G1Context, ptr %ctx, i32 0, i32 8
  %value = load i64, ptr %at, align 8
  %next = add i64 %value, 1
  store i64 %next, ptr %at, align 8
  ret void
}
