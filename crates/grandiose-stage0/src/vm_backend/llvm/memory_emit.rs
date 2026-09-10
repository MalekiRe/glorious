use super::{Body, LlvmError, NativeLayout, VmType, layout};
use crate::MemoryPrimitive as M;

impl Body<'_, '_> {
    pub(super) fn static_data_word(&mut self, register: u32, length: bool) -> String {
        let pointer = if length {
            self.value(format!("getelementptr i8, ptr %r{register}, i64 8"))
        } else { self.pointer(register) };
        let ty = if length { "i64" } else { "ptr" };
        self.value(format!("load {ty}, ptr {pointer}, align 8"))
    }
    fn memory_layout(&self, ty: &VmType) -> Result<std::sync::Arc<NativeLayout>, LlvmError> {
        layout::concrete_layout(ty, &self.function.nominal_copy_descriptors.clone().into())
    }

    /// Match MemoryLayout::repeat, including stride padding and the allocator's
    /// isize bound. This check is not proof of the source pointer's extent.
    fn memory_extent(&mut self, ty: &VmType, count: u32) -> Result<String, LlvmError> {
        let layout = self.memory_layout(ty)?;
        let stride = layout.memory.pad_to_alignment().size();
        let count = self.load(count)?;
        self.declarations
            .insert("declare { i64, i1 } @llvm.umul.with.overflow.i64(i64, i64)".into());
        let pair = self.value(format!(
            "call {{ i64, i1 }} @llvm.umul.with.overflow.i64(i64 {count}, i64 {stride})"
        ));
        let bytes = self.value(format!("extractvalue {{ i64, i1 }} {pair}, 0"));
        let overflow = self.value(format!("extractvalue {{ i64, i1 }} {pair}, 1"));
        let no_overflow = self.value(format!("xor i1 {overflow}, true"));
        let bound = i64::MAX as u64 - (layout.memory.alignment() as u64 - 1);
        let valid_size = self.value(format!("icmp ule i64 {bytes}, {bound}"));
        let valid = self.value(format!("and i1 {no_overflow}, {valid_size}"));
        self.guard(&valid, 9);
        Ok(bytes)
    }

    pub(super) fn memory(
        &mut self,
        dst: u32,
        primitive: M,
        types: &[VmType],
        arguments: &[u32],
    ) -> Result<(), LlvmError> {
        match primitive {
            M::SizeOf | M::AlignOf | M::Dangling => {
                let ty = self.memory_layout(&types[0])?;
                let value = if primitive == M::SizeOf {
                    ty.memory.size()
                } else {
                    ty.memory.alignment()
                };
                let value = if primitive == M::Dangling {
                    self.value(format!("inttoptr i64 {value} to ptr"))
                } else {
                    value.to_string()
                };
                self.store_scalar(dst, &value)?;
            }
            M::Null => self.store_scalar(dst, "null")?,
            M::Cast | M::CastConst | M::AsConst | M::AsRawShared | M::AsRawUnique => {
                let pointer = self.load(arguments[0])?;
                self.store_scalar(dst, &pointer)?;
            }
            M::PointerAddress => {
                let pointer = self.load(arguments[0])?;
                let address = self.value(format!("ptrtoint ptr {pointer} to i64"));
                self.store_scalar(dst, &address)?;
            }
            M::IsNull | M::PointerEq => {
                let left = self.load(arguments[0])?;
                let right = if primitive == M::IsNull {
                    "null".into()
                } else {
                    self.load(arguments[1])?
                };
                let same = self.value(format!("icmp eq ptr {left}, {right}"));
                let result = self.value(format!("zext i1 {same} to i32"));
                self.store_scalar(dst, &result)?;
            }
            M::Allocate | M::Reallocate | M::Deallocate => {
                let allocate_at = self.value("getelementptr %G1Context, ptr %ctx, i32 0, i32 13");
                let allocate = self.value(format!("load ptr, ptr {allocate_at}, align 8"));
                let available = self.value(format!("icmp ne ptr {allocate}, null"));
                self.guard(&available, 8);
                let (op, pointer, old_size, alignment, size) = match primitive {
                    M::Allocate => (
                        0,
                        "null".into(),
                        "0".into(),
                        self.load(arguments[1])?,
                        self.load(arguments[0])?,
                    ),
                    M::Reallocate => (
                        1,
                        self.load(arguments[0])?,
                        self.load(arguments[1])?,
                        self.load(arguments[2])?,
                        self.load(arguments[3])?,
                    ),
                    M::Deallocate => (
                        2,
                        self.load(arguments[0])?,
                        self.load(arguments[1])?,
                        self.load(arguments[2])?,
                        "0".into(),
                    ),
                    _ => unreachable!(),
                };
                let result = if primitive == M::Deallocate {
                    "null".into()
                } else {
                    self.pointer(dst)
                };
                let status = self.value(format!("call i32 {allocate}(ptr %ctx, i32 {op}, ptr {pointer}, i64 {old_size}, i64 {alignment}, i64 {size}, ptr {result})"));
                let success = self.value(format!("icmp eq i32 {status}, 0"));
                self.guard(&success, 8);
                self.mark(dst, &[], true);
            }
            M::Offset | M::OffsetConst => {
                let pointer = self.load(arguments[0])?;
                let bytes = self.memory_extent(&types[0], arguments[1])?;
                let derived = self.value(format!("getelementptr i8, ptr {pointer}, i64 {bytes}"));
                self.store_scalar(dst, &derived)?;
            }
            M::Read => {
                let layout = self.memory_layout(&types[0])?;
                let pointer = self.load(arguments[0])?;
                self.copy_bytes(&self.pointer(dst), &pointer, &layout);
                self.mark(dst, &[], true);
            }
            M::Write => {
                let layout = self.memory_layout(&types[0])?;
                let pointer = self.load(arguments[0])?;
                self.copy_bytes(&pointer, &self.pointer(arguments[1]), &layout);
                self.mark(arguments[1], &[], false);
                self.mark(dst, &[], true);
            }
            M::Copy | M::CopyNonoverlapping => {
                let source = self.load(arguments[0])?;
                let destination = self.load(arguments[1])?;
                let bytes = self.memory_extent(&types[0], arguments[2])?;
                let zero = self.value(format!("icmp eq i64 {bytes}, 0"));
                let copy = self.label();
                let completed = self.label();
                self.line(format!("br i1 {zero}, label %{completed}, label %{copy}"));
                self.block(&copy);
                let intrinsic = if primitive == M::Copy {
                    "memmove"
                } else {
                    "memcpy"
                };
                if primitive == M::CopyNonoverlapping {
                    self.declarations
                        .insert("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)".into());
                }
                self.line(format!("call void @g1_residents(ptr %ctx, i32 0, ptr {destination}, ptr {source}, i64 {bytes})"));
                self.line(format!("call void @llvm.{intrinsic}.p0.p0.i64(ptr {destination}, ptr {source}, i64 {bytes}, i1 false)"));
                self.line(format!("br label %{completed}"));
                self.block(&completed);
                self.mark(dst, &[], true);
            }
            M::BorrowShared | M::BorrowUnique => {
                let layout = self.memory_layout(&types[0])?;
                let pointer = self.load(arguments[0])?;
                let nonnull = self.value(format!("icmp ne ptr {pointer}, null"));
                let address = self.value(format!("ptrtoint ptr {pointer} to i64"));
                let remainder = self.value(format!(
                    "and i64 {address}, {}",
                    layout.memory.alignment() - 1
                ));
                let aligned = self.value(format!("icmp eq i64 {remainder}, 0"));
                let valid = self.value(format!("and i1 {nonnull}, {aligned}"));
                self.guard(&valid, 10);
                self.store_scalar(dst, &pointer)?;
            }
            M::Forget => {
                self.mark(arguments[0], &[], false);
                self.mark(dst, &[], true);
            }
            M::StaticBytesLen | M::StaticUtf8Address | M::StaticBytesAddress => {
                let word = self.static_data_word(arguments[0], primitive == M::StaticBytesLen);
                self.store_scalar(dst, &word)?;
            }
        }
        Ok(())
    }
}
