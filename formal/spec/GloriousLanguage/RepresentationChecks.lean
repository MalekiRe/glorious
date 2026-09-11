import GloriousLanguage.ABI

namespace Glorious.Language.RepresentationChecks

open Kernel Execution Memory

private def header : Layout := ⟨8,8,[],0,0,[]⟩
private def byte : Layout := ⟨1,1,[],0,0,[]⟩
private def captured : Layout := ⟨16,8,[0,8],0,0,[]⟩

private theorem headerValid : header.Valid := by
  exact ⟨⟨3,rfl⟩,by decide,by simp [header]⟩

private theorem byteValid : byte.Valid := by
  exact ⟨⟨0,rfl⟩,by decide,by simp [byte]⟩

private theorem captureLayout : AggregateLayout [header,byte] captured := by
  refine ⟨9,?_,rfl,rfl,rfl,rfl,rfl⟩
  exact .cons headerValid (.cons byteValid .nil)

/-- The captured field starts after the code identity, not at field zero of
an unrelated layout chosen by the memory consumer. -/
example {program : Language.Program} {world : World} {address id arguments}
    (fields : CallableFields program id arguments [.scalar (.integer false (.fixed 8))])
    (codeLayout : program.input.target.codeIdentityLayout = header)
    (alignment : program.input.target.scalarAlignment (.integer false (.fixed 8)) = 1) :
    FieldOffset program world address (.callable id arguments) 0 (.scalar (.integer false (.fixed 8))) 8 := by
  have scalar : LayoutOf program ⟨[],[],0,default,false⟩ (.scalar (.integer false (.fixed 8))) byte := by
    simpa [byte, Scalar.bytes, Width.bits, alignment] using
      (@LayoutOf.scalar program ⟨[],[],0,default,false⟩ (.integer false (.fixed 8)) (by simp [Scalar.Valid]))
  exact .callable fields rfl (.cons scalar .nil) (codeLayout.symm ▸ captureLayout) rfl

example (program : Language.Program) (context : Language.Context) (brand region result : Term) :
    LayoutOf program context (.label brand region result) ⟨0,1,[],0,0,[]⟩ := .label

example (program : Language.Program) (context : Language.Context) (brand argument answer effects : Term) (quantity : Quantity) :
    LayoutOf program context (.continuation brand argument answer effects quantity) program.input.target.continuationLayout := .continuation

example {program : Language.Program} {world : World} {address type physical}
    (physicalAddress : PhysicalAddress program world address type physical) :
    Addressable program ⟨[],[],0,default,false⟩ type := physicalAddress.1

example {program : Language.Program} {context : Language.Context} {id arguments fields region}
    (captures : CallableFields program id arguments fields)
    (outlives : ∀ field ∈ fields, TypeOutlives program context field region) :
    TypeOutlives program context (.callable id arguments) region := .callable captures outlives

example {target : TargetProfile} {fields : List Layout} {left right : Layout}
    (a : CRecordLayout target fields left) (b : CRecordLayout target fields right) : left = right :=
  a.2.1.trans b.2.1.symm

example {variants : List Layout} {layout : Layout} (three : layout.tagBytes = 3) : ¬ EnumLayout variants layout := by
  intro valid
  have supported := valid.2.2.1
  simp [three] at supported

end Glorious.Language.RepresentationChecks
