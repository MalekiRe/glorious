import GloriousLanguage.RuntimeSupport

/-! Runtime invocation consumes closed source templates and actual closed
arguments, so installing the callee's fresh scope cannot change input types. -/
namespace Glorious.Language

theorem Kernel.Instance.scopeClosed {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    (inventory : Kernel.BodyInventory program) {id : DeclId} {arguments : List Term} {function : Kernel.Function}
    (selected : Kernel.Instance program id arguments function) :
    (∀ parameter ∈ function.signature.parameters, parameter.ScopeClosed) ∧
    function.signature.result.ScopeClosed ∧
    (∀ capture ∈ function.captures, capture.type.ScopeClosed) := by
  obtain ⟨template,declaration,substitution,found,declared,signature,instantiated,_,closed,rfl⟩ := selected
  have admitted := valid.scopeClosed (List.mem_of_find?_eq_some (Program.function_lookup declared))
  have templateMember := List.mem_of_find?_eq_some found
  have captures := inventory.2.1 template templateMember
  obtain ⟨actual,actualFound,_,_,captureTypes⟩ := captures
  rw [Kernel.Program.function_declaration found] at actualFound
  have same : actual = declaration := Option.some.inj (actualFound.symm.trans declared)
  subst actual
  refine ⟨?_,?_,?_⟩
  · intro parameter member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    apply instantiated.scopeClosed closed
    apply admitted
    rw [signature] at present
    simp only [Definition.terms,Signature.terms,List.mem_append,List.mem_cons,present,true_or,or_true]
  · apply instantiated.scopeClosed closed
    apply admitted
    rw [signature]
    simp only [Definition.terms,Signature.terms,List.mem_append,List.mem_cons,true_or]
  · intro capture member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    apply instantiated.scopeClosed closed
    apply admitted
    have inCaptures : original.type ∈ declaration.captures := by
      rw [← captureTypes]
      exact List.mem_map.mpr ⟨original,present,rfl⟩
    simp only [Definition.terms,List.mem_append,inCaptures,true_or,or_true]

end Glorious.Language
