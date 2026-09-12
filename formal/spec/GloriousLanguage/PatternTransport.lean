import GloriousLanguage.Kernel

namespace Glorious.Language

theorem Kernel.Matches.transport {program : Language.Program} {before after : World} {address : Address} {pattern : Kernel.Pattern}
    (matched : Kernel.Matches program before address pattern)
    (read : ∀ address, after.read address = before.read address)
    (loans : ∀ id, after.loans.get id = before.loans.get id) : Kernel.Matches program after address pattern := by
  have stores {address value} (stored : before.Stores address value) : after.Stores address value := by
    change after.read address = some value
    rw [read]; exact stored
  refine Kernel.Matches.rec
    (motive_1 := fun address pattern _ => Kernel.Matches program after address pattern)
    (motive_2 := fun address offset patterns _ => Kernel.MatchesFields program after address offset patterns)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ matched
  · intro address; exact .wildcard
  · intro address localSlot value stored initialized; exact .bind (stores stored) initialized
  · intro address expected value stored initialized head notFloat; exact .scalar (stores stored) initialized head notFloat
  · intro address value stored head initialized; exact .unit (stores stored) head initialized
  · intro address value fields stored head live length _ ih; exact .tuple (stores stored) head live length ih
  · intro address value fields stored head initialized length _ ih; exact .array (stores stored) head initialized length ih
  · intro address value variant fields stored head live length _ ih; exact .constructor (stores stored) head live length ih
  · intro address value id loan mode pattern stored head found live modeEq _ ih
    exact .reference (stores stored) head (by rw [loans]; exact found) live modeEq ih
  · intro address offset; exact .nil
  · intro address offset first rest _ _ ihFirst ihRest; exact .cons ihFirst ihRest

end Glorious.Language
