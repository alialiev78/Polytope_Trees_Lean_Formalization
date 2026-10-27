module

public import Mathlib.Data.Nat.Basic

@[expose] public section

/-! # Stable numeral instances for independently elaborated statements

Named proofs keep the exported numerical definitions identical in the
standalone specification and the proof library. They assert only elementary
facts about the literal natural numbers used in those definitions.
-/

namespace PolytopeCounting.PublicNumerals
theorem two : (2 : ℕ).AtLeastTwo := Nat.instAtLeastTwoHAddOfNat 1
theorem three : (3 : ℕ).AtLeastTwo := Nat.instAtLeastTwoHAddOfNat 2
theorem four : (4 : ℕ).AtLeastTwo := Nat.instAtLeastTwoHAddOfNat 3
theorem five : (5 : ℕ).AtLeastTwo := Nat.instAtLeastTwoHAddOfNat 4
theorem six : (6 : ℕ).AtLeastTwo := Nat.instAtLeastTwoHAddOfNat 5
end PolytopeCounting.PublicNumerals
