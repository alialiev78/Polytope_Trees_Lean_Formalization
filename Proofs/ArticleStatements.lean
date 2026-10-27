module

public import Proofs.PublicNumerals

public import Proofs.AppendixAAnalytic
public import Proofs.AppendixDMaximum
public import Proofs.AppendixE
public import Proofs.MainBinomialConsequences

/-! # Public statements with explicit formulas

The maximizing index is displayed directly in the public specification.
The detailed proofs use the threshold characterization in Appendix D.
-/

@[expose] public section
noncomputable section

namespace PolytopeTrees
open PolytopeCounting.AppendixD
universe u

section
attribute [local instance 2000] PolytopeCounting.PublicNumerals.two PolytopeCounting.PublicNumerals.three PolytopeCounting.PublicNumerals.four PolytopeCounting.PublicNumerals.five PolytopeCounting.PublicNumerals.six
/-- The smaller maximizing boundary index, with the required parity. -/
def closedMode (N r : ℕ) : ℕ :=
  N % 2 + 2 * Nat.ceil (((Real.sqrt ((r : ℝ) ^ 2 + 6 * r + 1 + 4 * r * N) -
    (3 * r + 1)) / (2 * r) - (N % 2 : ℕ)) / 2)
end

theorem closedMode_eq_firstMode (N r : ℕ) (hr : 0 < r) :
    closedMode N r = firstMode N r := by
  symm
  exact firstMode_explicit N r hr

theorem W_maximum_explicit (L : Type u) [Group L] [Fintype L]
    (n h r m : ℕ) [MulAction L (Fin h)] (hr : 0 < r) :
    W L n h r m ≤ W L n h r (closedMode (h * n) r) := by
  rw [closedMode_eq_firstMode _ _ hr]
  exact W_le_firstMode L n h r m hr

theorem W_maximizers_explicit (L : Type u) [Group L] [Fintype L]
    (n h r m : ℕ) [MulAction L (Fin h)] (hr : 0 < r) :
    W L n h r m = W L n h r (closedMode (h * n) r) ↔
      m = closedMode (h * n) r ∨
        (m = closedMode (h * n) r + 2 ∧ h * n =
          closedMode (h * n) r + r * (closedMode (h * n) r + 1) *
            (closedMode (h * n) r + 2)) := by
  simpa [closedMode_eq_firstMode _ _ hr, threshold] using W_eq_max_iff L n h r m hr

end PolytopeTrees
