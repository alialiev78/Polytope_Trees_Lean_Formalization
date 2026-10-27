module

public import Solution
public import Proofs.AffineFactorialStirling
public import Proofs.ConcreteCoreInitial

@[expose] public section

/-!
# Unconditional Stirling asymptotics for the actual finite counts

The real sequences below are obtained by coercing the public rational counts,
not by defining new counts with the desired factorial expressions.  Their
identification with those expressions uses the existing `R_formula` and
`T_formula`.  Only the natural positivity conditions remain in the final types.
-/

namespace PolytopeTrees

noncomputable section
open PolytopeCounting.GeneralAsymptotics
open PolytopeCounting.HermiteAsymptotic
open Filter
open scoped Topology
universe u

/-- The concrete boundary-normalized tree mass, viewed as a real sequence. -/
def RBoundaryReal (L : Type u) [Fintype L] (h r n : ℕ) : ℝ :=
  (R L n h r : ℝ) / (((h - 2) * n + 2).factorial : ℝ)

/-- The concrete boundary-normalized fixed-core mass. -/
def TBoundaryReal (L : Type u) [Fintype L] (h₀ h r n : ℕ) : ℝ :=
  (T L n h₀ h r : ℝ) / (((h - 2) * n + h₀).factorial : ℝ)

theorem RBoundaryReal_eq_exact (L : Type u) [Group L] [Fintype L]
    (h r n : ℕ) [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hr : 0 < r) (hn : 0 < n) :
    RBoundaryReal L h r n = treeUnlabelledExact h r (Fintype.card L) n := by
  unfold RBoundaryReal
  rw [R_formula L n h r hh hr hn]
  push_cast
  unfold treeUnlabelledExact
  push_cast
  ring

theorem TBoundaryReal_eq_exact (L : Type u) [Group L] [Fintype L]
    (h₀ h r n : ℕ) [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hh₀ : 1 ≤ h₀) (hr : 0 < r) :
    TBoundaryReal L h₀ h r n =
      fixedCoreUnlabelledExact (T L 0 h₀ h r : ℝ) h₀ h r (Fintype.card L) n := by
  unfold TBoundaryReal
  rw [T_formula L n h₀ h r hh hh₀ hr]
  push_cast
  unfold fixedCoreUnlabelledExact
  push_cast
  ring

/-- Corollary 5.1 for finite-carrier masses, without a Stirling hypothesis. -/
theorem RBoundaryReal_asymptotic (L : Type u) [Group L] [Fintype L]
    (h r : ℕ) [MulAction L (Fin h)] (hh : 3 ≤ h) (hr : 0 < r) :
    SequenceEquivalent (RBoundaryReal L h r)
      (treeUnlabelledLeading h r (Fintype.card L)) := by
  have ht := treeUnlabelled_asymptotic_unconditional h r (Fintype.card L)
    hh hr Fintype.card_pos
  unfold SequenceEquivalent at ht ⊢
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [RBoundaryReal_eq_exact L h r n (by omega) hr hn]

/-- Corollary 5.2, with the actual initial core mass rather than an assumed
nonzero normalization constant. -/
theorem TBoundaryReal_asymptotic (L : Type u) [Group L] [Fintype L]
    (h₀ h r : ℕ) [MulAction L (Fin h)]
    (hh₀ : 1 ≤ h₀) (hh : 3 ≤ h) (hr : 0 < r) :
    SequenceEquivalent (TBoundaryReal L h₀ h r)
      (fixedCoreUnlabelledLeading (T L 0 h₀ h r : ℝ)
        h₀ h r (Fintype.card L)) := by
  have hT : (T L 0 h₀ h r : ℝ) ≠ 0 := by
    exact_mod_cast T_zero_ne_zero L h₀ h r
  have ht := fixedCoreUnlabelled_asymptotic_unconditional
    (T L 0 h₀ h r : ℝ) h₀ h r (Fintype.card L)
    hT hh₀ hh hr Fintype.card_pos
  unfold SequenceEquivalent at ht ⊢
  apply ht.congr'
  exact Filter.Eventually.of_forall (fun n ↦ by
    dsimp only
    rw [TBoundaryReal_eq_exact L h₀ h r n (by omega) hh₀ hr])

end
end PolytopeTrees
