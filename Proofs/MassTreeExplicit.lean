module

public import Proofs.ManuscriptTreeExplicit
public import Proofs.UnconditionalFinalRecurrences
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Explicit formula for the tree groupoid mass

The recurrence project defines `RMass` as the non-free action-groupoid mass
of connected boundary-labelled rank-zero facet-pairing diagrams.  This file
shows that its already-proved cut--join recurrence is literally the recurrence
solved in `ManuscriptTreeExplicit`.  Consequently the factorial formula follows
from the single-cell initial value.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace MassExplicit

open scoped BigOperators
open NumericalRecurrenceAssembly
open StratumBalanceSpecialization
open UnconditionalFinalRecurrences
open PolytopeCounting.ExplicitFormulas

noncomputable section

universe uL

variable {L : Type uL}

/-- Proper component sizes are the natural numbers in `[1,n-1]`. -/
def properCellSizeEquivIcc (n : ℕ) :
    BridgeAllocationCounting.ProperCellSize n ≃
      {k : ℕ // k ∈ Finset.Icc 1 (n - 1)} where
  toFun k := by
    refine ⟨k.1, ?_⟩
    rw [Finset.mem_Icc]
    exact ⟨k.2.1, by omega⟩
  invFun k := by
    have hk : 1 ≤ k.1 ∧ k.1 ≤ n - 1 := Finset.mem_Icc.mp k.2
    have hn : 0 < n := by omega
    have hkn : k.1 < n := (Nat.le_sub_one_iff_lt hn).mp hk.2
    refine ⟨⟨k.1, by omega⟩, ?_⟩
    exact ⟨hk.1, hkn⟩
  left_inv k := by
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv k := by
    apply Subtype.ext
    rfl

/-- Rewrite a sum over `ProperCellSize n` as the paper's sum
`k=1,...,n-1`. -/
theorem sum_properCellSize_eq_Icc
    (n : ℕ) (f : ℕ → ℚ) :
    (∑ k : BridgeAllocationCounting.ProperCellSize n, f k.1) =
      ∑ k ∈ Finset.Icc 1 (n - 1), f k := by
  calc
    (∑ k : BridgeAllocationCounting.ProperCellSize n, f k.1) =
        ∑ k : {k : ℕ // k ∈ Finset.Icc 1 (n - 1)}, f k.1 := by
      apply Fintype.sum_equiv (properCellSizeEquivIcc n)
      intro k
      rfl
    _ = ∑ k ∈ Finset.Icc 1 (n - 1), f k := by
      symm
      exact Finset.sum_subtype (Finset.Icc 1 (n - 1))
        (fun k => Iff.rfl) f

/-- The concrete mass recurrence `R_tree` has exactly the manuscript form. -/
theorem RMass_satisfies_paper_recurrence
    (h r : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) :
    SatisfiesPaperTreeRecurrence h (r : ℚ)
      (fun n => RMass L n h r) := by
  intro n hn
  have hR := R_tree (L := L) n h r hh
  have hsum :
      (∑ k : BridgeAllocationCounting.ProperCellSize n,
          treeMassSummand L n h r k) =
        ∑ k ∈ Finset.Icc 1 (n - 1),
          (Nat.choose ((h - 2) * n + 2)
              ((h - 2) * k + 1) : ℚ) *
            RMass L k h r * RMass L (n - k) h r := by
    calc
      (∑ k : BridgeAllocationCounting.ProperCellSize n,
          treeMassSummand L n h r k) =
        ∑ k : BridgeAllocationCounting.ProperCellSize n,
          (Nat.choose ((h - 2) * n + 2)
              ((h - 2) * k.1 + 1) : ℚ) *
            RMass L k.1 h r * RMass L (n - k.1) h r := by
          apply Fintype.sum_congr
          intro k
          simp [treeMassSummand, treeBoundary,
            unrootedTreeBoundary, unrootedTreeOldBoundary]
      _ = ∑ k ∈ Finset.Icc 1 (n - 1),
          (Nat.choose ((h - 2) * n + 2)
              ((h - 2) * k + 1) : ℚ) *
            RMass L k h r * RMass L (n - k) h r :=
        sum_properCellSize_eq_Icc n (fun k =>
          (Nat.choose ((h - 2) * n + 2)
              ((h - 2) * k + 1) : ℚ) *
            RMass L k h r * RMass L (n - k) h r)
  rw [hsum] at hR
  exact hR

/-- Formula (20) for the actual `RMass`, conditional only on the explicit
single-cell value.  The recurrence itself is supplied unconditionally by the
cut--join equivalence. -/
theorem RMass_closed_form_of_single_cell
    (h r tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hr : 0 < r) (htau : 0 < tau)
    (hbase : RMass L 1 h r = (h.factorial : ℚ) / (tau : ℚ))
    (n : ℕ) (hn : 0 < n) :
    RMass L n h r = manuscriptTreeClosedForm h r tau n := by
  have hrec :
      SatisfiesPaperTreeRecurrence h (r : ℚ)
        (fun n => RMass L n h r) :=
    RMass_satisfies_paper_recurrence (L := L) h r hh
  exact manuscript_tree_closed_form h r tau
    (fun n => RMass L n h r) hh hr htau hrec hbase n hn

/-- Tetrahedral specialization of the actual mass recurrence. -/
theorem tetrahedron_RMass_closed_form_of_single_cell
    [Group L] [Fintype L] [MulAction L (Fin 4)]
    (hbase : RMass L 1 4 3 = 2)
    (n : ℕ) (hn : 0 < n) :
    RMass L n 4 3 = ((3 * n).factorial : ℚ) /
      (3 * (n.factorial : ℚ)) := by
  have hrec : SatisfiesPaperTreeRecurrence 4 3
      (fun n => RMass L n 4 3) :=
    RMass_satisfies_paper_recurrence (L := L) 4 3 (by omega)
  exact tetrahedron_tree_closed_form
    (fun n => RMass L n 4 3) hrec hbase n hn


end
end MassExplicit
end FacetPairing
end PolytopeCounting
