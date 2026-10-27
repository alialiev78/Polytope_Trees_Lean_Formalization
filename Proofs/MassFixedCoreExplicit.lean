module

public import Proofs.ManuscriptFixedCoreExplicit
public import Proofs.MassTreeExplicit
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Explicit fixed-core formula for `TMass`

This file connects the rooted cut--join recurrence
`T_fixed_tree` to the abstract recurrence solved in
`ManuscriptFixedCoreExplicit`.
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

/-- The concrete `TMass` recurrence is the literal paper recurrence. -/
theorem TMass_satisfies_paper_fixed_core_recurrence
    (h₀ h r : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hbase : 1 ≤ h₀) :
    SatisfiesPaperFixedCoreRecurrence h h₀ (r : ℚ)
      (fun n => RMass L n h r)
      (fun n => TMass L n h₀ h r) := by
  intro n hn
  have hT := T_fixed_tree (L := L) n h₀ h r hh hbase
  let f : ℕ → ℚ := fun k =>
    (Nat.choose ((h - 2) * n + h₀)
        ((h - 2) * (n - k) + 1) : ℚ) *
      TMass L k h₀ h r * RMass L (n - k) h r
  have hsum :
      (∑ k : Fin n, fixedTreeMassSummand L n h₀ h r k) =
        ∑ k ∈ Finset.range n, f k := by
    calc
      (∑ k : Fin n, fixedTreeMassSummand L n h₀ h r k) =
          ∑ k : Fin n, f k.1 := by
        apply Fintype.sum_congr
        intro k
        simp [f, fixedTreeMassSummand, rootedTreeBoundary,
          treeBoundary, unrootedTreeBoundary, unrootedTreeOldBoundary,
          Nat.add_comm]
      _ = ∑ k ∈ Finset.range n, f k :=
        Fin.sum_univ_eq_sum_range f n
  rw [hsum] at hT
  simpa [f] using hT

/-- Formula (27) for the actual rooted mass, conditional only on the
single-cell value used by the unrooted tree series. -/
theorem TMass_closed_form_of_tree_single_cell
    (h₀ h r tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hbase : 1 ≤ h₀)
    (hr : 0 < r) (htau : 0 < tau)
    (hRbase : RMass L 1 h r =
      (h.factorial : ℚ) / (tau : ℚ))
    (n : ℕ) :
    TMass L n h₀ h r =
      manuscriptFixedCoreClosedForm
        (TMass L 0 h₀ h r) h₀ h r tau n := by
  have hRrec : SatisfiesPaperTreeRecurrence h (r : ℚ)
      (fun n => RMass L n h r) :=
    RMass_satisfies_paper_recurrence (L := L) h r hh
  have hTrec : SatisfiesPaperFixedCoreRecurrence h h₀ (r : ℚ)
      (fun n => RMass L n h r)
      (fun n => TMass L n h₀ h r) :=
    TMass_satisfies_paper_fixed_core_recurrence
      (L := L) h₀ h r hh hbase
  exact manuscript_fixed_core_closed_form h h₀ r tau
    (fun n => RMass L n h r)
    (fun n => TMass L n h₀ h r)
    hh hbase hr htau hRrec hTrec hRbase n


end
end MassExplicit
end FacetPairing
end PolytopeCounting
