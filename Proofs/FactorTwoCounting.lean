module

public import Proofs.FiniteCounting

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-! # The factor two in boundary-labelled cut data

An unordered pair of free slots, a labelling of its complement and an
orientation are equinumerous with labellings of the entire free boundary.
The result includes an empty complement. Concrete cut and join maps are
provided in `LabelledCutJoin`.
-/

open scoped BigOperators

namespace PolytopeCounting
namespace FactorTwoCounting

noncomputable section

open FacetPairing

universe uD

variable {D : Type uD} [Fintype D] [DecidableEq D]

/-- After joining a free pair, exactly two formerly free darts cease to be
boundary darts. -/
theorem card_boundary_joinFreePair
    (M : PartialMatching D) (p : M.FreePair) :
    Fintype.card (M.joinFreePair p).Boundary + 2 =
      Fintype.card M.Boundary := by
  have hcut := (M.joinFreePair p).card_boundary_erase
    (M.freePairNewSeam p)
  simpa only [M.erase_joinFreePair p] using hcut.symm

/-- Join data over one fixed cut matching.  `Bool` is the orientation of
the two exposed endpoints. -/
abbrev LabelledJoinData (M : PartialMatching D) (m : ℕ) :=
  Σ p : M.FreePair, ((M.joinFreePair p).Boundary ≃ Fin m) × Bool

/-- The natural-number identity behind the factor two. -/
theorem choose_two_mul_factorial_mul_two (m : ℕ) :
    Nat.choose (m + 2) 2 * (m.factorial * 2) =
      (m + 2).factorial := by
  have h := FiniteCounting.choose_add_mul_factorials 2 m
  simpa [Nat.add_comm, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- Exact cardinality of the oriented, boundary-labelled join data. -/
theorem card_labelledJoinData
    (M : PartialMatching D) (m : ℕ)
    (hboundary : Fintype.card M.Boundary = m + 2) :
    Fintype.card (LabelledJoinData M m) = (m + 2).factorial := by
  change Fintype.card
      (Σ p : M.FreePair, ((M.joinFreePair p).Boundary ≃ Fin m) × Bool) = _
  rw [Fintype.card_sigma]
  have hp (p : M.FreePair) :
      Fintype.card (M.joinFreePair p).Boundary = m := by
    have h := card_boundary_joinFreePair M p
    omega
  simp_rw [Fintype.card_prod]
  simp_rw [FiniteCounting.card_boundaryLabellings _ (hp _)]
  simp only [Fintype.card_bool, Finset.sum_const, Finset.card_univ,
    Nat.nsmul_eq_mul]
  rw [FiniteCounting.card_freePairs, hboundary]
  exact choose_two_mul_factorial_mul_two m

/-- The full boundary labellings have the same cardinality. -/
theorem card_fullBoundaryLabellings
    (M : PartialMatching D) (m : ℕ)
    (hboundary : Fintype.card M.Boundary = m + 2) :
    Fintype.card (M.Boundary ≃ Fin (m + 2)) = (m + 2).factorial :=
  FiniteCounting.card_boundaryLabellings M.Boundary hboundary

/-- A finite equivalence witnessing the exact factor-two count.  Unlike a
mere division in `ℚ`, this says there is no exceptional `m=0` case. -/
def labelledJoinDataEquivFullLabellings
    (M : PartialMatching D) (m : ℕ)
    (hboundary : Fintype.card M.Boundary = m + 2) :
    LabelledJoinData M m ≃ (M.Boundary ≃ Fin (m + 2)) :=
  Fintype.equivOfCardEq <| by
    rw [card_labelledJoinData M m hboundary,
      card_fullBoundaryLabellings M m hboundary]

/-- Adding the remembered seam colour preserves the equivalence. -/
def colouredLabelledJoinDataEquiv
    (M : PartialMatching D) (m r : ℕ)
    (hboundary : Fintype.card M.Boundary = m + 2) :
    (LabelledJoinData M m × Fin r) ≃
      ((M.Boundary ≃ Fin (m + 2)) × Fin r) :=
  (labelledJoinDataEquivFullLabellings M m hboundary).prodCongr
    (Equiv.refl _)

/-- Closed cut diagrams (`m=0`) still have exactly two oriented endpoint
choices and one empty labelling after rejoining. -/
theorem card_labelledJoinData_zero
    (M : PartialMatching D)
    (hboundary : Fintype.card M.Boundary = 2) :
    Fintype.card (LabelledJoinData M 0) = 2 := by
  simpa using card_labelledJoinData M 0 hboundary


end
end FactorTwoCounting
end PolytopeCounting
