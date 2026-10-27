module

public import Mathlib.Data.Sym.Card

public import Proofs.BoundaryCut
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Finite pointing and labelling counts

These are the raw finite-set identities behind the factors `e` and `m!`.
They do not assume an automorphism action is free.  The groupoid quotient is
handled separately; here a pointed object is literally a dependent pair.
-/

open scoped BigOperators

namespace PolytopeCounting
namespace FiniteCounting

open Finset Fintype Function Nat

universe u v

variable {X : Type u} [Fintype X]

/-- Objects equipped with one point in a dependent finite fibre. -/
abbrev Pointed (E : X → Type v) := Σ x : X, E x

/-- Constant-size dependent pointing multiplies cardinality by `e`. -/
theorem card_pointed_of_constant
    (E : X → Type v) [∀ x, Fintype (E x)] (e : ℕ)
    (hE : ∀ x, Fintype.card (E x) = e) :
    Fintype.card (Pointed E) = Fintype.card X * e := by
  rw [Fintype.card_sigma]
  simp_rw [hE]
  simp

/-- The literal seam-pointed carrier of a family of matchings. -/
abbrev SeamPointed
    {D : Type v} [DecidableEq D] (P : X → FacetPairing.PartialMatching D) :=
  Σ x : X, (P x).Seam

theorem card_seamPointed_of_constant
    {D : Type v} [DecidableEq D]
    (P : X → FacetPairing.PartialMatching D) (e : ℕ)
    (hE : ∀ x, (P x).seams.card = e) :
    Fintype.card (SeamPointed P) = Fintype.card X * e := by
  apply card_pointed_of_constant (fun x ↦ (P x).Seam) e
  intro x
  exact (Fintype.card_coe (P x).seams).trans (hE x)

/-- If a finite boundary has `m` elements, its bijective labellings by
`Fin m` are counted by `m!`; at `m=0` this is one. -/
theorem card_boundaryLabellings
    (B : Type v) [Fintype B] [DecidableEq B]
    {m : ℕ} (hB : Fintype.card B = m) :
    Fintype.card (B ≃ Fin m) = Nat.factorial m := by
  classical
  let e : B ≃ Fin m := Fintype.equivFinOfCardEq hB
  simpa [hB] using Fintype.card_equiv e

@[simp] theorem card_emptyLabellings :
    Fintype.card (Fin 0 ≃ Fin 0) = 1 := by
  exact card_boundaryLabellings (Fin 0) rfl

/-- The number of `k`-element subsets of a finite label set. -/
theorem card_kSubsets (L : Type v) [Fintype L] [DecidableEq L] (k : ℕ) :
    Fintype.card {s : Finset L // s.card = k} =
      Nat.choose (Fintype.card L) k := by
  exact @Fintype.card_finset_len L _ k

/-- Specialization to the manuscript's boundary-label set `Fin m`. -/
theorem card_labelPartitions (m k : ℕ) :
    Fintype.card {s : Finset (Fin m) // s.card = k} = Nat.choose m k := by
  simpa only [Fintype.card_fin] using card_kSubsets (Fin m) k

/-- The unordered off-diagonal pairs of free darts are counted by
`choose boundarySize 2`.  This is the exact raw factor on the join side of
the cut--join equivalence. -/
theorem card_freePairs
    {D : Type v} [Fintype D] [DecidableEq D]
    (M : FacetPairing.PartialMatching D) :
    Fintype.card M.FreePair =
      Nat.choose (Fintype.card M.Boundary) 2 := by
  classical
  rw [Fintype.card_congr
    (FacetPairing.PartialMatching.FreePair.equivBoundaryOffDiagonal M)]
  exact Sym2.card_subtype_not_diag

/-- If `M` has exactly `m` free darts, it has exactly `choose m 2`
unordered join pairs. -/
theorem card_freePairs_of_boundary_card
    {D : Type v} [Fintype D] [DecidableEq D]
    (M : FacetPairing.PartialMatching D) {m : ℕ}
    (hm : Fintype.card M.Boundary = m) :
    Fintype.card M.FreePair = Nat.choose m 2 := by
  rw [card_freePairs, hm]

/-- After also choosing one of `r` seam colours, the join data have
`choose m 2 * r` elements. -/
theorem card_coloredFreePairData
    {D : Type v} [Fintype D] [DecidableEq D] {r m : ℕ}
    (P : FacetPairing.ColoredMatching D r)
    (hm : Fintype.card P.Boundary = m) :
    Fintype.card P.FreePairDatum = Nat.choose m 2 * r := by
  rw [Fintype.card_congr
      (FacetPairing.ColoredMatching.FreePairDatum.equivProd P),
    Fintype.card_prod,
    card_freePairs_of_boundary_card P.matching hm]
  simp

/-- Cardinality consequence of the concrete colour-preserving cut--join
equivalence. -/
theorem card_markedColored_eq_freePairColored
    {D : Type v} [Fintype D] [DecidableEq D] (r : ℕ) :
    Fintype.card (FacetPairing.ColoredMatching.MarkedColoredMatching D r) =
      Fintype.card
        (FacetPairing.ColoredMatching.FreePairColoredMatching D r) := by
  exact Fintype.card_congr
    FacetPairing.ColoredMatching.markedColoredEquivFreePair

/-- The unconditional raw cut--join identity, summed over every coloured
partial matching on the fixed dart type.  The left side literally points a
seam; the right side chooses an unordered pair of free darts and a colour.
This theorem is already a complete finite-cardinality consequence of the
constructed inverse maps, before connectivity/rank strata are imposed. -/
theorem markedColored_master_identity
    {D : Type v} [Fintype D] [DecidableEq D] (r : ℕ) :
    Fintype.card
        (FacetPairing.ColoredMatching.MarkedColoredMatching D r) =
      ∑ P : FacetPairing.ColoredMatching D r,
        Nat.choose (Fintype.card P.Boundary) 2 * r := by
  rw [card_markedColored_eq_freePairColored]
  change Fintype.card
      (Σ P : FacetPairing.ColoredMatching D r, P.FreePairDatum) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro P _
  exact card_coloredFreePairData P rfl

/-- The cell-subset factor cancels the two component factorials.  This is
the normalization identity used after cutting a globally cell-labelled
diagram into components of sizes `k` and `n-k`. -/
theorem choose_mul_component_factorials {n k : ℕ} (hk : k ≤ n) :
    Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) =
      Nat.factorial n :=
  Nat.choose_mul_factorial_mul_factorial hk

/-- Addition-shaped form, avoiding truncated subtraction. -/
theorem choose_add_mul_factorials (k l : ℕ) :
    Nat.choose (k + l) k * Nat.factorial k * Nat.factorial l =
      Nat.factorial (k + l) := by
  simpa only [Nat.add_sub_cancel_left] using
    (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k l))


end FiniteCounting
end PolytopeCounting
