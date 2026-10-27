module

public import Proofs.RecurrenceAssembly
public import Proofs.BridgeAllocationCounting
public import Proofs.StratumBalanceSpecialization

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Concrete numerical assembly of the four recurrences

This module is the arithmetic endpoint of the exact bridge coproducts.  Its
only inputs are the literal cardinal equalities obtained by taking
cardinalities of those equivalences.  There are no cut--join certificates,
no freeness assumptions, and no abstract mass-preservation fields.

The index types below are the exact numerical fibers:

* unrooted: a proper nonempty cell size, an old-boundary split, and a rank
  split;
* rooted: a base-side ordinary-cell size (including zero), an old-boundary
  split, and a rank split.

The first two main theorems instantiate `RecurrenceAssembly` and rewrite
every normalized raw component cardinal as its non-free action-groupoid
mass.  The final section specializes rank zero and uses the exact support
lemmas in `StratumBalanceSpecialization` to recover the traditional `R` and
`T` boundary parameters.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace NumericalRecurrenceAssembly

open scoped BigOperators

open PointedDecomposition MassRecurrence AllRankMassRecurrence
open BridgeConvolutionNormalization
open StratumBalanceSpecialization
open Renaming

noncomputable section

universe uL

variable {L : Type uL}

local instance unrootedStratumFintype (n h r m b : ℕ) :
    Fintype (UnrootedStratum n h r m b) := Fintype.ofFinite _

local instance rootedStratumFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedStratum n h₀ h r m b) := Fintype.ofFinite _

local instance unrootedBridgePointedFintype (n h r m b : ℕ) :
    Fintype (UnrootedBridgePointed n h r m b) := Fintype.ofFinite _

local instance rootedBridgePointedFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedBridgePointed n h₀ h r m b) := Fintype.ofFinite _

/-! ## Concrete finite numerical index types -/

/-- A proper unrooted left cell block, an old-boundary split, and the left
circuit rank. -/
abbrev UnrootedIndex (n m b : ℕ) :=
  BridgeAllocationCounting.ProperCellSize n ×
    (Fin (m + 1) × Fin (b + 1))

/-- The base side may contain zero ordinary cells; the away side is nonempty,
so its size index is `Fin n`. -/
abbrev RootedIndex (n m b : ℕ) :=
  Fin n × (Fin (m + 1) × Fin (b + 1))

def unrootedCellIndex (i : UnrootedIndex n m b) : ℕ := i.1.1
def unrootedBoundaryIndex (i : UnrootedIndex n m b) : ℕ := i.2.1.1
def unrootedRankIndex (i : UnrootedIndex n m b) : ℕ := i.2.2.1

def rootedCellIndex (i : RootedIndex n m b) : ℕ := i.1.1
def rootedBoundaryIndex (i : RootedIndex n m b) : ℕ := i.2.1.1
def rootedRankIndex (i : RootedIndex n m b) : ℕ := i.2.2.1

def unrootedLeftCard (h r : ℕ) (i : UnrootedIndex n m b) : ℕ :=
  Fintype.card
    (UnrootedStratum (unrootedCellIndex i) h r
      (unrootedBoundaryIndex i + 1) (unrootedRankIndex i))

def unrootedRightCard (n h r m b : ℕ)
    (i : UnrootedIndex n m b) : ℕ :=
  Fintype.card
    (UnrootedStratum (n - unrootedCellIndex i) h r
      (m - unrootedBoundaryIndex i + 1)
      (b - unrootedRankIndex i))

def rootedLeftCard (h₀ h r : ℕ) (i : RootedIndex n m b) : ℕ :=
  Fintype.card
    (RootedStratum (rootedCellIndex i) h₀ h r
      (rootedBoundaryIndex i + 1) (rootedRankIndex i))

def rootedRightCard (n h r m b : ℕ)
    (i : RootedIndex n m b) : ℕ :=
  Fintype.card
    (UnrootedStratum (n - rootedCellIndex i) h r
      (m - rootedBoundaryIndex i + 1)
      (b - rootedRankIndex i))

/-! ## Literal raw cardinal sums -/

def unrootedRawBridgeSum (n h r m b : ℕ) : ℕ :=
  ∑ i : UnrootedIndex n m b,
    Nat.choose n (unrootedCellIndex i) *
      Nat.choose m (unrootedBoundaryIndex i) *
      unrootedLeftCard h r i * unrootedRightCard n h r m b i

def rootedRawBridgeSum (n h₀ h r m b : ℕ) : ℕ :=
  ∑ i : RootedIndex n m b,
    Nat.choose n (rootedCellIndex i) *
      Nat.choose m (rootedBoundaryIndex i) *
      rootedLeftCard h₀ h r i * rootedRightCard n h r m b i

/-! ## The normalized component convolutions -/

def unrootedMassSummand
    (L : Type uL) [Group L] [Fintype L] (n h r m b : ℕ)
    [MulAction L (Fin h)] (i : UnrootedIndex n m b) : ℚ :=
  (Nat.choose m (unrootedBoundaryIndex i) : ℚ) *
    UMass L (unrootedCellIndex i) h r
      (unrootedBoundaryIndex i + 1) (unrootedRankIndex i) *
    UMass L (n - unrootedCellIndex i) h r
      (m - unrootedBoundaryIndex i + 1) (b - unrootedRankIndex i)

def rootedMassSummand
    (L : Type uL) [Group L] [Fintype L] (n h₀ h r m b : ℕ)
    [MulAction L (Fin h)] (i : RootedIndex n m b) : ℚ :=
  (Nat.choose m (rootedBoundaryIndex i) : ℚ) *
    PsiMass L (rootedCellIndex i) h₀ h r
      (rootedBoundaryIndex i + 1) (rootedRankIndex i) *
    UMass L (n - rootedCellIndex i) h r
      (m - rootedBoundaryIndex i + 1) (b - rootedRankIndex i)

def unrootedMassConvolution
    (L : Type uL) [Group L] [Fintype L] (n h r m b : ℕ)
    [MulAction L (Fin h)] : ℚ :=
  ∑ i : UnrootedIndex n m b, unrootedMassSummand L n h r m b i

def rootedMassConvolution
    (L : Type uL) [Group L] [Fintype L] (n h₀ h r m b : ℕ)
    [MulAction L (Fin h)] : ℚ :=
  ∑ i : RootedIndex n m b, rootedMassSummand L n h₀ h r m b i

/-! ## Exact all-rank `U` and `Psi` recurrences -/

/-- Fully normalized all-rank unrooted recurrence from the exact raw bridge
cardinality theorem.  The input equality is precisely what the final
unrooted bridge equivalence supplies after taking cardinalities. -/
theorem unrooted_numerical_all_rank_recurrence
    (n h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (hbridge :
      2 * Fintype.card (UnrootedBridgePointed n h r m b) =
        r * unrootedRawBridgeSum n h r m b) :
    ((n + b - 1 : ℕ) : ℚ) * UMass L n h r m b =
      ((r : ℚ) / 2) * unrootedCyclePrevious L n h r m b +
        ((r : ℚ) / 2) * unrootedMassConvolution L n h r m b := by
  classical
  have hrec :=
    RecurrenceAssembly.unrooted_mass_recurrence_of_bridge_cardinality
      (I := UnrootedIndex n m b) (L := L) n h r m b tau
      unrootedCellIndex unrootedBoundaryIndex
      (unrootedLeftCard h r) (unrootedRightCard n h r m b)
      (fun i ↦ Nat.le_of_lt i.1.2.2) hcard hbridge
  have hsum :
      (∑ i : UnrootedIndex n m b,
        normalizedSummand n m tau unrootedCellIndex
          unrootedBoundaryIndex (unrootedLeftCard h r)
          (unrootedRightCard n h r m b) i) =
        unrootedMassConvolution L n h r m b := by
    apply Fintype.sum_congr
    intro i
    unfold normalizedSummand unrootedMassSummand
      unrootedLeftCard unrootedRightCard
    rw [← Renaming.GenericStratumMass.mass_genericWreath_unrootedStratum_of_card
          (L := L) (unrootedCellIndex i) h r
          (unrootedBoundaryIndex i + 1) (unrootedRankIndex i) tau ℚ hcard,
      ← Renaming.GenericStratumMass.mass_genericWreath_unrootedStratum_of_card
          (L := L) (n - unrootedCellIndex i) h r
          (m - unrootedBoundaryIndex i + 1)
          (b - unrootedRankIndex i) tau ℚ hcard]
  rw [hsum] at hrec
  exact hrec

/-- Fully normalized all-rank rooted recurrence.  The base side is intrinsic,
so the bridge convolution has coefficient `r`, not `r/2`; `ell = 0` is in
the index type `Fin n`. -/
theorem rooted_numerical_all_rank_recurrence
    (n h₀ h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (hbridge :
      Fintype.card (RootedBridgePointed n h₀ h r m b) =
        r * rootedRawBridgeSum n h₀ h r m b) :
    ((n + b : ℕ) : ℚ) * PsiMass L n h₀ h r m b =
      ((r : ℚ) / 2) * rootedCyclePrevious L n h₀ h r m b +
        (r : ℚ) * rootedMassConvolution L n h₀ h r m b := by
  classical
  have hrec :=
    RecurrenceAssembly.rooted_mass_recurrence_of_bridge_cardinality
      (I := RootedIndex n m b) (L := L) n h₀ h r m b tau
      rootedCellIndex rootedBoundaryIndex
      (rootedLeftCard h₀ h r) (rootedRightCard n h r m b)
      (fun i ↦ Nat.le_of_lt i.1.2) hcard hbridge
  have hsum :
      (∑ i : RootedIndex n m b,
        normalizedSummand n m tau rootedCellIndex rootedBoundaryIndex
          (rootedLeftCard h₀ h r) (rootedRightCard n h r m b) i) =
        rootedMassConvolution L n h₀ h r m b := by
    apply Fintype.sum_congr
    intro i
    unfold normalizedSummand rootedMassSummand rootedLeftCard rootedRightCard
    rw [← Renaming.GenericRootedStratumAction.mass_genericWreath_rootedStratum_of_card
          (L := L) (rootedCellIndex i) h₀ h r
          (rootedBoundaryIndex i + 1) (rootedRankIndex i) tau ℚ hcard,
      ← Renaming.GenericStratumMass.mass_genericWreath_unrootedStratum_of_card
          (L := L) (n - rootedCellIndex i) h r
          (m - rootedBoundaryIndex i + 1)
          (b - rootedRankIndex i) tau ℚ hcard]
  rw [hsum] at hrec
  exact hrec

/-! ## Rank-zero `R` and `T` APIs -/

/-- Traditional tree mass: the boundary parameter is forced by `n` and
`h`, so it is suppressed from the notation. -/
abbrev RMass
    (L : Type uL) [Group L] [Fintype L] (n h r : ℕ)
    [MulAction L (Fin h)] : ℚ :=
  UMass L n h r (treeBoundary h n) 0

/-- Traditional fixed-base tree mass. -/
abbrev TMass
    (L : Type uL) [Group L] [Fintype L] (n h₀ h r : ℕ)
    [MulAction L (Fin h)] : ℚ :=
  PsiMass L n h₀ h r (rootedTreeBoundary h₀ h n) 0

def treeMassSummand
    (L : Type uL) [Group L] [Fintype L] (n h r : ℕ)
    [MulAction L (Fin h)] (k : BridgeAllocationCounting.ProperCellSize n) :
    ℚ :=
  (Nat.choose (treeBoundary h n) (treeBoundary h k.1 - 1) : ℚ) *
    RMass L k.1 h r * RMass L (n - k.1) h r

def fixedTreeMassSummand
    (L : Type uL) [Group L] [Fintype L] (n h₀ h r : ℕ)
    [MulAction L (Fin h)] (k : Fin n) : ℚ :=
  (Nat.choose (rootedTreeBoundary h₀ h n)
      (treeBoundary h (n - k.1) - 1) : ℚ) *
    TMass L k.1 h₀ h r * RMass L (n - k.1) h r

/-! A finite sum may be divided by one fixed denominator termwise. -/

theorem sum_mul_div_mul
    {I : Type*} [Fintype I] (f : I → ℚ) (a b : ℚ) :
    (∑ i : I, f i) / (a * b) =
      ∑ i : I, (f i / a) / b := by
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Fintype.sum_congr
  intro i
  rw [mul_inv_rev]
  ac_rfl

theorem normalized_tree_sum_of_raw
    {I : Type*} [Fintype I]
    (c A B : I → ℕ) (c₀ A₀ B₀ : ℕ)
    (O₁ O₂ : ℕ)
    (hraw : ∑ i : I, c i * A i * B i = c₀ * A₀ * B₀) :
    (∑ i : I,
        (c i : ℚ) * ((A i : ℚ) / (O₁ : ℚ)) *
          ((B i : ℚ) / (O₂ : ℚ))) =
      (c₀ : ℚ) * ((A₀ : ℚ) / (O₁ : ℚ)) *
        ((B₀ : ℚ) / (O₂ : ℚ)) := by
  have hrawQ :
      (∑ i : I, ((c i * A i * B i : ℕ) : ℚ)) =
        ((c₀ * A₀ * B₀ : ℕ) : ℚ) := by
    simpa only [Nat.cast_sum] using congrArg (fun z : ℕ ↦ (z : ℚ)) hraw
  simp only [Nat.cast_mul] at hrawQ
  calc
    (∑ i : I,
        (c i : ℚ) * ((A i : ℚ) / (O₁ : ℚ)) *
          ((B i : ℚ) / (O₂ : ℚ))) =
      (∑ i : I, (c i : ℚ) * (A i : ℚ) * (B i : ℚ)) /
        ((O₁ : ℚ) * (O₂ : ℚ)) := by
          rw [sum_mul_div_mul]
          apply Fintype.sum_congr
          intro i
          symm
          calc
            ((c i : ℚ) * (A i : ℚ) * (B i : ℚ)) /
                (O₁ : ℚ) / (O₂ : ℚ) =
              ((c i : ℚ) * (A i : ℚ) * (B i : ℚ)) /
                ((O₁ : ℚ) * (O₂ : ℚ)) := div_div _ _ _
            _ = (c i : ℚ) * ((A i : ℚ) / (O₁ : ℚ)) *
                ((B i : ℚ) / (O₂ : ℚ)) := by
              symm
              calc
            (c i : ℚ) * ((A i : ℚ) / (O₁ : ℚ)) *
                ((B i : ℚ) / (O₂ : ℚ)) =
              ((c i : ℚ) * (A i : ℚ)) / (O₁ : ℚ) *
                ((B i : ℚ) / (O₂ : ℚ)) := by rw [mul_div_assoc]
            _ = ((c i : ℚ) * (A i : ℚ) * (B i : ℚ)) /
                ((O₁ : ℚ) * (O₂ : ℚ)) := div_mul_div_comm _ _ _ _
    _ = ((c₀ : ℚ) * (A₀ : ℚ) * (B₀ : ℚ)) /
        ((O₁ : ℚ) * (O₂ : ℚ)) := by rw [hrawQ]
    _ = (c₀ : ℚ) * ((A₀ : ℚ) / (O₁ : ℚ)) *
        ((B₀ : ℚ) / (O₂ : ℚ)) := by
          symm
          calc
            (c₀ : ℚ) * ((A₀ : ℚ) / (O₁ : ℚ)) *
                ((B₀ : ℚ) / (O₂ : ℚ)) =
              ((c₀ : ℚ) * (A₀ : ℚ)) / (O₁ : ℚ) *
                ((B₀ : ℚ) / (O₂ : ℚ)) := by rw [mul_div_assoc]
            _ = ((c₀ : ℚ) * (A₀ : ℚ) * (B₀ : ℚ)) /
                ((O₁ : ℚ) * (O₂ : ℚ)) := div_mul_div_comm _ _ _ _

/-! ## Eliminating the all-rank boundary index -/

def unrootedCollapsedMassSummand
    (L : Type uL) [Group L] [Fintype L] (n h r m b : ℕ)
    [MulAction L (Fin h)]
    (k : BridgeAllocationCounting.ProperCellSize n) (p : Fin (b + 1)) :
    ℚ :=
  let s := cyclicComponentOldBoundary h k.1 p.1
  (Nat.choose m s : ℚ) * UMass L k.1 h r (s + 1) p.1 *
    UMass L (n - k.1) h r (m - s + 1) (b - p.1)

def rootedCollapsedMassSummand
    (L : Type uL) [Group L] [Fintype L] (n h₀ h r m b : ℕ)
    [MulAction L (Fin h)] (k : Fin n) (p : Fin (b + 1)) : ℚ :=
  let s := rootedCyclicComponentOldBoundary h₀ h k.1 p.1
  (Nat.choose m s : ℚ) * PsiMass L k.1 h₀ h r (s + 1) p.1 *
    UMass L (n - k.1) h r (m - s + 1) (b - p.1)

def unrootedCollapsedMassConvolution
    (L : Type uL) [Group L] [Fintype L] (n h r m b : ℕ)
    [MulAction L (Fin h)] : ℚ :=
  ∑ k : BridgeAllocationCounting.ProperCellSize n,
    ∑ p : Fin (b + 1), unrootedCollapsedMassSummand L n h r m b k p

def rootedCollapsedMassConvolution
    (L : Type uL) [Group L] [Fintype L] (n h₀ h r m b : ℕ)
    [MulAction L (Fin h)] : ℚ :=
  ∑ k : Fin n, ∑ p : Fin (b + 1),
    rootedCollapsedMassSummand L n h₀ h r m b k p

/-- Boundary-balance eliminates the `s` sum from the all-rank unrooted
convolution, producing the manuscript lower index
`(h-2)k+1-2p`. -/
theorem unrootedMassConvolution_eq_collapsed
    (n h r m b : ℕ) [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) :
    unrootedMassConvolution L n h r m b =
      unrootedCollapsedMassConvolution L n h r m b := by
  classical
  unfold unrootedMassConvolution unrootedCollapsedMassConvolution
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro k
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Fintype.sum_congr
  intro p
  have hraw := sum_unrooted_bridge_components_eq_single_boundary
    n h r m b k.1 p.1 hh
  have hnorm := normalized_tree_sum_of_raw
    (fun s : Fin (m + 1) ↦ Nat.choose m s.1)
    (fun s ↦ Fintype.card (UnrootedStratum k.1 h r (s.1 + 1) p.1))
    (fun s ↦ Fintype.card
      (UnrootedStratum (n - k.1) h r (m - s.1 + 1) (b - p.1)))
    (Nat.choose m (cyclicComponentOldBoundary h k.1 p.1))
    (Fintype.card (UnrootedStratum k.1 h r
      (cyclicComponentOldBoundary h k.1 p.1 + 1) p.1))
    (Fintype.card (UnrootedStratum (n - k.1) h r
      (m - cyclicComponentOldBoundary h k.1 p.1 + 1) (b - p.1)))
    ((k.1.1).factorial * Fintype.card L ^ k.1.1)
    ((n - k.1.1).factorial * Fintype.card L ^ (n - k.1.1)) hraw
  simpa [unrootedMassSummand, unrootedCollapsedMassSummand,
    unrootedCellIndex, unrootedBoundaryIndex, unrootedRankIndex,
    Renaming.GenericStratumMass.mass_genericWreath_unrootedStratum]
    using hnorm

/-- Rooted analogue; `k=0` remains present. -/
theorem rootedMassConvolution_eq_collapsed
    (n h₀ h r m b : ℕ) [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) :
    rootedMassConvolution L n h₀ h r m b =
      rootedCollapsedMassConvolution L n h₀ h r m b := by
  classical
  unfold rootedMassConvolution rootedCollapsedMassConvolution
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro k
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Fintype.sum_congr
  intro p
  have hraw := sum_rooted_bridge_components_eq_single_boundary
    n h₀ h r m b k.1 p.1 hh
  have hnorm := normalized_tree_sum_of_raw
    (fun s : Fin (m + 1) ↦ Nat.choose m s.1)
    (fun s ↦ Fintype.card (RootedStratum k.1 h₀ h r (s.1 + 1) p.1))
    (fun s ↦ Fintype.card
      (UnrootedStratum (n - k.1) h r (m - s.1 + 1) (b - p.1)))
    (Nat.choose m (rootedCyclicComponentOldBoundary h₀ h k.1 p.1))
    (Fintype.card (RootedStratum k.1 h₀ h r
      (rootedCyclicComponentOldBoundary h₀ h k.1 p.1 + 1) p.1))
    (Fintype.card (UnrootedStratum (n - k.1) h r
      (m - rootedCyclicComponentOldBoundary h₀ h k.1 p.1 + 1)
      (b - p.1)))
    (k.1.factorial * Fintype.card L ^ k.1)
    ((n - k.1).factorial * Fintype.card L ^ (n - k.1)) hraw
  simpa [rootedMassSummand, rootedCollapsedMassSummand,
    rootedCellIndex, rootedBoundaryIndex, rootedRankIndex,
    Renaming.GenericRootedStratumAction.mass_genericWreath_rootedStratum,
    Renaming.GenericStratumMass.mass_genericWreath_unrootedStratum]
    using hnorm

/-- Boundary-collapsed all-rank `U` recurrence in manuscript form. -/
theorem unrooted_numerical_collapsed_all_rank_recurrence
    (n h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hcard : Fintype.card L = tau)
    (hbridge :
      2 * Fintype.card (UnrootedBridgePointed n h r m b) =
        r * unrootedRawBridgeSum n h r m b) :
    ((n + b - 1 : ℕ) : ℚ) * UMass L n h r m b =
      ((r : ℚ) / 2) * unrootedCyclePrevious L n h r m b +
        ((r : ℚ) / 2) *
          unrootedCollapsedMassConvolution L n h r m b := by
  rw [← unrootedMassConvolution_eq_collapsed (L := L) n h r m b hh]
  exact unrooted_numerical_all_rank_recurrence
    (L := L) n h r m b tau hcard hbridge

/-- Boundary-collapsed all-rank `Psi` recurrence; `ell=0` remains included. -/
theorem rooted_numerical_collapsed_all_rank_recurrence
    (n h₀ h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hcard : Fintype.card L = tau)
    (hbridge :
      Fintype.card (RootedBridgePointed n h₀ h r m b) =
        r * rootedRawBridgeSum n h₀ h r m b) :
    ((n + b : ℕ) : ℚ) * PsiMass L n h₀ h r m b =
      ((r : ℚ) / 2) * rootedCyclePrevious L n h₀ h r m b +
        (r : ℚ) * rootedCollapsedMassConvolution L n h₀ h r m b := by
  rw [← rootedMassConvolution_eq_collapsed (L := L) n h₀ h r m b hh]
  exact rooted_numerical_all_rank_recurrence
    (L := L) n h₀ h r m b tau hcard hbridge

/-- For an unrooted tree, the full numerical component convolution collapses
to the legacy single sum over proper cell splits.  No support condition is
assumed: impossible boundary indices have already been proved cardinal-zero.
-/
theorem unrootedMassConvolution_tree_eq_legacy
    (n h r : ℕ) [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) :
    unrootedMassConvolution L n h r (treeBoundary h n) 0 =
      ∑ k : BridgeAllocationCounting.ProperCellSize n,
        treeMassSummand L n h r k := by
  classical
  unfold unrootedMassConvolution
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro k
  rw [Fintype.sum_prod_type]
  have hraw := sum_unrooted_tree_components_legacy
    n h r k.1 hh (Nat.le_of_lt k.2.2)
  have hmass :
      (∑ s : Fin (treeBoundary h n + 1),
        (Nat.choose (treeBoundary h n) s.1 : ℚ) *
          UMass L k.1 h r (s.1 + 1) 0 *
          UMass L (n - k.1) h r
            (treeBoundary h n - s.1 + 1) 0) =
        treeMassSummand L n h r k := by
    have hnorm := normalized_tree_sum_of_raw
      (fun s : Fin (treeBoundary h n + 1) ↦
        Nat.choose (treeBoundary h n) s.1)
      (fun s ↦ Fintype.card (UnrootedStratum k.1 h r (s.1 + 1) 0))
      (fun s ↦ Fintype.card
        (UnrootedStratum (n - k.1) h r
          (treeBoundary h n - s.1 + 1) 0))
      (Nat.choose (treeBoundary h n) (treeBoundary h k.1 - 1))
      (Fintype.card (UnrootedStratum k.1 h r (treeBoundary h k.1) 0))
      (Fintype.card
        (UnrootedStratum (n - k.1) h r (treeBoundary h (n - k.1)) 0))
      ((k.1.1).factorial * Fintype.card L ^ k.1.1)
      ((n - k.1.1).factorial * Fintype.card L ^ (n - k.1.1)) hraw
    simpa [treeMassSummand, RMass,
      Renaming.GenericStratumMass.mass_genericWreath_unrootedStratum]
      using hnorm
  simpa [unrootedMassSummand, unrootedBoundaryIndex, unrootedRankIndex,
    unrootedCellIndex] using hmass

/-- The rooted rank-zero convolution likewise collapses to the legacy fixed-
base tree sum, including the `k=0` direct attachment term. -/
theorem rootedMassConvolution_tree_eq_legacy
    (n h₀ h r : ℕ) [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hbase : 1 ≤ h₀) :
    rootedMassConvolution L n h₀ h r (rootedTreeBoundary h₀ h n) 0 =
      ∑ k : Fin n, fixedTreeMassSummand L n h₀ h r k := by
  classical
  unfold rootedMassConvolution
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro k
  rw [Fintype.sum_prod_type]
  have hraw := sum_rooted_tree_components_legacy
    n h₀ h r k.1 hh (Nat.le_of_lt k.2) hbase
  have hmass :
      (∑ s : Fin (rootedTreeBoundary h₀ h n + 1),
        (Nat.choose (rootedTreeBoundary h₀ h n) s.1 : ℚ) *
          PsiMass L k.1 h₀ h r (s.1 + 1) 0 *
          UMass L (n - k.1) h r
            (rootedTreeBoundary h₀ h n - s.1 + 1) 0) =
        fixedTreeMassSummand L n h₀ h r k := by
    have hnorm := normalized_tree_sum_of_raw
      (fun s : Fin (rootedTreeBoundary h₀ h n + 1) ↦
        Nat.choose (rootedTreeBoundary h₀ h n) s.1)
      (fun s ↦ Fintype.card (RootedStratum k.1 h₀ h r (s.1 + 1) 0))
      (fun s ↦ Fintype.card
        (UnrootedStratum (n - k.1) h r
          (rootedTreeBoundary h₀ h n - s.1 + 1) 0))
      (Nat.choose (rootedTreeBoundary h₀ h n)
        (treeBoundary h (n - k.1) - 1))
      (Fintype.card
        (RootedStratum k.1 h₀ h r (rootedTreeBoundary h₀ h k.1) 0))
      (Fintype.card
        (UnrootedStratum (n - k.1) h r (treeBoundary h (n - k.1)) 0))
      (k.1.factorial * Fintype.card L ^ k.1)
      ((n - k.1).factorial * Fintype.card L ^ (n - k.1)) hraw
    simpa [fixedTreeMassSummand, TMass, RMass,
      Renaming.GenericRootedStratumAction.mass_genericWreath_rootedStratum,
      Renaming.GenericStratumMass.mass_genericWreath_unrootedStratum]
      using hnorm
  simpa [rootedMassSummand, rootedBoundaryIndex, rootedRankIndex,
    rootedCellIndex] using hmass

/-- Corrected legacy `R` recurrence, derived from the same literal bridge
cardinality equality as the all-rank theorem. -/
theorem tree_R_recurrence
    (n h r tau : ℕ) [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hcard : Fintype.card L = tau)
    (hbridge :
      2 * Fintype.card
          (UnrootedBridgePointed n h r (treeBoundary h n) 0) =
        r * unrootedRawBridgeSum n h r (treeBoundary h n) 0) :
    ((n - 1 : ℕ) : ℚ) * RMass L n h r =
      ((r : ℚ) / 2) *
        ∑ k : BridgeAllocationCounting.ProperCellSize n,
          treeMassSummand L n h r k := by
  have hrec := unrooted_numerical_all_rank_recurrence
    (L := L) n h r (treeBoundary h n) 0 tau hcard hbridge
  rw [unrootedCyclePrevious_zero,
    unrootedMassConvolution_tree_eq_legacy (L := L) n h r hh] at hrec
  simpa [RMass] using hrec

/-- Corrected legacy fixed-base `T` recurrence.  The sum runs over `Fin n`,
so the direct attachment to the base (`k=0`) is present and there is no
extraneous factor `1/2`. -/
theorem fixed_tree_T_recurrence
    (n h₀ h r tau : ℕ) [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hbase : 1 ≤ h₀)
    (hcard : Fintype.card L = tau)
    (hbridge :
      Fintype.card
          (RootedBridgePointed n h₀ h r (rootedTreeBoundary h₀ h n) 0) =
        r * rootedRawBridgeSum n h₀ h r (rootedTreeBoundary h₀ h n) 0) :
    (n : ℚ) * TMass L n h₀ h r =
      (r : ℚ) * ∑ k : Fin n, fixedTreeMassSummand L n h₀ h r k := by
  have hrec := rooted_numerical_all_rank_recurrence
    (L := L) n h₀ h r (rootedTreeBoundary h₀ h n) 0 tau hcard hbridge
  rw [rootedCyclePrevious_zero,
    rootedMassConvolution_tree_eq_legacy (L := L) n h₀ h r hh hbase] at hrec
  simpa [TMass] using hrec


end
end NumericalRecurrenceAssembly
end FacetPairing
end PolytopeCounting
