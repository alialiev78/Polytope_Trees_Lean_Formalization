module

public import Proofs.FiniteCounting
public import Proofs.LabelledCutJoin
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Exact allocation fibres in the bridge coproduct

Cutting a bridge does not merely remember the numerical sizes of the two
components.  It remembers which ambient cell labels and which old boundary
labels lie on the oriented left side.  This module counts those literal
allocation fibres.  These are the two binomial coefficients which are later
cancelled (cells) or retained (boundary labels) by wreath normalization.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace BridgeAllocationCounting

open LabelledCutJoin

noncomputable section

open scoped BigOperators

/-! ## Cell-label allocations -/

/-- Literal choices of `k` among the `n` ambient cell labels. -/
abbrev CellAllocation (n k : ℕ) :=
  {A : Finset (Fin n) // A.card = k}

/-- The cell-allocation fibre has the expected binomial cardinality. -/
theorem card_cellAllocation (n k : ℕ) :
    Fintype.card (CellAllocation n k) = Nat.choose n k := by
  exact FiniteCounting.card_labelPartitions n k

/-! ## Boundary-label allocations -/

/-- All cut-boundary labels except the two freshly exposed endpoint labels. -/
def oldBoundaryUniverse (m : ℕ) : Finset (Fin (m + 2)) :=
  ((Finset.univ : Finset (Fin (m + 2))).erase (firstStar m)).erase
    (secondStar m)

@[simp]
theorem firstStar_not_mem_oldBoundaryUniverse (m : ℕ) :
    firstStar m ∉ oldBoundaryUniverse m := by
  simp [oldBoundaryUniverse]

@[simp]
theorem secondStar_not_mem_oldBoundaryUniverse (m : ℕ) :
    secondStar m ∉ oldBoundaryUniverse m := by
  simp [oldBoundaryUniverse]

/-- Removing the two new endpoint labels leaves exactly the `m` old labels. -/
theorem card_oldBoundaryUniverse (m : ℕ) :
    (oldBoundaryUniverse m).card = m := by
  have hne : firstStar m ≠ secondStar m := firstStar_ne_secondStar m
  rw [oldBoundaryUniverse, Finset.card_erase_of_mem]
  · rw [Finset.card_erase_of_mem]
    · simp
    · exact Finset.mem_univ _
  · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact hne.symm

/-- An oriented left boundary block of total size `s+1`: it contains the
first exposed endpoint, excludes the second, and contains `s` old labels. -/
abbrev BoundaryAllocation (m s : ℕ) :=
  {B : Finset (Fin (m + 2)) //
    firstStar m ∈ B ∧ secondStar m ∉ B ∧ B.card = s + 1}

/-- Erase the compulsory first endpoint from an oriented boundary block. -/
def boundaryAllocationToOld (m s : ℕ) (B : BoundaryAllocation m s) :
    {A : Finset (Fin (m + 2)) //
      A ∈ (oldBoundaryUniverse m).powersetCard s} := by
  refine ⟨B.1.erase (firstStar m), ?_⟩
  rw [Finset.mem_powersetCard]
  constructor
  · intro x hx
    have hxB : x ∈ B.1 := (Finset.mem_erase.mp hx).2
    have hxf : x ≠ firstStar m := (Finset.mem_erase.mp hx).1
    have hxs : x ≠ secondStar m := by
      intro h
      exact B.2.2.1 (h ▸ hxB)
    simp only [oldBoundaryUniverse, Finset.mem_erase, Finset.mem_univ,
      and_true]
    exact ⟨hxs, hxf⟩
  · rw [Finset.card_erase_of_mem B.2.1, B.2.2.2]
    omega

/-- Insert the compulsory first endpoint into a choice of `s` old labels. -/
def oldToBoundaryAllocation (m s : ℕ)
    (A : {A : Finset (Fin (m + 2)) //
      A ∈ (oldBoundaryUniverse m).powersetCard s}) :
    BoundaryAllocation m s := by
  refine ⟨insert (firstStar m) A.1, ?_⟩
  have hmem := Finset.mem_powersetCard.mp A.2
  have hfirst : firstStar m ∉ A.1 := by
    intro h
    exact firstStar_not_mem_oldBoundaryUniverse m (hmem.1 h)
  have hsecond : secondStar m ∉ A.1 := by
    intro h
    exact secondStar_not_mem_oldBoundaryUniverse m (hmem.1 h)
  refine ⟨Finset.mem_insert_self (firstStar m) A.1, ?_, ?_⟩
  · intro hs
    rw [Finset.mem_insert] at hs
    rcases hs with hs | hs
    · exact (firstStar_ne_secondStar m) hs.symm
    · exact hsecond hs
  · rw [Finset.card_insert_of_notMem hfirst, hmem.2]

/-- Exact equivalence between oriented boundary blocks and choices of old
labels.  No endpoint-orientation factor is hidden here. -/
def boundaryAllocationEquivPowerset (m s : ℕ) :
    BoundaryAllocation m s ≃
      {A : Finset (Fin (m + 2)) //
        A ∈ (oldBoundaryUniverse m).powersetCard s} where
  toFun := boundaryAllocationToOld m s
  invFun := oldToBoundaryAllocation m s
  left_inv B := by
    apply Subtype.ext
    exact Finset.insert_erase B.2.1
  right_inv A := by
    apply Subtype.ext
    change (insert (firstStar m) A.1).erase (firstStar m) = A.1
    rw [Finset.erase_insert]
    intro h
    have hmem := (Finset.mem_powersetCard.mp A.2).1 h
    exact firstStar_not_mem_oldBoundaryUniverse m hmem

/-- The boundary-allocation fibre has cardinality `choose m s`, including
`m=0` and all empty/out-of-range cases. -/
theorem card_boundaryAllocation (m s : ℕ) :
    Fintype.card (BoundaryAllocation m s) = Nat.choose m s := by
  rw [Fintype.card_congr (boundaryAllocationEquivPowerset m s)]
  rw [Fintype.card_coe, Finset.card_powersetCard,
    card_oldBoundaryUniverse]

/-! ## Independent cell and boundary allocations -/

/-- The complete allocation fibre over fixed numerical sizes. -/
abbrev AllocationFiber (n k m s : ℕ) :=
  CellAllocation n k × BoundaryAllocation m s

theorem card_allocationFiber (n k m s : ℕ) :
    Fintype.card (AllocationFiber n k m s) =
      Nat.choose n k * Nat.choose m s := by
  rw [Fintype.card_prod, card_cellAllocation, card_boundaryAllocation]

/-! ## Cardinality of an allocation-enriched dependent coproduct -/

/-- The admissible numerical size of the oriented left component. -/
abbrev ProperCellSize (n : ℕ) :=
  {k : Fin (n + 1) // 0 < k.1 ∧ k.1 < n}

/-- A generic allocation-enriched bridge coproduct.  `Left` and `Right`
may be instantiated by the two canonical connected rank strata. -/
abbrev EnrichedCoproduct
    (n m b r : ℕ)
    (Left Right : ProperCellSize n → Fin (m + 1) → Fin (b + 1) → Type*) :=
  Σ k : ProperCellSize n,
    Σ s : Fin (m + 1),
      Σ p : Fin (b + 1),
        AllocationFiber n k.1 m s.1 ×
          Left k s p × Right k s p × Fin r

/-- Counting the exact enriched coproduct exposes the two allocation
binomials and no other symmetry factor. -/
theorem card_enrichedCoproduct
    (n m b r : ℕ)
    (Left Right : ProperCellSize n → Fin (m + 1) → Fin (b + 1) → Type*)
    [∀ k s p, Fintype (Left k s p)]
    [∀ k s p, Fintype (Right k s p)] :
    Fintype.card (EnrichedCoproduct n m b r Left Right) =
      ∑ k : ProperCellSize n,
        ∑ s : Fin (m + 1),
          ∑ p : Fin (b + 1),
            Nat.choose n k.1 * Nat.choose m s.1 *
              Fintype.card (Left k s p) *
              Fintype.card (Right k s p) * r := by
  change Fintype.card
      (Σ k : ProperCellSize n,
        Σ s : Fin (m + 1),
          Σ p : Fin (b + 1),
            AllocationFiber n k.1 m s.1 ×
              Left k s p × Right k s p × Fin r) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro p _
  rw [Fintype.card_prod, card_allocationFiber,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
  ac_rfl


end
end BridgeAllocationCounting
end FacetPairing
end PolytopeCounting
