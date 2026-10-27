module

public import Proofs.RootedGlobalBridgeCut
public import Proofs.LabelledReindexing
public import Proofs.BridgeAllocationCounting
public import Proofs.NumericalBridgeCut
public import Proofs.NonbridgeExact

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-! Allocation-enriched numerical target for the rooted bridge branch. -/

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

open RootedGlobalBridgeCut PointedDecomposition LabelledCutJoin
open NumericalBridgeCut

abbrev CellAllocation (n ℓ : ℕ) :=
  {A : Finset (Fin n) // A.card = ℓ}

/-- An oriented base-side boundary block contains the compulsory first star,
excludes the other star, and chooses `s` of the old labels. -/
abbrev BoundaryAllocation (m s : ℕ) :=
  BridgeAllocationCounting.BoundaryAllocation m s

@[simp]
theorem card_cellAllocation (n ℓ : ℕ) :
    Fintype.card (CellAllocation n ℓ) = Nat.choose n ℓ := by
  simpa using (@Fintype.card_finset_len (Fin n) _ ℓ)

@[simp]
theorem card_boundaryAllocation (m s : ℕ) :
    Fintype.card (BoundaryAllocation m s) = Nat.choose m s :=
  BridgeAllocationCounting.card_boundaryAllocation m s

noncomputable local instance rootedStratumFintype
    (n h₀ h r m b : ℕ) : Fintype (RootedStratum n h₀ h r m b) :=
  Fintype.ofFinite _

noncomputable local instance unrootedStratumFintype
    (n h r m b : ℕ) : Fintype (UnrootedStratum n h r m b) :=
  Fintype.ofFinite _

abbrev ComponentProduct
    (n h₀ h r m b : ℕ) (ℓ : Fin n) (s : Fin (m + 1))
    (p : Fin (b + 1)) :=
  RootedStratum ℓ.1 h₀ h r (s.1 + 1) p.1 ×
    UnrootedStratum (n - ℓ.1) h r (m - s.1 + 1) (b - p.1) ×
      Fin r

/-- Exact allocation-enriched target. The `Fin n` index admits `ℓ=0` and
forces the away-side component to contain at least one ordinary cell. -/
abbrev Coproduct (n h₀ h r m b : ℕ) :=
  Σ ℓ : Fin n,
    Σ s : Fin (m + 1),
      Σ p : Fin (b + 1),
        CellAllocation n ℓ.1 × BoundaryAllocation m s.1 ×
          ComponentProduct n h₀ h r m b ℓ s p

theorem rank_split_add (p : Fin (b + 1)) :
    p.1 + (b - p.1) = b := by
  have hp : p.1 ≤ b := by omega
  exact Nat.add_sub_of_le hp

theorem cell_index_lt (d : Coproduct n h₀ h r m b) : d.1.1 < n :=
  d.1.2

theorem boundary_index_le (d : Coproduct n h₀ h r m b) :
    d.2.1.1 ≤ m := by omega

theorem card_allocationFiber (n m : ℕ) (ℓ : Fin n) (s : Fin (m + 1)) :
    Fintype.card (CellAllocation n ℓ.1 × BoundaryAllocation m s.1) =
      Nat.choose n ℓ.1 * Nat.choose m s.1 := by
  simp [Fintype.card_prod]

theorem card_coproduct (n h₀ h r m b : ℕ) :
    Fintype.card (Coproduct n h₀ h r m b) =
      ∑ ℓ : Fin n, ∑ s : Fin (m + 1), ∑ p : Fin (b + 1),
        Nat.choose n ℓ.1 * Nat.choose m s.1 *
          Fintype.card (RootedStratum ℓ.1 h₀ h r (s.1 + 1) p.1) *
          Fintype.card
            (UnrootedStratum (n - ℓ.1) h r
              (m - s.1 + 1) (b - p.1)) * r := by
  classical
  simp only [Coproduct, ComponentProduct, Fintype.card_sigma,
    Fintype.card_prod, card_cellAllocation, card_boundaryAllocation,
    Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro ℓ _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  ac_rfl

theorem card_coproduct_rankPair (n h₀ h r m b : ℕ) :
    Fintype.card (Coproduct n h₀ h r m b) =
      ∑ ℓ : Fin n, ∑ s : Fin (m + 1), ∑ p : Fin (b + 1),
        Nat.choose n ℓ.1 * Nat.choose m s.1 *
          Fintype.card (RootedStratum ℓ.1 h₀ h r (s.1 + 1) p.1) *
          Fintype.card
            (UnrootedStratum (n - ℓ.1) h r
              (m - s.1 + 1) (b - p.1)) *
          Fintype.card (Fin r) := by
  simpa using card_coproduct n h₀ h r m b


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

