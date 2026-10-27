module

public import Proofs.UnrootedBridgeCoproduct
public import Proofs.NumericalRecurrenceAssembly

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Counting the exact unrooted bridge coproduct

`UnrootedBridgeCoproduct.Coproduct` is indexed by literal ambient cell and
boundary blocks and by a literal pair of complementary ranks.  The
recurrence layer is indexed by the three numerical parameters `k,s,p`.
This module proves the exact regrouping between them.

The two allocation fibers have cardinalities `choose n k` and `choose m s`.
The rank-pair fiber is a singleton.  Consequently the cardinality of the
literal coproduct is `r` times the raw numerical bridge sum.  Taking
cardinalities of any exact cut--join equivalence then immediately gives the
raw identity required by `NumericalRecurrenceAssembly`, with no certificate
or freeness assumption.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace UnrootedBridgeCoproductCounting

open scoped BigOperators

open PointedDecomposition LabelledCutJoin
open NumericalRecurrenceAssembly

noncomputable section

local instance unrootedStratumFintype (n h r m b : ℕ) :
    Fintype (UnrootedStratum n h r m b) := Fintype.ofFinite _

local instance unrootedBridgePointedFintype (n h r m b : ℕ) :
    Fintype (UnrootedBridgePointed n h r m b) := Fintype.ofFinite _

/-! ## Cell-allocation fibers -/

def cellSizeOf
    (A : UnrootedBridgeCoproduct.CellAllocation n) :
    BridgeAllocationCounting.ProperCellSize n :=
  ⟨⟨A.1.card, by
    have hle : A.1.card ≤ n := by
      simpa using Finset.card_le_univ A.1
    omega⟩, A.2.1, A.2.2⟩

@[simp]
theorem cellSizeOf_val
    (A : UnrootedBridgeCoproduct.CellAllocation n) :
    (cellSizeOf A).1.1 = A.1.card := rfl

def cellSizeFiberEquiv
    (k : BridgeAllocationCounting.ProperCellSize n) :
    {A : UnrootedBridgeCoproduct.CellAllocation n // cellSizeOf A = k} ≃
      BridgeAllocationCounting.CellAllocation n k.1.1 where
  toFun A := ⟨A.1.1, by
    have hk := congrArg
      (fun z : BridgeAllocationCounting.ProperCellSize n ↦ z.1.1) A.2
    simpa [cellSizeOf] using hk⟩
  invFun A :=
    ⟨⟨A.1, by simpa [A.2] using k.2.1,
        by simpa [A.2] using k.2.2⟩,
      by
        apply Subtype.ext
        apply Fin.ext
        simpa [cellSizeOf] using A.2⟩
  left_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    rfl

theorem card_cellSizeFiber
    (k : BridgeAllocationCounting.ProperCellSize n) :
    Fintype.card
        {A : UnrootedBridgeCoproduct.CellAllocation n // cellSizeOf A = k} =
      Nat.choose n k.1.1 := by
  rw [Fintype.card_congr (cellSizeFiberEquiv k)]
  exact BridgeAllocationCounting.card_cellAllocation n k.1.1

/-- Regroup any function depending only on the numerical size of a literal
proper cell block. -/
theorem sum_cellAllocations_by_size
    (F : ℕ → ℕ) :
    (∑ A : UnrootedBridgeCoproduct.CellAllocation n, F A.1.card) =
      ∑ k : BridgeAllocationCounting.ProperCellSize n,
        Nat.choose n k.1.1 * F k.1.1 := by
  classical
  calc
    (∑ A : UnrootedBridgeCoproduct.CellAllocation n, F A.1.card) =
        ∑ k : BridgeAllocationCounting.ProperCellSize n,
          ∑ A ∈ (Finset.univ :
              Finset (UnrootedBridgeCoproduct.CellAllocation n)) with
              cellSizeOf A = k,
            F A.1.card :=
      (Finset.sum_fiberwise
        (Finset.univ : Finset (UnrootedBridgeCoproduct.CellAllocation n))
        cellSizeOf (fun A ↦ F A.1.card)).symm
    _ = ∑ k : BridgeAllocationCounting.ProperCellSize n,
        Nat.choose n k.1.1 * F k.1.1 := by
      apply Fintype.sum_congr
      intro k
      have hcard :
          ((Finset.univ :
              Finset (UnrootedBridgeCoproduct.CellAllocation n)).filter
              (fun A ↦ cellSizeOf A = k)).card = Nat.choose n k.1.1 := by
        rw [← Fintype.card_subtype]
        exact card_cellSizeFiber k
      calc
        (∑ A ∈ (Finset.univ :
              Finset (UnrootedBridgeCoproduct.CellAllocation n)) with
              cellSizeOf A = k,
            F A.1.card) =
            ∑ _A ∈ (Finset.univ :
              Finset (UnrootedBridgeCoproduct.CellAllocation n)).filter
              (fun A ↦ cellSizeOf A = k), F k.1.1 := by
                apply Finset.sum_congr rfl
                intro A hA
                have hsize := (Finset.mem_filter.mp hA).2
                have hval := congrArg
                  (fun z : BridgeAllocationCounting.ProperCellSize n ↦ z.1.1)
                  hsize
                simpa [cellSizeOf] using congrArg F hval
        _ = ((Finset.univ :
              Finset (UnrootedBridgeCoproduct.CellAllocation n)).filter
              (fun A ↦ cellSizeOf A = k)).card * F k.1.1 := by simp
        _ = Nat.choose n k.1.1 * F k.1.1 := by rw [hcard]

/-! ## Boundary-allocation fibers -/

theorem erasedFirst_subset_oldUniverse
    (B : UnrootedBridgeCoproduct.BoundaryAllocation m) :
    B.1.erase (firstStar m) ⊆
      BridgeAllocationCounting.oldBoundaryUniverse m := by
  intro i hi
  have hiB := (Finset.mem_erase.mp hi).2
  have hif : i ≠ firstStar m := (Finset.mem_erase.mp hi).1
  have his : i ≠ secondStar m := by
    intro h
    exact B.2.2 (h ▸ hiB)
  simp only [BridgeAllocationCounting.oldBoundaryUniverse,
    Finset.mem_erase, Finset.mem_univ, and_true]
  exact ⟨his, hif⟩

def boundarySizeOf
    (B : UnrootedBridgeCoproduct.BoundaryAllocation m) : Fin (m + 1) :=
  ⟨(B.1.erase (firstStar m)).card, by
    have hle := Finset.card_le_card (erasedFirst_subset_oldUniverse B)
    rw [BridgeAllocationCounting.card_oldBoundaryUniverse] at hle
    omega⟩

theorem boundary_card_eq_size_add_one
    (B : UnrootedBridgeCoproduct.BoundaryAllocation m) :
    B.1.card = (boundarySizeOf B).1 + 1 := by
  change B.1.card = (B.1.erase (firstStar m)).card + 1
  exact (Finset.card_erase_add_one B.2.1).symm

def boundarySizeFiberEquiv (s : Fin (m + 1)) :
    {B : UnrootedBridgeCoproduct.BoundaryAllocation m // boundarySizeOf B = s} ≃
      BridgeAllocationCounting.BoundaryAllocation m s.1 where
  toFun B := ⟨B.1.1, B.1.2.1, B.1.2.2, by
    rw [boundary_card_eq_size_add_one]
    have hs := congrArg (fun z : Fin (m + 1) ↦ z.1) B.2
    simpa using congrArg (fun z : ℕ ↦ z + 1) hs⟩
  invFun B := ⟨⟨B.1, B.2.1, B.2.2.1⟩, by
    apply Fin.ext
    change (B.1.erase (firstStar m)).card = s.1
    rw [Finset.card_erase_of_mem B.2.1, B.2.2.2]
    omega⟩
  left_inv B := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv B := by
    apply Subtype.ext
    rfl

theorem card_boundarySizeFiber (s : Fin (m + 1)) :
    Fintype.card
        {B : UnrootedBridgeCoproduct.BoundaryAllocation m //
          boundarySizeOf B = s} = Nat.choose m s.1 := by
  rw [Fintype.card_congr (boundarySizeFiberEquiv s)]
  exact BridgeAllocationCounting.card_boundaryAllocation m s.1

/-- Regroup any function depending only on the total boundary size of a
literal oriented block.  The numerical index counts old labels, hence the
argument `s+1`. -/
theorem sum_boundaryAllocations_by_size
    (F : ℕ → ℕ) :
    (∑ B : UnrootedBridgeCoproduct.BoundaryAllocation m, F B.1.card) =
      ∑ s : Fin (m + 1), Nat.choose m s.1 * F (s.1 + 1) := by
  classical
  calc
    (∑ B : UnrootedBridgeCoproduct.BoundaryAllocation m, F B.1.card) =
        ∑ s : Fin (m + 1),
          ∑ B ∈ (Finset.univ :
              Finset (UnrootedBridgeCoproduct.BoundaryAllocation m)) with
              boundarySizeOf B = s,
            F B.1.card :=
      (Finset.sum_fiberwise
        (Finset.univ : Finset (UnrootedBridgeCoproduct.BoundaryAllocation m))
        boundarySizeOf (fun B ↦ F B.1.card)).symm
    _ = ∑ s : Fin (m + 1), Nat.choose m s.1 * F (s.1 + 1) := by
      apply Fintype.sum_congr
      intro s
      have hcard :
          ((Finset.univ :
              Finset (UnrootedBridgeCoproduct.BoundaryAllocation m)).filter
              (fun B ↦ boundarySizeOf B = s)).card = Nat.choose m s.1 := by
        rw [← Fintype.card_subtype]
        exact card_boundarySizeFiber s
      calc
        (∑ B ∈ (Finset.univ :
              Finset (UnrootedBridgeCoproduct.BoundaryAllocation m)) with
              boundarySizeOf B = s,
            F B.1.card) =
            ∑ _B ∈ (Finset.univ :
              Finset (UnrootedBridgeCoproduct.BoundaryAllocation m)).filter
              (fun B ↦ boundarySizeOf B = s), F (s.1 + 1) := by
                apply Finset.sum_congr rfl
                intro B hB
                have hsize := (Finset.mem_filter.mp hB).2
                have hs := congrArg (fun z : Fin (m + 1) ↦ z.1) hsize
                rw [boundary_card_eq_size_add_one]
                exact congrArg (fun z : ℕ ↦ F (z + 1)) hs
        _ = ((Finset.univ :
              Finset (UnrootedBridgeCoproduct.BoundaryAllocation m)).filter
              (fun B ↦ boundarySizeOf B = s)).card * F (s.1 + 1) := by simp
        _ = Nat.choose m s.1 * F (s.1 + 1) := by rw [hcard]

/-! ## Rank-pair normalization -/

def rankSplitEquiv (b : ℕ) :
    UnrootedBridgeCoproduct.RankSplit b ≃ Fin (b + 1) where
  toFun q := q.1.1
  invFun p := ⟨(p, ⟨b - p.1, by omega⟩),
    Nat.add_sub_of_le (Nat.le_of_lt_succ p.2)⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      have hq : q.1.1.1 + q.1.2.1 = b := q.2
      have hle : q.1.1.1 ≤ b := by omega
      have hsub : b - q.1.1.1 = q.1.2.1 := by omega
      exact hsub
  right_inv p := rfl

theorem sum_rankSplits
    (F : ℕ → ℕ → ℕ) :
    (∑ q : UnrootedBridgeCoproduct.RankSplit b, F q.1.1.1 q.1.2.1) =
      ∑ p : Fin (b + 1), F p.1 (b - p.1) := by
  apply Fintype.sum_equiv (rankSplitEquiv b)
  intro q
  have hq : q.1.2.1 = b - q.1.1.1 := by
    omega
  change F q.1.1.1 q.1.2.1 = F q.1.1.1 (b - q.1.1.1)
  rw [hq]

/-! ## Exact coproduct cardinality -/

/-- Literal allocation/rank-pair coproduct cardinality, regrouped into the
raw numerical triple sum used by the recurrence. -/
theorem card_coproduct (n h r m b : ℕ) :
    Fintype.card (UnrootedBridgeCoproduct.Coproduct n h r m b) =
      r * unrootedRawBridgeSum n h r m b := by
  classical
  have hexpand :
      Fintype.card (UnrootedBridgeCoproduct.Coproduct n h r m b) =
        ∑ k : BridgeAllocationCounting.ProperCellSize n,
          Nat.choose n k.1.1 *
            ∑ s : Fin (m + 1), Nat.choose m s.1 *
              ∑ p : Fin (b + 1),
                Fintype.card
                    (UnrootedStratum k.1.1 h r (s.1 + 1) p.1) *
                  Fintype.card
                    (UnrootedStratum (n - k.1.1) h r
                      (m - s.1 + 1) (b - p.1)) * r := by
    let canonical :
        Fintype (UnrootedBridgeCoproduct.Coproduct n h r m b) :=
      @Sigma.instFintype
        (UnrootedBridgeCoproduct.CellAllocation n)
        (fun A ↦
          Σ B : UnrootedBridgeCoproduct.BoundaryAllocation m,
            Σ q : UnrootedBridgeCoproduct.RankSplit b,
              UnrootedStratum A.1.card h r B.1.card q.1.1 ×
                UnrootedStratum (n - A.1.card) h r
                  (m + 2 - B.1.card) q.1.2.1 × Fin r)
        (fun _ ↦ inferInstance) inferInstance
    have hinst :
        @Fintype.card _
            (UnrootedBridgeCoproduct.coproductFintype n h r m b) =
          @Fintype.card _ canonical := by
      exact @Fintype.card_congr _ _
        (UnrootedBridgeCoproduct.coproductFintype n h r m b)
        canonical (Equiv.refl _)
    rw [hinst]
    dsimp only [canonical]
    rw [Fintype.card_sigma]
    simp_rw [Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fin]
    change
      (∑ A : UnrootedBridgeCoproduct.CellAllocation n,
        ∑ B : UnrootedBridgeCoproduct.BoundaryAllocation m,
          ∑ q : UnrootedBridgeCoproduct.RankSplit b,
            Fintype.card
                (UnrootedStratum A.1.card h r B.1.card q.1.1.1) *
              (Fintype.card
                (UnrootedStratum (n - A.1.card) h r
                  (m + 2 - B.1.card) q.1.2.1) * r)) = _
    rw [sum_cellAllocations_by_size (n := n) (F := fun k ↦
      ∑ B : UnrootedBridgeCoproduct.BoundaryAllocation m,
        ∑ q : UnrootedBridgeCoproduct.RankSplit b,
          Fintype.card (UnrootedStratum k h r B.1.card q.1.1.1) *
            (Fintype.card (UnrootedStratum (n - k) h r
              (m + 2 - B.1.card) q.1.2.1) * r))]
    apply Fintype.sum_congr
    intro k
    congr 1
    change
      (∑ B : UnrootedBridgeCoproduct.BoundaryAllocation m,
        ∑ q : UnrootedBridgeCoproduct.RankSplit b,
          Fintype.card
              (UnrootedStratum k.1.1 h r B.1.card q.1.1.1) *
            (Fintype.card
              (UnrootedStratum (n - k.1.1) h r
                (m + 2 - B.1.card) q.1.2.1) * r)) = _
    rw [sum_boundaryAllocations_by_size (m := m) (F := fun a ↦
      ∑ q : UnrootedBridgeCoproduct.RankSplit b,
        Fintype.card (UnrootedStratum k.1.1 h r a q.1.1.1) *
          (Fintype.card (UnrootedStratum (n - k.1.1) h r
            (m + 2 - a) q.1.2.1) * r))]
    apply Fintype.sum_congr
    intro s
    congr 1
    rw [sum_rankSplits (b := b) (F := fun p q ↦
      Fintype.card (UnrootedStratum k.1.1 h r (s.1 + 1) p) *
        (Fintype.card (UnrootedStratum (n - k.1.1) h r
          (m + 2 - (s.1 + 1)) q) * r))]
    apply Fintype.sum_congr
    intro p
    have hk : (k.1.1 : ℕ) = k.1.1 := rfl
    have hsright : m + 2 - (s.1 + 1) = m - s.1 + 1 := by
      have hs : s.1 ≤ m := by omega
      omega
    rw [hsright]
    ac_rfl
  have hraw :
      unrootedRawBridgeSum n h r m b =
        ∑ k : BridgeAllocationCounting.ProperCellSize n,
          ∑ s : Fin (m + 1), ∑ p : Fin (b + 1),
            Nat.choose n k.1.1 * Nat.choose m s.1 *
              Fintype.card
                (UnrootedStratum k.1.1 h r (s.1 + 1) p.1) *
              Fintype.card
                (UnrootedStratum (n - k.1.1) h r
                  (m - s.1 + 1) (b - p.1)) := by
    unfold unrootedRawBridgeSum UnrootedIndex
    rw [Fintype.sum_prod_type]
    apply Fintype.sum_congr
    intro k
    rw [Fintype.sum_prod_type]
    rfl
  rw [hexpand, hraw]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Fintype.sum_congr
  intro k
  apply Fintype.sum_congr
  intro s
  apply Fintype.sum_congr
  intro p
  ac_rfl

/-! ## From an exact equivalence to the recurrence identity -/

/-- Any exact cut--join equivalence from an oriented bridge point to the
literal coproduct discharges the precise raw bridge-cardinality hypothesis
of `NumericalRecurrenceAssembly`. -/
theorem raw_bridge_cardinality_of_equiv
    (e : (UnrootedBridgePointed n h r m b × Bool) ≃
      UnrootedBridgeCoproduct.Coproduct n h r m b) :
    2 * Fintype.card (UnrootedBridgePointed n h r m b) =
      r * unrootedRawBridgeSum n h r m b := by
  have hcard := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_bool, card_coproduct] at hcard
  simpa [Nat.mul_comm] using hcard


end
end UnrootedBridgeCoproductCounting
end FacetPairing
end PolytopeCounting
