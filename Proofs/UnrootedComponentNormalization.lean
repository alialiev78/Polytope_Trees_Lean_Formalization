module

public import Proofs.UnrootedBridgeCoproduct
public import Proofs.AllocationNormalization

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Exact normalization of reconstructed unrooted bridge components

This module isolates the dependent boundary-label cancellation needed by the
inverse half of the numerical unrooted bridge coproduct.  It deliberately does
not modify the coproduct construction itself.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace UnrootedBridgeCoproduct

noncomputable section

open PointedDecomposition LabelledCutJoin GlobalBridgeCut
open NumericalBridgeCut

variable {n h r m b : ℕ}

/-- The left restriction recovered by the forward carrier is exactly the
literal restricted component used by the inverse construction. -/
theorem orientedCarrier_from_leftRestriction
    (d : Coproduct n h r m b) :
    HEq ((orientedCarrier (fromCoproduct d)).core.1.1.restrict
        (orientedCarrier (fromCoproduct d)).leftCells)
      (leftRestrictedPairing d).pairing := by
  rw [orientedCarrier_from_leftCells, orientedCarrier_from_core_pairing]
  exact heq_of_eq (reconstructedCut_restrict_left d)

/-- Right-component counterpart of `orientedCarrier_from_leftRestriction`. -/
theorem orientedCarrier_from_rightRestriction
    (d : Coproduct n h r m b) :
    HEq ((orientedCarrier (fromCoproduct d)).core.1.1.restrict
        (orientedCarrier (fromCoproduct d)).rightCells)
      (rightRestrictedPairing d).pairing := by
  rw [orientedCarrier_from_rightCells, orientedCarrier_from_core_pairing]
  exact heq_of_eq (reconstructedCut_restrict_right d)

/-- The reconstructed global label restricts on the left summand to the
allocated left label. -/
@[simp]
theorem reconstructedCutLabel_includeLeft
    (d : Coproduct n h r m b)
    (x : (leftRestrictedPairing d).pairing.Boundary) :
    reconstructedCutLabel d
        (includeLeftBoundary (leftCellSet d) (rightCellSet d)
          (cellSets_disjoint d)
          (leftRestrictedPairing d).pairing
          (rightRestrictedPairing d).pairing x) =
      (leftAllocatedLabel d x).1 := by
  simp only [reconstructedCutLabel, reconstructedCutPairing,
    Equiv.trans_apply, boundaryReassembleEquiv_includeLeft,
    Equiv.sumCongr_apply, Sum.map_inl, finsetSumComplementEquiv]
  rfl

/-- The reconstructed global label restricts on the right summand to the
allocated right label. -/
@[simp]
theorem reconstructedCutLabel_includeRight
    (d : Coproduct n h r m b)
    (x : (rightRestrictedPairing d).pairing.Boundary) :
    reconstructedCutLabel d
        (includeRightBoundary (leftCellSet d) (rightCellSet d)
          (cellSets_disjoint d)
          (leftRestrictedPairing d).pairing
          (rightRestrictedPairing d).pairing x) =
      (rightAllocatedLabel d x).1 := by
  simp only [reconstructedCutLabel, reconstructedCutPairing,
    Equiv.trans_apply, boundaryReassembleEquiv_includeRight,
    Equiv.sumCongr_apply, Sum.map_inr, finsetSumComplementEquiv]
  rfl

set_option maxHeartbeats 1000000 in
/-- Pointwise left-label coherence.  The hypothesis is phrased solely in
terms of the ambient dart, so it remains usable across the dependent change
from the recovered component subtype to the stored allocation subtype. -/
theorem leftBoundaryLabelMap_fromCoproduct_of_include_eq
    (d : Coproduct n h r m b)
    (x : ((orientedCarrier (fromCoproduct d)).core.1.1.restrict
      (orientedCarrier (fromCoproduct d)).leftCells).Boundary)
    (y : (leftRestrictedPairing d).pairing.Boundary)
    (hxy : includeDart
        (orientedCarrier (fromCoproduct d)).leftCells x.1 =
      includeDart (leftCellSet d) y.1) :
    leftBoundaryLabelMap (orientedCarrier (fromCoproduct d)) x =
      (leftAllocatedLabel d y).1 := by
  let E := boundaryReassembleEquiv
    (orientedCarrier (fromCoproduct d)).leftCells
    (orientedCarrier (fromCoproduct d)).rightCells
    (orientedCarrier (fromCoproduct d)).cover
    (orientedCarrier (fromCoproduct d)).disjoint
    ((orientedCarrier (fromCoproduct d)).core.1.1.restrict
      (orientedCarrier (fromCoproduct d)).leftCells)
    ((orientedCarrier (fromCoproduct d)).core.1.1.restrict
      (orientedCarrier (fromCoproduct d)).rightCells)
  let w : (orientedCarrier (fromCoproduct d)).core.1.1.Boundary :=
    boundaryEquivOfEq (orientedCarrier (fromCoproduct d)).reassemble_exact
      (E.symm (Sum.inl x))
  have hcut : (orientedCarrier (fromCoproduct d)).core.1.1 =
      (orientedMarked (fromCoproduct d)).pairing.erase
        (orientedMarked (fromCoproduct d)).seamSubtype := by
    rcases hfd : fromCoproduct d with ⟨⟨⟨P, e⟩, hb⟩, o⟩
    cases o <;> rfl
  let u : ((orientedMarked (fromCoproduct d)).pairing.erase
      (orientedMarked (fromCoproduct d)).seamSubtype).Boundary :=
    boundaryEquivOfEq hcut w
  let q : (reconstructedCutPairing d).Boundary :=
    boundaryEquivOfEq (erase_reconstructedJoinMarked d) u
  have hcoh : orientedCutLabel (fromCoproduct d) u =
      reconstructedCutLabel d q := by
    calc
      orientedCutLabel (fromCoproduct d) u =
          ((boundaryEquivOfEq
            (erase_reconstructedJoinMarked d)).symm.trans
              (orientedCutLabel (fromCoproduct d)))
            (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u) := by
              simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
              rfl
      _ = reconstructedCutLabel d
          (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u) :=
            congrArg (fun L ↦ L
              (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u))
              (orientedCutLabel_fromCoproduct d)
      _ = reconstructedCutLabel d q := rfl
  change orientedCutLabel (fromCoproduct d) u = (leftAllocatedLabel d y).1
  rw [hcoh, ← reconstructedCutLabel_includeLeft d y]
  apply congrArg (reconstructedCutLabel d)
  apply Subtype.ext
  simp only [q, u, w, E, boundaryEquivOfEq_val,
    boundaryReassembleEquiv_symm_inl, includeLeftBoundary_val]
  exact hxy

set_option maxHeartbeats 1000000 in
/-- Pointwise right-label counterpart of
`leftBoundaryLabelMap_fromCoproduct_of_include_eq`. -/
theorem rightBoundaryLabelMap_fromCoproduct_of_include_eq
    (d : Coproduct n h r m b)
    (x : ((orientedCarrier (fromCoproduct d)).core.1.1.restrict
      (orientedCarrier (fromCoproduct d)).rightCells).Boundary)
    (y : (rightRestrictedPairing d).pairing.Boundary)
    (hxy : includeDart
        (orientedCarrier (fromCoproduct d)).rightCells x.1 =
      includeDart (rightCellSet d) y.1) :
    rightBoundaryLabelMap (orientedCarrier (fromCoproduct d)) x =
      (rightAllocatedLabel d y).1 := by
  let E := boundaryReassembleEquiv
    (orientedCarrier (fromCoproduct d)).leftCells
    (orientedCarrier (fromCoproduct d)).rightCells
    (orientedCarrier (fromCoproduct d)).cover
    (orientedCarrier (fromCoproduct d)).disjoint
    ((orientedCarrier (fromCoproduct d)).core.1.1.restrict
      (orientedCarrier (fromCoproduct d)).leftCells)
    ((orientedCarrier (fromCoproduct d)).core.1.1.restrict
      (orientedCarrier (fromCoproduct d)).rightCells)
  let w : (orientedCarrier (fromCoproduct d)).core.1.1.Boundary :=
    boundaryEquivOfEq (orientedCarrier (fromCoproduct d)).reassemble_exact
      (E.symm (Sum.inr x))
  have hcut : (orientedCarrier (fromCoproduct d)).core.1.1 =
      (orientedMarked (fromCoproduct d)).pairing.erase
        (orientedMarked (fromCoproduct d)).seamSubtype := by
    rcases hfd : fromCoproduct d with ⟨⟨⟨P, e⟩, hb⟩, o⟩
    cases o <;> rfl
  let u : ((orientedMarked (fromCoproduct d)).pairing.erase
      (orientedMarked (fromCoproduct d)).seamSubtype).Boundary :=
    boundaryEquivOfEq hcut w
  let q : (reconstructedCutPairing d).Boundary :=
    boundaryEquivOfEq (erase_reconstructedJoinMarked d) u
  have hcoh : orientedCutLabel (fromCoproduct d) u =
      reconstructedCutLabel d q := by
    calc
      orientedCutLabel (fromCoproduct d) u =
          ((boundaryEquivOfEq
            (erase_reconstructedJoinMarked d)).symm.trans
              (orientedCutLabel (fromCoproduct d)))
            (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u) := by
              simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
              rfl
      _ = reconstructedCutLabel d
          (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u) :=
            congrArg (fun L ↦ L
              (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u))
              (orientedCutLabel_fromCoproduct d)
      _ = reconstructedCutLabel d q := rfl
  change orientedCutLabel (fromCoproduct d) u = (rightAllocatedLabel d y).1
  rw [hcoh, ← reconstructedCutLabel_includeRight d y]
  apply congrArg (reconstructedCutLabel d)
  apply Subtype.ext
  simp only [q, u, w, E, boundaryEquivOfEq_val,
    boundaryReassembleEquiv_symm_inr, includeRightBoundary_val]
  exact hxy

/-! ## Heterogeneous canonical matching normalization -/

/-- Package every dependency of component matching normalization.  Equality
of this package lets the kernel transport the `Fintype` instance, cardinal
proof, restricted dart type, and pairing simultaneously. -/
structure MatchingNormalizationInput (n h r : ℕ) where
  cells : Set (Fin n)
  fintype : Fintype cells
  size : ℕ
  card_eq : @Fintype.card cells fintype = size
  pairing : ColoredMatching
    (RestrictedDart (facets := fun _ : Fin n ↦ h) cells) r

theorem MatchingNormalizationInput.ext
    {x y : MatchingNormalizationInput n h r}
    (hcells : x.cells = y.cells)
    (hfintype : HEq x.fintype y.fintype)
    (hsize : x.size = y.size)
    (hpairing : HEq x.pairing y.pairing) : x = y := by
  cases x with
  | mk X fX k hk P =>
    cases y with
    | mk Y fY l hl Q =>
      dsimp only at hcells hfintype hsize hpairing
      subst Y
      have hf : fX = fY := eq_of_heq hfintype
      subst fY
      subst l
      have hPQ : P = Q := eq_of_heq hpairing
      subst Q
      rfl

/-- Canonically reindex a packaged restricted component matching. -/
def normalizeMatchingInput (x : MatchingNormalizationInput n h r) :
    Σ k : ℕ, ColoredMatching (Dart k h) r := by
  letI : Fintype x.cells := x.fintype
  exact ⟨x.size,
    componentColoredMatchingEquiv x.cells x.card_eq x.pairing⟩

set_option maxHeartbeats 1000000 in
/-- The underlying left numerical matching reconstructed and then cut is the
stored component matching, heterogeneously across its recovered cardinal. -/
theorem leftNumericalPairing_pairing_fromCoproduct
    (d : Coproduct n h r m b) :
    HEq (leftNumericalPairing
      (orientedCarrier (fromCoproduct d))).pairing
      d.2.2.2.1.1.raw.pairing := by
  let C := orientedCarrier (fromCoproduct d)
  let S := leftCellSet d
  let PC := C.core.1.1.restrict C.leftCells
  let PD := (leftRestrictedPairing d).pairing
  have hS : C.leftCells = S := orientedCarrier_from_leftCells d
  have hQ : C.core.1.1 = reconstructedCutPairing d :=
    orientedCarrier_from_core_pairing d
  have hP : HEq PC PD := by
    have h1 : PC = (reconstructedCutPairing d).restrict C.leftCells :=
      congrArg (fun Q : ColoredMatching (Dart n h) r ↦
        Q.restrict C.leftCells) hQ
    have h2 : HEq ((reconstructedCutPairing d).restrict C.leftCells)
        ((reconstructedCutPairing d).restrict S) :=
      congr_arg_heq (fun U : Set (Fin n) ↦
        (reconstructedCutPairing d).restrict U) hS
    exact (heq_of_eq h1).trans <|
      h2.trans (heq_of_eq (reconstructedCut_restrict_left d))
  have hk : (leftCellAllocation C).card = d.1.1.card :=
    congrArg Finset.card (leftCellAllocation_orientedCarrier_from d)
  let fC : Fintype C.leftCells :=
    NumericalBridgeCut.finiteSetFintype C.leftCells
  let fD : Fintype S := inferInstance
  have hf : HEq fC fD := by
    have hfun := congr_arg_heq
      (fun U : Set (Fin n) ↦ NumericalBridgeCut.finiteSetFintype U) hS
    exact hfun.trans (heq_of_eq (Subsingleton.elim _ _))
  have hkC : @Fintype.card C.leftCells fC =
      (leftCellAllocation C).card :=
    (Set.toFinset_card C.leftCells).symm
  have hkD : @Fintype.card S fD = d.1.1.card := leftCellSet_card d
  let xC : MatchingNormalizationInput n h r :=
    ⟨C.leftCells, fC, (leftCellAllocation C).card, hkC, PC⟩
  let xD : MatchingNormalizationInput n h r :=
    ⟨S, fD, d.1.1.card, hkD, PD⟩
  have hx : xC = xD :=
    MatchingNormalizationInput.ext hS hf hk hP
  have hn := congrArg normalizeMatchingInput hx
  have hleft : (normalizeMatchingInput xC).2 =
      (leftNumericalPairing C).pairing := rfl
  have hright : (normalizeMatchingInput xD).2 =
      d.2.2.2.1.1.raw.pairing := by
    have hraw := componentBoundaryLabelledEquiv_apply_symm_apply
      (r := r) (m := d.2.1.1.card) S (leftCellSet_card d)
      d.2.2.2.1.1.raw
    exact congrArg BoundaryLabelledPairing.pairing hraw
  have hsnd : HEq (normalizeMatchingInput xC).2
      (normalizeMatchingInput xD).2 := (Sigma.ext_iff.mp hn).2
  exact (heq_of_eq hleft.symm).trans <|
    hsnd.trans (heq_of_eq hright)

set_option maxHeartbeats 1000000 in
/-- Right-component counterpart of
`leftNumericalPairing_pairing_fromCoproduct`. -/
theorem rightNumericalPairing_pairing_fromCoproduct
    (d : Coproduct n h r m b) :
    HEq (rightNumericalPairing
      (orientedCarrier (fromCoproduct d))).pairing
      d.2.2.2.2.1.1.raw.pairing := by
  let C := orientedCarrier (fromCoproduct d)
  let S := rightCellSet d
  let PC := C.core.1.1.restrict C.rightCells
  let PD := (rightRestrictedPairing d).pairing
  have hS : C.rightCells = S := orientedCarrier_from_rightCells d
  have hQ : C.core.1.1 = reconstructedCutPairing d :=
    orientedCarrier_from_core_pairing d
  have hP : HEq PC PD := by
    have h1 : PC = (reconstructedCutPairing d).restrict C.rightCells :=
      congrArg (fun Q : ColoredMatching (Dart n h) r ↦
        Q.restrict C.rightCells) hQ
    have h2 : HEq ((reconstructedCutPairing d).restrict C.rightCells)
        ((reconstructedCutPairing d).restrict S) :=
      congr_arg_heq (fun U : Set (Fin n) ↦
        (reconstructedCutPairing d).restrict U) hS
    exact (heq_of_eq h1).trans <|
      h2.trans (heq_of_eq (reconstructedCut_restrict_right d))
  have hk : n - (leftCellAllocation C).card = n - d.1.1.card :=
    congrArg (fun k ↦ n - k)
      (congrArg Finset.card (leftCellAllocation_orientedCarrier_from d))
  let fC : Fintype C.rightCells :=
    NumericalBridgeCut.finiteSetFintype C.rightCells
  let fD : Fintype S := inferInstance
  have hf : HEq fC fD := by
    have hfun := congr_arg_heq
      (fun U : Set (Fin n) ↦ NumericalBridgeCut.finiteSetFintype U) hS
    exact hfun.trans (heq_of_eq (Subsingleton.elim _ _))
  have hkC : @Fintype.card C.rightCells fC =
      n - (leftCellAllocation C).card := rightCellCard_eq_sub C
  have hkD : @Fintype.card S fD = n - d.1.1.card := rightCellSet_card d
  let xC : MatchingNormalizationInput n h r :=
    ⟨C.rightCells, fC, n - (leftCellAllocation C).card, hkC, PC⟩
  let xD : MatchingNormalizationInput n h r :=
    ⟨S, fD, n - d.1.1.card, hkD, PD⟩
  have hx : xC = xD :=
    MatchingNormalizationInput.ext hS hf hk hP
  have hn := congrArg normalizeMatchingInput hx
  have hleft : (normalizeMatchingInput xC).2 =
      (rightNumericalPairing C).pairing := rfl
  have hright : (normalizeMatchingInput xD).2 =
      d.2.2.2.2.1.1.raw.pairing := by
    have hraw := componentBoundaryLabelledEquiv_apply_symm_apply
      (r := r) (m := m + 2 - d.2.1.1.card) S (rightCellSet_card d)
      d.2.2.2.2.1.1.raw
    exact congrArg BoundaryLabelledPairing.pairing hraw
  have hsnd : HEq (normalizeMatchingInput xC).2
      (normalizeMatchingInput xD).2 := (Sigma.ext_iff.mp hn).2
  exact (heq_of_eq hleft.symm).trans <|
    hsnd.trans (heq_of_eq hright)


end
end UnrootedBridgeCoproduct
end FacetPairing
end PolytopeCounting
