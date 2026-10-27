module

public import Proofs.RootedNumericalBridgeCoproductSourceLabels

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

open RootedGlobalBridgeCut PointedDecomposition NumericalBridgeCut

theorem forwardOtherBoundaryCard_eq
    (z : RootedBridgePointed n h₀ h r m b) :
    (forwardOtherBoundaryLabels z).card =
      m - (forwardBoundaryIndex z).1 + 1 := by
  have hsum := forwardBoundaryLabel_cards_add z
  have hbase := forwardBaseBoundaryCard_eq z
  omega

structure OtherInverseInput (n h₀ h r : ℕ) where
  cellSet : Set (RootedCell n)
  ordinarySet : Set (Fin n)
  ordinaryFintype : Fintype ordinarySet
  size : ℕ
  card_eq : @Fintype.card ordinarySet ordinaryFintype = size
  base_not_mem : baseCell n ∉ cellSet
  ordinary_iff : ∀ i : Fin n,
    (Sum.inr i : RootedCell n) ∈ cellSet ↔ i ∈ ordinarySet
  boundaryCount : ℕ
  normalized : BoundaryLabelledPairing (Dart size h) r boundaryCount

theorem OtherInverseInput.ext
    {x y : OtherInverseInput n h₀ h r}
    (hcell : x.cellSet = y.cellSet)
    (hordinary : x.ordinarySet = y.ordinarySet)
    (hfintype : HEq x.ordinaryFintype y.ordinaryFintype)
    (hsize : x.size = y.size)
    (hboundary : x.boundaryCount = y.boundaryCount)
    (hnormalized : HEq x.normalized y.normalized) : x = y := by
  cases x with
  | mk X O fO k hk hb hi q P =>
    cases y with
    | mk Y U fU l hl hb' hi' s Q =>
      dsimp only at hcell hordinary hfintype hsize hboundary hnormalized
      subst Y
      subst U
      have hf : fO = fU := eq_of_heq hfintype
      subst fU
      subst l
      subst s
      have hPQ : P = Q := eq_of_heq hnormalized
      subst Q
      rfl

def otherInverseCellEquiv (x : OtherInverseInput n h₀ h r) :
    x.cellSet ≃ Fin x.size := by
  letI : Fintype x.ordinarySet := x.ordinaryFintype
  let eO : x.ordinarySet ≃ Fin x.size :=
    (Fintype.equivFin _).trans (finCongr x.card_eq)
  refine
    { toFun := fun c ↦ match hc : c.1 with
        | Sum.inl u => False.elim (by
            cases u
            exact x.base_not_mem (by simpa only [hc, baseCell] using c.2))
        | Sum.inr i => eO ⟨i, (x.ordinary_iff i).mp (by
            simpa only [hc] using c.2)⟩
      invFun := fun i ↦ ⟨Sum.inr (eO.symm i).1,
        (x.ordinary_iff _).mpr (eO.symm i).2⟩
      left_inv := by
        rintro ⟨u | i, hc⟩
        · cases u
          exact False.elim (x.base_not_mem hc)
        · apply Subtype.ext
          simp
      right_inv := by intro i; simp }

def otherInverseFacetEquiv (x : OtherInverseInput n h₀ h r)
    (c : x.cellSet) : Fin (rootedFacets h₀ h c.1) ≃ Fin h := by
  rcases c with ⟨u | i, hc⟩
  · cases u
    exact False.elim (x.base_not_mem hc)
  · exact Equiv.refl _

def otherInverseDartEquiv (x : OtherInverseInput n h₀ h r) :
    RestrictedDart (facets := rootedFacets h₀ h) x.cellSet ≃
      Dart x.size h :=
  Equiv.sigmaCongr (otherInverseCellEquiv x) (otherInverseFacetEquiv x)

def otherInverseNormalize (x : OtherInverseInput n h₀ h r) :
    BoundaryLabelledPairing
      (RestrictedDart (facets := rootedFacets h₀ h) x.cellSet) r
      x.boundaryCount :=
  (BoundaryLabelledPairing.reindexEquiv
    (otherInverseDartEquiv x)).symm x.normalized

def carrierOtherLocalPairing
    (z : RootedBridgePointed n h₀ h r m b) :
    BoundaryLabelledPairing
      (RestrictedDart (facets := rootedFacets h₀ h)
        (baseOrientedCarrier z).otherCells) r
      (m - (forwardBoundaryIndex z).1 + 1) where
  pairing := (baseOrientedCarrier z).core.1.1.restrict
    (baseOrientedCarrier z).otherCells
  label := (forwardOtherBoundaryAllocationEquiv z).trans <|
    (finsetSubtypeEquivFin (forwardOtherBoundaryLabels z)).trans <|
      finCongr (forwardOtherBoundaryCard_eq z)

def literalOtherInverseInput
    (z : RootedBridgePointed n h₀ h r m b) :
    OtherInverseInput n h₀ h r := by
  let d := toCoproduct z
  let O : Set (Fin n) := {i | i ∉ forwardCellFinset z}
  let fO : Fintype O := inferInstance
  refine
    { cellSet := otherCellSet d
      ordinarySet := O
      ordinaryFintype := fO
      size := n - (forwardCellIndex z).1
      card_eq := ?_
      base_not_mem := by simp [baseCell, otherCellSet]
      ordinary_iff := fun _ ↦ Iff.rfl
      boundaryCount := m - (forwardBoundaryIndex z).1 + 1
      normalized := forwardOtherNumericalPairing z }
  change Fintype.card {i : Fin n // i ∉ forwardCellFinset z} =
    n - (forwardCellIndex z).1
  rw [card_complement]
  rw [Fintype.card_fin, forwardCellFinset_card]
  rfl

def carrierOtherInverseInput
    (z : RootedBridgePointed n h₀ h r m b) :
    OtherInverseInput n h₀ h r := by
  let C := baseOrientedCarrier z
  let fO : Fintype (otherOrdinaryCells C) := Fintype.ofFinite _
  refine
    { cellSet := C.otherCells
      ordinarySet := otherOrdinaryCells C
      ordinaryFintype := fO
      size := n - (forwardCellIndex z).1
      card_eq := ?_
      base_not_mem := C.base_not_mem_other
      ordinary_iff := fun _ ↦ Iff.rfl
      boundaryCount := m - (forwardBoundaryIndex z).1 + 1
      normalized := forwardOtherNumericalPairing z }
  rw [← Nat.card_eq_fintype_card, card_otherOrdinaryCells]
  have hadd := C.ordinaryCounts_add
  change C.otherOrdinaryCount = n - C.baseOrdinaryCount
  omega

set_option maxHeartbeats 1000000 in
theorem literalOtherInverseInput_eq_carrier
    (z : RootedBridgePointed n h₀ h r m b) :
    literalOtherInverseInput z = carrierOtherInverseInput z := by
  let C := baseOrientedCarrier z
  let O : Set (Fin n) := {i | i ∉ forwardCellFinset z}
  have hcell : otherCellSet (toCoproduct z) = C.otherCells :=
    otherCellSet_toCoproduct z
  have hordinary : O = otherOrdinaryCells C := by
    ext i
    change (Sum.inr i : RootedCell n) ∈ otherCellSet (toCoproduct z) ↔
      (Sum.inr i : RootedCell n) ∈ C.otherCells
    exact Set.ext_iff.mp hcell _
  let fD : Fintype O := inferInstance
  let fC : Fintype (otherOrdinaryCells C) := Fintype.ofFinite _
  have hf : HEq fD fC := by
    have hfun := congr_arg_heq
      (fun U : Set (Fin n) ↦ Fintype.ofFinite U) hordinary
    exact (heq_of_eq (Subsingleton.elim _ _)).trans hfun
  apply OtherInverseInput.ext
  · simpa only [literalOtherInverseInput, carrierOtherInverseInput] using hcell
  · simpa only [literalOtherInverseInput, carrierOtherInverseInput] using hordinary
  · simpa only [literalOtherInverseInput, carrierOtherInverseInput] using hf
  · simp only [literalOtherInverseInput, carrierOtherInverseInput]
  · simp only [literalOtherInverseInput, carrierOtherInverseInput]
  · simp only [literalOtherInverseInput, carrierOtherInverseInput]
    rfl

theorem otherInverseDartEquiv_literal
    (z : RootedBridgePointed n h₀ h r m b) :
    otherInverseDartEquiv (literalOtherInverseInput z) =
      otherDartEquiv (toCoproduct z) := by
  simp only [literalOtherInverseInput]
  apply Equiv.ext
  rintro ⟨⟨u | i, hc⟩, j⟩
  · cases u
    exact False.elim hc
  · apply Sigma.ext <;> rfl

theorem otherInverseDartEquiv_carrier
    (z : RootedBridgePointed n h₀ h r m b) :
    otherInverseDartEquiv (carrierOtherInverseInput z) =
      forwardOtherDartEquiv z := by
  simp only [carrierOtherInverseInput]
  apply Equiv.ext
  rintro ⟨⟨u | i, hc⟩, j⟩
  · cases u
    exact False.elim ((baseOrientedCarrier z).base_not_mem_other hc)
  · apply Sigma.ext <;> rfl

theorem otherInverseNormalize_literal
    (z : RootedBridgePointed n h₀ h r m b) :
    otherInverseNormalize (literalOtherInverseInput z) =
      otherRestrictedPairing (toCoproduct z) := by
  simp only [literalOtherInverseInput, otherInverseNormalize]
  change (BoundaryLabelledPairing.reindexEquiv
      (otherInverseDartEquiv (literalOtherInverseInput z))).symm
        (forwardOtherNumericalPairing z) = _
  rw [otherInverseDartEquiv_literal]
  rfl

theorem otherInverseNormalize_carrier
    (z : RootedBridgePointed n h₀ h r m b) :
    otherInverseNormalize (carrierOtherInverseInput z) =
      carrierOtherLocalPairing z := by
  simp only [carrierOtherInverseInput, otherInverseNormalize]
  change (BoundaryLabelledPairing.reindexEquiv
      (otherInverseDartEquiv (carrierOtherInverseInput z))).symm
        (forwardOtherNumericalPairing z) = _
  rw [otherInverseDartEquiv_carrier]
  change (BoundaryLabelledPairing.reindexEquiv (forwardOtherDartEquiv z)).symm
      (BoundaryLabelledPairing.reindexEquiv (forwardOtherDartEquiv z)
        (carrierOtherLocalPairing z)) = _
  exact BoundaryLabelledPairing.reindexEquiv_symm_apply_apply
    (forwardOtherDartEquiv z) (carrierOtherLocalPairing z)

set_option maxHeartbeats 1000000 in
theorem otherRestrictedPairing_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    HEq (otherRestrictedPairing (toCoproduct z))
      (carrierOtherLocalPairing z) := by
  have hx := congr_arg_heq otherInverseNormalize
    (literalOtherInverseInput_eq_carrier z)
  exact (heq_of_eq (otherInverseNormalize_literal z).symm).trans <|
    hx.trans (heq_of_eq (otherInverseNormalize_carrier z))


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

