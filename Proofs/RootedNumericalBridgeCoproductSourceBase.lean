module

public import Proofs.RootedNumericalBridgeCoproductLabelledComponents
public import Proofs.OrientedCutJoinCoherence

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Source-side cancellation for the rooted numerical bridge coproduct

This is the converse normalization direction.  It packages the finite
component geometry together with the already normalized labelled pairing,
so inverse reindexing is stable under equality of the ambient allocation.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

open RootedGlobalBridgeCut PointedDecomposition NumericalBridgeCut LabelledCutJoin

structure RootedInverseInput (n h₀ h r : ℕ) where
  cellSet : Set (RootedCell n)
  ordinarySet : Set (Fin n)
  ordinaryFintype : Fintype ordinarySet
  size : ℕ
  card_eq : @Fintype.card ordinarySet ordinaryFintype = size
  base_mem : baseCell n ∈ cellSet
  ordinary_iff : ∀ i : Fin n,
    (Sum.inr i : RootedCell n) ∈ cellSet ↔ i ∈ ordinarySet
  boundaryCount : ℕ
  normalized : BoundaryLabelledPairing (RootedDart size h₀ h) r boundaryCount

theorem RootedInverseInput.ext
    {x y : RootedInverseInput n h₀ h r}
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

def rootedInverseCellEquiv (x : RootedInverseInput n h₀ h r) :
    x.cellSet ≃ RootedCell x.size := by
  letI : Fintype x.ordinarySet := x.ordinaryFintype
  let eO : x.ordinarySet ≃ Fin x.size :=
    (Fintype.equivFin _).trans (finCongr x.card_eq)
  refine
    { toFun := fun c ↦ match hc : c.1 with
        | Sum.inl u => Sum.inl u
        | Sum.inr i => Sum.inr (eO ⟨i, (x.ordinary_iff i).mp (by
            simpa only [hc] using c.2)⟩)
      invFun := fun c ↦ match c with
        | Sum.inl u => ⟨Sum.inl u, by cases u; exact x.base_mem⟩
        | Sum.inr i => ⟨Sum.inr (eO.symm i).1,
            (x.ordinary_iff _).mpr (eO.symm i).2⟩
      left_inv := by
        rintro ⟨u | i, hc⟩
        · cases u; rfl
        · apply Subtype.ext
          simp
      right_inv := by
        intro c
        rcases c with u | i
        · cases u; rfl
        · simp }

def rootedInverseFacetEquiv (x : RootedInverseInput n h₀ h r)
    (c : x.cellSet) :
    Fin (rootedFacets h₀ h c.1) ≃
      Fin (rootedFacets h₀ h (rootedInverseCellEquiv x c)) :=
  finCongr (by rcases c with ⟨u | i, hc⟩ <;> rfl)

def rootedInverseDartEquiv (x : RootedInverseInput n h₀ h r) :
    RestrictedDart (facets := rootedFacets h₀ h) x.cellSet ≃
      RootedDart x.size h₀ h :=
  Equiv.sigmaCongr (rootedInverseCellEquiv x) (rootedInverseFacetEquiv x)

def rootedInverseNormalize (x : RootedInverseInput n h₀ h r) :
    BoundaryLabelledPairing
      (RestrictedDart (facets := rootedFacets h₀ h) x.cellSet) r
      x.boundaryCount :=
  (BoundaryLabelledPairing.reindexEquiv
    (rootedInverseDartEquiv x)).symm x.normalized

def carrierBaseLocalPairing
    (z : RootedBridgePointed n h₀ h r m b) :
    BoundaryLabelledPairing
      (RestrictedDart (facets := rootedFacets h₀ h)
        (baseOrientedCarrier z).baseCells) r
      ((forwardBoundaryIndex z).1 + 1) where
  pairing := (baseOrientedCarrier z).core.1.1.restrict
    (baseOrientedCarrier z).baseCells
  label := (forwardBaseBoundaryAllocationEquiv z).trans <|
    (finsetSubtypeEquivFin (forwardBaseBoundaryLabels z)).trans <|
      finCongr (forwardBaseBoundaryCard_eq z)

theorem baseCellSet_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    baseCellSet (toCoproduct z) = (baseOrientedCarrier z).baseCells := by
  classical
  ext c
  rcases c with u | i
  · cases u
    simp only [baseCellSet, Set.mem_setOf_eq, true_iff]
    exact (baseOrientedCarrier z).base_mem
  · simp [baseCellSet, toCoproduct, forwardCellAllocation,
      forwardCellFinset, baseOrdinaryCells]

theorem otherCellSet_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    otherCellSet (toCoproduct z) = (baseOrientedCarrier z).otherCells := by
  classical
  let C := baseOrientedCarrier z
  ext c
  rcases c with u | i
  · cases u
    simp only [otherCellSet, Set.mem_setOf_eq, false_iff]
    exact C.base_not_mem_other
  · have hbase : (Sum.inr i : RootedCell n) ∈ baseCellSet (toCoproduct z) ↔
        (Sum.inr i : RootedCell n) ∈ C.baseCells :=
      Set.ext_iff.mp (baseCellSet_toCoproduct z) _
    constructor
    · intro hi
      have hnbase : (Sum.inr i : RootedCell n) ∉ C.baseCells := by
        intro hb
        exact hi (hbase.mpr hb)
      have hcover : (Sum.inr i : RootedCell n) ∈ C.baseCells ∨
          (Sum.inr i : RootedCell n) ∈ C.otherCells := by
        have hc : (Sum.inr i : RootedCell n) ∈ C.baseCells ∪ C.otherCells := by
          rw [C.cover]
          exact Set.mem_univ _
        simpa only [Set.mem_union] using hc
      exact hcover.resolve_left hnbase
    · intro hi hb
      exact Set.disjoint_left.mp C.disjoint (hbase.mp hb) hi

def literalRootedInverseInput
    (z : RootedBridgePointed n h₀ h r m b) :
    RootedInverseInput n h₀ h r := by
  let d := toCoproduct z
  let O : Set (Fin n) := {i | i ∈ forwardCellFinset z}
  let fO : Fintype O := inferInstance
  refine
    { cellSet := baseCellSet d
      ordinarySet := O
      ordinaryFintype := fO
      size := (forwardCellIndex z).1
      card_eq := ?_
      base_mem := by simp [baseCell, baseCellSet]
      ordinary_iff := fun _ ↦ Iff.rfl
      boundaryCount := (forwardBoundaryIndex z).1 + 1
      normalized := forwardBaseNumericalPairing z }
  change Fintype.card {i : Fin n // i ∈ forwardCellFinset z} =
    (forwardCellIndex z).1
  rw [Fintype.card_coe]
  exact forwardCellFinset_card z

def carrierRootedInverseInput
    (z : RootedBridgePointed n h₀ h r m b) :
    RootedInverseInput n h₀ h r := by
  let C := baseOrientedCarrier z
  let fO : Fintype (baseOrdinaryCells C) := Fintype.ofFinite _
  refine
    { cellSet := C.baseCells
      ordinarySet := baseOrdinaryCells C
      ordinaryFintype := fO
      size := (forwardCellIndex z).1
      card_eq := ?_
      base_mem := C.base_mem
      ordinary_iff := fun _ ↦ Iff.rfl
      boundaryCount := (forwardBoundaryIndex z).1 + 1
      normalized := forwardBaseNumericalPairing z }
  rw [← Nat.card_eq_fintype_card]
  exact card_baseOrdinaryCells C

set_option maxHeartbeats 1000000 in
theorem literalRootedInverseInput_eq_carrier
    (z : RootedBridgePointed n h₀ h r m b) :
    literalRootedInverseInput z = carrierRootedInverseInput z := by
  let C := baseOrientedCarrier z
  let O : Set (Fin n) := {i | i ∈ forwardCellFinset z}
  have hcell : baseCellSet (toCoproduct z) = C.baseCells :=
    baseCellSet_toCoproduct z
  have hordinary : O = baseOrdinaryCells C := by
    ext i
    change i ∈ forwardCellFinset z ↔
      (Sum.inr i : RootedCell n) ∈ C.baseCells
    simp [forwardCellFinset, C, baseOrdinaryCells]
  let fD : Fintype O := inferInstance
  let fC : Fintype (baseOrdinaryCells C) := Fintype.ofFinite _
  have hf : HEq fD fC := by
    have hfun := congr_arg_heq
      (fun U : Set (Fin n) ↦ Fintype.ofFinite U) hordinary
    exact (heq_of_eq (Subsingleton.elim _ _)).trans hfun
  apply RootedInverseInput.ext
  · simpa only [literalRootedInverseInput, carrierRootedInverseInput] using hcell
  · simpa only [literalRootedInverseInput, carrierRootedInverseInput] using hordinary
  · simpa only [literalRootedInverseInput, carrierRootedInverseInput] using hf
  · rfl
  · rfl
  · rfl

theorem rootedInverseDartEquiv_literal
    (z : RootedBridgePointed n h₀ h r m b) :
    rootedInverseDartEquiv (literalRootedInverseInput z) =
      baseDartEquiv (toCoproduct z) := by
  simp only [literalRootedInverseInput]
  apply Equiv.ext
  rintro ⟨⟨u | i, hc⟩, j⟩
  · cases u
    rfl
  · apply Sigma.ext <;> rfl

theorem rootedInverseDartEquiv_carrier
    (z : RootedBridgePointed n h₀ h r m b) :
    rootedInverseDartEquiv (carrierRootedInverseInput z) =
      forwardBaseDartEquiv z := by
  simp only [carrierRootedInverseInput]
  apply Equiv.ext
  rintro ⟨⟨u | i, hc⟩, j⟩
  · cases u
    rfl
  · apply Sigma.ext <;> rfl

theorem rootedInverseNormalize_literal
    (z : RootedBridgePointed n h₀ h r m b) :
    rootedInverseNormalize (literalRootedInverseInput z) =
      baseRestrictedPairing (toCoproduct z) := by
  simp only [literalRootedInverseInput, rootedInverseNormalize]
  change (BoundaryLabelledPairing.reindexEquiv
      (rootedInverseDartEquiv (literalRootedInverseInput z))).symm
        (forwardBaseNumericalPairing z) = _
  rw [rootedInverseDartEquiv_literal]
  rfl

theorem rootedInverseNormalize_carrier
    (z : RootedBridgePointed n h₀ h r m b) :
    rootedInverseNormalize (carrierRootedInverseInput z) =
      carrierBaseLocalPairing z := by
  simp only [carrierRootedInverseInput, rootedInverseNormalize]
  change (BoundaryLabelledPairing.reindexEquiv
      (rootedInverseDartEquiv (carrierRootedInverseInput z))).symm
        (forwardBaseNumericalPairing z) = _
  rw [rootedInverseDartEquiv_carrier]
  change (BoundaryLabelledPairing.reindexEquiv (forwardBaseDartEquiv z)).symm
      (BoundaryLabelledPairing.reindexEquiv (forwardBaseDartEquiv z)
        (carrierBaseLocalPairing z)) = _
  exact BoundaryLabelledPairing.reindexEquiv_symm_apply_apply
    (forwardBaseDartEquiv z) (carrierBaseLocalPairing z)

set_option maxHeartbeats 1000000 in
theorem baseRestrictedPairing_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    HEq (baseRestrictedPairing (toCoproduct z))
      (carrierBaseLocalPairing z) := by
  have hx := congr_arg_heq rootedInverseNormalize
    (literalRootedInverseInput_eq_carrier z)
  exact (heq_of_eq (rootedInverseNormalize_literal z).symm).trans <|
    hx.trans (heq_of_eq (rootedInverseNormalize_carrier z))


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

