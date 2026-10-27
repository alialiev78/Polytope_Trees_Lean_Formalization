module

public import Proofs.RootedNumericalBridgeCoproductSourceReassembly

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Exact source-side raw normalization for the rooted bridge coproduct

All dependent local pairings and their ambient boundary allocations are
packaged before reassembly.  This lets equality transport both component
subtypes and both boundary equivalences simultaneously.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

open RootedGlobalBridgeCut PointedDecomposition NumericalBridgeCut
open LabelledCutJoin

structure AllocatedRawInput (n h₀ h r m : ℕ) where
  baseCells : Set (RootedCell n)
  otherCells : Set (RootedCell n)
  cover : baseCells ∪ otherCells = Set.univ
  disjoint : Disjoint baseCells otherCells
  allocation : Finset (Fin (m + 2))
  basePairing : ColoredMatching
    (RestrictedDart (facets := rootedFacets h₀ h) baseCells) r
  otherPairing : ColoredMatching
    (RestrictedDart (facets := rootedFacets h₀ h) otherCells) r
  baseLabel : basePairing.Boundary ≃
    {i : Fin (m + 2) // i ∈ allocation}
  otherLabel : otherPairing.Boundary ≃
    {i : Fin (m + 2) // i ∉ allocation}

theorem AllocatedRawInput.ext
    {x y : AllocatedRawInput n h₀ h r m}
    (hbase : x.baseCells = y.baseCells)
    (hother : x.otherCells = y.otherCells)
    (halloc : x.allocation = y.allocation)
    (hbasePair : HEq x.basePairing y.basePairing)
    (hotherPair : HEq x.otherPairing y.otherPairing)
    (hbaseLabel : HEq x.baseLabel y.baseLabel)
    (hotherLabel : HEq x.otherLabel y.otherLabel) : x = y := by
  cases x with
  | mk S T hcover hdisj A P Q L K =>
    cases y with
    | mk S' T' hcover' hdisj' A' P' Q' L' K' =>
      dsimp only at hbase hother halloc hbasePair hotherPair hbaseLabel hotherLabel
      subst S'
      subst T'
      subst A'
      have hP : P = P' := eq_of_heq hbasePair
      subst P'
      have hQ : Q = Q' := eq_of_heq hotherPair
      subst Q'
      have hL : L = L' := eq_of_heq hbaseLabel
      subst L'
      have hK : K = K' := eq_of_heq hotherLabel
      subst K'
      rfl

def reassembleAllocatedRaw (x : AllocatedRawInput n h₀ h r m) :
    BoundaryLabelledPairing (RootedDart n h₀ h) r (m + 2) where
  pairing := reassembleColored x.baseCells x.otherCells x.disjoint
    x.basePairing x.otherPairing
  label := (boundaryReassembleEquiv x.baseCells x.otherCells x.cover
    x.disjoint x.basePairing x.otherPairing).trans <|
      (Equiv.sumCongr x.baseLabel x.otherLabel).trans
        (finsetSumComplementEquiv x.allocation)

def coproductRawInput (d : Coproduct n h₀ h r m b) :
    AllocatedRawInput n h₀ h r m :=
  { baseCells := baseCellSet d
    otherCells := otherCellSet d
    cover := cellSets_cover d
    disjoint := cellSets_disjoint d
    allocation := (labels d).1
    basePairing := (baseRestrictedPairing d).pairing
    otherPairing := (otherRestrictedPairing d).pairing
    baseLabel := baseAllocatedLabel d
    otherLabel := otherAllocatedLabel d }

@[simp] theorem reassembleAllocatedRaw_coproductRawInput
    (d : Coproduct n h₀ h r m b) :
    reassembleAllocatedRaw (coproductRawInput d) = reconstructedCutRaw d := by
  rfl

def carrierOtherAllocatedLabel
    (z : RootedBridgePointed n h₀ h r m b) :
    ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).otherCells).Boundary ≃
      {i : Fin (m + 2) // i ∉ forwardBaseBoundaryLabels z} :=
  (carrierOtherLocalPairing z).label.trans <|
    (finCongr (by
      have hs : (forwardBoundaryIndex z).1 ≤ m := by omega
      rw [Fintype.card_fin, forwardBaseBoundaryCard_eq]
      omega)).trans (complementEquivFin (forwardBaseBoundaryLabels z)).symm

def otherDenormalizedLabel
    (z : RootedBridgePointed n h₀ h r m b)
    (x : LocalPairingPackage n h₀ h r
      (m - (forwardBoundaryIndex z).1 + 1)) :
    x.2.pairing.Boundary ≃
      {i : Fin (m + 2) // i ∉ forwardBaseBoundaryLabels z} :=
  x.2.label.trans <|
    (finCongr (by
      have hs : (forwardBoundaryIndex z).1 ≤ m := by omega
      rw [Fintype.card_fin, forwardBaseBoundaryCard_eq]
      omega)).trans (complementEquivFin (forwardBaseBoundaryLabels z)).symm

theorem otherAllocatedLabel_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    HEq (otherAllocatedLabel (toCoproduct z))
      (carrierOtherAllocatedLabel z) := by
  let xD : LocalPairingPackage n h₀ h r
      (m - (forwardBoundaryIndex z).1 + 1) :=
    ⟨otherCellSet (toCoproduct z),
      otherRestrictedPairing (toCoproduct z)⟩
  let xC : LocalPairingPackage n h₀ h r
      (m - (forwardBoundaryIndex z).1 + 1) :=
    ⟨(baseOrientedCarrier z).otherCells, carrierOtherLocalPairing z⟩
  have hx : xD = xC := otherLocalPackage_toCoproduct z
  have hd : HEq (otherDenormalizedLabel z xD)
      (otherDenormalizedLabel z xC) :=
    congr_arg_heq (otherDenormalizedLabel z) hx
  have hD : otherDenormalizedLabel z xD =
      otherAllocatedLabel (toCoproduct z) := by
    rfl
  have hC : otherDenormalizedLabel z xC =
      carrierOtherAllocatedLabel z := by
    rfl
  exact (heq_of_eq hD.symm).trans <| hd.trans (heq_of_eq hC)

def carrierRawInput
    (z : RootedBridgePointed n h₀ h r m b) :
    AllocatedRawInput n h₀ h r m :=
  { baseCells := (baseOrientedCarrier z).baseCells
    otherCells := (baseOrientedCarrier z).otherCells
    cover := (baseOrientedCarrier z).cover
    disjoint := (baseOrientedCarrier z).disjoint
    allocation := forwardBaseBoundaryLabels z
    basePairing := (baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).baseCells
    otherPairing := (baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).otherCells
    baseLabel := forwardBaseBoundaryAllocationEquiv z
    otherLabel := carrierOtherAllocatedLabel z }

theorem coproductRawInput_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    coproductRawInput (toCoproduct z) = carrierRawInput z := by
  apply AllocatedRawInput.ext
  · exact baseCellSet_toCoproduct z
  · exact otherCellSet_toCoproduct z
  · rfl
  · exact baseRestrictedPairing_pairing_toCoproduct z
  · exact otherRestrictedPairing_pairing_toCoproduct z
  · exact baseAllocatedLabel_toCoproduct z
  · exact otherAllocatedLabel_toCoproduct z

theorem reconstructedCutRaw_toCoproduct_eq_carrierReassembly
    (z : RootedBridgePointed n h₀ h r m b) :
    reconstructedCutRaw (toCoproduct z) =
      reassembleAllocatedRaw (carrierRawInput z) := by
  rw [← reassembleAllocatedRaw_coproductRawInput,
    coproductRawInput_toCoproduct]

theorem forwardOtherBoundaryLabels_eq_compl
    (z : RootedBridgePointed n h₀ h r m b) :
    forwardOtherBoundaryLabels z = (forwardBaseBoundaryLabels z)ᶜ := by
  ext i
  constructor
  · intro hiO
    have hiB : i ∉ forwardBaseBoundaryLabels z := fun hiB ↦
      Finset.disjoint_left.mp (forwardBoundaryLabels_disjoint z) hiB hiO
    simpa using hiB
  · intro hiComp
    have hiB : i ∉ forwardBaseBoundaryLabels z := by simpa using hiComp
    have hiUnion : i ∈ forwardBaseBoundaryLabels z ∨
        i ∈ forwardOtherBoundaryLabels z := by
      have hi : i ∈ forwardBaseBoundaryLabels z ∪
          forwardOtherBoundaryLabels z := by
        rw [forwardBoundaryLabels_cover]
        exact Finset.mem_univ i
      simpa only [Finset.mem_union] using hi
    exact hiUnion.resolve_left hiB

def carrierOtherPredicateEq
    (z : RootedBridgePointed n h₀ h r m b) :
    (fun i : Fin (m + 2) ↦ i ∈ forwardOtherBoundaryLabels z) =
      (fun i : Fin (m + 2) ↦ i ∉ forwardBaseBoundaryLabels z) := by
  funext i
  apply propext
  rw [forwardOtherBoundaryLabels_eq_compl]
  simp

def carrierOtherSubtypeTypeEq
    (z : RootedBridgePointed n h₀ h r m b) :
    {i : Fin (m + 2) // i ∈ forwardOtherBoundaryLabels z} =
      {i : Fin (m + 2) // i ∉ forwardBaseBoundaryLabels z} :=
  congrArg Subtype (carrierOtherPredicateEq z)

theorem equivCast_congrArg_Subtype_val_rooted
    {X : Type*} {p q : X → Prop} (hpq : p = q) (x : Subtype p) :
    ((Equiv.cast (congrArg Subtype hpq)) x : Subtype q).1 = x.1 := by
  cases hpq
  rfl

universe u

theorem equivFin_cast_val_rooted {X Y : Type u}
    [fX : Fintype X] [fY : Fintype Y]
    (hXY : X = Y) (x : X) :
    (Fintype.equivFin Y (Equiv.cast hXY x)).val =
      (Fintype.equivFin X x).val := by
  subst Y
  have hf : fX = fY := Subsingleton.elim _ _
  subst fY
  rfl

set_option maxHeartbeats 1000000 in
theorem carrierOtherAllocatedLabel_val
    (z : RootedBridgePointed n h₀ h r m b)
    (x : ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).otherCells).Boundary) :
    (carrierOtherAllocatedLabel z x).1 = forwardOtherBoundaryMap z x := by
  let X := {i : Fin (m + 2) // i ∈ forwardOtherBoundaryLabels z}
  let Y := {i : Fin (m + 2) // i ∉ forwardBaseBoundaryLabels z}
  let hXY : X = Y := carrierOtherSubtypeTypeEq z
  let u : X := forwardOtherBoundaryAllocationEquiv z x
  have hcast : ((Equiv.cast hXY) u : Y).1 = u.1 := by
    exact equivCast_congrArg_Subtype_val_rooted
      (carrierOtherPredicateEq z) u
  have hcanon := equivFin_cast_val_rooted hXY u
  have heq : carrierOtherAllocatedLabel z x = Equiv.cast hXY u := by
    apply (Fintype.equivFin Y).injective
    apply Fin.ext
    simpa [carrierOtherAllocatedLabel, carrierOtherLocalPairing,
      complementEquivFin, finsetSubtypeEquivFin, X, Y, u] using hcanon.symm
  calc
    (carrierOtherAllocatedLabel z x).1 = ((Equiv.cast hXY) u : Y).1 :=
      congrArg Subtype.val heq
    _ = u.1 := hcast
    _ = forwardOtherBoundaryMap z x := rfl

def carrierReassembledRaw
    (z : RootedBridgePointed n h₀ h r m b) :
    BoundaryLabelledPairing (RootedDart n h₀ h) r (m + 2) where
  pairing := reassembleColored
    (baseOrientedCarrier z).baseCells
    (baseOrientedCarrier z).otherCells
    (baseOrientedCarrier z).disjoint
    ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).baseCells)
    ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).otherCells)
  label := (boundaryReassembleEquiv
    (baseOrientedCarrier z).baseCells
    (baseOrientedCarrier z).otherCells
    (baseOrientedCarrier z).cover
    (baseOrientedCarrier z).disjoint
    ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).baseCells)
    ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).otherCells)).trans
      (baseOrientedCarrier z).componentBoundaryLabel

theorem reassembleAllocatedRaw_carrierRawInput
    (z : RootedBridgePointed n h₀ h r m b) :
    reassembleAllocatedRaw (carrierRawInput z) = carrierReassembledRaw z := by
  let C := baseOrientedCarrier z
  let P := reassembleColored C.baseCells C.otherCells C.disjoint
    (C.core.1.1.restrict C.baseCells)
    (C.core.1.1.restrict C.otherCells)
  let E := boundaryReassembleEquiv C.baseCells C.otherCells C.cover
    C.disjoint (C.core.1.1.restrict C.baseCells)
    (C.core.1.1.restrict C.otherCells)
  let L := (Equiv.sumCongr (forwardBaseBoundaryAllocationEquiv z)
    (carrierOtherAllocatedLabel z)).trans
      (finsetSumComplementEquiv (forwardBaseBoundaryLabels z))
  have hlabel : E.trans L = E.trans C.componentBoundaryLabel := by
    apply Equiv.ext
    intro x
    simp only [Equiv.trans_apply]
    cases hs : E x with
    | inl y =>
        change
          (finsetSumComplementEquiv (forwardBaseBoundaryLabels z)
            (Sum.inl (forwardBaseBoundaryAllocationEquiv z y))) =
          C.componentBoundaryLabel (Sum.inl y)
        rfl
    | inr y =>
        apply Fin.eq_of_val_eq
        change (carrierOtherAllocatedLabel z y).1.val =
          (C.componentBoundaryLabel (Sum.inr y)).val
        exact congrArg Fin.val (carrierOtherAllocatedLabel_val z y)
  change (⟨P, E.trans L⟩ :
      BoundaryLabelledPairing (RootedDart n h₀ h) r (m + 2)) =
    ⟨P, E.trans C.componentBoundaryLabel⟩
  rw [hlabel]

def carrierCoreRaw
    (z : RootedBridgePointed n h₀ h r m b) :
    BoundaryLabelledPairing (RootedDart n h₀ h) r (m + 2) where
  pairing := (baseOrientedCarrier z).core.1.1
  label := carrierGlobalLabel (baseOrientedCarrier z)

theorem label_heq_transport_symm
    {P Q : ColoredMatching (RootedDart n h₀ h) r} (hPQ : P = Q)
    (L : P.Boundary ≃ Fin (m + 2)) :
    HEq L ((boundaryEquivOfEq hPQ).symm.trans L) := by
  cases hPQ
  rfl

theorem label_heq_transport
    {P Q : ColoredMatching (RootedDart n h₀ h) r} (hPQ : P = Q)
    (L : Q.Boundary ≃ Fin (m + 2)) :
    HEq ((boundaryEquivOfEq hPQ).trans L) L := by
  cases hPQ
  rfl

theorem carrierReassembledRaw_eq_carrierCoreRaw
    (z : RootedBridgePointed n h₀ h r m b) :
    carrierReassembledRaw z = carrierCoreRaw z := by
  let C := baseOrientedCarrier z
  apply BoundaryLabelledPairing.toData_injective
  apply Sigma.ext C.reassemble_exact
  exact label_heq_transport_symm C.reassemble_exact
    (carrierReassembledRaw z).label

theorem carrierGlobalLabel_baseOrientedCarrier
    (z : RootedBridgePointed n h₀ h r m b) :
    let C := baseOrientedCarrier z
    let hcut : C.core.1.1 =
        (baseOrientedMarked z).pairing.erase
          (baseOrientedMarked z).seamSubtype := cutBridge_core_pairing z
    carrierGlobalLabel C =
      (boundaryEquivOfEq hcut).trans (baseOrientedCutLabel z) := by
  dsimp only
  let C := cutBridge z
  let hcut : C.core.1.1 =
      (baseOrientedMarked z).pairing.erase
        (baseOrientedMarked z).seamSubtype := cutBridge_core_pairing z
  change carrierGlobalLabel { C with
      componentBoundaryLabel :=
        (boundaryReassembleEquiv C.baseCells C.otherCells C.cover C.disjoint
          (C.core.1.1.restrict C.baseCells)
          (C.core.1.1.restrict C.otherCells)).symm |>.trans <|
            (boundaryEquivOfEq C.reassemble_exact).trans <|
              (boundaryEquivOfEq hcut).trans (baseOrientedCutLabel z) } = _
  exact carrierGlobalLabel_of_component C
    ((boundaryEquivOfEq hcut).trans (baseOrientedCutLabel z))

theorem carrierCoreRaw_baseOrientedCarrier
    (z : RootedBridgePointed n h₀ h r m b) :
    carrierCoreRaw z = OrientedCutJoinCoherence.orientedCutRaw
      z.1.1.1.raw (baseOrientedSeam z) := by
  let C := baseOrientedCarrier z
  have hcut : C.core.1.1 =
      (baseOrientedMarked z).pairing.erase
        (baseOrientedMarked z).seamSubtype := cutBridge_core_pairing z
  have hlabel : carrierGlobalLabel C =
      (boundaryEquivOfEq hcut).trans (baseOrientedCutLabel z) :=
    carrierGlobalLabel_baseOrientedCarrier z
  apply BoundaryLabelledPairing.toData_injective
  apply Sigma.ext hcut
  exact (heq_of_eq hlabel).trans
    (label_heq_transport hcut (baseOrientedCutLabel z))

set_option maxHeartbeats 3000000 in
theorem reconstructedCutRaw_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    reconstructedCutRaw (toCoproduct z) =
      OrientedCutJoinCoherence.orientedCutRaw
        z.1.1.1.raw (baseOrientedSeam z) := by
  calc
    reconstructedCutRaw (toCoproduct z) =
        reassembleAllocatedRaw (carrierRawInput z) :=
      reconstructedCutRaw_toCoproduct_eq_carrierReassembly z
    _ = carrierReassembledRaw z :=
      reassembleAllocatedRaw_carrierRawInput z
    _ = carrierCoreRaw z :=
      carrierReassembledRaw_eq_carrierCoreRaw z
    _ = OrientedCutJoinCoherence.orientedCutRaw
        z.1.1.1.raw (baseOrientedSeam z) :=
      carrierCoreRaw_baseOrientedCarrier z


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

