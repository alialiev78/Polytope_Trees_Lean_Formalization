module

public import Proofs.RootedNumericalBridgeCoproductLabels

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

open RootedGlobalBridgeCut NumericalBridgeCut LabelledCutJoin
open AllocationNormalization

universe u

/-! ## Transport of the component away from the rooted base -/

def carrierOtherPackage (d : Coproduct n h₀ h r m b) :
    SidePackage n h₀ h r :=
  ⟨(baseOrientedCarrier (fromCoproduct d)).otherCells,
    (baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).otherCells⟩

def literalOtherPackage (d : Coproduct n h₀ h r m b) :
    SidePackage n h₀ h r :=
  ⟨otherCellSet d, (otherRestrictedPairing d).pairing⟩

theorem carrierOtherPackage_eq_literal
    (d : Coproduct n h₀ h r m b) :
    carrierOtherPackage d = literalOtherPackage d := by
  apply Sigma.ext
  · exact baseOrientedCarrier_from_otherCells d
  · exact carrierOtherRestriction_fromCoproduct d

def otherBoundaryTransport (d : Coproduct n h₀ h r m b) :
    ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).otherCells).Boundary ≃
      (otherRestrictedPairing d).pairing.Boundary :=
  Equiv.cast (congrArg sideBoundaryType (carrierOtherPackage_eq_literal d))

set_option maxHeartbeats 1000000 in
theorem forwardOtherBoundaryMap_fromCoproduct
    (d : Coproduct n h₀ h r m b)
    (x : ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).otherCells).Boundary) :
    forwardOtherBoundaryMap (fromCoproduct d) x =
      ((otherAllocatedLabel d) (otherBoundaryTransport d x)).1 := by
  let C := baseOrientedCarrier (fromCoproduct d)
  let y := otherBoundaryTransport d x
  let z : C.core.1.1.Boundary :=
    boundaryEquivOfEq C.reassemble_exact
      (includeRightBoundary C.baseCells C.otherCells C.disjoint
        (C.core.1.1.restrict C.baseCells)
        (C.core.1.1.restrict C.otherCells) x)
  let q : (reconstructedCutPairing d).Boundary :=
    boundaryEquivOfEq (baseOrientedCarrier_from_core_pairing d) z
  have hglobal : carrierGlobalLabel C z = reconstructedCutLabel d q := by
    calc
      carrierGlobalLabel C z =
          ((boundaryEquivOfEq
            (baseOrientedCarrier_from_core_pairing d)).symm.trans
              (carrierGlobalLabel C)) q := by
        simp [q]
        rfl
      _ = reconstructedCutLabel d q :=
        congrArg (fun L ↦ L q) (carrierGlobalLabel_fromCoproduct d)
  let includedY := includeRightBoundary (baseCellSet d) (otherCellSet d)
    (cellSets_disjoint d) (baseRestrictedPairing d).pairing
      (otherRestrictedPairing d).pairing y
  have hq : q = includedY := by
    apply Subtype.ext
    simp only [q, z, includedY, boundaryEquivOfEq_val,
      includeRightBoundary_val]
    exact (sideBoundaryCast_include (carrierOtherPackage d)
      (literalOtherPackage d) (carrierOtherPackage_eq_literal d) x).symm
  calc
    forwardOtherBoundaryMap (fromCoproduct d) x =
        carrierGlobalLabel C z := by
      exact (carrierGlobalLabel_include_other C x).symm
    _ = reconstructedCutLabel d q := hglobal
    _ = reconstructedCutLabel d includedY := congrArg _ hq
    _ = ((otherAllocatedLabel d) y).1 := by
      dsimp only [includedY]
      simp only [reconstructedCutLabel, reconstructedCutPairing,
        Equiv.trans_apply, boundaryReassembleEquiv_includeRight,
        Equiv.sumCongr_apply, Sum.map_inr, finsetSumComplementEquiv]
      rfl

/-! ## Complement allocation cancellation and the local numerical label -/

def otherCarrierAllocatedLabel (d : Coproduct n h₀ h r m b) :
    ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).otherCells).Boundary ≃
      {i : Fin (m + 2) // i ∉ (labels d).1} :=
  (otherBoundaryTransport d).trans (otherAllocatedLabel d)

def complementPredicateEq' (A : Finset (Fin (m + 2))) :
    (fun i : Fin (m + 2) ↦ i ∉ A) =
      (fun i : Fin (m + 2) ↦ i ∈ Aᶜ) := by
  funext i
  apply propext
  simp

def complementSubtypeTypeEq' (A : Finset (Fin (m + 2))) :
    {i : Fin (m + 2) // i ∉ A} = {i : Fin (m + 2) // i ∈ Aᶜ} :=
  congrArg Subtype (complementPredicateEq' A)

theorem equivCast_congrArg_Subtype_val'
    {α : Type u} {p q : α → Prop} (hpq : p = q) (x : Subtype p) :
    ((Equiv.cast (congrArg Subtype hpq)) x : Subtype q).1 = x.1 := by
  subst q
  rfl

@[simp]
theorem complementSubtypeCast_val' (A : Finset (Fin (m + 2)))
    (x : {i : Fin (m + 2) // i ∉ A}) :
    ((Equiv.cast (complementSubtypeTypeEq' A)) x).1 = x.1 := by
  exact equivCast_congrArg_Subtype_val' (complementPredicateEq' A) x

def otherComplementMembershipEquiv (d : Coproduct n h₀ h r m b) :
    {i : Fin (m + 2) // i ∉ (labels d).1} ≃
      {i : Fin (m + 2) // i ∈ (labels d).1ᶜ} :=
  Equiv.cast (complementSubtypeTypeEq' (labels d).1)

theorem equivFin_cast_val'
    {X Y : Type u} [fX : Fintype X] [fY : Fintype Y]
    (hXY : X = Y) (x : X) :
    (Fintype.equivFin Y (Equiv.cast hXY x)).val =
      (Fintype.equivFin X x).val := by
  subst Y
  have hf : fX = fY := Subsingleton.elim _ _
  subst fY
  rfl

set_option maxHeartbeats 1000000 in
theorem otherAllocatedLabel_normalizes
    (d : Coproduct n h₀ h r m b) :
    HEq (((otherAllocatedLabel d).trans
      (otherComplementMembershipEquiv d)).trans
      (finsetSubtypeEquivFin (labels d).1ᶜ))
      (otherRestrictedPairing d).label := by
  have hcard : (labels d).1ᶜ.card = m - d.2.1.1 + 1 := by
    rw [Finset.card_compl]
    rw [Fintype.card_fin, (labels d).2.2.2]
    omega
  have hnotcard : m - d.2.1.1 + 1 =
      Fintype.card {i : Fin (m + 2) // i ∉ (labels d).1} := by
    rw [card_complement]
    rw [Fintype.card_fin, (labels d).2.2.2]
    omega
  apply Equiv.heq_ext_of_forall rfl (congrArg Fin hcard)
  intro x
  apply (Fin.heq_ext_iff hcard).2
  simp only [Equiv.trans_apply, otherAllocatedLabel]
  change (Fintype.equivFin {i : Fin (m + 2) // i ∈ (labels d).1ᶜ}
      (Equiv.cast (complementSubtypeTypeEq' (labels d).1)
        ((Fintype.equivFin {i : Fin (m + 2) // i ∉ (labels d).1}).symm
          (Fin.cast hnotcard ((otherRestrictedPairing d).label x))))).val = _
  rw [equivFin_cast_val']
  simp

theorem forwardOtherBoundaryAllocationEquiv_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    forwardOtherBoundaryAllocationEquiv (fromCoproduct d) =
      @equivFinsetImage _ _ (Fintype.ofFinite _) (Classical.decEq _)
        (forwardOtherBoundaryMap (fromCoproduct d))
        (forwardOtherBoundaryMap_injective (fromCoproduct d)) := by
  apply Equiv.ext
  intro x
  rfl

def forwardOtherLocalLabel (d : Coproduct n h₀ h r m b) :
    ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).otherCells).Boundary ≃
      Fin (m - (forwardBoundaryIndex (fromCoproduct d)).1 + 1) :=
  (forwardOtherBoundaryAllocationEquiv (fromCoproduct d)).trans <|
    (finsetSubtypeEquivFin
      (forwardOtherBoundaryLabels (fromCoproduct d))).trans <|
        finCongr (by
          have hsum := forwardBoundaryLabel_cards_add (fromCoproduct d)
          have hbase := forwardBaseBoundaryCard_eq (fromCoproduct d)
          omega)

set_option maxHeartbeats 2000000 in
theorem forwardOtherLocalLabel_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    HEq (forwardOtherLocalLabel d) (otherRestrictedPairing d).label := by
  let X := ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
    (baseOrientedCarrier (fromCoproduct d)).otherCells).Boundary
  let B : Finset (Fin (m + 2)) := (labels d).1ᶜ
  have hcard : B.card = m - d.2.1.1 + 1 := by
    dsimp only [B]
    rw [Finset.card_compl]
    rw [Fintype.card_fin, (labels d).2.2.2]
    omega
  letI : Fintype X := Fintype.ofFinite _
  letI : DecidableEq (Fin (m + 2)) := Classical.decEq _
  let f : X → Fin (m + 2) := forwardOtherBoundaryMap (fromCoproduct d)
  let allocated : X ≃ {i : Fin (m + 2) // i ∈ B} :=
    (otherCarrierAllocatedLabel d).trans (otherComplementMembershipEquiv d)
  have hfe : ∀ x, f x = (allocated x).1 := by
    intro x
    calc
      f x = (otherCarrierAllocatedLabel d x).1 :=
        forwardOtherBoundaryMap_fromCoproduct d x
      _ = (allocated x).1 := by
        exact (complementSubtypeCast_val' (labels d).1
          (otherCarrierAllocatedLabel d x)).symm
  have himage : Finset.univ.image f =
      forwardOtherBoundaryLabels (fromCoproduct d) := by
    rfl
  have hpre := AllocationNormalization.numericalLabel_heq_of_allocation
    B allocated f
      (forwardOtherBoundaryMap_injective (fromCoproduct d)) hfe
  have hCD : Fin (Finset.univ.image f).card = Fin B.card :=
    congrArg (fun A : Finset (Fin (m + 2)) ↦ Fin A.card)
      (AllocationNormalization.mapImage_eq_allocation
        B allocated f hfe)
  have hcount : m - (forwardBoundaryIndex (fromCoproduct d)).1 + 1 =
      m - d.2.1.1 + 1 := congrArg (fun s ↦ m - s + 1)
        (congrArg Fin.val (forwardBoundaryIndex_fromCoproduct d))
  have htarget : m - (forwardBoundaryIndex (fromCoproduct d)).1 + 1 =
      B.card := hcount.trans hcard.symm
  have hpoint (x : X) : HEq
      (forwardOtherLocalLabel d x)
      ((allocated.trans (finsetSubtypeEquivFin B)) x) := by
    apply (Fin.heq_ext_iff htarget).2
    have happ := equiv_apply_heq_of_heq hCD hpre x
    have hval := Fin.val_eq_val_of_heq happ
    dsimp only [f, allocated] at hval
    simp only [forwardOtherLocalLabel,
      forwardOtherBoundaryAllocationEquiv_fromCoproduct,
      Equiv.trans_apply, finCongr_apply_coe]
    dsimp only [allocated]
    exact hval
  have hfull : HEq (forwardOtherLocalLabel d)
      (allocated.trans (finsetSubtypeEquivFin B)) := by
    exact Equiv.heq_ext_of_forall rfl (congrArg Fin htarget)
      _ _ hpoint
  have htransport : HEq
      ((((otherCarrierAllocatedLabel d).trans
        (otherComplementMembershipEquiv d)).trans
        (finsetSubtypeEquivFin B)))
      ((((otherAllocatedLabel d).trans
        (otherComplementMembershipEquiv d)).trans
        (finsetSubtypeEquivFin B))) := by
    change HEq
      ((otherBoundaryTransport d).trans
        (((otherAllocatedLabel d).trans
          (otherComplementMembershipEquiv d)).trans
          (finsetSubtypeEquivFin B)))
      (((otherAllocatedLabel d).trans
        (otherComplementMembershipEquiv d)).trans
        (finsetSubtypeEquivFin B))
    unfold otherBoundaryTransport
    exact boundaryTransport_label_heq
      (carrierOtherPackage d) (literalOtherPackage d)
      (carrierOtherPackage_eq_literal d) B.card
      (((otherAllocatedLabel d).trans
        (otherComplementMembershipEquiv d)).trans
          (finsetSubtypeEquivFin B))
  exact hfull.trans <| htransport.trans (otherAllocatedLabel_normalizes d)


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

