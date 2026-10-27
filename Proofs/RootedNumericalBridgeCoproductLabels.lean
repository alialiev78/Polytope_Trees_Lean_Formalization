module

public import Proofs.RootedNumericalBridgeCoproductComponents
public import Proofs.BoundaryLabelledHEq
public import Proofs.DependentEquivHEq
public import Proofs.AllocationNormalization
public import Proofs.AllocationLabelHEq

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

/-! ## A single global label on the intrinsic carrier -/

def carrierGlobalLabel (C : RootedBridgeCutCarrier n h₀ h r m b) :
    C.core.1.1.Boundary ≃ Fin (m + 2) :=
  (boundaryEquivOfEq C.reassemble_exact).symm |>.trans <|
    (boundaryReassembleEquiv C.baseCells C.otherCells C.cover C.disjoint
      (C.core.1.1.restrict C.baseCells)
      (C.core.1.1.restrict C.otherCells)).trans C.componentBoundaryLabel

@[simp]
theorem carrierGlobalLabel_include_base
    (C : RootedBridgeCutCarrier n h₀ h r m b)
    (x : (C.core.1.1.restrict C.baseCells).Boundary) :
    carrierGlobalLabel C
        (boundaryEquivOfEq C.reassemble_exact
          (includeLeftBoundary C.baseCells C.otherCells C.disjoint
            (C.core.1.1.restrict C.baseCells)
            (C.core.1.1.restrict C.otherCells) x)) =
      C.componentBoundaryLabel (Sum.inl x) := by
  simp [carrierGlobalLabel]

@[simp]
theorem carrierGlobalLabel_include_other
    (C : RootedBridgeCutCarrier n h₀ h r m b)
    (x : (C.core.1.1.restrict C.otherCells).Boundary) :
    carrierGlobalLabel C
        (boundaryEquivOfEq C.reassemble_exact
          (includeRightBoundary C.baseCells C.otherCells C.disjoint
            (C.core.1.1.restrict C.baseCells)
            (C.core.1.1.restrict C.otherCells) x)) =
      C.componentBoundaryLabel (Sum.inr x) := by
  simp [carrierGlobalLabel]

theorem carrierGlobalLabel_of_component
    (C : RootedBridgeCutCarrier n h₀ h r m b)
    (L : C.core.1.1.Boundary ≃ Fin (m + 2)) :
    let B := boundaryReassembleEquiv C.baseCells C.otherCells
      C.cover C.disjoint
      (C.core.1.1.restrict C.baseCells)
      (C.core.1.1.restrict C.otherCells)
    carrierGlobalLabel { C with
      componentBoundaryLabel := B.symm.trans <|
        (boundaryEquivOfEq C.reassemble_exact).trans L } = L := by
  dsimp only
  apply Equiv.ext
  intro x
  simp [carrierGlobalLabel]

set_option maxHeartbeats 3000000 in
theorem carrierGlobalLabel_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    (boundaryEquivOfEq
      (baseOrientedCarrier_from_core_pairing d)).symm.trans
        (carrierGlobalLabel (baseOrientedCarrier (fromCoproduct d))) =
      reconstructedCutLabel d := by
  let z := fromCoproduct d
  let C := cutBridge z
  let hcut : C.core.1.1 =
      (baseOrientedMarked z).pairing.erase
        (baseOrientedMarked z).seamSubtype := cutBridge_core_pairing z
  have hcarrier : carrierGlobalLabel (baseOrientedCarrier z) =
      (boundaryEquivOfEq hcut).trans (baseOrientedCutLabel z) := by
    change carrierGlobalLabel { C with
        componentBoundaryLabel :=
          (boundaryReassembleEquiv C.baseCells C.otherCells C.cover C.disjoint
            (C.core.1.1.restrict C.baseCells)
            (C.core.1.1.restrict C.otherCells)).symm |>.trans <|
              (boundaryEquivOfEq C.reassemble_exact).trans <|
                (boundaryEquivOfEq hcut).trans (baseOrientedCutLabel z) } = _
    exact carrierGlobalLabel_of_component C
      ((boundaryEquivOfEq hcut).trans (baseOrientedCutLabel z))
  change (boundaryEquivOfEq
      (baseOrientedCarrier_from_core_pairing d)).symm.trans
        (carrierGlobalLabel (baseOrientedCarrier z)) = _
  rw [hcarrier]
  calc
    _ = (boundaryEquivOfEq
          (erase_reconstructedJoinMarked d)).symm.trans
          (baseOrientedCutLabel (fromCoproduct d)) := by
      apply Equiv.ext
      intro q
      simp only [Equiv.trans_apply]
      apply congrArg (baseOrientedCutLabel (fromCoproduct d))
      apply Subtype.ext
      calc
        ((boundaryEquivOfEq hcut)
          ((boundaryEquivOfEq
            (baseOrientedCarrier_from_core_pairing d)).symm q)).1 =
            ((boundaryEquivOfEq
              (baseOrientedCarrier_from_core_pairing d)).symm q).1 :=
          boundaryEquivOfEq_val hcut _
        _ = q.1 := StarJoinLabelCoherence.boundaryEquivOfEq_symm_val
          (baseOrientedCarrier_from_core_pairing d) q
        _ = ((boundaryEquivOfEq
            (erase_reconstructedJoinMarked d)).symm q).1 :=
          (StarJoinLabelCoherence.boundaryEquivOfEq_symm_val
            (erase_reconstructedJoinMarked d) q).symm
    _ = reconstructedCutLabel d :=
      baseOrientedCutLabel_fromCoproduct d

/-! ## Boundary transport between the recovered and literal restrictions -/

abbrev SidePackage (n h₀ h r : ℕ) :=
  Σ S : Set (RootedCell n),
    ColoredMatching (RestrictedDart (facets := rootedFacets h₀ h) S) r

def carrierBasePackage (d : Coproduct n h₀ h r m b) :
    SidePackage n h₀ h r :=
  ⟨(baseOrientedCarrier (fromCoproduct d)).baseCells,
    (baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).baseCells⟩

def literalBasePackage (d : Coproduct n h₀ h r m b) :
    SidePackage n h₀ h r :=
  ⟨baseCellSet d, (baseRestrictedPairing d).pairing⟩

theorem carrierBasePackage_eq_literal
    (d : Coproduct n h₀ h r m b) :
    carrierBasePackage d = literalBasePackage d := by
  apply Sigma.ext
  · exact baseOrientedCarrier_from_baseCells d
  · exact carrierBaseRestriction_fromCoproduct d

def sideBoundaryType (p : SidePackage n h₀ h r) : Type :=
  p.2.Boundary

def baseBoundaryTransport (d : Coproduct n h₀ h r m b) :
    ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).baseCells).Boundary ≃
      (baseRestrictedPairing d).pairing.Boundary :=
  Equiv.cast (congrArg sideBoundaryType (carrierBasePackage_eq_literal d))

theorem sideBoundaryCast_include
    (p q : SidePackage n h₀ h r) (hpq : p = q)
    (x : p.2.Boundary) :
    includeDart (facets := rootedFacets h₀ h) q.1
        ((Equiv.cast (congrArg sideBoundaryType hpq)) x).1 =
      includeDart (facets := rootedFacets h₀ h) p.1 x.1 := by
  cases hpq
  rfl

set_option maxHeartbeats 1000000 in
theorem forwardBaseBoundaryMap_fromCoproduct
    (d : Coproduct n h₀ h r m b)
    (x : ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).baseCells).Boundary) :
    forwardBaseBoundaryMap (fromCoproduct d) x =
      ((baseAllocatedLabel d) (baseBoundaryTransport d x)).1 := by
  let C := baseOrientedCarrier (fromCoproduct d)
  let y := baseBoundaryTransport d x
  let z : C.core.1.1.Boundary :=
    boundaryEquivOfEq C.reassemble_exact
      (includeLeftBoundary C.baseCells C.otherCells C.disjoint
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
  let includedY := includeLeftBoundary (baseCellSet d) (otherCellSet d)
    (cellSets_disjoint d) (baseRestrictedPairing d).pairing
      (otherRestrictedPairing d).pairing y
  have hq : q = includedY := by
    apply Subtype.ext
    simp only [q, z, includedY, boundaryEquivOfEq_val,
      includeLeftBoundary_val]
    exact (sideBoundaryCast_include (carrierBasePackage d)
      (literalBasePackage d) (carrierBasePackage_eq_literal d) x).symm
  calc
    forwardBaseBoundaryMap (fromCoproduct d) x =
        carrierGlobalLabel C z := by
      exact (carrierGlobalLabel_include_base C x).symm
    _ = reconstructedCutLabel d q := hglobal
    _ = reconstructedCutLabel d includedY := congrArg _ hq
    _ = ((baseAllocatedLabel d) y).1 := by
      dsimp only [includedY]
      simp only [reconstructedCutLabel, reconstructedCutPairing,
        Equiv.trans_apply, boundaryReassembleEquiv_includeLeft,
        Equiv.sumCongr_apply, Sum.map_inl, finsetSumComplementEquiv]
      rfl

/-! ## Numerical label cancellation on the base component -/

def baseCarrierAllocatedLabel (d : Coproduct n h₀ h r m b) :
    ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).baseCells).Boundary ≃
      {i : Fin (m + 2) // i ∈ (labels d).1} :=
  (baseBoundaryTransport d).trans (baseAllocatedLabel d)

theorem forwardBaseBoundaryAllocationEquiv_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    forwardBaseBoundaryAllocationEquiv (fromCoproduct d) =
      @equivFinsetImage _ _ (Fintype.ofFinite _) (Classical.decEq _)
        (forwardBaseBoundaryMap (fromCoproduct d))
        (forwardBaseBoundaryMap_injective (fromCoproduct d)) := by
  apply Equiv.ext
  intro x
  rfl

theorem equiv_apply_heq_of_heq
    {A C D : Type u} (hCD : C = D)
    {f : A ≃ C} {g : A ≃ D} (hfg : HEq f g) (x : A) :
    HEq (f x) (g x) := by
  cases hCD
  exact heq_of_eq (congrArg (fun e ↦ e x) (eq_of_heq hfg))

theorem boundaryTransport_label_heq
    (p q : SidePackage n h₀ h r) (hpq : p = q) (k : ℕ)
    (label : q.2.Boundary ≃ Fin k) :
    HEq ((Equiv.cast (congrArg sideBoundaryType hpq)).trans label) label := by
  cases hpq
  rfl

theorem allocationEquiv_cancel
    {X Y : Type u} {s t : ℕ} (hst : s = t)
    (label : X ≃ Fin s) (e : Y ≃ Fin t) :
    ((((label.trans (finCongr hst)).trans e.symm).trans e).trans
      (finCongr hst.symm)) = label := by
  rw [Equiv.trans_assoc]
  rw [Equiv.trans_assoc]
  rw [← Equiv.trans_assoc e.symm e]
  rw [Equiv.symm_trans_self]
  rw [Equiv.refl_trans]
  rw [Equiv.trans_assoc]
  rw [← finCongr_symm hst]
  rw [Equiv.self_trans_symm]
  rw [Equiv.trans_refl]

def forwardBaseLocalLabel (d : Coproduct n h₀ h r m b) :
    ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).baseCells).Boundary ≃
      Fin ((forwardBoundaryIndex (fromCoproduct d)).1 + 1) :=
  (forwardBaseBoundaryAllocationEquiv (fromCoproduct d)).trans <|
    (finsetSubtypeEquivFin
      (forwardBaseBoundaryLabels (fromCoproduct d))).trans <|
        finCongr (forwardBaseBoundaryCard_eq (fromCoproduct d))

set_option maxHeartbeats 2000000 in
theorem forwardBaseLocalLabel_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    HEq (forwardBaseLocalLabel d) (baseRestrictedPairing d).label := by
  let X := ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
    (baseOrientedCarrier (fromCoproduct d)).baseCells).Boundary
  letI : Fintype X := Fintype.ofFinite _
  letI : DecidableEq (Fin (m + 2)) := Classical.decEq _
  let f : X → Fin (m + 2) := forwardBaseBoundaryMap (fromCoproduct d)
  let allocated : X ≃ {i : Fin (m + 2) // i ∈ (labels d).1} :=
    baseCarrierAllocatedLabel d
  have hfe : ∀ x, f x = (allocated x).1 :=
    forwardBaseBoundaryMap_fromCoproduct d
  have himage : Finset.univ.image f =
      forwardBaseBoundaryLabels (fromCoproduct d) := by
    rfl
  have hpre := AllocationNormalization.numericalLabel_heq_of_allocation
    (labels d).1 allocated f
      (forwardBaseBoundaryMap_injective (fromCoproduct d)) hfe
  have hCD : Fin (Finset.univ.image f).card = Fin (labels d).1.card :=
    congrArg (fun A : Finset (Fin (m + 2)) ↦ Fin A.card)
      (AllocationNormalization.mapImage_eq_allocation
        (labels d).1 allocated f hfe)
  have hcount : (forwardBoundaryIndex (fromCoproduct d)).1 + 1 =
      d.2.1.1 + 1 := congrArg (fun s ↦ s + 1)
        (congrArg Fin.val (forwardBoundaryIndex_fromCoproduct d))
  have hpoint (x : X) : HEq
      (forwardBaseLocalLabel d x)
      (((baseCarrierAllocatedLabel d).trans
          (finsetSubtypeEquivFin (labels d).1) |>.trans
            (finCongr (labels d).2.2.2)) x) := by
    apply (Fin.heq_ext_iff hcount).2
    have happ := equiv_apply_heq_of_heq hCD hpre x
    have hval := Fin.val_eq_val_of_heq happ
    dsimp only [f, allocated] at hval
    simp only [forwardBaseLocalLabel,
      forwardBaseBoundaryAllocationEquiv_fromCoproduct,
      Equiv.trans_apply, finCongr_apply_coe, himage, forwardBaseBoundaryLabels]
    exact hval
  have hfull : HEq (forwardBaseLocalLabel d)
      ((baseCarrierAllocatedLabel d).trans
        (finsetSubtypeEquivFin (labels d).1) |>.trans
          (finCongr (labels d).2.2.2)) := by
    exact Equiv.heq_ext_of_forall rfl (congrArg Fin hcount)
      _ _ hpoint
  have hdenorm :
      (((baseAllocatedLabel d).trans
          (finsetSubtypeEquivFin (labels d).1)).trans
            (finCongr (labels d).2.2.2)) =
        (baseRestrictedPairing d).label := by
    exact allocationEquiv_cancel (labels d).2.2.2.symm
      (baseRestrictedPairing d).label
      (finsetSubtypeEquivFin (labels d).1)
  have htransport : HEq
      (((baseCarrierAllocatedLabel d).trans
          (finsetSubtypeEquivFin (labels d).1)).trans
            (finCongr (labels d).2.2.2))
      (((baseAllocatedLabel d).trans
          (finsetSubtypeEquivFin (labels d).1)).trans
            (finCongr (labels d).2.2.2)) := by
    change HEq
      ((baseBoundaryTransport d).trans
        (((baseAllocatedLabel d).trans
          (finsetSubtypeEquivFin (labels d).1)).trans
            (finCongr (labels d).2.2.2)))
      (((baseAllocatedLabel d).trans
          (finsetSubtypeEquivFin (labels d).1)).trans
            (finCongr (labels d).2.2.2))
    exact boundaryTransport_label_heq
      (carrierBasePackage d) (literalBasePackage d)
      (carrierBasePackage_eq_literal d) (d.2.1.1 + 1) _
  exact hfull.trans (htransport.trans (heq_of_eq hdenorm))


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

