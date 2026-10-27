module

public import Proofs.UnrootedBridgeCoproductNormalization
public import Proofs.OrientedCutJoinCoherence

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

namespace PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct
noncomputable section

open PointedDecomposition LabelledCutJoin GlobalBridgeCut NumericalBridgeCut

variable {n h r m b : ℕ}

/-- Every dependency of the allocation-aware raw reassembly, packaged so
that equality transports the two restricted labelled pairings together. -/
structure AllocatedRawInput (n h r m : ℕ) where
  left : Set (Fin n)
  right : Set (Fin n)
  cover : left ∪ right = Set.univ
  disjoint : Disjoint left right
  allocation : Finset (Fin (m + 2))
  leftPairing : BoundaryLabelledPairing
    (RestrictedDart (facets := fun _ : Fin n ↦ h) left) r allocation.card
  rightPairing : BoundaryLabelledPairing
    (RestrictedDart (facets := fun _ : Fin n ↦ h) right) r
      (m + 2 - allocation.card)

theorem AllocatedRawInput.ext
    {x y : AllocatedRawInput n h r m}
    (hleft : x.left = y.left)
    (hright : x.right = y.right)
    (hallocation : x.allocation = y.allocation)
    (hleftPairing : HEq x.leftPairing y.leftPairing)
    (hrightPairing : HEq x.rightPairing y.rightPairing) : x = y := by
  cases x with
  | mk S T hcover hdisj A P Q =>
    cases y with
    | mk S' T' hcover' hdisj' A' P' Q' =>
      dsimp only at hleft hright hallocation hleftPairing hrightPairing
      subst S'
      subst T'
      subst A'
      have hP : P = P' := eq_of_heq hleftPairing
      subst P'
      have hQ : Q = Q' := eq_of_heq hrightPairing
      subst Q'
      rfl

/-- Reassemble both coloured restrictions and their ambient allocation
labels into the complete star-labelled raw cut object. -/
def reassembleAllocatedRaw (x : AllocatedRawInput n h r m) :
    BoundaryLabelledPairing (Dart n h) r (m + 2) where
  pairing := reassembleColored x.left x.right x.disjoint
    x.leftPairing.pairing x.rightPairing.pairing
  label :=
    (boundaryReassembleEquiv x.left x.right x.cover x.disjoint
      x.leftPairing.pairing x.rightPairing.pairing).trans <|
      (Equiv.sumCongr
        (x.leftPairing.label.trans
          (finsetSubtypeEquivFin x.allocation).symm)
        (x.rightPairing.label.trans <|
          (finCongr (by simp)).trans
            (complementEquivFin x.allocation).symm)).trans
        (finsetSumComplementEquiv x.allocation)

def coproductRawInput (d : Coproduct n h r m b) :
    AllocatedRawInput n h r m :=
  { left := leftCellSet d
    right := rightCellSet d
    cover := cellSets_cover d
    disjoint := cellSets_disjoint d
    allocation := d.2.1.1
    leftPairing := leftRestrictedPairing d
    rightPairing := rightRestrictedPairing d }

@[simp] theorem reassembleAllocatedRaw_coproductRawInput
    (d : Coproduct n h r m b) :
    reassembleAllocatedRaw (coproductRawInput d) = reconstructedCutRaw d := by
  rfl

def carrierRawInput (C : UnrootedBridgeCutCarrier n h r m b) :
    AllocatedRawInput n h r m :=
  { left := C.leftCells
    right := C.rightCells
    cover := C.cover
    disjoint := C.disjoint
    allocation := leftBoundaryLabels C
    leftPairing := carrierLeftLocalPairing C
    rightPairing := carrierRightLocalPairing C }

theorem coproductRawInput_toCoproduct
    (z : UnrootedBridgePointed n h r m b × Bool) :
    coproductRawInput (toCoproduct z) = carrierRawInput (orientedCarrier z) := by
  apply AllocatedRawInput.ext
  · exact leftCellSet_toCoproduct z
  · exact rightCellSet_toCoproduct z
  · rfl
  · exact leftRestrictedPairing_toCoproduct z
  · exact rightRestrictedPairing_toCoproduct z

theorem reconstructedCutRaw_toCoproduct_eq_carrierReassembly
    (z : UnrootedBridgePointed n h r m b × Bool) :
    reconstructedCutRaw (toCoproduct z) =
      reassembleAllocatedRaw (carrierRawInput (orientedCarrier z)) := by
  rw [← reassembleAllocatedRaw_coproductRawInput,
    coproductRawInput_toCoproduct]

end
end PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct

namespace PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct
noncomputable section
open PointedDecomposition LabelledCutJoin GlobalBridgeCut NumericalBridgeCut
variable {n h r m b : ℕ}

def carrierGlobalLabel' (C : UnrootedBridgeCutCarrier n h r m b) :
    C.core.1.1.Boundary ≃ Fin (m + 2) :=
  (boundaryEquivOfEq C.reassemble_exact).symm |>.trans <|
    (boundaryReassembleEquiv C.leftCells C.rightCells C.cover C.disjoint
      (C.core.1.1.restrict C.leftCells)
      (C.core.1.1.restrict C.rightCells)).trans C.componentBoundaryLabel

set_option maxHeartbeats 1000000 in
theorem carrierGlobalLabel_oriented' (z :
    UnrootedBridgePointed n h r m b × Bool) :
    let C := orientedCarrier z
    let hcut : C.core.1.1 =
        (orientedMarked z).pairing.erase (orientedMarked z).seamSubtype := by
      rcases z with ⟨⟨⟨P, e⟩, hb⟩, o⟩
      cases o <;> rfl
    carrierGlobalLabel' C =
      (boundaryEquivOfEq hcut).trans (orientedCutLabel z) := by
  dsimp only
  apply Equiv.ext
  intro x
  simp only [carrierGlobalLabel', orientedCarrier, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  apply congrArg (orientedCutLabel z)
  apply Subtype.ext
  simp only [boundaryEquivOfEq_val,
    StarJoinLabelCoherence.boundaryEquivOfEq_symm_val]

set_option maxHeartbeats 1000000 in
theorem carrierGlobalLabel_from' (d : Coproduct n h r m b) :
    (boundaryEquivOfEq (orientedCarrier_from_core_pairing d)).symm.trans
        (carrierGlobalLabel' (orientedCarrier (fromCoproduct d))) =
      reconstructedCutLabel d := by
  rw [carrierGlobalLabel_oriented']
  calc
    _ = (boundaryEquivOfEq
          (erase_reconstructedJoinMarked d)).symm.trans
          (orientedCutLabel (fromCoproduct d)) := by
      apply Equiv.ext
      intro q
      simp only [Equiv.trans_apply]
      apply congrArg (orientedCutLabel (fromCoproduct d))
      apply Subtype.ext
      simp only [boundaryEquivOfEq_val,
        StarJoinLabelCoherence.boundaryEquivOfEq_symm_val]
    _ = reconstructedCutLabel d := orientedCutLabel_fromCoproduct d

end
end PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct

namespace PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct
noncomputable section

open PointedDecomposition LabelledCutJoin GlobalBridgeCut NumericalBridgeCut

variable {n h r m b : ℕ}

theorem rightBoundaryLabels_eq_compl
    (C : UnrootedBridgeCutCarrier n h r m b) :
    rightBoundaryLabels C = (leftBoundaryLabels C)ᶜ := by
  ext i
  constructor
  · intro hiR
    have hiL : i ∉ leftBoundaryLabels C := fun hiL ↦
      Finset.disjoint_left.mp (boundaryLabelAllocations_disjoint C) hiL hiR
    simpa using hiL
  · intro hiComp
    have hiL : i ∉ leftBoundaryLabels C := by
      simpa using hiComp
    have hiUnion : i ∈ leftBoundaryLabels C ∨
        i ∈ rightBoundaryLabels C := by
      have hi : i ∈ leftBoundaryLabels C ∪ rightBoundaryLabels C := by
        rw [boundaryLabelAllocations_cover]
        exact Finset.mem_univ i
      simpa only [Finset.mem_union] using hi
    exact hiUnion.resolve_left hiL

/-- Canonical enumerations of a finset and of the propositionally equal
complement subtype cancel pointwise, independently of the cardinality
proofs used by the intervening `Fin` casts. -/
theorem complementEnumeration_val
    (B R : Finset (Fin (m + 2)))
    (hR : R = Bᶜ)
    (e : Fin R.card ≃
      Fin (Fintype.card (Fin (m + 2)) - B.card))
    (he : ∀ i, (e i).val = i.val)
    (y : {i : Fin (m + 2) // i ∈ R}) :
    ((complementEquivFin B).symm
      (e (finsetSubtypeEquivFin R y))).1 = y.1 := by
  subst R
  let ynot : {i : Fin (m + 2) // i ∉ B} :=
    ⟨y.1, Finset.mem_compl.mp y.2⟩
  have htype : {i : Fin (m + 2) // i ∉ B} =
      {i : Fin (m + 2) // i ∈ Bᶜ} := complementSubtypeTypeEq B
  have hycast : Equiv.cast htype ynot = y := by
    apply Subtype.ext
    exact complementSubtypeCast_val B ynot
  have hfin : e (finsetSubtypeEquivFin Bᶜ y) =
      complementEquivFin B ynot := by
    apply Fin.eq_of_val_eq
    rw [he]
    change (Fintype.equivFin {i : Fin (m + 2) // i ∈ Bᶜ} y).val =
      (Fintype.equivFin {i : Fin (m + 2) // i ∉ B} ynot).val
    rw [← equivFin_cast_val htype ynot, hycast]
  have hout := congrArg (complementEquivFin B).symm hfin
  have hout' :
      (complementEquivFin B).symm
          (e (finsetSubtypeEquivFin Bᶜ y)) = ynot := by
    simpa using hout
  exact congrArg Subtype.val hout'

@[simp] theorem carrierLeftAllocatedLabel
    (C : UnrootedBridgeCutCarrier n h r m b) :
    (carrierLeftLocalPairing C).label.trans
        (finsetSubtypeEquivFin (leftBoundaryLabels C)).symm =
      leftBoundaryAllocationEquiv C := by
  apply Equiv.ext
  intro x
  simp [carrierLeftLocalPairing]

theorem carrierRightAllocatedLabel_val
    (C : UnrootedBridgeCutCarrier n h r m b)
    (x : (C.core.1.1.restrict C.rightCells).Boundary) :
    (((carrierRightLocalPairing C).label.trans <|
        (finCongr (by simp)).trans
          (complementEquivFin (leftBoundaryLabels C)).symm) x).1 =
      rightBoundaryLabelMap C x := by
  let R := rightBoundaryLabels C
  let B := leftBoundaryLabels C
  let y : {i : Fin (m + 2) // i ∈ R} :=
    rightBoundaryAllocationEquiv C x
  let e : Fin R.card ≃
      Fin (Fintype.card (Fin (m + 2)) - B.card) :=
    (finCongr (rightBoundaryCard_eq_sub C)).trans
      (finCongr (by dsimp [B]; simp))
  have he : ∀ i, (e i).val = i.val := by
    intro i
    rfl
  change ((complementEquivFin B).symm
    (e (finsetSubtypeEquivFin R y))).1 = rightBoundaryLabelMap C x
  calc
    ((complementEquivFin B).symm
        (e (finsetSubtypeEquivFin R y))).1 = y.1 :=
      complementEnumeration_val B R (rightBoundaryLabels_eq_compl C) e he y
    _ = rightBoundaryLabelMap C x := rfl

/-- Carrier reassembly before transporting its matching back along the
stored exact reassembly equality. -/
def carrierReassembledRaw
    (C : UnrootedBridgeCutCarrier n h r m b) :
    BoundaryLabelledPairing (Dart n h) r (m + 2) where
  pairing := reassembleColored C.leftCells C.rightCells C.disjoint
    (C.core.1.1.restrict C.leftCells)
    (C.core.1.1.restrict C.rightCells)
  label := (boundaryReassembleEquiv C.leftCells C.rightCells C.cover
    C.disjoint (C.core.1.1.restrict C.leftCells)
    (C.core.1.1.restrict C.rightCells)).trans C.componentBoundaryLabel

theorem reassembleAllocatedRaw_carrierRawInput
    (C : UnrootedBridgeCutCarrier n h r m b) :
    reassembleAllocatedRaw (carrierRawInput C) = carrierReassembledRaw C := by
  let P := reassembleColored C.leftCells C.rightCells C.disjoint
    (C.core.1.1.restrict C.leftCells)
    (C.core.1.1.restrict C.rightCells)
  let E := boundaryReassembleEquiv C.leftCells C.rightCells C.cover
    C.disjoint (C.core.1.1.restrict C.leftCells)
    (C.core.1.1.restrict C.rightCells)
  let L :=
    (Equiv.sumCongr
      ((carrierLeftLocalPairing C).label.trans
        (finsetSubtypeEquivFin (leftBoundaryLabels C)).symm)
      ((carrierRightLocalPairing C).label.trans <|
        (finCongr (by simp)).trans
          (complementEquivFin (leftBoundaryLabels C)).symm)).trans
      (finsetSumComplementEquiv (leftBoundaryLabels C))
  have hlabel : E.trans L = E.trans C.componentBoundaryLabel := by
    apply Equiv.ext
    intro x
    simp only [Equiv.trans_apply]
    cases hs : E x with
    | inl y =>
        change
          ((finsetSumComplementEquiv (leftBoundaryLabels C))
            (Sum.inl
              (((carrierLeftLocalPairing C).label.trans
                (finsetSubtypeEquivFin (leftBoundaryLabels C)).symm) y))) =
            C.componentBoundaryLabel (Sum.inl y)
        rw [carrierLeftAllocatedLabel]
        rfl
    | inr y =>
        apply Fin.eq_of_val_eq
        change
          ((((carrierRightLocalPairing C).label.trans
            ((finCongr (by simp)).trans
              (complementEquivFin (leftBoundaryLabels C)).symm)) y)).1.val =
            (C.componentBoundaryLabel (Sum.inr y)).val
        exact congrArg Fin.val (carrierRightAllocatedLabel_val C y)
  change (⟨P, E.trans L⟩ : BoundaryLabelledPairing (Dart n h) r (m + 2)) =
    ⟨P, E.trans C.componentBoundaryLabel⟩
  rw [hlabel]

/-- The carrier's raw cut object, expressed on its stored ambient matching. -/
def carrierCoreRaw (C : UnrootedBridgeCutCarrier n h r m b) :
    BoundaryLabelledPairing (Dart n h) r (m + 2) where
  pairing := C.core.1.1
  label := carrierGlobalLabel' C

theorem label_heq_transport_symm
    {P Q : ColoredMatching (Dart n h) r} (hPQ : P = Q)
    (L : P.Boundary ≃ Fin (m + 2)) :
    HEq L ((boundaryEquivOfEq hPQ).symm.trans L) := by
  cases hPQ
  rfl

theorem label_heq_transport
    {P Q : ColoredMatching (Dart n h) r} (hPQ : P = Q)
    (L : Q.Boundary ≃ Fin (m + 2)) :
    HEq ((boundaryEquivOfEq hPQ).trans L) L := by
  cases hPQ
  rfl

/-- Transporting the explicitly reassembled carrier back along its stored
exact reassembly equality gives the literal carrier core. -/
theorem carrierReassembledRaw_eq_carrierCoreRaw
    (C : UnrootedBridgeCutCarrier n h r m b) :
    carrierReassembledRaw C = carrierCoreRaw C := by
  apply BoundaryLabelledPairing.toData_injective
  apply Sigma.ext C.reassemble_exact
  exact label_heq_transport_symm C.reassemble_exact
    (carrierReassembledRaw C).label

/-- For the carrier cut with the user-selected endpoint first, its stored
raw object is exactly the generic oriented cut of the source pairing. -/
theorem carrierCoreRaw_orientedCarrier
    (z : UnrootedBridgePointed n h r m b × Bool) :
    carrierCoreRaw (orientedCarrier z) =
      OrientedCutJoinCoherence.orientedCutRaw
        z.1.1.1.1.raw (orientedSeam z) := by
  let C := orientedCarrier z
  have hcut : C.core.1.1 =
      (orientedMarked z).pairing.erase (orientedMarked z).seamSubtype := by
    rcases z with ⟨⟨⟨P, e⟩, hb⟩, o⟩
    cases o <;> rfl
  have hlabel : carrierGlobalLabel' C =
      (boundaryEquivOfEq hcut).trans (orientedCutLabel z) := by
    exact carrierGlobalLabel_oriented' z
  apply BoundaryLabelledPairing.toData_injective
  apply Sigma.ext hcut
  exact (heq_of_eq hlabel).trans
    (label_heq_transport hcut (orientedCutLabel z))

/-- Complete forward raw normalization: independent component
normalization, allocation reassembly, and oriented cut semantics cancel
exactly. -/
theorem reconstructedCutRaw_toCoproduct
    (z : UnrootedBridgePointed n h r m b × Bool) :
    reconstructedCutRaw (toCoproduct z) =
      OrientedCutJoinCoherence.orientedCutRaw
        z.1.1.1.1.raw (orientedSeam z) := by
  calc
    reconstructedCutRaw (toCoproduct z) =
        reassembleAllocatedRaw (carrierRawInput (orientedCarrier z)) :=
      reconstructedCutRaw_toCoproduct_eq_carrierReassembly z
    _ = carrierReassembledRaw (orientedCarrier z) :=
      reassembleAllocatedRaw_carrierRawInput (orientedCarrier z)
    _ = carrierCoreRaw (orientedCarrier z) :=
      carrierReassembledRaw_eq_carrierCoreRaw (orientedCarrier z)
    _ = OrientedCutJoinCoherence.orientedCutRaw
        z.1.1.1.1.raw (orientedSeam z) :=
      carrierCoreRaw_orientedCarrier z

end
end PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct
