module

public import Proofs.UnrootedComponentNormalizationFinish

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

namespace PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct
noncomputable section

open PointedDecomposition LabelledCutJoin GlobalBridgeCut NumericalBridgeCut

variable {n h r m b : ℕ}

/-- A connected stratum element is determined by its raw labelled pairing;
the remaining fields and the rank witness are propositions. -/
theorem unrootedStratum_heq_of_raw_heq
    {k l a c q s : ℕ}
    {P : UnrootedStratum k h r a q}
    {Q : UnrootedStratum l h r c s}
    (hk : k = l) (ha : a = c) (hq : q = s)
    (hraw : HEq P.1.raw Q.1.raw) : HEq P Q := by
  cases hk.symm
  cases ha.symm
  cases hq
  rw [heq_iff_eq]
  apply Subtype.ext
  apply ConnectedDiagram.raw_injective
  exact eq_of_heq hraw

/-- Extensionality for the nested dependent bridge coproduct.  Component
equalities are heterogeneous because all three outer indices occur in their
types. -/
theorem coproduct_ext {x y : Coproduct n h r m b}
    (hA : x.1 = y.1)
    (hB : x.2.1 = y.2.1)
    (hq : x.2.2.1 = y.2.2.1)
    (hL : HEq x.2.2.2.1 y.2.2.2.1)
    (hR : HEq x.2.2.2.2.1 y.2.2.2.2.1)
    (hc : x.2.2.2.2.2 = y.2.2.2.2.2) : x = y := by
  rcases x with ⟨A, B, q, L, R, c⟩
  rcases y with ⟨A', B', q', L', R', c'⟩
  dsimp only at hA hB hq hL hR hc
  subst A'
  subst B'
  subst q'
  have hLeq : L = L' := eq_of_heq hL
  subst L'
  have hReq : R = R' := eq_of_heq hR
  subst R'
  subst c'
  rfl

set_option maxHeartbeats 2000000 in
/-- Cutting the object reconstructed from arbitrary coproduct data recovers
every allocation, rank, component, and deleted colour exactly. -/
theorem toCoproduct_fromCoproduct (d : Coproduct n h r m b) :
    toCoproduct (fromCoproduct d) = d := by
  let C := orientedCarrier (fromCoproduct d)
  have hA0 : leftCellAllocation C = d.1.1 :=
    leftCellAllocation_orientedCarrier_from d
  have hA : (toCoproduct (fromCoproduct d)).1 = d.1 :=
    Subtype.ext hA0
  have hk : (leftCellAllocation C).card = d.1.1.card :=
    congrArg Finset.card hA0
  have hB0 : leftBoundaryLabels C = d.2.1.1 :=
    orientedCarrier_from_leftBoundaryLabels d
  have hB : (toCoproduct (fromCoproduct d)).2.1 = d.2.1 :=
    Subtype.ext hB0
  have ha : (leftBoundaryLabels C).card = d.2.1.1.card :=
    congrArg Finset.card hB0
  have hlrank : C.leftRank = d.2.2.1.1.1 :=
    orientedCarrier_from_leftRank d
  have hrrank : C.rightRank = d.2.2.1.1.2.1 :=
    orientedCarrier_from_rightRank d
  have hq : (toCoproduct (fromCoproduct d)).2.2.1 = d.2.2.1 := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact hlrank
    · apply Fin.ext
      exact hrrank
  have hL : HEq (leftNumericalStratum C) d.2.2.2.1 := by
    apply unrootedStratum_heq_of_raw_heq hk ha hlrank
    exact leftNumericalPairing_fromCoproduct d
  have hR : HEq (rightNumericalStratumForSplit C) d.2.2.2.2.1 := by
    apply unrootedStratum_heq_of_raw_heq
      (congrArg (fun k ↦ n - k) hk)
      (congrArg (fun a ↦ m + 2 - a) ha) hrrank
    exact rightNumericalPairing_fromCoproduct d
  have hc : C.deletedColor = d.2.2.2.2.2 :=
    orientedCarrier_from_deletedColor d
  exact coproduct_ext hA hB hq hL hR hc


end
end PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct

namespace PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct
noncomputable section

open PointedDecomposition LabelledCutJoin GlobalBridgeCut NumericalBridgeCut

variable {n h r m b : ℕ}

structure InverseNormalizationInput (n h r : ℕ) where
  cells : Set (Fin n)
  fintype : Fintype cells
  size : ℕ
  card_eq : @Fintype.card cells fintype = size
  normalized : ColoredMatching (Dart size h) r

theorem InverseNormalizationInput.ext
    {x y : InverseNormalizationInput n h r}
    (hcells : x.cells = y.cells)
    (hfintype : HEq x.fintype y.fintype)
    (hsize : x.size = y.size)
    (hnormalized : HEq x.normalized y.normalized) : x = y := by
  cases x with
  | mk X fX k hk P =>
    cases y with
    | mk Y fY l hl Q =>
      dsimp only at hcells hfintype hsize hnormalized
      subst Y
      have hf : fX = fY := eq_of_heq hfintype
      subst fY
      subst l
      have hPQ : P = Q := eq_of_heq hnormalized
      subst Q
      rfl

def inverseNormalize (x : InverseNormalizationInput n h r) :
    ColoredMatching
      (RestrictedDart (facets := fun _ : Fin n ↦ h) x.cells) r := by
  letI : Fintype x.cells := x.fintype
  exact (componentColoredMatchingEquiv x.cells x.card_eq).symm x.normalized

structure InverseLabelledNormalizationInput (n h r : ℕ) where
  cells : Set (Fin n)
  fintype : Fintype cells
  size : ℕ
  card_eq : @Fintype.card cells fintype = size
  labels : ℕ
  normalized : BoundaryLabelledPairing (Dart size h) r labels

theorem InverseLabelledNormalizationInput.ext
    {x y : InverseLabelledNormalizationInput n h r}
    (hcells : x.cells = y.cells)
    (hfintype : HEq x.fintype y.fintype)
    (hsize : x.size = y.size)
    (hlabels : x.labels = y.labels)
    (hnormalized : HEq x.normalized y.normalized) : x = y := by
  cases x with
  | mk X fX k hk a P =>
    cases y with
    | mk Y fY l hl c Q =>
      dsimp only at hcells hfintype hsize hlabels hnormalized
      subst Y
      have hf : fX = fY := eq_of_heq hfintype
      subst fY
      subst l
      subst c
      have hPQ : P = Q := eq_of_heq hnormalized
      subst Q
      rfl

def inverseNormalizeLabelled
    (x : InverseLabelledNormalizationInput n h r) :
    BoundaryLabelledPairing
      (RestrictedDart (facets := fun _ : Fin n ↦ h) x.cells) r x.labels := by
  letI : Fintype x.cells := x.fintype
  exact (componentBoundaryLabelledEquiv x.cells x.card_eq).symm x.normalized

def carrierLeftLocalPairing (C : UnrootedBridgeCutCarrier n h r m b) :
    BoundaryLabelledPairing
      (RestrictedDart (facets := fun _ : Fin n ↦ h) C.leftCells) r
      (leftBoundaryLabels C).card where
  pairing := C.core.1.1.restrict C.leftCells
  label := (leftBoundaryAllocationEquiv C).trans
    (finsetSubtypeEquivFin (leftBoundaryLabels C))

def carrierRightLocalPairing (C : UnrootedBridgeCutCarrier n h r m b) :
    BoundaryLabelledPairing
      (RestrictedDart (facets := fun _ : Fin n ↦ h) C.rightCells) r
      (m + 2 - (leftBoundaryLabels C).card) where
  pairing := C.core.1.1.restrict C.rightCells
  label := (rightBoundaryAllocationEquiv C).trans <|
    (finsetSubtypeEquivFin (rightBoundaryLabels C)).trans
      (finCongr (rightBoundaryCard_eq_sub C))

structure ReassemblyInput (n h r : ℕ) where
  left : Set (Fin n)
  right : Set (Fin n)
  disjoint : Disjoint left right
  leftPairing : ColoredMatching
    (RestrictedDart (facets := fun _ : Fin n ↦ h) left) r
  rightPairing : ColoredMatching
    (RestrictedDart (facets := fun _ : Fin n ↦ h) right) r

theorem ReassemblyInput.ext {x y : ReassemblyInput n h r}
    (hleft : x.left = y.left) (hright : x.right = y.right)
    (hleftPairing : HEq x.leftPairing y.leftPairing)
    (hrightPairing : HEq x.rightPairing y.rightPairing) : x = y := by
  cases x with
  | mk S T hST P Q =>
    cases y with
    | mk S' T' hST' P' Q' =>
      dsimp only at hleft hright hleftPairing hrightPairing
      subst S'
      subst T'
      have hP : P = P' := eq_of_heq hleftPairing
      subst P'
      have hQ : Q = Q' := eq_of_heq hrightPairing
      subst Q'
      rfl

def reassembleInput (x : ReassemblyInput n h r) :
    ColoredMatching (Dart n h) r :=
  reassembleColored x.left x.right x.disjoint
    x.leftPairing x.rightPairing

theorem leftCellSet_toCoproduct
    (z : UnrootedBridgePointed n h r m b × Bool) :
    leftCellSet (toCoproduct z) = (orientedCarrier z).leftCells := by
  classical
  ext x
  simp [leftCellSet, toCoproduct, leftCellAllocation]

theorem rightCellSet_toCoproduct
    (z : UnrootedBridgePointed n h r m b × Bool) :
    rightCellSet (toCoproduct z) = (orientedCarrier z).rightCells := by
  classical
  ext x
  have hcover := (orientedCarrier z).cover
  have hdisj := (orientedCarrier z).disjoint
  constructor
  · intro hx
    have hxnot : x ∉ (orientedCarrier z).leftCells := by
      simpa [rightCellSet, toCoproduct, leftCellAllocation] using hx
    have hxside : x ∈ (orientedCarrier z).leftCells ∨
        x ∈ (orientedCarrier z).rightCells := by
      have : x ∈ (orientedCarrier z).leftCells ∪
          (orientedCarrier z).rightCells := by
        rw [hcover]
        exact Set.mem_univ x
      simpa only [Set.mem_union] using this
    exact hxside.resolve_left hxnot
  · intro hx
    change x ∉ (toCoproduct z).1.1
    intro hxA
    have hxL : x ∈ (orientedCarrier z).leftCells := by
      simpa [toCoproduct, leftCellAllocation] using hxA
    exact Set.disjoint_left.mp hdisj hxL hx

set_option maxHeartbeats 1000000 in
theorem leftRestrictedPairing_toCoproduct_pairing
    (z : UnrootedBridgePointed n h r m b × Bool) :
    HEq (leftRestrictedPairing (toCoproduct z)).pairing
      ((orientedCarrier z).core.1.1.restrict
        (orientedCarrier z).leftCells) := by
  let C := orientedCarrier z
  let d := toCoproduct z
  let S := leftCellSet d
  let P := C.core.1.1.restrict C.leftCells
  let Q := (leftRestrictedPairing d).pairing
  have hS : S = C.leftCells := leftCellSet_toCoproduct z
  let fQ : Fintype S := inferInstance
  let fP : Fintype C.leftCells :=
    NumericalBridgeCut.finiteSetFintype C.leftCells
  have hf : HEq fQ fP := by
    have hfun := congr_arg_heq
      (fun U : Set (Fin n) ↦ NumericalBridgeCut.finiteSetFintype U) hS
    exact (heq_of_eq (Subsingleton.elim _ _)).trans hfun
  have hkQ : @Fintype.card S fQ = (leftCellAllocation C).card := by
    change Fintype.card (leftCellSet d) = (toCoproduct z).1.1.card
    exact leftCellSet_card d
  have hkP : @Fintype.card C.leftCells fP =
      (leftCellAllocation C).card :=
    (Set.toFinset_card C.leftCells).symm
  have hQnorm :
      componentColoredMatchingEquiv S (leftCellSet_card d) Q =
        (leftNumericalPairing C).pairing := by
    exact congrArg BoundaryLabelledPairing.pairing
      (componentBoundaryLabelledEquiv_apply_symm_apply
        (r := r) (m := (leftBoundaryLabels C).card)
        S (leftCellSet_card d) (leftNumericalPairing C))
  have hPnorm :
      @componentColoredMatchingEquiv n h (leftCellAllocation C).card r
          C.leftCells fP
          (Set.toFinset_card C.leftCells).symm P =
        (leftNumericalPairing C).pairing := by
    rfl
  let xQ : InverseNormalizationInput n h r :=
    ⟨S, fQ, (leftCellAllocation C).card, hkQ,
      (leftNumericalPairing C).pairing⟩
  let xP : InverseNormalizationInput n h r :=
    ⟨C.leftCells, fP, (leftCellAllocation C).card, hkP,
      (leftNumericalPairing C).pairing⟩
  have hx : xQ = xP :=
    InverseNormalizationInput.ext hS hf rfl (heq_of_eq rfl)
  have hi : HEq (inverseNormalize xQ) (inverseNormalize xP) :=
    congr_arg_heq inverseNormalize hx
  have hiQ : inverseNormalize xQ = Q := by
    change (componentColoredMatchingEquiv S hkQ).symm
      (leftNumericalPairing C).pairing = Q
    rw [← hQnorm]
    exact componentColoredMatchingEquiv_symm_apply_apply S hkQ Q
  have hiP : inverseNormalize xP = P := by
    change (componentColoredMatchingEquiv C.leftCells hkP).symm
      (leftNumericalPairing C).pairing = P
    rw [← hPnorm]
    exact componentColoredMatchingEquiv_symm_apply_apply C.leftCells hkP P
  exact (heq_of_eq hiQ.symm).trans <| hi.trans (heq_of_eq hiP)

set_option maxHeartbeats 1000000 in
theorem rightRestrictedPairing_toCoproduct_pairing
    (z : UnrootedBridgePointed n h r m b × Bool) :
    HEq (rightRestrictedPairing (toCoproduct z)).pairing
      ((orientedCarrier z).core.1.1.restrict
        (orientedCarrier z).rightCells) := by
  let C := orientedCarrier z
  let d := toCoproduct z
  let S := rightCellSet d
  let P := C.core.1.1.restrict C.rightCells
  let Q := (rightRestrictedPairing d).pairing
  have hS : S = C.rightCells := rightCellSet_toCoproduct z
  let fQ : Fintype S := inferInstance
  let fP : Fintype C.rightCells :=
    NumericalBridgeCut.finiteSetFintype C.rightCells
  have hf : HEq fQ fP := by
    have hfun := congr_arg_heq
      (fun U : Set (Fin n) ↦ NumericalBridgeCut.finiteSetFintype U) hS
    exact (heq_of_eq (Subsingleton.elim _ _)).trans hfun
  have hkQ : @Fintype.card S fQ =
      n - (leftCellAllocation C).card := by
    change Fintype.card (rightCellSet d) =
      n - (toCoproduct z).1.1.card
    exact rightCellSet_card d
  have hkP : @Fintype.card C.rightCells fP =
      n - (leftCellAllocation C).card := rightCellCard_eq_sub C
  have hQnorm :
      componentColoredMatchingEquiv S (rightCellSet_card d) Q =
        (rightNumericalPairing C).pairing := by
    exact congrArg BoundaryLabelledPairing.pairing
      (componentBoundaryLabelledEquiv_apply_symm_apply
        (r := r) (m := m + 2 - (leftBoundaryLabels C).card)
        S (rightCellSet_card d) (rightNumericalPairing C))
  have hPnorm :
      @componentColoredMatchingEquiv n h
          (n - (leftCellAllocation C).card) r C.rightCells fP
          (rightCellCard_eq_sub C) P =
        (rightNumericalPairing C).pairing := by
    rfl
  let xQ : InverseNormalizationInput n h r :=
    ⟨S, fQ, n - (leftCellAllocation C).card, hkQ,
      (rightNumericalPairing C).pairing⟩
  let xP : InverseNormalizationInput n h r :=
    ⟨C.rightCells, fP, n - (leftCellAllocation C).card, hkP,
      (rightNumericalPairing C).pairing⟩
  have hx : xQ = xP :=
    InverseNormalizationInput.ext hS hf rfl (heq_of_eq rfl)
  have hi : HEq (inverseNormalize xQ) (inverseNormalize xP) :=
    congr_arg_heq inverseNormalize hx
  have hiQ : inverseNormalize xQ = Q := by
    change (componentColoredMatchingEquiv S hkQ).symm
      (rightNumericalPairing C).pairing = Q
    rw [← hQnorm]
    exact componentColoredMatchingEquiv_symm_apply_apply S hkQ Q
  have hiP : inverseNormalize xP = P := by
    change (componentColoredMatchingEquiv C.rightCells hkP).symm
      (rightNumericalPairing C).pairing = P
    rw [← hPnorm]
    exact componentColoredMatchingEquiv_symm_apply_apply C.rightCells hkP P
  exact (heq_of_eq hiQ.symm).trans <| hi.trans (heq_of_eq hiP)

set_option maxHeartbeats 1000000 in
theorem leftRestrictedPairing_toCoproduct
    (z : UnrootedBridgePointed n h r m b × Bool) :
    HEq (leftRestrictedPairing (toCoproduct z))
      (carrierLeftLocalPairing (orientedCarrier z)) := by
  let C := orientedCarrier z
  let d := toCoproduct z
  let S := leftCellSet d
  let Q := leftRestrictedPairing d
  let P := carrierLeftLocalPairing C
  have hS : S = C.leftCells := leftCellSet_toCoproduct z
  let fQ : Fintype S := inferInstance
  let fP : Fintype C.leftCells :=
    NumericalBridgeCut.finiteSetFintype C.leftCells
  have hf : HEq fQ fP := by
    have hfun := congr_arg_heq
      (fun U : Set (Fin n) ↦ NumericalBridgeCut.finiteSetFintype U) hS
    exact (heq_of_eq (Subsingleton.elim _ _)).trans hfun
  have hkQ : @Fintype.card S fQ = (leftCellAllocation C).card := by
    change Fintype.card (leftCellSet d) = (toCoproduct z).1.1.card
    exact leftCellSet_card d
  have hkP : @Fintype.card C.leftCells fP =
      (leftCellAllocation C).card :=
    (Set.toFinset_card C.leftCells).symm
  have hQnorm : componentBoundaryLabelledEquiv S (leftCellSet_card d) Q =
      leftNumericalPairing C :=
    componentBoundaryLabelledEquiv_apply_symm_apply S (leftCellSet_card d)
      (leftNumericalPairing C)
  have hPnorm :
      @componentBoundaryLabelledEquiv n h (leftCellAllocation C).card r
          (leftBoundaryLabels C).card C.leftCells fP
          (Set.toFinset_card C.leftCells).symm P =
        leftNumericalPairing C := by
    rfl
  let xQ : InverseLabelledNormalizationInput n h r :=
    ⟨S, fQ, (leftCellAllocation C).card, hkQ,
      (leftBoundaryLabels C).card, leftNumericalPairing C⟩
  let xP : InverseLabelledNormalizationInput n h r :=
    ⟨C.leftCells, fP, (leftCellAllocation C).card, hkP,
      (leftBoundaryLabels C).card, leftNumericalPairing C⟩
  have hx : xQ = xP := InverseLabelledNormalizationInput.ext
    hS hf rfl rfl (heq_of_eq rfl)
  have hi : HEq (inverseNormalizeLabelled xQ)
      (inverseNormalizeLabelled xP) :=
    congr_arg_heq inverseNormalizeLabelled hx
  have hiQ : inverseNormalizeLabelled xQ = Q := by
    change (componentBoundaryLabelledEquiv S hkQ).symm
      (leftNumericalPairing C) = Q
    rw [← hQnorm]
    exact componentBoundaryLabelledEquiv_symm_apply_apply S hkQ Q
  have hiP : inverseNormalizeLabelled xP = P := by
    change (componentBoundaryLabelledEquiv C.leftCells hkP).symm
      (leftNumericalPairing C) = P
    rw [← hPnorm]
    exact componentBoundaryLabelledEquiv_symm_apply_apply C.leftCells hkP P
  exact (heq_of_eq hiQ.symm).trans <| hi.trans (heq_of_eq hiP)

set_option maxHeartbeats 1000000 in
theorem rightRestrictedPairing_toCoproduct
    (z : UnrootedBridgePointed n h r m b × Bool) :
    HEq (rightRestrictedPairing (toCoproduct z))
      (carrierRightLocalPairing (orientedCarrier z)) := by
  let C := orientedCarrier z
  let d := toCoproduct z
  let S := rightCellSet d
  let Q := rightRestrictedPairing d
  let P := carrierRightLocalPairing C
  have hS : S = C.rightCells := rightCellSet_toCoproduct z
  let fQ : Fintype S := inferInstance
  let fP : Fintype C.rightCells :=
    NumericalBridgeCut.finiteSetFintype C.rightCells
  have hf : HEq fQ fP := by
    have hfun := congr_arg_heq
      (fun U : Set (Fin n) ↦ NumericalBridgeCut.finiteSetFintype U) hS
    exact (heq_of_eq (Subsingleton.elim _ _)).trans hfun
  have hkQ : @Fintype.card S fQ =
      n - (leftCellAllocation C).card := by
    change Fintype.card (rightCellSet d) = n - (toCoproduct z).1.1.card
    exact rightCellSet_card d
  have hkP : @Fintype.card C.rightCells fP =
      n - (leftCellAllocation C).card := rightCellCard_eq_sub C
  have hQnorm : componentBoundaryLabelledEquiv S (rightCellSet_card d) Q =
      rightNumericalPairing C :=
    componentBoundaryLabelledEquiv_apply_symm_apply S (rightCellSet_card d)
      (rightNumericalPairing C)
  have hPnorm :
      @componentBoundaryLabelledEquiv n h
          (n - (leftCellAllocation C).card) r
          (m + 2 - (leftBoundaryLabels C).card) C.rightCells fP
          (rightCellCard_eq_sub C) P = rightNumericalPairing C := by
    rfl
  let xQ : InverseLabelledNormalizationInput n h r :=
    ⟨S, fQ, n - (leftCellAllocation C).card, hkQ,
      m + 2 - (leftBoundaryLabels C).card, rightNumericalPairing C⟩
  let xP : InverseLabelledNormalizationInput n h r :=
    ⟨C.rightCells, fP, n - (leftCellAllocation C).card, hkP,
      m + 2 - (leftBoundaryLabels C).card, rightNumericalPairing C⟩
  have hx : xQ = xP := InverseLabelledNormalizationInput.ext
    hS hf rfl rfl (heq_of_eq rfl)
  have hi : HEq (inverseNormalizeLabelled xQ)
      (inverseNormalizeLabelled xP) :=
    congr_arg_heq inverseNormalizeLabelled hx
  have hiQ : inverseNormalizeLabelled xQ = Q := by
    change (componentBoundaryLabelledEquiv S hkQ).symm
      (rightNumericalPairing C) = Q
    rw [← hQnorm]
    exact componentBoundaryLabelledEquiv_symm_apply_apply S hkQ Q
  have hiP : inverseNormalizeLabelled xP = P := by
    change (componentBoundaryLabelledEquiv C.rightCells hkP).symm
      (rightNumericalPairing C) = P
    rw [← hPnorm]
    exact componentBoundaryLabelledEquiv_symm_apply_apply C.rightCells hkP P
  exact (heq_of_eq hiQ.symm).trans <| hi.trans (heq_of_eq hiP)

set_option maxHeartbeats 1000000 in
theorem reconstructedCutPairing_toCoproduct
    (z : UnrootedBridgePointed n h r m b × Bool) :
    reconstructedCutPairing (toCoproduct z) =
      (orientedCarrier z).core.1.1 := by
  let C := orientedCarrier z
  let d := toCoproduct z
  let xD : ReassemblyInput n h r :=
    ⟨leftCellSet d, rightCellSet d, cellSets_disjoint d,
      (leftRestrictedPairing d).pairing,
      (rightRestrictedPairing d).pairing⟩
  let xC : ReassemblyInput n h r :=
    ⟨C.leftCells, C.rightCells, C.disjoint,
      C.core.1.1.restrict C.leftCells,
      C.core.1.1.restrict C.rightCells⟩
  have hx : xD = xC := ReassemblyInput.ext
    (leftCellSet_toCoproduct z) (rightCellSet_toCoproduct z)
    (leftRestrictedPairing_toCoproduct_pairing z)
    (rightRestrictedPairing_toCoproduct_pairing z)
  have hr := congrArg reassembleInput hx
  change reconstructedCutPairing d = C.core.1.1
  calc
    reconstructedCutPairing d = reassembleInput xD := rfl
    _ = reassembleInput xC := hr
    _ = C.core.1.1 := C.reassemble_exact

end
end PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct
