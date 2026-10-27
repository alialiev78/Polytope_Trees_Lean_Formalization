module

public import Proofs.UnrootedComponentNormalization
public import Proofs.AllocationLabelHEq
public import Proofs.DependentEquivHEq

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Full boundary-labelled normalization of reconstructed unrooted components

This final layer combines pointwise global label coherence with the generic
allocation cancellation theorem and packages all dependent normalization
indices into a single equality.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace UnrootedBridgeCoproduct

noncomputable section

open PointedDecomposition LabelledCutJoin GlobalBridgeCut
open NumericalBridgeCut
open AllocationNormalization

variable {n h r m b : ℕ}

/-- Forget the local subtype proof and view a boundary dart of a packaged
component as an ambient dart. -/
def MatchingNormalizationInput.boundaryAmbient
    (x : MatchingNormalizationInput n h r)
    (z : x.pairing.Boundary) : Dart n h :=
  includeDart x.cells z.1

/-- Transporting an entire matching-normalization package preserves the
underlying ambient boundary dart. -/
theorem MatchingNormalizationInput.boundaryAmbient_cast
    {x y : MatchingNormalizationInput n h r} (hxy : x = y)
    (z : x.pairing.Boundary) :
    x.boundaryAmbient z = y.boundaryAmbient
      (cast (congrArg (fun w : MatchingNormalizationInput n h r ↦
        w.pairing.Boundary) hxy) z) := by
  subst y
  rfl

/-- All input data for normalizing a boundary-labelled component. -/
structure LabelledNormalizationInput (n h r : ℕ) where
  cells : Set (Fin n)
  fintype : Fintype cells
  size : ℕ
  card_eq : @Fintype.card cells fintype = size
  boundaryCount : ℕ
  pairing : ColoredMatching
    (RestrictedDart (facets := fun _ : Fin n ↦ h) cells) r
  label : pairing.Boundary ≃ Fin boundaryCount

/-- Dependent extensionality for the complete labelled input package. -/
theorem LabelledNormalizationInput.ext
    {x y : LabelledNormalizationInput n h r}
    (hcells : x.cells = y.cells)
    (hfintype : HEq x.fintype y.fintype)
    (hsize : x.size = y.size)
    (hboundary : x.boundaryCount = y.boundaryCount)
    (hpairing : HEq x.pairing y.pairing)
    (hlabel : HEq x.label y.label) : x = y := by
  cases x with
  | mk X fX k hk a P L =>
    cases y with
    | mk Y fY l hl c Q K =>
      dsimp only at hcells hfintype hsize hboundary hpairing hlabel
      subst Y
      have hf : fX = fY := eq_of_heq hfintype
      subst fY
      subst l
      subst c
      have hPQ : P = Q := eq_of_heq hpairing
      subst Q
      have hLK : L = K := eq_of_heq hlabel
      subst K
      rfl

/-- Normalize both cell and boundary-label indices simultaneously. -/
def normalizeLabelledInput (x : LabelledNormalizationInput n h r) :
    Σ ka : ℕ × ℕ,
      BoundaryLabelledPairing (Dart ka.1 h) r ka.2 := by
  letI : Fintype x.cells := x.fintype
  exact ⟨(x.size, x.boundaryCount),
    componentBoundaryLabelledEquiv x.cells x.card_eq
      ⟨x.pairing, x.label⟩⟩

set_option maxHeartbeats 2000000 in
/-- Full left-component normalization, including the dependent boundary
label, recovers the stored numerical component exactly up to `HEq`. -/
theorem leftNumericalPairing_fromCoproduct
    (d : Coproduct n h r m b) :
    HEq (leftNumericalPairing (orientedCarrier (fromCoproduct d)))
      d.2.2.2.1.1.raw := by
  let C := orientedCarrier (fromCoproduct d)
  let S := leftCellSet d
  let PC := C.core.1.1.restrict C.leftCells
  let PD := (leftRestrictedPairing d).pairing
  have hS : C.leftCells = S := orientedCarrier_from_leftCells d
  have hP : HEq PC PD := orientedCarrier_from_leftRestriction d
  have hk : (leftCellAllocation C).card = d.1.1.card :=
    congrArg Finset.card (leftCellAllocation_orientedCarrier_from d)
  have hA : leftBoundaryLabels C = d.2.1.1 :=
    orientedCarrier_from_leftBoundaryLabels d
  have ha : (leftBoundaryLabels C).card = d.2.1.1.card :=
    congrArg Finset.card hA
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
  have hdom : PC.Boundary = PD.Boundary := by
    simpa only [xC, xD] using congrArg
      (fun w : MatchingNormalizationInput n h r ↦ w.pairing.Boundary) hx
  let LC : PC.Boundary ≃ Fin (leftBoundaryLabels C).card :=
    (leftBoundaryAllocationEquiv C).trans
      (finsetSubtypeEquivFin (leftBoundaryLabels C))
  let LD : PD.Boundary ≃ Fin d.2.1.1.card :=
    (leftRestrictedPairing d).label
  let eA : {i : Fin (m + 2) // i ∈ leftBoundaryLabels C} ≃
      {i : Fin (m + 2) // i ∈ d.2.1.1} :=
    Set.equivOfEq (by
      ext i
      exact Finset.ext_iff.mp hA i)
  let allocated : PC.Boundary ≃
      {i : Fin (m + 2) // i ∈ d.2.1.1} :=
    (leftBoundaryAllocationEquiv C).trans eA
  have hfe (x : PC.Boundary) :
      leftBoundaryLabelMap C x = (allocated x).1 := by
    rfl
  have hnum : HEq LC
      (allocated.trans (finsetSubtypeEquivFin d.2.1.1)) := by
    exact numericalLabel_heq_of_allocation d.2.1.1 allocated
      (leftBoundaryLabelMap C) (leftBoundaryLabelMap_injective C) hfe
  have hstored : HEq
      (allocated.trans (finsetSubtypeEquivFin d.2.1.1)) LD := by
    apply Equiv.heq_ext_of_forall hdom rfl
    intro x
    apply heq_of_eq
    apply (finsetSubtypeEquivFin d.2.1.1).symm.injective
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    apply Subtype.ext
    change leftBoundaryLabelMap C x =
      (leftAllocatedLabel d (cast hdom x)).1
    apply leftBoundaryLabelMap_fromCoproduct_of_include_eq d
    have hamb := MatchingNormalizationInput.boundaryAmbient_cast hx x
    simpa only [MatchingNormalizationInput.boundaryAmbient, xC, xD,
      PC, PD, C, S] using hamb
  have hL : HEq LC LD := hnum.trans hstored
  let yC : LabelledNormalizationInput n h r :=
    ⟨C.leftCells, fC, (leftCellAllocation C).card, hkC,
      (leftBoundaryLabels C).card, PC, LC⟩
  let yD : LabelledNormalizationInput n h r :=
    ⟨S, fD, d.1.1.card, hkD, d.2.1.1.card, PD, LD⟩
  have hy : yC = yD :=
    LabelledNormalizationInput.ext hS hf hk ha hP hL
  have hn := congrArg normalizeLabelledInput hy
  have hsnd : HEq (normalizeLabelledInput yC).2
      (normalizeLabelledInput yD).2 := (Sigma.ext_iff.mp hn).2
  have hleft : (normalizeLabelledInput yC).2 =
      leftNumericalPairing C := rfl
  have hright : (normalizeLabelledInput yD).2 =
      d.2.2.2.1.1.raw := by
    exact componentBoundaryLabelledEquiv_apply_symm_apply
      (r := r) (m := d.2.1.1.card) S (leftCellSet_card d)
      d.2.2.2.1.1.raw
  exact (heq_of_eq hleft.symm).trans <|
    hsnd.trans (heq_of_eq hright)

/-! ## Complementary boundary-block transport -/

universe u

theorem equivFin_cast_val {X Y : Type u}
    [fX : Fintype X] [fY : Fintype Y]
    (hXY : X = Y) (x : X) :
    (Fintype.equivFin Y (Equiv.cast hXY x)).val =
      (Fintype.equivFin X x).val := by
  subst Y
  have hf : fX = fY := Subsingleton.elim _ _
  subst fY
  rfl

def complementPredicateEq (B : Finset (Fin (m + 2))) :
    (fun i : Fin (m + 2) ↦ i ∉ B) =
      (fun i : Fin (m + 2) ↦ i ∈ Bᶜ) := by
  funext i
  apply propext
  simp

def complementSubtypeTypeEq (B : Finset (Fin (m + 2))) :
    {i : Fin (m + 2) // i ∉ B} = {i : Fin (m + 2) // i ∈ Bᶜ} :=
  congrArg Subtype (complementPredicateEq B)

theorem equivCast_congrArg_Subtype_val
    {α : Type u} {p q : α → Prop} (hpq : p = q) (x : Subtype p) :
    ((Equiv.cast (congrArg Subtype hpq)) x : Subtype q).1 = x.1 := by
  subst q
  rfl

@[simp]
theorem complementSubtypeCast_val (B : Finset (Fin (m + 2)))
    (x : {i : Fin (m + 2) // i ∉ B}) :
    ((Equiv.cast (complementSubtypeTypeEq B)) x).1 = x.1 := by
  exact equivCast_congrArg_Subtype_val (complementPredicateEq B) x

set_option maxHeartbeats 1000000 in
/-- The inverse construction's complementary allocation label, followed by
the canonical numerical labelling of the complement finset, is the original
stored numerical label. -/
theorem rightAllocatedLabel_normalizes
    (d : Coproduct n h r m b) :
    let eComp : {i : Fin (m + 2) // i ∉ d.2.1.1} ≃
        {i : Fin (m + 2) // i ∈ d.2.1.1ᶜ} :=
      Equiv.cast (complementSubtypeTypeEq d.2.1.1)
    HEq ((rightAllocatedLabel d).trans eComp |>.trans
      (finsetSubtypeEquivFin d.2.1.1ᶜ))
      (rightRestrictedPairing d).label := by
  dsimp only
  have hcard : d.2.1.1ᶜ.card = m + 2 - d.2.1.1.card := by
    rw [Finset.card_compl]
    simp
  have hnotcard : m + 2 - d.2.1.1.card =
      Fintype.card {i : Fin (m + 2) // i ∉ d.2.1.1} := by
    rw [card_complement]
    simp
  apply Equiv.heq_ext_of_forall rfl (congrArg Fin hcard)
  intro x
  apply (Fin.heq_ext_iff hcard).2
  simp only [Equiv.trans_apply, rightAllocatedLabel]
  change (Fintype.equivFin {i : Fin (m + 2) // i ∈ d.2.1.1ᶜ}
      (Equiv.cast (complementSubtypeTypeEq d.2.1.1)
        ((Fintype.equivFin {i : Fin (m + 2) // i ∉ d.2.1.1}).symm
          (Fin.cast hnotcard ((rightRestrictedPairing d).label x))))).val = _
  rw [equivFin_cast_val]
  simp

set_option maxHeartbeats 2000000 in
/-- Full right-component normalization, including the complementary
boundary-label allocation, recovers the stored numerical component. -/
theorem rightNumericalPairing_fromCoproduct
    (d : Coproduct n h r m b) :
    HEq (rightNumericalPairing (orientedCarrier (fromCoproduct d)))
      d.2.2.2.2.1.1.raw := by
  let C := orientedCarrier (fromCoproduct d)
  let S := rightCellSet d
  let PC := C.core.1.1.restrict C.rightCells
  let PD := (rightRestrictedPairing d).pairing
  have hS : C.rightCells = S := orientedCarrier_from_rightCells d
  have hP : HEq PC PD := orientedCarrier_from_rightRestriction d
  have hk : n - (leftCellAllocation C).card = n - d.1.1.card :=
    congrArg (fun k ↦ n - k)
      (congrArg Finset.card (leftCellAllocation_orientedCarrier_from d))
  have hleftA : leftBoundaryLabels C = d.2.1.1 :=
    orientedCarrier_from_leftBoundaryLabels d
  have hrightA : rightBoundaryLabels C = d.2.1.1ᶜ := by
    ext i
    constructor
    · intro hiR
      have hiL : i ∉ leftBoundaryLabels C := fun hiL ↦
        Finset.disjoint_left.mp (boundaryLabelAllocations_disjoint C)
          hiL hiR
      have hiB : i ∉ d.2.1.1 := by
        rw [← hleftA]
        exact hiL
      simpa using hiB
    · intro hiComp
      have hiL : i ∉ leftBoundaryLabels C := by
        rw [hleftA]
        simpa using hiComp
      have hiUnion : i ∈ leftBoundaryLabels C ∨
          i ∈ rightBoundaryLabels C := by
        have hi : i ∈ leftBoundaryLabels C ∪ rightBoundaryLabels C := by
          rw [boundaryLabelAllocations_cover]
          exact Finset.mem_univ i
        simpa only [Finset.mem_union] using hi
      exact hiUnion.resolve_left hiL
  have ha : m + 2 - (leftBoundaryLabels C).card =
      m + 2 - d.2.1.1.card :=
    congrArg (fun a ↦ m + 2 - a) (congrArg Finset.card hleftA)
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
  have hdom : PC.Boundary = PD.Boundary := by
    simpa only [xC, xD] using congrArg
      (fun w : MatchingNormalizationInput n h r ↦ w.pairing.Boundary) hx
  let L0C : PC.Boundary ≃ Fin (rightBoundaryLabels C).card :=
    (rightBoundaryAllocationEquiv C).trans
      (finsetSubtypeEquivFin (rightBoundaryLabels C))
  let LC : PC.Boundary ≃
      Fin (m + 2 - (leftBoundaryLabels C).card) :=
    L0C.trans (finCongr (rightBoundaryCard_eq_sub C))
  let LD : PD.Boundary ≃ Fin (m + 2 - d.2.1.1.card) :=
    (rightRestrictedPairing d).label
  let eA : {i : Fin (m + 2) // i ∈ rightBoundaryLabels C} ≃
      {i : Fin (m + 2) // i ∈ d.2.1.1ᶜ} :=
    Set.equivOfEq (by
      ext i
      exact Finset.ext_iff.mp hrightA i)
  let allocatedC : PC.Boundary ≃
      {i : Fin (m + 2) // i ∈ d.2.1.1ᶜ} :=
    (rightBoundaryAllocationEquiv C).trans eA
  let eComp : {i : Fin (m + 2) // i ∉ d.2.1.1} ≃
      {i : Fin (m + 2) // i ∈ d.2.1.1ᶜ} :=
    Equiv.cast (complementSubtypeTypeEq d.2.1.1)
  let allocatedD : PD.Boundary ≃
      {i : Fin (m + 2) // i ∈ d.2.1.1ᶜ} :=
    (rightAllocatedLabel d).trans eComp
  have hfe (x : PC.Boundary) :
      rightBoundaryLabelMap C x = (allocatedC x).1 := by
    rfl
  have hnum : HEq L0C
      (allocatedC.trans (finsetSubtypeEquivFin d.2.1.1ᶜ)) := by
    exact numericalLabel_heq_of_allocation d.2.1.1ᶜ allocatedC
      (rightBoundaryLabelMap C) (rightBoundaryLabelMap_injective C) hfe
  have hstored : HEq
      (allocatedC.trans (finsetSubtypeEquivFin d.2.1.1ᶜ))
      (allocatedD.trans (finsetSubtypeEquivFin d.2.1.1ᶜ)) := by
    apply Equiv.heq_ext_of_forall hdom rfl
    intro x
    apply heq_of_eq
    apply (finsetSubtypeEquivFin d.2.1.1ᶜ).symm.injective
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    apply Subtype.ext
    change rightBoundaryLabelMap C x =
      ((Equiv.cast (complementSubtypeTypeEq d.2.1.1))
        (rightAllocatedLabel d (cast hdom x))).1
    rw [complementSubtypeCast_val]
    apply rightBoundaryLabelMap_fromCoproduct_of_include_eq d
    have hamb := MatchingNormalizationInput.boundaryAmbient_cast hx x
    simpa only [MatchingNormalizationInput.boundaryAmbient, xC, xD,
      PC, PD, C, S] using hamb
  have hD : HEq
      (allocatedD.trans (finsetSubtypeEquivFin d.2.1.1ᶜ)) LD := by
    exact rightAllocatedLabel_normalizes d
  have h0D : HEq L0C LD := hnum.trans (hstored.trans hD)
  have hC0 : HEq LC L0C := by
    apply Equiv.heq_ext_of_forall rfl
      (congrArg Fin (rightBoundaryCard_eq_sub C).symm)
    intro x
    apply (Fin.heq_ext_iff (rightBoundaryCard_eq_sub C).symm).2
    rfl
  have hL : HEq LC LD := hC0.trans h0D
  let yC : LabelledNormalizationInput n h r :=
    ⟨C.rightCells, fC, n - (leftCellAllocation C).card, hkC,
      m + 2 - (leftBoundaryLabels C).card, PC, LC⟩
  let yD : LabelledNormalizationInput n h r :=
    ⟨S, fD, n - d.1.1.card, hkD,
      m + 2 - d.2.1.1.card, PD, LD⟩
  have hy : yC = yD :=
    LabelledNormalizationInput.ext hS hf hk ha hP hL
  have hn := congrArg normalizeLabelledInput hy
  have hsnd : HEq (normalizeLabelledInput yC).2
      (normalizeLabelledInput yD).2 := (Sigma.ext_iff.mp hn).2
  have hleft : (normalizeLabelledInput yC).2 =
      rightNumericalPairing C := rfl
  have hright : (normalizeLabelledInput yD).2 =
      d.2.2.2.2.1.1.raw := by
    exact componentBoundaryLabelledEquiv_apply_symm_apply
      (r := r) (m := m + 2 - d.2.1.1.card) S (rightCellSet_card d)
      d.2.2.2.2.1.1.raw
  exact (heq_of_eq hleft.symm).trans <|
    hsnd.trans (heq_of_eq hright)


end
end UnrootedBridgeCoproduct
end FacetPairing
end PolytopeCounting
