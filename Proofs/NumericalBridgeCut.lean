module

public import Proofs.GlobalBridgeCut
public import Proofs.LabelledReindexing

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Numerical bridge cut data

This isolated development turns the literal component subtypes produced by
`GlobalBridgeCut` into standard `Fin k` component types, while retaining the
cell and boundary-label allocations needed for an exact inverse.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace NumericalBridgeCut

noncomputable section

open PointedDecomposition LabelledCutJoin GlobalBridgeCut

universe uD

variable {D : Type uD} [Fintype D] [DecidableEq D]

theorem cutBoundaryLabel_leftEndpoint
    (M : PartialMatching D) (e : M.Seam)
    (label : M.Boundary ≃ Fin m) :
    M.cutBoundaryLabel e label (M.leftBoundaryAfterErase e) =
      firstStar m := by
  have hocc : e.1.out.1 ∈ M.occupied :=
    (M.mem_occupied_iff _).mpr
      ⟨e.1, e.2, Sym2.out_fst_mem e.1⟩
  have hnot : ¬ e.1.out.1 ∉ M.occupied := not_not.mpr hocc
  simp only [PartialMatching.cutBoundaryLabel,
    PartialMatching.boundaryEraseEquiv,
    PartialMatching.leftBoundaryAfterErase,
    PartialMatching.endpointBoundaryAfterErase,
    Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply,
    subtypeOrEquiv, subtypeOrEquiv_apply, Equiv.coe_fn_mk,
    Set.equivOfEq_apply]
  rw [subtypeOrLeftEmbedding_apply_right _ hnot]
  change Fin.natAdd m (finTwoEquiv.symm
    (if e.1.out.1 = e.1.out.1 then false else true)) = firstStar m
  rw [if_pos rfl]
  rfl

theorem cutBoundaryLabel_rightEndpoint
    (M : PartialMatching D) (e : M.Seam)
    (label : M.Boundary ≃ Fin m) :
    M.cutBoundaryLabel e label (M.rightBoundaryAfterErase e) =
      secondStar m := by
  have hocc : e.1.out.2 ∈ M.occupied :=
    (M.mem_occupied_iff _).mpr
      ⟨e.1, e.2, Sym2.out_snd_mem e.1⟩
  have hnot : ¬ e.1.out.2 ∉ M.occupied := not_not.mpr hocc
  simp only [PartialMatching.cutBoundaryLabel,
    PartialMatching.boundaryEraseEquiv,
    PartialMatching.rightBoundaryAfterErase,
    PartialMatching.endpointBoundaryAfterErase,
    Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply,
    subtypeOrEquiv, subtypeOrEquiv_apply, Equiv.coe_fn_mk,
    Set.equivOfEq_apply]
  rw [subtypeOrLeftEmbedding_apply_right _ hnot]
  have hne := M.exposed_endpoints_ne e
  change e.1.out.1 ≠ e.1.out.2 at hne
  change Fin.natAdd m (finTwoEquiv.symm
    (if e.1.out.2 = e.1.out.1 then false else true)) = secondStar m
  rw [if_neg hne.symm]
  rfl


/-! ## Connectivity survives canonical component reindexing -/

theorem componentAdjacent_iff
    {n h k r : ℕ} (S : Set (Fin n)) [Fintype S]
    (hcard : Fintype.card S = k)
    (P : ColoredMatching
      (RestrictedDart (facets := fun _ : Fin n ↦ h) S) r)
    (u v : Fin k) :
    (componentColoredMatchingEquiv S hcard P).Adjacent (fun _ : Fin k ↦ h) u v ↔
      P.Adjacent (fun _ : S ↦ h)
        ((componentCellEquiv S hcard).symm u)
        ((componentCellEquiv S hcard).symm v) := by
  have hdart (w : Fin k) (i : Fin h) :
      componentDartEquiv S hcard
          ⟨(componentCellEquiv S hcard).symm w, i⟩ =
        (⟨w, i⟩ : Dart k h) := by
    apply Sigma.ext
    · exact (componentCellEquiv S hcard).apply_symm_apply w
    · simp
  constructor
  · rintro ⟨i, j, hij⟩
    refine ⟨i, j, ?_⟩
    change s(⟨u, i⟩, ⟨v, j⟩) ∈
      P.matching.seams.map
        ⟨Sym2.map (componentDartEquiv S hcard),
          Sym2.map.injective (componentDartEquiv S hcard).injective⟩ at hij
    obtain ⟨old, hold, hmap⟩ := Finset.mem_map.mp hij
    change Sym2.map (componentDartEquiv S hcard) old =
      s(⟨u, i⟩, ⟨v, j⟩) at hmap
    have holdEq : old =
        s(⟨(componentCellEquiv S hcard).symm u, i⟩,
          ⟨(componentCellEquiv S hcard).symm v, j⟩) := by
      apply Sym2.map.injective (componentDartEquiv S hcard).injective
      rw [hmap]
      rw [Sym2.map_mk, hdart, hdart]
    simpa only [holdEq] using hold
  · rintro ⟨i, j, hij⟩
    refine ⟨i, j, ?_⟩
    change s(⟨u, i⟩, ⟨v, j⟩) ∈
      P.matching.seams.map
        ⟨Sym2.map (componentDartEquiv S hcard),
          Sym2.map.injective (componentDartEquiv S hcard).injective⟩
    apply Finset.mem_map.mpr
    refine ⟨s(⟨(componentCellEquiv S hcard).symm u, i⟩,
      ⟨(componentCellEquiv S hcard).symm v, j⟩), hij, ?_⟩
    change Sym2.map (componentDartEquiv S hcard)
      s(⟨(componentCellEquiv S hcard).symm u, i⟩,
        ⟨(componentCellEquiv S hcard).symm v, j⟩) = _
    rw [Sym2.map_mk, hdart, hdart]

theorem componentReindex_connected
    {n h k r : ℕ} (S : Set (Fin n)) [Fintype S]
    (hcard : Fintype.card S = k)
    (P : ColoredMatching
      (RestrictedDart (facets := fun _ : Fin n ↦ h) S) r)
    (hconnected : P.IsConnected (fun _ : S ↦ h)) :
    (componentColoredMatchingEquiv S hcard P).IsConnected
      (fun _ : Fin k ↦ h) := by
  intro u v
  have hpath := hconnected
    ((componentCellEquiv S hcard).symm u)
    ((componentCellEquiv S hcard).symm v)
  have hmapped := Relation.ReflTransGen.lift
    (componentCellEquiv S hcard)
    (fun a b hab ↦ by
      apply (componentAdjacent_iff S hcard P _ _).mpr
      simpa using hab)
    _ _ hpath
  simpa [Function.onFun] using hmapped

@[simp]
theorem componentReindex_seam_card
    {n h k r : ℕ} (S : Set (Fin n)) [Fintype S]
    (hcard : Fintype.card S = k)
    (P : ColoredMatching
      (RestrictedDart (facets := fun _ : Fin n ↦ h) S) r) :
    (componentColoredMatchingEquiv S hcard P).matching.seams.card =
      P.matching.seams.card := by
  exact Finset.card_map _


/-! ## The finite allocation of cut-boundary labels -/

variable {n h r m b : ℕ}

noncomputable local instance finiteSetFintype (S : Set (Fin n)) : Fintype S :=
  Fintype.ofFinite S

abbrev Carrier := UnrootedBridgeCutCarrier n h r m b

def leftBoundaryLabelMap (C : Carrier (n := n) (h := h) (r := r)
    (m := m) (b := b))
    (x : (C.core.1.1.restrict C.leftCells).Boundary) : Fin (m + 2) :=
  C.componentBoundaryLabel (Sum.inl x)

def rightBoundaryLabelMap (C : Carrier (n := n) (h := h) (r := r)
    (m := m) (b := b))
    (x : (C.core.1.1.restrict C.rightCells).Boundary) : Fin (m + 2) :=
  C.componentBoundaryLabel (Sum.inr x)

theorem leftBoundaryLabelMap_injective
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    Function.Injective (leftBoundaryLabelMap C) := by
  intro x y hxy
  have hsum : (Sum.inl x :
      (C.core.1.1.restrict C.leftCells).Boundary ⊕
        (C.core.1.1.restrict C.rightCells).Boundary) = Sum.inl y :=
    C.componentBoundaryLabel.injective hxy
  exact Sum.inl_injective hsum

theorem rightBoundaryLabelMap_injective
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    Function.Injective (rightBoundaryLabelMap C) := by
  intro x y hxy
  have hsum : (Sum.inr x :
      (C.core.1.1.restrict C.leftCells).Boundary ⊕
        (C.core.1.1.restrict C.rightCells).Boundary) = Sum.inr y :=
    C.componentBoundaryLabel.injective hxy
  exact Sum.inr_injective hsum

def leftBoundaryLabels
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    Finset (Fin (m + 2)) :=
  Finset.univ.image (leftBoundaryLabelMap C)

def rightBoundaryLabels
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    Finset (Fin (m + 2)) :=
  Finset.univ.image (rightBoundaryLabelMap C)

@[simp]
theorem mem_leftBoundaryLabels_iff
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b))
    (i : Fin (m + 2)) :
    i ∈ leftBoundaryLabels C ↔ ∃ x, leftBoundaryLabelMap C x = i := by
  constructor
  · intro hi
    obtain ⟨x, _hx, hxi⟩ := Finset.mem_image.mp hi
    exact ⟨x, hxi⟩
  · rintro ⟨x, rfl⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

@[simp]
theorem mem_rightBoundaryLabels_iff
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b))
    (i : Fin (m + 2)) :
    i ∈ rightBoundaryLabels C ↔ ∃ x, rightBoundaryLabelMap C x = i := by
  constructor
  · intro hi
    obtain ⟨x, _hx, hxi⟩ := Finset.mem_image.mp hi
    exact ⟨x, hxi⟩
  · rintro ⟨x, rfl⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

theorem boundaryLabelAllocations_disjoint
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    Disjoint (leftBoundaryLabels C) (rightBoundaryLabels C) := by
  rw [Finset.disjoint_left]
  intro i hiL hiR
  obtain ⟨x, hx⟩ := (mem_leftBoundaryLabels_iff C i).mp hiL
  obtain ⟨y, hy⟩ := (mem_rightBoundaryLabels_iff C i).mp hiR
  have hsum : (Sum.inl x :
      (C.core.1.1.restrict C.leftCells).Boundary ⊕
        (C.core.1.1.restrict C.rightCells).Boundary) = Sum.inr y := by
    apply C.componentBoundaryLabel.injective
    exact hx.trans hy.symm
  cases hsum

theorem boundaryLabelAllocations_cover
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    leftBoundaryLabels C ∪ rightBoundaryLabels C = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  let z := C.componentBoundaryLabel.symm i
  cases hz : z with
  | inl x =>
      apply Finset.mem_union_left
      apply (mem_leftBoundaryLabels_iff C i).mpr
      refine ⟨x, ?_⟩
      change C.componentBoundaryLabel (Sum.inl x) = i
      rw [← hz]
      exact C.componentBoundaryLabel.apply_symm_apply i
  | inr y =>
      apply Finset.mem_union_right
      apply (mem_rightBoundaryLabels_iff C i).mpr
      refine ⟨y, ?_⟩
      change C.componentBoundaryLabel (Sum.inr y) = i
      rw [← hz]
      exact C.componentBoundaryLabel.apply_symm_apply i

theorem boundaryLabelAllocation_cards_add
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    (leftBoundaryLabels C).card + (rightBoundaryLabels C).card = m + 2 := by
  rw [← Finset.card_union_of_disjoint (boundaryLabelAllocations_disjoint C),
    boundaryLabelAllocations_cover]
  simp

def equivFinsetImage {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) :
    α ≃ {y : β // y ∈ Finset.univ.image f} :=
  (Equiv.ofInjective f hf).trans (Set.equivOfEq (by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    · intro hy
      obtain ⟨x, _hx, hxy⟩ := Finset.mem_image.mp hy
      exact ⟨x, hxy⟩))

def finsetSubtypeEquivFin {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) : {x : α // x ∈ A} ≃ Fin A.card :=
  (Fintype.equivFin {x : α // x ∈ A}).trans
    (finCongr (Fintype.card_coe A))

def leftBoundaryAllocationEquiv
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    (C.core.1.1.restrict C.leftCells).Boundary ≃
      {i : Fin (m + 2) // i ∈ leftBoundaryLabels C} :=
  equivFinsetImage (leftBoundaryLabelMap C)
    (leftBoundaryLabelMap_injective C)

def rightBoundaryAllocationEquiv
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    (C.core.1.1.restrict C.rightCells).Boundary ≃
      {i : Fin (m + 2) // i ∈ rightBoundaryLabels C} :=
  equivFinsetImage (rightBoundaryLabelMap C)
    (rightBoundaryLabelMap_injective C)


/-! ## Standard `Fin k` components -/

def leftCellAllocation
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    Finset (Fin n) :=
  C.leftCells.toFinset

def rightCellAllocation
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    Finset (Fin n) :=
  C.rightCells.toFinset

theorem carrierCellAllocation_cards_add
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    (leftCellAllocation C).card + (rightCellAllocation C).card = n := by
  classical
  let e : C.leftCells ⊕ C.rightCells ≃ Fin n :=
    (Equiv.Set.union C.disjoint).symm.trans <|
      (Set.equivOfEq C.cover).trans (Equiv.Set.univ (Fin n))
  have hcard := Fintype.card_congr e
  rw [Fintype.card_sum] at hcard
  simpa only [leftCellAllocation, rightCellAllocation,
    Set.toFinset_card, Fintype.card_fin] using hcard

theorem rightCellCard_eq_sub
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    Fintype.card C.rightCells = n - (leftCellAllocation C).card := by
  have hsum := carrierCellAllocation_cards_add C
  rw [rightCellAllocation, Set.toFinset_card] at hsum
  omega

theorem rightBoundaryCard_eq_sub
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    (rightBoundaryLabels C).card = m + 2 - (leftBoundaryLabels C).card := by
  have hsum := boundaryLabelAllocation_cards_add C
  omega

def leftNumericalPairing
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    BoundaryLabelledPairing
      (Dart (leftCellAllocation C).card h) r
      (leftBoundaryLabels C).card := by
  let P := C.core.1.1.restrict C.leftCells
  let hcard : Fintype.card C.leftCells = (leftCellAllocation C).card := by
    exact (Set.toFinset_card C.leftCells).symm
  let e := componentDartEquiv (h := h) C.leftCells hcard
  exact
    { pairing := componentColoredMatchingEquiv (h := h) C.leftCells hcard P
      label := (P.matching.boundaryReindexEquiv e).symm |>.trans <|
        (leftBoundaryAllocationEquiv C).trans
          (finsetSubtypeEquivFin (leftBoundaryLabels C)) }

def rightNumericalPairing
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    BoundaryLabelledPairing
      (Dart (n - (leftCellAllocation C).card) h) r
      (m + 2 - (leftBoundaryLabels C).card) := by
  let P := C.core.1.1.restrict C.rightCells
  let hcard : Fintype.card C.rightCells =
      n - (leftCellAllocation C).card := rightCellCard_eq_sub C
  let e := componentDartEquiv (h := h) C.rightCells hcard
  let hlabels : (rightBoundaryLabels C).card =
      m + 2 - (leftBoundaryLabels C).card := rightBoundaryCard_eq_sub C
  exact
    { pairing := componentColoredMatchingEquiv (h := h) C.rightCells hcard P
      label := (P.matching.boundaryReindexEquiv e).symm |>.trans <|
        (rightBoundaryAllocationEquiv C).trans <|
          (finsetSubtypeEquivFin (rightBoundaryLabels C)).trans
            (finCongr hlabels) }

@[simp]
theorem leftNumericalPairing_pairing
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    (leftNumericalPairing C).pairing =
      componentColoredMatchingEquiv C.leftCells
        (h := h)
        (Set.toFinset_card C.leftCells).symm
        (C.core.1.1.restrict C.leftCells) := rfl

@[simp]
theorem rightNumericalPairing_pairing
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    (rightNumericalPairing C).pairing =
      componentColoredMatchingEquiv C.rightCells
        (h := h)
        (rightCellCard_eq_sub C)
        (C.core.1.1.restrict C.rightCells) := rfl

def leftNumericalDiagram
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    UnrootedDiagram (leftCellAllocation C).card h r
      (leftBoundaryLabels C).card where
  raw := leftNumericalPairing C
  connected := by
    rw [leftNumericalPairing_pairing]
    exact componentReindex_connected C.leftCells
      (Set.toFinset_card C.leftCells).symm _ C.leftConnected

def rightNumericalDiagram
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    UnrootedDiagram (n - (leftCellAllocation C).card) h r
      (m + 2 - (leftBoundaryLabels C).card) where
  raw := rightNumericalPairing C
  connected := by
    rw [rightNumericalPairing_pairing]
    exact componentReindex_connected C.rightCells
      (rightCellCard_eq_sub C) _ C.rightConnected

def leftNumericalStratum
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    UnrootedStratum (leftCellAllocation C).card h r
      (leftBoundaryLabels C).card C.leftRank := by
  refine ⟨leftNumericalDiagram C, ?_⟩
  unfold ConnectedDiagram.HasCircuitRank ConnectedDiagram.edgeCount
  change (leftNumericalPairing C).pairing.matching.seams.card + 1 =
    Fintype.card (Fin (leftCellAllocation C).card) + C.leftRank
  rw [leftNumericalPairing_pairing]
  change (componentColoredMatchingEquiv C.leftCells _
      (C.core.1.1.restrict C.leftCells)).matching.seams.card + 1 =
    Fintype.card (Fin (leftCellAllocation C).card) + C.leftRank
  rw [componentReindex_seam_card, Fintype.card_fin]
  calc
    (C.core.1.1.restrict C.leftCells).matching.seams.card + 1 =
        Nat.card C.leftCells + C.leftRank := C.leftRank_spec
    _ = (leftCellAllocation C).card + C.leftRank := by
      rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
      rfl

def rightNumericalStratum
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    UnrootedStratum (n - (leftCellAllocation C).card) h r
      (m + 2 - (leftBoundaryLabels C).card) C.rightRank := by
  refine ⟨rightNumericalDiagram C, ?_⟩
  unfold ConnectedDiagram.HasCircuitRank ConnectedDiagram.edgeCount
  change (rightNumericalPairing C).pairing.matching.seams.card + 1 =
    Fintype.card (Fin (n - (leftCellAllocation C).card)) + C.rightRank
  rw [rightNumericalPairing_pairing]
  change (componentColoredMatchingEquiv C.rightCells _
      (C.core.1.1.restrict C.rightCells)).matching.seams.card + 1 =
    Fintype.card (Fin (n - (leftCellAllocation C).card)) + C.rightRank
  rw [componentReindex_seam_card, Fintype.card_fin]
  rw [← rightCellCard_eq_sub C]
  simpa only [Nat.card_eq_fintype_card] using C.rightRank_spec


/-! ## The numerical unrooted bridge coproduct -/

/-- Explicit numerical bridge data.  The two indices are literally
`k = cellAllocation.card` and `n-k`; the boundary indices are literally
`a = boundaryAllocation.card` and `m+2-a`.  Thus this is a dependent
coproduct over cell allocations, boundary-label allocations and the two
component circuit ranks, rather than a carrier with anonymous subtype
cardinalities. -/
structure NumericalUnrootedBridgeDatum (n h r m b : ℕ) where
  cellAllocation : Finset (Fin n)
  leftCells_nonempty : 0 < cellAllocation.card
  rightCells_nonempty : cellAllocation.card < n
  boundaryAllocation : Finset (Fin (m + 2))
  leftBoundary_nonempty : 0 < boundaryAllocation.card
  rightBoundary_nonempty : boundaryAllocation.card < m + 2
  leftRank : ℕ
  rightRank : ℕ
  ranks_add : leftRank + rightRank = b
  leftComponent :
    UnrootedStratum cellAllocation.card h r boundaryAllocation.card leftRank
  rightComponent :
    UnrootedStratum (n - cellAllocation.card) h r
      (m + 2 - boundaryAllocation.card) rightRank
  deletedColor : Fin r

theorem leftCellAllocation_card_pos
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    0 < (leftCellAllocation C).card := by
  rw [leftCellAllocation, Set.toFinset_card]
  exact Fintype.card_pos_iff.mpr
    ⟨⟨C.leftStar.1.1.1, C.leftStar.1.1.2⟩⟩

theorem leftCellAllocation_card_lt
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    (leftCellAllocation C).card < n := by
  have hsum := carrierCellAllocation_cards_add C
  have hright : 0 < (rightCellAllocation C).card := by
    rw [rightCellAllocation, Set.toFinset_card]
    exact Fintype.card_pos_iff.mpr
      ⟨⟨C.rightStar.1.1.1, C.rightStar.1.1.2⟩⟩
  omega

theorem leftBoundaryAllocation_card_pos
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    0 < (leftBoundaryLabels C).card := by
  exact Finset.card_pos.mpr ⟨leftBoundaryLabelMap C C.leftStar,
    (mem_leftBoundaryLabels_iff C _).mpr ⟨C.leftStar, rfl⟩⟩

theorem leftBoundaryAllocation_card_lt
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    (leftBoundaryLabels C).card < m + 2 := by
  have hsum := boundaryLabelAllocation_cards_add C
  have hright : 0 < (rightBoundaryLabels C).card :=
    Finset.card_pos.mpr ⟨rightBoundaryLabelMap C C.rightStar,
      (mem_rightBoundaryLabels_iff C _).mpr ⟨C.rightStar, rfl⟩⟩
  omega

/-- Forget only the literal subtype presentation of a bridge carrier:
all cells, boundary labels, ranks, components and the seam colour are now
stored in numerical standard types. -/
def numericalDatumOfCarrier
    (C : Carrier (n := n) (h := h) (r := r) (m := m) (b := b)) :
    NumericalUnrootedBridgeDatum n h r m b where
  cellAllocation := leftCellAllocation C
  leftCells_nonempty := leftCellAllocation_card_pos C
  rightCells_nonempty := leftCellAllocation_card_lt C
  boundaryAllocation := leftBoundaryLabels C
  leftBoundary_nonempty := leftBoundaryAllocation_card_pos C
  rightBoundary_nonempty := leftBoundaryAllocation_card_lt C
  leftRank := C.leftRank
  rightRank := C.rightRank
  ranks_add := C.ranks_add
  leftComponent := leftNumericalStratum C
  rightComponent := rightNumericalStratum C
  deletedColor := C.deletedColor

/-- Concrete forward map from an oriented marked unrooted bridge to the
explicit numerical coproduct. -/
def cutBridgeNumerical
    (z : UnrootedBridgePointed n h r m b × Bool) :
    NumericalUnrootedBridgeDatum n h r m b :=
  numericalDatumOfCarrier (cutBridge z)

@[simp]
theorem cutBridgeNumerical_ranks_add
    (z : UnrootedBridgePointed n h r m b × Bool) :
    (cutBridgeNumerical z).leftRank + (cutBridgeNumerical z).rightRank = b :=
  (cutBridgeNumerical z).ranks_add

@[simp]
theorem cutBridgeNumerical_deletedColor
    (z : UnrootedBridgePointed n h r m b × Bool) :
    (cutBridgeNumerical z).deletedColor =
      (cutBridge z).core.1.2.color := by
  exact (cutBridge z).deletedColor_eq


end
end NumericalBridgeCut
end FacetPairing
end PolytopeCounting
