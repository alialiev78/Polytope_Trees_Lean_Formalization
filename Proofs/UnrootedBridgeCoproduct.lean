module

public import Proofs.GlobalBridgeCardinality
public import Proofs.StarAllocation
public import Proofs.ColoredRawCutJoin
public import Proofs.NonbridgeExact
public import Proofs.StarJoinLabelCoherence
public import Proofs.AllocationNormalization

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# The numerical coproduct for the unrooted bridge branch

The Boolean orientation on a marked bridge orders its two components.  We
use that ordering to put the chosen endpoint in the left component and use
the *oriented* boundary cut, so the chosen endpoint always receives the
first star label and the opposite endpoint the second.  This avoids the
noncanonical factor-two bijection used in the nonbridge branch.

The target below is a genuine finite dependent coproduct.  Its two component
objects live on independent standard cell types `Fin k` and `Fin (n-k)`;
their boundary labels live on independent numerical blocks of sizes `a` and
`m+2-a`.  The allocation finsets remember how to put both cell and boundary
blocks back into the ambient labelled object.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace UnrootedBridgeCoproduct

noncomputable section

open PointedDecomposition LabelledCutJoin GlobalBridgeCut
open NumericalBridgeCut

/-! ## Finite index types -/

/-- A proper nonempty ordered left block of the `n` ambient cells. -/
abbrev CellAllocation (n : ℕ) :=
  {A : Finset (Fin n) // 0 < A.card ∧ A.card < n}

/-- A proper boundary block containing the chosen (first) star but not the
opposite (second) star.  This is the endpoint-exchange bookkeeping: the
left component is precisely the component containing `firstStar m`. -/
abbrev BoundaryAllocation (m : ℕ) :=
  {A : Finset (Fin (m + 2)) //
    firstStar m ∈ A ∧ secondStar m ∉ A}

/-- A finite ordered split of circuit rank `b`. -/
abbrev RankSplit (b : ℕ) :=
  {q : Fin (b + 1) × Fin (b + 1) // q.1.1 + q.2.1 = b}

/-- The desired numerical bridge coproduct.  It is a nested dependent sum,
not a realized-range subtype: after choosing the allocations and rank split,
the two connected component strata are independent. -/
abbrev Coproduct (n h r m b : ℕ) :=
  Σ A : CellAllocation n,
    Σ B : BoundaryAllocation m,
      Σ q : RankSplit b,
        UnrootedStratum A.1.card h r B.1.card q.1.1 ×
          UnrootedStratum (n - A.1.card) h r
            (m + 2 - B.1.card) q.1.2.1 × Fin r

noncomputable instance coproductFintype (n h r m b : ℕ) :
    Fintype (Coproduct n h r m b) := Fintype.ofFinite _

/-! ## Complements as explicit equivalences -/

/-- A finset and its complement form an explicit disjoint sum decomposition
of a finite ambient type. -/
def finsetSumComplementEquiv {X : Type*} [Fintype X] [DecidableEq X]
    (A : Finset X) :
    {x : X // x ∈ A} ⊕ {x : X // x ∉ A} ≃ X where
  toFun z := z.elim Subtype.val Subtype.val
  invFun x := if hx : x ∈ A then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, hx⟩
  left_inv z := by
    rcases z with x | x
    · simp [x.2]
    · simp [x.2]
  right_inv x := by
    by_cases hx : x ∈ A <;> simp [hx]

/-- Cardinality of the complementary block. -/
theorem card_complement {X : Type*} [Fintype X] [DecidableEq X]
    (A : Finset X) :
    Fintype.card {x : X // x ∉ A} = Fintype.card X - A.card := by
  have h := Fintype.card_congr (finsetSumComplementEquiv A)
  rw [Fintype.card_sum, Fintype.card_coe] at h
  omega

/-- Canonical numerical labelling of the complementary boundary block. -/
def complementEquivFin {X : Type*} [Fintype X] [DecidableEq X]
    (A : Finset X) :
    {x : X // x ∉ A} ≃ Fin (Fintype.card X - A.card) :=
  (Fintype.equivFin {x : X // x ∉ A}).trans
    (finCongr (card_complement A))

/-! ## Oriented cutting and its component carrier -/

/-- The endpoint selected by the source Boolean. -/
def selectedEndpoint
    (z : UnrootedBridgePointed n h r m b × Bool) :
    {d : Dart n h // d ∈ z.1.1.2.1} :=
  (z.1.1.1.1.raw.pairing.matching.seamEndpointEquivBool z.1.1.2).symm z.2

/-- Flat oriented coloured matching associated to an oriented bridge point. -/
def orientedMarked
    (z : UnrootedBridgePointed n h r m b × Bool) :
    OrientedMarkedColored (Dart n h) r where
  pairing := z.1.1.1.1.raw.pairing
  seam := z.1.1.2.1
  seam_mem := z.1.1.2.2
  first := (selectedEndpoint z).1
  first_mem := (selectedEndpoint z).2

/-- The dependent partial-matching orientation underlying `orientedMarked`. -/
def orientedSeam
    (z : UnrootedBridgePointed n h r m b × Bool) :
    (orientedMarked z).pairing.matching.OrientedSeam :=
  ⟨(orientedMarked z).seamSubtype,
    ⟨(orientedMarked z).first, (orientedMarked z).first_mem⟩⟩

/-- Full boundary labelling after cutting with the selected endpoint first. -/
def orientedCutLabel
    (z : UnrootedBridgePointed n h r m b × Bool) :
    ((orientedMarked z).pairing.erase (orientedMarked z).seamSubtype).Boundary
      ≃ Fin (m + 2) :=
  (orientedMarked z).pairing.matching.orientedCutBoundaryLabel
    (orientedSeam z) z.1.1.1.1.raw.label

/-- Exchange the two star names and leave every old boundary name fixed. -/
def starSwap (m : ℕ) : Equiv.Perm (Fin (m + 2)) :=
  Equiv.swap (firstStar m) (secondStar m)

/-- Replace only the boundary allocation in `cutBridge` by the oriented cut
allocation.  The canonical cut calls the `Sym2.out.1` end `firstStar`.
When the source orientation chooses the other end, postcomposing by
`starSwap` makes the chosen (left) endpoint `firstStar` again.  All bridge
partition, connectedness, rank, colour and exact reassembly fields are
inherited unchanged from the lossless global carrier. -/
def orientedCarrier
    (z : UnrootedBridgePointed n h r m b × Bool) :
    UnrootedBridgeCutCarrier n h r m b := by
  let C := cutBridge z
  have hcut : C.core.1.1 =
      (orientedMarked z).pairing.erase (orientedMarked z).seamSubtype := by
    rcases z with ⟨⟨⟨P, e⟩, hbridge⟩, o⟩
    cases o <;> rfl
  exact { C with
    componentBoundaryLabel :=
      (boundaryReassembleEquiv C.leftCells C.rightCells C.cover C.disjoint
        (C.core.1.1.restrict C.leftCells)
        (C.core.1.1.restrict C.rightCells)).symm |>.trans <|
        (boundaryEquivOfEq C.reassemble_exact).trans <|
          (boundaryEquivOfEq hcut).trans (orientedCutLabel z) }

/-! The following endpoint facts are stated separately because they are the
only coherence needed between endpoint orientation and numerical boundary
allocation. -/

theorem orientedCutBoundaryLabel_first
    {D : Type*} [DecidableEq D]
    (M : PartialMatching D) (o : M.OrientedSeam)
    (label : M.Boundary ≃ Fin m) :
    M.orientedCutBoundaryLabel o label
      (M.endpointBoundaryAfterErase o.1 o.2.1 o.2.2) = firstStar m := by
  have hocc : o.2.1 ∈ M.occupied :=
    (M.mem_occupied_iff _).mpr ⟨o.1.1, o.1.2, o.2.2⟩
  have hnot : ¬ o.2.1 ∉ M.occupied := not_not.mpr hocc
  simp only [PartialMatching.orientedCutBoundaryLabel,
    PartialMatching.orientedBoundaryEraseEquiv,
    PartialMatching.endpointBoundaryAfterErase,
    Equiv.trans_apply, Equiv.sumCongr_apply, subtypeOrEquiv,
    Equiv.coe_fn_mk, Set.equivOfEq_apply]
  rw [subtypeOrLeftEmbedding_apply_right _ hnot]
  change Fin.natAdd m (finTwoEquiv.symm
    (if o.2.1 = o.2.1 then false else true)) = firstStar m
  rw [if_pos rfl]
  rfl

theorem orientedCutBoundaryLabel_second
    {D : Type*} [DecidableEq D]
    (M : PartialMatching D) (o : M.OrientedSeam)
    (label : M.Boundary ≃ Fin m) :
    M.orientedCutBoundaryLabel o label
      (M.endpointBoundaryAfterErase o.1 (M.otherEndpoint o)
        (M.otherEndpoint_mem o)) = secondStar m := by
  have hocc : M.otherEndpoint o ∈ M.occupied :=
    (M.mem_occupied_iff _).mpr
      ⟨o.1.1, o.1.2, M.otherEndpoint_mem o⟩
  have hnot : ¬ M.otherEndpoint o ∉ M.occupied := not_not.mpr hocc
  simp only [PartialMatching.orientedCutBoundaryLabel,
    PartialMatching.orientedBoundaryEraseEquiv,
    PartialMatching.endpointBoundaryAfterErase,
    Equiv.trans_apply, Equiv.sumCongr_apply, subtypeOrEquiv,
    Equiv.coe_fn_mk, Set.equivOfEq_apply]
  rw [subtypeOrLeftEmbedding_apply_right _ hnot]
  change Fin.natAdd m (finTwoEquiv.symm
    (if M.otherEndpoint o = o.2.1 then false else true)) = secondStar m
  rw [if_neg (M.oriented_endpoints_ne o).symm]
  rfl

/-! ## Forward normalization -/

theorem otherEndpoint_out_fst
    {D : Type*} [DecidableEq D]
    (M : PartialMatching D) (e : M.Seam) :
    Sym2.Mem.other' (Sym2.out_fst_mem e.1) = e.1.out.2 := by
  apply Sym2.congr_right.mp
  calc
    s(e.1.out.1, Sym2.Mem.other' (Sym2.out_fst_mem e.1)) = e.1 :=
      Sym2.other_spec' _
    _ = s(e.1.out.1, e.1.out.2) := by
      symm
      rw [Sym2.mk, e.1.out_eq]

theorem otherEndpoint_out_snd
    {D : Type*} [DecidableEq D]
    (M : PartialMatching D) (e : M.Seam) :
    Sym2.Mem.other' (Sym2.out_snd_mem e.1) = e.1.out.1 := by
  apply Sym2.congr_right.mp
  calc
    s(e.1.out.2, Sym2.Mem.other' (Sym2.out_snd_mem e.1)) = e.1 :=
      Sym2.other_spec' _
    _ = s(e.1.out.2, e.1.out.1) := by
      rw [Sym2.eq_swap, Sym2.mk, e.1.out_eq]

theorem orientedCarrier_leftStar_val
    (z : UnrootedBridgePointed n h r m b × Bool) :
    includeDart (facets := fun _ : Fin n ↦ h)
      (orientedCarrier z).leftCells (orientedCarrier z).leftStar.1 =
        (selectedEndpoint z).1 := by
  rcases z with ⟨⟨⟨P, e⟩, hb⟩, o⟩
  cases o <;>
    simp [orientedCarrier, cutBridge, selectedEndpoint,
      PartialMatching.seamEndpointEquivBool,
      PartialMatching.leftBoundaryAfterErase,
      PartialMatching.rightBoundaryAfterErase,
      PartialMatching.endpointBoundaryAfterErase]

theorem orientedCarrier_rightStar_val
    (z : UnrootedBridgePointed n h r m b × Bool) :
    includeDart (facets := fun _ : Fin n ↦ h)
      (orientedCarrier z).rightCells (orientedCarrier z).rightStar.1 =
        (orientedMarked z).pairing.matching.otherEndpoint (orientedSeam z) := by
  rcases z with ⟨⟨⟨P, e⟩, hb⟩, o⟩
  cases o with
  | false =>
      change e.1.out.2 =
        Sym2.Mem.other' (Sym2.out_fst_mem e.1)
      exact (otherEndpoint_out_fst P.1.raw.pairing.matching e).symm
  | true =>
      change e.1.out.1 =
        Sym2.Mem.other' (Sym2.out_snd_mem e.1)
      exact (otherEndpoint_out_snd P.1.raw.pairing.matching e).symm

@[simp]
theorem boundaryEquivOfEq_val
    {D : Type*} [DecidableEq D] {P Q : ColoredMatching D r}
    (h : P = Q) (x : P.Boundary) :
    (boundaryEquivOfEq h x).1 = x.1 := by
  subst Q
  rfl

theorem bridgeComponentBoundaryLabel_leftStar
    (P : BoundaryLabelledPairing (Dart n h) r m)
    (e : P.pairing.Seam)
    (hconnected : P.pairing.IsConnected (fun _ : Fin n ↦ h))
    (hbridge : P.pairing.IsBridge e) :
    let Q := P.pairing.erase e
    let C := P.pairing.bridge_partition e hconnected hbridge
    let S := BridgePartition.LeftClass
      (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.leftCell e)
    let T := BridgePartition.RightClass
      (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.rightCell e)
    bridgeCutComponentBoundaryLabel P e hconnected hbridge
      (Sum.inl (restrictBoundary Q S
        (P.pairing.matching.leftBoundaryAfterErase e)
        (bridge_exposed_endpoints_on_opposite_sides
          P.pairing e hconnected hbridge).1)) = firstStar m := by
  let Q := P.pairing.erase e
  let C := P.pairing.bridge_partition e hconnected hbridge
  let S := BridgePartition.LeftClass
    (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.leftCell e)
  let T := BridgePartition.RightClass
    (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.rightCell e)
  let x := restrictBoundary Q S
    (P.pairing.matching.leftBoundaryAfterErase e)
    (bridge_exposed_endpoints_on_opposite_sides
      P.pairing e hconnected hbridge).1
  let hreassemble :
      reassembleColored S T C.disjoint (Q.restrict S) (Q.restrict T) = Q :=
    erase_bridge_reassemble_exact P.pairing e hconnected hbridge
  have harg :
      boundaryEquivOfEq hreassemble
        ((boundaryReassembleEquiv S T C.cover C.disjoint
          (Q.restrict S) (Q.restrict T)).symm (Sum.inl x)) =
        P.pairing.matching.leftBoundaryAfterErase e := by
    apply Subtype.ext
    rw [boundaryEquivOfEq_val,
      boundaryReassembleEquiv_symm_inl,
      includeLeftBoundary_val,
      includeDart_restrictBoundary]
  change (P.pairing.matching.cutBoundaryLabel e P.label)
      (boundaryEquivOfEq hreassemble
        ((boundaryReassembleEquiv S T C.cover C.disjoint
          (Q.restrict S) (Q.restrict T)).symm (Sum.inl x))) = firstStar m
  rw [harg]
  exact cutBoundaryLabel_leftEndpoint P.pairing.matching e P.label

theorem bridgeComponentBoundaryLabel_rightStar
    (P : BoundaryLabelledPairing (Dart n h) r m)
    (e : P.pairing.Seam)
    (hconnected : P.pairing.IsConnected (fun _ : Fin n ↦ h))
    (hbridge : P.pairing.IsBridge e) :
    let Q := P.pairing.erase e
    let C := P.pairing.bridge_partition e hconnected hbridge
    let S := BridgePartition.LeftClass
      (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.leftCell e)
    let T := BridgePartition.RightClass
      (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.rightCell e)
    bridgeCutComponentBoundaryLabel P e hconnected hbridge
      (Sum.inr (restrictBoundary Q T
        (P.pairing.matching.rightBoundaryAfterErase e)
        (bridge_exposed_endpoints_on_opposite_sides
          P.pairing e hconnected hbridge).2)) = secondStar m := by
  let Q := P.pairing.erase e
  let C := P.pairing.bridge_partition e hconnected hbridge
  let S := BridgePartition.LeftClass
    (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.leftCell e)
  let T := BridgePartition.RightClass
    (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.rightCell e)
  let x := restrictBoundary Q T
    (P.pairing.matching.rightBoundaryAfterErase e)
    (bridge_exposed_endpoints_on_opposite_sides
      P.pairing e hconnected hbridge).2
  let hreassemble :
      reassembleColored S T C.disjoint (Q.restrict S) (Q.restrict T) = Q :=
    erase_bridge_reassemble_exact P.pairing e hconnected hbridge
  have harg :
      boundaryEquivOfEq hreassemble
        ((boundaryReassembleEquiv S T C.cover C.disjoint
          (Q.restrict S) (Q.restrict T)).symm (Sum.inr x)) =
        P.pairing.matching.rightBoundaryAfterErase e := by
    apply Subtype.ext
    rw [boundaryEquivOfEq_val,
      boundaryReassembleEquiv_symm_inr,
      includeRightBoundary_val,
      includeDart_restrictBoundary]
  change (P.pairing.matching.cutBoundaryLabel e P.label)
      (boundaryEquivOfEq hreassemble
        ((boundaryReassembleEquiv S T C.cover C.disjoint
          (Q.restrict S) (Q.restrict T)).symm (Sum.inr x))) = secondStar m
  rw [harg]
  exact cutBoundaryLabel_rightEndpoint P.pairing.matching e P.label

/-- The oriented carrier's left boundary block contains the first star. -/
theorem firstStar_mem_leftBoundaryLabels
    (z : UnrootedBridgePointed n h r m b × Bool) :
    firstStar m ∈ leftBoundaryLabels (orientedCarrier z) := by
  let C := orientedCarrier z
  apply (mem_leftBoundaryLabels_iff C _).mpr
  refine ⟨C.leftStar, ?_⟩
  let B := boundaryReassembleEquiv C.leftCells C.rightCells C.cover C.disjoint
    (C.core.1.1.restrict C.leftCells)
    (C.core.1.1.restrict C.rightCells)
  have hcut : C.core.1.1 =
      (orientedMarked z).pairing.erase (orientedMarked z).seamSubtype := by
    rcases z with ⟨⟨⟨P, e⟩, hb⟩, o⟩
    cases o <;> rfl
  have harg :
      boundaryEquivOfEq hcut
        (boundaryEquivOfEq C.reassemble_exact
          (B.symm (Sum.inl C.leftStar))) =
        (orientedMarked z).pairing.matching.endpointBoundaryAfterErase
          (orientedSeam z).1 (orientedSeam z).2.1
          (orientedSeam z).2.2 := by
    apply Subtype.ext
    rw [boundaryEquivOfEq_val, boundaryEquivOfEq_val,
      boundaryReassembleEquiv_symm_inl, includeLeftBoundary_val]
    exact orientedCarrier_leftStar_val z
  change orientedCutLabel z
    (boundaryEquivOfEq hcut
      (boundaryEquivOfEq C.reassemble_exact
        (B.symm (Sum.inl C.leftStar)))) = firstStar m
  rw [harg]
  exact orientedCutBoundaryLabel_first _ _ _

theorem secondStar_mem_rightBoundaryLabels
    (z : UnrootedBridgePointed n h r m b × Bool) :
    secondStar m ∈ rightBoundaryLabels (orientedCarrier z) := by
  let C := orientedCarrier z
  apply (mem_rightBoundaryLabels_iff C _).mpr
  refine ⟨C.rightStar, ?_⟩
  let B := boundaryReassembleEquiv C.leftCells C.rightCells C.cover C.disjoint
    (C.core.1.1.restrict C.leftCells)
    (C.core.1.1.restrict C.rightCells)
  have hcut : C.core.1.1 =
      (orientedMarked z).pairing.erase (orientedMarked z).seamSubtype := by
    rcases z with ⟨⟨⟨P, e⟩, hb⟩, o⟩
    cases o <;> rfl
  have harg :
      boundaryEquivOfEq hcut
        (boundaryEquivOfEq C.reassemble_exact
          (B.symm (Sum.inr C.rightStar))) =
        (orientedMarked z).pairing.matching.endpointBoundaryAfterErase
          (orientedSeam z).1
          ((orientedMarked z).pairing.matching.otherEndpoint (orientedSeam z))
          ((orientedMarked z).pairing.matching.otherEndpoint_mem
            (orientedSeam z)) := by
    apply Subtype.ext
    rw [boundaryEquivOfEq_val, boundaryEquivOfEq_val,
      boundaryReassembleEquiv_symm_inr, includeRightBoundary_val]
    exact orientedCarrier_rightStar_val z
  change orientedCutLabel z
    (boundaryEquivOfEq hcut
      (boundaryEquivOfEq C.reassemble_exact
        (B.symm (Sum.inr C.rightStar)))) = secondStar m
  rw [harg]
  exact orientedCutBoundaryLabel_second _ _ _

/-- Consequently the opposite star belongs to the right block, not the
left block. -/
theorem secondStar_not_mem_leftBoundaryLabels
    (z : UnrootedBridgePointed n h r m b × Bool) :
    secondStar m ∉ leftBoundaryLabels (orientedCarrier z) := by
  intro hsecond
  have hdisj := boundaryLabelAllocations_disjoint (orientedCarrier z)
  have hsecondR := secondStar_mem_rightBoundaryLabels z
  exact Finset.disjoint_left.mp hdisj hsecond hsecondR

/-- Package the carrier rank pair as a finite split. -/
def carrierRankSplit (C : UnrootedBridgeCutCarrier n h r m b) : RankSplit b :=
  ⟨(⟨C.leftRank, by have := C.ranks_add; omega⟩,
    ⟨C.rightRank, by have := C.ranks_add; omega⟩), C.ranks_add⟩

/-- The right numerical component, with its rank index rewritten to the
second coordinate of `carrierRankSplit`. -/
def rightNumericalStratumForSplit
    (C : UnrootedBridgeCutCarrier n h r m b) :
    UnrootedStratum (n - (leftCellAllocation C).card) h r
      (m + 2 - (leftBoundaryLabels C).card)
      (carrierRankSplit C).1.2.1 :=
  rightNumericalStratum C

/-- Concrete map into the genuine dependent coproduct. -/
def toCoproduct
    (z : UnrootedBridgePointed n h r m b × Bool) :
    Coproduct n h r m b := by
  let C := orientedCarrier z
  let A : CellAllocation n :=
    ⟨leftCellAllocation C,
      leftCellAllocation_card_pos C, leftCellAllocation_card_lt C⟩
  let B : BoundaryAllocation m :=
    ⟨leftBoundaryLabels C,
      firstStar_mem_leftBoundaryLabels z,
      secondStar_not_mem_leftBoundaryLabels z⟩
  let q := carrierRankSplit C
  exact ⟨A, B, q,
    leftNumericalStratum C, rightNumericalStratumForSplit C, C.deletedColor⟩

@[simp]
theorem toCoproduct_rank_sum
    (z : UnrootedBridgePointed n h r m b × Bool) :
    (toCoproduct z).2.2.1.1.1 + (toCoproduct z).2.2.1.1.2.1 = b :=
  (toCoproduct z).2.2.1.2

@[simp]
theorem toCoproduct_deletedColor
    (z : UnrootedBridgePointed n h r m b × Bool) :
    (toCoproduct z).2.2.2.2.2 = (orientedCarrier z).deletedColor := rfl

/-! ## Reconstruction of an independently indexed cut object

The next definitions go in the inverse direction without assuming that the
two component strata arose from a cut.  The allocation finsets determine
literal complementary cell subtypes and literal complementary boundary
label blocks.  We first undo both component reindexings and then use the
exact coloured/boundary-labelled reassembly equivalences. -/

/-- The literal left cell subtype selected by the coproduct allocation. -/
abbrev leftCellSet (d : Coproduct n h r m b) : Set (Fin n) :=
  {x | x ∈ d.1.1}

/-- Its literal complementary right cell subtype. -/
abbrev rightCellSet (d : Coproduct n h r m b) : Set (Fin n) :=
  {x | x ∉ d.1.1}

@[simp]
theorem leftCellSet_card (d : Coproduct n h r m b) :
    Fintype.card (leftCellSet d) = d.1.1.card := by
  classical
  simp [leftCellSet]

@[simp]
theorem rightCellSet_card (d : Coproduct n h r m b) :
    Fintype.card (rightCellSet d) = n - d.1.1.card := by
  classical
  rw [← Nat.card_eq_fintype_card]
  change Nat.card {x : Fin n // x ∉ d.1.1} = n - d.1.1.card
  have hcard := card_complement d.1.1
  rw [← Nat.card_eq_fintype_card] at hcard
  simpa using hcard

theorem cellSets_cover (d : Coproduct n h r m b) :
    leftCellSet d ∪ rightCellSet d = Set.univ := by
  classical
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true, leftCellSet,
    rightCellSet, Set.mem_setOf_eq]
  exact Classical.em _

theorem cellSets_disjoint (d : Coproduct n h r m b) :
    Disjoint (leftCellSet d) (rightCellSet d) := by
  classical
  rw [Set.disjoint_left]
  simp [leftCellSet, rightCellSet]

/-- Undo the canonical cell reindexing on the left component. -/
def leftRestrictedPairing (d : Coproduct n h r m b) :
    BoundaryLabelledPairing
      (RestrictedDart (facets := fun _ : Fin n ↦ h) (leftCellSet d)) r
      d.2.1.1.card :=
  (componentBoundaryLabelledEquiv (h := h)
    (leftCellSet d) (leftCellSet_card d)).symm d.2.2.2.1.1.raw

/-- Undo the canonical cell reindexing on the complementary component. -/
def rightRestrictedPairing (d : Coproduct n h r m b) :
    BoundaryLabelledPairing
      (RestrictedDart (facets := fun _ : Fin n ↦ h) (rightCellSet d)) r
      (m + 2 - d.2.1.1.card) :=
  (componentBoundaryLabelledEquiv (h := h)
    (rightCellSet d) (rightCellSet_card d)).symm d.2.2.2.2.1.1.raw

/-- Interpret the left component's numerical labels as the allocated
ambient labels themselves. -/
def leftAllocatedLabel (d : Coproduct n h r m b) :
    (leftRestrictedPairing d).pairing.Boundary ≃
      {i : Fin (m + 2) // i ∈ d.2.1.1} :=
  (leftRestrictedPairing d).label.trans
    (finsetSubtypeEquivFin d.2.1.1).symm

/-- Interpret the right component's numerical labels as the complementary
ambient labels. -/
def rightAllocatedLabel (d : Coproduct n h r m b) :
    (rightRestrictedPairing d).pairing.Boundary ≃
      {i : Fin (m + 2) // i ∉ d.2.1.1} :=
  (rightRestrictedPairing d).label.trans <|
    (finCongr (by simp)).trans (complementEquivFin d.2.1.1).symm

/-- Exact coloured disjoint union of the two independently indexed
components on the original ambient cell set. -/
def reconstructedCutPairing (d : Coproduct n h r m b) :
    ColoredMatching (Dart n h) r :=
  reassembleColored (leftCellSet d) (rightCellSet d)
    (cellSets_disjoint d)
    (leftRestrictedPairing d).pairing
    (rightRestrictedPairing d).pairing

/-- The allocation-enriched global boundary labelling on the reconstructed
cut matching. -/
def reconstructedCutLabel (d : Coproduct n h r m b) :
    (reconstructedCutPairing d).Boundary ≃ Fin (m + 2) :=
  (boundaryReassembleEquiv (leftCellSet d) (rightCellSet d)
    (cellSets_cover d) (cellSets_disjoint d)
    (leftRestrictedPairing d).pairing
    (rightRestrictedPairing d).pairing).trans <|
      (Equiv.sumCongr (leftAllocatedLabel d) (rightAllocatedLabel d)).trans
        (finsetSumComplementEquiv d.2.1.1)

/-- The complete reconstructed star-labelled cut object. -/
def reconstructedCutRaw (d : Coproduct n h r m b) :
    BoundaryLabelledPairing (Dart n h) r (m + 2) where
  pairing := reconstructedCutPairing d
  label := reconstructedCutLabel d

/-- The reconstructed global label lies in the remembered left block
exactly when its boundary dart lies on a left allocated cell. -/
theorem reconstructedCutLabel_mem_left_iff
    (d : Coproduct n h r m b)
    (x : (reconstructedCutPairing d).Boundary) :
    reconstructedCutLabel d x ∈ d.2.1.1 ↔
      x.1.1 ∈ leftCellSet d := by
  classical
  by_cases hx : x.1.1 ∈ leftCellSet d
  · have hx' : x.1.1 ∈ d.1.1 := hx
    simp [reconstructedCutLabel, boundaryReassembleEquiv, hx',
      finsetSumComplementEquiv]
  · have hx' : x.1.1 ∉ d.1.1 := hx
    have hright (y : (rightRestrictedPairing d).pairing.Boundary) :
        ((rightAllocatedLabel d) y).1 ∉ d.2.1.1 :=
      ((rightAllocatedLabel d) y).2
    simp [reconstructedCutLabel, boundaryReassembleEquiv, hx',
      finsetSumComplementEquiv]
    exact hright _

/-- The canonical local boundary dart carrying the allocated first star. -/
def leftStarBoundary (d : Coproduct n h r m b) :
    (leftRestrictedPairing d).pairing.Boundary :=
  (leftAllocatedLabel d).symm ⟨firstStar m, d.2.1.2.1⟩

/-- The canonical local boundary dart carrying the complementary second
star. -/
def rightStarBoundary (d : Coproduct n h r m b) :
    (rightRestrictedPairing d).pairing.Boundary :=
  (rightAllocatedLabel d).symm ⟨secondStar m, d.2.1.2.2⟩

theorem reconstructedCutLabel_leftStar (d : Coproduct n h r m b) :
    (reconstructedCutRaw d).label
      (includeLeftBoundary (leftCellSet d) (rightCellSet d)
        (cellSets_disjoint d)
        (leftRestrictedPairing d).pairing
        (rightRestrictedPairing d).pairing (leftStarBoundary d)) =
      firstStar m := by
  simp only [reconstructedCutRaw, reconstructedCutLabel,
    reconstructedCutPairing, Equiv.trans_apply,
    boundaryReassembleEquiv_includeLeft, Equiv.sumCongr_apply,
    Sum.map_inl, leftStarBoundary, Equiv.apply_symm_apply,
    finsetSumComplementEquiv]
  rfl

theorem reconstructedCutLabel_rightStar (d : Coproduct n h r m b) :
    (reconstructedCutRaw d).label
      (includeRightBoundary (leftCellSet d) (rightCellSet d)
        (cellSets_disjoint d)
        (leftRestrictedPairing d).pairing
        (rightRestrictedPairing d).pairing (rightStarBoundary d)) =
      secondStar m := by
  simp only [reconstructedCutRaw, reconstructedCutLabel,
    reconstructedCutPairing, Equiv.trans_apply,
    boundaryReassembleEquiv_includeRight, Equiv.sumCongr_apply,
    Sum.map_inr, rightStarBoundary, Equiv.apply_symm_apply,
    finsetSumComplementEquiv]
  rfl

/-- The first star endpoint is literally in the allocated left cell set. -/
theorem firstStarDart_mem_leftCellSet (d : Coproduct n h r m b) :
    (firstStarDart (reconstructedCutRaw d)).1.1 ∈ leftCellSet d := by
  let x := includeLeftBoundary (leftCellSet d) (rightCellSet d)
    (cellSets_disjoint d)
    (leftRestrictedPairing d).pairing
    (rightRestrictedPairing d).pairing (leftStarBoundary d)
  have hx : x = firstStarDart (reconstructedCutRaw d) := by
    apply (reconstructedCutRaw d).label.injective
    rw [reconstructedCutLabel_leftStar]
    simp [firstStarDart]
  rw [← hx]
  exact (leftStarBoundary d).1.1.2

/-- The second star endpoint is literally in the complementary right cell
set. -/
theorem secondStarDart_mem_rightCellSet (d : Coproduct n h r m b) :
    (secondStarDart (reconstructedCutRaw d)).1.1 ∈ rightCellSet d := by
  let x := includeRightBoundary (leftCellSet d) (rightCellSet d)
    (cellSets_disjoint d)
    (leftRestrictedPairing d).pairing
    (rightRestrictedPairing d).pairing (rightStarBoundary d)
  have hx : x = secondStarDart (reconstructedCutRaw d) := by
    apply (reconstructedCutRaw d).label.injective
    rw [reconstructedCutLabel_rightStar]
    simp [secondStarDart]
  rw [← hx]
  exact (rightStarBoundary d).1.1.2

/-! ## Connectivity and separation of the reconstructed components -/

/-- Component reindexing reflects as well as preserves connectedness. -/
theorem componentReindex_connected_iff
    (S : Set (Fin n)) [Fintype S]
    (hcard : Fintype.card S = k)
    (P : ColoredMatching
      (RestrictedDart (facets := fun _ : Fin n ↦ h) S) r) :
    (componentColoredMatchingEquiv S hcard P).IsConnected
        (fun _ : Fin k ↦ h) ↔
      P.IsConnected (fun _ : S ↦ h) := by
  constructor
  · intro hconn x y
    let e := componentCellEquiv S hcard
    have hp := hconn (e x) (e y)
    have hlift := Relation.ReflTransGen.lift e.symm
      (fun u v huv ↦
        (componentAdjacent_iff S hcard P u v).mp huv) _ _ hp
    simpa only [e, Function.onFun, Equiv.symm_apply_apply] using hlift
  · exact componentReindex_connected S hcard P

theorem leftRestrictedPairing_connected (d : Coproduct n h r m b) :
    (leftRestrictedPairing d).pairing.IsConnected
      (fun _ : leftCellSet d ↦ h) := by
  apply (componentReindex_connected_iff (leftCellSet d)
    (leftCellSet_card d) (leftRestrictedPairing d).pairing).mp
  have hraw := componentBoundaryLabelledEquiv_apply_symm_apply
    (r := r) (m := d.2.1.1.card) (leftCellSet d)
    (leftCellSet_card d) d.2.2.2.1.1.raw
  have hp :
      componentColoredMatchingEquiv (leftCellSet d)
          (leftCellSet_card d) (leftRestrictedPairing d).pairing =
        d.2.2.2.1.1.raw.pairing := by
    change ((componentBoundaryLabelledEquiv (leftCellSet d)
      (leftCellSet_card d))
        ((componentBoundaryLabelledEquiv (leftCellSet d)
          (leftCellSet_card d)).symm d.2.2.2.1.1.raw)).pairing = _
    exact congrArg BoundaryLabelledPairing.pairing hraw
  rw [hp]
  exact d.2.2.2.1.1.connected

theorem rightRestrictedPairing_connected (d : Coproduct n h r m b) :
    (rightRestrictedPairing d).pairing.IsConnected
      (fun _ : rightCellSet d ↦ h) := by
  apply (componentReindex_connected_iff (rightCellSet d)
    (rightCellSet_card d) (rightRestrictedPairing d).pairing).mp
  have hraw := componentBoundaryLabelledEquiv_apply_symm_apply
    (r := r) (m := m + 2 - d.2.1.1.card) (rightCellSet d)
    (rightCellSet_card d) d.2.2.2.2.1.1.raw
  have hp :
      componentColoredMatchingEquiv (rightCellSet d)
          (rightCellSet_card d) (rightRestrictedPairing d).pairing =
        d.2.2.2.2.1.1.raw.pairing := by
    change ((componentBoundaryLabelledEquiv (rightCellSet d)
      (rightCellSet_card d))
        ((componentBoundaryLabelledEquiv (rightCellSet d)
          (rightCellSet_card d)).symm d.2.2.2.2.1.1.raw)).pairing = _
    exact congrArg BoundaryLabelledPairing.pairing hraw
  rw [hp]
  exact d.2.2.2.2.1.1.connected

theorem reconstructedCut_restrict_left (d : Coproduct n h r m b) :
    (reconstructedCutPairing d).restrict (leftCellSet d) =
      (leftRestrictedPairing d).pairing := by
  exact ColoredMatching.restrict_reassembleColored_left
    (leftCellSet d) (rightCellSet d) (cellSets_disjoint d)
    (leftRestrictedPairing d).pairing
    (rightRestrictedPairing d).pairing

theorem reconstructedCut_restrict_right (d : Coproduct n h r m b) :
    (reconstructedCutPairing d).restrict (rightCellSet d) =
      (rightRestrictedPairing d).pairing := by
  exact ColoredMatching.restrict_reassembleColored_right
    (leftCellSet d) (rightCellSet d) (cellSets_disjoint d)
    (leftRestrictedPairing d).pairing
    (rightRestrictedPairing d).pairing

/-- Any two allocated left cells are connected by an ambient path in the
reconstructed cut matching. -/
theorem reconstructedCut_left_connected (d : Coproduct n h r m b)
    (x y : leftCellSet d) :
    Relation.ReflTransGen
      ((reconstructedCutPairing d).Adjacent (fun _ : Fin n ↦ h)) x.1 y.1 := by
  have hlocal :
      ((reconstructedCutPairing d).restrict (leftCellSet d)).IsConnected
        (fun _ : leftCellSet d ↦ h) := by
    rw [reconstructedCut_restrict_left]
    exact leftRestrictedPairing_connected d
  have hlift := Relation.ReflTransGen.lift Subtype.val
    (fun u v huv ↦ ((reconstructedCutPairing d).adjacent_restrict_iff
      (leftCellSet d) u v).mp huv) _ _ (hlocal x y)
  simpa [Function.onFun] using hlift

/-- Any two complementary right cells are connected by an ambient path in
the reconstructed cut matching. -/
theorem reconstructedCut_right_connected (d : Coproduct n h r m b)
    (x y : rightCellSet d) :
    Relation.ReflTransGen
      ((reconstructedCutPairing d).Adjacent (fun _ : Fin n ↦ h)) x.1 y.1 := by
  have hlocal :
      ((reconstructedCutPairing d).restrict (rightCellSet d)).IsConnected
        (fun _ : rightCellSet d ↦ h) := by
    rw [reconstructedCut_restrict_right]
    exact rightRestrictedPairing_connected d
  have hlift := Relation.ReflTransGen.lift Subtype.val
    (fun u v huv ↦ ((reconstructedCutPairing d).adjacent_restrict_iff
      (rightCellSet d) u v).mp huv) _ _ (hlocal x y)
  simpa [Function.onFun] using hlift

/-- No seam of the reconstructed disjoint union crosses the allocation. -/
theorem reconstructedCut_noCrossing (d : Coproduct n h r m b) :
    NoCrossing (reconstructedCutPairing d)
      (leftCellSet d) (rightCellSet d) := by
  intro u hu v hv huv
  obtain ⟨i, j, hij⟩ := huv
  have hinternal := seamInternal_reassembleMatching
    (leftCellSet d) (rightCellSet d) (cellSets_disjoint d)
    (leftRestrictedPairing d).pairing.matching
    (rightRestrictedPairing d).pairing.matching
    s(⟨u, i⟩, ⟨v, j⟩) hij
  rcases hinternal with hleft | hright
  · exact Set.disjoint_left.mp (cellSets_disjoint d)
      (hleft ⟨v, j⟩ (by simp)) hv
  · exact Set.disjoint_left.mp (cellSets_disjoint d)
      hu (hright ⟨u, i⟩ (by simp))

/-- A path in the separated cut matching starting on the left cannot leave
the left allocation. -/
theorem reconstructedCut_path_stays_left (d : Coproduct n h r m b)
    {x y : Fin n} (hx : x ∈ leftCellSet d)
    (p : Relation.ReflTransGen
      ((reconstructedCutPairing d).Adjacent (fun _ : Fin n ↦ h)) x y) :
    y ∈ leftCellSet d := by
  induction p with
  | refl => exact hx
  | @tail u v huv huv' ih =>
      have hvSide : v ∈ leftCellSet d ∨ v ∈ rightCellSet d := by
        have : v ∈ leftCellSet d ∪ rightCellSet d := by
          rw [cellSets_cover d]
          exact Set.mem_univ v
        simpa only [Set.mem_union] using this
      exact hvSide.resolve_right (fun hv ↦
        reconstructedCut_noCrossing d ih hv huv')

/-- The two allocated star cells witness that the reconstructed cut matching
is disconnected. -/
theorem reconstructedCut_not_connected (d : Coproduct n h r m b) :
    ¬ (reconstructedCutPairing d).IsConnected (fun _ : Fin n ↦ h) := by
  intro hconn
  let a := (firstStarDart (reconstructedCutRaw d)).1.1
  let c := (secondStarDart (reconstructedCutRaw d)).1.1
  have ha : a ∈ leftCellSet d := firstStarDart_mem_leftCellSet d
  have hc : c ∈ rightCellSet d := secondStarDart_mem_rightCellSet d
  have hcLeft := reconstructedCut_path_stays_left d ha (hconn a c)
  exact Set.disjoint_left.mp (cellSets_disjoint d) hcLeft hc

/-! ## Seam counts, rank, and the literal star join -/

theorem leftRestrictedPairing_seam_card (d : Coproduct n h r m b) :
    (leftRestrictedPairing d).pairing.matching.seams.card + 1 =
      d.1.1.card + d.2.2.1.1.1 := by
  have hp :
      componentColoredMatchingEquiv (leftCellSet d)
          (leftCellSet_card d) (leftRestrictedPairing d).pairing =
        d.2.2.2.1.1.raw.pairing := by
    change ((componentBoundaryLabelledEquiv (leftCellSet d)
      (leftCellSet_card d))
        ((componentBoundaryLabelledEquiv (leftCellSet d)
          (leftCellSet_card d)).symm d.2.2.2.1.1.raw)).pairing = _
    exact congrArg BoundaryLabelledPairing.pairing
      (componentBoundaryLabelledEquiv_apply_symm_apply
        (r := r) (m := d.2.1.1.card) (leftCellSet d)
        (leftCellSet_card d) d.2.2.2.1.1.raw)
  have hcard := componentReindex_seam_card (leftCellSet d)
    (leftCellSet_card d) (leftRestrictedPairing d).pairing
  rw [hp] at hcard
  rw [← hcard]
  simpa [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
    BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount,
    card_unrootedCell] using d.2.2.2.1.2

theorem rightRestrictedPairing_seam_card (d : Coproduct n h r m b) :
    (rightRestrictedPairing d).pairing.matching.seams.card + 1 =
      (n - d.1.1.card) + d.2.2.1.1.2.1 := by
  have hp :
      componentColoredMatchingEquiv (rightCellSet d)
          (rightCellSet_card d) (rightRestrictedPairing d).pairing =
        d.2.2.2.2.1.1.raw.pairing := by
    change ((componentBoundaryLabelledEquiv (rightCellSet d)
      (rightCellSet_card d))
        ((componentBoundaryLabelledEquiv (rightCellSet d)
          (rightCellSet_card d)).symm d.2.2.2.2.1.1.raw)).pairing = _
    exact congrArg BoundaryLabelledPairing.pairing
      (componentBoundaryLabelledEquiv_apply_symm_apply
        (r := r) (m := m + 2 - d.2.1.1.card) (rightCellSet d)
        (rightCellSet_card d) d.2.2.2.2.1.1.raw)
  have hcard := componentReindex_seam_card (rightCellSet d)
    (rightCellSet_card d) (rightRestrictedPairing d).pairing
  rw [hp] at hcard
  rw [← hcard]
  simpa [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
    BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount,
    card_unrootedCell] using d.2.2.2.2.1.2

theorem reconstructedCut_seam_card_add (d : Coproduct n h r m b) :
    (reconstructedCutPairing d).matching.seams.card =
      (leftRestrictedPairing d).pairing.matching.seams.card +
        (rightRestrictedPairing d).pairing.matching.seams.card := by
  change (reassembleMatching (leftCellSet d) (rightCellSet d)
    (cellSets_disjoint d)
    (leftRestrictedPairing d).pairing.matching
    (rightRestrictedPairing d).pairing.matching).seams.card = _
  rw [seams_reassembleMatching]
  rw [Finset.card_union_of_disjoint]
  · simp
  · rw [Finset.disjoint_left]
    intro e heL heR
    obtain ⟨eL, heLM, heLe⟩ := Finset.mem_map.mp heL
    obtain ⟨eR, heRM, heRe⟩ := Finset.mem_map.mp heR
    exact includeSeam_ne_of_disjoint (leftCellSet d) (rightCellSet d)
      (cellSets_disjoint d) eL eR (heLe.trans heRe.symm)

theorem reconstructedCut_rank (d : Coproduct n h r m b) :
    (reconstructedCutPairing d).matching.seams.card + 2 = n + b := by
  have hA := d.1.2
  have hq := d.2.2.1.2
  have hL := leftRestrictedPairing_seam_card d
  have hR := rightRestrictedPairing_seam_card d
  rw [reconstructedCut_seam_card_add]
  omega

/-- Join the two allocated star darts with the remembered seam colour. -/
def reconstructedJoinMarked (d : Coproduct n h r m b) :
    ColoredMatching.MarkedColoredMatching (Dart n h) r :=
  joinStarsMarked (reconstructedCutRaw d, d.2.2.2.2.2)

/-- The boundary-labelled pairing after removing the two star labels. -/
def reconstructedJoinedRaw (d : Coproduct n h r m b) :
    UnrootedPairing n h r m where
  pairing := (reconstructedJoinMarked d).1
  label := NonbridgeEquiv.joinedBoundaryLabel
    (reconstructedCutRaw d) d.2.2.2.2.2

/-- Erasing the distinguished reconstructed seam returns the complete
allocated cut coloured matching exactly. -/
theorem erase_reconstructedJoinMarked (d : Coproduct n h r m b) :
    (reconstructedJoinMarked d).1.erase (reconstructedJoinMarked d).2 =
      reconstructedCutPairing d := by
  exact cut_joinStars_pairing
    (reconstructedCutRaw d, d.2.2.2.2.2)

theorem reconstructedJoined_rank (d : Coproduct n h r m b) :
    (reconstructedJoinedRaw d).pairing.matching.seams.card + 1 =
      n + b := by
  change (reconstructedJoinMarked d).1.matching.seams.card + 1 = n + b
  have hj : (reconstructedJoinMarked d).1.matching.seams.card =
      (reconstructedCutPairing d).matching.seams.card + 1 := by
    change ((reconstructedCutPairing d).joinFreePair
      (starFreePairDatum (reconstructedCutRaw d)
        d.2.2.2.2.2)).matching.seams.card = _
    exact PartialMatching.card_seams_join _ _ _
      ((starFreePairDatum (reconstructedCutRaw d)
        d.2.2.2.2.2).selected.left_ne_right _)
  rw [hj]
  have := reconstructedCut_rank d
  omega

/-! The connectivity proof below is specialized to the canonical star
endpoints.  It is the converse of bridge restriction: two connected,
separated components become connected after inserting their one cross seam. -/

theorem reconstructedJoined_adjacent_cross (d : Coproduct n h r m b) :
    (reconstructedJoinMarked d).1.Adjacent (fun _ : Fin n ↦ h)
      (firstStarDart (reconstructedCutRaw d)).1.1
      (secondStarDart (reconstructedCutRaw d)).1.1 := by
  refine ⟨(firstStarDart (reconstructedCutRaw d)).1.2,
    (secondStarDart (reconstructedCutRaw d)).1.2, ?_⟩
  change s((firstStarDart (reconstructedCutRaw d)).1,
      (secondStarDart (reconstructedCutRaw d)).1) ∈
    (reconstructedJoinMarked d).1.matching.seams
  change (starFreePair (reconstructedCutRaw d)).pair ∈
    ((reconstructedCutPairing d).joinFreePair
      (starFreePairDatum (reconstructedCutRaw d)
        d.2.2.2.2.2)).matching.seams
  rw [show (starFreePair (reconstructedCutRaw d)).pair =
      (starFreePairDatum (reconstructedCutRaw d)
        d.2.2.2.2.2).selected.pair from rfl]
  change _ ∈ insert _ _
  simp only [PartialMatching.FreePair.joinPair_left_right,
    Finset.mem_insert, true_or]

theorem reconstructedJoined_connected (d : Coproduct n h r m b) :
    (reconstructedJoinMarked d).1.IsConnected (fun _ : Fin n ↦ h) := by
  intro u v
  let a := (firstStarDart (reconstructedCutRaw d)).1.1
  let c := (secondStarDart (reconstructedCutRaw d)).1.1
  have ha : a ∈ leftCellSet d := firstStarDart_mem_leftCellSet d
  have hc : c ∈ rightCellSet d := secondStarDart_mem_rightCellSet d
  have oldMono {x y : Fin n}
      (p : Relation.ReflTransGen
        ((reconstructedCutPairing d).Adjacent (fun _ : Fin n ↦ h)) x y) :
      Relation.ReflTransGen
        ((reconstructedJoinMarked d).1.Adjacent (fun _ : Fin n ↦ h)) x y :=
    p.mapRelation (fun x y hxy ↦ by
      obtain ⟨i, j, hij⟩ := hxy
      exact ⟨i, j, Finset.mem_insert_of_mem hij⟩)
  have hside (x : Fin n) : x ∈ leftCellSet d ∨ x ∈ rightCellSet d := by
    have : x ∈ leftCellSet d ∪ rightCellSet d := by
      rw [cellSets_cover d]
      exact Set.mem_univ x
    simpa only [Set.mem_union] using this
  rcases hside u with huL | huR
  · rcases hside v with hvL | hvR
    · exact oldMono (reconstructedCut_left_connected d ⟨u, huL⟩ ⟨v, hvL⟩)
    · exact (oldMono (reconstructedCut_left_connected d ⟨u, huL⟩
          ⟨a, ha⟩)).trans <|
        (Relation.ReflTransGen.single
          (reconstructedJoined_adjacent_cross d)).trans <|
        oldMono (reconstructedCut_right_connected d ⟨c, hc⟩ ⟨v, hvR⟩)
  · rcases hside v with hvL | hvR
    · exact (oldMono (reconstructedCut_right_connected d ⟨u, huR⟩
          ⟨c, hc⟩)).trans <|
        (Relation.ReflTransGen.single
          ((reconstructedJoinMarked d).1.adjacent_symm _
            (reconstructedJoined_adjacent_cross d))).trans <|
        oldMono (reconstructedCut_left_connected d ⟨a, ha⟩ ⟨v, hvL⟩)
    · exact oldMono (reconstructedCut_right_connected d ⟨u, huR⟩ ⟨v, hvR⟩)

theorem reconstructedJoin_bridge (d : Coproduct n h r m b) :
    (reconstructedJoinMarked d).1.IsBridge (reconstructedJoinMarked d).2 := by
  intro hconnected
  rw [erase_reconstructedJoinMarked] at hconnected
  exact reconstructedCut_not_connected d hconnected

/-- The actual connected rank-`b` unrooted stratum reconstructed from the
independent component coproduct. -/
def reconstructedStratum (d : Coproduct n h r m b) :
    UnrootedStratum n h r m b :=
  ⟨⟨reconstructedJoinedRaw d, reconstructedJoined_connected d⟩,
    by simpa [ConnectedDiagram.HasCircuitRank,
      ConnectedDiagram.edgeCount, BoundaryLabelledPairing.edgeCount,
      ColoredMatching.edgeCount, card_unrootedCell] using
        reconstructedJoined_rank d⟩

def reconstructedNewSeam (d : Coproduct n h r m b) :
    (reconstructedStratum d).1.raw.pairing.Seam :=
  (reconstructedJoinMarked d).2

/-- The first-star dart, as an endpoint of the reconstructed seam. -/
def reconstructedOrientation (d : Coproduct n h r m b) :
    {x : Dart n h // x ∈ (reconstructedNewSeam d).1} :=
  ⟨(firstStarDart (reconstructedCutRaw d)).1, by
    change (firstStarDart (reconstructedCutRaw d)).1 ∈
      (reconstructedJoinMarked d).2.1
    rw [show (reconstructedJoinMarked d).2.1 =
      (starFreePair (reconstructedCutRaw d)).pair from
        ColoredMatching.freePairNewSeam_val _ _]
    simp [starFreePair]⟩

/-- Complete inverse map: the Boolean is the literal position, in
`Sym2.out`, of the endpoint selected by the first star. -/
def fromCoproduct (d : Coproduct n h r m b) :
    UnrootedBridgePointed n h r m b × Bool :=
  (⟨⟨reconstructedStratum d, reconstructedNewSeam d⟩,
      reconstructedJoin_bridge d⟩,
    (reconstructedStratum d).1.raw.pairing.matching.seamEndpointEquivBool
      (reconstructedNewSeam d) (reconstructedOrientation d))

/-! ## Recovery of the allocation indices -/

theorem orientedCarrier_leftCells_eq_reachable
    (z : UnrootedBridgePointed n h r m b × Bool) :
    (orientedCarrier z).leftCells =
      BridgePartition.LeftClass
        ((orientedCarrier z).core.1.1.Adjacent (fun _ : Fin n ↦ h))
        (selectedEndpoint z).1.1 := by
  rcases z with ⟨⟨⟨P, e⟩, hbridge⟩, o⟩
  cases o <;> rfl

theorem orientedCarrier_core_pairing
    (z : UnrootedBridgePointed n h r m b × Bool) :
    (orientedCarrier z).core.1.1 =
      z.1.1.1.1.raw.pairing.erase z.1.1.2 := by
  rcases z with ⟨⟨⟨P, e⟩, hbridge⟩, o⟩
  cases o <;> rfl

theorem orientedCarrier_core_color
    (z : UnrootedBridgePointed n h r m b × Bool) :
    (orientedCarrier z).core.1.2.color =
      z.1.1.1.1.raw.pairing.color z.1.1.2 := by
  rcases z with ⟨⟨⟨P, e⟩, hbridge⟩, o⟩
  cases o <;> rfl

@[simp]
theorem selectedEndpoint_fromCoproduct (d : Coproduct n h r m b) :
    selectedEndpoint (fromCoproduct d) = reconstructedOrientation d := by
  exact (((reconstructedStratum d).1.raw.pairing.matching.seamEndpointEquivBool
    (reconstructedNewSeam d))).symm_apply_apply
      (reconstructedOrientation d)

theorem orientedSeam_fromCoproduct (d : Coproduct n h r m b) :
    orientedSeam (fromCoproduct d) =
      StarJoinLabelCoherence.starJoinOrientation
        (reconstructedCutRaw d) d.2.2.2.2.2 := by
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (selectedEndpoint_fromCoproduct d)

set_option maxHeartbeats 1000000 in
theorem orientedCutLabel_fromCoproduct (d : Coproduct n h r m b) :
    (boundaryEquivOfEq (erase_reconstructedJoinMarked d)).symm.trans
        (orientedCutLabel (fromCoproduct d)) =
      (reconstructedCutRaw d).label := by
  have hstar := StarJoinLabelCoherence.orientedCut_starJoin_label
    (reconstructedCutRaw d) d.2.2.2.2.2
  unfold orientedCutLabel
  change (boundaryEquivOfEq (erase_reconstructedJoinMarked d)).symm.trans
      ((reconstructedJoinMarked d).1.matching.orientedCutBoundaryLabel
        (orientedSeam (fromCoproduct d))
        (NonbridgeEquiv.joinedBoundaryLabel
          (reconstructedCutRaw d) d.2.2.2.2.2)) =
    (reconstructedCutRaw d).label
  let M := (reconstructedJoinMarked d).1
  let e : M.Seam := (reconstructedJoinMarked d).2
  let lab := NonbridgeEquiv.joinedBoundaryLabel
    (reconstructedCutRaw d) d.2.2.2.2.2
  let cutAt : {x : Dart n h // x ∈ e.1} →
      ((M.erase e).Boundary ≃ Fin (m + 2)) := fun x ↦
    M.matching.orientedCutBoundaryLabel ⟨e, x⟩ lab
  have hcutAt := congrArg cutAt (selectedEndpoint_fromCoproduct d)
  change (boundaryEquivOfEq (erase_reconstructedJoinMarked d)).symm.trans
      (cutAt (selectedEndpoint (fromCoproduct d))) =
    (reconstructedCutRaw d).label
  rw [hcutAt]
  exact hstar

theorem orientedCarrier_from_leftCells (d : Coproduct n h r m b) :
    (orientedCarrier (fromCoproduct d)).leftCells = leftCellSet d := by
  rw [orientedCarrier_leftCells_eq_reachable]
  ext x
  constructor
  · intro hx
    change Relation.ReflTransGen
      ((orientedCarrier (fromCoproduct d)).core.1.1.Adjacent
        (fun _ : Fin n ↦ h)) _ x at hx
    have hcore : (orientedCarrier (fromCoproduct d)).core.1.1 =
        reconstructedCutPairing d := by
      rw [orientedCarrier_core_pairing]
      exact erase_reconstructedJoinMarked d
    rw [hcore, selectedEndpoint_fromCoproduct] at hx
    exact reconstructedCut_path_stays_left d
      (firstStarDart_mem_leftCellSet d) hx
  · intro hx
    change Relation.ReflTransGen
      ((orientedCarrier (fromCoproduct d)).core.1.1.Adjacent
        (fun _ : Fin n ↦ h)) _ x
    have hcore : (orientedCarrier (fromCoproduct d)).core.1.1 =
        reconstructedCutPairing d := by
      rw [orientedCarrier_core_pairing]
      exact erase_reconstructedJoinMarked d
    rw [hcore, selectedEndpoint_fromCoproduct]
    exact reconstructedCut_left_connected d
      ⟨_, firstStarDart_mem_leftCellSet d⟩ ⟨x, hx⟩

@[simp]
theorem leftCellAllocation_orientedCarrier_from
    (d : Coproduct n h r m b) :
    leftCellAllocation (orientedCarrier (fromCoproduct d)) = d.1.1 := by
  classical
  rw [leftCellAllocation, orientedCarrier_from_leftCells]
  ext x
  simp [leftCellSet]

theorem orientedCarrier_from_rightCells (d : Coproduct n h r m b) :
    (orientedCarrier (fromCoproduct d)).rightCells = rightCellSet d := by
  ext x
  constructor
  · intro hx
    change x ∉ d.1.1
    intro hxA
    have hxL : x ∈ (orientedCarrier (fromCoproduct d)).leftCells := by
      rw [orientedCarrier_from_leftCells]
      exact hxA
    exact Set.disjoint_left.mp
      (orientedCarrier (fromCoproduct d)).disjoint hxL hx
  · intro hx
    have hcover : x ∈ (orientedCarrier (fromCoproduct d)).leftCells ∨
        x ∈ (orientedCarrier (fromCoproduct d)).rightCells := by
      have : x ∈ (orientedCarrier (fromCoproduct d)).leftCells ∪
          (orientedCarrier (fromCoproduct d)).rightCells := by
        rw [(orientedCarrier (fromCoproduct d)).cover]
        exact Set.mem_univ x
      simpa only [Set.mem_union] using this
    exact hcover.resolve_left (fun hxL ↦ hx (by
      rw [orientedCarrier_from_leftCells] at hxL
      exact hxL))

theorem orientedCarrier_from_core_pairing (d : Coproduct n h r m b) :
    (orientedCarrier (fromCoproduct d)).core.1.1 =
      reconstructedCutPairing d := by
  rw [orientedCarrier_core_pairing]
  exact erase_reconstructedJoinMarked d

set_option maxHeartbeats 1000000 in
/-- Every label occurring on the reconstructed carrier's left restriction
belongs to the remembered boundary allocation. -/
theorem orientedCarrier_from_left_label_mem
    (d : Coproduct n h r m b)
    (x : ((orientedCarrier (fromCoproduct d)).core.1.1.restrict
      (orientedCarrier (fromCoproduct d)).leftCells).Boundary) :
    leftBoundaryLabelMap (orientedCarrier (fromCoproduct d)) x ∈
      d.2.1.1 := by
  let z := fromCoproduct d
  let C := orientedCarrier z
  change ((C.core.1.1.restrict C.leftCells).Boundary) at x
  let E := boundaryReassembleEquiv C.leftCells C.rightCells C.cover C.disjoint
    (C.core.1.1.restrict C.leftCells)
    (C.core.1.1.restrict C.rightCells)
  let y : C.core.1.1.Boundary :=
    boundaryEquivOfEq C.reassemble_exact (E.symm (Sum.inl x))
  have hcut : C.core.1.1 =
      (orientedMarked z).pairing.erase (orientedMarked z).seamSubtype := by
    rcases z with ⟨⟨⟨P, e⟩, hb⟩, o⟩
    cases o <;> rfl
  let u : ((orientedMarked z).pairing.erase
      (orientedMarked z).seamSubtype).Boundary :=
    boundaryEquivOfEq hcut y
  let q : (reconstructedCutPairing d).Boundary :=
    boundaryEquivOfEq (erase_reconstructedJoinMarked d) u
  have hcoh' : orientedCutLabel z u = reconstructedCutLabel d q := by
    calc
      orientedCutLabel z u =
          ((boundaryEquivOfEq (erase_reconstructedJoinMarked d)).symm.trans
            (orientedCutLabel z))
            (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u) := by
              simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
              rfl
      _ = reconstructedCutLabel d
          (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u) :=
            congrArg (fun L ↦ L
              (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u))
              (orientedCutLabel_fromCoproduct d)
      _ = reconstructedCutLabel d q := rfl
  change orientedCutLabel z u ∈ d.2.1.1
  rw [hcoh']
  apply (reconstructedCutLabel_mem_left_iff d q).2
  have hxcell : x.1.1.1 ∈ leftCellSet d := by
    have hxmem := x.1.1.2
    exact (Set.ext_iff.mp (orientedCarrier_from_leftCells d) _).mp hxmem
  have hqcell : q.1.1 = x.1.1.1 := by
    simp only [q, u, y, E, boundaryEquivOfEq_val,
      boundaryReassembleEquiv_symm_inl, includeLeftBoundary_val]
    rfl
  rwa [hqcell]

set_option maxHeartbeats 1000000 in
/-- No label occurring on the reconstructed carrier's right restriction
belongs to the remembered left boundary allocation. -/
theorem orientedCarrier_from_right_label_not_mem
    (d : Coproduct n h r m b)
    (x : ((orientedCarrier (fromCoproduct d)).core.1.1.restrict
      (orientedCarrier (fromCoproduct d)).rightCells).Boundary) :
    rightBoundaryLabelMap (orientedCarrier (fromCoproduct d)) x ∉
      d.2.1.1 := by
  let z := fromCoproduct d
  let C := orientedCarrier z
  change ((C.core.1.1.restrict C.rightCells).Boundary) at x
  let E := boundaryReassembleEquiv C.leftCells C.rightCells C.cover C.disjoint
    (C.core.1.1.restrict C.leftCells)
    (C.core.1.1.restrict C.rightCells)
  let y : C.core.1.1.Boundary :=
    boundaryEquivOfEq C.reassemble_exact (E.symm (Sum.inr x))
  have hcut : C.core.1.1 =
      (orientedMarked z).pairing.erase (orientedMarked z).seamSubtype := by
    rcases z with ⟨⟨⟨P, e⟩, hb⟩, o⟩
    cases o <;> rfl
  let u : ((orientedMarked z).pairing.erase
      (orientedMarked z).seamSubtype).Boundary :=
    boundaryEquivOfEq hcut y
  let q : (reconstructedCutPairing d).Boundary :=
    boundaryEquivOfEq (erase_reconstructedJoinMarked d) u
  have hcoh' : orientedCutLabel z u = reconstructedCutLabel d q := by
    calc
      orientedCutLabel z u =
          ((boundaryEquivOfEq (erase_reconstructedJoinMarked d)).symm.trans
            (orientedCutLabel z))
            (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u) := by
              simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
              rfl
      _ = reconstructedCutLabel d
          (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u) :=
            congrArg (fun L ↦ L
              (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u))
              (orientedCutLabel_fromCoproduct d)
      _ = reconstructedCutLabel d q := rfl
  change orientedCutLabel z u ∉ d.2.1.1
  rw [hcoh']
  intro hlabel
  have hqleft := (reconstructedCutLabel_mem_left_iff d q).1 hlabel
  have hxright : x.1.1.1 ∈ rightCellSet d := by
    have hxmem := x.1.1.2
    exact (Set.ext_iff.mp (orientedCarrier_from_rightCells d) _).mp hxmem
  have hqcell : q.1.1 = x.1.1.1 := by
    simp only [q, u, y, E, boundaryEquivOfEq_val,
      boundaryReassembleEquiv_symm_inr, includeRightBoundary_val]
    rfl
  exact Set.disjoint_left.mp (cellSets_disjoint d)
    (hqcell ▸ hqleft) hxright

@[simp]
theorem orientedCarrier_from_leftBoundaryLabels
    (d : Coproduct n h r m b) :
    leftBoundaryLabels (orientedCarrier (fromCoproduct d)) = d.2.1.1 := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨x, rfl⟩ :=
      (mem_leftBoundaryLabels_iff
        (orientedCarrier (fromCoproduct d)) i).mp hi
    exact orientedCarrier_from_left_label_mem d x
  · intro hi
    have hcover := boundaryLabelAllocations_cover
      (orientedCarrier (fromCoproduct d))
    have hiUnion : i ∈ leftBoundaryLabels (orientedCarrier (fromCoproduct d)) ∨
        i ∈ rightBoundaryLabels (orientedCarrier (fromCoproduct d)) := by
      have : i ∈ leftBoundaryLabels (orientedCarrier (fromCoproduct d)) ∪
          rightBoundaryLabels (orientedCarrier (fromCoproduct d)) := by
        rw [hcover]
        exact Finset.mem_univ i
      simpa only [Finset.mem_union] using this
    rcases hiUnion with hiL | hiR
    · exact hiL
    · obtain ⟨x, hx⟩ :=
        (mem_rightBoundaryLabels_iff
          (orientedCarrier (fromCoproduct d)) i).mp hiR
      exact False.elim ((orientedCarrier_from_right_label_not_mem d x)
        (hx ▸ hi))

theorem orientedCarrier_from_left_seam_card (d : Coproduct n h r m b) :
    ((orientedCarrier (fromCoproduct d)).core.1.1.restrict
      (orientedCarrier (fromCoproduct d)).leftCells).matching.seams.card =
        (leftRestrictedPairing d).pairing.matching.seams.card := by
  rw [orientedCarrier_from_leftCells, orientedCarrier_from_core_pairing]
  exact congrArg (fun P : ColoredMatching
      (RestrictedDart (facets := fun _ : Fin n ↦ h) (leftCellSet d)) r ↦
        P.matching.seams.card) (reconstructedCut_restrict_left d)

theorem orientedCarrier_from_right_seam_card (d : Coproduct n h r m b) :
    ((orientedCarrier (fromCoproduct d)).core.1.1.restrict
      (orientedCarrier (fromCoproduct d)).rightCells).matching.seams.card =
        (rightRestrictedPairing d).pairing.matching.seams.card := by
  rw [orientedCarrier_from_rightCells, orientedCarrier_from_core_pairing]
  exact congrArg (fun P : ColoredMatching
      (RestrictedDart (facets := fun _ : Fin n ↦ h) (rightCellSet d)) r ↦
        P.matching.seams.card) (reconstructedCut_restrict_right d)

theorem orientedCarrier_from_leftRank (d : Coproduct n h r m b) :
    (orientedCarrier (fromCoproduct d)).leftRank = d.2.2.1.1.1 := by
  let C := orientedCarrier (fromCoproduct d)
  have hspec := C.leftRank_spec
  have hlocal := leftRestrictedPairing_seam_card d
  have hset := orientedCarrier_from_leftCells d
  have hpair := orientedCarrier_from_left_seam_card d
  rw [hpair] at hspec
  have hcard : Nat.card C.leftCells = d.1.1.card := by
    rw [hset, Nat.card_eq_fintype_card, leftCellSet_card]
  rw [hcard] at hspec
  exact Nat.add_left_cancel (hspec.symm.trans hlocal)

theorem orientedCarrier_from_rightRank (d : Coproduct n h r m b) :
    (orientedCarrier (fromCoproduct d)).rightRank = d.2.2.1.1.2.1 := by
  let C := orientedCarrier (fromCoproduct d)
  have hspec := C.rightRank_spec
  have hlocal := rightRestrictedPairing_seam_card d
  have hset := orientedCarrier_from_rightCells d
  have hpair := orientedCarrier_from_right_seam_card d
  rw [hpair] at hspec
  have hcard : Nat.card C.rightCells = n - d.1.1.card := by
    rw [hset, Nat.card_eq_fintype_card, rightCellSet_card]
  rw [hcard] at hspec
  exact Nat.add_left_cancel (hspec.symm.trans hlocal)

theorem orientedCarrier_from_deletedColor (d : Coproduct n h r m b) :
    (orientedCarrier (fromCoproduct d)).deletedColor = d.2.2.2.2.2 := by
  rw [(orientedCarrier (fromCoproduct d)).deletedColor_eq]
  rw [orientedCarrier_core_color]
  exact cut_joinStars_color (reconstructedCutRaw d, d.2.2.2.2.2)


end
end UnrootedBridgeCoproduct
end FacetPairing
end PolytopeCounting
