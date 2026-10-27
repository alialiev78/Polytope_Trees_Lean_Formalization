module

public import Proofs.BridgeLabelledRestriction
public import Proofs.LabelledCutJoin
public import Proofs.CircuitRankComponents
public import Proofs.PointedDecomposition

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# A lossless global carrier for cutting an unrooted bridge

This module assembles the local bridge results into one global forward map.
Its target retains the exact labelled cut--join core, but also exposes the
two oriented reachability classes, the two concrete connected restrictions,
one new boundary dart on each side, the allocation of all old labels and the
two star labels, the deleted colour, additive component ranks, and exact
colour-preserving reassembly of the cut matching.

Keeping the labelled cut--join core is intentional: it makes the carrier
lossless before the later finite-set choices which replace literal component
subtypes by `Fin k` and split the boundary labels into numerical blocks.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace GlobalBridgeCut

noncomputable section

open PointedDecomposition LabelledCutJoin

universe uC

variable {Cell : Type uC} [Fintype Cell] [DecidableEq Cell]
  {facets : Cell → ℕ} {r : ℕ}

/-! ## Restricting a free ambient dart -/

/-- A free ambient dart whose cell lies in `S` is a free dart of the
restricted matching.  This is the boundary-level companion to
`ColoredMatching.restrict`. -/
def restrictBoundary
    (P : ColoredMatching (CellDart Cell facets) r) (S : Set Cell)
    (x : P.Boundary) (hx : x.1.1 ∈ S) : (P.restrict S).Boundary := by
  refine ⟨restrictDart S x.1 hx, ?_⟩
  intro hocc
  obtain ⟨e, he, hde⟩ :=
    ((P.restrict S).matching.mem_occupied_iff _).mp hocc
  apply x.2
  apply (P.matching.mem_occupied_iff x.1).mpr
  refine ⟨includeSeam (facets := facets) S e,
    (P.matching.mem_restrict_seams S e).mp he, ?_⟩
  exact Sym2.mem_map.mpr
    ⟨restrictDart S x.1 hx, hde, includeDart_restrictDart S x.1 hx⟩

@[simp]
theorem includeDart_restrictBoundary
    (P : ColoredMatching (CellDart Cell facets) r) (S : Set Cell)
    (x : P.Boundary) (hx : x.1.1 ∈ S) :
    includeDart (facets := facets) S (restrictBoundary P S x hx).1 = x.1 :=
  includeDart_restrictDart S x.1 hx

/-! ## The global bridge-cut carrier -/

/-- The complete concrete data retained by the global bridge cut.

`core` is the exact output of the labelled cut--join equivalence.  Thus
`core.1.1` is the erased coloured matching, `core.1.2.selected` is the
unordered exposed pair, `core.1.2.color` is the deleted colour, and `core.2`
is the old `Fin m` boundary labelling after that pair is rejoined.

The remaining fields expose the bridge decomposition rather than hiding it
inside `core`.  In particular the component boundary equivalence labels the
disjoint sum of the two literal component boundaries by `Fin (m+2)`.
-/
structure UnrootedBridgeCutCarrier (n h r m b : ℕ) where
  core : RejoinedBoundaryLabelledFreePair (Dart n h) r m
  orientation : Bool
  leftCells : Set (Fin n)
  rightCells : Set (Fin n)
  cover : leftCells ∪ rightCells = Set.univ
  disjoint : Disjoint leftCells rightCells
  noCrossing : NoCrossing core.1.1 leftCells rightCells
  leftConnected :
    (core.1.1.restrict leftCells).IsConnected
      (fun _ : leftCells ↦ h)
  rightConnected :
    (core.1.1.restrict rightCells).IsConnected
      (fun _ : rightCells ↦ h)
  leftStar : (core.1.1.restrict leftCells).Boundary
  rightStar : (core.1.1.restrict rightCells).Boundary
  exposedPair :
    s(includeDart (facets := fun _ : Fin n ↦ h) leftCells leftStar.1,
      includeDart (facets := fun _ : Fin n ↦ h) rightCells rightStar.1) =
      core.1.2.selected.pair
  componentBoundaryLabel :
    (core.1.1.restrict leftCells).Boundary ⊕
        (core.1.1.restrict rightCells).Boundary ≃ Fin (m + 2)
  leftRank : ℕ
  rightRank : ℕ
  leftRank_spec :
    (core.1.1.restrict leftCells).matching.seams.card + 1 =
      Nat.card leftCells + leftRank
  rightRank_spec :
    (core.1.1.restrict rightCells).matching.seams.card + 1 =
      Nat.card rightCells + rightRank
  ranks_add : leftRank + rightRank = b
  deletedColor : Fin r
  deletedColor_eq : deletedColor = core.1.2.color
  reassemble_exact :
    reassembleColored leftCells rightCells disjoint
      (core.1.1.restrict leftCells) (core.1.1.restrict rightCells) =
      core.1.1

/-! ## Forgetful projections and exact recovery -/

/-- Rejoin the selected exposed pair, recovering a marked
boundary-labelled object. -/
def recoverMarked (C : UnrootedBridgeCutCarrier n h r m b) :
    MarkedBoundaryLabelledPairing (Dart n h) r m :=
  joinLabelled C.core

/-- The old boundary allocation is retained literally in the core. -/
def oldBoundaryLabel (C : UnrootedBridgeCutCarrier n h r m b) :
    (ColoredMatching.joinSelected C.core.1).1.Boundary ≃ Fin m :=
  C.core.2

/-- The deleted seam colour is also a literal projection. -/
theorem deletedColor_is_core
    (C : UnrootedBridgeCutCarrier n h r m b) :
    C.deletedColor = C.core.1.2.color :=
  C.deletedColor_eq

/-- The two stored component restrictions recover the complete cut
matching, including all seam colours. -/
theorem recoverCutMatching
    (C : UnrootedBridgeCutCarrier n h r m b) :
    reassembleColored C.leftCells C.rightCells C.disjoint
      (C.core.1.1.restrict C.leftCells)
      (C.core.1.1.restrict C.rightCells) = C.core.1.1 :=
  C.reassemble_exact

/-! ## The concrete forward map -/

/-- Forget the bridge and proof fields while retaining the marked labelled
object and its orientation.  This encoding is injective because connectivity,
rank, and bridge fields are propositions. -/
def domainEncoding
    (z : UnrootedBridgePointed n h r m b × Bool) :
    MarkedBoundaryLabelledPairing (Dart n h) r m × Bool :=
  (⟨z.1.1.1.1.raw, z.1.1.2⟩, z.2)

theorem domainEncoding_injective :
    Function.Injective
      (domainEncoding : UnrootedBridgePointed n h r m b × Bool →
        MarkedBoundaryLabelledPairing (Dart n h) r m × Bool) := by
  rintro ⟨⟨⟨P, e⟩, hb⟩, o⟩ ⟨⟨⟨Q, f⟩, hb'⟩, o'⟩ heq
  have ho : o = o' := congrArg Prod.snd heq
  have hmarked :
      (⟨P.1.raw, e⟩ : MarkedBoundaryLabelledPairing (Dart n h) r m) =
        ⟨Q.1.raw, f⟩ := congrArg Prod.fst heq
  have hraw : P.1.raw = Q.1.raw := congrArg Sigma.fst hmarked
  have hdiagram : P.1 = Q.1 := ConnectedDiagram.raw_injective hraw
  have hstratum : P = Q := Subtype.ext hdiagram
  cases ho
  subst Q
  have hseam : e = f := by
    apply Subtype.ext
    exact congrArg (fun z ↦ z.2.1) hmarked
  subst f
  rfl

/-- Cut a bridge into the full global carrier.  The Boolean chooses which
endpoint-reachability class is called left; `false` uses `Sym2.out.1` and
`true` swaps the two sides. -/
def cutBridge
    (z : UnrootedBridgePointed n h r m b × Bool) :
    UnrootedBridgeCutCarrier n h r m b := by
  rcases z with ⟨⟨⟨P, e⟩, hbridge⟩, orientation⟩
  let A := P.1.raw
  let M := A.pairing
  let Q := M.erase e
  let C := M.bridge_partition e P.1.connected hbridge
  let S := BridgePartition.LeftClass (Q.Adjacent (fun _ : Fin n ↦ h))
    (M.leftCell e)
  let T := BridgePartition.RightClass (Q.Adjacent (fun _ : Fin n ↦ h))
    (M.rightCell e)
  letI := Classical.decPred (fun x ↦ x ∈ S)
  letI := Classical.decPred (fun x ↦ x ∈ T)
  let core := cutLabelled
    (⟨A, e⟩ : MarkedBoundaryLabelledPairing (Dart n h) r m)
  have hcoreQ : core.1.1 = Q := rfl
  have hstars := bridge_exposed_endpoints_on_opposite_sides
    M e P.1.connected hbridge
  have hrankExists :=
    erase_bridge_component_ranks M e P.1.connected hbridge
  let sRank : ℕ := Classical.choose hrankExists
  have htRankExists := Classical.choose_spec hrankExists
  let tRank : ℕ := Classical.choose htRankExists
  have hrankSpecs := Classical.choose_spec htRankExists
  have hsRank := hrankSpecs.1
  have htRank := hrankSpecs.2.1
  have hRanks := hrankSpecs.2.2
  have hCircuit : circuitRank M = b := by
    have hspec := circuitRank_spec M P.1.connected
    have hp := P.2
    simp only [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
      BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount,
      card_unrootedCell] at hp hspec
    have hpM : M.matching.seams.card + 1 = n + b := by
      simpa only [M, A] using hp
    omega
  have hRanksB : sRank + tRank = b := by
    simpa only [sRank, tRank] using hRanks.trans hCircuit
  have hsRankNat :
      (Q.restrict S).matching.seams.card + 1 = Nat.card S + sRank := by
    rw [Nat.card_eq_fintype_card]
    simpa only [Q, S, sRank] using hsRank
  have htRankNat :
      (Q.restrict T).matching.seams.card + 1 = Nat.card T + tRank := by
    rw [Nat.card_eq_fintype_card]
    simpa only [Q, T, tRank] using htRank
  cases orientation with
  | false =>
      let leftStar := restrictBoundary Q S
        (M.matching.leftBoundaryAfterErase e) hstars.1
      let rightStar := restrictBoundary Q T
        (M.matching.rightBoundaryAfterErase e) hstars.2
      refine
        { core := core
          orientation := false
          leftCells := S
          rightCells := T
          cover := C.cover
          disjoint := C.disjoint
          noCrossing := ?_
          leftConnected := bridge_left_restriction_connected Q _ _ C
          rightConnected := bridge_right_restriction_connected Q _ _ C
          leftStar := leftStar
          rightStar := rightStar
          exposedPair := ?_
          componentBoundaryLabel :=
            bridgeCutComponentBoundaryLabel A e P.1.connected hbridge
          leftRank := sRank
          rightRank := tRank
          leftRank_spec := by
            rw [hcoreQ]
            exact hsRankNat
          rightRank_spec := by
            rw [hcoreQ]
            exact htRankNat
          ranks_add := hRanksB
          deletedColor := M.color e
          deletedColor_eq := rfl
          reassemble_exact := ?_ }
      · intro u hu v hv
        exact C.no_left_right ⟨u, hu⟩ ⟨v, hv⟩
      · change
          s(includeDart (facets := fun _ : Fin n ↦ h) S leftStar.1,
            includeDart (facets := fun _ : Fin n ↦ h) T rightStar.1) = e.1
        simpa [leftStar, rightStar, Q, M,
          PartialMatching.leftBoundaryAfterErase,
          PartialMatching.rightBoundaryAfterErase,
          PartialMatching.endpointBoundaryAfterErase] using M.seam_out_repr e
      · change
          reassembleColored S T C.disjoint (Q.restrict S) (Q.restrict T) = Q
        exact erase_bridge_reassemble_exact M e P.1.connected hbridge
  | true =>
      let leftStar := restrictBoundary Q T
        (M.matching.rightBoundaryAfterErase e) hstars.2
      let rightStar := restrictBoundary Q S
        (M.matching.leftBoundaryAfterErase e) hstars.1
      refine
        { core := core
          orientation := true
          leftCells := T
          rightCells := S
          cover := by simpa [Set.union_comm] using C.cover
          disjoint := C.disjoint.symm
          noCrossing := ?_
          leftConnected := bridge_right_restriction_connected Q _ _ C
          rightConnected := bridge_left_restriction_connected Q _ _ C
          leftStar := leftStar
          rightStar := rightStar
          exposedPair := ?_
          componentBoundaryLabel :=
            (Equiv.sumComm _ _).trans
              (bridgeCutComponentBoundaryLabel A e P.1.connected hbridge)
          leftRank := tRank
          rightRank := sRank
          leftRank_spec := by
            rw [hcoreQ]
            exact htRankNat
          rightRank_spec := by
            rw [hcoreQ]
            exact hsRankNat
          ranks_add := by omega
          deletedColor := M.color e
          deletedColor_eq := rfl
          reassemble_exact := ?_ }
      · intro u hu v hv huv
        exact C.no_left_right ⟨v, hv⟩ ⟨u, hu⟩
          (Q.adjacent_symm (fun _ : Fin n ↦ h) huv)
      · change
          s(includeDart (facets := fun _ : Fin n ↦ h) T leftStar.1,
            includeDart (facets := fun _ : Fin n ↦ h) S rightStar.1) = e.1
        rw [Sym2.eq_swap]
        simpa [leftStar, rightStar, Q, M,
          PartialMatching.leftBoundaryAfterErase,
          PartialMatching.rightBoundaryAfterErase,
          PartialMatching.endpointBoundaryAfterErase] using M.seam_out_repr e
      · change
          reassembleColored T S C.disjoint.symm (Q.restrict T) (Q.restrict S) = Q
        apply Q.reassembleColored_restrict T S C.disjoint.symm
        intro seam hseam
        exact Or.symm (seam_internal_left_or_right Q S T C.cover
          (fun u hu v hv huv ↦
            C.no_left_right ⟨u, hu⟩ ⟨v, hv⟩ huv)
          seam hseam)

/-! ## Losslessness -/

@[simp]
theorem recoverMarked_cutBridge
    (z : UnrootedBridgePointed n h r m b × Bool) :
    recoverMarked (cutBridge z) = (domainEncoding z).1 := by
  rcases z with ⟨⟨⟨P, e⟩, hbridge⟩, orientation⟩
  cases orientation <;>
    exact joinLabelled_cutLabelled
      (⟨P.1.raw, e⟩ : MarkedBoundaryLabelledPairing (Dart n h) r m)

@[simp]
theorem cutBridge_orientation
    (z : UnrootedBridgePointed n h r m b × Bool) :
    (cutBridge z).orientation = z.2 := by
  rcases z with ⟨⟨⟨P, e⟩, hbridge⟩, orientation⟩
  cases orientation <;> simp [cutBridge]

/-- The global bridge cut loses no information.  This conclusion uses the
actual inverse law of labelled cut--join, not a cardinality certificate. -/
theorem cutBridge_injective :
    Function.Injective
      (cutBridge : UnrootedBridgePointed n h r m b × Bool →
        UnrootedBridgeCutCarrier n h r m b) := by
  intro x y hxy
  apply domainEncoding_injective
  apply Prod.ext
  · rw [← recoverMarked_cutBridge x, ← recoverMarked_cutBridge y, hxy]
  · change x.2 = y.2
    rw [← cutBridge_orientation x, ← cutBridge_orientation y, hxy]

/-- Exact equivalence with the realized image of the global carrier.  A
surjectivity theorem onto a numerical coproduct of standard `Fin k`
components is deliberately separate: it additionally requires choices of
cell reindexings and boundary-label blocks. -/
def cutBridgeEquivRange :
    (UnrootedBridgePointed n h r m b × Bool) ≃
      Set.range
        (cutBridge : UnrootedBridgePointed n h r m b × Bool →
          UnrootedBridgeCutCarrier n h r m b) :=
  Equiv.ofInjective cutBridge cutBridge_injective


end
end GlobalBridgeCut
end FacetPairing
end PolytopeCounting
