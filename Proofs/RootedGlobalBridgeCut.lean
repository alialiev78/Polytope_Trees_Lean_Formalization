module

public import Proofs.BridgeLabelledRestriction
public import Proofs.LabelledCutJoin
public import Proofs.CircuitRankComponents
public import Proofs.PointedDecomposition

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# A lossless global carrier for cutting a rooted bridge

This is the fixed-base analogue of the unrooted global bridge carrier.  The
component containing `baseCell n` is selected intrinsically.  Consequently
there is no Boolean orientation and no exchange of the two components.

The carrier retains the erased labelled cut--join core, both literal
component restrictions, their exposed stars, all boundary labels, the
deleted colour, additive circuit ranks, and exact colour-preserving
reassembly.  It also records the number of *ordinary* cells on the base
side in subtraction-free form

`card baseCells = baseOrdinaryCount + 1`.

Thus `baseOrdinaryCount = 0` is admitted: the distinguished base may be the
only cell on its side of the bridge.  This is the endpoint needed in the
rooted bridge convolution.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace RootedGlobalBridgeCut

noncomputable section

open PointedDecomposition LabelledCutJoin

/-! ## Restriction of a free ambient dart -/

/-- A free ambient dart whose cell belongs to a component becomes a free
dart of the restricted matching. -/
def restrictBoundary
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    {facets : Cell → ℕ} {r : ℕ}
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
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    {facets : Cell → ℕ} {r : ℕ}
    (P : ColoredMatching (CellDart Cell facets) r) (S : Set Cell)
    (x : P.Boundary) (hx : x.1.1 ∈ S) :
    includeDart (facets := facets) S (restrictBoundary P S x hx).1 = x.1 :=
  includeDart_restrictDart S x.1 hx

/-! ## The rooted global bridge-cut carrier -/

/-- Complete rooted bridge-cut data, canonically ordered by the distinguished
base cell.  `baseCells` contains `baseCell n`; `otherCells` cannot contain it.
No exchange bit occurs anywhere in the structure. -/
structure RootedBridgeCutCarrier (n h₀ h r m b : ℕ) where
  core : RejoinedBoundaryLabelledFreePair (RootedDart n h₀ h) r m
  baseCells : Set (RootedCell n)
  otherCells : Set (RootedCell n)
  cover : baseCells ∪ otherCells = Set.univ
  disjoint : Disjoint baseCells otherCells
  base_mem : baseCell n ∈ baseCells
  base_not_mem_other : baseCell n ∉ otherCells
  noCrossing : NoCrossing core.1.1 baseCells otherCells
  baseConnected :
    (core.1.1.restrict baseCells).IsConnected
      (fun c : baseCells ↦ rootedFacets h₀ h c.1)
  otherConnected :
    (core.1.1.restrict otherCells).IsConnected
      (fun c : otherCells ↦ rootedFacets h₀ h c.1)
  baseStar : (core.1.1.restrict baseCells).Boundary
  otherStar : (core.1.1.restrict otherCells).Boundary
  exposedPair :
    s(includeDart (facets := rootedFacets h₀ h) baseCells baseStar.1,
      includeDart (facets := rootedFacets h₀ h) otherCells otherStar.1) =
      core.1.2.selected.pair
  componentBoundaryLabel :
    (core.1.1.restrict baseCells).Boundary ⊕
        (core.1.1.restrict otherCells).Boundary ≃ Fin (m + 2)
  baseRank : ℕ
  otherRank : ℕ
  baseRank_spec :
    (core.1.1.restrict baseCells).matching.seams.card + 1 =
      Nat.card baseCells + baseRank
  otherRank_spec :
    (core.1.1.restrict otherCells).matching.seams.card + 1 =
      Nat.card otherCells + otherRank
  ranks_add : baseRank + otherRank = b
  baseOrdinaryCount : ℕ
  otherOrdinaryCount : ℕ
  baseOrdinaryCount_spec :
    Nat.card baseCells = baseOrdinaryCount + 1
  otherOrdinaryCount_spec :
    Nat.card otherCells = otherOrdinaryCount
  ordinaryCounts_add : baseOrdinaryCount + otherOrdinaryCount = n
  deletedColor : Fin r
  deletedColor_eq : deletedColor = core.1.2.color
  reassemble_exact :
    reassembleColored baseCells otherCells disjoint
      (core.1.1.restrict baseCells) (core.1.1.restrict otherCells) =
      core.1.1

/-! ## Numerical consequences, including the zero endpoint -/

/-- Ordinary cells lying in the intrinsically selected base component. -/
def baseOrdinaryCells
    (C : RootedBridgeCutCarrier n h₀ h r m b) : Set (Fin n) :=
  {i | Sum.inr i ∈ C.baseCells}

/-- Ordinary cells lying in the component away from the base. -/
def otherOrdinaryCells
    (C : RootedBridgeCutCarrier n h₀ h r m b) : Set (Fin n) :=
  {i | Sum.inr i ∈ C.otherCells}

/-- The base component is exactly the distinguished base together with its
ordinary cells. -/
def baseCellsEquiv
    (C : RootedBridgeCutCarrier n h₀ h r m b) :
    C.baseCells ≃ Unit ⊕ baseOrdinaryCells C := by
  refine
    { toFun := fun x ↦ by
        rcases x with ⟨u | i, hx⟩
        · exact Sum.inl u
        · exact Sum.inr ⟨i, hx⟩
      invFun := fun x ↦ match x with
        | Sum.inl u => ⟨Sum.inl u, by cases u; exact C.base_mem⟩
        | Sum.inr i => ⟨Sum.inr i.1, i.2⟩
      left_inv := by
        rintro ⟨x, hx⟩
        cases x with
        | inl u => cases u; rfl
        | inr i => rfl
      right_inv := by
        intro x
        cases x with
        | inl u => cases u; rfl
        | inr i => rfl }

/-- Every cell in the component away from the base is an ordinary cell.
The impossible base case is discharged by `base_not_mem_other`. -/
def otherCellsEquiv
    (C : RootedBridgeCutCarrier n h₀ h r m b) :
    C.otherCells ≃ otherOrdinaryCells C := by
  refine
    { toFun := fun x ↦ by
        rcases x with ⟨u | i, hx⟩
        · cases u
          exact False.elim (C.base_not_mem_other hx)
        · exact ⟨i, hx⟩
      invFun := fun i ↦ ⟨Sum.inr i.1, i.2⟩
      left_inv := by
        rintro ⟨x, hx⟩
        cases x with
        | inl u =>
            cases u
            exact False.elim (C.base_not_mem_other hx)
        | inr i => rfl
      right_inv := by
        rintro ⟨i, hi⟩
        rfl }

/-- The two ordinary-cell subsets form a partition of `Fin n`. -/
theorem ordinaryCells_cover
    (C : RootedBridgeCutCarrier n h₀ h r m b) :
    baseOrdinaryCells C ∪ otherOrdinaryCells C = Set.univ := by
  ext i
  have hi : (Sum.inr i : RootedCell n) ∈ C.baseCells ∪ C.otherCells := by
    rw [C.cover]
    exact Set.mem_univ _
  simpa only [baseOrdinaryCells, otherOrdinaryCells, Set.mem_union,
    Set.mem_setOf_eq, Set.mem_univ, iff_true] using hi

theorem ordinaryCells_disjoint
    (C : RootedBridgeCutCarrier n h₀ h r m b) :
    Disjoint (baseOrdinaryCells C) (otherOrdinaryCells C) := by
  rw [Set.disjoint_left]
  intro i hiBase hiOther
  exact Set.disjoint_left.mp C.disjoint hiBase hiOther

/-- The stored base-side number really is the cardinality of its ordinary
cell subset, including when that subset is empty. -/
theorem card_baseOrdinaryCells
    (C : RootedBridgeCutCarrier n h₀ h r m b) :
    Nat.card (baseOrdinaryCells C) = C.baseOrdinaryCount := by
  have heq := Nat.card_congr (baseCellsEquiv C)
  have hunit : Nat.card Unit = 1 := by simp
  rw [Nat.card_sum, hunit] at heq
  have hspec := C.baseOrdinaryCount_spec
  omega

theorem card_otherOrdinaryCells
    (C : RootedBridgeCutCarrier n h₀ h r m b) :
    Nat.card (otherOrdinaryCells C) = C.otherOrdinaryCount := by
  rw [← C.otherOrdinaryCount_spec]
  exact (Nat.card_congr (otherCellsEquiv C)).symm

theorem baseOrdinaryCount_le
    (C : RootedBridgeCutCarrier n h₀ h r m b) :
    C.baseOrdinaryCount ≤ n := by
  have h := C.ordinaryCounts_add
  omega

theorem otherOrdinaryCount_le
    (C : RootedBridgeCutCarrier n h₀ h r m b) :
    C.otherOrdinaryCount ≤ n := by
  have h := C.ordinaryCounts_add
  omega

/-- The component away from the base contains the endpoint star and hence at
least one ordinary cell.  Only the base-side count is allowed to be zero. -/
theorem otherOrdinaryCount_pos
    (C : RootedBridgeCutCarrier n h₀ h r m b) :
    0 < C.otherOrdinaryCount := by
  have hnonempty : Nonempty C.otherCells :=
    ⟨C.otherStar.1.1⟩
  letI : Nonempty C.otherCells := hnonempty
  have hcard : 0 < Nat.card C.otherCells := Finite.card_pos
  rwa [C.otherOrdinaryCount_spec] at hcard

/-- Accordingly the canonical rooted convolution index ranges over
`0 ≤ ℓ < n`; in particular its lower endpoint is not discarded. -/
theorem baseOrdinaryCount_lt
    (C : RootedBridgeCutCarrier n h₀ h r m b) :
    C.baseOrdinaryCount < n := by
  have hadd := C.ordinaryCounts_add
  have hpos := otherOrdinaryCount_pos C
  omega

/-- The lower endpoint `ℓ = 0` is represented exactly by a base component
containing one cell (the distinguished base) and no ordinary cells. -/
theorem baseOrdinaryCount_eq_zero_iff
    (C : RootedBridgeCutCarrier n h₀ h r m b) :
    C.baseOrdinaryCount = 0 ↔ Nat.card C.baseCells = 1 := by
  have h := C.baseOrdinaryCount_spec
  omega

/-! ## Recovery projections -/

/-- Rejoining the selected exposed pair recovers the marked rooted object. -/
def recoverMarked (C : RootedBridgeCutCarrier n h₀ h r m b) :
    MarkedBoundaryLabelledPairing (RootedDart n h₀ h) r m :=
  joinLabelled C.core

/-- The original `Fin m` boundary allocation is retained literally. -/
def oldBoundaryLabel (C : RootedBridgeCutCarrier n h₀ h r m b) :
    (ColoredMatching.joinSelected C.core.1).1.Boundary ≃ Fin m :=
  C.core.2

theorem deletedColor_is_core
    (C : RootedBridgeCutCarrier n h₀ h r m b) :
    C.deletedColor = C.core.1.2.color :=
  C.deletedColor_eq

theorem recoverCutMatching
    (C : RootedBridgeCutCarrier n h₀ h r m b) :
    reassembleColored C.baseCells C.otherCells C.disjoint
      (C.core.1.1.restrict C.baseCells)
      (C.core.1.1.restrict C.otherCells) = C.core.1.1 :=
  C.reassemble_exact

/-! ## The intrinsic forward cut -/

/-- Forget the bridge, connectedness, and rank proofs while retaining the
marked rooted boundary-labelled object. -/
def domainEncoding (z : RootedBridgePointed n h₀ h r m b) :
    MarkedBoundaryLabelledPairing (RootedDart n h₀ h) r m :=
  ⟨z.1.1.1.raw, z.1.2⟩

theorem domainEncoding_injective :
    Function.Injective
      (domainEncoding : RootedBridgePointed n h₀ h r m b →
        MarkedBoundaryLabelledPairing (RootedDart n h₀ h) r m) := by
  rintro ⟨⟨P, e⟩, hb⟩ ⟨⟨Q, f⟩, hb'⟩ heq
  have hraw : P.1.raw = Q.1.raw := congrArg Sigma.fst heq
  have hdiagram : P.1 = Q.1 := ConnectedDiagram.raw_injective hraw
  have hstratum : P = Q := Subtype.ext hdiagram
  subst Q
  have hseam : e = f := by
    apply Subtype.ext
    exact congrArg (fun z ↦ z.2.1) heq
  subst f
  rfl

/-- Cut a rooted bridge and order its components intrinsically: whichever
endpoint class contains `baseCell n` becomes `baseCells`. -/
def cutBridge (z : RootedBridgePointed n h₀ h r m b) :
    RootedBridgeCutCarrier n h₀ h r m b := by
  rcases z with ⟨⟨P, e⟩, hbridge⟩
  let A := P.1.raw
  let M := A.pairing
  let Q := M.erase e
  let C := M.bridge_partition e P.1.connected hbridge
  let S := BridgePartition.LeftClass
    (Q.Adjacent (rootedFacets h₀ h)) (M.leftCell e)
  let T := BridgePartition.RightClass
    (Q.Adjacent (rootedFacets h₀ h)) (M.rightCell e)
  letI := Classical.decPred (fun x ↦ x ∈ S)
  letI := Classical.decPred (fun x ↦ x ∈ T)
  let core := cutLabelled
    (⟨A, e⟩ : MarkedBoundaryLabelledPairing (RootedDart n h₀ h) r m)
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
      card_rootedCell] at hp hspec
    have hpM : M.matching.seams.card + 1 = n + 1 + b := by
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
  have hCardSum : Nat.card S + Nat.card T = n + 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simpa only [card_rootedCell] using BridgePartition.class_sizes_add C
  have hSpos : 0 < Nat.card S := by
    rw [Nat.card_eq_fintype_card]
    exact BridgePartition.left_class_size_pos
  have hTpos : 0 < Nat.card T := by
    rw [Nat.card_eq_fintype_card]
    exact BridgePartition.right_class_size_pos
  by_cases hbaseS : baseCell n ∈ S
  · let baseStar := restrictBoundary Q S
      (M.matching.leftBoundaryAfterErase e) hstars.1
    let otherStar := restrictBoundary Q T
      (M.matching.rightBoundaryAfterErase e) hstars.2
    refine
      { core := core
        baseCells := S
        otherCells := T
        cover := C.cover
        disjoint := C.disjoint
        base_mem := hbaseS
        base_not_mem_other := fun hbT ↦
          Set.disjoint_left.mp C.disjoint hbaseS hbT
        noCrossing := ?_
        baseConnected := bridge_left_restriction_connected Q _ _ C
        otherConnected := bridge_right_restriction_connected Q _ _ C
        baseStar := baseStar
        otherStar := otherStar
        exposedPair := ?_
        componentBoundaryLabel :=
          bridgeCutComponentBoundaryLabel A e P.1.connected hbridge
        baseRank := sRank
        otherRank := tRank
        baseRank_spec := by rw [hcoreQ]; exact hsRankNat
        otherRank_spec := by rw [hcoreQ]; exact htRankNat
        ranks_add := hRanksB
        baseOrdinaryCount := Nat.card S - 1
        otherOrdinaryCount := Nat.card T
        baseOrdinaryCount_spec := by omega
        otherOrdinaryCount_spec := rfl
        ordinaryCounts_add := by omega
        deletedColor := M.color e
        deletedColor_eq := rfl
        reassemble_exact := ?_ }
    · intro u hu v hv
      exact C.no_left_right ⟨u, hu⟩ ⟨v, hv⟩
    · change
        s(includeDart (facets := rootedFacets h₀ h) S baseStar.1,
          includeDart (facets := rootedFacets h₀ h) T otherStar.1) = e.1
      simpa [baseStar, otherStar, Q, M,
        PartialMatching.leftBoundaryAfterErase,
        PartialMatching.rightBoundaryAfterErase,
        PartialMatching.endpointBoundaryAfterErase] using M.seam_out_repr e
    · change
        reassembleColored S T C.disjoint (Q.restrict S) (Q.restrict T) = Q
      exact erase_bridge_reassemble_exact M e P.1.connected hbridge
  · have hbaseT : baseCell n ∈ T := by
      have hb : baseCell n ∈ S ∪ T := by rw [C.cover]; exact Set.mem_univ _
      exact (by simpa only [Set.mem_union] using hb :
        baseCell n ∈ S ∨ baseCell n ∈ T) |>.resolve_left hbaseS
    let baseStar := restrictBoundary Q T
      (M.matching.rightBoundaryAfterErase e) hstars.2
    let otherStar := restrictBoundary Q S
      (M.matching.leftBoundaryAfterErase e) hstars.1
    refine
      { core := core
        baseCells := T
        otherCells := S
        cover := by simpa [Set.union_comm] using C.cover
        disjoint := C.disjoint.symm
        base_mem := hbaseT
        base_not_mem_other := hbaseS
        noCrossing := ?_
        baseConnected := bridge_right_restriction_connected Q _ _ C
        otherConnected := bridge_left_restriction_connected Q _ _ C
        baseStar := baseStar
        otherStar := otherStar
        exposedPair := ?_
        componentBoundaryLabel :=
          (Equiv.sumComm _ _).trans
            (bridgeCutComponentBoundaryLabel A e P.1.connected hbridge)
        baseRank := tRank
        otherRank := sRank
        baseRank_spec := by rw [hcoreQ]; exact htRankNat
        otherRank_spec := by rw [hcoreQ]; exact hsRankNat
        ranks_add := by omega
        baseOrdinaryCount := Nat.card T - 1
        otherOrdinaryCount := Nat.card S
        baseOrdinaryCount_spec := by omega
        otherOrdinaryCount_spec := rfl
        ordinaryCounts_add := by omega
        deletedColor := M.color e
        deletedColor_eq := rfl
        reassemble_exact := ?_ }
    · intro u hu v hv huv
      exact C.no_left_right ⟨v, hv⟩ ⟨u, hu⟩
        (Q.adjacent_symm (rootedFacets h₀ h) huv)
    · change
        s(includeDart (facets := rootedFacets h₀ h) T baseStar.1,
          includeDart (facets := rootedFacets h₀ h) S otherStar.1) = e.1
      rw [Sym2.eq_swap]
      simpa [baseStar, otherStar, Q, M,
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

/-! ## Exact losslessness -/

@[simp]
theorem recoverMarked_cutBridge
    (z : RootedBridgePointed n h₀ h r m b) :
    recoverMarked (cutBridge z) = domainEncoding z := by
  rcases z with ⟨⟨P, e⟩, hbridge⟩
  simp only [recoverMarked, domainEncoding]
  unfold cutBridge
  dsimp only
  split <;>
    exact joinLabelled_cutLabelled
      (⟨P.1.raw, e⟩ : MarkedBoundaryLabelledPairing (RootedDart n h₀ h) r m)

/-- The rooted global bridge cut loses no information.  Unlike the unrooted
carrier, the proof does not recover an orientation bit because none exists. -/
theorem cutBridge_injective :
    Function.Injective
      (cutBridge : RootedBridgePointed n h₀ h r m b →
        RootedBridgeCutCarrier n h₀ h r m b) := by
  intro x y hxy
  apply domainEncoding_injective
  rw [← recoverMarked_cutBridge x, ← recoverMarked_cutBridge y, hxy]

/-- Exact equivalence with the realized image of the rooted global carrier. -/
def cutBridgeEquivRange :
    RootedBridgePointed n h₀ h r m b ≃
      Set.range
        (cutBridge : RootedBridgePointed n h₀ h r m b →
          RootedBridgeCutCarrier n h₀ h r m b) :=
  Equiv.ofInjective cutBridge cutBridge_injective


end
end RootedGlobalBridgeCut
end FacetPairing
end PolytopeCounting
