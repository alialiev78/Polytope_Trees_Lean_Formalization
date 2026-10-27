module

public import Proofs.NonbridgeEquiv

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# The fixed-base nonbridge cut--join equivalence

This is the rooted analogue of `NonbridgeEquiv`.  The distinguished base
cell is never renamed or removed: cutting a marked nonbridge seam keeps the
same `RootedCell n` carrier, lowers circuit rank by one, and exposes two new
boundary darts.  A `Bool` records the orientation of those exposed ends.

The proof is an equivalence of the actual finite carrier types.  It uses the
concrete labelled cut--join inverse for the lossless part and the elementary
factor-two boundary-label equivalence for the final change of presentation.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNonbridgeEquiv

noncomputable section

open PointedDecomposition
open LabelledCutJoin

noncomputable local instance rootedStratumFintype
    (n h₀ h r m b : ℕ) : Fintype (RootedStratum n h₀ h r m b) :=
  Fintype.ofFinite _

noncomputable local instance rootedNonbridgePointedFintype
    (n h₀ h r m b : ℕ) :
    Fintype (RootedNonbridgePointed n h₀ h r m b) :=
  Fintype.ofFinite _

/-! ## A lossless rooted cut carrier -/

/-- The exact data left after cutting a rooted nonbridge seam.  Connectivity
and rank are stated on the literal fixed-base cell carrier. -/
abbrev RootedNonbridgeCutCarrier
    (n h₀ h r m b : ℕ) :=
  {w : RejoinedBoundaryLabelledFreePair (RootedDart n h₀ h) r m //
    w.1.1.IsConnected (rootedFacets h₀ h) ∧
      w.1.1.edgeCount + 1 = Fintype.card (RootedCell n) + b} × Bool

/-- Forget proof fields while retaining the marked rooted pairing and the
orientation of its marked seam. -/
def domainEncoding
    (z : RootedNonbridgePointed n h₀ h r m (b + 1) × Bool) :
    MarkedBoundaryLabelledPairing (RootedDart n h₀ h) r m × Bool :=
  (⟨z.1.1.1.1.raw, z.1.1.2⟩, z.2)

theorem domainEncoding_injective :
    Function.Injective
      (domainEncoding :
        RootedNonbridgePointed n h₀ h r m (b + 1) × Bool →
          MarkedBoundaryLabelledPairing (RootedDart n h₀ h) r m × Bool) := by
  rintro ⟨⟨⟨P, e⟩, hn⟩, o⟩ ⟨⟨⟨Q, f⟩, hm⟩, o'⟩ heq
  have ho : o = o' := congrArg Prod.snd heq
  have hmarked :
      (⟨P.1.raw, e⟩ :
        MarkedBoundaryLabelledPairing (RootedDart n h₀ h) r m) =
        ⟨Q.1.raw, f⟩ := congrArg Prod.fst heq
  have hraw : P.1.raw = Q.1.raw :=
    congrArg (fun z ↦ z.1) hmarked
  have hdiagram : P.1 = Q.1 := ConnectedDiagram.raw_injective hraw
  have hstratum : P = Q := Subtype.ext hdiagram
  cases ho
  subst Q
  have hseam : e = f := by
    apply Subtype.ext
    exact congrArg (fun z ↦ z.2.1) hmarked
  subst f
  rfl

/-- Forget only the proof that the cut object is in the rooted lower
stratum. -/
def carrierEncoding
    (z : RootedNonbridgeCutCarrier n h₀ h r m b) :
    RejoinedBoundaryLabelledFreePair (RootedDart n h₀ h) r m × Bool :=
  (z.1.1, z.2)

theorem carrierEncoding_injective :
    Function.Injective
      (carrierEncoding : RootedNonbridgeCutCarrier n h₀ h r m b →
        RejoinedBoundaryLabelledFreePair (RootedDart n h₀ h) r m × Bool) := by
  rintro ⟨x, o⟩ ⟨y, o'⟩ hxy
  have hw : x.1 = y.1 := congrArg Prod.fst hxy
  have ho : o = o' := congrArg Prod.snd hxy
  cases ho
  cases Subtype.ext hw
  rfl

/-- Concrete cutting into the lossless rooted carrier. -/
def toCutCarrier
    (z : RootedNonbridgePointed n h₀ h r m (b + 1) × Bool) :
    RootedNonbridgeCutCarrier n h₀ h r m b := by
  let S : RootedStratum n h₀ h r m (b + 1) := z.1.1.1
  let e : S.1.raw.pairing.Seam := z.1.1.2
  let w := cutLabelled
    (⟨S.1.raw, e⟩ :
      MarkedBoundaryLabelledPairing (RootedDart n h₀ h) r m)
  refine ⟨⟨w, ?_, ?_⟩, z.2⟩
  · change (S.1.raw.pairing.erase e).IsConnected (rootedFacets h₀ h)
    exact z.1.2
  · change (S.1.raw.pairing.erase e).edgeCount + 1 =
      Fintype.card (RootedCell n) + b
    exact NonbridgeCut.rooted_rank_after_erase S e

/-- Rejoin a lossless rooted cut carrier.  Adding the marked seam preserves
connectivity, and the erase-cardinality identity restores rank `b+1`. -/
def fromCutCarrier
    (z : RootedNonbridgeCutCarrier n h₀ h r m b) :
    RootedNonbridgePointed n h₀ h r m (b + 1) × Bool := by
  let w : RejoinedBoundaryLabelledFreePair (RootedDart n h₀ h) r m := z.1.1
  let a : MarkedBoundaryLabelledPairing (RootedDart n h₀ h) r m :=
    joinLabelled w
  have hcut : cutLabelled a = w := cutLabelled_joinLabelled w
  have herase : a.1.pairing.erase a.2 = w.1.1 := by
    have h := congrArg (fun y ↦ y.1.1) hcut
    exact h
  have heraseConnected :
      (a.1.pairing.erase a.2).IsConnected (rootedFacets h₀ h) := by
    rw [herase]
    exact z.1.2.1
  have hconnected : a.1.pairing.IsConnected (rootedFacets h₀ h) :=
    NonbridgeEquiv.connected_of_erase_connected
      a.1.pairing a.2 heraseConnected
  let P : RootedDiagram n h₀ h r m :=
    { raw := a.1
      connected := hconnected }
  have hrank : P.HasCircuitRank (b + 1) := by
    have hafter := z.1.2.2
    have hcard := a.1.pairing.matching.card_seams_erase a.2
    rw [← herase] at hafter
    simp only [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
      BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount]
    simp only [ColoredMatching.edgeCount] at hafter
    change a.1.pairing.matching.seams.card + 1 =
      Fintype.card (RootedCell n) + (b + 1)
    change (a.1.pairing.matching.erase a.2).seams.card + 1 =
      Fintype.card (RootedCell n) + b at hafter
    omega
  let S : RootedStratum n h₀ h r m (b + 1) := ⟨P, hrank⟩
  have hnonbridge : S.1.raw.pairing.IsNonbridge a.2 := heraseConnected
  exact (⟨⟨S, a.2⟩, hnonbridge⟩, z.2)

theorem fromCutCarrier_toCutCarrier
    (z : RootedNonbridgePointed n h₀ h r m (b + 1) × Bool) :
    fromCutCarrier (toCutCarrier z) = z := by
  apply domainEncoding_injective
  have hcore := joinLabelled_cutLabelled
    (⟨z.1.1.1.1.raw, z.1.1.2⟩ :
      MarkedBoundaryLabelledPairing (RootedDart n h₀ h) r m)
  apply Prod.ext
  · exact hcore
  · rfl

theorem toCutCarrier_fromCutCarrier
    (z : RootedNonbridgeCutCarrier n h₀ h r m b) :
    toCutCarrier (fromCutCarrier z) = z := by
  apply carrierEncoding_injective
  have hcore := cutLabelled_joinLabelled z.1.1
  apply Prod.ext
  · exact hcore
  · rfl

/-- Exact fixed-base nonbridge cut equivalence before changing the join-data
presentation to a full boundary label. -/
def rootedNonbridgePointedEquivCutCarrier :
    (RootedNonbridgePointed n h₀ h r m (b + 1) × Bool) ≃
      RootedNonbridgeCutCarrier n h₀ h r m b where
  toFun := toCutCarrier
  invFun := fromCutCarrier
  left_inv := fromCutCarrier_toCutCarrier
  right_inv := toCutCarrier_fromCutCarrier

/-! ## Factor two and the ordinary rooted lower stratum -/

/-- The cut rooted carrier has exactly the two new boundary darts in
addition to the `m` darts surviving the rejoin. -/
theorem cutCarrier_boundary_card
    (z : RootedNonbridgeCutCarrier n h₀ h r m b) :
    Fintype.card z.1.1.1.1.Boundary = m + 2 := by
  let Q := z.1.1.1.1
  let p := z.1.1.1.2.selected
  have hjoin := FactorTwoCounting.card_boundary_joinFreePair Q.matching p
  have hlabel :
      Fintype.card (Q.matching.joinFreePair p).Boundary = m := by
    change Fintype.card ((ColoredMatching.joinSelected z.1.1.1).1).Boundary = m
    exact (Fintype.card_congr z.1.1.2).trans (Fintype.card_fin m)
  rw [hlabel] at hjoin
  exact hjoin.symm

/-- An unlabelled lower rooted matching with its connectivity, rank, and
boundary-cardinality equations. -/
abbrev RootedLowerCore (n h₀ h r m b : ℕ) :=
  {Q : ColoredMatching (RootedDart n h₀ h) r //
    Q.IsConnected (rootedFacets h₀ h) ∧
      Q.edgeCount + 1 = Fintype.card (RootedCell n) + b ∧
      Fintype.card Q.Boundary = m + 2}

/-- Join data over an unlabelled fixed-base lower matching. -/
abbrev RootedJoinDataCarrier (n h₀ h r m b : ℕ) :=
  Σ Q : RootedLowerCore n h₀ h r m b,
    FactorTwoCounting.LabelledJoinData Q.1.matching m × Fin r

/-- Full boundary labels over the same fixed-base lower matching. -/
abbrev RootedFullLabelCarrier (n h₀ h r m b : ℕ) :=
  Σ Q : RootedLowerCore n h₀ h r m b,
    (Q.1.Boundary ≃ Fin (m + 2)) × Fin r

/-- Reassociate the lossless rooted cut carrier into factor-two fibres. -/
def cutCarrierEquivJoinData :
    RootedNonbridgeCutCarrier n h₀ h r m b ≃
      RootedJoinDataCarrier n h₀ h r m b where
  toFun z := by
    let w := z.1.1
    let Q := w.1.1
    let d := w.1.2
    exact ⟨⟨Q, z.1.2.1, z.1.2.2, cutCarrier_boundary_card z⟩,
      (⟨d.selected, (w.2, z.2)⟩, d.color)⟩
  invFun z := by
    rcases z with ⟨Q, jd, c⟩
    rcases jd with ⟨p, label, orientation⟩
    let d : Q.1.FreePairDatum := ⟨p, c⟩
    let w : RejoinedBoundaryLabelledFreePair (RootedDart n h₀ h) r m :=
      ⟨⟨Q.1, d⟩, label⟩
    exact (⟨w, Q.2.1, Q.2.2.1⟩, orientation)
  left_inv := by
    rintro ⟨⟨⟨⟨Q, d⟩, label⟩, hp⟩, orientation⟩
    rfl
  right_inv := by
    rintro ⟨Q, ⟨p, label, orientation⟩, c⟩
    rfl

/-- Apply the factor-two boundary-labelling equivalence independently over
each rooted lower matching. -/
def joinDataEquivFullLabels :
    RootedJoinDataCarrier n h₀ h r m b ≃
      RootedFullLabelCarrier n h₀ h r m b :=
  Equiv.sigmaCongrRight (fun Q ↦
    FactorTwoCounting.colouredLabelledJoinDataEquiv
      Q.1.matching m r Q.2.2.2)

/-- Package a fully labelled fixed-base lower matching as an ordinary rooted
stratum object. -/
def fullLabelsToLower
    (z : RootedFullLabelCarrier n h₀ h r m b) :
    RootedStratum n h₀ h r (m + 2) b × Fin r := by
  rcases z with ⟨Q, label, c⟩
  let raw : RootedPairing n h₀ h r (m + 2) :=
    { pairing := Q.1
      label := label }
  let diagram : RootedDiagram n h₀ h r (m + 2) :=
    { raw := raw
      connected := Q.2.1 }
  have hrank : diagram.HasCircuitRank b := by
    simpa [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
      BoundaryLabelledPairing.edgeCount] using Q.2.2.1
  exact (⟨diagram, hrank⟩, c)

/-- Forget the lower boundary label while retaining its cardinality proof. -/
def lowerToFullLabels
    (z : RootedStratum n h₀ h r (m + 2) b × Fin r) :
    RootedFullLabelCarrier n h₀ h r m b := by
  let S := z.1
  let Q := S.1.raw.pairing
  have hrank : Q.edgeCount + 1 = Fintype.card (RootedCell n) + b := by
    simpa [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
      BoundaryLabelledPairing.edgeCount] using S.2
  have hboundary : Fintype.card Q.Boundary = m + 2 := by
    simpa using Fintype.card_congr S.1.raw.label
  exact ⟨⟨Q, S.1.connected, hrank, hboundary⟩,
    S.1.raw.label, z.2⟩

theorem lowerToFullLabels_fullLabelsToLower
    (z : RootedFullLabelCarrier n h₀ h r m b) :
    lowerToFullLabels (fullLabelsToLower z) = z := by
  rcases z with ⟨⟨Q, hp⟩, label, c⟩
  rfl

theorem fullLabelsToLower_lowerToFullLabels
    (z : RootedStratum n h₀ h r (m + 2) b × Fin r) :
    fullLabelsToLower (lowerToFullLabels z) = z := by
  rcases z with ⟨⟨⟨raw, hconnected⟩, hrank⟩, c⟩
  rcases raw with ⟨Q, label⟩
  rfl

/-- Exact equivalence between full-label carrier data and the ordinary
fixed-base lower stratum. -/
def fullLabelCarrierEquivLower :
    RootedFullLabelCarrier n h₀ h r m b ≃
      (RootedStratum n h₀ h r (m + 2) b × Fin r) where
  toFun := fullLabelsToLower
  invFun := lowerToFullLabels
  left_inv := lowerToFullLabels_fullLabelsToLower
  right_inv := fullLabelsToLower_lowerToFullLabels

/-- The unconditional fixed-base nonbridge cut--join equivalence.  The base
cell and all its darts remain part of the carrier throughout. -/
def rootedNonbridgeEquiv :
    (RootedNonbridgePointed n h₀ h r m (b + 1) × Bool) ≃
      (RootedStratum n h₀ h r (m + 2) b × Fin r) :=
  rootedNonbridgePointedEquivCutCarrier.trans <|
    cutCarrierEquivJoinData.trans <|
      joinDataEquivFullLabels.trans fullLabelCarrierEquivLower

/-- Cardinal form of the rooted nonbridge term, valid without positivity or
admissibility hypotheses and including `m=0`, `r=0`, and empty strata. -/
theorem card_rootedNonbridge_mul_two
    (n h₀ h r m b : ℕ) :
    2 * Fintype.card (RootedNonbridgePointed n h₀ h r m (b + 1)) =
      r * Fintype.card (RootedStratum n h₀ h r (m + 2) b) := by
  have hcard := Fintype.card_congr
    (rootedNonbridgeEquiv
      (n := n) (h₀ := h₀) (h := h) (r := r) (m := m) (b := b))
  simpa [Fintype.card_prod, Nat.mul_comm] using hcard


end
end RootedNonbridgeEquiv
end FacetPairing
end PolytopeCounting
