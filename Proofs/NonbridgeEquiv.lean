module

public import Proofs.NonbridgeCut
public import Proofs.LabelledCutJoin
public import Proofs.BoundaryCut
public import Proofs.FactorTwoCounting

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# The nonbridge cut--join equivalence

This file constructs the inverse direction of `NonbridgeCut.cutUnrooted`.
The two boundary labels `m` and `m+1` select the free pair to be joined;
the remaining boundary labels restrict, without any quotient or freeness
assumption, to a `Fin m` labelling after the join.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace NonbridgeEquiv

noncomputable section

open PointedDecomposition
open LabelledCutJoin

universe uD

variable {D : Type uD} [DecidableEq D] {r m : ℕ}

noncomputable local instance unrootedStratumFintype
    (n h r m b : ℕ) : Fintype (UnrootedStratum n h r m b) :=
  Fintype.ofFinite _

noncomputable local instance unrootedNonbridgePointedFintype
    (n h r m b : ℕ) :
    Fintype (UnrootedNonbridgePointed n h r m b) :=
  Fintype.ofFinite _

/-- A dart remains free after joining a selected free pair exactly when it
was free before and is not one of the two selected darts. -/
theorem boundary_joinFreePair_iff
    (P : ColoredMatching D r) (p : P.FreePairDatum) (d : D) :
    d ∉ (P.joinFreePair p).matching.occupied ↔
      d ∉ P.matching.occupied ∧ d ∉ p.selected.pair := by
  constructor
  · intro h
    constructor
    · intro hold
      apply h
      rw [PartialMatching.mem_occupied_iff]
      obtain ⟨e, he, hde⟩ :=
        (PartialMatching.mem_occupied_iff P.matching d).mp hold
      refine ⟨e, ?_, hde⟩
      exact Finset.mem_insert_of_mem he
    · intro hpair
      apply h
      rw [PartialMatching.mem_occupied_iff]
      refine ⟨p.selected.pair, ?_, hpair⟩
      change p.selected.pair ∈
        (P.matching.join
          (p.selected.left P.matching) (p.selected.right P.matching)
          (p.selected.left_ne_right P.matching)).seams
      rw [PartialMatching.seams_join]
      simpa only [PartialMatching.FreePair.joinPair_left_right] using
        (Finset.mem_insert_self p.selected.pair P.matching.seams)
  · rintro ⟨hold, hpair⟩ hocc
    rw [PartialMatching.mem_occupied_iff] at hocc
    obtain ⟨e, he, hde⟩ := hocc
    change e ∈
      (P.matching.join
        (p.selected.left P.matching) (p.selected.right P.matching)
        (p.selected.left_ne_right P.matching)).seams at he
    rw [PartialMatching.seams_join,
      p.selected.joinPair_left_right P.matching] at he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hpair hde
    · exact hold ((PartialMatching.mem_occupied_iff P.matching d).mpr
        ⟨e, he, hde⟩)

/-! ## Removing the two star labels -/

/-- The coloured matching obtained by joining the two boundary darts carrying
the two reserved star labels. -/
def joinStarsPairing
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r) :
    ColoredMatching D r :=
  Q.pairing.joinFreePair (starFreePairDatum Q c)

/-- A boundary dart after the star join, viewed as a boundary dart before the
join. -/
def joinedBoundaryAsOld
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r)
    (x : (joinStarsPairing Q c).Boundary) : Q.pairing.Boundary :=
  ⟨x.1, (boundary_joinFreePair_iff Q.pairing
    (starFreePairDatum Q c) x.1).mp x.2 |>.1⟩

theorem joinedBoundaryAsOld_not_starPair
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r)
    (x : (joinStarsPairing Q c).Boundary) :
    (joinedBoundaryAsOld Q c x).1 ∉ (starFreePair Q).pair := by
  exact (boundary_joinFreePair_iff Q.pairing
    (starFreePairDatum Q c) x.1).mp x.2 |>.2

/-- The old label of a boundary dart which survives the star join is strictly
below `m`; it cannot be either of the two star labels. -/
theorem joinedBoundary_label_lt
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r)
    (x : (joinStarsPairing Q c).Boundary) :
    (Q.label (joinedBoundaryAsOld Q c x)).val < m := by
  let q := joinedBoundaryAsOld Q c x
  have hnot : q.1 ∉ (starFreePair Q).pair :=
    joinedBoundaryAsOld_not_starPair Q c x
  have hfirst : Q.label q ≠ firstStar m := by
    intro h
    apply hnot
    rw [starFreePair_pair, Sym2.mem_iff]
    left
    have hq : q = firstStarDart Q := by
      apply Q.label.injective
      simpa only [firstStarDart, Equiv.apply_symm_apply] using h
    exact congrArg Subtype.val hq
  have hsecond : Q.label q ≠ secondStar m := by
    intro h
    apply hnot
    rw [starFreePair_pair, Sym2.mem_iff]
    right
    have hq : q = secondStarDart Q := by
      apply Q.label.injective
      simpa only [secondStarDart, Equiv.apply_symm_apply] using h
    exact congrArg Subtype.val hq
  have hvfirst : (Q.label q).val ≠ m := by
    intro hv
    apply hfirst
    apply Fin.eq_of_val_eq
    simpa [firstStar] using hv
  have hvsecond : (Q.label q).val ≠ m + 1 := by
    intro hv
    apply hsecond
    apply Fin.eq_of_val_eq
    simpa [secondStar] using hv
  have hlt := (Q.label q).isLt
  change (Q.label q).val < m
  omega

/-- Restrict the cut boundary label to the darts which remain free after the
two star-labelled darts are joined. -/
def joinedBoundaryToFin
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r) :
    (joinStarsPairing Q c).Boundary → Fin m :=
  fun x ↦ ⟨(Q.label (joinedBoundaryAsOld Q c x)).val,
    joinedBoundary_label_lt Q c x⟩

/-- A non-star label selects a dart which survives the star join. -/
def finToJoinedBoundary
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r) :
    Fin m → (joinStarsPairing Q c).Boundary := fun i ↦ by
  let q : Q.pairing.Boundary := Q.label.symm (Fin.castAdd 2 i)
  refine ⟨q.1, (boundary_joinFreePair_iff Q.pairing
    (starFreePairDatum Q c) q.1).mpr ⟨q.2, ?_⟩⟩
  change q.1 ∉ (starFreePair Q).pair
  rw [starFreePair_pair, Sym2.mem_iff]
  intro h
  rcases h with h | h
  · have hq : q = firstStarDart Q := Subtype.ext h
    have hl := congrArg (fun z ↦ (Q.label z).val) hq
    simp [q, firstStarDart, firstStar] at hl
    omega
  · have hq : q = secondStarDart Q := Subtype.ext h
    have hl := congrArg (fun z ↦ (Q.label z).val) hq
    simp [q, secondStarDart, secondStar] at hl
    omega

theorem joinedBoundaryToFin_finToJoinedBoundary
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r) (i : Fin m) :
    joinedBoundaryToFin Q c (finToJoinedBoundary Q c i) = i := by
  apply Fin.eq_of_val_eq
  change
    (Q.label
      (joinedBoundaryAsOld Q c (finToJoinedBoundary Q c i))).val = i.val
  have hq : joinedBoundaryAsOld Q c (finToJoinedBoundary Q c i) =
      Q.label.symm (Fin.castAdd 2 i) := by
    apply Subtype.ext
    rfl
  rw [hq, Equiv.apply_symm_apply]
  rfl

theorem finToJoinedBoundary_joinedBoundaryToFin
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r)
    (x : (joinStarsPairing Q c).Boundary) :
    finToJoinedBoundary Q c (joinedBoundaryToFin Q c x) = x := by
  apply Subtype.ext
  dsimp only [finToJoinedBoundary]
  change
    ((Q.label.symm
      (Fin.castAdd 2 (joinedBoundaryToFin Q c x))) : Q.pairing.Boundary).1 = x.1
  have hfin : Fin.castAdd 2 (joinedBoundaryToFin Q c x) =
      Q.label (joinedBoundaryAsOld Q c x) := by
    apply Fin.eq_of_val_eq
    rfl
  rw [hfin, Equiv.symm_apply_apply]
  rfl

/-- Exact restriction equivalence for the boundary after the star join. -/
def joinedBoundaryLabel
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r) :
    (joinStarsPairing Q c).Boundary ≃ Fin m where
  toFun := joinedBoundaryToFin Q c
  invFun := finToJoinedBoundary Q c
  left_inv := finToJoinedBoundary_joinedBoundaryToFin Q c
  right_inv := joinedBoundaryToFin_finToJoinedBoundary Q c

/-! ## A lossless carrier for the nonbridge cut -/

/-- Adding back a seam cannot destroy dual connectivity.  This proof uses
only literal seam membership and therefore also covers loops and parallel
seams. -/
theorem connected_of_erase_connected
    {Cell : Type*} [DecidableEq Cell] {facets : Cell → ℕ}
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam)
    (h : (P.erase e).IsConnected facets) : P.IsConnected facets := by
  intro u v
  exact (h u v).mapRelation (fun a b hab ↦ by
    obtain ⟨i, j, hij⟩ := hab
    exact ⟨i, j, Finset.mem_of_mem_erase hij⟩)

/-- The exact data left after a nonbridge cut, before replacing the join
data by an arbitrary full boundary labelling. -/
abbrev UnrootedNonbridgeCutCarrier (n h r m b : ℕ) :=
  {w : RejoinedBoundaryLabelledFreePair (Dart n h) r m //
    w.1.1.IsConnected (fun _ ↦ h) ∧
      w.1.1.edgeCount + 1 = n + b} × Bool

/-- Forget proof fields from the pointed nonbridge stratum while retaining
the marked labelled pairing and its orientation. -/
def domainEncoding
    (z : UnrootedNonbridgePointed n h r m (b + 1) × Bool) :
    MarkedBoundaryLabelledPairing (Dart n h) r m × Bool :=
  (⟨z.1.1.1.1.raw, z.1.1.2⟩, z.2)

theorem domainEncoding_injective :
    Function.Injective
      (domainEncoding :
        UnrootedNonbridgePointed n h r m (b + 1) × Bool →
          MarkedBoundaryLabelledPairing (Dart n h) r m × Bool) := by
  rintro ⟨⟨⟨P, e⟩, hn⟩, o⟩ ⟨⟨⟨Q, f⟩, hm⟩, o'⟩ heq
  have ho : o = o' := congrArg Prod.snd heq
  have hmarked :
      (⟨P.1.raw, e⟩ : MarkedBoundaryLabelledPairing (Dart n h) r m) =
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

/-- Forget only the proof that the cut base lies in the lower stratum. -/
def carrierEncoding
    (z : UnrootedNonbridgeCutCarrier n h r m b) :
    RejoinedBoundaryLabelledFreePair (Dart n h) r m × Bool :=
  (z.1.1, z.2)

theorem carrierEncoding_injective :
    Function.Injective
      (carrierEncoding : UnrootedNonbridgeCutCarrier n h r m b →
        RejoinedBoundaryLabelledFreePair (Dart n h) r m × Bool) := by
  rintro ⟨x, o⟩ ⟨y, o'⟩ h
  have hxy : x.1 = y.1 := congrArg Prod.fst h
  have ho : o = o' := congrArg Prod.snd h
  cases ho
  cases Subtype.ext hxy
  rfl

/-- Concrete cutting into the lossless carrier.  The dependent old boundary
labelling is transported by the already proved labelled cut--join
equivalence, rather than by an assumed certificate. -/
def toCutCarrier
    (z : UnrootedNonbridgePointed n h r m (b + 1) × Bool) :
    UnrootedNonbridgeCutCarrier n h r m b := by
  let S : UnrootedStratum n h r m (b + 1) := z.1.1.1
  let e : S.1.raw.pairing.Seam := z.1.1.2
  let w := cutLabelled
    (⟨S.1.raw, e⟩ : MarkedBoundaryLabelledPairing (Dart n h) r m)
  refine ⟨⟨w, ?_, ?_⟩, z.2⟩
  · change (S.1.raw.pairing.erase e).IsConnected (fun _ ↦ h)
    exact z.1.2
  · change (S.1.raw.pairing.erase e).edgeCount + 1 = n + b
    exact NonbridgeCut.unrooted_rank_after_erase S e

/-- Reassemble a cut carrier into a pointed nonbridge diagram. -/
def fromCutCarrier
    (z : UnrootedNonbridgeCutCarrier n h r m b) :
    UnrootedNonbridgePointed n h r m (b + 1) × Bool := by
  let w : RejoinedBoundaryLabelledFreePair (Dart n h) r m := z.1.1
  let a : MarkedBoundaryLabelledPairing (Dart n h) r m := joinLabelled w
  have hcut : cutLabelled a = w := cutLabelled_joinLabelled w
  have herase : a.1.pairing.erase a.2 = w.1.1 := by
    have := congrArg (fun y ↦ y.1.1) hcut
    exact this
  have heraseConnected :
      (a.1.pairing.erase a.2).IsConnected (fun _ ↦ h) := by
    rw [herase]
    exact z.1.2.1
  have hconnected : a.1.pairing.IsConnected (fun _ ↦ h) :=
    connected_of_erase_connected a.1.pairing a.2 heraseConnected
  let P : UnrootedDiagram n h r m :=
    { raw := a.1
      connected := hconnected }
  have hrank : P.HasCircuitRank (b + 1) := by
    have hafter := z.1.2.2
    have hcard := a.1.pairing.matching.card_seams_erase a.2
    rw [← herase] at hafter
    simp only [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
      BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount,
      card_unrootedCell]
    simp only [ColoredMatching.edgeCount] at hafter
    change a.1.pairing.matching.seams.card + 1 = n + (b + 1)
    change (a.1.pairing.matching.erase a.2).seams.card + 1 = n + b at hafter
    omega
  let S : UnrootedStratum n h r m (b + 1) := ⟨P, hrank⟩
  have hnonbridge : S.1.raw.pairing.IsNonbridge a.2 := heraseConnected
  exact (⟨⟨S, a.2⟩, hnonbridge⟩, z.2)

theorem fromCutCarrier_toCutCarrier
    (z : UnrootedNonbridgePointed n h r m (b + 1) × Bool) :
    fromCutCarrier (toCutCarrier z) = z := by
  apply domainEncoding_injective
  have hcore := joinLabelled_cutLabelled
    (⟨z.1.1.1.1.raw, z.1.1.2⟩ :
      MarkedBoundaryLabelledPairing (Dart n h) r m)
  apply Prod.ext
  · exact hcore
  · rfl

theorem toCutCarrier_fromCutCarrier
    (z : UnrootedNonbridgeCutCarrier n h r m b) :
    toCutCarrier (fromCutCarrier z) = z := by
  apply carrierEncoding_injective
  have hcore := cutLabelled_joinLabelled z.1.1
  apply Prod.ext
  · exact hcore
  · rfl

/-- Exact nonbridge cut equivalence before the elementary factor-two
replacement of join data by a full `Fin (m+2)` boundary labelling. -/
def nonbridgePointedEquivCutCarrier :
    (UnrootedNonbridgePointed n h r m (b + 1) × Bool) ≃
      UnrootedNonbridgeCutCarrier n h r m b where
  toFun := toCutCarrier
  invFun := fromCutCarrier
  left_inv := fromCutCarrier_toCutCarrier
  right_inv := toCutCarrier_fromCutCarrier

/-! ## The factor-two replacement and the lower stratum -/

/-- The cut matching in the lossless carrier has exactly `m+2` boundary
darts.  This is derived from the actual selected pair and the actual
`Fin m` labelling after rejoining; it is not an arithmetic side condition. -/
theorem cutCarrier_boundary_card
    (z : UnrootedNonbridgeCutCarrier n h r m b) :
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

/-- An unlabelled lower-stratum matching, including the boundary-cardinality
equation needed by the factor-two equivalence. -/
abbrev UnrootedLowerCore (n h r m b : ℕ) :=
  {Q : ColoredMatching (Dart n h) r //
    Q.IsConnected (fun _ ↦ h) ∧
      Q.edgeCount + 1 = n + b ∧
      Fintype.card Q.Boundary = m + 2}

/-- Reassociated join data over an unlabelled lower-stratum matching. -/
abbrev UnrootedJoinDataCarrier (n h r m b : ℕ) :=
  Σ Q : UnrootedLowerCore n h r m b,
    FactorTwoCounting.LabelledJoinData Q.1.matching m × Fin r

/-- Full boundary labels over the same unlabelled lower-stratum matching. -/
abbrev UnrootedFullLabelCarrier (n h r m b : ℕ) :=
  Σ Q : UnrootedLowerCore n h r m b,
    (Q.1.Boundary ≃ Fin (m + 2)) × Fin r

/-- Pure reassociation of the lossless cut carrier into the fibre used by
`FactorTwoCounting`. -/
def cutCarrierEquivJoinData :
    UnrootedNonbridgeCutCarrier n h r m b ≃
      UnrootedJoinDataCarrier n h r m b where
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
    let w : RejoinedBoundaryLabelledFreePair (Dart n h) r m :=
      ⟨⟨Q.1, d⟩, label⟩
    exact (⟨w, Q.2.1, Q.2.2.1⟩, orientation)
  left_inv := by
    rintro ⟨⟨⟨⟨Q, d⟩, label⟩, hp⟩, orientation⟩
    rfl
  right_inv := by
    rintro ⟨Q, ⟨p, label, orientation⟩, c⟩
    rfl

/-- Fibrewise application of the already proved elementary identity
`choose (m+2) 2 * m! * 2 = (m+2)!`. -/
def joinDataEquivFullLabels :
    UnrootedJoinDataCarrier n h r m b ≃
      UnrootedFullLabelCarrier n h r m b :=
  Equiv.sigmaCongrRight (fun Q ↦
    FactorTwoCounting.colouredLabelledJoinDataEquiv
      Q.1.matching m r Q.2.2.2)

/-- Package a fully labelled lower matching as a member of the ordinary
lower circuit-rank stratum. -/
def fullLabelsToLower
    (z : UnrootedFullLabelCarrier n h r m b) :
    UnrootedStratum n h r (m + 2) b × Fin r := by
  rcases z with ⟨Q, label, c⟩
  let raw : UnrootedPairing n h r (m + 2) :=
    { pairing := Q.1
      label := label }
  let diagram : UnrootedDiagram n h r (m + 2) :=
    { raw := raw
      connected := Q.2.1 }
  have hrank : diagram.HasCircuitRank b := by
    simpa [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
      BoundaryLabelledPairing.edgeCount, card_unrootedCell] using Q.2.2.1
  exact (⟨diagram, hrank⟩, c)

/-- Forget the lower boundary label while retaining its cardinality proof. -/
def lowerToFullLabels
    (z : UnrootedStratum n h r (m + 2) b × Fin r) :
    UnrootedFullLabelCarrier n h r m b := by
  let S := z.1
  let Q := S.1.raw.pairing
  have hrank : Q.edgeCount + 1 = n + b := by
    simpa [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
      BoundaryLabelledPairing.edgeCount, card_unrootedCell] using S.2
  have hboundary : Fintype.card Q.Boundary = m + 2 := by
    simpa using Fintype.card_congr S.1.raw.label
  exact ⟨⟨Q, S.1.connected, hrank, hboundary⟩,
    S.1.raw.label, z.2⟩

theorem lowerToFullLabels_fullLabelsToLower
    (z : UnrootedFullLabelCarrier n h r m b) :
    lowerToFullLabels (fullLabelsToLower z) = z := by
  rcases z with ⟨⟨Q, hp⟩, label, c⟩
  rfl

theorem fullLabelsToLower_lowerToFullLabels
    (z : UnrootedStratum n h r (m + 2) b × Fin r) :
    fullLabelsToLower (lowerToFullLabels z) = z := by
  rcases z with ⟨⟨⟨raw, hconnected⟩, hrank⟩, c⟩
  rcases raw with ⟨Q, label⟩
  rfl

/-- Exact equivalence between full-label carrier data and the lower
unrooted stratum. -/
def fullLabelCarrierEquivLower :
    UnrootedFullLabelCarrier n h r m b ≃
      (UnrootedStratum n h r (m + 2) b × Fin r) where
  toFun := fullLabelsToLower
  invFun := lowerToFullLabels
  left_inv := lowerToFullLabels_fullLabelsToLower
  right_inv := fullLabelsToLower_lowerToFullLabels

/-- The unconditional unrooted nonbridge equivalence.  It is an equivalence
of the actual finite carrier types, not a quotient-cardinality certificate.
The middle factor-two bijection is noncanonical (`Fintype.equivOfCardEq`),
while the cut and reassembly on either side are concrete and mutually
inverse. -/
def unrootedNonbridgeEquiv :
    (UnrootedNonbridgePointed n h r m (b + 1) × Bool) ≃
      (UnrootedStratum n h r (m + 2) b × Fin r) :=
  nonbridgePointedEquivCutCarrier.trans <|
    cutCarrierEquivJoinData.trans <|
      joinDataEquivFullLabels.trans fullLabelCarrierEquivLower

/-- Therefore the two carrier types have exactly the same finite
cardinality, including at `m=0`. -/
theorem card_unrootedNonbridge_mul_two
    (n h r m b : ℕ) :
    2 * Fintype.card (UnrootedNonbridgePointed n h r m (b + 1)) =
      r * Fintype.card (UnrootedStratum n h r (m + 2) b) := by
  have hcard := Fintype.card_congr
    (unrootedNonbridgeEquiv (n := n) (h := h) (r := r) (m := m) (b := b))
  simpa [Fintype.card_prod, Nat.mul_comm] using hcard


end
end NonbridgeEquiv
end FacetPairing
end PolytopeCounting
