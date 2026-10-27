module

public import Proofs.LabelledCutJoin
public import Proofs.NonbridgeCut
public import Proofs.BoundaryJoin
public import Proofs.OrientedBoundaryCut

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Exact star-join construction on unrooted strata

This module constructs the inverse object associated to the two
canonical star labels.  It proves connectedness and the rank shift without
any numerical side condition.  In particular the definitions remain valid
for `m = 0`; if `Fin r` is empty, the target data type is empty automatically.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace NonbridgeExact

noncomputable section

open LabelledCutJoin PointedDecomposition

universe uD

variable {D : Type uD} [DecidableEq D]

/-- Unrooted predecessor data in rank `b`: a connected cut diagram and the
colour of the seam to be restored between its two star-labelled facets. -/
abbrev UnrootedStarDatum (n h r m b : ℕ) :=
  UnrootedStratum n h r (m + 2) b × Fin r

/-- The marked coloured matching obtained by joining the two star darts. -/
def joinUnrootedStarsMarked
    (w : UnrootedStarDatum n h r m b) :
    ColoredMatching.MarkedColoredMatching (Dart n h) r :=
  joinStarsMarked (⟨w.1.1.raw, w.2⟩ :
    BoundaryLabelledPairing (Dart n h) r (m + 2) × Fin r)

/-- The boundary split of a star-labelled cut diagram.  The left summand
contains the old labels `Fin m`; the two `Bool` values are exactly the star
labels `m,m+1`. -/
def starBoundarySplit
    (Q : BoundaryLabelledPairing D r (m + 2)) :
    Q.pairing.Boundary ≃ Fin m ⊕ Bool :=
  Q.label.trans (PartialMatching.finSumEquiv.symm.trans
    ((Equiv.refl (Fin m)).sumCongr finTwoEquiv))

/-- Join the two star darts and label the remaining boundary by `Fin m`. -/
def joinStarBoundaryLabel
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r) :
    (joinStarsMarked (Q, c)).1.Boundary ≃ Fin m := by
  let split := starBoundarySplit Q
  let x := Q.pairing.matching.splitEndpoint split false
  let y := Q.pairing.matching.splitEndpoint split true
  have hx : x = firstStarDart Q := by
    apply Q.label.injective
    simp [x, split, starBoundarySplit, PartialMatching.splitEndpoint,
      firstStarDart, firstStar, PartialMatching.finSumEquiv]
    apply Fin.ext
    simp [finTwoEquiv]
  have hy : y = secondStarDart Q := by
    apply Q.label.injective
    simp [y, split, starBoundarySplit, PartialMatching.splitEndpoint,
      secondStarDart, secondStar, PartialMatching.finSumEquiv]
    apply Fin.ext
    simp [finTwoEquiv]
  let E := Q.pairing.matching.boundaryJoinEquiv split
  have hm :
      (Q.pairing.matching.join x y
        (Q.pairing.matching.splitEndpoint_ne split)) =
      (joinStarsMarked (Q, c)).1.matching := by
    apply PartialMatching.ext
    change insert (Q.pairing.matching.joinPair x y)
        Q.pairing.matching.seams =
      insert
        (Q.pairing.matching.joinPair
          ((starFreePair Q).left Q.pairing.matching)
          ((starFreePair Q).right Q.pairing.matching))
        Q.pairing.matching.seams
    rw [(starFreePair Q).joinPair_left_right]
    simp only [starFreePair_pair, hx, hy, PartialMatching.joinPair]
  exact (Equiv.cast (by rw [hm])).trans E

/-- Boundary-labelled object produced by joining the two star facets. -/
def joinUnrootedRaw (w : UnrootedStarDatum n h r m b) :
    UnrootedPairing n h r m where
  pairing := (joinUnrootedStarsMarked w).1
  label := joinStarBoundaryLabel w.1.1.raw w.2

/-- Adding a seam to a connected coloured matching preserves connectivity. -/
theorem isConnected_joinFreePair
    {Cell : Type*} [DecidableEq Cell] {facets : Cell → ℕ}
    (P : ColoredMatching (CellDart Cell facets) r)
    (d : P.FreePairDatum) (hP : P.IsConnected facets) :
    (P.joinFreePair d).IsConnected facets := by
  intro u v
  exact (hP u v).mapRelation (by
    intro a b hab
    obtain ⟨i, j, hij⟩ := hab
    exact ⟨i, j, Finset.mem_insert_of_mem hij⟩)

/-- The star-joined unrooted pairing is connected. -/
theorem joinUnrootedRaw_connected
    (w : UnrootedStarDatum n h r m b) :
    (joinUnrootedRaw w).pairing.IsConnected (fun _ : Fin n ↦ h) := by
  change (joinUnrootedStarsMarked w).1.IsConnected (fun _ : Fin n ↦ h)
  exact isConnected_joinFreePair w.1.1.raw.pairing
    (starFreePairDatum w.1.1.raw w.2) w.1.1.connected

/-- Joining one seam raises the circuit rank by exactly one. -/
theorem unrooted_rank_after_star_join
    (w : UnrootedStarDatum n h r m b) :
    (joinUnrootedRaw w).edgeCount + 1 = n + (b + 1) := by
  have hrank := w.1.2
  simp only [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
    BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount,
    card_unrootedCell] at hrank
  change (joinUnrootedStarsMarked w).1.matching.seams.card + 1 =
    n + (b + 1)
  have hnew :
      (joinUnrootedStarsMarked w).1.matching.seams.card =
        w.1.1.raw.pairing.matching.seams.card + 1 := by
    change
      (w.1.1.raw.pairing.joinFreePair
        (starFreePairDatum w.1.1.raw w.2)).matching.seams.card = _
    change
      (insert
        (w.1.1.raw.pairing.matching.joinPair
          ((starFreePairDatum w.1.1.raw w.2).selected.left
            w.1.1.raw.pairing.matching)
          ((starFreePairDatum w.1.1.raw w.2).selected.right
            w.1.1.raw.pairing.matching))
        w.1.1.raw.pairing.matching.seams).card = _
    rw [(starFreePairDatum w.1.1.raw w.2).selected.joinPair_left_right]
    rw [Finset.card_insert_of_notMem]
    exact w.1.1.raw.pairing.matching.joinPair_not_mem _ _
  omega

/-- Reassembled connected unrooted stratum of rank `b+1`. -/
def joinUnrootedStars (w : UnrootedStarDatum n h r m b) :
    UnrootedStratum n h r m (b + 1) :=
  ⟨⟨joinUnrootedRaw w, joinUnrootedRaw_connected w⟩,
    by simpa [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
      card_unrootedCell] using unrooted_rank_after_star_join w⟩

/-- The newly inserted seam, marked in the reassembled stratum. -/
def joinUnrootedNewSeam (w : UnrootedStarDatum n h r m b) :
    (joinUnrootedStars w).1.raw.pairing.Seam :=
  (joinUnrootedStarsMarked w).2

/-- The inserted seam is automatically nonbridging: deleting it returns the
connected predecessor matching. -/
theorem joinUnrootedNewSeam_nonbridge
    (w : UnrootedStarDatum n h r m b) :
    (joinUnrootedStars w).1.raw.pairing.IsNonbridge
      (joinUnrootedNewSeam w) := by
  change
    (((w.1.1.raw.pairing.joinFreePair
      (starFreePairDatum w.1.1.raw w.2)).erase
      (w.1.1.raw.pairing.freePairNewSeam
        (starFreePairDatum w.1.1.raw w.2))).IsConnected
          (fun _ : Fin n ↦ h))
  rw [ColoredMatching.erase_joinFreePair]
  exact w.1.1.connected

/-- The complete inverse-side pointed nonbridge object. -/
def joinUnrootedNonbridgePointed
    (w : UnrootedStarDatum n h r m b) :
    UnrootedNonbridgePointed n h r m (b + 1) :=
  ⟨⟨joinUnrootedStars w, joinUnrootedNewSeam w⟩,
    joinUnrootedNewSeam_nonbridge w⟩

/-- Cutting the newly joined seam recovers the predecessor coloured
matching and the remembered colour exactly. -/
theorem cut_joinUnrootedStars_pairing
    (w : UnrootedStarDatum n h r m b) :
    (ColoredMatching.cutMarked (joinUnrootedStarsMarked w)).1 =
      w.1.1.raw.pairing := by
  exact cut_joinStars_pairing
    (⟨w.1.1.raw, w.2⟩ :
      BoundaryLabelledPairing (Dart n h) r (m + 2) × Fin r)

theorem cut_joinUnrootedStars_color
    (w : UnrootedStarDatum n h r m b) :
    (ColoredMatching.cutMarked (joinUnrootedStarsMarked w)).2.color =
      w.2 := by
  exact cut_joinStars_color
    (⟨w.1.1.raw, w.2⟩ :
      BoundaryLabelledPairing (Dart n h) r (m + 2) × Fin r)

/-! ## Exact orientation recovery -/

/-- The first endpoint of the newly inserted seam, oriented by the first
star label.  This avoids the arbitrary representative `Sym2.out`. -/
def joinUnrootedOrientation
    (w : UnrootedStarDatum n h r m b) :
    {d : Dart n h // d ∈ (joinUnrootedNewSeam w).1} :=
  ⟨(firstStarDart w.1.1.raw).1, by
    rw [show (joinUnrootedNewSeam w).1 =
      (starFreePair w.1.1.raw).pair from
        ColoredMatching.freePairNewSeam_val _ _]
    simp [starFreePair]⟩

/-- Exact endpoint-ordered label produced when a marked seam is cut. -/
def orientedCutUnrooted
    (z : UnrootedNonbridgePointed n h r m (b + 1))
    (first : {d : Dart n h // d ∈ z.1.2.1}) :
    UnrootedStarDatum n h r m b := by
  let P : UnrootedStratum n h r m (b + 1) := z.1.1
  let e : P.1.raw.pairing.Seam := z.1.2
  let o : P.1.raw.pairing.matching.OrientedSeam := ⟨e, first⟩
  let Qraw : UnrootedPairing n h r (m + 2) :=
    { pairing := P.1.raw.pairing.erase e
      label := P.1.raw.pairing.matching.orientedCutBoundaryLabel o
        P.1.raw.label }
  let Q : UnrootedDiagram n h r (m + 2) :=
    { raw := Qraw
      connected := z.2 }
  have hQrank : Q.HasCircuitRank b := by
    simpa [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
      card_unrootedCell, Q, Qraw, BoundaryLabelledPairing.edgeCount] using NonbridgeCut.unrooted_rank_after_erase P e
  exact (⟨Q, hQrank⟩, P.1.raw.pairing.color e)

@[simp]
theorem orientedCutUnrooted_pairing
    (z : UnrootedNonbridgePointed n h r m (b + 1))
    (first : {d : Dart n h // d ∈ z.1.2.1}) :
    (orientedCutUnrooted z first).1.1.raw.pairing =
      z.1.1.1.raw.pairing.erase z.1.2 := rfl

@[simp]
theorem orientedCutUnrooted_color
    (z : UnrootedNonbridgePointed n h r m (b + 1))
    (first : {d : Dart n h // d ∈ z.1.2.1}) :
    (orientedCutUnrooted z first).2 =
      z.1.1.1.raw.pairing.color z.1.2 := rfl

/-- The fully oriented inverse candidate. -/
def joinUnrootedOriented
    (w : UnrootedStarDatum n h r m b) :=
  (joinUnrootedNonbridgePointed w, joinUnrootedOrientation w)

/-- Cutting the oriented star-join recovers the predecessor coloured
matching exactly.  This is the structural, non-label part of the right
inverse. -/
theorem orientedCut_joinUnrooted_pairing
    (w : UnrootedStarDatum n h r m b) :
    (orientedCutUnrooted (joinUnrootedNonbridgePointed w)
      (joinUnrootedOrientation w)).1.1.raw.pairing =
        w.1.1.raw.pairing := by
  change
    ((joinUnrootedStarsMarked w).1.erase
      (joinUnrootedStarsMarked w).2) = w.1.1.raw.pairing
  exact congrArg Sigma.fst
    (cutMarked_joinStarsMarked
      (⟨w.1.1.raw, w.2⟩ :
        BoundaryLabelledPairing (Dart n h) r (m + 2) × Fin r))

theorem orientedCut_joinUnrooted_color
    (w : UnrootedStarDatum n h r m b) :
    (orientedCutUnrooted (joinUnrootedNonbridgePointed w)
      (joinUnrootedOrientation w)).2 = w.2 := by
  exact cut_joinUnrootedStars_color w


end
end NonbridgeExact
end FacetPairing
end PolytopeCounting
