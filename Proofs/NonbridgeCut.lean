module

public import Proofs.BoundaryCut
public import Proofs.PointedDecomposition

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Concrete cutting in the nonbridge branch

This module constructs the forward, nonbridge half of the global cut--join
correspondence on the actual diagram strata.  Cutting a marked nonbridge
seam

* keeps the same cells;
* lowers circuit rank by one;
* creates two boundary labels;
* retains connectivity; and
* remembers the deleted seam colour.

The extra `Bool` records which exposed end receives the first of the two new
labels.  This is the literal two-fold orientation whose cardinality later
becomes the denominator `2` in the nonbridge recurrence term.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace NonbridgeCut

noncomputable section

open PointedDecomposition

/-- The first of the two new boundary labels. -/
def firstStar (m : ℕ) : Fin (m + 2) := ⟨m, by omega⟩

/-- The second of the two new boundary labels. -/
def secondStar (m : ℕ) : Fin (m + 2) := ⟨m + 1, by omega⟩

theorem firstStar_ne_secondStar (m : ℕ) : firstStar m ≠ secondStar m := by
  intro h
  have := congrArg Fin.val h
  simp [firstStar, secondStar] at this

/-- Swap only the two newly created boundary labels. -/
def swapStars (m : ℕ) : Equiv.Perm (Fin (m + 2)) :=
  Equiv.swap (firstStar m) (secondStar m)

/-- Extend the old boundary labelling across a cut, and use `orientation` to
decide whether the two new labels are swapped. -/
def orientedCutBoundaryLabel
    {D : Type*} [DecidableEq D]
    (M : PartialMatching D) (e : M.Seam)
    (label : M.Boundary ≃ Fin m) (orientation : Bool) :
    (M.erase e).Boundary ≃ Fin (m + 2) :=
  (M.cutBoundaryLabel e label).trans
    (if orientation then swapStars m else Equiv.refl _)

/-- Cutting lowers the unrooted circuit rank by exactly one. -/
theorem unrooted_rank_after_erase
    (P : UnrootedStratum n h r m (b + 1))
    (e : P.1.raw.pairing.Seam) :
    (P.1.raw.pairing.erase e).edgeCount + 1 = n + b := by
  have hrank := P.2
  have herase := P.1.raw.pairing.matching.card_seams_erase e
  have hpos : 0 < P.1.raw.pairing.matching.seams.card :=
    Finset.card_pos.mpr ⟨e.1, e.2⟩
  simp only [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
    BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount,
    card_unrootedCell] at hrank
  change (P.1.raw.pairing.matching.erase e).seams.card + 1 = n + b
  omega

/-- Cutting lowers the rooted circuit rank by exactly one. -/
theorem rooted_rank_after_erase
    (P : RootedStratum n h₀ h r m (b + 1))
    (e : P.1.raw.pairing.Seam) :
    (P.1.raw.pairing.erase e).edgeCount + 1 =
      Fintype.card (RootedCell n) + b := by
  have hrank := P.2
  have herase := P.1.raw.pairing.matching.card_seams_erase e
  have hpos : 0 < P.1.raw.pairing.matching.seams.card :=
    Finset.card_pos.mpr ⟨e.1, e.2⟩
  simp only [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
    BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount] at hrank
  change (P.1.raw.pairing.matching.erase e).seams.card + 1 =
    Fintype.card (RootedCell n) + b
  omega

/-- The concrete output of cutting an oriented, marked, unrooted nonbridge
seam.  The deleted seam colour is returned separately. -/
def cutUnrooted
    (z : UnrootedNonbridgePointed n h r m (b + 1))
    (orientation : Bool) :
    UnrootedStratum n h r (m + 2) b × Fin r := by
  let P : UnrootedStratum n h r m (b + 1) := z.1.1
  let e : P.1.raw.pairing.Seam := z.1.2
  let Qraw : UnrootedPairing n h r (m + 2) :=
    { pairing := P.1.raw.pairing.erase e
      label := orientedCutBoundaryLabel P.1.raw.pairing.matching e
        P.1.raw.label orientation }
  let Q : UnrootedDiagram n h r (m + 2) :=
    { raw := Qraw
      connected := z.2 }
  have hQrank : Q.HasCircuitRank b := by
    simpa [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
      card_unrootedCell, Q, Qraw, BoundaryLabelledPairing.edgeCount] using unrooted_rank_after_erase P e
  exact (⟨Q, hQrank⟩, P.1.raw.pairing.color e)

/-- The concrete output of cutting an oriented, marked, rooted nonbridge
seam. -/
def cutRooted
    (z : RootedNonbridgePointed n h₀ h r m (b + 1))
    (orientation : Bool) :
    RootedStratum n h₀ h r (m + 2) b × Fin r := by
  let P : RootedStratum n h₀ h r m (b + 1) := z.1.1
  let e : P.1.raw.pairing.Seam := z.1.2
  let Qraw : RootedPairing n h₀ h r (m + 2) :=
    { pairing := P.1.raw.pairing.erase e
      label := orientedCutBoundaryLabel P.1.raw.pairing.matching e
        P.1.raw.label orientation }
  let Q : RootedDiagram n h₀ h r (m + 2) :=
    { raw := Qraw
      connected := z.2 }
  exact (⟨Q, rooted_rank_after_erase P e⟩, P.1.raw.pairing.color e)

/-- Forgetting boundary labels, the coloured matching underlying the
unrooted cut is definitionally the erased matching. -/
theorem cutUnrooted_pairing
    (z : UnrootedNonbridgePointed n h r m (b + 1))
    (orientation : Bool) :
    (cutUnrooted z orientation).1.1.raw.pairing =
      z.1.1.1.raw.pairing.erase z.1.2 := rfl

/-- The cut remembers the old seam colour exactly. -/
theorem cutUnrooted_color
    (z : UnrootedNonbridgePointed n h r m (b + 1))
    (orientation : Bool) :
    (cutUnrooted z orientation).2 =
      z.1.1.1.raw.pairing.color z.1.2 := rfl

theorem cutRooted_pairing
    (z : RootedNonbridgePointed n h₀ h r m (b + 1))
    (orientation : Bool) :
    (cutRooted z orientation).1.1.raw.pairing =
      z.1.1.1.raw.pairing.erase z.1.2 := rfl

theorem cutRooted_color
    (z : RootedNonbridgePointed n h₀ h r m (b + 1))
    (orientation : Bool) :
    (cutRooted z orientation).2 =
      z.1.1.1.raw.pairing.color z.1.2 := rfl


end
end NonbridgeCut
end FacetPairing
end PolytopeCounting
