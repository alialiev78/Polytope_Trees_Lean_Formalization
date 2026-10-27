module

public import Proofs.NonbridgeEquiv
public import Proofs.OrientedSeam
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Unrestricted cut--join equivalence for the disconnected series W

This file removes the connectivity and circuit-rank restrictions from the
nonbridge cut--join construction.  Every seam of an unrestricted pairing can
be cut.  After choosing one of its two endpoint orientations, cutting gives a
pairing with two additional boundary labels and remembers one of `r` seam
colours.

The equivalence is between actual finite carrier types.  It does not use a
free group action and it includes the closed-boundary case `m = 0`.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace DisconnectedRawCutJoin

noncomputable section

open LabelledCutJoin
open FactorTwoCounting

universe uD

variable {D : Type uD} [Fintype D] [DecidableEq D]

/-- A coloured matching with `m` boundary labels, a marked seam, and one of
its two endpoint orientations.  The `Bool` factor is cardinally equivalent
to choosing an actual endpoint of the marked unordered seam. -/
abbrev OrientedMarkedBoundaryLabelledPairing (D : Type uD)
    [DecidableEq D] (r m : ℕ) :=
  LabelledCutJoin.MarkedBoundaryLabelledPairing D r m × Bool

/-- The unlabelled cut matching together with the proof that it has exactly
`m+2` free darts. -/
abbrev RawCutCore (D : Type uD) [Fintype D] [DecidableEq D] (r m : ℕ) :=
  {Q : ColoredMatching D r // Fintype.card Q.Boundary = m + 2}

/-- The lossless cut carrier, reassociated into the fibre used by the
factor-two boundary-label theorem. -/
abbrev RawJoinDataCarrier (D : Type uD) [Fintype D] [DecidableEq D]
    (r m : ℕ) :=
  Σ Q : RawCutCore D r m,
    FactorTwoCounting.LabelledJoinData Q.1.matching m × Fin r

/-- The same cut matching equipped with an arbitrary full `Fin (m+2)`
boundary labelling and the remembered seam colour. -/
abbrev RawFullLabelCarrier (D : Type uD) [Fintype D] [DecidableEq D]
    (r m : ℕ) :=
  Σ Q : RawCutCore D r m,
    (Q.1.Boundary ≃ Fin (m + 2)) × Fin r

/-- A lossless labelled cut has `m+2` free darts. -/
theorem rejoined_boundary_card
    (z : LabelledCutJoin.RejoinedBoundaryLabelledFreePair D r m) :
    Fintype.card z.1.1.Boundary = m + 2 := by
  let Q := z.1.1
  let p := z.1.2.selected
  have hjoin := FactorTwoCounting.card_boundary_joinFreePair Q.matching p
  have hlabel :
      Fintype.card (Q.matching.joinFreePair p).Boundary = m := by
    change Fintype.card ((ColoredMatching.joinSelected z.1).1).Boundary = m
    exact (Fintype.card_congr z.2).trans (Fintype.card_fin m)
  rw [hlabel] at hjoin
  exact hjoin.symm

/-- Reassociate exact cut data and the endpoint orientation into join data
for a fixed unlabelled cut matching. -/
def rejoinedEquivJoinData :
    (LabelledCutJoin.RejoinedBoundaryLabelledFreePair D r m × Bool) ≃
      RawJoinDataCarrier D r m where
  toFun z := by
    let w := z.1
    let Q := w.1.1
    let d := w.1.2
    exact ⟨⟨Q, rejoined_boundary_card w⟩,
      (⟨d.selected, (w.2, z.2)⟩, d.color)⟩
  invFun z := by
    rcases z with ⟨Q, jd, c⟩
    rcases jd with ⟨p, label, orientation⟩
    let d : Q.1.FreePairDatum := ⟨p, c⟩
    let w : LabelledCutJoin.RejoinedBoundaryLabelledFreePair D r m :=
      ⟨⟨Q.1, d⟩, label⟩
    exact (w, orientation)
  left_inv := by
    rintro ⟨⟨⟨Q, d⟩, label⟩, orientation⟩
    rfl
  right_inv := by
    rintro ⟨Q, ⟨p, label, orientation⟩, c⟩
    rfl

/-- Fibrewise application of the exact finite factor-two equivalence. -/
def rawJoinDataEquivFullLabels :
    RawJoinDataCarrier D r m ≃ RawFullLabelCarrier D r m :=
  Equiv.sigmaCongrRight (fun Q ↦
    FactorTwoCounting.colouredLabelledJoinDataEquiv
      Q.1.matching m r Q.2)

/-- Forget the redundant boundary-cardinality proof and package the fully
labelled cut matching as an ordinary unrestricted pairing. -/
def rawFullLabelsToPairing
    (z : RawFullLabelCarrier D r m) :
    BoundaryLabelledPairing D r (m + 2) × Fin r := by
  rcases z with ⟨Q, label, c⟩
  exact (⟨Q.1, label⟩, c)

/-- Recover the boundary-cardinality proof from the full boundary label. -/
def rawPairingToFullLabels
    (z : BoundaryLabelledPairing D r (m + 2) × Fin r) :
    RawFullLabelCarrier D r m := by
  let Q := z.1.pairing
  have hboundary : Fintype.card Q.Boundary = m + 2 := by
    simpa using Fintype.card_congr z.1.label
  exact ⟨⟨Q, hboundary⟩, z.1.label, z.2⟩

theorem rawPairingToFullLabels_left
    (z : RawFullLabelCarrier D r m) :
    rawPairingToFullLabels (rawFullLabelsToPairing z) = z := by
  rcases z with ⟨⟨Q, hQ⟩, label, c⟩
  rfl

theorem rawPairingToFullLabels_right
    (z : BoundaryLabelledPairing D r (m + 2) × Fin r) :
    rawFullLabelsToPairing (rawPairingToFullLabels z) = z := by
  rcases z with ⟨⟨Q, label⟩, c⟩
  rfl

/-- Exact equivalence between the full-label carrier and the ordinary cut
pairing carrier. -/
def rawFullLabelCarrierEquivPairing :
    RawFullLabelCarrier D r m ≃
      (BoundaryLabelledPairing D r (m + 2) × Fin r) where
  toFun := rawFullLabelsToPairing
  invFun := rawPairingToFullLabels
  left_inv := rawPairingToFullLabels_left
  right_inv := rawPairingToFullLabels_right

/-- The unrestricted oriented cut--join equivalence. -/
def rawOrientedCutJoinEquiv :
    OrientedMarkedBoundaryLabelledPairing D r m ≃
      (BoundaryLabelledPairing D r (m + 2) × Fin r) :=
  (LabelledCutJoin.markedBoundaryLabelledEquivRejoinedFreePair.prodCongr
      (Equiv.refl Bool)).trans <|
    rejoinedEquivJoinData.trans <|
      rawJoinDataEquivFullLabels.trans rawFullLabelCarrierEquivPairing

/-- Every object in a supported boundary stratum has the same number `ell`
of seams. -/
theorem seam_count_of_support
    (P : BoundaryLabelledPairing D r m)
    (ell : ℕ) (hsupport : Fintype.card D = m + 2 * ell) :
    P.pairing.matching.seams.card = ell := by
  have hbal := P.boundary_balance
  change m + 2 * P.pairing.matching.seams.card = Fintype.card D at hbal
  omega

/-- Cardinal form of unrestricted cut--join.  If the total number of darts
is `m+2*ell`, then orienting one of the `ell` seams gives

`2*ell * card(W_m) = r * card(W_{m+2})`.
-/
theorem raw_card_recurrence
    (r m ell : ℕ) (hsupport : Fintype.card D = m + 2 * ell) :
    2 * ell * Fintype.card (BoundaryLabelledPairing D r m) =
      r * Fintype.card (BoundaryLabelledPairing D r (m + 2)) := by
  classical
  have hcard := Fintype.card_congr
    (rawOrientedCutJoinEquiv (D := D) (r := r) (m := m))
  have hpointed :
      Fintype.card
          (LabelledCutJoin.MarkedBoundaryLabelledPairing D r m) =
        Fintype.card (BoundaryLabelledPairing D r m) * ell := by
    change Fintype.card
        (Σ P : BoundaryLabelledPairing D r m, P.pairing.Seam) = _
    rw [Fintype.card_sigma]
    simp_rw [show ∀ P : BoundaryLabelledPairing D r m,
        Fintype.card P.pairing.Seam = ell by
      intro P
      change Fintype.card P.pairing.matching.Seam = ell
      simpa [PartialMatching.Seam] using
        seam_count_of_support P ell hsupport]
    simp
  rw [Fintype.card_prod, hpointed, Fintype.card_bool,
    Fintype.card_prod] at hcard
  simp only [Fintype.card_fin] at hcard
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard

/-- Specialization to `n` cells with `h` darts per cell. -/
theorem unrooted_raw_card_recurrence
    (n h r m ell : ℕ) (hsupport : n * h = m + 2 * ell) :
    2 * ell * Fintype.card (UnrootedPairing n h r m) =
      r * Fintype.card (UnrootedPairing n h r (m + 2)) := by
  apply raw_card_recurrence (D := Dart n h) r m ell
  simpa using hsupport


end
end DisconnectedRawCutJoin
end FacetPairing
end PolytopeCounting
