module

public import Proofs.DisconnectedRawCutJoin
public import Proofs.DisconnectedWHat
public import Proofs.ActionGroupoidMass
public import Proofs.RenamingAction
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# The concrete disconnected groupoid mass and its recurrence

`WLabelledMass` is the finite action-groupoid cardinality of unrestricted
boundary-labelled facet pairings.  Dividing by `m!` gives the manuscript's
symmetry-weighted coefficient `\widehat W_{n,m}`.

The recurrence is derived from the concrete unrestricted cut--join
equivalence in `DisconnectedRawCutJoin`; it is not assumed as an abstract
coefficient identity.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace DisconnectedMass

noncomputable section

open Renaming
open DisconnectedRawCutJoin

universe uL

variable {L : Type uL}

local instance unrootedPairingFintype (n h r m : ℕ) :
    Fintype (UnrootedPairing n h r m) := Fintype.ofFinite _

/-- Groupoid mass of unrestricted pairings with all `m` boundary facets
labelled. -/
abbrev WLabelledMass
    (L : Type uL) [Group L] [Fintype L]
    (n h r m : ℕ) [MulAction L (Fin h)] : ℚ :=
  ActionGroupoid.mass (WreathRenaming (Fin n) L)
    (UnrootedPairing n h r m) ℚ

/-- The coefficient used in the paper: forget the boundary labels by
dividing the labelled groupoid mass by `m!`. -/
def WHatMass
    (L : Type uL) [Group L] [Fintype L]
    (n h r m : ℕ) [MulAction L (Fin h)] : ℚ :=
  WLabelledMass L n h r m / (m.factorial : ℚ)

/-- Exact normalization by the order `n! |L|^n` of the constructed wreath
renaming group.  Stabilizers need not be trivial. -/
theorem WLabelledMass_eq_card_div
    (n h r m : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)] :
    WLabelledMass L n h r m =
      (Fintype.card (UnrootedPairing n h r m) : ℚ) /
        ((n.factorial * (Fintype.card L) ^ n : ℕ) : ℚ) := by
  unfold WLabelledMass
  rw [ActionGroupoid.mass_eq_card_div_card]
  rw [WreathRenaming.card]
  simp only [Fintype.card_fin]

/-- The same normalization with a named local group order `tau`. -/
theorem WLabelledMass_eq_card_div_of_card
    (n h r m tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau) :
    WLabelledMass L n h r m =
      (Fintype.card (UnrootedPairing n h r m) : ℚ) /
        ((n.factorial * tau ^ n : ℕ) : ℚ) := by
  simpa only [hcard] using
    (WLabelledMass_eq_card_div (L := L) n h r m)

/-- The raw labelled mass recurrence obtained by dividing the concrete
finite-cardinality cut--join identity by the common wreath order. -/
theorem WLabelledMass_recurrence
    (n h r m ell tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (hsupport : n * h = m + 2 * ell) :
    (2 * ell : ℚ) * WLabelledMass L n h r m =
      (r : ℚ) * WLabelledMass L n h r (m + 2) := by
  have hraw :=
    DisconnectedRawCutJoin.unrooted_raw_card_recurrence
      n h r m ell hsupport
  have hrawQ :
      (2 * ell : ℚ) *
          (Fintype.card (UnrootedPairing n h r m) : ℚ) =
        (r : ℚ) *
          (Fintype.card (UnrootedPairing n h r (m + 2)) : ℚ) := by
    exact_mod_cast hraw
  rw [WLabelledMass_eq_card_div_of_card (L := L) n h r m tau hcard,
    WLabelledMass_eq_card_div_of_card (L := L) n h r (m + 2) tau hcard]
  rw [← mul_div_assoc, ← mul_div_assoc]
  rw [hrawQ]

/-- Two-step factorial identity in the coefficient field. -/
theorem factorial_add_two_cast (m : ℕ) :
    ((m + 2).factorial : ℚ) =
      ((m + 2 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ) *
        (m.factorial : ℚ) := by
  have h1 : (m + 2).factorial = (m + 2) * (m + 1).factorial := by
    simpa [Nat.add_assoc] using Nat.factorial_succ (m + 1)
  have h2 : (m + 1).factorial = (m + 1) * m.factorial :=
    Nat.factorial_succ m
  rw [h1, h2]
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- Recurrence (43) for the normalized concrete mass, in a subtraction-free
support parameterization.  Here `ell+1` is the number of seams. -/
theorem WHatMass_recurrence_by_pairs
    (n h r m ell tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (hsupport : n * h = m + 2 * (ell + 1)) :
    (2 * (ell + 1) : ℚ) * WHatMass L n h r m =
      (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        WHatMass L n h r (m + 2) := by
  have hraw := WLabelledMass_recurrence
    (L := L) n h r m (ell + 1) tau hcard hsupport
  norm_num only [Nat.cast_add, Nat.cast_one] at hraw
  have hmfac : (m.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  unfold WHatMass
  calc
    (2 * (ell + 1) : ℚ) *
        (WLabelledMass L n h r m / (m.factorial : ℚ)) =
      ((2 * (ell + 1) : ℚ) * WLabelledMass L n h r m) /
        (m.factorial : ℚ) := by ring
    _ = ((r : ℚ) * WLabelledMass L n h r (m + 2)) /
        (m.factorial : ℚ) := by rw [hraw]
    _ = (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        (WLabelledMass L n h r (m + 2) /
          ((m + 2).factorial : ℚ)) := by
      rw [factorial_add_two_cast]
      field_simp [hmfac]

/-- Literal form of recurrence (43):

`(hn-m) W_hat[n,m] = r(m+1)(m+2) W_hat[n,m+2]`.
-/
theorem WHatMass_recurrence
    (n h r m ell tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (hsupport : n * h = m + 2 * (ell + 1)) :
    ((n * h - m : ℕ) : ℚ) * WHatMass L n h r m =
      (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        WHatMass L n h r (m + 2) := by
  have hdiff : n * h - m = 2 * (ell + 1) := by omega
  rw [hdiff]
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
    (WHatMass_recurrence_by_pairs
      (L := L) n h r m ell tau hcard hsupport)


/-- The concrete normalized mass equals formula (46) once its no-gluing top
coefficient is supplied.  All lower supported coefficients then follow from
the concrete cut--join recurrence by uniqueness. -/
theorem WHatMass_eq_closedForm_of_top
    (n h r tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (htau : 0 < tau)
    (hTop : WHatMass L n h r (h * n) =
      1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n)) :
    ∀ m ell, h * n = m + 2 * ell →
      WHatMass L n h r m =
        ExplicitFormulas.WHatClosedForm h r tau n m := by
  apply ExplicitFormulas.WHatClosedForm_unique h r tau n htau
    (fun m ↦ WHatMass L n h r m) hTop
  intro m ell hs
  have hs' : n * h = m + 2 * (ell + 1) := by
    simpa [Nat.mul_comm] using hs
  exact WHatMass_recurrence_by_pairs
    (L := L) n h r m ell tau hcard hs'


end
end DisconnectedMass
end FacetPairing
end PolytopeCounting
