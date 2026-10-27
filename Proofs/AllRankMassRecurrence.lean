module

public import Proofs.MassRecurrence
public import Proofs.TreeBridgeIdentity

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Unconditional all-rank mass recurrences

`MassRecurrence` proves the successor-rank step, while
`TreeBridgeIdentity` proves that in rank zero every pointed seam is a bridge
and the nonbridge branch is empty.  This file joins those two cases into one
statement valid for every natural circuit rank.

The bridge contribution remains the cardinality of the literal bridge-
pointed subtype divided by the ambient wreath order.  No numerical bridge
coproduct, component convolution, or freeness assumption is used.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace AllRankMassRecurrence

open PointedDecomposition
open ConcreteRecurrenceStep TreeBridgeIdentity MassRecurrence
open Renaming Renaming.GenericStratumAction

noncomputable section

universe uL

variable {L : Type uL}

local instance unrootedStratumFintype (n h r m b : ℕ) :
    Fintype (UnrootedStratum n h r m b) := Fintype.ofFinite _

local instance unrootedBridgePointedFintype (n h r m b : ℕ) :
    Fintype (UnrootedBridgePointed n h r m b) := Fintype.ofFinite _

local instance rootedStratumFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedStratum n h₀ h r m b) := Fintype.ofFinite _

local instance rootedBridgePointedFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedBridgePointed n h₀ h r m b) := Fintype.ofFinite _

/-! ## A total previous-rank term -/

/-- Raw unrooted previous-rank cardinality.  Rank zero has no previous
nonbridge stratum; successor rank `b+1` uses rank `b` and two exposed
boundary labels. -/
def unrootedPreviousCard (n h r m b : ℕ) : ℕ :=
  match b with
  | 0 => 0
  | k + 1 => Fintype.card (UnrootedStratum n h r (m + 2) k)

/-- Raw rooted previous-rank cardinality, totalized at rank zero. -/
def rootedPreviousCard (n h₀ h r m b : ℕ) : ℕ :=
  match b with
  | 0 => 0
  | k + 1 => Fintype.card (RootedStratum n h₀ h r (m + 2) k)

/-- The unrooted cycle predecessor as an actual groupoid mass: zero at rank
zero and the preceding-rank mass at successor rank. -/
def unrootedCyclePrevious
    (L : Type uL) [Group L] [Fintype L]
    (n h r m b : ℕ) [MulAction L (Fin h)] : ℚ :=
  match b with
  | 0 => 0
  | k + 1 => UMass L n h r (m + 2) k

/-- Rooted analogue of `unrootedCyclePrevious`. -/
def rootedCyclePrevious
    (L : Type uL) [Group L] [Fintype L]
    (n h₀ h r m b : ℕ) [MulAction L (Fin h)] : ℚ :=
  match b with
  | 0 => 0
  | k + 1 => PsiMass L n h₀ h r (m + 2) k

@[simp]
theorem unrootedCyclePrevious_zero
    [Group L] [Fintype L]
    (n h r m : ℕ) [MulAction L (Fin h)] :
    unrootedCyclePrevious L n h r m 0 = 0 := rfl

@[simp]
theorem unrootedCyclePrevious_succ
    [Group L] [Fintype L]
    (n h r m b : ℕ) [MulAction L (Fin h)] :
    unrootedCyclePrevious L n h r m (b + 1) =
      UMass L n h r (m + 2) b := rfl

@[simp]
theorem rootedCyclePrevious_zero
    [Group L] [Fintype L]
    (n h₀ h r m : ℕ) [MulAction L (Fin h)] :
    rootedCyclePrevious L n h₀ h r m 0 = 0 := rfl

@[simp]
theorem rootedCyclePrevious_succ
    [Group L] [Fintype L]
    (n h₀ h r m b : ℕ) [MulAction L (Fin h)] :
    rootedCyclePrevious L n h₀ h r m (b + 1) =
      PsiMass L n h₀ h r (m + 2) b := rfl

/-! ## All-rank literal finite-cardinality decompositions -/

/-- The exact unrooted cut decomposition at every rank.  At rank zero the
middle term is literally zero because every seam is a bridge; at successor
rank this is the already constructed nonbridge cut--join equivalence. -/
theorem unrooted_all_rank_cut_decomposition
    (n h r m b : ℕ) :
    2 * ((n + b - 1) *
        Fintype.card (UnrootedStratum n h r m b)) =
      r * unrootedPreviousCard n h r m b +
        2 * Fintype.card (UnrootedBridgePointed n h r m b) := by
  cases b with
  | zero =>
      simp [unrootedPreviousCard,
        TreeBridgeIdentity.card_unrootedTreeBridgePointed]
  | succ b =>
      simpa [unrootedPreviousCard, Nat.succ_eq_add_one,
        Nat.add_assoc] using
        (ConcreteRecurrenceStep.unrooted_successor_cut_decomposition
          n h r m b)

/-- Rooted all-rank finite-cardinality decomposition.  The fixed base changes
the seam-pointing coefficient from `n+b-1` to `n+b`. -/
theorem rooted_all_rank_cut_decomposition
    (n h₀ h r m b : ℕ) :
    2 * ((n + b) *
        Fintype.card (RootedStratum n h₀ h r m b)) =
      r * rootedPreviousCard n h₀ h r m b +
        2 * Fintype.card (RootedBridgePointed n h₀ h r m b) := by
  cases b with
  | zero =>
      simp [rootedPreviousCard,
        TreeBridgeIdentity.card_rootedTreeBridgePointed]
  | succ b =>
      simpa [rootedPreviousCard, Nat.succ_eq_add_one,
        Nat.add_assoc] using
        (ConcreteRecurrenceStep.rooted_successor_cut_decomposition
          n h₀ h r m b)

/-! ## Rank-zero mass identities -/

/-- In rank zero the unrooted recurrence has only the literal bridge term. -/
theorem unrooted_tree_mass_recurrence
    (n h r m tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau) :
    ((n - 1 : ℕ) : ℚ) * UMass L n h r m 0 =
      bridgeRemainder n h r m 0 tau := by
  simp only [UMass, bridgeRemainder]
  rw [Renaming.GenericStratumMass.mass_genericWreath_unrootedStratum_of_card
      (L := L) n h r m 0 tau ℚ hcard,
    TreeBridgeIdentity.card_unrootedTreeBridgePointed]
  simp only [Nat.cast_mul]
  rw [mul_div_assoc]

/-- Rooted rank-zero identity; the base changes the pointing factor to `n`. -/
theorem rooted_tree_mass_recurrence
    (n h₀ h r m tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau) :
    (n : ℚ) * PsiMass L n h₀ h r m 0 =
      rootedBridgeRemainder n h₀ h r m 0 tau := by
  simp only [PsiMass, rootedBridgeRemainder]
  rw [Renaming.GenericRootedStratumAction.mass_genericWreath_rootedStratum_of_card
      (L := L) n h₀ h r m 0 tau ℚ hcard,
    TreeBridgeIdentity.card_rootedTreeBridgePointed]
  simp only [Nat.cast_mul]
  rw [mul_div_assoc]

/-! ## Unified rational recurrences -/

/-- Exact unrooted groupoid-mass recurrence for every natural circuit rank:

`(n+b-1) U_b = (r/2) cyclePrevious_b + literalBridge_b`.

This includes `b=0`, closed boundary `m=0`, loops, parallel seams, and
non-free symmetry actions. -/
theorem unrooted_all_rank_mass_recurrence
    (n h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau) :
    ((n + b - 1 : ℕ) : ℚ) * UMass L n h r m b =
      ((r : ℚ) / 2) * unrootedCyclePrevious L n h r m b +
        bridgeRemainder n h r m b tau := by
  cases b with
  | zero =>
      simpa using
        (unrooted_tree_mass_recurrence (L := L) n h r m tau hcard)
  | succ b =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        (MassRecurrence.unrooted_successor_mass_recurrence
          (L := L) n h r m b tau hcard)

/-- Exact rooted groupoid-mass recurrence for every natural circuit rank:

`(n+b) Psi_b = (r/2) cyclePrevious_b + literalRootedBridge_b`. -/
theorem rooted_all_rank_mass_recurrence
    (n h₀ h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau) :
    ((n + b : ℕ) : ℚ) * PsiMass L n h₀ h r m b =
      ((r : ℚ) / 2) * rootedCyclePrevious L n h₀ h r m b +
        rootedBridgeRemainder n h₀ h r m b tau := by
  cases b with
  | zero =>
      simpa using
        (rooted_tree_mass_recurrence (L := L) n h₀ h r m tau hcard)
  | succ b =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, add_assoc] using
        (MassRecurrence.rooted_successor_mass_recurrence
          (L := L) n h₀ h r m b tau hcard)

/-- Closed-boundary unrooted specialization, including the unique empty
labelling at `m=0`. -/
theorem unrooted_all_rank_mass_recurrence_closed
    (n h r b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau) :
    ((n + b - 1 : ℕ) : ℚ) * UMass L n h r 0 b =
      ((r : ℚ) / 2) * unrootedCyclePrevious L n h r 0 b +
        bridgeRemainder n h r 0 b tau := by
  exact unrooted_all_rank_mass_recurrence
    (L := L) n h r 0 b tau hcard

/-- Closed-boundary rooted specialization. -/
theorem rooted_all_rank_mass_recurrence_closed
    (n h₀ h r b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau) :
    ((n + b : ℕ) : ℚ) * PsiMass L n h₀ h r 0 b =
      ((r : ℚ) / 2) * rootedCyclePrevious L n h₀ h r 0 b +
        rootedBridgeRemainder n h₀ h r 0 b tau := by
  exact rooted_all_rank_mass_recurrence
    (L := L) n h₀ h r 0 b tau hcard


end
end AllRankMassRecurrence
end FacetPairing
end PolytopeCounting
