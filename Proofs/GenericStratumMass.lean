module

public import Proofs.ActionGroupoidMass
public import Proofs.GenericStratumAction

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Non-free groupoid mass for an arbitrary local symmetry group

No freeness hypothesis is used.  The denominator is the proved order of the
wreath renaming group, `n! * |L|^n`.  Consequently the statements include
closed diagrams (`m = 0`), where an empty boundary labelling need not remove
any automorphisms.
-/

namespace PolytopeCounting
namespace Renaming
namespace GenericStratumMass

open FacetPairing
open GenericStratumAction

noncomputable section

universe uL uK

variable {L : Type uL}

local instance stratumFintype (n h r m b : ℕ) :
    Fintype (UnrootedStratum n h r m b) :=
  Fintype.ofFinite _

/-- Groupoid cardinality of a concrete unrooted stratum modulo cell
renamings and an arbitrary finite local symmetry group. -/
theorem mass_genericWreath_unrootedStratum
    (n h r m b : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (K : Type uK) [Field K] [CharZero K]
    :
    ActionGroupoid.mass (WreathRenaming (Fin n) L)
        (UnrootedStratum n h r m b) K =
      (Fintype.card (UnrootedStratum n h r m b) : K) /
        ((n.factorial * (Fintype.card L) ^ n : ℕ) : K) := by
  rw [ActionGroupoid.mass_eq_card_div_card]
  rw [WreathRenaming.card]
  simp only [Fintype.card_fin]

/-- The same normalization written with a named local group order `tau`. -/
theorem mass_genericWreath_unrootedStratum_of_card
    (n h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (K : Type uK) [Field K] [CharZero K]
    (hcard : Fintype.card L = tau) :
    ActionGroupoid.mass (WreathRenaming (Fin n) L)
        (UnrootedStratum n h r m b) K =
      (Fintype.card (UnrootedStratum n h r m b) : K) /
        ((n.factorial * tau ^ n : ℕ) : K) := by
  simpa only [hcard] using
    (mass_genericWreath_unrootedStratum (L := L) n h r m b K)

/-- Closed diagrams are covered without choosing or labelling any external
facet.  Stabilizers are handled by the groupoid-mass theorem itself. -/
theorem mass_genericWreath_unrootedStratum_closed
    (n h r b : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (K : Type uK) [Field K] [CharZero K]
    :
    ActionGroupoid.mass (WreathRenaming (Fin n) L)
        (UnrootedStratum n h r 0 b) K =
      (Fintype.card (UnrootedStratum n h r 0 b) : K) /
        ((n.factorial * (Fintype.card L) ^ n : ℕ) : K) := by
  exact mass_genericWreath_unrootedStratum (L := L) n h r 0 b K

/-- Closed form with the traditional notation `tau = |L|`. -/
theorem mass_genericWreath_unrootedStratum_closed_of_card
    (n h r b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (K : Type uK) [Field K] [CharZero K]
    (hcard : Fintype.card L = tau) :
    ActionGroupoid.mass (WreathRenaming (Fin n) L)
        (UnrootedStratum n h r 0 b) K =
      (Fintype.card (UnrootedStratum n h r 0 b) : K) /
        ((n.factorial * tau ^ n : ℕ) : K) := by
  exact mass_genericWreath_unrootedStratum_of_card
    (L := L) n h r 0 b tau K hcard


end

end GenericStratumMass
end Renaming
end PolytopeCounting
