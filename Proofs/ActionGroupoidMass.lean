module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Proofs.RenamingAction

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Cardinality of a finite translation groupoid

For a finite group `G` acting on a finite type `X`, the translation groupoid
has objects `X` and arrows `x → y` given by the elements `g : G` satisfying
`g • x = y`.  Its automorphism group at `x` is its stabilizer.

The theorem below proves the groupoid-mass identity without any freeness
hypothesis.  It is stated over an arbitrary characteristic-zero field, so it
specializes to `ℚ` while keeping this module's imports small.
-/

open scoped BigOperators

namespace PolytopeCounting
namespace ActionGroupoid

noncomputable section

universe uG uX uK

variable (G : Type uG) (X : Type uX)
variable [Group G] [MulAction G X] [Fintype G] [Fintype X]

local notation "Ω" => MulAction.orbitRel.Quotient G X

local instance : Fintype Ω := Fintype.ofFinite Ω

local instance orbitFintype (ω : Ω) :
    Fintype (MulAction.orbit G ω.out) := Fintype.ofFinite _

local instance stabilizerFintype (ω : Ω) :
    Fintype (MulAction.stabilizer G ω.out) := Fintype.ofFinite _

/-- The groupoid cardinality of `X // G`, namely the sum over orbits of the
reciprocal orders of their stabilizers. -/
def mass (K : Type uK) [Field K] [CharZero K] : K :=
  ∑ ω : Ω, ((Fintype.card (MulAction.stabilizer G ω.out) : K)⁻¹)

/-- The underlying finite set is the disjoint union of its orbits. -/
theorem card_eq_sum_card_orbits :
    Fintype.card X =
      ∑ ω : Ω, Fintype.card (MulAction.orbit G ω.out) := by
  calc
    Fintype.card X =
        Fintype.card (Σ ω : Ω, MulAction.orbit G ω.out) :=
      Fintype.card_congr (MulAction.selfEquivSigmaOrbits G X)
    _ = ∑ ω : Ω, Fintype.card (MulAction.orbit G ω.out) :=
      Fintype.card_sigma

/-- Orbit--stabilizer rewritten in the form needed by groupoid cardinality. -/
theorem reciprocal_stabilizer_eq_orbit_div_group
    (K : Type uK) [Field K] [CharZero K] (ω : Ω) :
    ((Fintype.card (MulAction.stabilizer G ω.out) : K)⁻¹) =
      (Fintype.card (MulAction.orbit G ω.out) : K) /
        (Fintype.card G : K) := by
  let o : ℕ := Fintype.card (MulAction.orbit G ω.out)
  let s : ℕ := Fintype.card (MulAction.stabilizer G ω.out)
  let g : ℕ := Fintype.card G
  have hOS : o * s = g := by
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G ω.out
  have hsNat : s ≠ 0 := Fintype.card_ne_zero
  have hgNat : g ≠ 0 := Fintype.card_ne_zero
  have hs : (s : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr hsNat
  have hg : (g : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr hgNat
  have hOSK : (o : K) * (s : K) = (g : K) := by
    have hc := congrArg (fun q : ℕ ↦ (q : K)) hOS
    simpa only [Nat.cast_mul] using hc
  apply (eq_div_iff hg).2
  rw [← hOSK]
  calc
    (s : K)⁻¹ * ((o : K) * (s : K)) =
        (o : K) * ((s : K)⁻¹ * (s : K)) := by
          ac_rfl
    _ = (o : K) := by simp [hs]

/-- The mass formula for a finite action groupoid.  No stabilizer is assumed
trivial.  In particular it applies to closed (`m = 0`) diagrams whose empty
boundary labelling does not destroy automorphisms. -/
theorem mass_eq_card_div_card
    (K : Type uK) [Field K] [CharZero K] :
    mass G X K = (Fintype.card X : K) / (Fintype.card G : K) := by
  rw [mass]
  simp_rw [reciprocal_stabilizer_eq_orbit_div_group G X K]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  congr 1
  have hc := congrArg (fun q : ℕ ↦ (q : K))
    (card_eq_sum_card_orbits G X)
  simpa only [Nat.cast_sum] using hc.symm

/-- A useful stress test: for the trivial action, the stabilizer is the whole
group, and the formula gives one copy of `1 / |G|` for each object.  Thus the
theorem genuinely includes maximally non-free actions. -/
theorem mass_of_trivial_action
    (K : Type uK) [Field K] [CharZero K]
    (htriv : ∀ (g : G) (x : X), g • x = x) :
    mass G X K = (Fintype.card X : K) / (Fintype.card G : K) := by
  exact mass_eq_card_div_card G X K

local instance unrootedStratumFintype (n h r m b : ℕ) :
    Fintype (FacetPairing.UnrootedStratum n h r m b) :=
  Fintype.ofFinite _

/-- The non-free mass normalization specialized to the concrete unrooted
rank stratum and the fully constructed wreath renaming action. -/
theorem mass_fullDartRenaming_unrootedStratum
    (K : Type uK) [Field K] [CharZero K]
    (n h r m b : ℕ) :
    mass (Renaming.FullDartRenaming n h)
        (FacetPairing.UnrootedStratum n h r m b) K =
      (Fintype.card (FacetPairing.UnrootedStratum n h r m b) : K) /
        ((n.factorial * h.factorial ^ n : ℕ) : K) := by
  rw [mass_eq_card_div_card]
  rw [Renaming.card_fullDartRenaming]


end

end ActionGroupoid
end PolytopeCounting
