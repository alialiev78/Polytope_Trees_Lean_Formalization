module

public import Proofs.ConcreteRecurrenceStep
public import Proofs.GenericStratumMass
public import Proofs.GenericRootedStratumAction
public import Proofs.Normalization
public import Mathlib.Algebra.Field.Basic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Rational groupoid-mass form of the concrete unrooted recurrence step

This module proves the rational mass normalization.
The input is the unconditional finite-cardinality cut decomposition proved
in `ConcreteRecurrenceStep`.  The two stratum cardinalities are replaced by
the non-free translation-groupoid masses proved in `GenericStratumMass`.
The bridge contribution remains the cardinality of the literal pointed
bridge subtype divided by the ambient wreath order; no unproved bridge
product decomposition is assumed.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace MassRecurrence

open PointedDecomposition ConcreteRecurrenceStep
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

/-- The concrete unrooted stratum mass for a specified local symmetry
group.  This is a translation-groupoid mass, not an orbit count. -/
abbrev UMass (L : Type uL) [Group L] [Fintype L]
    (n h r m b : ℕ) [MulAction L (Fin h)] : ℚ :=
  ActionGroupoid.mass (WreathRenaming (Fin n) L)
    (UnrootedStratum n h r m b) ℚ

/-- The still-unexpanded bridge term, normalized by the ambient wreath
order.  Its numerator is already a concrete finite subtype. -/
def bridgeRemainder (n h r m b tau : ℕ) : ℚ :=
  (Fintype.card (UnrootedBridgePointed n h r m b) : ℚ) /
    ((n.factorial * tau ^ n : ℕ) : ℚ)

/-- The generic rooted-stratum mass; the base cell and its facets are fixed,
while only the `n` ordinary cells are renamed. -/
abbrev PsiMass (L : Type uL) [Group L] [Fintype L]
    (n h₀ h r m b : ℕ) [MulAction L (Fin h)] : ℚ :=
  ActionGroupoid.mass (WreathRenaming (Fin n) L)
    (RootedStratum n h₀ h r m b) ℚ

/-- Literal rooted bridge remainder divided by the ordinary-cell wreath
order.  No component-product formula is hidden in this definition. -/
def rootedBridgeRemainder
    (n h₀ h r m b tau : ℕ) : ℚ :=
  (Fintype.card (RootedBridgePointed n h₀ h r m b) : ℚ) /
    ((n.factorial * tau ^ n : ℕ) : ℚ)

/-- Arithmetic core: an exact double-counting identity over `ℕ` becomes
the recurrence with coefficient `r/2` after division by a nonzero common
normalizing order. -/
theorem rational_recurrence_of_double_count
    {x r A C B O : ℕ} (hO : O ≠ 0)
    (hraw : 2 * (x * A) = r * C + 2 * B) :
    (x : ℚ) * ((A : ℚ) / (O : ℚ)) =
      ((r : ℚ) / 2) * ((C : ℚ) / (O : ℚ)) +
        (B : ℚ) / (O : ℚ) := by
  have hOQ : (O : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hO
  have hrawQ :
      (2 : ℚ) * ((x : ℚ) * (A : ℚ)) =
        (r : ℚ) * (C : ℚ) + (2 : ℚ) * (B : ℚ) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
      congrArg (fun z : ℕ ↦ (z : ℚ)) hraw
  have htwo : (2 : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 1)
  have hnum :
      (x : ℚ) * (A : ℚ) =
        ((r : ℚ) / 2) * (C : ℚ) + (B : ℚ) := by
    apply mul_left_cancel₀ (a := (2 : ℚ)) htwo
    calc
      (2 : ℚ) * ((x : ℚ) * (A : ℚ)) =
          (r : ℚ) * (C : ℚ) + (2 : ℚ) * (B : ℚ) := hrawQ
      _ = (2 : ℚ) * (((r : ℚ) / 2) * (C : ℚ)) +
          (2 : ℚ) * (B : ℚ) := by
        congr 1
        calc
          (r : ℚ) * (C : ℚ) =
              ((r : ℚ) * (C : ℚ) / 2) * 2 :=
            (div_mul_cancel₀ _ htwo).symm
          _ = (((r : ℚ) / 2) * (C : ℚ)) * 2 := by
            congr 1
            exact (div_mul_eq_mul_div (r : ℚ) 2 (C : ℚ)).symm
          _ = 2 * (((r : ℚ) / 2) * (C : ℚ)) := by
            rw [mul_comm]
      _ = (2 : ℚ) *
          (((r : ℚ) / 2) * (C : ℚ) + (B : ℚ)) := by
        rw [mul_add]
  calc
    (x : ℚ) * ((A : ℚ) / (O : ℚ)) =
        ((x : ℚ) * (A : ℚ)) / (O : ℚ) := by
      rw [mul_div_assoc]
    _ = ((((r : ℚ) / 2) * (C : ℚ) + (B : ℚ)) /
          (O : ℚ)) := by rw [hnum]
    _ = ((r : ℚ) / 2) * ((C : ℚ) / (O : ℚ)) +
          (B : ℚ) / (O : ℚ) := by
      rw [add_div, mul_div_assoc]

/-- Exact `U` successor recurrence in groupoid-mass normalization:

`(n+b) U_{n,b+1}^m = (r/2) U_{n,b}^{m+2} + bridge`.

It is unconditional for the concrete facet-pairing model.  In particular,
it uses neither a free action nor a choice of an external facet, so `m = 0`
is included. -/
theorem unrooted_successor_mass_recurrence
    (n h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau) :
    (n + b : ℚ) * UMass L n h r m (b + 1) =
      ((r : ℚ) / 2) * UMass L n h r (m + 2) b +
        bridgeRemainder n h r m (b + 1) tau := by
  have htau : tau ≠ 0 := by
    rw [← hcard]
    exact Fintype.card_ne_zero
  have horder : n.factorial * tau ^ n ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero n) (pow_ne_zero n htau)
  simp only [UMass, bridgeRemainder]
  rw [Renaming.GenericStratumMass.mass_genericWreath_unrootedStratum_of_card
      (L := L) n h r m (b + 1) tau ℚ hcard,
    Renaming.GenericStratumMass.mass_genericWreath_unrootedStratum_of_card
      (L := L) n h r (m + 2) b tau ℚ hcard]
  simpa only [Nat.cast_add] using
    (rational_recurrence_of_double_count horder
      (unrooted_successor_cut_decomposition n h r m b))

/-- Closed-boundary specialization.  The empty boundary labelling is the
unique map `Fin 0 ≃ Fin 0`; automorphisms are still accounted for by the
non-free groupoid mass. -/
theorem unrooted_successor_mass_recurrence_closed
    (n h r b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau) :
    (n + b : ℚ) * UMass L n h r 0 (b + 1) =
      ((r : ℚ) / 2) * UMass L n h r 2 b +
        bridgeRemainder n h r 0 (b + 1) tau := by
  simpa using
    (unrooted_successor_mass_recurrence
      (L := L) n h r 0 b tau hcard)

/-- Exact rooted `Psi` successor step in groupoid-mass normalization:

`(n+b+1) Psi_{n,b+1}^m = (r/2) Psi_{n,b}^{m+2} + rootedBridge`.

The fixed base contributes the additional one in the seam-pointing factor,
but contributes no symmetry factor to the denominator. -/
theorem rooted_successor_mass_recurrence
    (n h₀ h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau) :
    (n + b + 1 : ℚ) * PsiMass L n h₀ h r m (b + 1) =
      ((r : ℚ) / 2) * PsiMass L n h₀ h r (m + 2) b +
        rootedBridgeRemainder n h₀ h r m (b + 1) tau := by
  have htau : tau ≠ 0 := by
    rw [← hcard]
    exact Fintype.card_ne_zero
  have horder : n.factorial * tau ^ n ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero n) (pow_ne_zero n htau)
  simp only [PsiMass, rootedBridgeRemainder]
  rw [Renaming.GenericRootedStratumAction.mass_genericWreath_rootedStratum_of_card
      (L := L) n h₀ h r m (b + 1) tau ℚ hcard,
    Renaming.GenericRootedStratumAction.mass_genericWreath_rootedStratum_of_card
      (L := L) n h₀ h r (m + 2) b tau ℚ hcard]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (rational_recurrence_of_double_count horder
      (rooted_successor_cut_decomposition n h₀ h r m b))

/-- Closed-boundary rooted specialization.  It is meaningful even though
the boundary-label type is empty: the base is still distinguished, while
all residual automorphisms are weighted by reciprocal stabilizer order. -/
theorem rooted_successor_mass_recurrence_closed
    (n h₀ h r b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau) :
    (n + b + 1 : ℚ) * PsiMass L n h₀ h r 0 (b + 1) =
      ((r : ℚ) / 2) * PsiMass L n h₀ h r 2 b +
        rootedBridgeRemainder n h₀ h r 0 (b + 1) tau := by
  simpa using
    (rooted_successor_mass_recurrence
      (L := L) n h₀ h r 0 b tau hcard)

/-! ## Normalizing the bridge-product formula

The following lemma is the exact binomial/factorial step needed once the
range of the concrete bridge cut has been identified with component pairs.
It introduces no combinatorial assumption: it simply turns one raw summand
with a cell-label factor `choose n k` and boundary-label factor `choose m s`
into the product of the two normalized component masses. -/

/-- One bridge convolution summand after wreath normalization. -/
theorem normalize_bridge_summand
    {n k m s tau A B : ℕ}
    (hk : k ≤ n) (htau : 0 < tau) :
    ((Nat.choose n k * Nat.choose m s * A * B : ℕ) : ℚ) /
        ((n.factorial * tau ^ n : ℕ) : ℚ) =
      (Nat.choose m s : ℚ) *
        ((A : ℚ) / ((k.factorial * tau ^ k : ℕ) : ℚ)) *
        ((B : ℚ) /
          (((n - k).factorial * tau ^ (n - k) : ℕ) : ℚ)) := by
  simpa only [Nat.cast_mul] using
    Normalization.choose_cells_labels_normalized hk htau (A : ℚ) (B : ℚ)


end

end MassRecurrence
end FacetPairing
end PolytopeCounting
