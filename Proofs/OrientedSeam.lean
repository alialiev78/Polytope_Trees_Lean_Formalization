module

public import Proofs.BoundaryCut
public import Proofs.FiniteCounting

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Orienting a marked seam

The manuscript repeatedly replaces an unordered marked seam by an ordered
choice of one of its two ends and later divides by two.  This file makes that
step literal.  No freeness hypothesis is involved: for every matching, an
oriented seam is a dependent triple consisting of the seam and one of its
two endpoints, and this type is explicitly equivalent to `Seam × Bool`.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace PartialMatching

universe uD

variable {D : Type uD} [DecidableEq D]

/-- A seam together with a distinguished endpoint. -/
abbrev OrientedSeam (M : PartialMatching D) :=
  Σ e : M.Seam, {d : D // d ∈ e.1}

/-- Every unoriented seam has exactly two literal orientations. -/
noncomputable def orientedSeamEquiv (M : PartialMatching D) :
    M.OrientedSeam ≃ M.Seam × Bool :=
  Equiv.sigmaEquivProdOfEquiv (fun e ↦ M.seamEndpointEquivBool e)

/-- Finite-cardinality form of the orientation factor. -/
theorem card_orientedSeam [Fintype D] (M : PartialMatching D) :
    Fintype.card M.OrientedSeam = 2 * M.seams.card := by
  rw [Fintype.card_congr M.orientedSeamEquiv, Fintype.card_prod]
  simp [Nat.mul_comm]

/-- Oriented pointing in a finite family multiplies its cardinality by
twice the common seam number. -/
theorem card_orientedPointed_of_constant
    {X : Type*} [Fintype X] (P : X → PartialMatching D)
    [Fintype D] (e : ℕ) (hE : ∀ x, (P x).seams.card = e) :
    Fintype.card (Σ x : X, (P x).OrientedSeam) =
      Fintype.card X * (2 * e) := by
  rw [Fintype.card_sigma]
  simp_rw [card_orientedSeam, hE]
  simp

/-- The statement remains valid when the family has no seams. -/
@[simp] theorem card_orientedPointed_zero
    {X : Type*} [Fintype X] (P : X → PartialMatching D)
    [Fintype D] (hE : ∀ x, (P x).seams.card = 0) :
    Fintype.card (Σ x : X, (P x).OrientedSeam) = 0 := by
  simpa using card_orientedPointed_of_constant P 0 hE


end PartialMatching
end FacetPairing
end PolytopeCounting
