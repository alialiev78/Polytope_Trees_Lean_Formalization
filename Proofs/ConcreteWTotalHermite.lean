module

public import Proofs.DisconnectedTopCoefficient
public import Proofs.PhysicistsHermiteExact
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# The concrete total disconnected mass and its Hermite representation

The paper's one-variable coefficient `\widehat W_n` is the sum over all
possible numbers of free facets.  Because support has fixed parity, it is
most convenient to index the same finite sum by the number `ell` of paired
facet pairs.

This file connects the *actual* action-groupoid mass from
`DisconnectedMassRecurrence` to the closed finite sum and then to the exact
physicists-Hermite expression.  Thus the Hermite identity is not merely a
statement about an auxiliary sequence.
-/

namespace PolytopeCounting
namespace FacetPairing

open scoped BigOperators
namespace ConcreteWTotal

noncomputable section

universe uL
variable {L : Type uL}

/-- Total disconnected groupoid mass at fixed `n`, indexed by the number of
paired facet pairs.  The corresponding number of free facets is
`h*n - 2*ell`. -/
def WTotalMass
    (L : Type uL) [Group L] [Fintype L]
    (n h r : ℕ) [MulAction L (Fin h)] : ℚ :=
  ∑ ell ∈ Finset.range (h * n / 2 + 1),
    DisconnectedMass.WHatMass L n h r (h * n - 2 * ell)

/-- Every index in the defining range gives the expected support identity. -/
theorem support_of_mem_total_range
    (h n ell : ℕ)
    (hell : ell ∈ Finset.range (h * n / 2 + 1)) :
    h * n = (h * n - 2 * ell) + 2 * ell := by
  have hell' : ell < h * n / 2 + 1 := Finset.mem_range.mp hell
  have hle : 2 * ell ≤ h * n := by omega
  omega

/-- The concrete total mass is exactly the closed finite sum used in the
Hermite reduction. -/
theorem WTotalMass_eq_closedForm
    (n h r tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (htau : 0 < tau) :
    WTotalMass L n h r =
      ExplicitFormulas.WTotalClosedForm h r tau n := by
  classical
  unfold WTotalMass ExplicitFormulas.WTotalClosedForm
  apply Finset.sum_congr rfl
  intro ell hell
  have hs : h * n = (h * n - 2 * ell) + 2 * ell :=
    support_of_mem_total_range h n ell hell
  have hsMass : n * h = (h * n - 2 * ell) + 2 * ell := by
    simpa [Nat.mul_comm] using hs
  rw [DisconnectedTop.WHatMass_closed_form
      (L := L) n h r tau hcard htau
      (h * n - 2 * ell) ell hsMass]
  exact ExplicitFormulas.WHatClosedForm_eq_of_support
    h r tau n (h * n - 2 * ell) ell hs

/-- The exact branch-independent Hermite identity for the concrete total
mass. -/
theorem WTotalMass_cast_eq_hermite
    (n h r tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (htau : 0 < tau)
    (a : ℂ) (hr : 0 < r) (ha0 : a ≠ 0)
    (ha : a ^ 2 = -(2 / (r : ℂ))) :
    ((WTotalMass L n h r : ℚ) : ℂ) =
      1 / ((n.factorial : ℂ) * (tau : ℂ) ^ n) *
        HermiteExact.physicistsHermiteValue (h * n) (a / 2) /
          a ^ (h * n) := by
  rw [WTotalMass_eq_closedForm (L := L) n h r tau hcard htau]
  exact HermiteExact.WTotalClosedForm_cast_eq_hermite
    h r tau n a hr ha0 ha

/-- Equation (47) with the positive-real square-root branch used in the
manuscript, now for the concrete groupoid mass. -/
theorem WTotalMass_cast_eq_manuscriptHermite
    (n h r tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (htau : 0 < tau)
    (hr : 0 < r) :
    ((WTotalMass L n h r : ℚ) : ℂ) =
      1 / ((n.factorial : ℂ) * (tau : ℂ) ^ n) *
        HermiteExact.physicistsHermiteValue (h * n)
          (HermiteExact.manuscriptHermiteScale (r : ℝ) / 2) /
        HermiteExact.manuscriptHermiteScale (r : ℝ) ^ (h * n) := by
  rw [WTotalMass_eq_closedForm (L := L) n h r tau hcard htau]
  exact HermiteExact.WTotalClosedForm_cast_eq_manuscriptHermite
    h r tau n hr


end
end ConcreteWTotal
end FacetPairing
end PolytopeCounting
