module

public import Proofs.DisconnectedWHat

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Coefficientwise bivariate generating-function equation for W

Rather than hiding coefficient shifts behind analytic notation, this module
formalizes the bivariate formal-series operators directly on coefficient
families `F n m`.  Equality of the coefficient families below is exactly the
formal PDE

`h t₀ ∂₀ W - t₁ ∂₁ W = r ∂₁² W`.

No convergence assumption is involved.
-/

namespace PolytopeCounting
namespace BivariateCoefficients

noncomputable section

/-- Coefficients of a bivariate formal series. -/
abbrev Series₂ (K : Type*) := ℕ → ℕ → K

/-- Coefficients of `h t₀ ∂W/∂t₀`. -/
def cellEuler (h : ℕ) (F : Series₂ ℚ) : Series₂ ℚ :=
  fun n m ↦ ((h * n : ℕ) : ℚ) * F n m

/-- Coefficients of `t₁ ∂W/∂t₁`. -/
def boundaryEuler (F : Series₂ ℚ) : Series₂ ℚ :=
  fun n m ↦ (m : ℚ) * F n m

/-- Coefficients of `∂²W/∂t₁²`. -/
def boundarySecondDerivative (F : Series₂ ℚ) : Series₂ ℚ :=
  fun n m ↦ ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) * F n (m + 2)

/-- Coefficientwise statement of the linear heat-type PDE for the
disconnected series. -/
def SatisfiesDisconnectedPDE (h r : ℕ) (F : Series₂ ℚ) : Prop :=
  ∀ n m,
    cellEuler h F n m - boundaryEuler F n m =
      (r : ℚ) * boundarySecondDerivative F n m

/-- The literal coefficient family associated with formula (46). -/
def WCoefficient (h r tau : ℕ) : Series₂ ℚ :=
  fun n m ↦ ExplicitFormulas.WHatClosedForm h r tau n m

/-- Expanding the operator notation gives recurrence (43). -/
theorem satisfiesDisconnectedPDE_iff
    (h r : ℕ) (F : Series₂ ℚ) :
    SatisfiesDisconnectedPDE h r F ↔
      ∀ n m : ℕ,
        (((h * n : ℕ) : ℚ) - (m : ℚ)) * F n m =
          (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
            F n (m + 2) := by
  constructor
  · intro hPDE n m
    have h := hPDE n m
    dsimp [SatisfiesDisconnectedPDE, cellEuler, boundaryEuler,
      boundarySecondDerivative] at h ⊢
    linear_combination h
  · intro hrec n m
    have h := hrec n m
    dsimp [SatisfiesDisconnectedPDE, cellEuler, boundaryEuler,
      boundarySecondDerivative] at h ⊢
    linear_combination h

/-- Formula (46) satisfies the bivariate formal PDE. -/
theorem WCoefficient_satisfiesDisconnectedPDE
    (h r tau : ℕ) (htau : 0 < tau) :
    SatisfiesDisconnectedPDE h r (WCoefficient h r tau) := by
  rw [satisfiesDisconnectedPDE_iff]
  intro n m
  exact ExplicitFormulas.WHatClosedForm_recurrence_all h r tau n m htau

/-- Pointwise expanded version, convenient for matching the displayed PDE
with the manuscript. -/
theorem WCoefficient_PDE_coefficient
    (h r tau n m : ℕ) (htau : 0 < tau) :
    cellEuler h (WCoefficient h r tau) n m -
        boundaryEuler (WCoefficient h r tau) n m =
      (r : ℚ) *
        boundarySecondDerivative (WCoefficient h r tau) n m := by
  exact WCoefficient_satisfiesDisconnectedPDE h r tau htau n m


end
end BivariateCoefficients
end PolytopeCounting
