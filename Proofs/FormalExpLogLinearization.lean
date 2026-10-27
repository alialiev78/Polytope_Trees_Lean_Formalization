module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Algebraic `W = exp V`, `V = log W` linearization

This file isolates the formal algebra behind the substitution used in
Statement 6.3.  It is deliberately independent of analytic convergence.

Let `E = h t₀ ∂₀ - t₁ ∂₁` and `D = ∂₁`.  Both are derivations on the
bivariate formal-series ring.  If `W = exp V`, then

* `D W = W * D V`, and
* `E W = W * E V`.

These two logarithmic-derivative identities turn

`E V = ρ (D² V + (D V)²)`

into the linear equation

`E W = ρ D² W`.

The theorem is stated for arbitrary derivations; no commutation hypothesis
is required for this identity.  The concrete
coefficient family for `\widehat W` is connected to the linear equation in
`DisconnectedGeneratingPDE.lean`.  A separate component-decomposition
module is still needed to identify the concrete connected groupoid series
with the actual formal logarithm; this file does not hide that semantic step.
-/

namespace PolytopeCounting
namespace FormalExpLog

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The nonlinear connected-series equation
`E V = ρ (D²V + (DV)²)`. -/
def SatisfiesConnectedEquation
    (E D : Derivation ℚ A A) (ρ V : A) : Prop :=
  E V = ρ * (D (D V) + D V * D V)

/-- The linear disconnected-series equation `E W = ρ D²W`. -/
def SatisfiesDisconnectedEquation
    (E D : Derivation ℚ A A) (ρ W : A) : Prop :=
  E W = ρ * D (D W)

/-- The two differential identities supplied by the formal relation
`W = exp V`.  They are separated from the word `exp` so the linearization
can be reused in any complete differential algebra. -/
def IsFormalExpPair
    (E D : Derivation ℚ A A) (V W : A) : Prop :=
  D W = W * D V ∧ E W = W * E V

/-- The second derivative of a formal exponential pair. -/
theorem secondDerivative_of_expPair
    (E D : Derivation ℚ A A) (V W : A)
    (hExp : IsFormalExpPair E D V W) :
    D (D W) = W * (D (D V) + D V * D V) := by
  rcases hExp with ⟨hDW, _hEW⟩
  rw [hDW, D.leibniz, hDW]
  simp only [smul_eq_mul]
  ring

/-- Formal proof of the substitution `W = exp V` used in Statement 6.3. -/
theorem disconnectedEquation_of_exp_connectedEquation
    (E D : Derivation ℚ A A) (ρ V W : A)
    (hExp : IsFormalExpPair E D V W)
    (hV : SatisfiesConnectedEquation E D ρ V) :
    SatisfiesDisconnectedEquation E D ρ W := by
  rcases hExp with ⟨hDW, hEW⟩
  unfold SatisfiesConnectedEquation at hV
  unfold SatisfiesDisconnectedEquation
  have hD2 : D (D W) = W * (D (D V) + D V * D V) := by
    rw [hDW, D.leibniz, hDW]
    simp only [smul_eq_mul]
    ring
  rw [hEW, hV, hD2]
  ring

/-- Logarithmic-derivative form of `V = log W` in a field.

The separate predicate is useful when the actual `PowerSeries.logOf`
identification has been established.  The forward theorem above is the only
one needed for the paper's linearization step. -/
def IsFormalLogPair
    {K : Type*} [Field K] [Algebra ℚ K]
    (E D : Derivation ℚ K K) (W V : K) : Prop :=
  W ≠ 0 ∧ D V = W⁻¹ * D W ∧ E V = W⁻¹ * E W


end
end FormalExpLog
end PolytopeCounting
