module

public import Proofs.DisconnectedWHat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Exact Hermite representation of the total disconnected coefficient

The manuscript uses the physicists' Hermite polynomials

`H_N(x) = N! sum_{ell=0}^{floor(N/2)}
  (-1)^ell (2x)^(N-2ell)/(ell! (N-2ell)!)`.

This file formalizes the finite sum itself and the exact algebraic identity
behind equation (47).  To avoid burying square-root branch choices in the
algebra, the theorem is stated for any complex number `a` satisfying
`a^2 = -2/rho`; the manuscript's choice is
`a = i sqrt(2/r)` and `x = a/2 = i/sqrt(2r)`.
-/

namespace PolytopeCounting
namespace HermiteExact

open scoped BigOperators

noncomputable section

open scoped ComplexConjugate

/-- Evaluation of the physicists' Hermite polynomial, given by its finite
coefficient formula. -/
def physicistsHermiteValue (N : ℕ) (x : ℂ) : ℂ :=
  ∑ ell ∈ Finset.range (N / 2 + 1),
    (N.factorial : ℂ) * (-1 : ℂ) ^ ell *
      (2 * x) ^ (N - 2 * ell) /
        ((ell.factorial : ℂ) * ((N - 2 * ell).factorial : ℂ))

/-- The weighted partial-matching numerator occurring in the total
coefficient `sum_m \widehat W_{n,m}`. -/
def matchingFactorialSum (N : ℕ) (rho : ℂ) : ℂ :=
  ∑ ell ∈ Finset.range (N / 2 + 1),
    (rho / 2) ^ ell * (N.factorial : ℂ) /
      ((ell.factorial : ℂ) * ((N - 2 * ell).factorial : ℂ))

/-- Elementary scaled-power identity behind the imaginary Hermite
specialization. -/
theorem scaled_power_identity
    (N ell : ℕ) (rho a : ℂ)
    (hrho : rho ≠ 0)
    (ha : a ^ 2 = -(2 / rho))
    (hle : 2 * ell ≤ N) :
    (-1 : ℂ) ^ ell * a ^ (N - 2 * ell) =
      a ^ N * (rho / 2) ^ ell := by
  have hpow : a ^ N = a ^ (N - 2 * ell) * (a ^ 2) ^ ell := by
    calc
      a ^ N = a ^ ((N - 2 * ell) + 2 * ell) := by
        rw [Nat.sub_add_cancel hle]
      _ = a ^ (N - 2 * ell) * a ^ (2 * ell) := by
        rw [pow_add]
      _ = a ^ (N - 2 * ell) * (a ^ 2) ^ ell := by
        rw [pow_mul]
  have hunit : (a ^ 2) * (rho / 2) = (-1 : ℂ) := by
    rw [ha]
    field_simp [hrho]
  calc
    (-1 : ℂ) ^ ell * a ^ (N - 2 * ell) =
        a ^ (N - 2 * ell) * (-1 : ℂ) ^ ell := by ring
    _ = a ^ (N - 2 * ell) *
        (((a ^ 2) * (rho / 2)) ^ ell) := by rw [hunit]
    _ = a ^ (N - 2 * ell) *
        ((a ^ 2) ^ ell * (rho / 2) ^ ell) := by rw [mul_pow]
    _ = (a ^ (N - 2 * ell) * (a ^ 2) ^ ell) *
        (rho / 2) ^ ell := by ring
    _ = a ^ N * (rho / 2) ^ ell := by rw [hpow]

/-- Exact physicists-Hermite identity for the weighted matching sum. -/
theorem physicistsHermiteValue_scaled
    (N : ℕ) (rho a : ℂ)
    (hrho : rho ≠ 0)
    (ha : a ^ 2 = -(2 / rho)) :
    physicistsHermiteValue N (a / 2) =
      a ^ N * matchingFactorialSum N rho := by
  unfold physicistsHermiteValue matchingFactorialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  have hell_lt : ell < N / 2 + 1 := Finset.mem_range.mp hell
  have hle : 2 * ell ≤ N := by omega
  have htwo : (2 : ℂ) * (a / 2) = a := by ring
  rw [htwo, mul_assoc,
    scaled_power_identity N ell rho a hrho ha hle]
  ring

/-- A complex-valued version of the total disconnected coefficient, with
`N=h*n`. -/
def disconnectedTotalComplex
    (h n : ℕ) (rho tau : ℂ) : ℂ :=
  1 / ((n.factorial : ℂ) * tau ^ n) *
    matchingFactorialSum (h * n) rho

/-- Equation (47) in a branch-independent form. -/
theorem disconnectedTotalComplex_eq_hermite
    (h n : ℕ) (rho tau a : ℂ)
    (hrho : rho ≠ 0)
    (ha0 : a ≠ 0)
    (ha : a ^ 2 = -(2 / rho)) :
    disconnectedTotalComplex h n rho tau =
      1 / ((n.factorial : ℂ) * tau ^ n) *
        physicistsHermiteValue (h * n) (a / 2) / a ^ (h * n) := by
  rw [physicistsHermiteValue_scaled (h * n) rho a hrho ha]
  unfold disconnectedTotalComplex
  field_simp [ha0]

/-- Multiplication form of equation (47), which does not divide by the
Hermite scaling root. -/
theorem disconnectedTotalComplex_mul_scale
    (h n : ℕ) (rho tau a : ℂ)
    (hrho : rho ≠ 0)
    (ha : a ^ 2 = -(2 / rho)) :
    a ^ (h * n) * disconnectedTotalComplex h n rho tau =
      1 / ((n.factorial : ℂ) * tau ^ n) *
        physicistsHermiteValue (h * n) (a / 2) := by
  rw [physicistsHermiteValue_scaled (h * n) rho a hrho ha]
  unfold disconnectedTotalComplex
  ring


/-- The complex total defined here is exactly the complexification of the
rational closed form in `DisconnectedWHat`. -/
theorem WTotalClosedForm_cast_complex
    (h r tau n : ℕ) :
    ((ExplicitFormulas.WTotalClosedForm h r tau n : ℚ) : ℂ) =
      disconnectedTotalComplex h n (r : ℂ) (tau : ℂ) := by
  rw [ExplicitFormulas.WTotalClosedForm_eq_sum]
  unfold disconnectedTotalComplex matchingFactorialSum
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  ring

/-- Equation (47) for the actual rational total coefficient after coercion
to `ℂ`. -/
theorem WTotalClosedForm_cast_eq_hermite
    (h r tau n : ℕ) (a : ℂ)
    (hr : 0 < r)
    (ha0 : a ≠ 0)
    (ha : a ^ 2 = -(2 / (r : ℂ))) :
    ((ExplicitFormulas.WTotalClosedForm h r tau n : ℚ) : ℂ) =
      1 / ((n.factorial : ℂ) * (tau : ℂ) ^ n) *
        physicistsHermiteValue (h * n) (a / 2) / a ^ (h * n) := by
  rw [WTotalClosedForm_cast_complex]
  exact disconnectedTotalComplex_eq_hermite h n (r : ℂ) (tau : ℂ) a
    (by exact_mod_cast hr.ne') ha0 ha


/-- The scaling used in the manuscript: `a = i sqrt(2/r)`. -/
def manuscriptHermiteScale (r : ℝ) : ℂ :=
  Complex.I * (Real.sqrt (2 / r) : ℂ)

/-- The manuscript scaling satisfies the branch-independent quadratic
identity required above. -/
theorem manuscriptHermiteScale_sq
    (r : ℝ) (hr : 0 < r) :
    manuscriptHermiteScale r ^ 2 = -(2 / (r : ℂ)) := by
  have hnonneg : 0 ≤ 2 / r := by positivity
  have hsqrt : Real.sqrt (2 / r) ^ 2 = 2 / r :=
    Real.sq_sqrt hnonneg
  have hsqrtC : ((Real.sqrt (2 / r) : ℝ) : ℂ) ^ 2 =
      ((2 / r : ℝ) : ℂ) := by
    exact_mod_cast hsqrt
  unfold manuscriptHermiteScale
  rw [mul_pow]
  rw [show Complex.I ^ 2 = (-1 : ℂ) by norm_num]
  rw [hsqrtC]
  push_cast
  ring

/-- The manuscript scaling is nonzero for positive `r`. -/
theorem manuscriptHermiteScale_ne_zero
    (r : ℝ) (hr : 0 < r) :
    manuscriptHermiteScale r ≠ 0 := by
  intro hz
  have hs := manuscriptHermiteScale_sq r hr
  rw [hz] at hs
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hrC] at hs
  norm_num at hs

/-- Equation (47) with the square-root choice printed in the paper. -/
theorem WTotalClosedForm_cast_eq_manuscriptHermite
    (h r tau n : ℕ) (hr : 0 < r) :
    ((ExplicitFormulas.WTotalClosedForm h r tau n : ℚ) : ℂ) =
      1 / ((n.factorial : ℂ) * (tau : ℂ) ^ n) *
        physicistsHermiteValue (h * n)
          (manuscriptHermiteScale (r : ℝ) / 2) /
        manuscriptHermiteScale (r : ℝ) ^ (h * n) := by
  apply WTotalClosedForm_cast_eq_hermite h r tau n
  · exact hr
  · exact manuscriptHermiteScale_ne_zero (r : ℝ) (by exact_mod_cast hr)
  · exact manuscriptHermiteScale_sq (r : ℝ) (by exact_mod_cast hr)


end
end HermiteExact
end PolytopeCounting
