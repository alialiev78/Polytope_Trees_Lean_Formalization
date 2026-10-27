module

public import Solution
public import Proofs.ManuscriptTreeExplicit
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# The quadratic case of Appendix A

For triangles (`h=3`, `r=1`, `tau=3`) the actual counting recurrence supplies
the formal branch `Y=X+Y^2` with constant term zero. We prove its uniqueness
and the corresponding square-root branch. The real radical, its branch
condition, the primitive in (64), and its derivative are checked below.
`AppendixARadicals` gives the higher-degree branches; `AppendixAAnalytic`
identifies all three with convergent counting series.
-/

namespace PolytopeCounting.AppendixA
noncomputable section
open ExplicitFormulas PowerSeries
universe u

/-- Auxiliary series built from the existing finite tree counts. -/
def triangleFormalY (L : Type u) [Fintype L] : PowerSeries ℚ :=
  X * auxiliarySeries (normalizedTreeCoefficient 3 1 (fun n => PolytopeTrees.R L n 3 1))

@[simp] theorem triangleFormalY_constantCoeff (L : Type u) [Fintype L] :
    constantCoeff (triangleFormalY L) = 0 := by simp [triangleFormalY]

/-- The quadratic equation is derived from the concrete cut--join recurrence. -/
theorem triangleFormalY_equation (L : Type u) [Group L] [Fintype L]
    [MulAction L (Fin 3)] (hcard : Fintype.card L = 3) :
    triangleFormalY L = X + triangleFormalY L ^ 2 := by
  let a := normalizedTreeCoefficient 3 1 (fun n => PolytopeTrees.R L n 3 1)
  have hrec : SatisfiesPaperTreeRecurrence 3 1 (fun n => PolytopeTrees.R L n 3 1) := by
    intro n hn
    simpa using PolytopeTrees.R_recurrence L n 3 1 (by decide) hn
  have ha1 : a 1 = 1 := by
    dsimp [a, normalizedTreeCoefficient]
    rw [PolytopeTrees.R_formula L 1 3 1 (by decide) (by decide) (by decide), hcard]
    norm_num
  have heq := functional_equation_of_auxiliary_recurrence 1 a
    (normalized_recurrence_of_paper_recurrence 3 1 _ hrec)
  rw [ha1] at heq
  norm_num only [map_one, one_mul] at heq
  have hm := congrArg (fun Z : PowerSeries ℚ => X * Z) heq
  change X * auxiliarySeries a = X + (X * auxiliarySeries a) ^ 2
  linear_combination hm

/-- The zero-constant-term branch is unique over the formal power series ring. -/
theorem triangleFormalY_unique (L : Type u) [Group L] [Fintype L]
    [MulAction L (Fin 3)] (hcard : Fintype.card L = 3)
    (Z : PowerSeries ℚ) (hZ0 : constantCoeff Z = 0) (hZ : Z = X + Z ^ 2) :
    Z = triangleFormalY L := by
  have hY := triangleFormalY_equation L hcard
  have hprod : (Z - triangleFormalY L) * (1 - Z - triangleFormalY L) = 0 := by
    linear_combination hZ - hY
  have hfactor : (1 - Z - triangleFormalY L : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have := congrArg constantCoeff heq
    simp [hZ0] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hfactor)

/-- The normalized square root is derived from the counting series. -/
def triangleFormalSqrt (L : Type u) [Fintype L] : PowerSeries ℚ :=
  1 - 2 * triangleFormalY L

theorem triangleFormalSqrt_spec (L : Type u) [Group L] [Fintype L]
    [MulAction L (Fin 3)] (hcard : Fintype.card L = 3) :
    constantCoeff (triangleFormalSqrt L) = 1 ∧
      triangleFormalSqrt L ^ 2 = 1 - 4 * X := by
  constructor
  · simp [triangleFormalSqrt]
  · dsimp [triangleFormalSqrt]
    linear_combination -4 * triangleFormalY_equation L hcard

theorem triangleFormalSqrt_unique (L : Type u) [Group L] [Fintype L]
    [MulAction L (Fin 3)] (hcard : Fintype.card L = 3)
    (S : PowerSeries ℚ) (hS0 : constantCoeff S = 1) (hS : S ^ 2 = 1 - 4 * X) :
    S = triangleFormalSqrt L := by
  have hspec := triangleFormalSqrt_spec L hcard
  have hp : (S - triangleFormalSqrt L) * (S + triangleFormalSqrt L) = 0 := by
    linear_combination hS - hspec.2
  have hn : S + triangleFormalSqrt L ≠ 0 := by
    intro he
    have := congrArg constantCoeff he
    norm_num [hS0, hspec.1] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hn)

/-- Polynomial primitive in the quadratic case. Its coefficients are
identified with the concrete tree counts below. -/
def triangleFormalR (L : Type u) [Fintype L] : PowerSeries ℚ :=
  C (1 / 6 : ℚ) * (2 * triangleFormalY L ^ 3 - 3 * triangleFormalY L ^ 4)

@[simp] theorem triangleFormalR_constantCoeff (L : Type u) [Fintype L] :
    constantCoeff (triangleFormalR L) = 0 := by simp [triangleFormalR]

theorem triangleFormalR_derivative (L : Type u) [Group L] [Fintype L]
    [MulAction L (Fin 3)] (hcard : Fintype.card L = 3) :
    derivative (R := ℚ) (triangleFormalR L) = triangleFormalY L - X := by
  have hY := triangleFormalY_equation L hcard
  have hd := congrArg (derivative (R := ℚ)) hY
  simp only [map_add, derivative_X, derivative_pow] at hd
  norm_num only at hd
  have hd2 : derivative (R := ℚ) (2 : PowerSeries ℚ) = 0 := by
    change derivative (R := ℚ) (C 2) = 0
    exact derivative_C
  have hd3 : derivative (R := ℚ) (3 : PowerSeries ℚ) = 0 := by
    change derivative (R := ℚ) (C 3) = 0
    exact derivative_C
  have hp : derivative (R := ℚ)
      (2 * triangleFormalY L ^ 3 - 3 * triangleFormalY L ^ 4) =
      6 * triangleFormalY L ^ 2 := by
    simp only [map_sub, Derivation.leibniz, derivative_pow, hd2, hd3, smul_eq_mul]
    norm_num
    linear_combination 6 * triangleFormalY L ^ 2 * hd
  have hc : C (1 / 6 : ℚ) * (6 : PowerSeries ℚ) = 1 := by
    change C (1 / 6 : ℚ) * C 6 = 1
    rw [← map_mul]
    norm_num
  rw [triangleFormalR, Derivation.leibniz, derivative_C, hp]
  simp only [smul_eq_mul, mul_zero, add_zero]
  rw [← mul_assoc, hc, one_mul]
  linear_combination -hY

/-- The polynomial primitive has the manuscript's factorial-normalized
coefficients, derived from the actual finite counts. -/
theorem triangleFormalR_coeff (L : Type u) [Group L] [Fintype L]
    [MulAction L (Fin 3)] (hcard : Fintype.card L = 3) (n : ℕ) (hn : 0 < n) :
    coeff (n + 2) (triangleFormalR L) =
      PolytopeTrees.R L n 3 1 / ((n + 2).factorial : ℚ) := by
  have hd := congrArg (coeff (n + 1)) (triangleFormalR_derivative L hcard)
  rw [coeff_derivative, map_sub] at hd
  have hY : coeff (n + 1) (triangleFormalY L) =
      PolytopeTrees.R L n 3 1 / ((n + 1).factorial : ℚ) := by
    unfold triangleFormalY
    rw [← pow_one (X : PowerSeries ℚ), coeff_X_pow_mul,
      coeff_auxiliarySeries_of_pos _ hn]
    simp [normalizedTreeCoefficient]
  have hX : coeff (n + 1) (X : PowerSeries ℚ) = 0 := by
    simp [coeff_X, hn.ne']
  rw [hY, hX, sub_zero] at hd
  have hfac : (((n + 2).factorial : ℕ) : ℚ) =
      (n + 2 : ℚ) * ((n + 1).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ (n + 1)
  have hn2 : (n + 2 : ℚ) ≠ 0 := by positivity
  rw [hfac]
  apply (eq_div_iff (mul_ne_zero hn2 (by positivity))).mpr
  push_cast at hd
  have hd' := congrArg (fun q : ℚ => q * ((n + 1).factorial : ℚ)) hd
  field_simp at hd'
  nlinarith [hd']

/-- Formula (64) as an exact formal-power-series identity, with denominators
cleared. The square root is the unique branch with constant coefficient one. -/
theorem triangleFormalR_radical (L : Type u) [Group L] [Fintype L]
    [MulAction L (Fin 3)] (hcard : Fintype.card L = 3) :
    12 * triangleFormalR L = 6 * X - 6 * X ^ 2 +
      (1 - 4 * X) * triangleFormalSqrt L - 1 := by
  have hX : (X : PowerSeries ℚ) = triangleFormalY L - triangleFormalY L ^ 2 := by
    linear_combination -triangleFormalY_equation L hcard
  have hc : (12 : PowerSeries ℚ) * C (1 / 6 : ℚ) = 2 := by
    change C 12 * C (1 / 6 : ℚ) = 2
    rw [← map_mul]
    norm_num
    rfl
  dsimp [triangleFormalR, triangleFormalSqrt]
  rw [← mul_assoc, hc, hX]
  ring

/-- The branch of `y^2-y+t=0` with value zero at the origin. -/
def triangleY (t : ℝ) : ℝ := (1 - Real.sqrt (1 - 4 * t)) / 2

/-- Formula (64), with `(1-4t)^(3/2)` written as `(1-4t)*sqrt(1-4t)`. -/
def triangleR (t : ℝ) : ℝ :=
  (t - t ^ 2 + (1 - 4 * t) * Real.sqrt (1 - 4 * t) / 6) / 2 - 1 / 12

@[simp] theorem triangleY_zero : triangleY 0 = 0 := by norm_num [triangleY]
@[simp] theorem triangleR_zero : triangleR 0 = 0 := by norm_num [triangleR]

theorem triangleY_equation (t : ℝ) (ht : t ≤ 1 / 4) :
    triangleY t ^ 2 = triangleY t - t := by
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - 4 * t)
  dsimp [triangleY]
  nlinarith

theorem triangleY_le_half (t : ℝ) : triangleY t ≤ 1 / 2 := by
  have hs := Real.sqrt_nonneg (1 - 4 * t)
  dsimp [triangleY]
  linarith

/-- The branch condition selects the radical uniquely, including the endpoint. -/
theorem triangleY_unique (t y : ℝ) (ht : t ≤ 1 / 4)
    (hy : y ^ 2 = y - t) (hbranch : y ≤ 1 / 2) : y = triangleY t := by
  have hs : Real.sqrt (1 - 4 * t) = 1 - 2 * y := by
    apply (Real.sqrt_eq_iff_eq_sq (by linarith) (by linarith)).mpr
    nlinarith
  simp only [triangleY, hs]
  ring

/-- The polynomial primitive and the radical expression agree. -/
theorem triangleR_polynomial (t : ℝ) (ht : t ≤ 1 / 4) :
    triangleY t ^ 3 / 3 - triangleY t ^ 4 / 2 = triangleR t := by
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - 4 * t)
  dsimp [triangleY, triangleR]
  linear_combination ((-3 * Real.sqrt (1 - 4 * t) ^ 2 +
    8 * Real.sqrt (1 - 4 * t) + 12 * t - 9) / 96) * hs

theorem triangleR_hasDerivAt (t : ℝ) (ht : t < 1 / 4) :
    HasDerivAt triangleR (triangleY t - t) t := by
  have hrad : 0 < 1 - 4 * t := by linarith
  have hspos : 0 < Real.sqrt (1 - 4 * t) := Real.sqrt_pos.mpr hrad
  have hs := Real.sq_sqrt hrad.le
  have hlin : HasDerivAt (fun x : ℝ => 1 - 4 * x) (-4) t := by
    convert ((hasDerivAt_id t).const_mul 4).const_sub 1 using 1 <;> norm_num
  have hsqrt := hlin.sqrt hrad.ne'
  have hd := (((hasDerivAt_id t).sub ((hasDerivAt_id t).pow 2)).add
    ((hlin.mul hsqrt).div_const 6)).div_const 2
  have hd' := hd.sub_const (1 / 12)
  convert hd' using 1
  · rfl
  · dsimp [triangleY]
    generalize Real.sqrt (1 - 4 * t) = s at hs hspos ⊢
    field_simp [hspos.ne']
    nlinarith

theorem triangleR_derivative_equation (t : ℝ) (ht : t < 1 / 4) :
    deriv triangleR t = (t + deriv triangleR t) ^ 2 := by
  rw [(triangleR_hasDerivAt t ht).deriv]
  have hy := triangleY_equation t ht.le
  convert hy.symm using 1
  ring

/-- The algebraic rewrite in A.1, independent of any radical branch. -/
theorem quartic_primitive_rewrite (r t y : ℝ) (hy : y ^ 4 = y - t) :
    (y ^ 5 / 5 - y ^ 8 / 2) / r = (y ^ 5 / 5 - (y - t) ^ 2 / 2) / r := by
  rw [show y ^ 8 = (y ^ 4) ^ 2 by ring, hy]

/-- The normalization displayed in A.2. -/
theorem square_primitive_rewrite (y : ℝ) :
    3 * (y ^ 4 / 12 - y ^ 6 / 6) = y ^ 4 / 4 - y ^ 6 / 2 := by ring

end
end PolytopeCounting.AppendixA
