module

public import Proofs.HermiteAsymptoticReduction
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! # The positive saddle and the exact Poisson representation

The weighted matching generating function is exp(z+r*z^2/2). Its positive
saddle gives an exact finite Poisson-weight sum. The local limit used with
this representation is proved in `MatchingLocalGaussian`.
-/

namespace PolytopeCounting.MatchingSaddle

noncomputable section
open Filter HermiteAsymptotic
open scoped Topology BigOperators

/-- Positive solution of s+r*s^2=N for positive r and N. -/
def saddle (N : ℕ) (r : ℝ) : ℝ :=
  (Real.sqrt (1 + 4 * r * N) - 1) / (2 * r)

theorem saddle_nonneg (N : ℕ) (r : ℝ) (hr : 0 < r) :
    0 ≤ saddle N r := by
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ 1 + 4 * r * (N : ℝ))
  have hpos := Real.sqrt_nonneg (1 + 4 * r * (N : ℝ))
  have hge : 1 ≤ Real.sqrt (1 + 4 * r * (N : ℝ)) := by nlinarith
  exact div_nonneg (sub_nonneg.mpr hge) (by positivity)

/-- The defining saddle equation is proved from the square-root formula. -/
theorem saddle_equation (N : ℕ) (r : ℝ) (hr : 0 < r) :
    saddle N r + r * (saddle N r)^2 = (N : ℝ) := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + 4 * r * (N : ℝ))
  unfold saddle
  field_simp [hr.ne']
  nlinarith

theorem saddle_pos (N : ℕ) (r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    0 < saddle N r := by
  have he := saddle_equation N r hr
  have hs := saddle_nonneg N r hr
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  by_contra h
  have hz : saddle N r = 0 := le_antisymm (not_lt.mp h) hs
  simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at he
  linarith

/-- There is no second nonnegative saddle. -/
theorem saddle_unique (N : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s)
    (he : s + r * s^2 = N) : s = saddle N r := by
  have hq := saddle_equation N r hr
  have hnon := saddle_nonneg N r hr
  have hfac : (s - saddle N r) * (1 + r * (s + saddle N r)) = 0 := by
    nlinarith
  have hp : 0 < 1 + r * (s + saddle N r) := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hp.ne')

/-- Stable rationalized formula, valid also at N=0. -/
theorem saddle_rationalized (N : ℕ) (r : ℝ) (hr : 0 < r) :
    saddle N r = 2 * N / (1 + Real.sqrt (1 + 4 * r * N)) := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + 4 * r * (N : ℝ))
  have hd : 1 + Real.sqrt (1 + 4 * r * (N : ℝ)) ≠ 0 := by positivity
  unfold saddle
  field_simp [hr.ne', hd]
  nlinarith

/-- Natural square-root scale. -/
def rootScale (N : ℕ) (r : ℝ) : ℝ := Real.sqrt ((N : ℝ) / r)

theorem rootScale_pos (N : ℕ) (r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    0 < rootScale N r := by unfold rootScale; positivity

theorem saddle_le_rootScale (N : ℕ) (r : ℝ) (hr : 0 < r) :
    saddle N r ≤ rootScale N r := by
  have he := saddle_equation N r hr
  have hs := saddle_nonneg N r hr
  have hu : 0 ≤ rootScale N r := Real.sqrt_nonneg _
  have hu2 : (rootScale N r)^2 = (N : ℝ) / r :=
    Real.sq_sqrt (by positivity)
  have hsq : (saddle N r)^2 ≤ (rootScale N r)^2 := by
    rw [hu2]
    apply (le_div_iff₀ hr).mpr
    nlinarith
  exact (sq_le_sq₀ hs hu).mp hsq

/-- The saddle differs from its square-root scale by a bounded amount. -/
theorem rootScale_sub_le_saddle (N : ℕ) (r : ℝ) (hr : 0 < r) :
    rootScale N r - 1 / (2 * r) ≤ saddle N r := by
  have he := saddle_equation N r hr
  have hs := saddle_nonneg N r hr
  have hu : 0 ≤ rootScale N r := Real.sqrt_nonneg _
  have hu2 : (rootScale N r)^2 = (N : ℝ) / r :=
    Real.sq_sqrt (by positivity)
  have hshift : (saddle N r + 1 / (2 * r))^2 =
      (rootScale N r)^2 + 1 / (4 * r^2) := by
    rw [hu2]
    field_simp [hr.ne']
    nlinarith
  have hc : 0 ≤ 1 / (4 * r^2) := by positivity
  have hp : 0 ≤ saddle N r + 1 / (2 * r) := by positivity
  have hle : rootScale N r ≤ saddle N r + 1 / (2 * r) :=
    (sq_le_sq₀ hu hp).mp (by nlinarith [hc])
  linarith

/-- Normalize the saddle before passing to a limit; no varying-exponent
continuity assertion is used. -/
theorem saddle_ratio_rewrite (N : ℕ) (r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    saddle N r / rootScale N r =
      (Real.sqrt (1 / (N : ℝ) + 4 * r) - Real.sqrt (1 / (N : ℝ))) /
        (2 * Real.sqrt r) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsN : Real.sqrt (N : ℝ) ≠ 0 := by positivity
  have hsR : Real.sqrt r ≠ 0 := by positivity
  have heR := Real.sq_sqrt hr.le
  have hratio : Real.sqrt (1 + 4 * r * N) / Real.sqrt (N : ℝ) =
      Real.sqrt (1 / (N : ℝ) + 4 * r) := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ 1 + 4 * r * (N : ℝ))]
    congr 1
    field_simp
  rw [← hratio]
  unfold saddle rootScale
  rw [Real.sqrt_div hn.le, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
    Real.sqrt_one]
  field_simp [hn.ne', hr.ne', hsN, hsR]
  rw [heR]
  ring

/-- The saddle has the predicted square-root scale, unconditionally. -/
theorem saddle_ratio_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ ↦ saddle N r / rootScale N r) atTop (𝓝 1) := by
  have hz : Tendsto (fun N : ℕ ↦ 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hA := Real.continuous_sqrt.continuousAt.tendsto.comp
    (hz.add_const (4 * r))
  have hB := Real.continuous_sqrt.continuousAt.tendsto.comp hz
  have hh := (hA.sub hB).div_const (2 * Real.sqrt r)
  have hsR : Real.sqrt r ≠ 0 := by positivity
  have hs4 : Real.sqrt (4 * r) = 2 * Real.sqrt r := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have ht : Tendsto
      (fun N : ℕ ↦ (Real.sqrt (1 / (N : ℝ) + 4 * r) -
        Real.sqrt (1 / (N : ℝ))) / (2 * Real.sqrt r)) atTop (𝓝 1) := by
    simpa [hs4, hsR] using hh
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (saddle_ratio_rewrite N r hN hr).symm

/-- An exact identity determines the constant-order correction from the
ratio limit; merely bounding the saddle is not enough for this correction. -/
theorem saddle_difference_rewrite (N : ℕ) (r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    saddle N r - rootScale N r =
      -(saddle N r / rootScale N r) /
        (r * (saddle N r / rootScale N r + 1)) := by
  have hu := rootScale_pos N r hN hr
  have hs := saddle_nonneg N r hr
  have he := saddle_equation N r hr
  have hu2 : (rootScale N r)^2 = (N : ℝ) / r :=
    Real.sq_sqrt (by positivity)
  have hd : saddle N r / rootScale N r + 1 ≠ 0 := by positivity
  field_simp [hr.ne', hu.ne', hd]
  have hb : r * (rootScale N r)^2 = (N : ℝ) := by
    rw [hu2]; field_simp
  nlinarith

theorem saddle_difference_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ ↦ saddle N r - rootScale N r)
      atTop (𝓝 (-(1 / (2 * r)))) := by
  have ht := saddle_ratio_tendsto r hr
  have hden := (ht.add_const 1).const_mul r
  have hh := ht.neg.div hden (by positivity : r * (1 + 1) ≠ 0)
  have hh' : Tendsto
      (fun N : ℕ ↦ -(saddle N r / rootScale N r) /
        (r * (saddle N r / rootScale N r + 1)))
      atTop (𝓝 (-(1 / (2 * r)))) := by
    convert hh using 1 <;> norm_num <;> ring
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (saddle_difference_rewrite N r hN hr).symm

/-- Gaussian curvature at the saddle. -/
def curvature (N : ℕ) (r : ℝ) := saddle N r + 2 * r * (saddle N r)^2

theorem curvature_eq (N : ℕ) (r : ℝ) (hr : 0 < r) :
    curvature N r = 2 * N - saddle N r := by
  unfold curvature
  nlinarith [saddle_equation N r hr]

theorem curvature_pos (N : ℕ) (r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    0 < curvature N r := by
  unfold curvature
  have hs := saddle_pos N r hN hr
  positivity

/-- The saddle is sublinear. -/
theorem saddle_div_index_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ ↦ saddle N r / (N : ℝ)) atTop (𝓝 0) := by
  have ht := saddle_ratio_tendsto r hr
  have hz : Tendsto (fun N : ℕ ↦ 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hz
  have hsR : Real.sqrt r ≠ 0 := by positivity
  have hh := ht.mul (hsqrt.div_const (Real.sqrt r))
  have hh' : Tendsto
      (fun N : ℕ ↦ (saddle N r / rootScale N r) *
        (Real.sqrt (1 / (N : ℝ)) / Real.sqrt r)) atTop (𝓝 0) := by
    simpa using hh
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsN : Real.sqrt (N : ℝ) ≠ 0 := by positivity
  have hsq := Real.sq_sqrt hn.le
  unfold rootScale
  rw [Real.sqrt_div hn.le, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
    Real.sqrt_one]
  field_simp [hsR, hsN, hn.ne']
  rw [hsq]

/-- The local Gaussian variance is asymptotic to 2N. -/
theorem curvature_ratio_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ ↦ curvature N r / (2 * N)) atTop (𝓝 1) := by
  have ht := (saddle_div_index_tendsto r hr).div_const 2
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub ht
  have hh' : Tendsto
      (fun N : ℕ ↦ 1 - (saddle N r / (N : ℝ)) / 2) atTop (𝓝 1) := by
    simpa using hh
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [curvature_eq N r hr]
  field_simp

/-! ### Exact finite probability-weight identity -/

/-- A nonnegative Poisson weight, without invoking probability theory. -/
def poissonWeight (a : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-a) * a^k / (k.factorial : ℝ)

/-- The lattice weight of X+2Y=N, where the two Poisson parameters would be
s and r*s^2/2.  This is an explicit finite sum, not an assumed distribution. -/
def latticeWeight (N : ℕ) (r s : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N / 2 + 1),
    poissonWeight s (N - 2*k) * poissonWeight (r*s^2/2) k

theorem latticeWeight_nonneg (N : ℕ) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    0 ≤ latticeWeight N r s := by
  apply Finset.sum_nonneg
  intro k hk
  unfold poissonWeight
  positivity

/-- The exact bridge from the original factorial sum to real positive
Poisson weights.  The missing analytic step is a local Gaussian estimate
for this concrete sum at `s = saddle N r`. -/
theorem latticeWeight_eq (N : ℕ) (r s : ℝ) :
    latticeWeight N r s =
      Real.exp (-(s + r*s^2/2)) * s^N / (N.factorial : ℝ) *
        matchingFactorialSumReal N r := by
  unfold latticeWeight matchingFactorialSumReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk2 : 2*k ≤ N := by
    have hk' : k ≤ N/2 := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    omega
  have hp : N - 2*k + 2*k = N := Nat.sub_add_cancel hk2
  have he : Real.exp (-s) * Real.exp (-(r*s^2/2)) =
      Real.exp (-(s+r*s^2/2)) := by rw [← Real.exp_add]; congr 1 <;> ring
  have hpw : s^(N-2*k) * (s^2)^k = s^N := by
    rw [← pow_mul, ← pow_add, hp]
  have hnfac : (N.factorial : ℝ) ≠ 0 := by positivity
  have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hdfac : ((N-2*k).factorial : ℝ) ≠ 0 := by positivity
  have hpower : (r*s^2/2)^k = (r/2)^k * (s^2)^k := by
    rw [show r*s^2/2 = (r/2)*s^2 by ring, mul_pow]
  unfold poissonWeight
  rw [hpower]
  calc
    _ = (Real.exp (-s) * Real.exp (-(r*s^2/2))) *
        (r/2)^k * (s^(N-2*k)*(s^2)^k) /
          (((N-2*k).factorial : ℝ) * (k.factorial : ℝ)) := by ring
    _ = _ := by
      rw [he, hpw]
      field_simp

/-- The saddle-point leading term.  No asymptotic assertion is part of the
definition. -/
def saddleLeading (N : ℕ) (r : ℝ) : ℝ :=
  (N.factorial : ℝ) * Real.exp (saddle N r + r * (saddle N r)^2 / 2) /
    ((saddle N r)^N * Real.sqrt (2 * Real.pi * curvature N r))

/-- Exact reduction to the local limit proved in `MatchingLocalGaussian`. -/
theorem matching_saddle_ratio (N : ℕ) (r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    matchingFactorialSumReal N r / saddleLeading N r =
      Real.sqrt (2 * Real.pi * curvature N r) *
        latticeWeight N r (saddle N r) := by
  rw [latticeWeight_eq]
  unfold saddleLeading
  have hs : saddle N r ≠ 0 := (saddle_pos N r hN hr).ne'
  have hb : Real.sqrt (2 * Real.pi * curvature N r) ≠ 0 := by
    have hp := curvature_pos N r hN hr
    positivity
  rw [Real.exp_neg]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end
end PolytopeCounting.MatchingSaddle
