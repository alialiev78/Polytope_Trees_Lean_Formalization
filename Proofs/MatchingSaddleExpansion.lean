module

public import Proofs.MatchingSaddlePoint
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic

@[expose] public section

/-! # Expansion of the positive saddle

The saddle leading term is asymptotic to the Hermite normalization. The
quadratic term in log(1+t), with t=1/(r*s), supplies exp(-1/(4r)).
The local lattice estimate is provided by `MatchingLocalGaussian`.
-/

namespace PolytopeCounting.MatchingSaddle

noncomputable section
open Filter HermiteAsymptotic
open scoped Topology

/-- The saddle tends to infinity. This is derived directly from its equation. -/
theorem saddle_tendsto_atTop (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ ↦ saddle N r) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  let c := max b 0
  have hc : 0 ≤ c := le_max_right _ _
  have hb : b ≤ c := le_max_left _ _
  have hN : ∀ᶠ N : ℕ in atTop, c + r*c^2 + 1 ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hN] with N hN
  have he := saddle_equation N r hr
  have hs := saddle_nonneg N r hr
  have hcs : c < saddle N r := by
    by_contra h
    have hsle : saddle N r ≤ c := not_lt.mp h
    have hsq : (saddle N r)^2 ≤ c^2 := (sq_le_sq₀ hs hc).2 hsle
    nlinarith [mul_le_mul_of_nonneg_left hsq hr.le]
  exact hb.trans hcs.le

theorem inv_saddle_tendsto_zero (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ ↦ (saddle N r)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (saddle_tendsto_atTop r hr)

/-- Explicit third-order error bound; this is a library Taylor estimate
specialized to -x and two terms, not an assumed asymptotic expansion. -/
theorem log_one_add_quadratic_bound (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
    |Real.log (1+x) - x + x^2/2| ≤ 2*x^3 := by
  have habs : |(-x)| < 1 := by rw [abs_neg, abs_of_nonneg hx]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 2
  have h' : |Real.log (1+x) - x + x^2/2| ≤ x^3/(1-x) := by
    convert h using 1 <;>
      simp [Finset.sum_range_succ, abs_of_nonneg hx, abs_neg] <;> ring
  have hd : 0 < 1-x := by linarith
  refine h'.trans ((div_le_iff₀ hd).2 ?_)
  have hc : 0 ≤ x^3 := pow_nonneg hx _
  nlinarith

def saddleSmallParameter (N : ℕ) (r : ℝ) : ℝ := 1/(r*saddle N r)

theorem saddleSmallParameter_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N ↦ saddleSmallParameter N r) atTop (𝓝 0) := by
  simpa [saddleSmallParameter, div_eq_mul_inv, mul_inv_rev] using
    (inv_saddle_tendsto_zero r hr).mul_const r⁻¹

/-- The error after the constant term in N*log(1+t)/2. -/
def saddleLogError (N : ℕ) (r : ℝ) : ℝ :=
  (N : ℝ)/2 * Real.log (1+saddleSmallParameter N r) -
    saddle N r/2 - 1/(4*r)

/-- Exact quadratic cancellation, before taking limits. -/
theorem saddleLogError_rewrite (N : ℕ) (r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    saddleLogError N r =
      (N : ℝ)/2 * (Real.log (1+saddleSmallParameter N r) -
        saddleSmallParameter N r + (saddleSmallParameter N r)^2/2) -
      1/(4*r^2*saddle N r) := by
  have hs := (saddle_pos N r hN hr).ne'
  have he := saddle_equation N r hr
  unfold saddleLogError saddleSmallParameter
  rw [← he]
  field_simp [hs, hr.ne']
  ring

/-- An effective O(1/s) bound for the logarithmic error. -/
theorem saddleLogError_bound (N : ℕ) (r : ℝ) (hN : 0 < N) (hr : 0 < r)
    (ht : saddleSmallParameter N r ≤ 1/2) :
    |saddleLogError N r| ≤
      5/(4*r^2) * (saddle N r)⁻¹ +
      1/r^3 * ((saddle N r)⁻¹)^2 := by
  have hs := saddle_pos N r hN hr
  have ht0 : 0 ≤ saddleSmallParameter N r := by
    unfold saddleSmallParameter; positivity
  have hlog := log_one_add_quadratic_bound (saddleSmallParameter N r) ht0 ht
  rw [saddleLogError_rewrite N r hN hr]
  calc
    _ ≤ |(N : ℝ)/2 * (Real.log (1+saddleSmallParameter N r) -
        saddleSmallParameter N r + (saddleSmallParameter N r)^2/2)| +
        |1/(4*r^2*saddle N r)| := abs_sub _ _
    _ ≤ (N : ℝ) * (saddleSmallParameter N r)^3 +
        1/(4*r^2*saddle N r) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)/2),
        abs_of_nonneg (by positivity : 0 ≤ 1/(4*r^2*saddle N r))]
      nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (N : ℝ)/2)]
    _ = _ := by
      rw [← saddle_equation N r hr]
      unfold saddleSmallParameter
      field_simp [hs.ne', hr.ne']
      ring

theorem saddleLogError_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N ↦ saddleLogError N r) atTop (𝓝 0) := by
  have hi := inv_saddle_tendsto_zero r hr
  have hbound := (hi.const_mul (5/(4*r^2))).add ((hi.pow 2).const_mul (1/r^3))
  have hsmall : ∀ᶠ N in atTop, saddleSmallParameter N r ≤ 1/2 :=
    (saddleSmallParameter_tendsto r hr).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  apply squeeze_zero_norm' (a := fun N ↦
    5/(4*r^2)*(saddle N r)⁻¹ + 1/r^3*((saddle N r)⁻¹)^2)
  · filter_upwards [eventually_ge_atTop 1, hsmall] with N hN ht
    simpa only [Real.norm_eq_abs] using saddleLogError_bound N r hN hr ht
  · simpa using hbound

/-- The usual Stirling ratio, independent of the matching sequence. -/
def saddleStirlingRatio (N : ℕ) : ℝ :=
  (N.factorial : ℝ) /
    (Real.sqrt (2*(N : ℝ)*Real.pi) * ((N : ℝ)/Real.exp 1)^N)

theorem saddleStirlingRatio_tendsto :
    Tendsto saddleStirlingRatio atTop (𝓝 1) := by
  have hs := Stirling.factorial_isEquivalent_stirling
  have hz : ∀ᶠ N : ℕ in atTop,
      Real.sqrt (2*(N : ℝ)*Real.pi) * ((N : ℝ)/Real.exp 1)^N ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : 0 < (N : ℝ) := by exact_mod_cast hN
    positivity
  exact (Asymptotics.isEquivalent_iff_tendsto_one hz).mp hs

/-- Multiplicative remainder whose logarithm tends to zero. -/
def saddleExponentError (N : ℕ) (r : ℝ) : ℝ :=
  saddle N r - rootScale N r + 1/(2*r) + saddleLogError N r

theorem saddleExponentError_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N ↦ saddleExponentError N r) atTop (𝓝 0) := by
  have hs := (saddle_difference_tendsto r hr).add_const (1/(2*r))
  simpa [saddleExponentError] using hs.add (saddleLogError_tendsto r hr)

/-- All logarithmic relations needed for the exact leading-term identity. -/
theorem log_index_from_saddle (N : ℕ) (r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    Real.log (N : ℝ) = Real.log r + 2*Real.log (saddle N r) +
      Real.log (1+saddleSmallParameter N r) := by
  have hs := saddle_pos N r hN hr
  have ht : 0 < 1+saddleSmallParameter N r := by
    unfold saddleSmallParameter; positivity
  have he : (N : ℝ) = r*(saddle N r)^2*(1+saddleSmallParameter N r) := by
    rw [← saddle_equation N r hr]
    unfold saddleSmallParameter
    field_simp [hr.ne', hs.ne']
    ring
  rw [he, Real.log_mul (by positivity) ht.ne',
    Real.log_mul hr.ne' (pow_ne_zero 2 hs.ne'), Real.log_pow]
  norm_num

/-- Exact ratio. The factorial is not replaced by its approximation here. -/
theorem saddleLeading_ratio_rewrite (N : ℕ) (r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    saddleLeading N r / matchingHermiteLeadingTerm N r =
      saddleStirlingRatio N * Real.sqrt (2*(N : ℝ)/curvature N r) *
        Real.exp (saddleExponentError N r) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs := saddle_pos N r hN hr
  have hb := curvature_pos N r hN hr
  have ht : 0 < 1+saddleSmallParameter N r := by
    unfold saddleSmallParameter; positivity
  have hL : 0 < saddleLeading N r / matchingHermiteLeadingTerm N r := by
    have hp := matchingHermiteLeadingTerm_pos N r hr
    unfold saddleLeading
    positivity
  have hR : 0 < saddleStirlingRatio N * Real.sqrt (2*(N : ℝ)/curvature N r) *
      Real.exp (saddleExponentError N r) := by
    unfold saddleStirlingRatio
    positivity
  have hindex := log_index_from_saddle N r hN hr
  have he := saddle_equation N r hr
  have hlog : Real.log (saddleLeading N r / matchingHermiteLeadingTerm N r) =
      Real.log (saddleStirlingRatio N * Real.sqrt (2*(N : ℝ)/curvature N r) *
        Real.exp (saddleExponentError N r)) := by
    simp (disch := positivity) only [saddleLeading, matchingHermiteLeadingTerm,
      saddleStirlingRatio, saddleExponentError, saddleLogError, rootScale,
      Real.rpow_eq_pow, Real.log_mul, Real.log_div, Real.log_pow, Real.log_rpow,
      Real.log_sqrt, Real.log_exp, Real.log_one]
    linear_combination he / 2 + ((N : ℝ) / 2) * hindex
  calc
    _ = Real.exp (Real.log (saddleLeading N r / matchingHermiteLeadingTerm N r)) :=
      (Real.exp_log hL).symm
    _ = _ := by rw [hlog, Real.exp_log hR]

/-- Completed expansion: there is no local-limit or Hermite hypothesis here. -/
theorem saddleLeading_equivalent_hermite (r : ℝ) (hr : 0 < r) :
    SequenceEquivalent (fun N ↦ saddleLeading N r)
      (fun N ↦ matchingHermiteLeadingTerm N r) := by
  have hc := (curvature_ratio_tendsto r hr).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hroot : Tendsto (fun N : ℕ ↦ Real.sqrt (2*(N : ℝ)/curvature N r))
      atTop (𝓝 1) := by
    simpa only [inv_one, inv_div, Real.sqrt_one] using hc.sqrt
  have hexp := (saddleExponentError_tendsto r hr).rexp
  have hprod := (saddleStirlingRatio_tendsto.mul hroot).mul hexp
  unfold SequenceEquivalent
  apply (show Tendsto (fun N ↦ saddleStirlingRatio N *
      Real.sqrt (2*(N : ℝ)/curvature N r) * Real.exp (saddleExponentError N r))
      atTop (𝓝 1) by simpa using hprod).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (saddleLeading_ratio_rewrite N r hN hr).symm

/-- Transfer of the local lattice limit to the matching asymptotic. -/
theorem matchingEquivalent_of_localGaussian (r : ℝ) (hr : 0 < r)
    (hlocal : Tendsto (fun N ↦ Real.sqrt (2*Real.pi*curvature N r) *
      latticeWeight N r (saddle N r)) atTop (𝓝 1)) :
    SequenceEquivalent (fun N ↦ matchingFactorialSumReal N r)
      (fun N ↦ matchingHermiteLeadingTerm N r) := by
  have hs := saddleLeading_equivalent_hermite r hr
  unfold SequenceEquivalent at hs ⊢
  have hmul := hlocal.mul hs
  apply (show Tendsto (fun N ↦
      (Real.sqrt (2*Real.pi*curvature N r) * latticeWeight N r (saddle N r)) *
      (saddleLeading N r / matchingHermiteLeadingTerm N r)) atTop (𝓝 1)
      by simpa using hmul).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← matching_saddle_ratio N r hN hr]
  have ha : saddleLeading N r ≠ 0 := by
    have hp := saddle_pos N r hN hr
    have hb := curvature_pos N r hN hr
    unfold saddleLeading
    positivity
  field_simp [ha]

end
end PolytopeCounting.MatchingSaddle
