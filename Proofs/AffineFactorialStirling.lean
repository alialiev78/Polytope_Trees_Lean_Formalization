module

public import Proofs.TreeFixedCoreAsymptotics

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Removing the affine-factorial Stirling hypotheses

Fixed shifts are handled by the factorial recurrence, not by taking a
limit through a variable exponent.  The only imported asymptotic input is
Mathlib's proved Stirling theorem.  The leading terms are then simplified
by exact equalities for positive n.  No asymptotic hypothesis appears in
the final corollaries.
-/

namespace PolytopeCounting.AffineStirling

noncomputable section
open Filter Asymptotics HermiteAsymptotic GeneralAsymptotics
open scoped Topology BigOperators

/-- A positive integral dilation tends to infinity. -/
theorem nat_dilation_tendsto (a : ℕ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ a * n) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  have ha1 : 1 ≤ a := ha
  nlinarith

/-- Every fixed affine shift is negligible relative to a positive dilation. -/
theorem linear_shift_equivalent (a : ℕ) (ha : 0 < a) (c : ℝ) :
    IsEquivalent atTop (fun n : ℕ ↦ ((a * n : ℕ) : ℝ) + c)
      (fun n : ℕ ↦ ((a * n : ℕ) : ℝ)) := by
  have ht : Tendsto (fun n : ℕ ↦ ((a * n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (nat_dilation_tendsto a ha)
  have hn : Tendsto (fun n : ℕ ↦ ‖((a * n : ℕ) : ℝ)‖) atTop atTop := by
    simpa only [Real.norm_eq_abs, Nat.abs_cast] using ht
  exact IsEquivalent.refl.add_const_of_norm_tendsto_atTop hn

/-- `(an+s)! ~ (an)! (an)^s` for fixed natural shift s. -/
theorem factorial_shift_equivalent (a s : ℕ) (ha : 0 < a) :
    IsEquivalent atTop
      (fun n : ℕ ↦ ((a * n + s).factorial : ℝ))
      (fun n : ℕ ↦ ((a * n).factorial : ℝ) * ((a * n : ℕ) : ℝ) ^ s) := by
  induction s with
  | zero => simpa using (IsEquivalent.refl
      (u := fun n : ℕ ↦ ((a * n).factorial : ℝ)) (l := atTop))
  | succ s ih =>
      have hs := linear_shift_equivalent a ha ((s : ℝ) + 1)
      have hh := ih.mul hs
      convert hh using 1 <;> funext n
      · change ((a * n + (s + 1)).factorial : ℝ) = _
        rw [show a * n + (s + 1) = (a * n + s) + 1 by omega,
          Nat.factorial_succ]
        push_cast
        simp only [Pi.mul_apply]
        ring
      · simp [pow_succ] <;> ring

/-- Stirling with a fixed shift, without any additional limit assumptions. -/
theorem affine_factorial_stirling (a s : ℕ) (ha : 0 < a) :
    IsEquivalent atTop
      (fun n : ℕ ↦ ((a * n + s).factorial : ℝ))
      (fun n : ℕ ↦ stirlingApprox (a * n) * ((a * n : ℕ) : ℝ) ^ s) := by
  have hst : IsEquivalent atTop
      (fun n : ℕ ↦ ((a * n).factorial : ℝ))
      (fun n : ℕ ↦ stirlingApprox (a * n)) := by
    simpa only [stirlingApprox, Function.comp_def] using
      Stirling.factorial_isEquivalent_stirling.comp_tendsto
        (nat_dilation_tendsto a ha)
  exact (factorial_shift_equivalent a s ha).trans (hst.mul IsEquivalent.refl)

/-- Growth constant, using only integer powers. -/
def growth (q : ℕ) : ℝ :=
  ((q + 1 : ℕ) : ℝ) ^ (q + 1) / (q : ℝ) ^ q

/-- A half-integral-power-free leading term for the shifted ratio. -/
def shiftedLeading (q s t n : ℕ) : ℝ :=
  Real.sqrt ((q + 1 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ) ^ s /
    (Real.sqrt (2 * Real.pi) * Real.sqrt (q : ℝ) * (q : ℝ) ^ t) *
    ((n : ℝ) ^ s / (Real.sqrt (n : ℝ) * (n : ℝ) ^ t)) * growth q ^ n

theorem shiftedLeading_pos (q s t n : ℕ) (hq : 0 < q) (hn : 0 < n) :
    0 < shiftedLeading q s t n := by
  unfold shiftedLeading growth
  positivity

/-- Exact dilation formula for the standard Stirling approximation. -/
theorem stirlingApprox_dilate (a n : ℕ) :
    stirlingApprox (a * n) =
      Real.sqrt (a : ℝ) * Real.sqrt (2 * (n : ℝ) * Real.pi) *
        ((a : ℝ) ^ a) ^ n * ((n : ℝ) / Real.exp 1) ^ (a * n) := by
  unfold stirlingApprox
  have hroot : 2 * ((a * n : ℕ) : ℝ) * Real.pi =
      (a : ℝ) * (2 * (n : ℝ) * Real.pi) := by push_cast; ring
  have hbase : ((a * n : ℕ) : ℝ) / Real.exp 1 =
      (a : ℝ) * ((n : ℝ) / Real.exp 1) := by push_cast; ring
  rw [hroot, Real.sqrt_mul (Nat.cast_nonneg a), hbase, mul_pow,
    pow_mul (a : ℝ) a n]
  ring

/-- The cancellation of exponential factors uses `(q+1)n=qn+n` exactly. -/
theorem unshifted_stirling_quotient (q n : ℕ) (hq : 0 < q) (hn : 0 < n) :
    stirlingApprox ((q + 1) * n) /
        (stirlingApprox n * stirlingApprox (q * n)) =
      Real.sqrt ((q + 1 : ℕ) : ℝ) /
        (Real.sqrt (2 * Real.pi) * Real.sqrt (q : ℝ) * Real.sqrt (n : ℝ)) *
      growth q ^ n := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : Real.sqrt (2 * (n : ℝ) * Real.pi) ≠ 0 := by positivity
  have hs' : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hsq : Real.sqrt (q : ℝ) ≠ 0 := by positivity
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hu : ((n : ℝ) / Real.exp 1) ≠ 0 := by positivity
  rw [stirlingApprox_dilate (q + 1) n, stirlingApprox_dilate q n]
  unfold stirlingApprox growth
  rw [show (q + 1) * n = q * n + n by ring,
    pow_add ((n : ℝ) / Real.exp 1) (q * n) n]
  rw [show 2 * (n : ℝ) * Real.pi = (2 * Real.pi) * n by ring,
    Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  rw [div_pow (((q + 1 : ℕ) : ℝ) ^ (q + 1)) ((q : ℝ) ^ q) n]
  field_simp [hqR.ne', hnR.ne', hs', hsq, hsn, hu]

/-- Exact simplification of the leading quotient with fixed shifts. -/
theorem shifted_stirling_quotient (q s t n : ℕ) (hq : 0 < q) (hn : 0 < n) :
    (stirlingApprox ((q + 1) * n) * (((q + 1) * n : ℕ) : ℝ) ^ s) /
        (stirlingApprox n *
          (stirlingApprox (q * n) * ((q * n : ℕ) : ℝ) ^ t)) =
      shiftedLeading q s t n := by
  calc
    _ = (stirlingApprox ((q + 1) * n) /
          (stirlingApprox n * stirlingApprox (q * n))) *
        ((((q + 1) * n : ℕ) : ℝ) ^ s / ((q * n : ℕ) : ℝ) ^ t) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = shiftedLeading q s t n := by
      rw [unshifted_stirling_quotient q n hq hn]
      unfold shiftedLeading
      push_cast
      simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
      ring

/-- Master shifted factorial-ratio theorem. -/
theorem factorial_ratio_equivalent (q s t : ℕ) (hq : 0 < q) :
    IsEquivalent atTop
      (fun n : ℕ ↦ (((q + 1) * n + s).factorial : ℝ) /
        ((n.factorial : ℝ) * ((q * n + t).factorial : ℝ)))
      (shiftedLeading q s t) := by
  have hnum := affine_factorial_stirling (q + 1) s (by omega)
  have hden0 : IsEquivalent atTop (fun n : ℕ ↦ (n.factorial : ℝ))
      (fun n : ℕ ↦ stirlingApprox n) := by
    simpa [stirlingApprox] using Stirling.factorial_isEquivalent_stirling
  have hden1 := affine_factorial_stirling q t hq
  have hr := hnum.div (hden0.mul hden1)
  apply hr.congr_right
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact shifted_stirling_quotient q s t n hq hn

/-- Ratio orientation used by the original project. -/
theorem factorial_ratio_tendsto (q s t : ℕ) (hq : 0 < q) :
    SequenceEquivalent
      (fun n : ℕ ↦ (((q + 1) * n + s).factorial : ℝ) /
        ((n.factorial : ℝ) * ((q * n + t).factorial : ℝ)))
      (shiftedLeading q s t) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp
    (factorial_ratio_equivalent q s t hq)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (shiftedLeading_pos q s t n hq hn).ne'

/-- Exact half-integer power simplification for positive bases. -/
theorem rpow_nat_add_half (x : ℝ) (hx : 0 < x) (s : ℕ) :
    Real.rpow x ((s : ℝ) + 1 / 2) = x ^ s * Real.sqrt x := by
  rw [Real.rpow_eq_pow, Real.rpow_add hx, Real.rpow_natCast, ← Real.sqrt_eq_rpow]

/-- Negative half-integer powers are reciprocal square-root expressions. -/
theorem rpow_neg_nat_add_half (x : ℝ) (hx : 0 < x) (s : ℕ) :
    Real.rpow x (-((s : ℝ) + 1 / 2)) = (x ^ s * Real.sqrt x)⁻¹ := by
  rw [Real.rpow_eq_pow, Real.rpow_neg hx.le]
  exact congrArg (fun y : ℝ ↦ y⁻¹) (rpow_nat_add_half x hx s)

theorem explicit_rpow_natCast (x : ℝ) (n : ℕ) : Real.rpow x (n : ℝ) = x ^ n :=
  Real.rpow_natCast x n

/-- The tree leading term in precisely the manuscript's real-power form. -/
theorem tree_leading_rewrite (h n : ℕ) (hh : 3 ≤ h) (hn : 0 < n) :
    shiftedLeading (h - 2) 0 2 n =
      Real.sqrt (h - 1 : ℝ) /
        (Real.sqrt (2 * Real.pi) * Real.rpow (h - 2 : ℝ) (5 / 2 : ℝ)) *
      Real.rpow (n : ℝ) (-5 / 2 : ℝ) *
      (Real.rpow (h - 1 : ℝ) (h - 1 : ℝ) /
        Real.rpow (h - 2 : ℝ) (h - 2 : ℝ)) ^ n := by
  have hq : 0 < ((h - 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < h - 2 by omega)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have h1 : (h - 1 : ℝ) = (((h - 2) + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ h)]
    norm_num <;> ring
  have h2 : (h - 2 : ℝ) = ((h - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ h)]; norm_num
  rw [h1, h2, explicit_rpow_natCast, explicit_rpow_natCast]
  rw [show (5 / 2 : ℝ) = (2 : ℕ) + 1 / 2 by norm_num,
    rpow_nat_add_half _ hq]
  rw [show (-5 / 2 : ℝ) = -((2 : ℕ) + 1 / 2) by norm_num,
    rpow_neg_nat_add_half _ hnR]
  simp only [shiftedLeading, growth, pow_zero, one_mul,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- The fixed-core leading term; the cancellation of n^(h0-1) is exact. -/
theorem fixed_core_leading_rewrite (h₀ h n : ℕ)
    (hh₀ : 1 ≤ h₀) (hh : 3 ≤ h) (hn : 0 < n) :
    shiftedLeading (h - 2) (h₀ - 1) h₀ n =
      Real.rpow (h - 1 : ℝ) (h₀ - (1 / 2 : ℝ)) /
        (Real.sqrt (2 * Real.pi) *
          Real.rpow (h - 2 : ℝ) (h₀ + (1 / 2 : ℝ))) *
      Real.rpow (n : ℝ) (-3 / 2 : ℝ) *
      (Real.rpow (h - 1 : ℝ) (h - 1 : ℝ) /
        Real.rpow (h - 2 : ℝ) (h - 2 : ℝ)) ^ n := by
  have hq : 0 < ((h - 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < h - 2 by omega)
  have hp : 0 < (((h - 2) + 1 : ℕ) : ℝ) := by positivity
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have h1 : (h - 1 : ℝ) = (((h - 2) + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ h)]; norm_num <;> ring
  have h2 : (h - 2 : ℝ) = ((h - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ h)]; norm_num
  have hs : (h₀ : ℝ) - 1 / 2 = ((h₀ - 1 : ℕ) : ℝ) + 1 / 2 := by
    rw [Nat.cast_sub hh₀]; norm_num <;> ring
  rw [h1, h2, hs, rpow_nat_add_half _ hp,
    rpow_nat_add_half _ hq, explicit_rpow_natCast, explicit_rpow_natCast]
  rw [show (-3 / 2 : ℝ) = -((1 : ℕ) + 1 / 2) by norm_num,
    rpow_neg_nat_add_half _ hnR]
  have hnPow : (n : ℝ) ^ h₀ = (n : ℝ) ^ (h₀ - 1) * n := by
    conv_lhs => rw [show h₀ = (h₀ - 1) + 1 by omega, pow_succ]
  unfold shiftedLeading growth
  rw [hnPow]
  simp only [pow_one]
  have hS : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hQ : Real.sqrt ((h - 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hN : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  field_simp [hS, hQ, hN, hnR.ne', hq.ne']

end
end PolytopeCounting.AffineStirling

namespace PolytopeCounting.GeneralAsymptotics

noncomputable section
open Filter HermiteAsymptotic AffineStirling
open scoped Topology

/-- The formerly missing TreeAffineStirlingInput is now a conclusion. -/
theorem treeAffineStirlingInput (h : ℕ) (hh : 3 ≤ h) :
    TreeAffineStirlingInput h := by
  have hb := factorial_ratio_tendsto (h - 2) 0 2 (by omega)
  unfold SequenceEquivalent at hb
  unfold TreeAffineStirlingInput SequenceEquivalent
  apply hb.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [tree_leading_rewrite h n hh hn]
  simp only [Nat.add_zero, show h - 2 + 1 = h - 1 by omega, Nat.mul_comm]

/-- The formerly missing FixedCoreAffineStirlingInput is now a conclusion. -/
theorem fixedCoreAffineStirlingInput (h₀ h : ℕ)
    (hh₀ : 1 ≤ h₀) (hh : 3 ≤ h) :
    FixedCoreAffineStirlingInput h₀ h := by
  have hb := factorial_ratio_tendsto (h - 2) (h₀ - 1) h₀ (by omega)
  unfold SequenceEquivalent at hb
  unfold FixedCoreAffineStirlingInput SequenceEquivalent
  apply hb.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [fixed_core_leading_rewrite h₀ h n hh₀ hh hn]
  have hi : (h - 2 + 1) * n + (h₀ - 1) = n * (h - 1) + h₀ - 1 := by
    rw [show h - 2 + 1 = h - 1 by omega, Nat.mul_comm (h - 1) n]
    omega
  rw [hi]

/-- Corollary 5.1 without an affine-Stirling hypothesis. -/
theorem treeUnlabelled_asymptotic_unconditional
    (h r tau : ℕ) (hh : 3 ≤ h) (hr : 0 < r) (htau : 0 < tau) :
    SequenceEquivalent (treeUnlabelledExact h r tau)
      (treeUnlabelledLeading h r tau) :=
  treeUnlabelled_asymptotic h r tau hh hr htau (treeAffineStirlingInput h hh)

/-- Corollary 5.2 without an affine-Stirling hypothesis. -/
theorem fixedCoreUnlabelled_asymptotic_unconditional
    (T₀ : ℝ) (h₀ h r tau : ℕ)
    (hT₀ : T₀ ≠ 0) (hh₀ : 1 ≤ h₀) (hh : 3 ≤ h)
    (hr : 0 < r) (htau : 0 < tau) :
    SequenceEquivalent (fixedCoreUnlabelledExact T₀ h₀ h r tau)
      (fixedCoreUnlabelledLeading T₀ h₀ h r tau) :=
  fixedCoreUnlabelled_asymptotic T₀ h₀ h r tau hT₀ hh₀ hh hr htau
    (fixedCoreAffineStirlingInput h₀ h hh₀ hh)

end
end PolytopeCounting.GeneralAsymptotics
