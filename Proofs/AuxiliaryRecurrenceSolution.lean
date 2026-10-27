module

public import Proofs.AuxiliarySeriesDifferential
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Solving the normalized tree recurrence

This file supplies the missing logical bridge between a quadratic cut--join
recurrence and the scaled Raney functional equation.  The proof is entirely
formal-power-series algebra.

For a sequence `a` with `a 0 = 0`, set

`A = 1 + Σ_{n≥1} a_n X^n`.

The normalized tree recurrence

`2(n-1)a_n = (q n + 2) Σ_{k=1}^{n-1} a_k a_{n-k}`

is first converted into

`(q+1) X A' - q X A A' = A²-A`.

Using the inverse of the unit series `A`, we then prove that

`(A-1)A^{-(q+1)}`

satisfies `X B' = B`; hence it is its linear coefficient times `X`.  This
gives the functional equation

`A = 1 + a_1 X A^(q+1)`.

The Lagrange--Bürmann/Raney theorem can therefore be applied to every
sequence satisfying the recurrence; existence of a solution is not assumed
separately.
-/

namespace PolytopeCounting
namespace ExplicitFormulas

open scoped BigOperators
open PowerSeries

noncomputable section

/-- A power series with zero constant coefficient and prescribed positive
coefficients. -/
def positiveSeries (a : ℕ → ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else a n)

@[simp]
theorem coeff_positiveSeries_zero (a : ℕ → ℚ) :
    PowerSeries.coeff 0 (positiveSeries a) = 0 := by
  simp [positiveSeries]

@[simp]
theorem coeff_positiveSeries_of_pos (a : ℕ → ℚ) {n : ℕ} (hn : 0 < n) :
    PowerSeries.coeff n (positiveSeries a) = a n := by
  simp [positiveSeries, hn.ne']

/-- The auxiliary series `A=1+S`. -/
def auxiliarySeries (a : ℕ → ℚ) : PowerSeries ℚ :=
  1 + positiveSeries a

@[simp]
theorem constantCoeff_auxiliarySeries (a : ℕ → ℚ) :
    PowerSeries.constantCoeff (auxiliarySeries a) = 1 := by
  have hp0 : PowerSeries.constantCoeff (positiveSeries a) = 0 :=
    (PowerSeries.coeff_zero_eq_constantCoeff_apply
      (positiveSeries a)).symm.trans (coeff_positiveSeries_zero a)
  simp [auxiliarySeries, hp0]

@[simp]
theorem coeff_auxiliarySeries_zero (a : ℕ → ℚ) :
    PowerSeries.coeff 0 (auxiliarySeries a) = 1 := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
    constantCoeff_auxiliarySeries a

@[simp]
theorem coeff_auxiliarySeries_of_pos (a : ℕ → ℚ) {n : ℕ} (hn : 0 < n) :
    PowerSeries.coeff n (auxiliarySeries a) = a n := by
  simp [auxiliarySeries, hn.ne', coeff_positiveSeries_of_pos a hn]

/-- The positive-part convolution occurring in the tree recurrence. -/
def properConvolution (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)

/-- The coefficient of the square of the positive series is exactly the
sum over proper nonempty splits. -/
theorem coeff_positiveSeries_sq
    (a : ℕ → ℚ) (n : ℕ) (hn : 2 ≤ n) :
    PowerSeries.coeff n ((positiveSeries a) ^ 2) =
      properConvolution a n := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold properConvolution
  symm
  have hinside :
      (∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)) =
        ∑ k ∈ Finset.Icc 1 (n - 1),
          PowerSeries.coeff k (positiveSeries a) *
            PowerSeries.coeff (n - k) (positiveSeries a) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [coeff_positiveSeries_of_pos a (by omega),
      coeff_positiveSeries_of_pos a (by omega)]
  rw [hinside]
  apply Finset.sum_subset
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  · intro k hkrange hknot
    rw [Finset.mem_range] at hkrange
    have hkCases : k = 0 ∨ k = n := by
      rw [Finset.mem_Icc] at hknot
      push_neg at hknot
      omega
    rcases hkCases with rfl | rfl
    · simp
    · simp [positiveSeries]

/-- The normalized recurrence used to solve all tree counts. -/
def SatisfiesAuxiliaryTreeRecurrence
    (q : ℕ) (a : ℕ → ℚ) : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (2 : ℚ) * ((n - 1 : ℕ) : ℚ) * a n =
      (((q * n + 2 : ℕ) : ℚ)) * properConvolution a n

/-- Multiplication by `X` shifts the coefficient of a derivative. -/
private theorem coeff_X_mul_derivative
    (F : PowerSeries ℚ) (n : ℕ) (hn : 0 < n) :
    PowerSeries.coeff n
        (PowerSeries.X * PowerSeries.derivative (R := ℚ) F) =
      (n : ℚ) * PowerSeries.coeff n F := by
  have hsplit : n = (n - 1) + 1 := by omega
  calc
    PowerSeries.coeff n
        (PowerSeries.X * PowerSeries.derivative (R := ℚ) F) =
      PowerSeries.coeff ((n - 1) + 1)
        (PowerSeries.X ^ 1 * PowerSeries.derivative (R := ℚ) F) := by
          simpa only [pow_one] using congrArg
            (fun k : ℕ => PowerSeries.coeff k
              (PowerSeries.X * PowerSeries.derivative (R := ℚ) F)) hsplit
    _ = PowerSeries.coeff (n - 1) (PowerSeries.derivative (R := ℚ) F) := by
      rw [PowerSeries.coeff_X_pow_mul]
    _ = PowerSeries.coeff ((n - 1) + 1) F *
        (((n - 1 : ℕ) : ℚ) + 1) := by
      rw [PowerSeries.coeff_derivative]
    _ = (n : ℚ) * PowerSeries.coeff n F := by
      have hidx : n - 1 + 1 = n := hsplit.symm
      have hcast : (((n - 1 : ℕ) : ℚ) + 1) = (n : ℚ) := by
        exact_mod_cast hidx
      rw [hidx, hcast]
      ring

/-- Since `(A²)'=2AA'`, the coefficient of `XAA'` is one half of
`n [X^n]A²`; the division-free form is used here. -/
private theorem two_mul_coeff_X_mul_self_mul_derivative
    (A : PowerSeries ℚ) (n : ℕ) (hn : 0 < n) :
    (2 : ℚ) * PowerSeries.coeff n
      (PowerSeries.X * A * PowerSeries.derivative (R := ℚ) A) =
      (n : ℚ) * PowerSeries.coeff n (A ^ 2) := by
  have hpow := (PowerSeries.derivative (R := ℚ)).leibniz_pow A 2
  have htwoC : (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) := by
    change PowerSeries.C (2 : ℚ) = PowerSeries.C (2 : ℚ)
    rfl
  have hpow' :
      PowerSeries.derivative (R := ℚ) (A ^ 2) =
        PowerSeries.C (2 : ℚ) *
          (A * PowerSeries.derivative (R := ℚ) A) := by
    rw [(PowerSeries.derivative (R := ℚ)).leibniz_pow]
    simp only [Nat.reduceSubDiff, pow_one, two_nsmul, smul_eq_mul]
    rw [← htwoC]
    ring
  have hc := congrArg (PowerSeries.coeff (n - 1)) hpow'
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul] at hc
  have hsplit : n = (n - 1) + 1 := by omega
  have hshift :
      PowerSeries.coeff n
          (PowerSeries.X * A * PowerSeries.derivative (R := ℚ) A) =
        PowerSeries.coeff (n - 1)
          (A * PowerSeries.derivative (R := ℚ) A) := by
    calc
      PowerSeries.coeff n
          (PowerSeries.X * A * PowerSeries.derivative (R := ℚ) A) =
        PowerSeries.coeff n
          (PowerSeries.X * (A * PowerSeries.derivative (R := ℚ) A)) := by
            congr 1
            ring
      _ =
        PowerSeries.coeff ((n - 1) + 1)
          (PowerSeries.X ^ 1 *
            (A * PowerSeries.derivative (R := ℚ) A)) := by
          simpa only [pow_one] using congrArg
            (fun k : ℕ => PowerSeries.coeff k
              (PowerSeries.X *
                (A * PowerSeries.derivative (R := ℚ) A))) hsplit
      _ = PowerSeries.coeff (n - 1)
          (A * PowerSeries.derivative (R := ℚ) A) := by
        rw [PowerSeries.coeff_X_pow_mul]
  rw [hshift]
  have hcast : (((n - 1 : ℕ) : ℚ) + 1) = (n : ℚ) := by
    exact_mod_cast hsplit.symm
  rw [hcast, hsplit.symm] at hc
  calc
    (2 : ℚ) * PowerSeries.coeff (n - 1)
        (A * PowerSeries.derivative (R := ℚ) A) =
      PowerSeries.coeff n (A ^ 2) * (n : ℚ) := hc.symm
    _ = (n : ℚ) * PowerSeries.coeff n (A ^ 2) := by ring

/-- For positive degree, `A²` is the proper convolution plus the two
endpoint terms. -/
private theorem coeff_auxiliary_sq
    (a : ℕ → ℚ) (n : ℕ) (hn : 2 ≤ n) :
    PowerSeries.coeff n ((auxiliarySeries a) ^ 2) =
      properConvolution a n + 2 * a n := by
  have hring :
      (auxiliarySeries a) ^ 2 =
        (positiveSeries a) ^ 2 +
          PowerSeries.C (2 : ℚ) * positiveSeries a + 1 := by
    have htwoC : (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) := by
      change PowerSeries.C (2 : ℚ) = PowerSeries.C (2 : ℚ)
      rfl
    unfold auxiliarySeries
    rw [← htwoC]
    ring
  have hn0 : n ≠ 0 := by omega
  rw [hring, map_add, map_add, PowerSeries.coeff_C_mul,
    coeff_positiveSeries_sq a n hn,
    coeff_positiveSeries_of_pos a (by omega), PowerSeries.coeff_one]
  simp [hn0]

/-- The quadratic recurrence is equivalent to the formal differential
identity from Appendix B. -/
theorem differential_of_auxiliary_recurrence
    (q : ℕ) (a : ℕ → ℚ)
    (hrec : SatisfiesAuxiliaryTreeRecurrence q a) :
    PowerSeries.C ((q + 1 : ℕ) : ℚ) * PowerSeries.X *
          PowerSeries.derivative (R := ℚ) (auxiliarySeries a) -
        PowerSeries.C (q : ℚ) * PowerSeries.X * auxiliarySeries a *
          PowerSeries.derivative (R := ℚ) (auxiliarySeries a) =
      (auxiliarySeries a) ^ 2 - auxiliarySeries a := by
  apply PowerSeries.ext
  intro n
  rw [show PowerSeries.C ((q + 1 : ℕ) : ℚ) * PowerSeries.X *
        PowerSeries.derivative (R := ℚ) (auxiliarySeries a) =
      PowerSeries.C ((q + 1 : ℕ) : ℚ) *
        (PowerSeries.X *
          PowerSeries.derivative (R := ℚ) (auxiliarySeries a)) by ring]
  rw [show PowerSeries.C (q : ℚ) * PowerSeries.X * auxiliarySeries a *
        PowerSeries.derivative (R := ℚ) (auxiliarySeries a) =
      PowerSeries.C (q : ℚ) *
        (PowerSeries.X * auxiliarySeries a *
          PowerSeries.derivative (R := ℚ) (auxiliarySeries a)) by ring]
  rw [map_sub, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul]
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hn1 : n = 1
  · subst n
    have hxd := coeff_X_mul_derivative (auxiliarySeries a) 1 (by norm_num)
    have hxaa := two_mul_coeff_X_mul_self_mul_derivative
      (auxiliarySeries a) 1 (by norm_num)
    have hsq1 :
        PowerSeries.coeff 1 ((auxiliarySeries a) ^ 2) = 2 * a 1 := by
      rw [pow_two, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      norm_num [Finset.sum_range_succ,
        coeff_auxiliarySeries_zero,
        coeff_auxiliarySeries_of_pos]
      ring
    rw [hsq1] at hxaa
    norm_num at hxaa
    have hxaa' :
        PowerSeries.coeff 1
            (PowerSeries.X * auxiliarySeries a *
              PowerSeries.derivative (R := ℚ) (auxiliarySeries a)) = a 1 := by
      linarith [hxaa]
    rw [hxd, hxaa', hsq1,
      coeff_auxiliarySeries_of_pos a (by norm_num)]
    push_cast
    ring
  · have hn : 2 ≤ n := by omega
    have hxd := coeff_X_mul_derivative (auxiliarySeries a) n (by omega)
    have hxaa := two_mul_coeff_X_mul_self_mul_derivative
      (auxiliarySeries a) n (by omega)
    have hsq := coeff_auxiliary_sq a n hn
    have hr := hrec n hn
    rw [hsq] at hxaa
    rw [hxd]
    have ha : PowerSeries.coeff n (auxiliarySeries a) = a n :=
      coeff_auxiliarySeries_of_pos a (by omega)
    rw [ha, hsq]
    have hncast : (((n - 1 : ℕ) : ℚ)) = (n : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hncast] at hr
    push_cast at hr ⊢
    linear_combination (-(q : ℚ) / 2) * hxaa + (1 / 2) * hr

/-- The inverse of the auxiliary series is a genuine multiplicative
inverse because its constant term is one. -/
private theorem auxiliary_inv_mul (a : ℕ → ℚ) :
    (auxiliarySeries a)⁻¹ * auxiliarySeries a = 1 := by
  apply PowerSeries.inv_mul_cancel
  simp

/-- A series satisfying `X B'=B` and having zero constant term is a
multiple of `X`; the multiple is its linear coefficient. -/
private theorem eq_C_mul_X_of_X_mul_derivative_eq
    (B : PowerSeries ℚ)
    (hB0 : PowerSeries.constantCoeff B = 0)
    (hODE : PowerSeries.X * PowerSeries.derivative (R := ℚ) B = B) :
    B = PowerSeries.C (PowerSeries.coeff 1 B) * PowerSeries.X := by
  apply PowerSeries.ext
  intro n
  rcases n with _ | n
  · simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply, hB0]
  rcases n with _ | n
  · simp
  · have hcoeff := congrArg (PowerSeries.coeff (n + 2)) hODE
    have hxd := coeff_X_mul_derivative B (n + 2) (by omega)
    rw [hxd] at hcoeff
    have hz : PowerSeries.coeff (n + 2) B = 0 := by
      have hnonzero : (((n + 2 : ℕ) : ℚ) - 1) ≠ 0 := by
        have hfactor : (((n + 2 : ℕ) : ℚ) - 1) =
            ((n + 1 : ℕ) : ℚ) := by
          push_cast
          ring
        rw [hfactor]
        exact_mod_cast Nat.succ_ne_zero n
      apply mul_left_cancel₀ hnonzero
      linear_combination hcoeff
    rw [hz]
    simp [PowerSeries.coeff_C_mul_X_pow]

/-- The normalized recurrence determines the scaled Raney functional
equation. -/
theorem functional_equation_of_auxiliary_recurrence
    (q : ℕ) (a : ℕ → ℚ)
    (hrec : SatisfiesAuxiliaryTreeRecurrence q a) :
    auxiliarySeries a =
      1 + PowerSeries.C (a 1) * PowerSeries.X *
        (auxiliarySeries a) ^ (q + 1) := by
  let A : PowerSeries ℚ := auxiliarySeries a
  let B : PowerSeries ℚ :=
    (A - 1) * (A⁻¹) ^ (q + 1)
  have hdiff := differential_of_auxiliary_recurrence q a hrec
  have hA0 : PowerSeries.constantCoeff A = 1 := by
    dsimp [A]
    simp
  have hAne : PowerSeries.constantCoeff A ≠ 0 := by
    rw [hA0]
    norm_num
  have hcancel : A⁻¹ * A = 1 :=
    PowerSeries.inv_mul_cancel A hAne
  have hAinv2 : A * (A⁻¹) ^ 2 = A⁻¹ := by
    rw [pow_two]
    calc
      A * (A⁻¹ * A⁻¹) = (A⁻¹ * A) * A⁻¹ := by ring
      _ = A⁻¹ := by rw [hcancel, one_mul]
  have hdinv :
      PowerSeries.derivative (R := ℚ) (A⁻¹) =
        -(A⁻¹) ^ 2 * PowerSeries.derivative (R := ℚ) A := by
    simpa using PowerSeries.derivative_inv' A
  have hDB :
      PowerSeries.derivative (R := ℚ) B =
        (A⁻¹) ^ (q + 2) *
          (PowerSeries.C ((q + 1 : ℕ) : ℚ) *
              PowerSeries.derivative (R := ℚ) A -
            PowerSeries.C (q : ℚ) * A *
              PowerSeries.derivative (R := ℚ) A) := by
    dsimp [B]
    rw [Derivation.leibniz, map_sub,
      (PowerSeries.derivative (R := ℚ)).map_one_eq_zero,
      (PowerSeries.derivative (R := ℚ)).leibniz_pow, hdinv]
    simp only [smul_eq_mul, sub_zero, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, map_add, map_natCast, map_one]
    have hq1 : (A⁻¹) ^ (q + 1) = (A⁻¹) ^ q * A⁻¹ := by
      rw [pow_succ]
    have hq2 : (A⁻¹) ^ (q + 2) = (A⁻¹) ^ q * (A⁻¹) ^ 2 := by
      exact pow_add (A⁻¹) q 2
    rw [hq1, hq2]
    linear_combination
      (-((A⁻¹) ^ q * PowerSeries.derivative (R := ℚ) A)) * hAinv2
  have hODE : PowerSeries.X * PowerSeries.derivative (R := ℚ) B = B := by
    rw [hDB]
    have hdiffA :
        PowerSeries.X *
            (PowerSeries.C ((q + 1 : ℕ) : ℚ) *
                PowerSeries.derivative (R := ℚ) A -
              PowerSeries.C (q : ℚ) * A *
                PowerSeries.derivative (R := ℚ) A) =
          A ^ 2 - A := by
      dsimp [A] at hdiff ⊢
      linear_combination hdiff
    rw [show PowerSeries.X *
          ((A⁻¹) ^ (q + 2) *
            (PowerSeries.C ((q + 1 : ℕ) : ℚ) *
                PowerSeries.derivative (R := ℚ) A -
              PowerSeries.C (q : ℚ) * A *
                PowerSeries.derivative (R := ℚ) A)) =
        (A⁻¹) ^ (q + 2) *
          (PowerSeries.X *
            (PowerSeries.C ((q + 1 : ℕ) : ℚ) *
                PowerSeries.derivative (R := ℚ) A -
              PowerSeries.C (q : ℚ) * A *
                PowerSeries.derivative (R := ℚ) A)) by ring]
    rw [hdiffA]
    dsimp [B]
    rw [show A ^ 2 - A = A * (A - 1) by ring]
    calc
      (A⁻¹) ^ (q + 2) * (A * (A - 1)) =
          ((A⁻¹) ^ (q + 1) * (A⁻¹ * A)) * (A - 1) := by
        rw [show q + 2 = (q + 1) + 1 by omega, pow_succ]
        ring
      _ = (A⁻¹) ^ (q + 1) * (A - 1) := by rw [hcancel, mul_one]
      _ = (A - 1) * (A⁻¹) ^ (q + 1) := by ring
  have hB0 : PowerSeries.constantCoeff B = 0 := by
    dsimp [B]
    simp [hA0]
  have hBlinear := eq_C_mul_X_of_X_mul_derivative_eq B hB0 hODE
  have hB1 : PowerSeries.coeff 1 B = a 1 := by
    dsimp [B]
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ, A, auxiliarySeries,
      positiveSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hA0]
  rw [hB1] at hBlinear
  have hpowcancel : (A⁻¹) ^ (q + 1) * A ^ (q + 1) = 1 := by
    rw [← mul_pow, PowerSeries.inv_mul_cancel A hAne, one_pow]
  have hmul := congrArg (fun Z : PowerSeries ℚ => Z * A ^ (q + 1)) hBlinear
  dsimp [B] at hmul
  rw [mul_assoc, hpowcancel, mul_one] at hmul
  dsimp [A] at hmul ⊢
  linear_combination hmul

/-- Complete coefficient solution of the normalized recurrence. -/
theorem auxiliary_recurrence_explicit
    (q : ℕ) (a : ℕ → ℚ)
    (hrec : SatisfiesAuxiliaryTreeRecurrence q a)
    (ha1 : a 1 ≠ 0) (n : ℕ) (hn : 0 < n) :
    a n = (a 1) ^ n *
      PolytopeCounting.LagrangeBurmann.RaneyApplication.raneyNumber
        (q + 1) 1 n := by
  let A := auxiliarySeries a
  have hA := functional_equation_of_auxiliary_recurrence q a hrec
  have hc :=
    PolytopeCounting.LagrangeBurmann.ScaledRaneyApplication.coeff_scaled_solution_pow_eq_raney
        A (a 1) (q + 1) 1 n ha1 hA (by omega)
  have hpow : A ^ 1 = A := by simp
  rw [hpow] at hc
  simpa [A, coeff_auxiliarySeries_of_pos a hn] using hc


end
end ExplicitFormulas
end PolytopeCounting
