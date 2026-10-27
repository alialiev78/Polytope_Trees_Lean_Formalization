module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Polynomial Lagrange--Bürmann inversion

This file proves the coefficient identity needed in the facet-pairing
application.  The proof is the coefficient induction of Surya--Warnke,
so it does not require a pre-existing compositional inverse API.

For a characteristic-zero field `K`, a power series `A`, and polynomials
`Φ,H`, if

  `A = X * H( A )` with `H` replaced by `Φ`, i.e.
  `A = X * subst A (Φ : K⟦X⟧)`,

then for every positive `n`,

  `n * [X^n] H(A) = [X^(n-1)] H'(X) * Φ(X)^n`.

The polynomial version is enough for the Raney specialization
`Φ = (1 + X)^p`, `H = (1 + X)^h₀`.
-/

namespace PolytopeCounting
namespace LagrangeBurmann

open PowerSeries
open scoped Polynomial

noncomputable section

private theorem constantCoeff_subst_eq
    {K : Type*} [Field K]
    {A F : PowerSeries K}
    (hA0 : PowerSeries.constantCoeff A = 0)
    (hsubst : PowerSeries.HasSubst A) :
    PowerSeries.constantCoeff (F.subst A) =
      PowerSeries.constantCoeff F := by
  change MvPowerSeries.constantCoeff (F.subst A) =
    MvPowerSeries.constantCoeff F
  have hA0' : MvPowerSeries.constantCoeff A = 0 := hA0
  rw [PowerSeries.constantCoeff_subst hsubst F]
  rw [finsum_eq_single _ 0]
  · simp only [pow_zero, map_one, smul_eq_mul, mul_one,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rfl
  · intro d hd
    simp [map_pow, hA0', hd]

private theorem derivative_coe_pow
    {K : Type*} [Field K]
    (Φ : K[X]) (n : ℕ) :
    PowerSeries.derivative (R := K) (((Φ ^ n : K[X]) : PowerSeries K)) =
      PowerSeries.C (n : K) *
        ((Φ : PowerSeries K) ^ (n - 1)) *
          PowerSeries.derivative (R := K) (Φ : PowerSeries K) := by
  calc
    PowerSeries.derivative (R := K) (((Φ ^ n : K[X]) : PowerSeries K)) =
        ((Polynomial.derivative (Φ ^ n) : K[X]) : PowerSeries K) :=
      PowerSeries.derivative_coe (Φ ^ n)
    _ = ((Polynomial.C (n : K) * Φ ^ (n - 1) *
          Polynomial.derivative Φ : K[X]) : PowerSeries K) := by
      rw [Polynomial.derivative_pow]
    _ = PowerSeries.C (n : K) *
          ((Φ : PowerSeries K) ^ (n - 1)) *
            PowerSeries.derivative (R := K) (Φ : PowerSeries K) := by
      rw [PowerSeries.derivative_coe]
      simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C]

private theorem subst_monomial
    {K : Type*} [Field K]
    {A : PowerSeries K}
    (hsubst : PowerSeries.HasSubst A)
    (k : ℕ) (c : K) :
    (((Polynomial.monomial k c : K[X]) : PowerSeries K).subst A) =
      PowerSeries.C c * A ^ k := by
  calc
    (((Polynomial.monomial k c : K[X]) : PowerSeries K).subst A) =
        (((Polynomial.C c * Polynomial.X ^ k : K[X]) : PowerSeries K).subst A) := by
      rw [Polynomial.C_mul_X_pow_eq_monomial]
    _ = ((PowerSeries.C c * PowerSeries.X ^ k : PowerSeries K).subst A) := by
      simp
    _ = PowerSeries.C c * A ^ k := by
      rw [PowerSeries.subst_mul hsubst, PowerSeries.subst_pow hsubst,
        PowerSeries.subst_X hsubst]
      rw [← Polynomial.coe_C, PowerSeries.subst_coe hsubst]
      simp

private theorem derivative_coe_monomial
    {K : Type*} [Field K]
    (k : ℕ) (c : K) :
    PowerSeries.derivative (R := K)
        (((Polynomial.monomial k c : K[X]) : PowerSeries K)) =
      PowerSeries.C (c * (k : K)) * PowerSeries.X ^ (k - 1) := by
  calc
    PowerSeries.derivative (R := K)
        (((Polynomial.monomial k c : K[X]) : PowerSeries K)) =
      ((Polynomial.derivative (Polynomial.monomial k c) : K[X]) :
        PowerSeries K) := PowerSeries.derivative_coe _
    _ = ((Polynomial.monomial (k - 1) (c * (k : K)) : K[X]) :
        PowerSeries K) := by rw [Polynomial.derivative_monomial]
    _ = PowerSeries.C (c * (k : K)) * PowerSeries.X ^ (k - 1) := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C,
        Polynomial.coe_X]

/-- Polynomial Lagrange--Bürmann coefficient identity.

The statement is division-free.  Over a characteristic-zero field it is
identical to

`[X^n] H(A) = (1/n) [X^(n-1)] H'(X) Φ(X)^n`.
-/
theorem lagrange_burmann_polynomial
    {K : Type*} [Field K] [CharZero K]
    (A : PowerSeries K) (Φ H : K[X])
    (hA : A = PowerSeries.X * ((Φ : PowerSeries K).subst A))
    (n : ℕ) (hn : 0 < n) :
    (n : K) * PowerSeries.coeff n (((H : PowerSeries K).subst A)) =
      PowerSeries.coeff (n - 1)
        (PowerSeries.derivative (R := K) (H : PowerSeries K) *
          (Φ : PowerSeries K) ^ n) := by
  have hA0 : PowerSeries.constantCoeff A = 0 := by
    rw [hA]
    simp
  have hsubst : PowerSeries.HasSubst A :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hA0

  have main : ∀ N : ℕ, 0 < N → ∀ P : K[X],
      (N : K) * PowerSeries.coeff N (((P : PowerSeries K).subst A)) =
        PowerSeries.coeff (N - 1)
          (PowerSeries.derivative (R := K) (P : PowerSeries K) *
            (Φ : PowerSeries K) ^ N) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro hN P

      have hpower : ∀ k : ℕ, k ≤ N →
          (N : K) * PowerSeries.coeff N (A ^ k) =
            (k : K) * PowerSeries.coeff (N - k)
              ((Φ : PowerSeries K) ^ N) := by
        intro k hk
        by_cases hk0 : k = 0
        · subst k
          simp [hN.ne']
        by_cases hkN : k = N
        · subst k
          have hshift :
              PowerSeries.coeff N (A ^ N) =
                PowerSeries.coeff 0
                  ((((Φ ^ N : K[X]) : PowerSeries K).subst A)) := by
            calc
              PowerSeries.coeff N (A ^ N) =
                  PowerSeries.coeff N
                    (PowerSeries.X ^ N *
                      (((Φ : PowerSeries K).subst A) ^ N)) := by
                nth_rewrite 1 [hA]
                rw [mul_pow]
              _ = PowerSeries.coeff 0
                    (((Φ : PowerSeries K).subst A) ^ N) := by
                simpa using
                  (PowerSeries.coeff_X_pow_mul
                    (((Φ : PowerSeries K).subst A) ^ N) N 0)
              _ = PowerSeries.coeff 0
                    ((((Φ ^ N : K[X]) : PowerSeries K).subst A)) := by
                rw [show (((Φ ^ N : K[X]) : PowerSeries K)) =
                    (Φ : PowerSeries K) ^ N by simp]
                rw [PowerSeries.subst_pow hsubst]
          have hconst :
              PowerSeries.coeff 0
                  ((((Φ ^ N : K[X]) : PowerSeries K).subst A)) =
                PowerSeries.coeff 0 ((Φ : PowerSeries K) ^ N) := by
            simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
              (constantCoeff_subst_eq
                (A := A)
                (F := (((Φ ^ N : K[X]) : PowerSeries K)))
                hA0 hsubst)
          rw [hshift, hconst]
          simp
        · have hklt : k < N := by omega
          let m : ℕ := N - k
          have hmpos : 0 < m := by
            dsimp [m]
            omega
          have hmlt : m < N := by
            dsimp [m]
            omega
          have hNm : m + k = N := by
            dsimp [m]
            omega
          have hkm : k - 1 + m = N - 1 := by
            dsimp [m]
            omega

          have hshift :
              PowerSeries.coeff N (A ^ k) =
                PowerSeries.coeff m
                  ((((Φ ^ k : K[X]) : PowerSeries K).subst A)) := by
            calc
              PowerSeries.coeff N (A ^ k) =
                  PowerSeries.coeff N
                    (PowerSeries.X ^ k *
                      (((Φ : PowerSeries K).subst A) ^ k)) := by
                nth_rewrite 1 [hA]
                rw [mul_pow]
              _ = PowerSeries.coeff (N - k)
                    (((Φ : PowerSeries K).subst A) ^ k) := by
                rw [PowerSeries.coeff_X_pow_mul']
                simp [hk]
              _ = PowerSeries.coeff m
                    ((((Φ ^ k : K[X]) : PowerSeries K).subst A)) := by
                dsimp [m]
                rw [show (((Φ ^ k : K[X]) : PowerSeries K)) =
                    (Φ : PowerSeries K) ^ k by simp]
                rw [PowerSeries.subst_pow hsubst]

          have hIH := ih m hmlt hmpos (Φ ^ k)
          have hderivK := derivative_coe_pow (K := K) Φ k
          have hprodK :
              PowerSeries.derivative (R := K)
                    (((Φ ^ k : K[X]) : PowerSeries K)) *
                  (Φ : PowerSeries K) ^ m =
                PowerSeries.C (k : K) *
                  (PowerSeries.derivative (R := K) (Φ : PowerSeries K) *
                    (Φ : PowerSeries K) ^ (N - 1)) := by
            rw [hderivK]
            calc
              (PowerSeries.C (k : K) *
                    (Φ : PowerSeries K) ^ (k - 1) *
                    PowerSeries.derivative (R := K) (Φ : PowerSeries K)) *
                  (Φ : PowerSeries K) ^ m =
                PowerSeries.C (k : K) *
                  (PowerSeries.derivative (R := K) (Φ : PowerSeries K) *
                    ((Φ : PowerSeries K) ^ (k - 1) *
                      (Φ : PowerSeries K) ^ m)) := by ring
              _ = PowerSeries.C (k : K) *
                  (PowerSeries.derivative (R := K) (Φ : PowerSeries K) *
                    (Φ : PowerSeries K) ^ ((k - 1) + m)) := by
                rw [pow_add]
              _ = PowerSeries.C (k : K) *
                  (PowerSeries.derivative (R := K) (Φ : PowerSeries K) *
                    (Φ : PowerSeries K) ^ (N - 1)) := by
                rw [hkm]

          have hIH' :
              (m : K) * PowerSeries.coeff m
                  ((((Φ ^ k : K[X]) : PowerSeries K).subst A)) =
                (k : K) * PowerSeries.coeff (m - 1)
                  (PowerSeries.derivative (R := K) (Φ : PowerSeries K) *
                    (Φ : PowerSeries K) ^ (N - 1)) := by
            calc
              (m : K) * PowerSeries.coeff m
                  ((((Φ ^ k : K[X]) : PowerSeries K).subst A)) =
                PowerSeries.coeff (m - 1)
                  (PowerSeries.derivative (R := K)
                      (((Φ ^ k : K[X]) : PowerSeries K)) *
                    (Φ : PowerSeries K) ^ m) := hIH
              _ = PowerSeries.coeff (m - 1)
                  (PowerSeries.C (k : K) *
                    (PowerSeries.derivative (R := K) (Φ : PowerSeries K) *
                      (Φ : PowerSeries K) ^ (N - 1))) := by rw [hprodK]
              _ = (k : K) * PowerSeries.coeff (m - 1)
                  (PowerSeries.derivative (R := K) (Φ : PowerSeries K) *
                    (Φ : PowerSeries K) ^ (N - 1)) := by
                      rw [PowerSeries.coeff_C_mul]

          have hderivN := derivative_coe_pow (K := K) Φ N
          have hmstep : m - 1 + 1 = m := by omega
          have hmstepK : ((m - 1 : ℕ) : K) + 1 = (m : K) := by
            exact_mod_cast hmstep
          have hcoeffDerivative :=
            PowerSeries.coeff_derivative
              ((((Φ ^ N : K[X]) : PowerSeries K))) (m - 1)
          have hND :
              (N : K) * PowerSeries.coeff (m - 1)
                  (PowerSeries.derivative (R := K) (Φ : PowerSeries K) *
                    (Φ : PowerSeries K) ^ (N - 1)) =
                (m : K) * PowerSeries.coeff m
                  ((Φ : PowerSeries K) ^ N) := by
            rw [hderivN, mul_assoc] at hcoeffDerivative
            rw [PowerSeries.coeff_C_mul] at hcoeffDerivative
            rw [hmstep] at hcoeffDerivative
            simpa [hmstepK, mul_comm, mul_left_comm, mul_assoc] using
              hcoeffDerivative

          have hmK : (m : K) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hmpos)
          apply (mul_left_cancel₀ hmK)
          calc
            (m : K) *
                ((N : K) * PowerSeries.coeff N (A ^ k)) =
              (N : K) *
                ((m : K) * PowerSeries.coeff m
                  ((((Φ ^ k : K[X]) : PowerSeries K).subst A))) := by
                rw [hshift]
                ring
            _ = (N : K) *
                ((k : K) * PowerSeries.coeff (m - 1)
                  (PowerSeries.derivative (R := K) (Φ : PowerSeries K) *
                    (Φ : PowerSeries K) ^ (N - 1))) := by rw [hIH']
            _ = (k : K) *
                ((N : K) * PowerSeries.coeff (m - 1)
                  (PowerSeries.derivative (R := K) (Φ : PowerSeries K) *
                    (Φ : PowerSeries K) ^ (N - 1))) := by ring
            _ = (k : K) *
                ((m : K) * PowerSeries.coeff m
                  ((Φ : PowerSeries K) ^ N)) := by rw [hND]
            _ = (m : K) *
                ((k : K) * PowerSeries.coeff (N - k)
                  ((Φ : PowerSeries K) ^ N)) := by
                dsimp [m]
                ring

      refine Polynomial.induction_on' P ?_ ?_
      · intro P Q hP hQ
        rw [show (((P + Q : K[X]) : PowerSeries K)) =
            (P : PowerSeries K) + (Q : PowerSeries K) by simp]
        rw [PowerSeries.subst_add hsubst]
        rw [(PowerSeries.derivative (R := K)).map_add, add_mul]
        simp only [map_add]
        linear_combination hP + hQ
      · intro k c
        have hsubstMono := subst_monomial (A := A) hsubst k c
        have hderivMono := derivative_coe_monomial (K := K) k c
        by_cases hk0 : k = 0
        · subst k
          rw [hsubstMono, hderivMono]
          simp [hN.ne']
          rw [PowerSeries.coeff_C]
          simp [hN.ne']
        by_cases hk : k ≤ N
        · have hkm1 : k - 1 ≤ N - 1 := by omega
          have hdiff : (N - 1) - (k - 1) = N - k := by omega
          rw [hsubstMono, PowerSeries.coeff_C_mul]
          rw [hderivMono]
          have hright :
              PowerSeries.coeff (N - 1)
                  ((PowerSeries.C (c * (k : K)) *
                      PowerSeries.X ^ (k - 1)) *
                    (Φ : PowerSeries K) ^ N) =
                (c * (k : K)) * PowerSeries.coeff (N - k)
                  ((Φ : PowerSeries K) ^ N) := by
            calc
              PowerSeries.coeff (N - 1)
                  ((PowerSeries.C (c * (k : K)) *
                      PowerSeries.X ^ (k - 1)) *
                    (Φ : PowerSeries K) ^ N) =
                PowerSeries.coeff (N - 1)
                  (PowerSeries.C (c * (k : K)) *
                    (PowerSeries.X ^ (k - 1) *
                      (Φ : PowerSeries K) ^ N)) := by
                    congr 1
                    ring
              _ = (c * (k : K)) *
                  PowerSeries.coeff (N - 1)
                    (PowerSeries.X ^ (k - 1) *
                      (Φ : PowerSeries K) ^ N) := by
                        rw [PowerSeries.coeff_C_mul]
              _ = (c * (k : K)) *
                  PowerSeries.coeff (N - k)
                    ((Φ : PowerSeries K) ^ N) := by
                rw [PowerSeries.coeff_X_pow_mul']
                simp [hkm1, hdiff]
          rw [hright]
          calc
            (N : K) * (c * PowerSeries.coeff N (A ^ k)) =
                c * ((N : K) * PowerSeries.coeff N (A ^ k)) := by ring
            _ = c * ((k : K) * PowerSeries.coeff (N - k)
                ((Φ : PowerSeries K) ^ N)) := by rw [hpower k hk]
            _ = (c * (k : K)) * PowerSeries.coeff (N - k)
                ((Φ : PowerSeries K) ^ N) := by ring
        · have hkgt : N < k := Nat.lt_of_not_ge hk
          have hAk : PowerSeries.coeff N (A ^ k) = 0 := by
            rw [hA, mul_pow, PowerSeries.coeff_X_pow_mul']
            simp [hk]
          have hkm1 : ¬ k - 1 ≤ N - 1 := by omega
          rw [hsubstMono, PowerSeries.coeff_C_mul, hAk]
          rw [hderivMono]
          have hzero :
              PowerSeries.coeff (N - 1)
                  ((PowerSeries.C (c * (k : K)) *
                      PowerSeries.X ^ (k - 1)) *
                    (Φ : PowerSeries K) ^ N) = 0 := by
            calc
              PowerSeries.coeff (N - 1)
                  ((PowerSeries.C (c * (k : K)) *
                      PowerSeries.X ^ (k - 1)) *
                    (Φ : PowerSeries K) ^ N) =
                (c * (k : K)) *
                  PowerSeries.coeff (N - 1)
                    (PowerSeries.X ^ (k - 1) *
                      (Φ : PowerSeries K) ^ N) := by
                        rw [mul_assoc, PowerSeries.coeff_C_mul]
              _ = 0 := by
                rw [PowerSeries.coeff_X_pow_mul']
                simp [hkm1]
          rw [hzero]
          simp

  exact main n hn H

/-- The usual divided form over a characteristic-zero field. -/
theorem coeff_subst_eq_div
    {K : Type*} [Field K] [CharZero K]
    (A : PowerSeries K) (Φ H : K[X])
    (hA : A = PowerSeries.X * ((Φ : PowerSeries K).subst A))
    (n : ℕ) (hn : 0 < n) :
    PowerSeries.coeff n (((H : PowerSeries K).subst A)) =
      (n : K)⁻¹ *
        PowerSeries.coeff (n - 1)
          (PowerSeries.derivative (R := K) (H : PowerSeries K) *
            (Φ : PowerSeries K) ^ n) := by
  have hnK : (n : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have h := lagrange_burmann_polynomial A Φ H hA n hn
  apply (mul_left_cancel₀ hnK)
  calc
    (n : K) * PowerSeries.coeff n (((H : PowerSeries K).subst A)) =
      PowerSeries.coeff (n - 1)
        (PowerSeries.derivative (R := K) (H : PowerSeries K) *
          (Φ : PowerSeries K) ^ n) := h
    _ = (n : K) * ((n : K)⁻¹ *
        PowerSeries.coeff (n - 1)
          (PowerSeries.derivative (R := K) (H : PowerSeries K) *
            (Φ : PowerSeries K) ^ n)) := by
      field_simp [hnK]


end
end LagrangeBurmann
end PolytopeCounting
