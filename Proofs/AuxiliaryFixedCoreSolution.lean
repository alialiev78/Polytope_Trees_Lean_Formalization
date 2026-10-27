module

public import Proofs.ManuscriptTreeExplicit
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Solving the normalized fixed-core recurrence

Let `A=1+Σ_{n≥1}a_n X^n` be the tree series.  The normalized fixed-core
coefficients satisfy

`n u_n = Σ_{k=0}^{n-1} (q k+h₀) u_k a_{n-k}`.

This file proves that the recurrence has a unique solution for a prescribed
constant coefficient and that the solution is

`u_n = u_0 [X^n] A^h₀`.

The scaled Raney theorem then gives the explicit coefficient formula.  This
is the formal-power-series version of equation (69) and Theorem 5.2.
-/

namespace PolytopeCounting
namespace ExplicitFormulas

open scoped BigOperators
open PowerSeries

noncomputable section

/-- The normalized fixed-core recurrence from Appendix B. -/
def SatisfiesAuxiliaryFixedRecurrence
    (q h₀ : ℕ) (a u : ℕ → ℚ) : Prop :=
  ∀ n : ℕ, 0 < n →
    (n : ℚ) * u n =
      ∑ k ∈ Finset.range n,
        (((q * k + h₀ : ℕ) : ℚ)) * u k * a (n - k)

private theorem coeff_X_mul_derivative_all
    (F : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.X * PowerSeries.derivative (R := ℚ) F) =
      (n : ℚ) * PowerSeries.coeff n F := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hp : 0 < n := Nat.pos_of_ne_zero hn
    have hsplit : n = (n - 1) + 1 := by omega
    calc
      PowerSeries.coeff n
          (PowerSeries.X * PowerSeries.derivative (R := ℚ) F) =
        PowerSeries.coeff ((n - 1) + 1)
          (PowerSeries.X ^ 1 * PowerSeries.derivative (R := ℚ) F) := by
            simpa only [pow_one] using congrArg
              (fun k : ℕ => PowerSeries.coeff k
                (PowerSeries.X * PowerSeries.derivative (R := ℚ) F)) hsplit
      _ = PowerSeries.coeff (n - 1)
          (PowerSeries.derivative (R := ℚ) F) := by
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

/-- Coefficients of the weighted operator `q X U' + h₀ U`. -/
private theorem coeff_weighted_fixed_operator
    (U : PowerSeries ℚ) (q h₀ k : ℕ) :
    PowerSeries.coeff k
        (PowerSeries.C (q : ℚ) * PowerSeries.X *
            PowerSeries.derivative (R := ℚ) U +
          PowerSeries.C (h₀ : ℚ) * U) =
      (((q * k + h₀ : ℕ) : ℚ)) * PowerSeries.coeff k U := by
  rw [show PowerSeries.C (q : ℚ) * PowerSeries.X *
        PowerSeries.derivative (R := ℚ) U =
      PowerSeries.C (q : ℚ) *
        (PowerSeries.X * PowerSeries.derivative (R := ℚ) U) by ring]
  rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    coeff_X_mul_derivative_all]
  norm_num
  push_cast
  ring

/-- Coefficient extraction from the fixed-core differential equation. -/
theorem coefficients_of_fixed_differential
    (A U : PowerSeries ℚ) (q h₀ : ℕ)
    (hA0 : PowerSeries.constantCoeff A = 1)
    (hODE :
      PowerSeries.X * PowerSeries.derivative (R := ℚ) U =
        (A - 1) *
          (PowerSeries.C (q : ℚ) * PowerSeries.X *
              PowerSeries.derivative (R := ℚ) U +
            PowerSeries.C (h₀ : ℚ) * U)) :
    SatisfiesAuxiliaryFixedRecurrence q h₀
      (fun n => PowerSeries.coeff n A)
      (fun n => PowerSeries.coeff n U) := by
  intro n hn
  have hcoeff := congrArg (PowerSeries.coeff n) hODE
  rw [coeff_X_mul_derivative_all] at hcoeff
  have hrhs :
      PowerSeries.coeff n
        ((A - 1) *
          (PowerSeries.C (q : ℚ) * PowerSeries.X *
              PowerSeries.derivative (R := ℚ) U +
            PowerSeries.C (h₀ : ℚ) * U)) =
        ∑ k ∈ Finset.range n,
          (((q * k + h₀ : ℕ) : ℚ)) *
            PowerSeries.coeff k U * PowerSeries.coeff (n - k) A := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Finset.sum_range_succ']
    have hzero : PowerSeries.coeff 0 (A - 1) = 0 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply, hA0]
    rw [hzero]
    simp only [zero_mul, add_zero]
    have hreflect := Finset.sum_range_reflect
      (fun k => (((q * k + h₀ : ℕ) : ℚ)) *
        PowerSeries.coeff k U * PowerSeries.coeff (n - k) A) n
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hjp : 0 < j + 1 := by omega
    have hsub1 : n - (j + 1) = n - 1 - j := by omega
    have hsub2 : n - (n - 1 - j) = j + 1 := by omega
    rw [hsub1, hsub2,
      coeff_weighted_fixed_operator]
    have hposcoeff :
        PowerSeries.coeff (j + 1) (A - 1) =
          PowerSeries.coeff (j + 1) A := by
      simp [hjp.ne']
    rw [hposcoeff]
    ring
  rw [hrhs] at hcoeff
  exact hcoeff

/-- The power `A^h₀` satisfies the fixed-core differential equation. -/
theorem fixed_power_differential
    (A : PowerSeries ℚ) (c : ℚ) (q h₀ : ℕ)
    (hbase : 1 ≤ h₀)
    (hA : A =
      1 + PowerSeries.C c * PowerSeries.X * A ^ (q + 1)) :
    PowerSeries.X * PowerSeries.derivative (R := ℚ) (A ^ h₀) =
      (A - 1) *
        (PowerSeries.C (q : ℚ) * PowerSeries.X *
            PowerSeries.derivative (R := ℚ) (A ^ h₀) +
          PowerSeries.C (h₀ : ℚ) * A ^ h₀) := by
  have htree := scaled_raney_tree_differential A c q hA
  have hcast :
      PowerSeries.C (((q + 1 : ℕ) : ℚ)) =
        PowerSeries.C (q : ℚ) + 1 := by
    norm_num
  rw [hcast] at htree
  have hbaseA :
      PowerSeries.X * PowerSeries.derivative (R := ℚ) A =
        (A - 1) *
          (PowerSeries.C (q : ℚ) * PowerSeries.X *
              PowerSeries.derivative (R := ℚ) A + A) := by
    linear_combination htree
  have hder := (PowerSeries.derivative (R := ℚ)).leibniz_pow A h₀
  have hder' :
      PowerSeries.derivative (R := ℚ) (A ^ h₀) =
        PowerSeries.C (h₀ : ℚ) * A ^ (h₀ - 1) *
          PowerSeries.derivative (R := ℚ) A := by
    have hhC : (h₀ : PowerSeries ℚ) =
        PowerSeries.C (h₀ : ℚ) := by
      norm_num
    rw [(PowerSeries.derivative (R := ℚ)).leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul]
    rw [hhC]
    ring
  have hexp : h₀ - 1 + 1 = h₀ := by omega
  have hpow : A ^ (h₀ - 1) * A = A ^ h₀ := by
    rw [← pow_succ, hexp]
  rw [hder']
  calc
    PowerSeries.X *
        (PowerSeries.C (h₀ : ℚ) * A ^ (h₀ - 1) *
          PowerSeries.derivative (R := ℚ) A) =
      PowerSeries.C (h₀ : ℚ) * A ^ (h₀ - 1) *
        (PowerSeries.X * PowerSeries.derivative (R := ℚ) A) := by ring
    _ = PowerSeries.C (h₀ : ℚ) * A ^ (h₀ - 1) *
        ((A - 1) *
          (PowerSeries.C (q : ℚ) * PowerSeries.X *
              PowerSeries.derivative (R := ℚ) A + A)) := by rw [hbaseA]
    _ = (A - 1) *
        (PowerSeries.C (q : ℚ) * PowerSeries.X *
            (PowerSeries.C (h₀ : ℚ) * A ^ (h₀ - 1) *
              PowerSeries.derivative (R := ℚ) A) +
          PowerSeries.C (h₀ : ℚ) * A ^ h₀) := by
      rw [← hpow]
      ring

/-- Coefficients of a scalar multiple of `A^h₀`. -/
def fixedAuxiliaryCoefficient
    (A : PowerSeries ℚ) (u₀ : ℚ) (h₀ n : ℕ) : ℚ :=
  u₀ * PowerSeries.coeff n (A ^ h₀)

/-- The coefficient sequence of `u₀ A^h₀` satisfies the normalized
fixed-core recurrence. -/
theorem fixedAuxiliaryCoefficient_recurrence
    (A : PowerSeries ℚ) (c u₀ : ℚ) (q h₀ : ℕ)
    (hbase : 1 ≤ h₀)
    (hA : A =
      1 + PowerSeries.C c * PowerSeries.X * A ^ (q + 1)) :
    SatisfiesAuxiliaryFixedRecurrence q h₀
      (fun n => PowerSeries.coeff n A)
      (fixedAuxiliaryCoefficient A u₀ h₀) := by
  have hA0 : PowerSeries.constantCoeff A = 1 := by
    rw [hA]
    simp
  have hpowODE := fixed_power_differential A c q h₀ hbase hA
  have hrec := coefficients_of_fixed_differential
    A (A ^ h₀) q h₀ hA0 hpowODE
  intro n hn
  have hnrec := hrec n hn
  unfold fixedAuxiliaryCoefficient
  calc
    (n : ℚ) * (u₀ * PowerSeries.coeff n (A ^ h₀)) =
        u₀ * ((n : ℚ) * PowerSeries.coeff n (A ^ h₀)) := by ring
    _ = u₀ *
        (∑ k ∈ Finset.range n,
          (((q * k + h₀ : ℕ) : ℚ)) *
            PowerSeries.coeff k (A ^ h₀) *
              PowerSeries.coeff (n - k) A) := by rw [hnrec]
    _ = ∑ k ∈ Finset.range n,
        (((q * k + h₀ : ℕ) : ℚ)) *
          (u₀ * PowerSeries.coeff k (A ^ h₀)) *
            PowerSeries.coeff (n - k) A := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- The normalized fixed-core recurrence is triangular and hence has a
unique solution once `u_0` is fixed. -/
theorem auxiliary_fixed_recurrence_unique
    (q h₀ : ℕ) (a u v : ℕ → ℚ)
    (hu : SatisfiesAuxiliaryFixedRecurrence q h₀ a u)
    (hv : SatisfiesAuxiliaryFixedRecurrence q h₀ a v)
    (hzero : u 0 = v 0) :
    ∀ n : ℕ, u n = v n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        exact hzero
      · have hn : 0 < n := Nat.pos_of_ne_zero hn0
        have huN := hu n hn
        have hvN := hv n hn
        have hsums :
            (∑ k ∈ Finset.range n,
              (((q * k + h₀ : ℕ) : ℚ)) * u k * a (n - k)) =
            ∑ k ∈ Finset.range n,
              (((q * k + h₀ : ℕ) : ℚ)) * v k * a (n - k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          rw [ih k hk]
        have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
        apply mul_left_cancel₀ hnQ
        calc
          (n : ℚ) * u n =
              ∑ k ∈ Finset.range n,
                (((q * k + h₀ : ℕ) : ℚ)) * u k * a (n - k) := huN
          _ = ∑ k ∈ Finset.range n,
                (((q * k + h₀ : ℕ) : ℚ)) * v k * a (n - k) := hsums
          _ = (n : ℚ) * v n := hvN.symm

/-- Explicit solution of the normalized fixed-core recurrence. -/
theorem auxiliary_fixed_recurrence_explicit
    (q h₀ : ℕ) (a u : ℕ → ℚ)
    (hbase : 1 ≤ h₀)
    (htree : SatisfiesAuxiliaryTreeRecurrence q a)
    (hfixed : SatisfiesAuxiliaryFixedRecurrence q h₀ a u)
    (ha1 : a 1 ≠ 0) (n : ℕ) :
    u n = u 0 * (a 1) ^ n *
      PolytopeCounting.LagrangeBurmann.RaneyApplication.raneyNumber
        (q + 1) h₀ n := by
  let A : PowerSeries ℚ := auxiliarySeries a
  have hA := functional_equation_of_auxiliary_recurrence q a htree
  have hcand := fixedAuxiliaryCoefficient_recurrence
    A (a 1) (u 0) q h₀ hbase hA
  have hfixedA :
      SatisfiesAuxiliaryFixedRecurrence q h₀
        (fun k => PowerSeries.coeff k A) u := by
    intro m hm
    calc
      (m : ℚ) * u m =
          ∑ k ∈ Finset.range m,
            (((q * k + h₀ : ℕ) : ℚ)) * u k * a (m - k) :=
        hfixed m hm
      _ = ∑ k ∈ Finset.range m,
            (((q * k + h₀ : ℕ) : ℚ)) * u k *
              PowerSeries.coeff (m - k) A := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        have hmk : 0 < m - k := by omega
        dsimp [A]
        rw [coeff_auxiliarySeries_of_pos a hmk]
  have hzero : u 0 = fixedAuxiliaryCoefficient A (u 0) h₀ 0 := by
    unfold fixedAuxiliaryCoefficient
    have hA0 : PowerSeries.constantCoeff A = 1 := by
      dsimp [A]
      simp
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hA0]
  have heq := auxiliary_fixed_recurrence_unique q h₀
    (fun n => PowerSeries.coeff n A) u
    (fixedAuxiliaryCoefficient A (u 0) h₀)
    hfixedA hcand hzero n
  have hcoeff :=
    PolytopeCounting.LagrangeBurmann.ScaledRaneyApplication.coeff_scaled_solution_pow_eq_raney
        A (a 1) (q + 1) h₀ n ha1 hA hbase
  unfold fixedAuxiliaryCoefficient at heq
  rw [hcoeff] at heq
  simpa [mul_assoc] using heq


end
end ExplicitFormulas
end PolytopeCounting
