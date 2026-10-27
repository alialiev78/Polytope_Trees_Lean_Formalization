module

public import Proofs.RaneyApplication
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Scaled Lagrange--Bürmann/Raney extraction

The manuscript does not only use the normalized functional equation

`A = 1 + X * A^p`,

but also its scaled form

`A = 1 + c X A^p`.

This file proves the corresponding coefficient formula

`[X^n] A^q = c^n * Raney(p,q,n)`

by rescaling the formal variable and applying the polynomial
Lagrange--Bürmann theorem already proved in `LagrangeBurmannPolynomial`.
-/

namespace PolytopeCounting
namespace LagrangeBurmann
namespace ScaledRaneyApplication

open RaneyApplication

noncomputable section

private theorem rescale_C (a c : ℚ) :
    PowerSeries.rescale a (PowerSeries.C c) = PowerSeries.C c := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [PowerSeries.coeff_rescale]
  · rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
    simp [hn]

/-- Rescaling by `c⁻¹` turns `A = 1 + c X A^p` into the normalized
functional equation. -/
theorem rescale_scaled_solution
    (A : PowerSeries ℚ) (c : ℚ) (p : ℕ)
    (hc : c ≠ 0)
    (hA : A = 1 + PowerSeries.C c * PowerSeries.X * A ^ p) :
    PowerSeries.rescale c⁻¹ A =
      1 + PowerSeries.X * (PowerSeries.rescale c⁻¹ A) ^ p := by
  calc
    PowerSeries.rescale c⁻¹ A =
        PowerSeries.rescale c⁻¹
          (1 + PowerSeries.C c * PowerSeries.X * A ^ p) :=
      congrArg (PowerSeries.rescale c⁻¹) hA
    _ = 1 +
        (PowerSeries.C c * (PowerSeries.C c⁻¹ * PowerSeries.X)) *
          (PowerSeries.rescale c⁻¹ A) ^ p := by
      rw [map_add, map_one, map_mul, map_mul, map_pow,
        rescale_C, PowerSeries.rescale_X]
    _ = 1 + PowerSeries.X * (PowerSeries.rescale c⁻¹ A) ^ p := by
      have hcinv : c * c⁻¹ = 1 := by exact mul_inv_cancel₀ hc
      rw [← mul_assoc, ← map_mul, hcinv, map_one, one_mul]

/-- Scaled Raney coefficient extraction. -/
theorem coeff_scaled_solution_pow_eq_raney
    (A : PowerSeries ℚ) (c : ℚ) (p q n : ℕ)
    (hc : c ≠ 0)
    (hA : A = 1 + PowerSeries.C c * PowerSeries.X * A ^ p)
    (hq : 0 < q) :
    PowerSeries.coeff n (A ^ q) =
      c ^ n * RaneyApplication.raneyNumber p q n := by
  let B : PowerSeries ℚ := PowerSeries.rescale c⁻¹ A
  have hB : B = 1 + PowerSeries.X * B ^ p := by
    dsimp [B]
    exact rescale_scaled_solution A c p hc hA
  have hcoeff :=
    RaneyApplication.coeff_solution_pow_eq_raney B p q n hB hq
  have hpow : B ^ q = PowerSeries.rescale c⁻¹ (A ^ q) := by
    dsimp [B]
    rw [map_pow]
  rw [hpow, PowerSeries.coeff_rescale] at hcoeff
  calc
    PowerSeries.coeff n (A ^ q) =
        c ^ n * ((c⁻¹) ^ n * PowerSeries.coeff n (A ^ q)) := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow, one_mul]
    _ = c ^ n * RaneyApplication.raneyNumber p q n := by rw [hcoeff]

/-- The exact scaled specialization used by the polytope-tree formulas. -/
theorem coeff_scaled_manuscript_solution
    (A : PowerSeries ℚ) (c : ℚ) (h h₀ n : ℕ)
    (hc : c ≠ 0)
    (hA : A = 1 + PowerSeries.C c * PowerSeries.X * A ^ (h - 1))
    (hbase : 0 < h₀) :
    PowerSeries.coeff n (A ^ h₀) =
      c ^ n * RaneyApplication.manuscriptRaneyNumber h h₀ n := by
  exact coeff_scaled_solution_pow_eq_raney
    A c (h - 1) h₀ n hc hA hbase


end
end ScaledRaneyApplication
end LagrangeBurmann
end PolytopeCounting
