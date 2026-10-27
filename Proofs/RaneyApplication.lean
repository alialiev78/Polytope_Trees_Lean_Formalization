module

public import Proofs.LagrangeBurmannPolynomial
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Lagrange--Bürmann for the rooted tree series and Raney numbers

This file specializes `lagrange_burmann_polynomial` to

* `Φ(u) = (1 + u)^p`,
* `H(u) = (1 + u)^q`,
* `B = X * (1 + B)^p`,
* `A = 1 + B`, equivalently `A = 1 + X * A^p`.

For `q > 0` it proves, for every `n`,

`[X^n] A^q = q / (p*n + q) * choose (p*n + q) n`.

This is the Raney-number coefficient formula used in the manuscript.  The
proof is split into three independently reusable steps:

1. the Lagrange--Bürmann coefficient identity;
2. evaluation of the binomial coefficient on the right;
3. conversion from the predecessor-binomial form to the standard Raney form.
-/

namespace PolytopeCounting
namespace LagrangeBurmann
namespace RaneyApplication

open scoped BigOperators
open Polynomial

noncomputable section

/-- The rational Raney number in the manuscript's normalization. -/
def raneyNumber (p q n : ℕ) : ℚ :=
  (q : ℚ) / (p * n + q : ℕ) * (Nat.choose (p * n + q) n : ℚ)

/-- The substitution of `(1 + X)^e` into a series with zero constant term is
literally `(1 + B)^e`. -/
private theorem subst_one_add_X_pow
    {K : Type*} [Field K] [CharZero K]
    (B : PowerSeries K)
    (hB0 : PowerSeries.constantCoeff B = 0)
    (e : ℕ) :
    ((((1 + Polynomial.X) ^ e : K[X]) : PowerSeries K).subst B) =
      (1 + B) ^ e := by
  have hsubst : PowerSeries.HasSubst B :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hB0
  rw [PowerSeries.subst_coe hsubst]
  simp

/-- The familiar equation `B = X * (1 + B)^p` has the exact polynomial-
substitution shape required by the general theorem. -/
private theorem functional_equation_as_subst
    {K : Type*} [Field K] [CharZero K]
    (B : PowerSeries K) (p : ℕ)
    (hB : B = PowerSeries.X * (1 + B) ^ p) :
    B = PowerSeries.X *
      (((((1 + Polynomial.X) ^ p : K[X]) : PowerSeries K).subst B)) := by
  have hB0 : PowerSeries.constantCoeff B = 0 := by
    rw [hB]
    simp
  rw [subst_one_add_X_pow B hB0 p]
  exact hB

/-- Polynomial identity used to evaluate the right side of
Lagrange--Bürmann in the binomial case. -/
private theorem derivative_binomial_product
    (p q n : ℕ) (hq : 0 < q) :
    Polynomial.derivative (((1 + Polynomial.X) ^ q : ℚ[X])) *
        ((1 + Polynomial.X) ^ p : ℚ[X]) ^ n =
      Polynomial.C (q : ℚ) *
        ((1 + Polynomial.X) ^ (p * n + q - 1) : ℚ[X]) := by
  have hexp : q - 1 + p * n = p * n + q - 1 := by omega
  rw [Polynomial.derivative_pow]
  simp only [map_add, Polynomial.derivative_one, Polynomial.derivative_X,
    zero_add, mul_one]
  rw [← pow_mul, mul_assoc, ← pow_add, hexp]

/-- The coefficient form obtained immediately from Lagrange--Bürmann:

`n * [X^n](1+B)^q = q * choose (p*n+q-1) (n-1)`.
-/
theorem lagrange_burmann_binomial
    (B : PowerSeries ℚ) (p q n : ℕ)
    (hB : B = PowerSeries.X * (1 + B) ^ p)
    (hn : 0 < n) :
    (n : ℚ) * PowerSeries.coeff n ((1 + B) ^ q) =
      (q : ℚ) * (Nat.choose (p * n + q - 1) (n - 1) : ℚ) := by
  by_cases hq0 : q = 0
  · subst q
    simp [hn.ne']
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    let Φ : ℚ[X] := (1 + Polynomial.X) ^ p
    let H : ℚ[X] := (1 + Polynomial.X) ^ q
    have hB0 : PowerSeries.constantCoeff B = 0 := by
      rw [hB]
      simp
    have hΦsubst : ((Φ : PowerSeries ℚ).subst B) = (1 + B) ^ p := by
      dsimp [Φ]
      exact subst_one_add_X_pow B hB0 p
    have hHsubst : ((H : PowerSeries ℚ).subst B) = (1 + B) ^ q := by
      dsimp [H]
      exact subst_one_add_X_pow B hB0 q
    have hfun : B = PowerSeries.X * ((Φ : PowerSeries ℚ).subst B) := by
      rw [hΦsubst]
      exact hB
    have hLB := lagrange_burmann_polynomial B Φ H hfun n hn
    rw [hHsubst] at hLB
    have hpoly :
        Polynomial.derivative H * Φ ^ n =
          Polynomial.C (q : ℚ) *
            ((1 + Polynomial.X) ^ (p * n + q - 1) : ℚ[X]) := by
      dsimp [H, Φ]
      exact derivative_binomial_product p q n hq
    have hseries :
        PowerSeries.derivative (R := ℚ) (H : PowerSeries ℚ) *
            (Φ : PowerSeries ℚ) ^ n =
          ((Polynomial.C (q : ℚ) *
              ((1 + Polynomial.X) ^ (p * n + q - 1) : ℚ[X]) : ℚ[X]) :
            PowerSeries ℚ) := by
      calc
        PowerSeries.derivative (R := ℚ) (H : PowerSeries ℚ) *
              (Φ : PowerSeries ℚ) ^ n =
            ((Polynomial.derivative H : ℚ[X]) : PowerSeries ℚ) *
              ((Φ ^ n : ℚ[X]) : PowerSeries ℚ) := by
                rw [PowerSeries.derivative_coe]
                simp
        _ = ((Polynomial.derivative H * Φ ^ n : ℚ[X]) : PowerSeries ℚ) := by
              simp
        _ = ((Polynomial.C (q : ℚ) *
              ((1 + Polynomial.X) ^ (p * n + q - 1) : ℚ[X]) : ℚ[X]) :
            PowerSeries ℚ) := by rw [hpoly]
    rw [hseries] at hLB
    have hcoeff :
        PowerSeries.coeff (n - 1)
            (((Polynomial.C (q : ℚ) *
                ((1 + Polynomial.X) ^ (p * n + q - 1) : ℚ[X]) : ℚ[X]) :
              PowerSeries ℚ)) =
          (q : ℚ) * (Nat.choose (p * n + q - 1) (n - 1) : ℚ) := by
      rw [Polynomial.coeff_coe, Polynomial.coeff_C_mul,
        Polynomial.coeff_one_add_X_pow]
    rw [hcoeff] at hLB
    exact hLB

/-- Divided predecessor-binomial form of the same result. -/
theorem coeff_one_add_pow_eq_predecessor
    (B : PowerSeries ℚ) (p q n : ℕ)
    (hB : B = PowerSeries.X * (1 + B) ^ p)
    (hn : 0 < n) :
    PowerSeries.coeff n ((1 + B) ^ q) =
      (q : ℚ) / (n : ℚ) *
        (Nat.choose (p * n + q - 1) (n - 1) : ℚ) := by
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  apply (mul_left_cancel₀ hnQ)
  calc
    (n : ℚ) * PowerSeries.coeff n ((1 + B) ^ q) =
        (q : ℚ) * (Nat.choose (p * n + q - 1) (n - 1) : ℚ) :=
      lagrange_burmann_binomial B p q n hB hn
    _ = (n : ℚ) *
        ((q : ℚ) / (n : ℚ) *
          (Nat.choose (p * n + q - 1) (n - 1) : ℚ)) := by
      field_simp [hnQ]

/-- Elementary conversion between the two common forms of the Raney number. -/
theorem predecessor_choose_eq_raney
    (p q n : ℕ) (hq : 0 < q) (hn : 0 < n) :
    (q : ℚ) / (n : ℚ) *
        (Nat.choose (p * n + q - 1) (n - 1) : ℚ) =
      raneyNumber p q n := by
  let M : ℕ := p * n + q
  have hM : 0 < M := by
    dsimp [M]
    omega
  have hnat :
      M * Nat.choose (M - 1) (n - 1) = Nat.choose M n * n := by
    have hMstep : M - 1 + 1 = M := by omega
    have hnstep : n - 1 + 1 = n := by omega
    simpa only [hMstep, hnstep] using
      (Nat.add_one_mul_choose_eq (M - 1) (n - 1))
  have hrat :
      (M : ℚ) * (Nat.choose (M - 1) (n - 1) : ℚ) =
        (Nat.choose M n : ℚ) * (n : ℚ) := by
    exact_mod_cast hnat
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  dsimp [raneyNumber, M]
  field_simp [hnQ, hMQ]
  nlinarith [hrat]

/-- Standard Raney-number formula for positive degree. -/
theorem coeff_one_add_pow_eq_raney_of_pos
    (B : PowerSeries ℚ) (p q n : ℕ)
    (hB : B = PowerSeries.X * (1 + B) ^ p)
    (hq : 0 < q) (hn : 0 < n) :
    PowerSeries.coeff n ((1 + B) ^ q) = raneyNumber p q n := by
  rw [coeff_one_add_pow_eq_predecessor B p q n hB hn]
  exact predecessor_choose_eq_raney p q n hq hn

/-- Standard Raney-number formula in every degree, including `n=0`. -/
theorem coeff_one_add_pow_eq_raney
    (B : PowerSeries ℚ) (p q n : ℕ)
    (hB : B = PowerSeries.X * (1 + B) ^ p)
    (hq : 0 < q) :
    PowerSeries.coeff n ((1 + B) ^ q) = raneyNumber p q n := by
  cases n with
  | zero =>
      have hB0 : PowerSeries.constantCoeff B = 0 := by
        rw [hB]
        simp
      simp [raneyNumber, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        hB0, hq.ne']
  | succ n =>
      exact coeff_one_add_pow_eq_raney_of_pos B p q (n + 1) hB hq (by omega)

/-- The manuscript form with `A = 1 + X*A^p` rather than
`B = X*(1+B)^p`. -/
theorem coeff_solution_pow_eq_raney
    (A : PowerSeries ℚ) (p q n : ℕ)
    (hA : A = 1 + PowerSeries.X * A ^ p)
    (hq : 0 < q) :
    PowerSeries.coeff n (A ^ q) = raneyNumber p q n := by
  let B : PowerSeries ℚ := A - 1
  have hBA : 1 + B = A := by
    dsimp [B]
    ring
  have hB : B = PowerSeries.X * (1 + B) ^ p := by
    calc
      B = A - 1 := rfl
      _ = PowerSeries.X * A ^ p := by
        calc
          A - 1 = (1 + PowerSeries.X * A ^ p) - 1 :=
            congrArg (fun S : PowerSeries ℚ => S - 1) hA
          _ = PowerSeries.X * A ^ p := by ring
      _ = PowerSeries.X * (1 + B) ^ p := by rw [hBA]
  rw [← hBA]
  exact coeff_one_add_pow_eq_raney B p q n hB hq


/-- The exact notation used in the manuscript: `p = h - 1` and `q = h₀`. -/
def manuscriptRaneyNumber (h h₀ n : ℕ) : ℚ :=
  raneyNumber (h - 1) h₀ n

/-- Lagrange--Bürmann/Raney formula in the manuscript's `h,h₀` notation.

If `A = 1 + X * A^(h-1)` and the fixed base has at least one boundary
facet, then

`[X^n] A^h₀ = h₀ / ((h-1)n+h₀) * choose (((h-1)n+h₀)) n`.
-/
theorem coeff_manuscript_tree_solution
    (A : PowerSeries ℚ) (h h₀ n : ℕ)
    (hA : A = 1 + PowerSeries.X * A ^ (h - 1))
    (hbase : 0 < h₀) :
    PowerSeries.coeff n (A ^ h₀) = manuscriptRaneyNumber h h₀ n := by
  exact coeff_solution_pow_eq_raney A (h - 1) h₀ n hA hbase


end
end RaneyApplication
end LagrangeBurmann
end PolytopeCounting
