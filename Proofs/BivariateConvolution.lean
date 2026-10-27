module

public import Proofs.FormalExpLogLinearization
public import Proofs.RecursiveXiPairableCore
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Coefficientwise products for `W`, `V`, `Psi`, and `Xi`

The manuscript uses ordinary multiplication of the two-variable normalized
series.  This file records the exact finite Cauchy product.  The definition
is independent of convergence and therefore applies to formal series.
-/

namespace PolytopeCounting
namespace BivariateCoefficients

open scoped BigOperators

abbrev Series (R : Type*) := ℕ → ℕ → R

/-- Finite Cauchy product of bivariate coefficient families. -/
def convolution {R : Type*} [Semiring R]
    (A B : Series R) : Series R :=
  fun n m ↦
    ∑ i ∈ Finset.range (n + 1),
      ∑ j ∈ Finset.range (m + 1),
        A i j * B (n - i) (m - j)

/-- The delta series `1`. -/
def oneSeries {R : Type*} [Semiring R] : Series R :=
  fun n m ↦ if n = 0 ∧ m = 0 then 1 else 0

/-- The degree-zero row concentrated at boundary degree `m₀`. -/
def fixedCoreBase {R : Type*} [Semiring R]
    (c : R) (m₀ : ℕ) : Series R :=
  fun n m ↦ if n = 0 ∧ m = m₀ then c else 0

/-- Literal formal meaning of `Xi = W * Psi`. -/
def XiEqualsProduct {R : Type*} [Semiring R]
    (W Psi Xi : Series R) : Prop :=
  Xi = convolution W Psi

@[simp] theorem convolution_one_left {R : Type*} [Semiring R]
    (A : Series R) :
    convolution oneSeries A = A := by
  funext n m
  simp only [convolution, oneSeries, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  · intro i _ hi
    simp [hi]
  · simp

@[simp] theorem convolution_one_right {R : Type*} [Semiring R]
    (A : Series R) :
    convolution A oneSeries = A := by
  funext n m
  simp only [convolution, oneSeries, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single n]
  · rw [Finset.sum_eq_single m]
    · simp
    · intro j hj hjne
      have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hsub : m - j ≠ 0 := by omega
      simp [hsub]
    · simp
  · intro i hi hine
    have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsub : n - i ≠ 0 := by omega
    simp [hsub]
  · simp

/-- If `W` has the usual degree-zero row `W[0,0]=1`, then the degree-zero
row of `Xi=W*Psi` is exactly the degree-zero row of `Psi`. -/
theorem degree_zero_of_product
    {R : Type*} [Semiring R]
    (W Psi Xi : Series R)
    (hW0 : ∀ m, W 0 m = if m = 0 then 1 else 0)
    (hXi : XiEqualsProduct W Psi Xi) :
    ∀ m, Xi 0 m = Psi 0 m := by
  intro m
  rw [hXi]
  simp [convolution, hW0]

/-- Consequently, a genuinely fixed core gives `Xi[0,m]=c` only at
`m=m₀`; formula (53) cannot be extended to all `n=0` coefficients unless
core--core pairings are part of the model. -/
theorem degree_zero_fixed_core
    {R : Type*} [Semiring R]
    (W Xi : Series R) (c : R) (m₀ : ℕ)
    (hW0 : ∀ m, W 0 m = if m = 0 then 1 else 0)
    (hXi : XiEqualsProduct W (fixedCoreBase c m₀) Xi) :
    ∀ m, Xi 0 m = if m = m₀ then c else 0 := by
  intro m
  rw [degree_zero_of_product W (fixedCoreBase c m₀) Xi hW0 hXi]
  simp [fixedCoreBase]


end BivariateCoefficients
end PolytopeCounting
