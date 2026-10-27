module

public import Proofs.PoissonLocalEstimate
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact Poisson moments, parity, and a tail estimate

These lemmas concern the literal positive weights used in MatchingSaddlePoint.
They are proved from their series and recurrence. In particular, the parity
mass and the variance bound are not local-limit hypotheses.
-/

namespace PolytopeCounting.MatchingSaddle

noncomputable section
open Filter
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable

/-- Normalization of the actual weights. -/
theorem poissonWeight_hasSum_one (a : ℝ) (ha : 0 ≤ a) :
    HasSum (poissonWeight a) 1 := by
  exact ProbabilityTheory.hasSum_one_poissonMeasure ⟨a, ha⟩

/-- First moment, obtained by shifting the recurrence by one. -/
theorem poissonWeight_hasSum_mean (a : ℝ) (ha : 0 ≤ a) :
    HasSum (fun j : ℕ ↦ (j : ℝ)*poissonWeight a j) a := by
  have hs : HasSum (fun j : ℕ ↦ ((j+1 : ℕ) : ℝ)*poissonWeight a (j+1)) a := by
    convert (poissonWeight_hasSum_one a ha).mul_left a using 1
    · ext j
      simpa using poissonWeight_succ a j
    · ring
  simpa using HasSum.zero_add (f := fun j : ℕ ↦ (j : ℝ) * poissonWeight a j) hs

/-- Second factorial moment. Real subtraction avoids natural truncation. -/
theorem poissonWeight_hasSum_second_factorial (a : ℝ) (ha : 0 ≤ a) :
    HasSum (fun j : ℕ ↦ (j : ℝ)*((j : ℝ)-1)*poissonWeight a j) (a^2) := by
  have he (j : ℕ) :
      ((j+2 : ℕ) : ℝ)*(((j+2 : ℕ) : ℝ)-1)*poissonWeight a (j+2) =
        a^2*poissonWeight a j := by
    have h1 := poissonWeight_succ a j
    have h2 := poissonWeight_succ a (j+1)
    push_cast at h1 h2 ⊢
    nlinarith [congrArg (fun x : ℝ ↦ ((j : ℝ)+1)*x) h2,
      congrArg (fun x : ℝ ↦ a*x) h1]
  have hs : HasSum (fun j : ℕ ↦ ((j+2 : ℕ) : ℝ)*
      (((j+2 : ℕ) : ℝ)-1)*poissonWeight a (j+2)) (a^2) := by
    simpa only [he, mul_one] using (poissonWeight_hasSum_one a ha).mul_left (a^2)
  simpa [Finset.sum_range_succ] using
    HasSum.sum_range_add (f := fun j : ℕ ↦ (j : ℝ) * ((j : ℝ) - 1) *
      poissonWeight a j) (k := 2) hs

/-- The centered second moment is exactly a. -/
theorem poissonWeight_hasSum_variance (a : ℝ) (ha : 0 ≤ a) :
    HasSum (fun j : ℕ ↦ ((j : ℝ)-a)^2*poissonWeight a j) a := by
  have h0 := poissonWeight_hasSum_one a ha
  have h1 := poissonWeight_hasSum_mean a ha
  have h2 := poissonWeight_hasSum_second_factorial a ha
  convert ((h2.add h1).sub (h1.mul_left (2*a))).add (h0.mul_left (a^2)) using 1
  · ext j; ring
  · ring

theorem neg_one_pow_mod_two (n : ℕ) :
    (-1 : ℝ)^n = (-1 : ℝ)^(n%2) := by
  conv_lhs => rw [← Nat.mod_add_div n 2]
  rw [pow_add, pow_mul]
  norm_num

/-- Alternating mass is exponentially small. -/
theorem poissonWeight_hasSum_alternating (a : ℝ) :
    HasSum (fun j : ℕ ↦ (-1 : ℝ)^j*poissonWeight a j) (Real.exp (-2*a)) := by
  have he := (NormedSpace.expSeries_div_hasSum_exp (-a)).mul_left (Real.exp (-a))
  convert he using 1
  · ext j
    simp only [poissonWeight]
    rw [neg_pow a j]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1; ring

def parityWeight (a : ℝ) (p j : ℕ) : ℝ :=
  if j%2 = p%2 then poissonWeight a j else 0

def parityMass (a : ℝ) (p : ℕ) : ℝ := ∑' j, parityWeight a p j

theorem parityWeight_rewrite (a : ℝ) (p j : ℕ) :
    parityWeight a p j =
      (poissonWeight a j + (-1 : ℝ)^p*((-1 : ℝ)^j*poissonWeight a j))/2 := by
  rw [neg_one_pow_mod_two p, neg_one_pow_mod_two j]
  have hp : p%2 = 0 ∨ p%2 = 1 := by omega
  have hj : j%2 = 0 ∨ j%2 = 1 := by omega
  rcases hp with hp|hp <;> rcases hj with hj|hj <;>
    simp [parityWeight, hp, hj] <;> ring

theorem parityWeight_hasSum (a : ℝ) (ha : 0 ≤ a) (p : ℕ) :
    HasSum (parityWeight a p) ((1+(-1 : ℝ)^p*Real.exp (-2*a))/2) := by
  convert
    ((poissonWeight_hasSum_one a ha).add
      ((poissonWeight_hasSum_alternating a).mul_left ((-1 : ℝ)^p))).div_const 2 using 1
  ext j
  exact parityWeight_rewrite a p j

theorem parityMass_eq (a : ℝ) (ha : 0 ≤ a) (p : ℕ) :
    parityMass a p = (1+(-1 : ℝ)^p*Real.exp (-2*a))/2 :=
  (parityWeight_hasSum a ha p).tsum_eq

theorem parityMass_error (a : ℝ) (ha : 0 ≤ a) (p : ℕ) :
    |parityMass a p - 1/2| = Real.exp (-2*a)/2 := by
  rw [parityMass_eq a ha p]
  have he : (1+(-1 : ℝ)^p*Real.exp (-2*a))/2-1/2 =
      (-1 : ℝ)^p*Real.exp (-2*a)/2 := by ring
  rw [he, abs_div, abs_mul, abs_pow]
  simp

/-- Scalar Chebyshev bound, applied to any subset of the tail. -/
theorem poissonWeight_tail_bound (a w : ℝ) (ha : 0 ≤ a) (hw : 0 < w)
    (S : Set ℕ) (hS : ∀ j ∈ S, w < |(j : ℝ)-a|) :
    (∑' j : ℕ, if j ∈ S then poissonWeight a j else 0) ≤ a/w^2 := by
  classical
  have hp := poissonWeight_hasSum_one a ha
  have hv := poissonWeight_hasSum_variance a ha
  have htail : Summable (fun j : ℕ ↦ if j ∈ S then poissonWeight a j else 0) :=
    Summable.of_nonneg_of_le (fun j ↦ by
      split_ifs
      · exact poissonWeight_nonneg a j ha
      · exact le_rfl)
      (fun j ↦ by split_ifs; exact le_rfl; exact poissonWeight_nonneg a j ha) hp.summable
  have hbound (j : ℕ) :
      (if j ∈ S then poissonWeight a j else 0) ≤
        (((j : ℝ)-a)^2*poissonWeight a j)/w^2 := by
    by_cases hj : j ∈ S
    · rw [if_pos hj]
      have hsq : w^2 ≤ ((j : ℝ)-a)^2 := by
        have hab := hS j hj
        nlinarith [sq_abs ((j : ℝ)-a)]
      apply (le_div_iff₀ (sq_pos_of_pos hw)).2
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_right hsq (poissonWeight_nonneg a j ha)
    · rw [if_neg hj]
      exact div_nonneg (mul_nonneg (sq_nonneg _) (poissonWeight_nonneg a j ha))
        (sq_nonneg w)
  exact (Summable.tsum_le_tsum hbound htail (hv.div_const (w^2)).summable).trans_eq
    (hv.div_const (w^2)).tsum_eq

/-- A useful finite probability bound. -/
theorem poissonWeight_sum_le_one (a : ℝ) (ha : 0 ≤ a) (S : Finset ℕ) :
    ∑ j ∈ S, poissonWeight a j ≤ 1 := by
  have h := poissonWeight_hasSum_one a ha
  exact (h.summable.sum_le_tsum S (fun j _ ↦ poissonWeight_nonneg a j ha)).trans_eq h.tsum_eq

end
end PolytopeCounting.MatchingSaddle
