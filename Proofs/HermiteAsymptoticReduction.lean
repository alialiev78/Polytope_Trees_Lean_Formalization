module

public import Proofs.PublicNumerals

public import Proofs.PhysicistsHermiteExact
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-! # Normalization of the matching asymptotic

The exact matching sum and its leading term are related to the disconnected
count by factorial normalization. The matching limit is proved by the
Poisson and saddle-point modules and applied in
`UnconditionalMatchingAsymptotic`.
-/

namespace PolytopeCounting
namespace HermiteAsymptotic

open scoped BigOperators

noncomputable section

open Filter
open scoped Topology

/-- Ratio form of asymptotic equivalence for real sequences. -/
def SequenceEquivalent (u v : ℕ → ℝ) : Prop :=
  Tendsto (fun n ↦ u n / v n) atTop (𝓝 1)

/-- Dividing both sequences by the same nowhere-zero normalization preserves
ratio asymptotic equivalence. -/
theorem SequenceEquivalent.div_same
    {u v A : ℕ → ℝ}
    (hA : ∀ n, A n ≠ 0)
    (h : SequenceEquivalent u v) :
    SequenceEquivalent (fun n ↦ u n / A n) (fun n ↦ v n / A n) := by
  unfold SequenceEquivalent at h ⊢
  have hfun :
      (fun n ↦ (u n / A n) / (v n / A n)) =
        (fun n ↦ u n / v n) := by
    funext n
    by_cases hv : v n = 0
    · simp [hv]
    · field_simp [hA n, hv]
  rw [hfun]
  exact h

/-- The real weighted matching sum whose complexification occurs in
`HermiteExact.matchingFactorialSum`. -/
def matchingFactorialSumReal (N : ℕ) (r : ℝ) : ℝ :=
  ∑ ell ∈ Finset.range (N / 2 + 1),
    (r / 2) ^ ell * (N.factorial : ℝ) /
      ((ell.factorial : ℝ) * ((N - 2 * ell).factorial : ℝ))

/-- The fixed-imaginary Hermite leading term after division by the scale
`(i sqrt(2/r))^N`.  This is the standard weighted-involution asymptotic

`2^{-1/2} exp(-1/(4r)) (rN/e)^{N/2} exp(sqrt(N/r))`.
-/
def matchingHermiteLeadingTerm (N : ℕ) (r : ℝ) : ℝ :=
  (1 / Real.sqrt 2) * Real.exp (-1 / (4 * r)) *
    Real.rpow (r * (N : ℝ) / Real.exp 1) ((N : ℝ) / 2) *
    Real.exp (Real.sqrt ((N : ℝ) / r))

/-- Positivity of the Hermite leading term for positive weight. -/
theorem matchingHermiteLeadingTerm_pos
    (N : ℕ) (r : ℝ) (hr : 0 < r) :
    0 < matchingHermiteLeadingTerm N r := by
  cases N with
  | zero =>
      simp [matchingHermiteLeadingTerm]
      positivity
  | succ N =>
      unfold matchingHermiteLeadingTerm
      have hbase :
          0 < r * ((N + 1 : ℕ) : ℝ) / Real.exp 1 := by
        positivity
      have hrpow := Real.rpow_pos_of_pos hbase (((N + 1 : ℕ) : ℝ) / 2)
      positivity

/-- In particular the Hermite leading term never vanishes for positive
weight. -/
theorem matchingHermiteLeadingTerm_ne_zero
    (N : ℕ) (r : ℝ) (hr : 0 < r) :
    matchingHermiteLeadingTerm N r ≠ 0 :=
  (matchingHermiteLeadingTerm_pos N r hr).ne'

/-- Exact real normalization defining the total disconnected coefficient. -/
def disconnectedTotalReal (h n : ℕ) (r tau : ℝ) : ℝ :=
  matchingFactorialSumReal (h * n) r /
    ((n.factorial : ℝ) * tau ^ n)

/-- The real sequence used for the asymptotic is exactly the real coercion
of the rational closed finite sum. -/
theorem WTotalClosedForm_cast_real
    (h r tau n : ℕ) :
    ((ExplicitFormulas.WTotalClosedForm h r tau n : ℚ) : ℝ) =
      disconnectedTotalReal h n (r : ℝ) (tau : ℝ) := by
  rw [ExplicitFormulas.WTotalClosedForm_eq_sum]
  unfold disconnectedTotalReal matchingFactorialSumReal
  push_cast
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  ring

/-- The corresponding normalized leading term before expanding Stirling's
formula into the manuscript's final display. -/
def disconnectedHermiteLeadingTerm
    (h n : ℕ) (r tau : ℝ) : ℝ :=
  matchingHermiteLeadingTerm (h * n) r /
    ((n.factorial : ℝ) * tau ^ n)

/-- Nonvanishing of the normalized Hermite leading term for positive
weight and nonzero local-symmetry order. -/
theorem disconnectedHermiteLeadingTerm_ne_zero
    (h n : ℕ) (r tau : ℝ) (hr : 0 < r) (htau : tau ≠ 0) :
    disconnectedHermiteLeadingTerm h n r tau ≠ 0 := by
  unfold disconnectedHermiteLeadingTerm
  have hfac : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  exact div_ne_zero
    (matchingHermiteLeadingTerm_ne_zero (h * n) r hr)
    (mul_ne_zero hfac (pow_ne_zero n htau))

/-- The exact normalization is never zero when `tau` is nonzero. -/
theorem disconnectedNormalization_ne_zero
    (tau : ℝ) (htau : tau ≠ 0) (n : ℕ) :
    (n.factorial : ℝ) * tau ^ n ≠ 0 := by
  exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n)
    (pow_ne_zero n htau)

/-- Formal transfer from the fixed-imaginary Hermite asymptotic to the total
`W` coefficient.  This theorem contains all normalization bookkeeping; its
only analytic hypothesis is the weighted matching/Hermite asymptotic itself. -/
theorem disconnectedTotal_equivalent_of_matching
    (h : ℕ) (r tau : ℝ) (htau : tau ≠ 0)
    (hHermite :
      SequenceEquivalent
        (fun n ↦ matchingFactorialSumReal (h * n) r)
        (fun n ↦ matchingHermiteLeadingTerm (h * n) r)) :
    SequenceEquivalent
      (fun n ↦ disconnectedTotalReal h n r tau)
      (fun n ↦ disconnectedHermiteLeadingTerm h n r tau) := by
  exact SequenceEquivalent.div_same
    (fun n ↦ disconnectedNormalization_ne_zero tau htau n) hHermite

/-- The matching-limit proposition proved in `UnconditionalMatchingAsymptotic`. -/
def FixedImaginaryHermiteAsymptotic (h : ℕ) (r : ℝ) : Prop :=
  SequenceEquivalent
    (fun n ↦ matchingFactorialSumReal (h * n) r)
    (fun n ↦ matchingHermiteLeadingTerm (h * n) r)

/-- Transfer of the matching limit to the normalized `W` count. -/
theorem disconnectedTotal_equivalent_of_fixedImaginaryHermite
    (h : ℕ) (r tau : ℝ) (htau : tau ≠ 0)
    (hHermite : FixedImaginaryHermiteAsymptotic h r) :
    SequenceEquivalent
      (fun n ↦ disconnectedTotalReal h n r tau)
      (fun n ↦ disconnectedHermiteLeadingTerm h n r tau) := by
  exact disconnectedTotal_equivalent_of_matching h r tau htau hHermite

/-- Stirling's formula is already available in Mathlib and is imported by
this module.  This named theorem records the exact library theorem used for
the final elementary simplification. -/
theorem factorial_isEquivalent_stirling :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ ↦ (n.factorial : ℝ))
      (fun n : ℕ ↦ Real.sqrt (2 * (n : ℝ) * Real.pi) *
        ((n : ℝ) / Real.exp 1) ^ n) :=
  Stirling.factorial_isEquivalent_stirling


end
end HermiteAsymptotic
end PolytopeCounting

namespace PolytopeCounting
namespace HermiteAsymptotic

noncomputable section

open Filter
open scoped Topology

/-- Transitivity of ratio asymptotic equivalence when the intermediate
sequence is nowhere zero. -/
theorem SequenceEquivalent.trans_of_ne
    {u v w : ℕ → ℝ}
    (hv : ∀ n, v n ≠ 0)
    (huv : SequenceEquivalent u v)
    (hvw : SequenceEquivalent v w) :
    SequenceEquivalent u w := by
  unfold SequenceEquivalent at huv hvw ⊢
  have hmul := huv.mul hvw
  have hfun :
      (fun n ↦ (u n / v n) * (v n / w n)) =
        (fun n ↦ u n / w n) := by
    funext n
    by_cases hw : w n = 0
    · simp [hw]
    · field_simp [hv n, hw]
  rw [hfun] at hmul
  simpa using hmul

section
attribute [local instance 2000] PolytopeCounting.PublicNumerals.two PolytopeCounting.PublicNumerals.three PolytopeCounting.PublicNumerals.four PolytopeCounting.PublicNumerals.five PolytopeCounting.PublicNumerals.six
/-- The final leading term displayed in Statement 6.4.  Real powers are used
so this definition also covers odd `h`. -/
def statement64LeadingTerm
    (h n : ℕ) (r tau : ℝ) : ℝ :=
  1 / (2 * Real.sqrt (Real.pi * (n : ℝ))) *
    Real.exp (-1 / (4 * r)) *
    (Real.rpow (r * (h : ℝ)) ((h : ℝ) / 2) *
        Real.exp (1 - (h : ℝ) / 2) / tau) ^ n *
    Real.rpow (n : ℝ) ((n : ℝ) * ((h : ℝ) / 2 - 1)) *
    Real.exp (Real.sqrt (((h * n : ℕ) : ℝ) / r))
end

/-- Formal statement corresponding to the Hermite asymptotic in the paper. -/
def Statement64 (h : ℕ) (r tau : ℝ) : Prop :=
  SequenceEquivalent
    (fun n ↦ disconnectedTotalReal h n r tau)
    (fun n ↦ statement64LeadingTerm h n r tau)

/-- The purely Stirling/algebraic bridge between the structured Hermite
leading term and the expanded display in Statement 6.4. -/
def StirlingRewriteForStatement64 (h : ℕ) (r tau : ℝ) : Prop :=
  SequenceEquivalent
    (fun n ↦ disconnectedHermiteLeadingTerm h n r tau)
    (fun n ↦ statement64LeadingTerm h n r tau)

/-- Statement 6.4 follows from exactly two isolated inputs: the
fixed-imaginary Hermite asymptotic and the Stirling/algebraic rewrite. -/
theorem statement64_of_hermite_and_stirling
    (h : ℕ) (r tau : ℝ)
    (htau : tau ≠ 0)
    (hmid : ∀ n, disconnectedHermiteLeadingTerm h n r tau ≠ 0)
    (hHermite : FixedImaginaryHermiteAsymptotic h r)
    (hStirling : StirlingRewriteForStatement64 h r tau) :
    Statement64 h r tau := by
  exact SequenceEquivalent.trans_of_ne hmid
    (disconnectedTotal_equivalent_of_fixedImaginaryHermite
      h r tau htau hHermite)
    hStirling


end
end HermiteAsymptotic
end PolytopeCounting

namespace PolytopeCounting
namespace HermiteAsymptotic

noncomputable section

open Filter
open scoped Topology

/-- The explicit Stirling denominator from Mathlib's theorem. -/
def stirlingApprox (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) * Real.pi) *
    ((n : ℝ) / Real.exp 1) ^ n

/-- The structured leading term obtained by replacing `n!` by its Stirling
approximation, before rewriting real powers into the final display. -/
def disconnectedStirlingLeadingTerm
    (h n : ℕ) (r tau : ℝ) : ℝ :=
  matchingHermiteLeadingTerm (h * n) r /
    (stirlingApprox n * tau ^ n)

/-- Mathlib's Stirling theorem expressed in the ratio orientation needed
below: `stirlingApprox n / n! -> 1`. -/
theorem tendsto_stirlingApprox_div_factorial :
    Tendsto
      (fun n : ℕ ↦ stirlingApprox n / (n.factorial : ℝ))
      atTop (𝓝 1) := by
  have hEq :
      Asymptotics.IsEquivalent atTop
        (fun n : ℕ ↦ stirlingApprox n)
        (fun n : ℕ ↦ (n.factorial : ℝ)) := by
    simpa [stirlingApprox] using
      Stirling.factorial_isEquivalent_stirling.symm
  have hne : ∀ᶠ n : ℕ in atTop, (n.factorial : ℝ) ≠ 0 :=
    Filter.Eventually.of_forall (fun n ↦ by
      exact_mod_cast Nat.factorial_ne_zero n)
  exact (Asymptotics.isEquivalent_iff_tendsto_one hne).mp hEq

/-- The Stirling part of Statement 6.4, before the final exact `rpow`
rearrangement. -/
theorem disconnectedHermite_equivalent_stirlingNormalized
    (h : ℕ) (r tau : ℝ)
    (htau : tau ≠ 0)
    (hnum : ∀ n, matchingHermiteLeadingTerm (h * n) r ≠ 0) :
    SequenceEquivalent
      (fun n ↦ disconnectedHermiteLeadingTerm h n r tau)
      (fun n ↦ disconnectedStirlingLeadingTerm h n r tau) := by
  unfold SequenceEquivalent
  have hfun :
      (fun n ↦ disconnectedHermiteLeadingTerm h n r tau /
        disconnectedStirlingLeadingTerm h n r tau) =
      (fun n ↦ stirlingApprox n / (n.factorial : ℝ)) := by
    funext n
    unfold disconnectedHermiteLeadingTerm disconnectedStirlingLeadingTerm
    have hfac : (n.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    have htaupow : tau ^ n ≠ 0 := pow_ne_zero n htau
    field_simp [hnum n, hfac, htaupow]
  rw [hfun]
  exact tendsto_stirlingApprox_div_factorial

/-- The elementary real-power rearrangement used in Statement 6.4.  This is formulated
as eventual equality because all possible zero-index conventions are
irrelevant at `atTop`. -/
def ExpandedStatement64Rewrite (h : ℕ) (r tau : ℝ) : Prop :=
  (fun n ↦ disconnectedStirlingLeadingTerm h n r tau) =ᶠ[atTop]
    (fun n ↦ statement64LeadingTerm h n r tau)

/-- Eventual equality converts the structured Stirling leading term into the
literal display of Statement 6.4. -/
theorem stirlingRewriteForStatement64_of_expanded
    (h : ℕ) (r tau : ℝ)
    (htau : tau ≠ 0)
    (hnum : ∀ n, matchingHermiteLeadingTerm (h * n) r ≠ 0)
    (hexpand : ExpandedStatement64Rewrite h r tau) :
    StirlingRewriteForStatement64 h r tau := by
  unfold StirlingRewriteForStatement64
  have hstir := disconnectedHermite_equivalent_stirlingNormalized
    h r tau htau hnum
  unfold SequenceEquivalent at hstir ⊢
  apply hstir.congr'
  filter_upwards [hexpand] with n hn
  rw [hn]


end
end HermiteAsymptotic
end PolytopeCounting

namespace PolytopeCounting
namespace HermiteAsymptotic

noncomputable section

/-- Positive-parameter transfer of the exact real-power rearrangement. -/
theorem stirlingRewriteForStatement64_of_expanded_pos
    (h : ℕ) (r tau : ℝ)
    (hr : 0 < r) (htau : tau ≠ 0)
    (hexpand : ExpandedStatement64Rewrite h r tau) :
    StirlingRewriteForStatement64 h r tau := by
  apply stirlingRewriteForStatement64_of_expanded h r tau htau
  · intro n
    exact matchingHermiteLeadingTerm_ne_zero (h * n) r hr
  · exact hexpand

/-- Statement 6.4 follows from the fixed-imaginary Hermite asymptotic and
the exact expansion of the structured Stirling term. -/
theorem statement64_of_hermite_and_expanded
    (h : ℕ) (r tau : ℝ)
    (hr : 0 < r) (htau : tau ≠ 0)
    (hHermite : FixedImaginaryHermiteAsymptotic h r)
    (hexpand : ExpandedStatement64Rewrite h r tau) :
    Statement64 h r tau := by
  apply statement64_of_hermite_and_stirling h r tau htau
  · intro n
    exact disconnectedHermiteLeadingTerm_ne_zero h n r tau hr htau
  · exact hHermite
  · exact stirlingRewriteForStatement64_of_expanded_pos
      h r tau hr htau hexpand


end
end HermiteAsymptotic
end PolytopeCounting
