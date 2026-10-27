module

public import Proofs.PublicNumerals

public import Proofs.ManuscriptTreeExplicit
public import Proofs.ManuscriptFixedCoreExplicit
public import Proofs.HermiteAsymptoticReduction
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-! # Tree and fixed-core asymptotic normalizations

This module specifies the affine-factorial ratios and transfers their limits
to the manuscript normalizations. `AffineFactorialStirling` proves the
required limits; `ConcreteTreeAsymptotics` supplies the finite-count endpoints.
-/

namespace PolytopeCounting
namespace GeneralAsymptotics

noncomputable section

open Filter
open scoped Topology
open HermiteAsymptotic

/-- Exact boundary-unlabelled, symmetry-weighted groupoid-mass tree
coefficient (23), coerced to `ℝ`.  This is not the ordinary orbit count
`sum 1`. -/
def treeUnlabelledExact (h r tau n : ℕ) : ℝ :=
  (1 / (r : ℝ)) * (((h * r : ℕ) : ℝ) / (tau : ℝ)) ^ n *
    ((n * (h - 1)).factorial : ℝ) /
      ((n.factorial : ℝ) * (((h - 2) * n + 2).factorial : ℝ))

section
attribute [local instance 2000] PolytopeCounting.PublicNumerals.two PolytopeCounting.PublicNumerals.three PolytopeCounting.PublicNumerals.four PolytopeCounting.PublicNumerals.five PolytopeCounting.PublicNumerals.six
/-- Leading term in Corollary 5.1. -/
def treeUnlabelledLeading (h r tau n : ℕ) : ℝ :=
  Real.sqrt (h - 1 : ℝ) /
      ((r : ℝ) * Real.sqrt (2 * Real.pi) *
        Real.rpow (h - 2 : ℝ) (5 / 2 : ℝ)) *
    Real.rpow (n : ℝ) (-5 / 2 : ℝ) *
    ((((h * r : ℕ) : ℝ) / (tau : ℝ)) *
      Real.rpow (h - 1 : ℝ) (h - 1 : ℝ) /
      Real.rpow (h - 2 : ℝ) (h - 2 : ℝ)) ^ n
end

/-- Exact fixed-core coefficient after boundary-label normalization (28). -/
def fixedCoreUnlabelledExact
    (T₀ : ℝ) (h₀ h r tau n : ℕ) : ℝ :=
  T₀ * (((h * r : ℕ) : ℝ) / (tau : ℝ)) ^ n *
    ((n * (h - 1) + h₀ - 1).factorial : ℝ) /
      (((h₀ - 1).factorial : ℝ) * (n.factorial : ℝ) *
        (((h - 2) * n + h₀).factorial : ℝ))

section
attribute [local instance 2000] PolytopeCounting.PublicNumerals.two PolytopeCounting.PublicNumerals.three PolytopeCounting.PublicNumerals.four PolytopeCounting.PublicNumerals.five PolytopeCounting.PublicNumerals.six
/-- Leading term in Corollary 5.2. -/
def fixedCoreUnlabelledLeading
    (T₀ : ℝ) (h₀ h r tau n : ℕ) : ℝ :=
  T₀ *
    Real.rpow (h - 1 : ℝ) (h₀ - (1 / 2 : ℝ)) /
      (((h₀ - 1).factorial : ℝ) * Real.sqrt (2 * Real.pi) *
        Real.rpow (h - 2 : ℝ) (h₀ + (1 / 2 : ℝ))) *
    Real.rpow (n : ℝ) (-3 / 2 : ℝ) *
    ((((h * r : ℕ) : ℝ) / (tau : ℝ)) *
      Real.rpow (h - 1 : ℝ) (h - 1 : ℝ) /
      Real.rpow (h - 2 : ℝ) (h - 2 : ℝ)) ^ n
end

/-- The parameter-free affine factorial-ratio asymptotic underlying
Corollary 5.1. -/
def TreeAffineStirlingInput (h : ℕ) : Prop :=
  SequenceEquivalent
    (fun n ↦
      ((n * (h - 1)).factorial : ℝ) /
        ((n.factorial : ℝ) * (((h - 2) * n + 2).factorial : ℝ)))
    (fun n ↦
      Real.sqrt (h - 1 : ℝ) /
          (Real.sqrt (2 * Real.pi) *
            Real.rpow (h - 2 : ℝ) (5 / 2 : ℝ)) *
        Real.rpow (n : ℝ) (-5 / 2 : ℝ) *
        (Real.rpow (h - 1 : ℝ) (h - 1 : ℝ) /
          Real.rpow (h - 2 : ℝ) (h - 2 : ℝ)) ^ n)

/-- The parameter-free affine factorial-ratio asymptotic underlying
Corollary 5.2. -/
def FixedCoreAffineStirlingInput (h₀ h : ℕ) : Prop :=
  SequenceEquivalent
    (fun n ↦
      ((n * (h - 1) + h₀ - 1).factorial : ℝ) /
        ((n.factorial : ℝ) * (((h - 2) * n + h₀).factorial : ℝ)))
    (fun n ↦
      Real.rpow (h - 1 : ℝ) (h₀ - (1 / 2 : ℝ)) /
          (Real.sqrt (2 * Real.pi) *
            Real.rpow (h - 2 : ℝ) (h₀ + (1 / 2 : ℝ))) *
        Real.rpow (n : ℝ) (-3 / 2 : ℝ) *
        (Real.rpow (h - 1 : ℝ) (h - 1 : ℝ) /
          Real.rpow (h - 2 : ℝ) (h - 2 : ℝ)) ^ n)

/-- Multiplying both sides of a ratio asymptotic by the same nowhere-zero
sequence preserves it. -/
theorem SequenceEquivalent.mul_same
    {u v A : ℕ → ℝ}
    (hA : ∀ n, A n ≠ 0)
    (h : SequenceEquivalent u v) :
    SequenceEquivalent (fun n ↦ A n * u n) (fun n ↦ A n * v n) := by
  unfold SequenceEquivalent at h ⊢
  have hfun :
      (fun n ↦ (A n * u n) / (A n * v n)) =
        (fun n ↦ u n / v n) := by
    funext n
    by_cases hv : v n = 0
    · simp [hv]
    · field_simp [hA n, hv]
  rw [hfun]
  exact h

/-- Corollary 5.1 from its affine Stirling input. -/
theorem treeUnlabelled_asymptotic
    (h r tau : ℕ) (hh : 3 ≤ h) (hr : 0 < r) (htau : 0 < tau)
    (hStirling : TreeAffineStirlingInput h) :
    SequenceEquivalent
      (fun n ↦ treeUnlabelledExact h r tau n)
      (fun n ↦ treeUnlabelledLeading h r tau n) := by
  let A : ℕ → ℝ := fun n ↦
    (1 / (r : ℝ)) * (((h * r : ℕ) : ℝ) / (tau : ℝ)) ^ n
  have hA : ∀ n, A n ≠ 0 := by
    intro n
    unfold A
    exact mul_ne_zero (one_div_ne_zero (by exact_mod_cast hr.ne'))
      (pow_ne_zero n (div_ne_zero
        (by positivity) (by exact_mod_cast htau.ne')))
  have hmul := SequenceEquivalent.mul_same hA hStirling
  convert hmul using 1
  · funext n
    unfold treeUnlabelledExact A
    ring
  · funext n
    unfold treeUnlabelledLeading A
    rw [show
      (((h * r : ℕ) : ℝ) / (tau : ℝ)) *
          Real.rpow (h - 1 : ℝ) (h - 1 : ℝ) /
          Real.rpow (h - 2 : ℝ) (h - 2 : ℝ) =
        ((((h * r : ℕ) : ℝ) / (tau : ℝ)) *
          (Real.rpow (h - 1 : ℝ) (h - 1 : ℝ) /
            Real.rpow (h - 2 : ℝ) (h - 2 : ℝ))) by ring]
    rw [mul_pow]
    ring

/-- Corollary 5.2 from its affine Stirling input. -/
theorem fixedCoreUnlabelled_asymptotic
    (T₀ : ℝ) (h₀ h r tau : ℕ)
    (hT₀ : T₀ ≠ 0) (hh₀ : 1 ≤ h₀) (hh : 3 ≤ h)
    (hr : 0 < r) (htau : 0 < tau)
    (hStirling : FixedCoreAffineStirlingInput h₀ h) :
    SequenceEquivalent
      (fun n ↦ fixedCoreUnlabelledExact T₀ h₀ h r tau n)
      (fun n ↦ fixedCoreUnlabelledLeading T₀ h₀ h r tau n) := by
  let A : ℕ → ℝ := fun n ↦
    T₀ / ((h₀ - 1).factorial : ℝ) *
      (((h * r : ℕ) : ℝ) / (tau : ℝ)) ^ n
  have hA : ∀ n, A n ≠ 0 := by
    intro n
    unfold A
    have hfac : (((h₀ - 1).factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (h₀ - 1)
    exact mul_ne_zero (div_ne_zero hT₀ hfac)
      (pow_ne_zero n (div_ne_zero
        (by positivity) (by exact_mod_cast htau.ne')))
  have hmul := SequenceEquivalent.mul_same hA hStirling
  convert hmul using 1
  · funext n
    unfold fixedCoreUnlabelledExact A
    ring
  · funext n
    unfold fixedCoreUnlabelledLeading A
    rw [show
      (((h * r : ℕ) : ℝ) / (tau : ℝ)) *
          Real.rpow (h - 1 : ℝ) (h - 1 : ℝ) /
          Real.rpow (h - 2 : ℝ) (h - 2 : ℝ) =
        ((((h * r : ℕ) : ℝ) / (tau : ℝ)) *
          (Real.rpow (h - 1 : ℝ) (h - 1 : ℝ) /
            Real.rpow (h - 2 : ℝ) (h - 2 : ℝ))) by ring]
    rw [mul_pow]
    ring

/-- Tetrahedral boundary-unlabelled groupoid-mass asymptotic as the
orientation-preserving specialization `h=4,r=3,tau=12`. -/
def TetrahedronUnlabelledAsymptotic : Prop :=
  SequenceEquivalent
    (fun n ↦ treeUnlabelledExact 4 3 12 n)
    (fun n ↦ treeUnlabelledLeading 4 3 12 n)


end
end GeneralAsymptotics
end PolytopeCounting
