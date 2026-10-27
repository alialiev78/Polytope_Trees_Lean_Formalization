module

public import Proofs.RecursiveXiPairableCore

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# The complete homogeneous Xi recurrence and its uniqueness theorem

The original module proves the pairable-core recurrence on supported
positive-pair coefficients. This extension includes all boundary and
out-of-support cases, and proves that the factorial expression is the
unique supported solution with the prescribed unpaired coefficient.

These are unconditional algebraic theorems about the explicit model. They
do not identify the actual rooted component family with a convolution.
-/

namespace PolytopeCounting.ExplicitFormulas.RecursiveXi

noncomputable section

/-- Cutting one pair preserves support, in the direction needed to prove
that an unsupported coefficient and its successor are both zero. -/
theorem supported_of_supported_add_two
    {h h₀ n m : ℕ}
    (hs : PairableCoreSupported h h₀ n (m + 2)) :
    PairableCoreSupported h h₀ n m := by
  rcases hs with ⟨ell, hell⟩
  exact ⟨ell + 1, by omega⟩

/-- With zero ports on the distinguished core, the homogeneous Xi
coefficient is exactly the core weight times the existing W formula. -/
theorem pairableCoreXiClosedForm_zero_core
    (h r tau : ℕ) (c : ℚ) (n m : ℕ) :
    pairableCoreXiClosedForm h 0 r tau c n m =
      c * WHatClosedForm h r tau n m := by
  by_cases hs : WSupported h n m
  · obtain ⟨ell, hell⟩ := hs
    have hsub : h * n - ell * 2 = m := by
      have hcomm' : ell * 2 = 2 * ell := Nat.mul_comm ell 2
      omega
    rw [pairableCoreXiClosedForm_eq_of_support
        h 0 r tau c n m ell (by simpa using hell),
      WHatClosedForm_eq_of_support h r tau n m ell hell]
    simp only [Nat.add_zero, disconnectedPairingClosedForm, Nat.mul_comm]
    rw [hsub]
    ring
  · have hs' : ¬ PairableCoreSupported h 0 n m := by
      simpa only [PairableCoreSupported, WSupported, Nat.add_zero] using hs
    rw [pairableCoreXiClosedForm_eq_zero_of_not_supported
      h 0 r tau c n m hs',
      WHatClosedForm_eq_zero_of_not_supported h r tau n m hs]
    simp

/-- Statement (52) on every coefficient, including the unpaired top term
and all parity and range failures. -/
theorem pairableCoreXiClosedForm_recurrence_all
    (h h₀ r tau : ℕ) (c : ℚ) (htau : 0 < tau)
    (n m : ℕ) :
    (((h * n + h₀ : ℕ) : ℚ) - (m : ℚ)) *
        pairableCoreXiClosedForm h h₀ r tau c n m =
      (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        pairableCoreXiClosedForm h h₀ r tau c n (m + 2) := by
  by_cases hs : PairableCoreSupported h h₀ n m
  · rcases hs with ⟨ell, hell⟩
    cases ell with
    | zero =>
      have htop : h * n + h₀ = m := by omega
      have hnext : ¬ PairableCoreSupported h h₀ n (m + 2) := by
        rintro ⟨q, hq⟩
        omega
      rw [pairableCoreXiClosedForm_eq_zero_of_not_supported
        h h₀ r tau c n (m + 2) hnext]
      simp [htop]
    | succ ell =>
      exact pairableCoreXiClosedForm_recurrence
        h h₀ r tau c n m ell htau (by simpa [Nat.succ_eq_add_one] using hell)
  · have hnext : ¬ PairableCoreSupported h h₀ n (m + 2) :=
      fun hnext ↦ hs (supported_of_supported_add_two hnext)
    rw [pairableCoreXiClosedForm_eq_zero_of_not_supported
      h h₀ r tau c n m hs,
      pairableCoreXiClosedForm_eq_zero_of_not_supported
      h h₀ r tau c n (m + 2) hnext]
    simp

/-- Any supported solution of the homogeneous recurrence with the same
unpaired coefficient agrees with (53), coefficient by coefficient.
The proof is induction on the number of pairs, not an assumed solution
certificate or a supplied equivalence. -/
theorem pairableCoreXiClosedForm_unique
    (h h₀ r tau : ℕ) (c : ℚ) (htau : 0 < tau)
    (Xi : ℕ → ℕ → ℚ)
    (hzero : ∀ n m, ¬ PairableCoreSupported h h₀ n m → Xi n m = 0)
    (htop : ∀ n,
      Xi n (h * n + h₀) =
        c * (1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n)))
    (hrec : ∀ n m : ℕ,
      (((h * n + h₀ : ℕ) : ℚ) - (m : ℚ)) * Xi n m =
        (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) * Xi n (m + 2)) :
    Xi = pairableCoreXiClosedForm h h₀ r tau c := by
  have hsupported : ∀ ell n m,
      h * n + h₀ = m + 2 * ell →
      Xi n m = pairableCoreXiClosedForm h h₀ r tau c n m := by
    intro ell
    induction ell with
    | zero =>
      intro n m hm
      have hm' : m = h * n + h₀ := by omega
      rw [hm', htop, pairableCoreXiClosedForm_top]
    | succ ell ih =>
      intro n m hm
      have hnext : h * n + h₀ = (m + 2) + 2 * ell := by omega
      have hsource := hrec n m
      have htarget := pairableCoreXiClosedForm_recurrence_all
        h h₀ r tau c htau n m
      rw [ih n (m + 2) hnext] at hsource
      have hdiff : (((h * n + h₀ : ℕ) : ℚ) - (m : ℚ)) ≠ 0 := by
        have hlt : m < h * n + h₀ := by omega
        have hltQ : (m : ℚ) < ((h * n + h₀ : ℕ) : ℚ) := by
          exact_mod_cast hlt
        linarith
      exact mul_left_cancel₀ hdiff (hsource.trans htarget.symm)
  funext n m
  by_cases hs : PairableCoreSupported h h₀ n m
  · obtain ⟨ell, hell⟩ := hs
    exact hsupported ell n m hell
  · rw [hzero n m hs,
      pairableCoreXiClosedForm_eq_zero_of_not_supported
        h h₀ r tau c n m hs]


end
end PolytopeCounting.ExplicitFormulas.RecursiveXi
