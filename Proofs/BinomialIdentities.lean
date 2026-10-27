module

public import Proofs.ManuscriptTreeExplicit
public import Proofs.ManuscriptFixedCoreExplicit
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Binomial identities (13), (17), (29), (30), and Appendix E

The identities are the parameter-free forms obtained after substituting the
explicit factorial solutions into the two cut--join recurrences and cancelling
the common scale.  This module records the literal statements, the factorial
ratio used in the cancellation, and the specializations (13) and (17).

The main implication theorems below deliberately take the corresponding
factorial recurrence as a hypothesis.  In the complete project that
hypothesis is supplied by the already formalized cut--join recurrence after
rewriting with the explicit formula.  This separation makes the algebraic
cancellation independently auditable.
-/

namespace PolytopeCounting
namespace BinomialIdentities

open scoped BigOperators

noncomputable section

/-- The factorial sequence occurring after removal of the common factor
`r⁻¹ (hr/tau)^n` from the tree formula. -/
def treeFactorialTerm (h n : ℕ) : ℚ :=
  ((n * (h - 1)).factorial : ℚ) / (n.factorial : ℚ)

/-- The corresponding fixed-core factorial sequence. -/
def fixedFactorialTerm (h₀ h n : ℕ) : ℚ :=
  ((n * (h - 1) + h₀ - 1).factorial : ℚ) /
    (((h₀ - 1).factorial : ℚ) * (n.factorial : ℚ))

/-- Literal identity (29). -/
def Identity29 (h n : ℕ) : Prop :=
  (2 * (n - 1) : ℚ) =
    ∑ k ∈ Finset.Icc 1 (n - 1),
      (Nat.choose ((h - 2) * n + 2) ((h - 2) * k + 1) : ℚ) *
      (Nat.choose n k : ℚ) /
      (Nat.choose (n * (h - 1)) (k * (h - 1)) : ℚ)

/-- Literal identity (30). -/
def Identity30 (h h₀ n : ℕ) : Prop :=
  (Nat.choose (n * (h - 1) + h₀ - 1) (h₀ - 1) : ℚ) =
    (1 / (n : ℚ)) *
      ∑ k ∈ Finset.range n,
        (Nat.choose ((h - 2) * n + h₀)
          ((h - 2) * (n - k) + 1) : ℚ) *
        (Nat.choose (k * (h - 1) + h₀ - 1) (h₀ - 1) : ℚ) *
        (Nat.choose n k : ℚ) /
        (Nat.choose (n * (h - 1)) (k * (h - 1)) : ℚ)

/-- Identity (13) is the tetrahedral specialization of (29). -/
def Identity13 (n : ℕ) : Prop := Identity29 4 n

/-- Identity (17) is the tetrahedral fixed-core specialization of (30),
with the manuscript's `h₀=2n₀`. -/
def Identity17 (n₀ n : ℕ) : Prop := Identity30 4 (2 * n₀) n

@[simp] theorem identity13_iff_identity29 (n : ℕ) :
    Identity13 n ↔ Identity29 4 n := Iff.rfl

@[simp] theorem identity17_iff_identity30 (n₀ n : ℕ) :
    Identity17 n₀ n ↔ Identity30 4 (2 * n₀) n := Iff.rfl

/-- The termwise factorial cancellation behind (29):

`F_k F_{n-k}/F_n = choose n k / choose (a n) (a k)`.
-/
theorem treeFactorial_ratio_eq_choose_ratio
    (a n k : ℕ) (ha : 1 ≤ a) (hk : k ≤ n) :
    ( (((a * k).factorial : ℚ) / (k.factorial : ℚ)) *
      (((a * (n - k)).factorial : ℚ) /
        ((n - k).factorial : ℚ)) ) /
      (((a * n).factorial : ℚ) / (n.factorial : ℚ)) =
    (Nat.choose n k : ℚ) /
      (Nat.choose (a * n) (a * k) : ℚ) := by
  have hak : a * k ≤ a * n := Nat.mul_le_mul_left a hk
  have hsub : a * n - a * k = a * (n - k) := by
    exact (Nat.mul_sub_left_distrib a n k).symm
  have hnChoose := Nat.choose_mul_factorial_mul_factorial hk
  have haChoose := Nat.choose_mul_factorial_mul_factorial hak
  have hnChooseQ :
      (Nat.choose n k : ℚ) * (k.factorial : ℚ) *
          ((n - k).factorial : ℚ) = (n.factorial : ℚ) := by
    exact_mod_cast hnChoose
  have haChooseQ :
      (Nat.choose (a * n) (a * k) : ℚ) *
          ((a * k).factorial : ℚ) *
          ((a * n - a * k).factorial : ℚ) =
        ((a * n).factorial : ℚ) := by
    exact_mod_cast haChoose
  rw [hsub] at haChooseQ
  have hkf : (k.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hnkf : ((n - k).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - k)
  have hakf : ((a * k).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (a * k)
  have hankf : ((a * (n - k)).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (a * (n - k))
  have hanf : ((a * n).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (a * n)
  have hnChoose0 : (Nat.choose n k : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hk
  have haChoose0 : (Nat.choose (a * n) (a * k) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hak
  field_simp [hkf, hnkf, hakf, hankf, hanf, hnChoose0, haChoose0]
  nlinarith [hnChooseQ, haChooseQ]

/-- Factorial-form recurrence obtained by direct substitution into (18). -/
def TreeFactorialRecurrenceAt (h n : ℕ) : Prop :=
  (2 : ℚ) * ((n - 1 : ℕ) : ℚ) * treeFactorialTerm h n =
    ∑ k ∈ Finset.Icc 1 (n - 1),
      (Nat.choose ((h - 2) * n + 2) ((h - 2) * k + 1) : ℚ) *
      treeFactorialTerm h k * treeFactorialTerm h (n - k)

/-- Substitution into the tree recurrence gives identity (29). -/
theorem identity29_of_factorial_recurrence
    (h n : ℕ) (hh : 2 ≤ h) (hn : 2 ≤ n)
    (hrec : TreeFactorialRecurrenceAt h n) :
    Identity29 h n := by
  unfold TreeFactorialRecurrenceAt at hrec
  unfold Identity29
  have hFn : treeFactorialTerm h n ≠ 0 := by
    unfold treeFactorialTerm
    exact div_ne_zero
      (by exact_mod_cast Nat.factorial_ne_zero (n * (h - 1)))
      (by exact_mod_cast Nat.factorial_ne_zero n)
  have hdiv := congrArg (fun x : ℚ => x / treeFactorialTerm h n) hrec
  rw [Finset.sum_div] at hdiv
  have hleft :
      ((2 : ℚ) * ((n - 1 : ℕ) : ℚ) * treeFactorialTerm h n) /
          treeFactorialTerm h n =
        (2 * (n - 1) : ℚ) := by
    rw [Nat.cast_sub (by omega)]
    field_simp [hFn]
    ring
  rw [hleft] at hdiv
  rw [hdiv]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  have hk' : k ≤ n := by omega
  have hratio := treeFactorial_ratio_eq_choose_ratio
    (h - 1) n k (by omega) hk'
  unfold treeFactorialTerm at hratio ⊢
  simp only [Nat.mul_comm] at hratio ⊢
  linear_combination
    (Nat.choose (n * (h - 2) + 2) (k * (h - 2) + 1) : ℚ) * hratio

/-- Factorial-form recurrence obtained by direct substitution into (24). -/
def FixedFactorialRecurrenceAt (h h₀ n : ℕ) : Prop :=
  (n : ℚ) * fixedFactorialTerm h₀ h n =
    ∑ k ∈ Finset.range n,
      (Nat.choose ((h - 2) * n + h₀)
        ((h - 2) * (n - k) + 1) : ℚ) *
      fixedFactorialTerm h₀ h k * treeFactorialTerm h (n - k)


/-- The fixed-core factorial term is the tree factorial term multiplied by
its pointing binomial coefficient. -/
theorem fixedFactorialTerm_eq_tree_mul_choose
    (h h₀ n : ℕ) (hbase : 1 ≤ h₀) :
    fixedFactorialTerm h₀ h n =
      treeFactorialTerm h n *
        (Nat.choose (n * (h - 1) + h₀ - 1) (h₀ - 1) : ℚ) := by
  let N := n * (h - 1) + h₀ - 1
  let K := h₀ - 1
  have hK : K ≤ N := by
    dsimp [N, K]
    omega
  have hsub : N - K = n * (h - 1) := by
    dsimp [N, K]
    omega
  have hcNat := Nat.choose_mul_factorial_mul_factorial hK
  have hcQ :
      (Nat.choose N K : ℚ) * (K.factorial : ℚ) *
          ((N - K).factorial : ℚ) = (N.factorial : ℚ) := by
    exact_mod_cast hcNat
  rw [hsub] at hcQ
  have hkf : (K.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero K
  have hanf : ((n * (h - 1)).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n * (h - 1))
  have hnf : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  unfold fixedFactorialTerm treeFactorialTerm
  change
    (N.factorial : ℚ) / ((K.factorial : ℚ) * (n.factorial : ℚ)) =
      ((n * (h - 1)).factorial : ℚ) / (n.factorial : ℚ) *
        (Nat.choose N K : ℚ)
  field_simp [hkf, hanf, hnf]
  nlinarith [hcQ]

/-- Substitution into the fixed-core recurrence gives identity (30). -/
theorem identity30_of_factorial_recurrence
    (h h₀ n : ℕ) (hh : 2 ≤ h) (hbase : 1 ≤ h₀) (hn : 0 < n)
    (hrec : FixedFactorialRecurrenceAt h h₀ n) :
    Identity30 h h₀ n := by
  unfold FixedFactorialRecurrenceAt at hrec
  unfold Identity30
  have hFn : treeFactorialTerm h n ≠ 0 := by
    unfold treeFactorialTerm
    exact div_ne_zero
      (by exact_mod_cast Nat.factorial_ne_zero (n * (h - 1)))
      (by exact_mod_cast Nat.factorial_ne_zero n)
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hGn := fixedFactorialTerm_eq_tree_mul_choose h h₀ n hbase
  rw [hGn] at hrec
  have hdiv := congrArg (fun x : ℚ => x / treeFactorialTerm h n) hrec
  rw [Finset.sum_div] at hdiv
  have hleft :
      ((n : ℚ) *
          (treeFactorialTerm h n *
            (Nat.choose (n * (h - 1) + h₀ - 1) (h₀ - 1) : ℚ))) /
          treeFactorialTerm h n =
        (n : ℚ) *
          (Nat.choose (n * (h - 1) + h₀ - 1) (h₀ - 1) : ℚ) := by
    field_simp [hFn]
  rw [hleft] at hdiv
  have hsum :
      (∑ k ∈ Finset.range n,
        (Nat.choose ((h - 2) * n + h₀)
          ((h - 2) * (n - k) + 1) : ℚ) *
        (Nat.choose (k * (h - 1) + h₀ - 1) (h₀ - 1) : ℚ) *
        (Nat.choose n k : ℚ) /
        (Nat.choose (n * (h - 1)) (k * (h - 1)) : ℚ)) =
      (n : ℚ) *
        (Nat.choose (n * (h - 1) + h₀ - 1) (h₀ - 1) : ℚ) := by
    rw [hdiv]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hk' : k ≤ n := Nat.le_of_lt hk
    have hGk := fixedFactorialTerm_eq_tree_mul_choose h h₀ k hbase
    have hratio := treeFactorial_ratio_eq_choose_ratio
      (h - 1) n k (by omega) hk'
    rw [hGk]
    unfold treeFactorialTerm at hratio ⊢
    simp only [Nat.mul_comm] at hratio ⊢
    linear_combination
      -((Nat.choose (n * (h - 2) + h₀)
          ((n - k) * (h - 2) + 1) : ℚ) *
        (Nat.choose (k * (h - 1) + h₀ - 1) (h₀ - 1) : ℚ)) * hratio
  rw [hsum]
  field_simp [hnQ]

/-- Statement of Appendix E.  Its proof is the Pascal symmetrization of the
`h₀=1` case of (30); the definition is kept explicit for audit/navigation. -/
def AppendixEStatement : Prop :=
  ∀ h n, 2 ≤ h → 2 ≤ n → Identity30 h 1 n → Identity29 h n


end
end BinomialIdentities
end PolytopeCounting
