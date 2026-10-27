module

public import Solution
public import Proofs.BinomialIdentities
public import Proofs.ConcreteCoreInitial

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Unconditional binomial consequences in the main text

The four main-text identities (13), (17), (29), and (30) are obtained here
from the actual finite-carrier recurrences and their already proved closed
forms. In particular, `TreeFactorialRecurrenceAt` and
`FixedFactorialRecurrenceAt` are conclusions, not input certificates.

A trivial one-element local symmetry group and one seam colour suffice:
the common nonzero scale is `h^n`. The initial core count `h₀!` is proved in
`ConcreteCoreInitial`. No result from an appendix is added in this module.
-/

namespace PolytopeCounting.BinomialIdentities

open scoped BigOperators

noncomputable section

/-- A one-element local group may act trivially on any number of slots. -/
local instance trivialSlotAction (h : ℕ) : MulAction Unit (Fin h) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

private theorem concrete_R_scaled (h n : ℕ) (hh : 2 ≤ h) (hn : 0 < n) :
    PolytopeTrees.R Unit n h 1 = (h : ℚ) ^ n * treeFactorialTerm h n := by
  simpa [treeFactorialTerm, mul_div_assoc] using
    (PolytopeTrees.R_formula Unit n h 1 hh (by decide) hn)

private theorem concrete_T_scaled (h h₀ n : ℕ)
    (hh : 2 ≤ h) (hbase : 1 ≤ h₀) :
    PolytopeTrees.T Unit n h₀ h 1 =
      (h₀.factorial : ℚ) * (h : ℚ) ^ n * fixedFactorialTerm h₀ h n := by
  have hf := PolytopeTrees.T_formula Unit n h₀ h 1 hh hbase (by decide)
  rw [PolytopeTrees.T_zero] at hf
  simpa [fixedFactorialTerm, mul_div_assoc, mul_assoc] using hf

/-- Factorial recurrence supplied by the genuine tree model. -/
theorem treeFactorialRecurrence (h n : ℕ) (hh : 2 ≤ h) (hn : 2 ≤ n) :
    TreeFactorialRecurrenceAt h n := by
  have hrec := PolytopeTrees.R_recurrence Unit n h 1 hh hn
  rw [concrete_R_scaled h n hh (by omega)] at hrec
  have hsum :
      (∑ k ∈ Finset.Icc 1 (n - 1),
        (Nat.choose ((h - 2) * n + 2) ((h - 2) * k + 1) : ℚ) *
          PolytopeTrees.R Unit k h 1 * PolytopeTrees.R Unit (n - k) h 1) =
      (h : ℚ) ^ n *
        ∑ k ∈ Finset.Icc 1 (n - 1),
          (Nat.choose ((h - 2) * n + 2) ((h - 2) * k + 1) : ℚ) *
            treeFactorialTerm h k * treeFactorialTerm h (n - k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hkpos : 0 < k := by omega
    have hnkpos : 0 < n - k := by omega
    have hadd : k + (n - k) = n := by omega
    rw [concrete_R_scaled h k hh hkpos,
      concrete_R_scaled h (n - k) hh hnkpos]
    calc
      _ = ((h : ℚ) ^ k * (h : ℚ) ^ (n - k)) *
          ((Nat.choose ((h - 2) * n + 2) ((h - 2) * k + 1) : ℚ) *
            treeFactorialTerm h k * treeFactorialTerm h (n - k)) := by ring
      _ = _ := by rw [← pow_add, hadd]
  rw [hsum] at hrec
  have hscale : (h : ℚ) ^ n ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (show h ≠ 0 by omega)
  unfold TreeFactorialRecurrenceAt
  apply mul_left_cancel₀ hscale
  norm_num only [Nat.cast_one] at hrec
  linear_combination 2 * hrec

/-- Factorial recurrence supplied by the genuine rooted tree model. -/
theorem fixedFactorialRecurrence (h h₀ n : ℕ)
    (hh : 2 ≤ h) (hbase : 1 ≤ h₀) (hn : 0 < n) :
    FixedFactorialRecurrenceAt h h₀ n := by
  have hrec := PolytopeTrees.T_recurrence Unit n h₀ h 1 hh hbase hn
  rw [concrete_T_scaled h h₀ n hh hbase] at hrec
  have hsum :
      (∑ k ∈ Finset.range n,
        (Nat.choose ((h - 2) * n + h₀)
          ((h - 2) * (n - k) + 1) : ℚ) *
          PolytopeTrees.T Unit k h₀ h 1 * PolytopeTrees.R Unit (n - k) h 1) =
      ((h₀.factorial : ℚ) * (h : ℚ) ^ n) *
        ∑ k ∈ Finset.range n,
          (Nat.choose ((h - 2) * n + h₀)
            ((h - 2) * (n - k) + 1) : ℚ) *
            fixedFactorialTerm h₀ h k * treeFactorialTerm h (n - k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hadd : k + (n - k) = n := by omega
    rw [concrete_T_scaled h h₀ k hh hbase,
      concrete_R_scaled h (n - k) hh (by omega)]
    calc
      _ = (h₀.factorial : ℚ) * ((h : ℚ) ^ k * (h : ℚ) ^ (n - k)) *
          ((Nat.choose ((h - 2) * n + h₀)
            ((h - 2) * (n - k) + 1) : ℚ) *
            fixedFactorialTerm h₀ h k * treeFactorialTerm h (n - k)) := by ring
      _ = _ := by rw [← pow_add, hadd]
  rw [hsum] at hrec
  have hscale : (h₀.factorial : ℚ) * (h : ℚ) ^ n ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast Nat.factorial_ne_zero h₀
    · apply pow_ne_zero
      exact_mod_cast (show h ≠ 0 by omega)
  unfold FixedFactorialRecurrenceAt
  apply mul_left_cancel₀ hscale
  norm_num only [Nat.cast_one, one_mul] at hrec
  linear_combination hrec

/-- Main-text identity (29), with no recurrence or cardinality hypothesis. -/
theorem identity29 (h n : ℕ) (hh : 2 ≤ h) (hn : 2 ≤ n) :
    Identity29 h n :=
  identity29_of_factorial_recurrence h n hh hn
    (treeFactorialRecurrence h n hh hn)

/-- Main-text identity (30), with no recurrence or cardinality hypothesis. -/
theorem identity30 (h h₀ n : ℕ) (hh : 2 ≤ h) (hbase : 1 ≤ h₀) (hn : 0 < n) :
    Identity30 h h₀ n :=
  identity30_of_factorial_recurrence h h₀ n hh hbase hn
    (fixedFactorialRecurrence h h₀ n hh hbase hn)

/-- Tetrahedral identity (13). -/
theorem identity13 (n : ℕ) (hn : 2 ≤ n) : Identity13 n :=
  identity29 4 n (by decide) hn

/-- Tetrahedral fixed-core identity (17). -/
theorem identity17 (n₀ n : ℕ) (hn₀ : 1 ≤ n₀) (hn : 0 < n) :
    Identity17 n₀ n :=
  identity30 4 (2 * n₀) n (by decide) (by omega) hn

end
end PolytopeCounting.BinomialIdentities
