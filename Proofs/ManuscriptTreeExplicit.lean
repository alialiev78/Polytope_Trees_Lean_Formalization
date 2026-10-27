module

public import Proofs.AuxiliaryRecurrenceSolution
public import Proofs.UnconditionalFinalRecurrences
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Explicit solution of the manuscript tree recurrence

This module starts with the literal recurrence of Statements 3.1 and
5.1 (with `q=h-2`), performs the factorial normalization from Appendix B,
derives the scaled Raney equation through `AuxiliaryRecurrenceSolution`, and
then removes the normalization.

The final public theorems are:

* `paper_tree_closed_form`: the solution in terms of its first normalized
  coefficient;
* `manuscript_tree_closed_form`: formula (20), using `R₁=h!/tau`;
* `tetrahedron_tree_closed_form`: Theorem 3.3.

No analytic convergence or radical formula is used.
-/

namespace PolytopeCounting
namespace ExplicitFormulas

open scoped BigOperators

noncomputable section

/-- The recurrence printed in Statement 5.1, with `h-2` kept explicit in
all boundary sizes.  The coefficient type is `ℚ`, which is the natural
codomain of groupoid cardinality. -/
def SatisfiesPaperTreeRecurrence
    (h : ℕ) (r : ℚ) (R : ℕ → ℚ) : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (((n - 1 : ℕ) : ℚ) * R n) =
      (r / 2) *
        ∑ k ∈ Finset.Icc 1 (n - 1),
          (Nat.choose ((h - 2) * n + 2) ((h - 2) * k + 1) : ℚ) *
            R k * R (n - k)

/-- The normalization `a_n=r R_n/(((h-2)n+1)!)` used to pass from the
manuscript recurrence to the Raney recurrence. -/
def normalizedTreeCoefficient
    (h : ℕ) (r : ℚ) (R : ℕ → ℚ) (n : ℕ) : ℚ :=
  r * R n / ((((h - 2) * n + 1).factorial : ℕ) : ℚ)

/-- The binomial/factorial cancellation at one proper split. -/
private theorem boundary_choose_div_factorial
    (q n k : ℕ) (hn : 2 ≤ n)
    (hk : k ∈ Finset.Icc 1 (n - 1)) :
    (Nat.choose (q * n + 2) (q * k + 1) : ℚ) /
        (((q * n + 1).factorial : ℕ) : ℚ) =
      ((q * n + 2 : ℕ) : ℚ) /
        ((((q * k + 1).factorial : ℕ) : ℚ) *
          (((q * (n - k) + 1).factorial : ℕ) : ℚ)) := by
  rw [Finset.mem_Icc] at hk
  have hkn : k ≤ n := by omega
  have hsle : q * k + 1 ≤ q * n + 2 := by
    have hmul : q * k ≤ q * n := Nat.mul_le_mul_left q hkn
    omega
  have hsub : q * n + 2 - (q * k + 1) = q * (n - k) + 1 := by
    rw [Nat.mul_sub_left_distrib]
    have hmul : q * k ≤ q * n := Nat.mul_le_mul_left q hkn
    omega
  have hchooseNat :=
    Nat.choose_mul_factorial_mul_factorial hsle
  have hchooseQ :
      (Nat.choose (q * n + 2) (q * k + 1) : ℚ) *
          (((q * k + 1).factorial : ℕ) : ℚ) *
          ((((q * n + 2) - (q * k + 1)).factorial : ℕ) : ℚ) =
        (((q * n + 2).factorial : ℕ) : ℚ) := by
    exact_mod_cast hchooseNat
  rw [hsub] at hchooseQ
  have hMpos : 0 < q * n + 2 := by omega
  have hfacNat :
      (q * n + 2) * (q * n + 1).factorial =
        (q * n + 2).factorial := by
    simpa using Nat.mul_factorial_pred hMpos.ne'
  have hfacQ :
      ((q * n + 2 : ℕ) : ℚ) *
          (((q * n + 1).factorial : ℕ) : ℚ) =
        (((q * n + 2).factorial : ℕ) : ℚ) := by
    exact_mod_cast hfacNat
  have hpred : ((((q * n + 1).factorial : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (q * n + 1)
  have hkfac : ((((q * k + 1).factorial : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (q * k + 1)
  have hrestfac :
      ((((q * (n - k) + 1).factorial : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (q * (n - k) + 1)
  apply (div_eq_div_iff hpred (mul_ne_zero hkfac hrestfac)).2
  calc
    (Nat.choose (q * n + 2) (q * k + 1) : ℚ) *
        ((((q * k + 1).factorial : ℕ) : ℚ) *
          (((q * (n - k) + 1).factorial : ℕ) : ℚ)) =
      (((q * n + 2).factorial : ℕ) : ℚ) := by
        simpa [mul_assoc] using hchooseQ
    _ = ((q * n + 2 : ℕ) : ℚ) *
        (((q * n + 1).factorial : ℕ) : ℚ) := hfacQ.symm

/-- The literal paper recurrence implies the division-free normalized
recurrence solved in `AuxiliaryRecurrenceSolution`. -/
theorem normalized_recurrence_of_paper_recurrence
    (h : ℕ) (r : ℚ) (R : ℕ → ℚ)
    (hrec : SatisfiesPaperTreeRecurrence h r R) :
    SatisfiesAuxiliaryTreeRecurrence (h - 2)
      (normalizedTreeCoefficient h r R) := by
  intro n hn
  have hp := hrec n hn
  let q : ℕ := h - 2
  let F : ℚ := (((q * n + 1).factorial : ℕ) : ℚ)
  let M : ℚ := ((q * n + 2 : ℕ) : ℚ)
  have hterm : ∀ k ∈ Finset.Icc 1 (n - 1),
      ((2 : ℚ) * r / F) *
          ((r / 2) *
            ((Nat.choose (q * n + 2) (q * k + 1) : ℚ) *
              R k * R (n - k))) =
        M *
          (normalizedTreeCoefficient h r R k *
            normalizedTreeCoefficient h r R (n - k)) := by
    intro k hk
    have hchoose := boundary_choose_div_factorial q n k hn hk
    dsimp [q, F, M] at hchoose ⊢
    unfold normalizedTreeCoefficient
    calc
      (2 * r / (((((h - 2) * n + 1).factorial : ℕ) : ℚ))) *
          (r / 2 *
            ((Nat.choose ((h - 2) * n + 2) ((h - 2) * k + 1) : ℚ) *
              R k * R (n - k))) =
        r ^ 2 *
          ((Nat.choose ((h - 2) * n + 2) ((h - 2) * k + 1) : ℚ) /
            (((((h - 2) * n + 1).factorial : ℕ) : ℚ))) *
          R k * R (n - k) := by ring
      _ = ((h - 2) * n + 2 : ℕ) *
          (r * R k / (((((h - 2) * k + 1).factorial : ℕ) : ℚ)) *
            (r * R (n - k) /
              (((((h - 2) * (n - k) + 1).factorial : ℕ) : ℚ)))) := by
        rw [hchoose]
        ring
  have hsum :
      (((2 : ℚ) * r /
          (((((h - 2) * n + 1).factorial : ℕ) : ℚ))) * (r / 2)) *
          (∑ k ∈ Finset.Icc 1 (n - 1),
            (Nat.choose ((h - 2) * n + 2)
                ((h - 2) * k + 1) : ℚ) *
              R k * R (n - k)) =
        (((h - 2) * n + 2 : ℕ) : ℚ) *
          (∑ k ∈ Finset.Icc 1 (n - 1),
            normalizedTreeCoefficient h r R k *
              normalizedTreeCoefficient h r R (n - k)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      (((2 : ℚ) * r /
          (((((h - 2) * n + 1).factorial : ℕ) : ℚ))) * (r / 2)) *
          ((Nat.choose ((h - 2) * n + 2)
              ((h - 2) * k + 1) : ℚ) * R k * R (n - k)) =
        (((2 : ℚ) * r /
          (((((h - 2) * n + 1).factorial : ℕ) : ℚ))) *
          ((r / 2) *
            ((Nat.choose ((h - 2) * n + 2)
                ((h - 2) * k + 1) : ℚ) * R k * R (n - k)))) := by ring
      _ = (((h - 2) * n + 2 : ℕ) : ℚ) *
          (normalizedTreeCoefficient h r R k *
            normalizedTreeCoefficient h r R (n - k)) := by
        simpa [q, F, M] using hterm k hk
  change
    (2 : ℚ) * (((n - 1 : ℕ) : ℚ)) *
        normalizedTreeCoefficient h r R n =
      (((h - 2) * n + 2 : ℕ) : ℚ) *
        properConvolution (normalizedTreeCoefficient h r R) n
  unfold properConvolution
  calc
    (2 : ℚ) * (((n - 1 : ℕ) : ℚ)) *
        normalizedTreeCoefficient h r R n =
      ((2 : ℚ) * r /
          (((((h - 2) * n + 1).factorial : ℕ) : ℚ))) *
        ((((n - 1 : ℕ) : ℚ)) * R n) := by
          unfold normalizedTreeCoefficient
          ring
    _ = ((2 : ℚ) * r /
          (((((h - 2) * n + 1).factorial : ℕ) : ℚ))) *
        ((r / 2) *
          ∑ k ∈ Finset.Icc 1 (n - 1),
            (Nat.choose ((h - 2) * n + 2)
                ((h - 2) * k + 1) : ℚ) *
              R k * R (n - k)) := by rw [hp]
    _ = (((2 : ℚ) * r /
          (((((h - 2) * n + 1).factorial : ℕ) : ℚ))) * (r / 2)) *
          (∑ k ∈ Finset.Icc 1 (n - 1),
            (Nat.choose ((h - 2) * n + 2)
                ((h - 2) * k + 1) : ℚ) *
              R k * R (n - k)) := by ring
    _ = (((h - 2) * n + 2 : ℕ) : ℚ) *
        ∑ k ∈ Finset.Icc 1 (n - 1),
          normalizedTreeCoefficient h r R k *
            normalizedTreeCoefficient h r R (n - k) := hsum

/-- The paper recurrence has the closed solution determined by its first
normalized coefficient. -/
theorem paper_tree_closed_form
    (h : ℕ) (r : ℚ) (R : ℕ → ℚ)
    (hh : 2 ≤ h) (hr : r ≠ 0)
    (hrec : SatisfiesPaperTreeRecurrence h r R)
    (hfirst : normalizedTreeCoefficient h r R 1 ≠ 0)
    (n : ℕ) (hn : 0 < n) :
    R n = treeClosedForm h r
      (normalizedTreeCoefficient h r R 1) n := by
  let a : ℕ → ℚ := normalizedTreeCoefficient h r R
  let A : PowerSeries ℚ := auxiliarySeries a
  have harec : SatisfiesAuxiliaryTreeRecurrence (h - 2) a := by
    dsimp [a]
    exact normalized_recurrence_of_paper_recurrence h r R hrec
  have hA0 := functional_equation_of_auxiliary_recurrence (h - 2) a harec
  have hexp : (h - 2) + 1 = h - 1 := by omega
  rw [hexp] at hA0
  have hclosed := treeCountFromAux_eq_closedForm
    A h n r (a 1) hh hr hfirst hA0
  have hfac :
      (((((h - 2) * n + 1).factorial : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero ((h - 2) * n + 1)
  have hleft : treeCountFromAux A h r n = R n := by
    unfold treeCountFromAux
    rw [show PowerSeries.coeff n A = a n by
      exact coeff_auxiliarySeries_of_pos a hn]
    dsimp [a, normalizedTreeCoefficient]
    field_simp [hr, hfac]
  exact hleft.symm.trans hclosed

/-- Formula (20) of the manuscript. -/
theorem manuscript_tree_closed_form
    (h r tau : ℕ) (R : ℕ → ℚ)
    (hh : 2 ≤ h) (hr : 0 < r) (htau : 0 < tau)
    (hrec : SatisfiesPaperTreeRecurrence h (r : ℚ) R)
    (hR1 : R 1 = (h.factorial : ℚ) / (tau : ℚ))
    (n : ℕ) (hn : 0 < n) :
    R n = manuscriptTreeClosedForm h r tau n := by
  have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have htauQ : (tau : ℚ) ≠ 0 := by exact_mod_cast htau.ne'
  have hfacNat : h * (h - 1).factorial = h.factorial :=
    Nat.mul_factorial_pred (by omega)
  have hfacQ :
      (h : ℚ) * (((h - 1).factorial : ℕ) : ℚ) =
        (h.factorial : ℚ) := by
    exact_mod_cast hfacNat
  have hpred : ((((h - 1).factorial : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (h - 1)
  have hboundary : (h - 2) * 1 + 1 = h - 1 := by omega
  have hfirst :
      normalizedTreeCoefficient h (r : ℚ) R 1 =
        geometricScale h r tau := by
    unfold normalizedTreeCoefficient geometricScale
    rw [hR1, hboundary]
    field_simp [htauQ, hpred]
    rw [← hfacQ]
    push_cast
    ring
  have hfirstNe : normalizedTreeCoefficient h (r : ℚ) R 1 ≠ 0 := by
    rw [hfirst]
    unfold geometricScale
    have hhpos : 0 < h := by omega
    positivity
  have hmain := paper_tree_closed_form h (r : ℚ) R hh hrQ hrec
    hfirstNe n hn
  unfold manuscriptTreeClosedForm
  rwa [hfirst] at hmain

/-- Theorem 3.3: the tetrahedral specialization. -/
theorem tetrahedron_tree_closed_form
    (R : ℕ → ℚ)
    (hrec : SatisfiesPaperTreeRecurrence 4 3 R)
    (hR1 : R 1 = 2)
    (n : ℕ) (hn : 0 < n) :
    R n = ((3 * n).factorial : ℚ) /
      (3 * (n.factorial : ℚ)) := by
  have hR1' : R 1 = (Nat.factorial 4 : ℚ) / (12 : ℚ) := by
    norm_num at hR1 ⊢
    exact hR1
  have hmain := manuscript_tree_closed_form 4 3 12 R
    (by omega) (by omega) (by omega) hrec hR1' n hn
  rw [tetrahedron_closed_form] at hmain
  exact hmain


end
end ExplicitFormulas
end PolytopeCounting
