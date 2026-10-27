module

public import Proofs.AuxiliaryFixedCoreSolution
public import Proofs.MassTreeExplicit
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Explicit solution of the manuscript fixed-core recurrence

This file formalizes the second main coefficient formula.  It converts the
literal binomial recurrence of Statements 4.1 and 5.2 to the triangular
normalized recurrence solved in `AuxiliaryFixedCoreSolution`, identifies its
solution with a scalar multiple of `A^h₀`, and then applies the scaled
Lagrange--Bürmann/Raney coefficient theorem.
-/

namespace PolytopeCounting
namespace ExplicitFormulas

open scoped BigOperators

noncomputable section

/-- The fixed-core recurrence (24)/(25), with `q=h-2`. -/
def SatisfiesPaperFixedCoreRecurrence
    (h h₀ : ℕ) (r : ℚ) (R T : ℕ → ℚ) : Prop :=
  ∀ n : ℕ, 0 < n →
    (n : ℚ) * T n =
      r * ∑ k ∈ Finset.range n,
        (Nat.choose ((h - 2) * n + h₀)
            ((h - 2) * (n - k) + 1) : ℚ) *
          T k * R (n - k)

/-- Boundary-factorial normalization for the fixed-core sequence. -/
def normalizedFixedCoreCoefficient
    (h h₀ : ℕ) (T : ℕ → ℚ) (n : ℕ) : ℚ :=
  T n / (((((h - 2) * n + h₀).factorial : ℕ) : ℚ))

/-- Factorial cancellation in one fixed-core summand. -/
private theorem fixed_choose_div_factorial
    (q h₀ n k : ℕ) (hbase : 1 ≤ h₀)
    (hk : k ∈ Finset.range n) :
    (Nat.choose (q * n + h₀) (q * (n - k) + 1) : ℚ) /
        (((q * n + h₀).factorial : ℕ) : ℚ) =
      1 /
        ((((q * (n - k) + 1).factorial : ℕ) : ℚ) *
          (((q * k + h₀ - 1).factorial : ℕ) : ℚ)) := by
  rw [Finset.mem_range] at hk
  have hkn : k ≤ n := by omega
  have hsplit : n = k + (n - k) := by omega
  have hsle : q * (n - k) + 1 ≤ q * n + h₀ := by
    have hmul : q * (n - k) ≤ q * n :=
      Nat.mul_le_mul_left q (Nat.sub_le n k)
    omega
  have hsub :
      q * n + h₀ - (q * (n - k) + 1) = q * k + h₀ - 1 := by
    have hmul : q * n = q * k + q * (n - k) := by
      calc
        q * n = q * (k + (n - k)) := by rw [← hsplit]
        _ = q * k + q * (n - k) := by rw [Nat.mul_add]
    rw [hmul]
    omega
  have hchooseNat :=
    Nat.choose_mul_factorial_mul_factorial hsle
  have hchooseQ :
      (Nat.choose (q * n + h₀) (q * (n - k) + 1) : ℚ) *
          (((q * (n - k) + 1).factorial : ℕ) : ℚ) *
          ((((q * n + h₀) - (q * (n - k) + 1)).factorial : ℕ) : ℚ) =
        (((q * n + h₀).factorial : ℕ) : ℚ) := by
    exact_mod_cast hchooseNat
  rw [hsub] at hchooseQ
  have hMfac : ((((q * n + h₀).factorial : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (q * n + h₀)
  have hsfac : ((((q * (n - k) + 1).factorial : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (q * (n - k) + 1)
  have htB : ((((q * k + h₀ - 1).factorial : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (q * k + h₀ - 1)
  apply (div_eq_div_iff hMfac (mul_ne_zero hsfac htB)).2
  simpa [mul_assoc] using hchooseQ

/-- The literal fixed-core recurrence becomes the normalized triangular
recurrence. -/
theorem normalized_fixed_recurrence_of_paper
    (h h₀ : ℕ) (r : ℚ) (R T : ℕ → ℚ)
    (hh : 2 ≤ h) (hbase : 1 ≤ h₀)
    (hrec : SatisfiesPaperFixedCoreRecurrence h h₀ r R T) :
    SatisfiesAuxiliaryFixedRecurrence (h - 2) h₀
      (normalizedTreeCoefficient h r R)
      (normalizedFixedCoreCoefficient h h₀ T) := by
  intro n hn
  have hp := hrec n hn
  let q : ℕ := h - 2
  have hterm : ∀ k ∈ Finset.range n,
      (r /
          (((q * n + h₀).factorial : ℕ) : ℚ)) *
        ((Nat.choose (q * n + h₀) (q * (n - k) + 1) : ℚ) *
          T k * R (n - k)) =
      (((q * k + h₀ : ℕ) : ℚ)) *
        normalizedFixedCoreCoefficient h h₀ T k *
        normalizedTreeCoefficient h r R (n - k) := by
    intro k hk
    have hchoose := fixed_choose_div_factorial q h₀ n k hbase hk
    have hBpos : 0 < q * k + h₀ := by omega
    have hfacNat :
        (q * k + h₀) * (q * k + h₀ - 1).factorial =
          (q * k + h₀).factorial :=
      Nat.mul_factorial_pred hBpos.ne'
    have hfacQ :
        ((q * k + h₀ : ℕ) : ℚ) *
            (((q * k + h₀ - 1).factorial : ℕ) : ℚ) =
          (((q * k + h₀).factorial : ℕ) : ℚ) := by
      exact_mod_cast hfacNat
    dsimp [q] at hchoose hfacQ ⊢
    unfold normalizedFixedCoreCoefficient normalizedTreeCoefficient
    have hden1 :
        (((((h - 2) * k + h₀).factorial : ℕ) : ℚ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero ((h - 2) * k + h₀)
    have hden2 :
        (((((h - 2) * (n - k) + 1).factorial : ℕ) : ℚ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero ((h - 2) * (n - k) + 1)
    have hpred :
        (((((h - 2) * k + h₀ - 1).factorial : ℕ) : ℚ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero ((h - 2) * k + h₀ - 1)
    calc
      (r / (((((h - 2) * n + h₀).factorial : ℕ) : ℚ))) *
          ((Nat.choose ((h - 2) * n + h₀)
              ((h - 2) * (n - k) + 1) : ℚ) * T k * R (n - k)) =
        r *
          ((Nat.choose ((h - 2) * n + h₀)
              ((h - 2) * (n - k) + 1) : ℚ) /
            (((((h - 2) * n + h₀).factorial : ℕ) : ℚ))) *
          T k * R (n - k) := by ring
      _ = r *
          (1 /
            (((((h - 2) * (n - k) + 1).factorial : ℕ) : ℚ) *
              (((((h - 2) * k + h₀ - 1).factorial : ℕ) : ℚ)))) *
          T k * R (n - k) := by rw [hchoose]
      _ = (((h - 2) * k + h₀ : ℕ) : ℚ) *
          (T k / (((((h - 2) * k + h₀).factorial : ℕ) : ℚ))) *
          (r * R (n - k) /
            (((((h - 2) * (n - k) + 1).factorial : ℕ) : ℚ))) := by
        field_simp [hden1, hden2, hpred]
        rw [← hfacQ]
        ring
  have hsum :
      (r /
          (((((h - 2) * n + h₀).factorial : ℕ) : ℚ))) *
        (∑ k ∈ Finset.range n,
          (Nat.choose ((h - 2) * n + h₀)
              ((h - 2) * (n - k) + 1) : ℚ) *
            T k * R (n - k)) =
      ∑ k ∈ Finset.range n,
        ((((h - 2) * k + h₀ : ℕ) : ℚ)) *
          normalizedFixedCoreCoefficient h h₀ T k *
          normalizedTreeCoefficient h r R (n - k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm k hk
  change
    (n : ℚ) * normalizedFixedCoreCoefficient h h₀ T n =
      ∑ k ∈ Finset.range n,
        ((((h - 2) * k + h₀ : ℕ) : ℚ)) *
          normalizedFixedCoreCoefficient h h₀ T k *
          normalizedTreeCoefficient h r R (n - k)
  calc
    (n : ℚ) * normalizedFixedCoreCoefficient h h₀ T n =
      1 /
          (((((h - 2) * n + h₀).factorial : ℕ) : ℚ)) *
        ((n : ℚ) * T n) := by
      unfold normalizedFixedCoreCoefficient
      ring
    _ = 1 /
          (((((h - 2) * n + h₀).factorial : ℕ) : ℚ)) *
        (r * ∑ k ∈ Finset.range n,
          (Nat.choose ((h - 2) * n + h₀)
              ((h - 2) * (n - k) + 1) : ℚ) *
            T k * R (n - k)) := by rw [hp]
    _ = r /
          (((((h - 2) * n + h₀).factorial : ℕ) : ℚ)) *
        (∑ k ∈ Finset.range n,
          (Nat.choose ((h - 2) * n + h₀)
              ((h - 2) * (n - k) + 1) : ℚ) *
            T k * R (n - k)) := by ring
    _ = ∑ k ∈ Finset.range n,
        ((((h - 2) * k + h₀ : ℕ) : ℚ)) *
          normalizedFixedCoreCoefficient h h₀ T k *
          normalizedTreeCoefficient h r R (n - k) := hsum

/-- The fixed-core recurrence has the closed solution determined by `T_0`
and the first normalized tree coefficient. -/
theorem paper_fixed_core_closed_form
    (h h₀ : ℕ) (r : ℚ) (R T : ℕ → ℚ)
    (hh : 2 ≤ h) (hbase : 1 ≤ h₀) (hr : r ≠ 0)
    (hRrec : SatisfiesPaperTreeRecurrence h r R)
    (hTrec : SatisfiesPaperFixedCoreRecurrence h h₀ r R T)
    (hfirst : normalizedTreeCoefficient h r R 1 ≠ 0)
    (n : ℕ) :
    T n = fixedCoreClosedForm (T 0) h₀ h
      (normalizedTreeCoefficient h r R 1) n := by
  let a : ℕ → ℚ := normalizedTreeCoefficient h r R
  let u : ℕ → ℚ := normalizedFixedCoreCoefficient h h₀ T
  let A : PowerSeries ℚ := auxiliarySeries a
  have harec : SatisfiesAuxiliaryTreeRecurrence (h - 2) a := by
    dsimp [a]
    exact normalized_recurrence_of_paper_recurrence h r R hRrec
  have hurec : SatisfiesAuxiliaryFixedRecurrence (h - 2) h₀ a u := by
    dsimp [a, u]
    exact normalized_fixed_recurrence_of_paper h h₀ r R T
      hh hbase hTrec
  have hA0 := functional_equation_of_auxiliary_recurrence (h - 2) a harec
  have hexp : (h - 2) + 1 = h - 1 := by omega
  rw [hexp] at hA0
  have hcand := fixedAuxiliaryCoefficient_recurrence
    A (a 1) (u 0) (h - 2) h₀ hbase (by
      rw [hexp]
      exact hA0)
  have hzero : u 0 = fixedAuxiliaryCoefficient A (u 0) h₀ 0 := by
    unfold fixedAuxiliaryCoefficient
    have hconst : PowerSeries.constantCoeff A = 1 := by
      dsimp [A]
      simp
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hconst]
  have hurecA :
      SatisfiesAuxiliaryFixedRecurrence (h - 2) h₀
        (fun j => PowerSeries.coeff j A) u := by
    intro m hm
    calc
      (m : ℚ) * u m =
          ∑ k ∈ Finset.range m,
            ((((h - 2) * k + h₀ : ℕ) : ℚ)) * u k * a (m - k) :=
        hurec m hm
      _ = ∑ k ∈ Finset.range m,
            ((((h - 2) * k + h₀ : ℕ) : ℚ)) * u k *
              PowerSeries.coeff (m - k) A := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        have hmk : 0 < m - k := by omega
        dsimp [A]
        rw [coeff_auxiliarySeries_of_pos a hmk]
  have heq := auxiliary_fixed_recurrence_unique
    (h - 2) h₀ (fun j => PowerSeries.coeff j A)
    u (fixedAuxiliaryCoefficient A (u 0) h₀)
    hurecA hcand hzero n
  have hboundary : (h - 2) * 0 + h₀ = h₀ := by omega
  have hu0 : u 0 = T 0 / (h₀.factorial : ℚ) := by
    dsimp [u, normalizedFixedCoreCoefficient]
    simp
  rw [hu0] at heq
  have hfac :
      (((((h - 2) * n + h₀).factorial : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero ((h - 2) * n + h₀)
  have hleft :
      fixedCoreCountFromAux A (T 0) h₀ h n = T n := by
    unfold fixedCoreCountFromAux
    unfold fixedAuxiliaryCoefficient at heq
    dsimp [u, normalizedFixedCoreCoefficient] at heq
    field_simp [hfac] at heq ⊢
    linear_combination (-1) * heq
  have hclosed := fixedCoreCountFromAux_eq_closedForm
    A (T 0) (a 1) h₀ h n hh hbase hfirst hA0
  exact hleft.symm.trans hclosed

/-- Formula (27), using `R_1=h!/tau`. -/
theorem manuscript_fixed_core_closed_form
    (h h₀ r tau : ℕ) (R T : ℕ → ℚ)
    (hh : 2 ≤ h) (hbase : 1 ≤ h₀)
    (hr : 0 < r) (htau : 0 < tau)
    (hRrec : SatisfiesPaperTreeRecurrence h (r : ℚ) R)
    (hTrec : SatisfiesPaperFixedCoreRecurrence h h₀ (r : ℚ) R T)
    (hR1 : R 1 = (h.factorial : ℚ) / (tau : ℚ))
    (n : ℕ) :
    T n = manuscriptFixedCoreClosedForm (T 0) h₀ h r tau n := by
  have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have htauQ : (tau : ℚ) ≠ 0 := by exact_mod_cast htau.ne'
  have hfacNat : h * (h - 1).factorial = h.factorial :=
    Nat.mul_factorial_pred (by omega)
  have hfacQ :
      (h : ℚ) * (((h - 1).factorial : ℕ) : ℚ) =
        (h.factorial : ℚ) := by exact_mod_cast hfacNat
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
    positivity
  have hmain := paper_fixed_core_closed_form h h₀ (r : ℚ)
    R T hh hbase hrQ hRrec hTrec hfirstNe n
  unfold manuscriptFixedCoreClosedForm
  rwa [hfirst] at hmain


end
end ExplicitFormulas
end PolytopeCounting
