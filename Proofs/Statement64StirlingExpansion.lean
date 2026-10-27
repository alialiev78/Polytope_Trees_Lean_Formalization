module

public import Proofs.ConcreteWAsymptotic

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-! # The Stirling normalization in Statement 6.4

For positive h, r and tau, logarithms reduce the real-power normalization
to algebra. The resulting reduction is combined with the proved matching
limit in `UnconditionalMatchingAsymptotic`.
-/

namespace PolytopeCounting.HermiteAsymptotic

noncomputable section
open Filter
open scoped Topology

/-- The exact leading-term rearrangement for each positive index. -/
theorem disconnectedStirlingLeadingTerm_eq_statement64
    (h n : ℕ) (r tau : ℝ)
    (hh : 0 < h) (hn : 0 < n) (hr : 0 < r) (htau : 0 < tau) :
    disconnectedStirlingLeadingTerm h n r tau =
      statement64LeadingTerm h n r tau := by
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hN : 0 < ((h * n : ℕ) : ℝ) := by positivity
  have hbase : 0 < r * (h : ℝ) := by positivity
  have hpbase := Real.rpow_pos_of_pos hbase ((h : ℝ) / 2)
  have hpindex := Real.rpow_pos_of_pos hnR ((n : ℝ) * ((h : ℝ) / 2 - 1))
  have hl : 0 < disconnectedStirlingLeadingTerm h n r tau := by
    unfold disconnectedStirlingLeadingTerm stirlingApprox
    have hp := matchingHermiteLeadingTerm_pos (h * n) r hr
    positivity
  have hrhs : 0 < statement64LeadingTerm h n r tau := by
    unfold statement64LeadingTerm
    positivity
  have hlog : Real.log (disconnectedStirlingLeadingTerm h n r tau) =
      Real.log (statement64LeadingTerm h n r tau) := by
    simp (disch := positivity) only [disconnectedStirlingLeadingTerm,
      matchingHermiteLeadingTerm, stirlingApprox, statement64LeadingTerm,
      Nat.cast_mul, Real.rpow_eq_pow, Real.log_mul, Real.log_div, Real.log_pow,
      Real.log_rpow, Real.log_sqrt, Real.log_exp, Real.log_one]
    ring
  calc
    disconnectedStirlingLeadingTerm h n r tau =
        Real.exp (Real.log (disconnectedStirlingLeadingTerm h n r tau)) :=
      (Real.exp_log hl).symm
    _ = Real.exp (Real.log (statement64LeadingTerm h n r tau)) :=
      congrArg Real.exp hlog
    _ = statement64LeadingTerm h n r tau := Real.exp_log hrhs

/-- ExpandedStatement64Rewrite is a conclusion, not an input. -/
theorem expandedStatement64Rewrite
    (h : ℕ) (r tau : ℝ) (hh : 0 < h) (hr : 0 < r) (htau : 0 < tau) :
    ExpandedStatement64Rewrite h r tau := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact disconnectedStirlingLeadingTerm_eq_statement64 h n r tau hh hn hr htau

/-- Unconditional completion of the Stirling/rearrangement bridge. -/
theorem stirlingRewriteForStatement64
    (h : ℕ) (r tau : ℝ) (hh : 0 < h) (hr : 0 < r) (htau : 0 < tau) :
    StirlingRewriteForStatement64 h r tau :=
  stirlingRewriteForStatement64_of_expanded_pos h r tau hr htau.ne'
    (expandedStatement64Rewrite h r tau hh hr htau)

/-- Reduction using the matching/Hermite estimate;
there is no Stirling or real-power identity among the hypotheses. -/
theorem statement64_of_hermite
    (h : ℕ) (r tau : ℝ) (hh : 0 < h) (hr : 0 < r) (htau : 0 < tau)
    (hHermite : FixedImaginaryHermiteAsymptotic h r) :
    Statement64 h r tau :=
  statement64_of_hermite_and_expanded h r tau hr htau.ne' hHermite
    (expandedStatement64Rewrite h r tau hh hr htau)

end
end PolytopeCounting.HermiteAsymptotic

namespace PolytopeCounting.FacetPairing.ConcreteWAsymptotic

noncomputable section
universe uL

/-- Transfer to the existing action-groupoid mass, retaining just the one
analytic estimate proved in `UnconditionalMatchingAsymptotic`. -/
theorem concreteStatement64_of_hermite
    (L : Type uL) [Group L] [Fintype L]
    (h r : ℕ) [MulAction L (Fin h)] (hh : 0 < h) (hr : 0 < r)
    (hHermite : HermiteAsymptotic.FixedImaginaryHermiteAsymptotic h (r : ℝ)) :
    ConcreteStatement64 L h r (Fintype.card L) := by
  apply concreteStatement64_of_statement64 h r (Fintype.card L) rfl Fintype.card_pos
  exact HermiteAsymptotic.statement64_of_hermite h r (Fintype.card L)
    hh (by exact_mod_cast hr) (by exact_mod_cast (Fintype.card_pos (α := L))) hHermite

end
end PolytopeCounting.FacetPairing.ConcreteWAsymptotic
