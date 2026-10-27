module

public import Proofs.DisconnectedPairingFormula
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Explicit formulas in the case `h = 2`

This file proves the non-radical formulas of Section 7.  It also records the
correct boundary-label normalization: a path has two external facets, so the
symmetry-weighted unlabelled value is the labeled value divided by `2!`.
-/

namespace PolytopeCounting
namespace ExplicitFormulas

noncomputable section

/-- Removing the external-facet labels from the tree formula. -/
def unlabelledTreeClosedForm (h r tau n : ℕ) : ℚ :=
  manuscriptTreeClosedForm h r tau n /
    ((((h - 2) * n + 2).factorial : ℕ) : ℚ)

/-- For `h=2`, the general tree formula is geometric. -/
theorem treeClosedForm_h_two
    (r c : ℚ) (n : ℕ) :
    treeClosedForm 2 r c n = (1 / r) * c ^ n := by
  have hfac : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  unfold treeClosedForm
  simp [hfac]

/-- Formula (60): `R_n = (1/r) (2r/tau)^n`. -/
theorem manuscriptTreeClosedForm_h_two
    (r tau n : ℕ) :
    manuscriptTreeClosedForm 2 r tau n =
      (1 / (r : ℚ)) *
        (((2 * r : ℕ) : ℚ) / (tau : ℚ)) ^ n := by
  unfold manuscriptTreeClosedForm geometricScale
  rw [treeClosedForm_h_two]

/-- For the segment (`r=1`) this is `(2/tau)^n`. -/
theorem segment_labeled_closed_form (tau n : ℕ) :
    manuscriptTreeClosedForm 2 1 tau n =
      ((2 : ℚ) / (tau : ℚ)) ^ n := by
  rw [manuscriptTreeClosedForm_h_two]
  norm_num

/-- Corrected normalization for the unlabelled path mass.

The manuscript's printed expression omits the division by `2!`; the
formal count is `1/2 * (2/tau)^n`.
-/
theorem segment_unlabelled_closed_form (tau n : ℕ) :
    unlabelledTreeClosedForm 2 1 tau n =
      (1 / 2 : ℚ) * ((2 : ℚ) / (tau : ℚ)) ^ n := by
  unfold unlabelledTreeClosedForm
  rw [segment_labeled_closed_form]
  norm_num
  ring

/-- In the unoriented segment case `tau=2`, every path has mass `1/2`. -/
theorem unoriented_path_mass (n : ℕ) :
    unlabelledTreeClosedForm 2 1 2 n = (1 / 2 : ℚ) := by
  rw [segment_unlabelled_closed_form]
  norm_num

/-- Stars-and-bars form of the fixed-core formula for `h=2`. -/
theorem fixedCoreClosedForm_h_two
    (T₀ c : ℚ) (h₀ n : ℕ) (hbase : 1 ≤ h₀) :
    fixedCoreClosedForm T₀ h₀ 2 c n =
      T₀ * c ^ n * (Nat.choose (n + h₀ - 1) n : ℚ) := by
  let N : ℕ := n + h₀ - 1
  have hnN : n ≤ N := by
    dsimp [N]
    omega
  have hsub : N - n = h₀ - 1 := by
    dsimp [N]
    omega
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hnN
  have hchooseQ :
      (Nat.choose N n : ℚ) * (n.factorial : ℚ) *
          ((N - n).factorial : ℚ) = (N.factorial : ℚ) := by
    exact_mod_cast hchooseNat
  have hnfac : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hpfac : ((h₀ - 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (h₀ - 1)
  unfold fixedCoreClosedForm
  norm_num
  change
    T₀ * c ^ n * (N.factorial : ℚ) /
        (((h₀ - 1).factorial : ℚ) * (n.factorial : ℚ)) =
      T₀ * c ^ n * (Nat.choose N n : ℚ)
  rw [hsub] at hchooseQ
  field_simp [hnfac, hpfac]
  rw [← hchooseQ]
  ring

/-- Formula (61) in the manuscript's parameters. -/
theorem manuscriptFixedCoreClosedForm_h_two
    (T₀ : ℚ) (h₀ r tau n : ℕ) (hbase : 1 ≤ h₀) :
    manuscriptFixedCoreClosedForm T₀ h₀ 2 r tau n =
      T₀ * (((2 * r : ℕ) : ℚ) / (tau : ℚ)) ^ n *
        (Nat.choose (n + h₀ - 1) n : ℚ) := by
  unfold manuscriptFixedCoreClosedForm geometricScale
  exact fixedCoreClosedForm_h_two T₀
    (((2 * r : ℕ) : ℚ) / (tau : ℚ)) h₀ n hbase

/-- The cycle value from Section 7: for `tau=2`, `r=1`, the mass is
`1/(2n)` for positive `n`. -/
theorem unoriented_cycle_mass (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℚ)) * unlabelledTreeClosedForm 2 1 2 n =
      1 / (2 * (n : ℚ)) := by
  rw [unoriented_path_mass]
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnQ]


end
end ExplicitFormulas
end PolytopeCounting
