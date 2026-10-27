module

public import Proofs.PublicationProofs

@[expose] public section

namespace PolytopeTrees
open scoped BigOperators
noncomputable section
universe u
variable (L : Type u) [Group L] [Fintype L]

/-- Connected cut--join, including closed boundaries and nontrivial stabilizers. -/
theorem U_recurrence (n h r m b : ℕ) [MulAction L (Fin h)] :
    ((n + b - 1 : ℕ) : ℚ) * U L n h r m b =
      (r : ℚ) / 2 * Uprev L n h r m b + (r : ℚ) / 2 * Uconv L n h r m b := by
  rw [U_eq_mass, Uprev_eq_mass, Uconv_eq_mass]
  exact PolytopeCounting.FacetPairing.UnconditionalFinalRecurrences.U_all_rank n h r m b

/-- Rooted cut--join; the root component may have zero ordinary cells. -/
theorem Psi_recurrence (n h₀ h r m b : ℕ) [MulAction L (Fin h)] :
    ((n + b : ℕ) : ℚ) * Psi L n h₀ h r m b =
      (r : ℚ) / 2 * Psiprev L n h₀ h r m b + (r : ℚ) * Psiconv L n h₀ h r m b := by
  rw [Psi_eq_mass, Psiprev_eq_mass, Psiconv_eq_mass]
  exact PolytopeCounting.FacetPairing.UnconditionalFinalRecurrences.Psi_all_rank n h₀ h r m b

/-- Statement 5.1, for the concrete rank-zero counts. -/
theorem R_recurrence (n h r : ℕ) [MulAction L (Fin h)] (hh : 2 ≤ h) (hn : 2 ≤ n) :
    ((n - 1 : ℕ) : ℚ) * R L n h r = (r : ℚ) / 2 *
      ∑ k ∈ Finset.Icc 1 (n - 1),
        (Nat.choose ((h - 2) * n + 2) ((h - 2) * k + 1) : ℚ) *
          R L k h r * R L (n - k) h r := by
  simpa only [R_eq_mass] using
    (PolytopeCounting.FacetPairing.MassExplicit.RMass_satisfies_paper_recurrence
      (L := L) h r hh n hn)

/-- Statement 5.2, with a fixed distinguished root cell. -/
theorem T_recurrence (n h₀ h r : ℕ) [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hroot : 1 ≤ h₀) (hn : 0 < n) :
    (n : ℚ) * T L n h₀ h r = (r : ℚ) *
      ∑ k ∈ Finset.range n,
        (Nat.choose ((h - 2) * n + h₀) ((h - 2) * (n - k) + 1) : ℚ) *
          T L k h₀ h r * R L (n - k) h r := by
  simpa only [R_eq_mass, T_eq_mass] using
    (PolytopeCounting.FacetPairing.MassExplicit.TMass_satisfies_paper_fixed_core_recurrence
      (L := L) h₀ h r hh hroot n hn)

/-- Formula (20), including the proved one-cell initial condition. -/
theorem R_formula (n h r : ℕ) [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hr : 0 < r) (hn : 0 < n) :
    R L n h r = 1 / (r : ℚ) *
      ((h : ℚ) * (r : ℚ) / (Fintype.card L : ℚ)) ^ n *
      ((n * (h - 1)).factorial : ℚ) / (n.factorial : ℚ) := by
  have hb : PolytopeCounting.FacetPairing.NumericalRecurrenceAssembly.RMass L 1 h r =
      (h.factorial : ℚ) / (Fintype.card L : ℚ) := by
    rw [← R_eq_mass]
    exact R_one L h r hh
  have hf := PolytopeCounting.FacetPairing.MassExplicit.RMass_closed_form_of_single_cell
    (L := L) h r (Fintype.card L) hh hr (Fintype.card_pos) hb n hn
  simpa only [R_eq_mass, PolytopeCounting.ExplicitFormulas.manuscriptTreeClosedForm,
    PolytopeCounting.ExplicitFormulas.treeClosedForm,
    PolytopeCounting.ExplicitFormulas.geometricScale, Nat.cast_mul] using hf

/-- Formula (27), with the actual root count as initial value. -/
theorem T_formula (n h₀ h r : ℕ) [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hroot : 1 ≤ h₀) (hr : 0 < r) :
    T L n h₀ h r = T L 0 h₀ h r *
      ((h : ℚ) * (r : ℚ) / (Fintype.card L : ℚ)) ^ n *
      ((n * (h - 1) + h₀ - 1).factorial : ℚ) /
      (((h₀ - 1).factorial : ℚ) * (n.factorial : ℚ)) := by
  have hb : PolytopeCounting.FacetPairing.NumericalRecurrenceAssembly.RMass L 1 h r =
      (h.factorial : ℚ) / (Fintype.card L : ℚ) := by
    rw [← R_eq_mass]
    exact R_one L h r hh
  have hf := PolytopeCounting.FacetPairing.MassExplicit.TMass_closed_form_of_tree_single_cell
    (L := L) h₀ h r (Fintype.card L) hh hroot hr (Fintype.card_pos) hb n
  simpa only [T_eq_mass, PolytopeCounting.ExplicitFormulas.manuscriptFixedCoreClosedForm,
    PolytopeCounting.ExplicitFormulas.fixedCoreClosedForm,
    PolytopeCounting.ExplicitFormulas.geometricScale, Nat.cast_mul] using hf

/-- Formula (46), with explicit parity and support. -/
theorem W_formula (n h r m e : ℕ) [MulAction L (Fin h)]
    (hs : h * n = m + 2 * e) :
    W L n h r m = 1 / ((n.factorial : ℚ) * (Fintype.card L : ℚ) ^ n) *
      ((r : ℚ) / 2) ^ e * ((h * n).factorial : ℚ) /
      ((m.factorial : ℚ) * (e.factorial : ℚ)) := by
  rw [W_eq_mass, PolytopeCounting.FacetPairing.DisconnectedTop.WHatMass_closed_form
    n h r (Fintype.card L) rfl Fintype.card_pos m e (by simpa [Nat.mul_comm] using hs)]
  exact PolytopeCounting.ExplicitFormulas.WHatClosedForm_formula46 h r (Fintype.card L) n m e hs

/-- Recurrence (43), expressed without truncated subtraction. -/
theorem W_recurrence (n h r m e : ℕ) [MulAction L (Fin h)]
    (hs : h * n = m + 2 * (e + 1)) :
    (2 * (e + 1) : ℚ) * W L n h r m =
      (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) * W L n h r (m + 2) := by
  have hs' : h * n = (m + 2) + 2 * e := by omega
  rw [W_formula L n h r m (e + 1) hs, W_formula L n h r (m + 2) e hs']
  have hf := PolytopeCounting.ExplicitFormulas.WHatClosedForm_recurrence_by_pairs
    h r (Fintype.card L) n m e Fintype.card_pos hs
  simpa only [PolytopeCounting.ExplicitFormulas.WHatClosedForm_formula46 h r (Fintype.card L) n m (e + 1) hs,
    PolytopeCounting.ExplicitFormulas.WHatClosedForm_formula46 h r (Fintype.card L) n (m + 2) e hs'] using hf
end
end PolytopeTrees
