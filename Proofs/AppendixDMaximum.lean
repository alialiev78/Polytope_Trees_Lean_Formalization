module

public import Proofs.DisconnectedWHat
public import Proofs.ConcreteFormalExpPair
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Appendix D: exact modes of the disconnected coefficients

The admissible free-boundary sizes have parity `h*n`. The first mode is the
first such size at which `h*n ≤ m + r*(m+1)*(m+2)`. There are two modes
exactly when equality holds there. These statements include both parities,
small sizes, the boundary cases, and all unsupported indices.
-/

namespace PolytopeCounting.AppendixD

open ExplicitFormulas
noncomputable section

/-- The strictly increasing polynomial controlling successive coefficients. -/
def threshold (r m : ℕ) : ℕ := m + r * (m + 1) * (m + 2)

/-- Enumerate the admissible parity class in increasing order. -/
def boundaryIndex (N k : ℕ) : ℕ := N % 2 + 2 * k

theorem threshold_strictMono (r : ℕ) : StrictMono (threshold r) := by
  intro a b hab
  unfold threshold
  apply add_lt_add_of_lt_of_le hab
  gcongr

theorem boundaryIndex_strictMono (N : ℕ) : StrictMono (boundaryIndex N) := by
  intro a b hab
  dsimp [boundaryIndex]
  omega

@[simp] theorem boundaryIndex_top (N : ℕ) : boundaryIndex N (N / 2) = N := by
  unfold boundaryIndex
  omega

@[simp] theorem boundaryIndex_succ (N k : ℕ) :
    boundaryIndex N (k + 1) = boundaryIndex N k + 2 := by
  unfold boundaryIndex
  omega

theorem threshold_exists (N r : ℕ) : ∃ k, N ≤ threshold r (boundaryIndex N k) := by
  refine ⟨N / 2, ?_⟩
  simp [threshold]

/-- Index of the smaller maximizer. Defined by a numerical threshold, not
by an optimization predicate. -/
def modeIndex (N r : ℕ) : ℕ := Nat.find (threshold_exists N r)

def firstMode (N r : ℕ) : ℕ := boundaryIndex N (modeIndex N r)

theorem modeIndex_le (N r : ℕ) : modeIndex N r ≤ N / 2 := by
  apply Nat.find_min'
  simp [threshold]

theorem threshold_firstMode (N r : ℕ) : N ≤ threshold r (firstMode N r) :=
  Nat.find_spec (threshold_exists N r)

theorem threshold_before (N r k : ℕ) (hk : k < modeIndex N r) :
    threshold r (boundaryIndex N k) < N := by
  exact Nat.lt_of_not_ge (Nat.find_min (threshold_exists N r) hk)

theorem threshold_after (N r k : ℕ) (hk : modeIndex N r < k) :
    N < threshold r (boundaryIndex N k) :=
  lt_of_le_of_lt (threshold_firstMode N r)
    (threshold_strictMono r (boundaryIndex_strictMono N hk))

theorem modeIndex_eq_zero_iff (N r : ℕ) :
    modeIndex N r = 0 ↔ N ≤ threshold r (N % 2) := by
  constructor
  · intro h
    have ht := threshold_firstMode N r
    simpa [firstMode, h, boundaryIndex] using ht
  · intro h
    apply Nat.eq_zero_of_le_zero
    apply Nat.find_min'
    simpa [boundaryIndex] using h

theorem supported_boundaryIndex (h n k : ℕ) (hk : k ≤ h * n / 2) :
    WSupported h n (boundaryIndex (h * n) k) := by
  refine ⟨h * n / 2 - k, ?_⟩
  unfold boundaryIndex
  omega

theorem supported_iff_boundaryIndex (h n m : ℕ) :
    WSupported h n m ↔ ∃ k, k ≤ h * n / 2 ∧ m = boundaryIndex (h * n) k := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨m / 2, ?_, ?_⟩
    · omega
    · dsimp [boundaryIndex]
      omega
  · rintro ⟨k, hk, rfl⟩
    exact supported_boundaryIndex h n k hk

theorem coefficient_pos (h r tau n m : ℕ) (hr : 0 < r) (htau : 0 < tau)
    (hs : WSupported h n m) : 0 < WHatClosedForm h r tau n m := by
  obtain ⟨e, he⟩ := hs
  rw [WHatClosedForm_formula46 h r tau n m e he]
  positivity

/-- Exact weak comparison across a step of size two. -/
theorem step_le_iff (h r tau n m : ℕ) (hr : 0 < r) (htau : 0 < tau)
    (hs : WSupported h n m) :
    WHatClosedForm h r tau n (m + 2) ≤ WHatClosedForm h r tau n m ↔
      h * n ≤ threshold r m := by
  have hp := coefficient_pos h r tau n m hr htau hs
  have hc : 0 < (r : ℚ) * (m + 1) * (m + 2) := by positivity
  have hrec := WHatClosedForm_recurrence_all h r tau n m htau
  push_cast at hrec
  rw [← mul_le_mul_iff_right₀ hc, ← hrec, mul_le_mul_iff_left₀ hp]
  have hcst : ((threshold r m : ℕ) : ℚ) =
      (m : ℚ) + (r : ℚ) * (m + 1) * (m + 2) := by
    simp [threshold]
  rw [← Nat.cast_le (α := ℚ), hcst, Nat.cast_mul]
  constructor <;> intro h' <;> linarith

/-- Equality is possible only at an exact integer/parity threshold. -/
theorem step_eq_iff (h r tau n m : ℕ) (hr : 0 < r) (htau : 0 < tau)
    (hs : WSupported h n m) :
    WHatClosedForm h r tau n (m + 2) = WHatClosedForm h r tau n m ↔
      h * n = threshold r m := by
  have hp := coefficient_pos h r tau n m hr htau hs
  have hc : (r : ℚ) * (m + 1) * (m + 2) ≠ 0 := by positivity
  have hrec := WHatClosedForm_recurrence_all h r tau n m htau
  push_cast at hrec
  rw [← mul_right_inj' hc, ← hrec, mul_left_inj' hp.ne']
  have hcst : ((threshold r m : ℕ) : ℚ) =
      (m : ℚ) + (r : ℚ) * (m + 1) * (m + 2) := by simp [threshold]
  rw [← Nat.cast_inj (R := ℚ), hcst, Nat.cast_mul]
  constructor <;> intro h' <;> linarith

theorem step_lt_iff (h r tau n m : ℕ) (hr : 0 < r) (htau : 0 < tau)
    (hs : WSupported h n m) :
    WHatClosedForm h r tau n (m + 2) < WHatClosedForm h r tau n m ↔
      h * n < threshold r m := by
  simp only [lt_iff_le_and_ne, step_le_iff h r tau n m hr htau hs,
    ne_eq, step_eq_iff h r tau n m hr htau hs]

theorem step_increase_iff (h r tau n m : ℕ) (hr : 0 < r) (htau : 0 < tau)
    (hs : WSupported h n m) :
    WHatClosedForm h r tau n m < WHatClosedForm h r tau n (m + 2) ↔
      threshold r m < h * n := by
  rw [← not_le, step_le_iff h r tau n m hr htau hs, not_le]

private theorem chain_le (F : ℕ → ℚ) (a b : ℕ) (hab : a ≤ b)
    (hs : ∀ k, a ≤ k → k < b → F k ≤ F (k + 1)) : F a ≤ F b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (ih (fun k hak hkb => hs k hak (by omega))).trans (hs b hab (by omega))

private theorem chain_lt (F : ℕ → ℚ) (a b : ℕ) (hab : a < b)
    (hs : ∀ k, a ≤ k → k < b → F k < F (k + 1)) : F a < F b := by
  exact (hs a le_rfl hab).trans_le
    (chain_le F (a + 1) b hab (fun k hak hkb => (hs k (by omega) hkb).le))

/-- Every coefficient before the first mode is strictly smaller. -/
theorem before_mode_lt (h r tau n k : ℕ) (hr : 0 < r) (htau : 0 < tau)
    (hk : k < modeIndex (h * n) r) :
    WHatClosedForm h r tau n (boundaryIndex (h * n) k) <
      WHatClosedForm h r tau n (firstMode (h * n) r) := by
  apply chain_lt (fun j => WHatClosedForm h r tau n (boundaryIndex (h * n) j))
    k (modeIndex (h * n) r) hk
  intro j hj hjM
  rw [boundaryIndex_succ]
  apply (step_increase_iff h r tau n _ hr htau
    (supported_boundaryIndex h n j
      (le_trans (Nat.le_of_lt hjM) (modeIndex_le (h * n) r)))).2
  exact threshold_before _ _ _ hjM

/-- All indices strictly beyond the possible second mode are smaller. -/
theorem after_second_mode_lt (h r tau n k : ℕ) (hr : 0 < r) (htau : 0 < tau)
    (hk : modeIndex (h * n) r + 1 < k) (hkmax : k ≤ h * n / 2) :
    WHatClosedForm h r tau n (boundaryIndex (h * n) k) <
      WHatClosedForm h r tau n (firstMode (h * n) r) := by
  have hchain := chain_lt
    (fun j => -WHatClosedForm h r tau n (boundaryIndex (h * n) j))
    (modeIndex (h * n) r + 1) k hk (by
      intro j hj hjk
      rw [boundaryIndex_succ, neg_lt_neg_iff]
      apply (step_lt_iff h r tau n _ hr htau
        (supported_boundaryIndex h n j (by omega))).2
      exact threshold_after _ _ _ (by omega))
  have hstep := (step_le_iff h r tau n (firstMode (h * n) r) hr htau
    (supported_boundaryIndex h n _ (modeIndex_le _ _))).2 (threshold_firstMode _ _)
  simp only [boundaryIndex_succ] at hchain
  change -WHatClosedForm h r tau n (firstMode (h * n) r + 2) < _ at hchain
  linarith

/-- Global maximum, including zero coefficients outside the admissible support. -/
theorem coefficient_le_firstMode (h r tau n m : ℕ) (hr : 0 < r) (htau : 0 < tau) :
    WHatClosedForm h r tau n m ≤ WHatClosedForm h r tau n (firstMode (h * n) r) := by
  by_cases hs : WSupported h n m
  · obtain ⟨k, hk, rfl⟩ := (supported_iff_boundaryIndex h n m).mp hs
    rcases lt_trichotomy k (modeIndex (h * n) r) with hlt | heq | hgt
    · exact (before_mode_lt h r tau n k hr htau hlt).le
    · subst k
      exact le_rfl
    · by_cases heq : k = modeIndex (h * n) r + 1
      · subst k
        rw [boundaryIndex_succ]
        exact (step_le_iff h r tau n _ hr htau
          (supported_boundaryIndex h n _ (modeIndex_le _ _))).2
            (threshold_firstMode _ _)
      · exact (after_second_mode_lt h r tau n k hr htau (by omega) hk).le
  · rw [WHatClosedForm_eq_zero_of_not_supported h r tau n m hs]
    exact (coefficient_pos h r tau n _ hr htau
      (supported_boundaryIndex h n _ (modeIndex_le _ _))).le

/-- Complete classification of the maximizers: one, or exactly two at distance two. -/
theorem coefficient_eq_max_iff (h r tau n m : ℕ) (hr : 0 < r) (htau : 0 < tau) :
    WHatClosedForm h r tau n m = WHatClosedForm h r tau n (firstMode (h * n) r) ↔
      m = firstMode (h * n) r ∨
        (m = firstMode (h * n) r + 2 ∧ h * n = threshold r (firstMode (h * n) r)) := by
  constructor
  · intro heq
    have hs : WSupported h n m := by
      by_contra hns
      rw [WHatClosedForm_eq_zero_of_not_supported h r tau n m hns] at heq
      exact (ne_of_gt (coefficient_pos h r tau n _ hr htau
        (supported_boundaryIndex h n _ (modeIndex_le _ _)))) heq.symm
    obtain ⟨k, hk, rfl⟩ := (supported_iff_boundaryIndex h n m).mp hs
    rcases lt_trichotomy k (modeIndex (h * n) r) with hlt | he | hgt
    · exact ((before_mode_lt h r tau n k hr htau hlt).ne heq).elim
    · left
      subst k
      rfl
    · have he : k = modeIndex (h * n) r + 1 := by
        by_contra hne
        exact ((after_second_mode_lt h r tau n k hr htau (by omega) hk).ne heq).elim
      subst k
      rw [boundaryIndex_succ] at heq ⊢
      refine Or.inr ⟨rfl, ?_⟩
      exact (step_eq_iff h r tau n _ hr htau
        (supported_boundaryIndex h n _ (modeIndex_le _ _))).mp heq
  · rintro (rfl | ⟨rfl, he⟩)
    · rfl
    · exact (step_eq_iff h r tau n _ hr htau
        (supported_boundaryIndex h n _ (modeIndex_le _ _))).mpr he

/-- The larger real root of the turning-point quadratic. It can be negative
for small `N`; the natural ceiling below correctly handles that case. -/
def turningPoint (N r : ℕ) : ℝ :=
  (Real.sqrt ((r : ℝ) ^ 2 + 6 * r + 1 + 4 * r * N) - (3 * r + 1)) / (2 * r)

theorem turningPoint_equation (N r : ℕ) (hr : 0 < r) :
    (r : ℝ) * turningPoint N r ^ 2 + (3 * r + 1) * turningPoint N r +
      2 * r - N = 0 := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs := Real.sq_sqrt
    (by positivity : 0 ≤ (r : ℝ) ^ 2 + 6 * r + 1 + 4 * r * N)
  unfold turningPoint
  generalize Real.sqrt ((r : ℝ) ^ 2 + 6 * r + 1 + 4 * r * N) = s at hs ⊢
  field_simp [hrR]
  nlinarith

theorem turningPoint_le_iff (N r : ℕ) (x : ℝ) (hr : 0 < r) (hx : 0 ≤ x) :
    turningPoint N r ≤ x ↔ (N : ℝ) ≤ x + r * (x + 1) * (x + 2) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  unfold turningPoint
  rw [div_le_iff₀ (by positivity), sub_le_iff_le_add,
    Real.sqrt_le_left (by positivity), ← sub_nonneg]
  have hid :
      (x * (2 * r) + (3 * r + 1)) ^ 2 -
          ((r : ℝ) ^ 2 + 6 * r + 1 + 4 * r * N) =
        (4 * r) * (x + r * (x + 1) * (x + 2) - N) := by ring
  rw [hid, mul_nonneg_iff_of_pos_left (by positivity), sub_nonneg]

/-- Explicit parity-aware rounding formula for the smaller maximizing index. -/
theorem modeIndex_eq_ceil (N r : ℕ) (hr : 0 < r) :
    modeIndex N r = ⌈(turningPoint N r - (N % 2 : ℕ)) / 2⌉₊ := by
  apply Nat.le_antisymm
  · apply Nat.find_min'
    have hceil := Nat.le_ceil ((turningPoint N r - (N % 2 : ℕ)) / 2)
    have hroot : turningPoint N r ≤
        (boundaryIndex N ⌈(turningPoint N r - (N % 2 : ℕ)) / 2⌉₊ : ℝ) := by
      dsimp [boundaryIndex]
      push_cast
      linarith
    have hcrit := (turningPoint_le_iff N r _ hr (by positivity)).mp hroot
    exact_mod_cast hcrit
  · apply Nat.ceil_le.mpr
    have hcrit : (N : ℝ) ≤
        (firstMode N r : ℝ) + r * ((firstMode N r : ℝ) + 1) * ((firstMode N r : ℝ) + 2) := by
      exact_mod_cast threshold_firstMode N r
    have hroot := (turningPoint_le_iff N r _ hr (by positivity)).mpr hcrit
    dsimp [firstMode, boundaryIndex] at hroot
    push_cast at hroot
    linarith

theorem firstMode_explicit (N r : ℕ) (hr : 0 < r) :
    firstMode N r = N % 2 + 2 * ⌈(turningPoint N r - (N % 2 : ℕ)) / 2⌉₊ := by
  rw [firstMode, boundaryIndex, modeIndex_eq_ceil N r hr]

theorem even_lower_boundary (N r : ℕ) (hN : N % 2 = 0) :
    firstMode N r = 0 ↔ N ≤ 2 * r := by
  have hm : firstMode N r = 0 ↔ modeIndex N r = 0 := by
    dsimp [firstMode, boundaryIndex]
    rw [hN]
    omega
  rw [hm, modeIndex_eq_zero_iff, hN]
  simp [threshold, Nat.mul_comm]

theorem odd_lower_boundary (N r : ℕ) (hN : N % 2 = 1) :
    firstMode N r = 1 ↔ N ≤ 1 + 6 * r := by
  have hm : firstMode N r = 1 ↔ modeIndex N r = 0 := by
    dsimp [firstMode, boundaryIndex]
    rw [hN]
    omega
  rw [hm, modeIndex_eq_zero_iff, hN]
  have ht : threshold r 1 = 1 + 6 * r := by unfold threshold; ring
  rw [ht]

/-- In the tetrahedral case a tie is arithmetically impossible. -/
theorem tetrahedron_no_tie (n : ℕ) :
    4 * n ≠ threshold 3 (firstMode (4 * n) 3) := by
  have heven : (4 * n) % 2 = 0 := by omega
  have hm : firstMode (4 * n) 3 = 2 * modeIndex (4 * n) 3 := by
    simp [firstMode, boundaryIndex, heven]
  rw [hm]
  have ht (k : ℕ) : threshold 3 (2 * k) = 4 * (3 * k ^ 2 + 5 * k + 1) + 2 := by
    unfold threshold
    ring
  rw [ht]
  omega

theorem tetrahedron_unique_mode (tau n m : ℕ) (htau : 0 < tau) :
    WHatClosedForm 4 3 tau n m = WHatClosedForm 4 3 tau n (firstMode (4 * n) 3) ↔
      m = firstMode (4 * n) 3 := by
  rw [coefficient_eq_max_iff 4 3 tau n m (by decide) htau]
  simp [tetrahedron_no_tie]

end
end PolytopeCounting.AppendixD

namespace PolytopeTrees
noncomputable section
open PolytopeCounting PolytopeCounting.AppendixD
universe u

/-- Appendix D for the original finite matching counts, not just the formula. -/
theorem W_le_firstMode (L : Type u) [Group L] [Fintype L]
    (n h r m : ℕ) [MulAction L (Fin h)] (hr : 0 < r) :
    W L n h r m ≤ W L n h r (firstMode (h * n) r) := by
  rw [W_eq_WCoefficient_all, W_eq_WCoefficient_all]
  exact coefficient_le_firstMode h r (Fintype.card L) n m hr Fintype.card_pos

/-- All maximizers of the concrete disconnected mass. -/
theorem W_eq_max_iff (L : Type u) [Group L] [Fintype L]
    (n h r m : ℕ) [MulAction L (Fin h)] (hr : 0 < r) :
    W L n h r m = W L n h r (firstMode (h * n) r) ↔
      m = firstMode (h * n) r ∨
        (m = firstMode (h * n) r + 2 ∧ h * n = threshold r (firstMode (h * n) r)) := by
  rw [W_eq_WCoefficient_all, W_eq_WCoefficient_all]
  exact coefficient_eq_max_iff h r (Fintype.card L) n m hr Fintype.card_pos

end
end PolytopeTrees
