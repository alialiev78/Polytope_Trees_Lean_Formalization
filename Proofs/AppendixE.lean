module

public import Proofs.BinomialIdentities

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Appendix E: Pascal symmetrization

This proof uses the `h₀ = 1` instance of (30), removes its zero-index term,
reflects the remaining sum, and applies Pascal's identity. It does not use
the independently proved identity (29) or its tree recurrence.
-/

namespace PolytopeCounting.BinomialIdentities

open scoped BigOperators
noncomputable section

def splitChooseRatio (h n k : ℕ) : ℚ :=
  (Nat.choose n k : ℚ) / (Nat.choose (n * (h - 1)) (k * (h - 1)) : ℚ)

theorem splitChooseRatio_reflect (h n k : ℕ) (hk : k ≤ n) :
    splitChooseRatio h n (n - k) = splitChooseRatio h n k := by
  unfold splitChooseRatio
  rw [Nat.choose_symm hk, Nat.sub_mul,
    Nat.choose_symm (Nat.mul_le_mul_right (h - 1) hk)]

theorem sum_proper_splits_reflect (n : ℕ) (f : ℕ → ℚ) :
    (∑ k ∈ Finset.Icc 1 (n - 1), f (n - k)) =
      ∑ k ∈ Finset.Icc 1 (n - 1), f k := by
  apply Finset.sum_bij (fun k _ => n - k)
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Icc] at ha hb
    omega
  · intro k hk
    refine ⟨n - k, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hk ⊢
      omega
    · simp only [Finset.mem_Icc] at hk
      omega
  · intro k hk
    rfl

/-- The implication in Appendix E, proved by the stated algebraic route. -/
theorem identity29_of_identity30_one (h n : ℕ) (_hh : 2 ≤ h) (hn : 2 ≤ n)
    (h30 : Identity30 h 1 n) : Identity29 h n := by
  let q := h - 2
  let f : ℕ → ℚ := fun k =>
    (Nat.choose (q * n + 1) (q * (n - k) + 1) : ℚ) * splitChooseRatio h n k
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h30' : (1 : ℚ) = (1 / (n : ℚ)) * ∑ k ∈ Finset.range n, f k := by
    simpa [Identity30, f, q, splitChooseRatio, mul_div_assoc] using h30
  have htotal : (∑ k ∈ Finset.range n, f k) = (n : ℚ) := by
    field_simp at h30'
    linarith
  have hrange : Finset.range n = insert 0 (Finset.Icc 1 (n - 1)) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hz : f 0 = 1 := by simp [f, splitChooseRatio]
  have hsum : (∑ k ∈ Finset.Icc 1 (n - 1), f k) = (n : ℚ) - 1 := by
    rw [hrange, Finset.sum_insert (by simp), hz] at htotal
    linarith
  have hreflect :
      (∑ k ∈ Finset.Icc 1 (n - 1),
        (Nat.choose (q * n + 1) (q * k + 1) : ℚ) * splitChooseRatio h n k) =
      (n : ℚ) - 1 := by
    rw [← hsum, ← sum_proper_splits_reflect n f]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hnk : n - (n - k) = k := by omega
    simp only [f, hnk, splitChooseRatio_reflect h n k (by omega)]
  have hsymm :
      (∑ k ∈ Finset.Icc 1 (n - 1),
        (Nat.choose (q * n + 1) (q * k) : ℚ) * splitChooseRatio h n k) =
      (n : ℚ) - 1 := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hkn : k ≤ n := by omega
    have hmul := Nat.mul_le_mul_left q hkn
    have hsub : q * n + 1 - q * k = q * (n - k) + 1 := by
      rw [Nat.mul_sub_left_distrib]
      omega
    dsimp [f]
    rw [← Nat.choose_symm (show q * k ≤ q * n + 1 by omega), hsub]
  unfold Identity29
  change (2 * (n - 1) : ℚ) = ∑ k ∈ Finset.Icc 1 (n - 1),
    (Nat.choose (q * n + 2) (q * k + 1) : ℚ) *
      (Nat.choose n k : ℚ) / (Nat.choose (n * (h - 1)) (k * (h - 1)) : ℚ)
  calc
    (2 * (n - 1) : ℚ) =
        (∑ k ∈ Finset.Icc 1 (n - 1),
          (Nat.choose (q * n + 1) (q * k + 1) : ℚ) * splitChooseRatio h n k) +
        (∑ k ∈ Finset.Icc 1 (n - 1),
          (Nat.choose (q * n + 1) (q * k) : ℚ) * splitChooseRatio h n k) := by
      rw [hreflect, hsymm]
      ring
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hpascal := Nat.choose_succ_succ (q * n + 1) (q * k)
      have hpascalQ :
          (Nat.choose (q * n + 2) (q * k + 1) : ℚ) =
          (Nat.choose (q * n + 1) (q * k) : ℚ) +
          (Nat.choose (q * n + 1) (q * k + 1) : ℚ) := by
        exact_mod_cast hpascal
      rw [hpascalQ]
      simp only [splitChooseRatio]
      ring

theorem appendixE : AppendixEStatement := by
  intro h n hh hn h30
  exact identity29_of_identity30_one h n hh hn h30

end
end PolytopeCounting.BinomialIdentities
