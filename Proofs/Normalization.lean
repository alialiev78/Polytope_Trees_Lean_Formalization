module

public import Proofs.FiniteCounting
public import Proofs.FactorTwoCounting
public import Mathlib.Algebra.Field.Rat

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Exact binomial and factorial normalization

These are the arithmetic cancellations used after the global cut--join
equivalences are counted on labelled cells.  The cell-subset binomial is
absorbed by the two component wreath-group orders, while the boundary-label
binomial remains visible in the recurrence.  The statements are equalities,
not asymptotics and not certificate fields.
-/

namespace PolytopeCounting
namespace Normalization

open FiniteCounting

/-- Allocating `k` of `n` cell labels and multiplying the two component
wreath orders gives the ambient wreath order. -/
theorem choose_mul_wreath_orders {n k : ℕ} (tau : ℕ) (hk : k ≤ n) :
    Nat.choose n k * (k.factorial * tau ^ k) *
        ((n - k).factorial * tau ^ (n - k)) =
      n.factorial * tau ^ n := by
  calc
    Nat.choose n k * (k.factorial * tau ^ k) *
          ((n - k).factorial * tau ^ (n - k)) =
        (Nat.choose n k * k.factorial * (n - k).factorial) *
          (tau ^ k * tau ^ (n - k)) := by ac_rfl
    _ = n.factorial * tau ^ (k + (n - k)) := by
      rw [choose_mul_component_factorials hk, pow_add]
    _ = n.factorial * tau ^ n := by
      congr 2
      omega

/-- Simultaneously allocating cells and old boundary labels.  The first
binomial cancels against group orders; the second records the label split. -/
theorem choose_cells_labels_mul_orders
    {n k m s : ℕ} (tau : ℕ) (hk : k ≤ n) (hs : s ≤ m) :
    Nat.choose n k * Nat.choose m s *
        ((k.factorial * tau ^ k) * s.factorial) *
        (((n - k).factorial * tau ^ (n - k)) * (m - s).factorial) =
      (n.factorial * tau ^ n) * m.factorial := by
  calc
    Nat.choose n k * Nat.choose m s *
          ((k.factorial * tau ^ k) * s.factorial) *
          (((n - k).factorial * tau ^ (n - k)) * (m - s).factorial) =
        (Nat.choose n k * (k.factorial * tau ^ k) *
            ((n - k).factorial * tau ^ (n - k))) *
          (Nat.choose m s * s.factorial * (m - s).factorial) := by ac_rfl
    _ = (n.factorial * tau ^ n) * m.factorial := by
      rw [choose_mul_wreath_orders tau hk,
        choose_mul_component_factorials hs]

/-- Rational form of the cell-label cancellation.  This is the exact
algebraic step converting a labelled bridge count into a product of two
component groupoid masses. -/
theorem choose_mul_normalized_components
    {n k tau : ℕ} (hk : k ≤ n) (htau : 0 < tau) (A B : ℚ) :
    (Nat.choose n k : ℚ) * A * B /
        ((n.factorial * tau ^ n : ℕ) : ℚ) =
      (A / ((k.factorial * tau ^ k : ℕ) : ℚ)) *
        (B / (((n - k).factorial * tau ^ (n - k) : ℕ) : ℚ)) := by
  have hleft : (k.factorial * tau ^ k : ℕ) ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.factorial_ne_zero k)
      (pow_ne_zero k (Nat.ne_of_gt htau))
  have hright : ((n - k).factorial * tau ^ (n - k) : ℕ) ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.factorial_ne_zero (n - k))
      (pow_ne_zero (n - k) (Nat.ne_of_gt htau))
  have hamb : (n.factorial * tau ^ n : ℕ) ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.factorial_ne_zero n)
      (pow_ne_zero n (Nat.ne_of_gt htau))
  have hleftQ : (((k.factorial * tau ^ k : ℕ) : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr hleft
  have hrightQ :
      ((((n - k).factorial * tau ^ (n - k) : ℕ) : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr hright
  have horder := choose_mul_wreath_orders tau hk
  have hcast := congrArg (fun z : ℕ ↦ (z : ℚ)) horder
  have horderQ :
      (Nat.choose n k : ℚ) *
          ((k.factorial * tau ^ k : ℕ) : ℚ) *
          (((n - k).factorial * tau ^ (n - k) : ℕ) : ℚ) =
        ((n.factorial * tau ^ n : ℕ) : ℚ) := by
    simpa only [Nat.cast_mul] using hcast
  apply (div_eq_iff (Nat.cast_ne_zero.mpr hamb)).2
  rw [← horderQ]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  symm
  calc
    A * (((k.factorial * tau ^ k : ℕ) : ℚ))⁻¹ *
          (B * ((((n - k).factorial * tau ^ (n - k) : ℕ) : ℚ))⁻¹) *
          ((Nat.choose n k : ℚ) *
            ((k.factorial * tau ^ k : ℕ) : ℚ) *
            (((n - k).factorial * tau ^ (n - k) : ℕ) : ℚ)) =
        (Nat.choose n k : ℚ) * A * B *
          (((((k.factorial * tau ^ k : ℕ) : ℚ))⁻¹ *
              ((k.factorial * tau ^ k : ℕ) : ℚ)) *
            (((((n - k).factorial * tau ^ (n - k) : ℕ) : ℚ))⁻¹ *
              (((n - k).factorial * tau ^ (n - k) : ℕ) : ℚ))) := by
          ac_rfl
    _ = (Nat.choose n k : ℚ) * A * B := by
      rw [inv_mul_cancel₀ hleftQ, inv_mul_cancel₀ hrightQ]
      simp

/-- The same cancellation with the boundary-label allocation factor kept
explicit, exactly as in the bridge terms of `R`, `T`, `U`, and `Psi`. -/
theorem choose_cells_labels_normalized
    {n k m s tau : ℕ} (hk : k ≤ n) (htau : 0 < tau) (A B : ℚ) :
    (Nat.choose n k : ℚ) * (Nat.choose m s : ℚ) * A * B /
        ((n.factorial * tau ^ n : ℕ) : ℚ) =
      (Nat.choose m s : ℚ) *
        (A / ((k.factorial * tau ^ k : ℕ) : ℚ)) *
        (B / (((n - k).factorial * tau ^ (n - k) : ℕ) : ℚ)) := by
  calc
    (Nat.choose n k : ℚ) * (Nat.choose m s : ℚ) * A * B /
          ((n.factorial * tau ^ n : ℕ) : ℚ) =
        (Nat.choose n k : ℚ) *
          ((Nat.choose m s : ℚ) * A) * B /
            ((n.factorial * tau ^ n : ℕ) : ℚ) := by ac_rfl
    _ = (((Nat.choose m s : ℚ) * A) /
          ((k.factorial * tau ^ k : ℕ) : ℚ)) *
        (B / (((n - k).factorial * tau ^ (n - k) : ℕ) : ℚ)) :=
      choose_mul_normalized_components hk htau _ _
    _ = (Nat.choose m s : ℚ) *
        (A / ((k.factorial * tau ^ k : ℕ) : ℚ)) *
        (B / (((n - k).factorial * tau ^ (n - k) : ℕ) : ℚ)) := by
      rw [mul_div_assoc]


end Normalization
end PolytopeCounting
