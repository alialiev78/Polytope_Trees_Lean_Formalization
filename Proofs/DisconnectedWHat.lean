module

public import Proofs.DisconnectedPairingFormula
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# A literal `m`-indexed closed form for `\widehat W_{n,m}`

`DisconnectedPairingFormula` uses the number `ell` of glued pairs.  This file
packages the same expression as a function of the free-boundary index `m`,
sets unsupported parity/range indices to zero, and proves recurrence (43),
the top coefficient, and formula (46) in the manuscript's notation.
-/

namespace PolytopeCounting
namespace ExplicitFormulas

open scoped BigOperators

noncomputable section

/-- The support condition for a pairing of `h*n` darts with `m` unmatched
darts: there is a unique number `ell` of pairs with
`h*n = m + 2*ell`. -/
def WSupported (h n m : ℕ) : Prop :=
  ∃ ell : ℕ, h * n = m + 2 * ell

/-- The literal free-boundary-indexed coefficient.  The witness is unique,
so using `Nat.find` does not introduce a choice ambiguity. -/
noncomputable def WHatClosedForm (h r tau n m : ℕ) : ℚ := by
  classical
  exact if hs : WSupported h n m then
    disconnectedPairingClosedForm h r tau n (Nat.find hs)
  else
    0

/-- Uniqueness of the number of glued pairs. -/
theorem WSupported_witness_unique
    {h n m ell k : ℕ}
    (hell : h * n = m + 2 * ell)
    (hk : h * n = m + 2 * k) :
    ell = k := by
  omega

/-- On a supported index, the `m`-indexed definition is exactly the existing
`ell`-parameterized formula. -/
theorem WHatClosedForm_eq_of_support
    (h r tau n m ell : ℕ)
    (hsupport : h * n = m + 2 * ell) :
    WHatClosedForm h r tau n m =
      disconnectedPairingClosedForm h r tau n ell := by
  let hs : WSupported h n m := ⟨ell, hsupport⟩
  rw [WHatClosedForm, dif_pos hs]
  have hfind := Nat.find_spec hs
  have heq : Nat.find hs = ell :=
    WSupported_witness_unique hfind hsupport
  rw [heq]

/-- Unsupported indices vanish. -/
theorem WHatClosedForm_eq_zero_of_not_supported
    (h r tau n m : ℕ) (hs : ¬ WSupported h n m) :
    WHatClosedForm h r tau n m = 0 := by
  simp [WHatClosedForm, hs]

/-- In particular, indices above the maximum number `h*n` of free darts
vanish. -/
theorem WHatClosedForm_eq_zero_of_lt
    (h r tau n m : ℕ) (hm : h * n < m) :
    WHatClosedForm h r tau n m = 0 := by
  apply WHatClosedForm_eq_zero_of_not_supported
  rintro ⟨ell, hell⟩
  omega

/-- The top/no-gluing coefficient. -/
theorem WHatClosedForm_top
    (h r tau n : ℕ) :
    WHatClosedForm h r tau n (h * n) =
      1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n) := by
  rw [WHatClosedForm_eq_of_support h r tau n (h * n) 0 (by omega)]
  exact disconnectedPairingClosedForm_zero h r tau n

/-- Formula (46), now displayed directly with the free-facet index `m`. -/
theorem WHatClosedForm_formula46
    (h r tau n m ell : ℕ)
    (hsupport : h * n = m + 2 * ell) :
    WHatClosedForm h r tau n m =
      1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n) *
        ((r : ℚ) / 2) ^ ell *
        ((h * n).factorial : ℚ) /
          ((m.factorial : ℚ) * (ell.factorial : ℚ)) := by
  rw [WHatClosedForm_eq_of_support h r tau n m ell hsupport]
  exact disconnectedPairing_formula46 h r tau n m ell hsupport

/-- Recurrence (43) in subtraction-free support notation. -/
theorem WHatClosedForm_recurrence_by_pairs
    (h r tau n m ell : ℕ)
    (htau : 0 < tau)
    (hsupport : h * n = m + 2 * (ell + 1)) :
    (2 * (ell + 1) : ℚ) * WHatClosedForm h r tau n m =
      (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        WHatClosedForm h r tau n (m + 2) := by
  have hnext : h * n = (m + 2) + 2 * ell := by omega
  rw [WHatClosedForm_eq_of_support h r tau n m (ell + 1) hsupport,
    WHatClosedForm_eq_of_support h r tau n (m + 2) ell hnext]
  have hrec := disconnectedPairingClosedForm_recurrence
    h r tau n ell htau (by omega : 2 * (ell + 1) ≤ h * n)
  have hm1 : h * n - 2 * ell - 1 = m + 1 := by omega
  have hm2 : h * n - 2 * ell = m + 2 := by omega
  simpa [hm1, hm2] using hrec

/-- Literal form of recurrence (43). -/
theorem WHatClosedForm_recurrence
    (h r tau n m ell : ℕ)
    (htau : 0 < tau)
    (hsupport : h * n = m + 2 * (ell + 1)) :
    ((h * n - m : ℕ) : ℚ) * WHatClosedForm h r tau n m =
      (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        WHatClosedForm h r tau n (m + 2) := by
  have hdiff : h * n - m = 2 * (ell + 1) := by omega
  rw [hdiff]
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
    (WHatClosedForm_recurrence_by_pairs
      h r tau n m ell htau hsupport)

/-- Recurrence (43) also holds at every unsupported or top index.  This is
the coefficientwise form needed for the bivariate generating-function PDE. -/
theorem WHatClosedForm_recurrence_all
    (h r tau n m : ℕ) (htau : 0 < tau) :
    (((h * n : ℕ) : ℚ) - (m : ℚ)) * WHatClosedForm h r tau n m =
      (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        WHatClosedForm h r tau n (m + 2) := by
  by_cases hm : m = h * n
  · subst m
    have hz : WHatClosedForm h r tau n (h * n + 2) = 0 :=
      WHatClosedForm_eq_zero_of_lt h r tau n (h * n + 2) (by omega)
    rw [hz]
    ring
  by_cases hs : WSupported h n m
  · obtain ⟨k, hk⟩ := hs
    have hkpos : 0 < k := by
      by_contra hk0
      have : k = 0 := Nat.eq_zero_of_not_pos hk0
      subst k
      omega
    obtain ⟨ell, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
    have hrec := WHatClosedForm_recurrence_by_pairs
      h r tau n m ell htau hk
    have hkQ :
        ((h * n : ℕ) : ℚ) = (m : ℚ) + (2 * (ell + 1) : ℚ) := by
      exact_mod_cast hk
    have hcast :
        (((h * n : ℕ) : ℚ) - (m : ℚ)) = (2 * (ell + 1) : ℚ) := by
      linarith
    rw [hcast]
    exact hrec
  · have hzero : WHatClosedForm h r tau n m = 0 :=
      WHatClosedForm_eq_zero_of_not_supported h r tau n m hs
    have hsnext : ¬ WSupported h n (m + 2) := by
      rintro ⟨ell, hell⟩
      apply hs
      exact ⟨ell + 1, by omega⟩
    have hzeronext : WHatClosedForm h r tau n (m + 2) = 0 :=
      WHatClosedForm_eq_zero_of_not_supported h r tau n (m + 2) hsnext
    rw [hzero, hzeronext]
    ring

/-- The total disconnected coefficient, parameterized directly by the
number of glued pairs.  It equals `sum_m \widehat W_{n,m}` because every
supported `m` is uniquely `h*n-2*ell`. -/
def WTotalClosedForm (h r tau n : ℕ) : ℚ :=
  ∑ ell ∈ Finset.range (h * n / 2 + 1),
    disconnectedPairingClosedForm h r tau n ell

/-- Expanded finite-sum form used in the Hermite reduction. -/
theorem WTotalClosedForm_eq_sum
    (h r tau n : ℕ) :
    WTotalClosedForm h r tau n =
      1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n) *
        ∑ ell ∈ Finset.range (h * n / 2 + 1),
          ((r : ℚ) / 2) ^ ell *
            ((h * n).factorial : ℚ) /
              ((((h * n - 2 * ell).factorial : ℕ) : ℚ) *
                (ell.factorial : ℚ)) := by
  unfold WTotalClosedForm disconnectedPairingClosedForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  ring


/-- Uniqueness of the supported solution of recurrence (43) from the top
coefficient.  This is the bridge used to identify a concrete groupoid mass
with formula (46). -/
theorem WHatClosedForm_unique
    (h r tau n : ℕ) (htau : 0 < tau)
    (F : ℕ → ℚ)
    (hTop : F (h * n) =
      1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n))
    (hRec : ∀ m ell,
      h * n = m + 2 * (ell + 1) →
        (2 * (ell + 1) : ℚ) * F m =
          (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
            F (m + 2)) :
    ∀ m ell, h * n = m + 2 * ell →
      F m = WHatClosedForm h r tau n m := by
  intro m ell
  induction ell generalizing m with
  | zero =>
      intro hs
      have hm : m = h * n := by omega
      subst m
      rw [hTop, WHatClosedForm_top]
  | succ ell ih =>
      intro hs
      have hsnext : h * n = (m + 2) + 2 * ell := by omega
      have hih := ih (m + 2) hsnext
      have hF := hRec m ell hs
      have hC := WHatClosedForm_recurrence_by_pairs
        h r tau n m ell htau hs
      rw [hih] at hF
      have hcoef : (2 * (ell + 1) : ℚ) ≠ 0 := by positivity
      exact mul_left_cancel₀ hcoef (hF.trans hC.symm)


end
end ExplicitFormulas
end PolytopeCounting
