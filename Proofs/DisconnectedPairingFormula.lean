module

public import Proofs.ClosedFormArithmetic
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Closed formula for possibly disconnected facet pairings

For `D = h*n` total facets and `ell` glued pairs, the number of free facets
is `m = D - 2*ell`.  This file formalizes formula (46) in the equivalent,
subtraction-safe `ell`-parameterization and proves its coefficient
recurrence and top boundary value.
-/

namespace PolytopeCounting
namespace ExplicitFormulas

noncomputable section

/-- Formula (46), parameterized by the number `ell` of glued facet pairs.
It corresponds to `m = h*n - 2*ell`. -/
def disconnectedPairingClosedForm
    (h r tau n ell : ℕ) : ℚ :=
  1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n) *
    ((r : ℚ) / 2) ^ ell *
    ((h * n).factorial : ℚ) /
      ((((h * n - 2 * ell).factorial : ℕ) : ℚ) *
        (ell.factorial : ℚ))

/-- No gluing gives the top coefficient `1/(n! tau^n)`. -/
theorem disconnectedPairingClosedForm_zero
    (h r tau n : ℕ) :
    disconnectedPairingClosedForm h r tau n 0 =
      1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n) := by
  have hfac : (((h * n).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (h * n)
  unfold disconnectedPairingClosedForm
  simp [hfac]

/-- Two-step factorial identity used by the recurrence proof. -/
private theorem factorial_two_step
    (N : ℕ) (hN : 2 ≤ N) :
    (N.factorial : ℚ) =
      (N : ℚ) * (N - 1 : ℕ) * ((N - 2).factorial : ℚ) := by
  have hN0 : N ≠ 0 := by omega
  have hN10 : N - 1 ≠ 0 := by omega
  have h1 : N * (N - 1).factorial = N.factorial :=
    Nat.mul_factorial_pred hN0
  have h2 : (N - 1) * (N - 2).factorial = (N - 1).factorial := by
    have hpred : N - 1 - 1 = N - 2 := by omega
    simpa only [hpred] using Nat.mul_factorial_pred hN10
  have h1Q :
      (N : ℚ) * ((N - 1).factorial : ℚ) = (N.factorial : ℚ) := by
    exact_mod_cast h1
  have h2Q :
      ((N - 1 : ℕ) : ℚ) * ((N - 2).factorial : ℚ) =
        ((N - 1).factorial : ℚ) := by
    exact_mod_cast h2
  rw [← h1Q, ← h2Q]
  ring

/-- Formula (46) satisfies recurrence (43), written with
`m = h*n - 2*(ell+1)` and `m+2 = h*n - 2*ell`.

This is exactly

`(h*n-m) W[n,m] = r (m+1)(m+2) W[n,m+2]`.
-/
theorem disconnectedPairingClosedForm_recurrence
    (h r tau n ell : ℕ)
    (htau : 0 < tau)
    (hell : 2 * (ell + 1) ≤ h * n) :
    (2 * (ell + 1) : ℚ) *
        disconnectedPairingClosedForm h r tau n (ell + 1) =
      (r : ℚ) *
        ((h * n - 2 * ell - 1 : ℕ) : ℚ) *
        ((h * n - 2 * ell : ℕ) : ℚ) *
        disconnectedPairingClosedForm h r tau n ell := by
  let N : ℕ := h * n - 2 * ell
  have hN : 2 ≤ N := by
    dsimp [N]
    omega
  have hshift : h * n - 2 * (ell + 1) = N - 2 := by
    dsimp [N]
    omega
  have hNm1 : h * n - 2 * ell - 1 = N - 1 := by
    dsimp [N]
  have hNdef : h * n - 2 * ell = N := by rfl
  have hfacN := factorial_two_step N hN
  have hfacEllNat : (ell + 1).factorial = (ell + 1) * ell.factorial :=
    Nat.factorial_succ ell
  have hfacEllQ :
      ((ell + 1).factorial : ℚ) =
        ((ell + 1 : ℕ) : ℚ) * (ell.factorial : ℚ) := by
    exact_mod_cast hfacEllNat
  have hnfac : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have htauQ : (tau : ℚ) ≠ 0 := by exact_mod_cast htau.ne'
  have hellfac : (ell.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero ell
  have hN2fac : ((N - 2).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (N - 2)
  have hNm1Q : ((N - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show N - 1 ≠ 0 by omega)
  unfold disconnectedPairingClosedForm
  rw [hshift, hNm1, hNdef, pow_succ, hfacEllQ, hfacN]
  field_simp [hnfac, htauQ, hellfac, hN2fac, hNm1Q]
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

/-- The same recurrence with the free-facet variable displayed explicitly. -/
theorem disconnectedPairing_formula46_recurrence
    (h r tau n ell : ℕ)
    (htau : 0 < tau)
    (hell : 2 * (ell + 1) ≤ h * n) :
    let m := h * n - 2 * (ell + 1)
    ((h * n - m : ℕ) : ℚ) *
        disconnectedPairingClosedForm h r tau n (ell + 1) =
      (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        disconnectedPairingClosedForm h r tau n ell := by
  dsimp
  have hleft : h * n - (h * n - 2 * (ell + 1)) = 2 * (ell + 1) := by
    omega
  have hm1 : h * n - 2 * (ell + 1) + 1 = h * n - 2 * ell - 1 := by
    omega
  have hm2 : h * n - 2 * (ell + 1) + 2 = h * n - 2 * ell := by
    omega
  rw [hleft, hm1, hm2]
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
    (disconnectedPairingClosedForm_recurrence h r tau n ell htau hell)

/-- Formula (46) in the literal free-facet notation, under an explicit
witness `h*n = m + 2*ell` of the parity/support condition. -/
theorem disconnectedPairing_formula46
    (h r tau n m ell : ℕ)
    (hsupport : h * n = m + 2 * ell) :
    disconnectedPairingClosedForm h r tau n ell =
      1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n) *
        ((r : ℚ) / 2) ^ ell *
        ((h * n).factorial : ℚ) /
          ((m.factorial : ℚ) * (ell.factorial : ℚ)) := by
  unfold disconnectedPairingClosedForm
  have hm : h * n - 2 * ell = m := by omega
  rw [hm]


end
end ExplicitFormulas
end PolytopeCounting
