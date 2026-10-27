module

public import Proofs.DisconnectedWHat
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Statement 6.6: the pairable-core model and the fixed-core obstruction

The homogeneous recurrence (52) and the factorial expression (53) are
correct for a model in which all `h*n + h₀` ports form one homogeneous pool;
in particular, two ports belonging to the distinguished core may be paired.

For an actual fixed initial complex, whose original boundary facets are not
allowed to be glued to one another, the `n = 0` coefficient is concentrated
at `m = h₀`.  If `h₀ ≥ 2`, this is incompatible with the homogeneous
recurrence (52).  The final theorem in this file records that obstruction
formally, so the two models cannot be conflated.
-/

namespace PolytopeCounting
namespace ExplicitFormulas
namespace RecursiveXi

noncomputable section

/-- Support of the pairable-core coefficient: `ell` is the total number of
pairs among the `h*n + h₀` available ports. -/
def PairableCoreSupported (h h₀ n m : ℕ) : Prop :=
  ∃ ell : ℕ, h * n + h₀ = m + 2 * ell

/-- Formula (53) in the homogeneous/pairable-core interpretation.

`c` is the normalized coefficient of the unpaired core.  The normalization
of the `n` ordinary cells is `n! * tau^n`; the distinguished core is not
permuted with them. -/
noncomputable def pairableCoreXiClosedForm
    (h h₀ r tau : ℕ) (c : ℚ) (n m : ℕ) : ℚ := by
  classical
  exact if hs : PairableCoreSupported h h₀ n m then
    c *
      (1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n)) *
      (((r : ℚ) / 2) ^ Nat.find hs) *
      (((h * n + h₀).factorial : ℚ) /
        ((m.factorial : ℚ) * ((Nat.find hs).factorial : ℚ)))
  else
    0

/-- The number of pairs is unique. -/
theorem PairableCoreSupported_witness_unique
    {h h₀ n m ell k : ℕ}
    (hell : h * n + h₀ = m + 2 * ell)
    (hk : h * n + h₀ = m + 2 * k) :
    ell = k := by
  omega

/-- Supported coefficients are given by the literal factorial expression
from (53). -/
theorem pairableCoreXiClosedForm_eq_of_support
    (h h₀ r tau : ℕ) (c : ℚ) (n m ell : ℕ)
    (hsupport : h * n + h₀ = m + 2 * ell) :
    pairableCoreXiClosedForm h h₀ r tau c n m =
      c *
        (1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n)) *
        (((r : ℚ) / 2) ^ ell) *
        (((h * n + h₀).factorial : ℚ) /
          ((m.factorial : ℚ) * (ell.factorial : ℚ))) := by
  let hs : PairableCoreSupported h h₀ n m := ⟨ell, hsupport⟩
  rw [pairableCoreXiClosedForm, dif_pos hs]
  have hfind := Nat.find_spec hs
  have heq : Nat.find hs = ell :=
    PairableCoreSupported_witness_unique hfind hsupport
  rw [heq]

/-- Unsupported coefficients vanish. -/
theorem pairableCoreXiClosedForm_eq_zero_of_not_supported
    (h h₀ r tau : ℕ) (c : ℚ) (n m : ℕ)
    (hs : ¬ PairableCoreSupported h h₀ n m) :
    pairableCoreXiClosedForm h h₀ r tau c n m = 0 := by
  simp [pairableCoreXiClosedForm, hs]

/-- The maximal free-boundary coefficient is `c/(n! tau^n)`. -/
theorem pairableCoreXiClosedForm_top
    (h h₀ r tau : ℕ) (c : ℚ) (n : ℕ) :
    pairableCoreXiClosedForm h h₀ r tau c n (h * n + h₀) =
      c * (1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n)) := by
  have hfac : (((h * n + h₀).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (h * n + h₀)
  rw [pairableCoreXiClosedForm_eq_of_support
    h h₀ r tau c n (h * n + h₀) 0 (by omega)]
  simp [hfac]

/-- Two-step factorial identity over `ℚ`. -/
private theorem factorial_two_step_cast
    (N : ℕ) (hN : 2 ≤ N) :
    (N.factorial : ℚ) =
      (N : ℚ) * ((N - 1 : ℕ) : ℚ) * ((N - 2).factorial : ℚ) := by
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

/-- Formula (53) satisfies the homogeneous recurrence (52), in the
subtraction-free parameterization where `ell+1` is the number of pairs. -/
theorem pairableCoreXiClosedForm_recurrence_by_pairs
    (h h₀ r tau : ℕ) (c : ℚ) (n m ell : ℕ)
    (htau : 0 < tau)
    (hsupport : h * n + h₀ = m + 2 * (ell + 1)) :
    (2 * (ell + 1) : ℚ) *
        pairableCoreXiClosedForm h h₀ r tau c n m =
      (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        pairableCoreXiClosedForm h h₀ r tau c n (m + 2) := by
  have hnext : h * n + h₀ = (m + 2) + 2 * ell := by omega
  rw [pairableCoreXiClosedForm_eq_of_support
      h h₀ r tau c n m (ell + 1) hsupport,
    pairableCoreXiClosedForm_eq_of_support
      h h₀ r tau c n (m + 2) ell hnext]
  let N : ℕ := m + 2
  have hN : 2 ≤ N := by simp [N]
  have hfac := factorial_two_step_cast N hN
  have hnfac : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have htauQ : (tau : ℚ) ≠ 0 := by exact_mod_cast htau.ne'
  have hellfac : (ell.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero ell
  have hmfac : (m.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  have hEll : ((ell + 1).factorial : ℚ) =
      ((ell + 1 : ℕ) : ℚ) * (ell.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ ell
  have hNfac : ((m + 2).factorial : ℚ) =
      ((m + 2 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ) *
        (m.factorial : ℚ) := by
    simpa [N] using hfac
  rw [pow_succ, hEll, hNfac]
  field_simp [hnfac, htauQ, hellfac, hmfac]
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

/-- Literal form of recurrence (52). -/
theorem pairableCoreXiClosedForm_recurrence
    (h h₀ r tau : ℕ) (c : ℚ) (n m ell : ℕ)
    (htau : 0 < tau)
    (hsupport : h * n + h₀ = m + 2 * (ell + 1)) :
    (((h * n + h₀ : ℕ) : ℚ) - (m : ℚ)) *
        pairableCoreXiClosedForm h h₀ r tau c n m =
      (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        pairableCoreXiClosedForm h h₀ r tau c n (m + 2) := by
  have hdiff :
      (((h * n + h₀ : ℕ) : ℚ) - (m : ℚ)) =
        (2 * (ell + 1) : ℚ) := by
    have hmle : m ≤ h * n + h₀ := by omega
    rw [← Nat.cast_sub hmle]
    exact_mod_cast (show h * n + h₀ - m = 2 * (ell + 1) by omega)
  rw [hdiff]
  exact pairableCoreXiClosedForm_recurrence_by_pairs
    h h₀ r tau c n m ell htau hsupport

/-- The homogeneous formula creates a core--core pair already at `n=0`.
This is the first lower coefficient and is precisely the obstruction to
interpreting (53) as a formula for a fixed, unmodified initial complex. -/
theorem pairableCoreXiClosedForm_zero_two_less
    (h h₀ r tau : ℕ) (c : ℚ)
    (hh₀ : 2 ≤ h₀) (htau : 0 < tau) :
    pairableCoreXiClosedForm h h₀ r tau c 0 (h₀ - 2) =
      c * ((r : ℚ) / 2) *
        ((h₀.factorial : ℚ) /
          (((h₀ - 2).factorial : ℚ))) := by
  have hs : h * 0 + h₀ = (h₀ - 2) + 2 * 1 := by omega
  rw [pairableCoreXiClosedForm_eq_of_support
    h h₀ r tau c 0 (h₀ - 2) 1 hs]
  simp [htau.ne']

/-- A coefficient family has the fixed-core base condition if at `n=0` it
is concentrated at the original number `h₀` of free core facets. -/
def HasFixedCoreBase (h₀ : ℕ) (c : ℚ) (Xi : ℕ → ℕ → ℚ) : Prop :=
  ∀ m, Xi 0 m = if m = h₀ then c else 0

/-- The homogeneous recurrence (52) is incompatible with the fixed-core
base condition as soon as `h₀ ≥ 2` and the core and gluing weights are
nonzero.  Thus (52)--(53) cannot simultaneously describe an unmodified
fixed core and all `n ≥ 0` coefficients. -/
theorem no_fixed_core_base_with_homogeneous_recurrence
    (h h₀ : ℕ) (r c : ℚ) (Xi : ℕ → ℕ → ℚ)
    (hh₀ : 2 ≤ h₀)
    (hr : r ≠ 0) (hc : c ≠ 0)
    (hbase : HasFixedCoreBase h₀ c Xi)
    (hrec : ∀ n m : ℕ,
      (((h * n + h₀ : ℕ) : ℚ) - (m : ℚ)) * Xi n m =
        r * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) * Xi n (m + 2)) :
    False := by
  have hlow : Xi 0 (h₀ - 2) = 0 := by
    rw [hbase (h₀ - 2)]
    simp [show h₀ - 2 ≠ h₀ by omega]
  have htop : Xi 0 h₀ = c := by
    rw [hbase h₀]
    simp
  have h := hrec 0 (h₀ - 2)
  rw [hlow] at h
  have hplus : h₀ - 2 + 2 = h₀ := by omega
  rw [hplus, htop] at h
  have h₀Q : ((h₀ - 2 + 1 : ℕ) : ℚ) ≠ 0 := by
    positivity
  have h₀Q' : (h₀ : ℚ) ≠ 0 := by
    positivity
  have hprod :
      r * ((h₀ - 2 + 1 : ℕ) : ℚ) * (h₀ : ℚ) * c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hr h₀Q) h₀Q') hc
  apply hprod
  simpa [mul_assoc] using h.symm


end
end RecursiveXi
end ExplicitFormulas
end PolytopeCounting
