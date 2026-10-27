module

public import Proofs.MatchingLocalGaussian
public import Proofs.Statement64StirlingExpansion

@[expose] public section

/-!
# The concrete disconnected asymptotic, without an analytic input predicate

The matching estimate is derived via real Poisson weights, a variance bound,
exact parity, Stirling's formula, and a uniform near-mean estimate. It is not
an invocation of a fixed-complex-argument Hermite asymptotic. The old
`FixedImaginaryHermiteAsymptotic` interface is proved as a consequence.

These are source proof scripts; a successful pinned-toolchain build and
kernel audit are required before describing them as machine-checked.
-/

namespace PolytopeCounting.HermiteAsymptotic
noncomputable section
open Filter
open scoped Topology

theorem fixedImaginaryHermiteAsymptotic
    (h : ℕ) (r : ℝ) (hh : 0 < h) (hr : 0 < r) :
    FixedImaginaryHermiteAsymptotic h r := by
  have hm := MatchingSaddle.matching_hermite_asymptotic r hr
  have ht : Tendsto (fun n : ℕ ↦ h*n) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    filter_upwards [eventually_ge_atTop M] with n hn
    have : n ≤ h*n := by
      calc
        n = 1*n := by simp
        _ ≤ h*n := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr hh)
    exact hn.trans this
  exact hm.comp ht

/-- Statement 6.4 with only its explicit positive parameters. -/
theorem statement64_unconditional
    (h : ℕ) (r tau : ℝ) (hh : 0 < h) (hr : 0 < r) (htau : 0 < tau) :
    Statement64 h r tau :=
  statement64_of_hermite h r tau hh hr htau
    (fixedImaginaryHermiteAsymptotic h r hh hr)

end
end PolytopeCounting.HermiteAsymptotic

namespace PolytopeCounting.FacetPairing.ConcreteWAsymptotic
noncomputable section
universe uL

/-- This is the original finite action-groupoid mass, not a sequence defined
by the asymptotic expression. No analytic hypothesis remains in the signature. -/
theorem concreteStatement64_unconditional
    (L : Type uL) [Group L] [Fintype L]
    (h r : ℕ) [MulAction L (Fin h)] (hh : 0 < h) (hr : 0 < r) :
    ConcreteStatement64 L h r (Fintype.card L) := by
  apply concreteStatement64_of_hermite L h r hh hr
  exact HermiteAsymptotic.fixedImaginaryHermiteAsymptotic h (r : ℝ) hh
    (by exact_mod_cast hr)

end
end PolytopeCounting.FacetPairing.ConcreteWAsymptotic
