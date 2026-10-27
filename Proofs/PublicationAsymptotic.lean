module

public import Proofs.UnconditionalMatchingAsymptotic
public import Solution

@[expose] public section

/-! # Statement 6.4 directly in the public finite-carrier notation -/

namespace PolytopeTrees
noncomputable section
open PolytopeCounting PolytopeCounting.FacetPairing
universe u

/-- Sum over all supported free-boundary sizes; the mass comes from the finite
carrier `W`, and the ratio to the displayed leading term tends to one. -/
theorem W_total_asymptotic (L : Type u) [Group L] [Fintype L]
    (h r : ℕ) [MulAction L (Fin h)] (hh : 0 < h) (hr : 0 < r) :
    HermiteAsymptotic.SequenceEquivalent
      (fun n ↦ ((∑ e ∈ Finset.range (h * n / 2 + 1),
        W L n h r (h * n - 2 * e) : ℚ) : ℝ))
      (fun n ↦ HermiteAsymptotic.statement64LeadingTerm
        h n (r : ℝ) (Fintype.card L : ℝ)) := by
  have H := ConcreteWAsymptotic.concreteStatement64_unconditional L h r hh hr
  change HermiteAsymptotic.SequenceEquivalent
    (fun n ↦ (ConcreteWTotal.WTotalMass L n h r : ℝ)) _ at H
  simpa only [ConcreteWTotal.WTotalMass, W_eq_mass] using H

end
end PolytopeTrees
