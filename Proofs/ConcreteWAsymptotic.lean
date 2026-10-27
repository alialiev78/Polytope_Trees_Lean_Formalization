module

public import Proofs.ConcreteWTotalHermite
public import Proofs.HermiteAsymptoticReduction

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-! # Transport to the concrete disconnected mass

These reduction lemmas transfer the matching and Stirling estimates to the
finite counts. Their hypotheses are discharged in
`UnconditionalMatchingAsymptotic`.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace ConcreteWAsymptotic

noncomputable section

universe uL
variable {L : Type uL}

/-- The real coercion of the concrete total mass is the real matching sum
used in the asymptotic theorem. -/
theorem WTotalMass_cast_real
    (n h r tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (htau : 0 < tau) :
    ((ConcreteWTotal.WTotalMass L n h r : ℚ) : ℝ) =
      HermiteAsymptotic.disconnectedTotalReal
        h n (r : ℝ) (tau : ℝ) := by
  rw [ConcreteWTotal.WTotalMass_eq_closedForm
      (L := L) n h r tau hcard htau]
  exact HermiteAsymptotic.WTotalClosedForm_cast_real h r tau n

/-- Statement 6.4 formulated directly for the concrete total mass. -/
def ConcreteStatement64
    (L : Type uL) [Group L] [Fintype L]
    (h r tau : ℕ) [MulAction L (Fin h)] : Prop :=
  HermiteAsymptotic.SequenceEquivalent
    (fun n ↦ ((ConcreteWTotal.WTotalMass L n h r : ℚ) : ℝ))
    (fun n ↦ HermiteAsymptotic.statement64LeadingTerm
      h n (r : ℝ) (tau : ℝ))

/-- The closed-form Statement 6.4 immediately gives its concrete-mass
version. -/
theorem concreteStatement64_of_statement64
    (h r tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (htau : 0 < tau)
    (h64 : HermiteAsymptotic.Statement64 h (r : ℝ) (tau : ℝ)) :
    ConcreteStatement64 L h r tau := by
  unfold ConcreteStatement64
  unfold HermiteAsymptotic.Statement64 at h64
  have hfun :
      (fun n ↦ ((ConcreteWTotal.WTotalMass L n h r : ℚ) : ℝ)) =
        (fun n ↦ HermiteAsymptotic.disconnectedTotalReal
          h n (r : ℝ) (tau : ℝ)) := by
    funext n
    exact WTotalMass_cast_real (L := L) n h r tau hcard htau
  rw [hfun]
  exact h64

/-- Conditional completion of Statement 6.4 for the concrete groupoid mass.
No new axiom is introduced: the fixed-imaginary Hermite asymptotic and the
Stirling rewrite are ordinary theorem hypotheses. -/
theorem concreteStatement64_of_hermite_and_stirling
    (h r tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (htau : 0 < tau)
    (hmid : ∀ n,
      HermiteAsymptotic.disconnectedHermiteLeadingTerm
        h n (r : ℝ) (tau : ℝ) ≠ 0)
    (hHermite :
      HermiteAsymptotic.FixedImaginaryHermiteAsymptotic h (r : ℝ))
    (hStirling :
      HermiteAsymptotic.StirlingRewriteForStatement64
        h (r : ℝ) (tau : ℝ)) :
    ConcreteStatement64 L h r tau := by
  apply concreteStatement64_of_statement64
    (L := L) h r tau hcard htau
  exact HermiteAsymptotic.statement64_of_hermite_and_stirling
    h (r : ℝ) (tau : ℝ) (by exact_mod_cast htau.ne')
      hmid hHermite hStirling


end
end ConcreteWAsymptotic
end FacetPairing
end PolytopeCounting
