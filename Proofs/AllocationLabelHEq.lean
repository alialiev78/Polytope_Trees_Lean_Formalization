module

public import Proofs.AllocationNormalization

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Heterogeneous cancellation of allocation label normalization

The recovered image finset is propositionally equal to the stored block,
so its canonical `Fin` target may not be definitionally the same type.  This
lemma packages the exact heterogeneous equality across that card transport.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace AllocationNormalization

noncomputable section

open NumericalBridgeCut

universe uX uI

set_option maxHeartbeats 1000000

/-- Image-normalizing an injective allocated label recovers its original
numerical label, including the dependent equality of the two `Fin` targets. -/
theorem numericalLabel_heq_of_allocation
    {X : Type uX} {I : Type uI}
    [Fintype X] [Fintype I] [DecidableEq I]
    (A : Finset I) (allocated : X ≃ {i : I // i ∈ A})
    (f : X → I) (hf : Function.Injective f)
    (hfe : ∀ x, f x = (allocated x).1) :
    HEq ((equivFinsetImage f hf).trans
          (finsetSubtypeEquivFin (Finset.univ.image f)))
      (allocated.trans (finsetSubtypeEquivFin A)) := by
  have hA : Finset.univ.image f = A :=
    mapImage_eq_allocation A allocated f hfe
  cases hA
  rw [heq_iff_eq]
  apply Equiv.ext
  intro x
  apply (finsetSubtypeEquivFin (Finset.univ.image f)).symm.injective
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  exact hfe x


end
end AllocationNormalization
end FacetPairing
end PolytopeCounting
