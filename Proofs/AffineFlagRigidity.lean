module

public import Proofs.RegularFacetRestriction
public import Mathlib.LinearAlgebra.AffineSpace.Basis

@[expose] public section

/-! Geometric flag rigidity from an affine frame.
If a symmetry acts on the affine basis attached to a flag in the expected way,
its image flag determines the symmetry. This supplies the rigidity hypotheses
of the restriction theorem for an affine realization with flag frames. -/

namespace PolytopeCounting.FacetPairing.RegularFacet

variable {G F I V P : Type*} [Group G] [MulAction G F]
variable [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- No rigidity axiom is required once flags carry an equivariant affine frame. -/
theorem affine_flag_rigid (representation : G →* (P ≃ᵃ[ℝ] P))
    (faithful : Function.Injective representation) (flag : F)
    (basis : AffineBasis I ℝ P) (frame : F → I → P)
    (equivariant : ∀ g i, representation g (basis i) = frame (g • flag) i) :
    Function.Injective (fun g : G ↦ g • flag) := by
  intro g k hflag
  change g • flag = k • flag at hflag
  apply faithful
  apply AffineEquiv.ext_on basis.tot
  rintro x ⟨i,rfl⟩
  rw [equivariant, equivariant,hflag]

/-- For a subgroup of actual affine symmetries, faithfulness is automatic. -/
theorem affine_subgroup_flag_rigid (H : Subgroup (P ≃ᵃ[ℝ] P)) [MulAction H F]
    (flag : F) (basis : AffineBasis I ℝ P) (frame : F → I → P)
    (equivariant : ∀ g : H, ∀ i, g.1 (basis i) = frame (g • flag) i) :
    Function.Injective (fun g : H ↦ g • flag) :=
  affine_flag_rigid H.subtype Subtype.val_injective flag basis frame equivariant

end PolytopeCounting.FacetPairing.RegularFacet
