module

public import Proofs.RegularPresentationMass
public import Proofs.AffineFlagRigidity

@[expose] public section

/-!
# Counting with the actual facet rotation parameter

The signed flag and restriction hypotheses are geometric input data. Neither
a finite palette nor bijectivity of restriction nor the relation tau = h*r
is assumed. They are conclusions of the preceding modules.

This is not an unconditional instantiation of all Euclidean regular polytopes:
constructing these input data from a convex polytope is outside this module.
-/

namespace PolytopeCounting.FacetPairing.RegularFacet.OrientedFlags
noncomputable section
attribute [local instance] Classical.propDecidable

variable {G F : Type} [Group G] [Fintype G] [MulAction G F] {h : ℕ}
variable (R : OrientedFlags G F h)
variable {B : Type} [Group B] [Fintype B] [MulAction B R.FacetFlags]
variable (restriction : R.stabilizer →* B)
variable (compatible : ∀ g, restriction g • R.facetBase = g • R.facetBase)
variable (cell_rigid : Function.Injective (fun g : G ↦ g • R.base))
variable (facet_rigid : Function.Injective (fun b : B ↦ b • R.facetBase))
variable (signB : B →* ℤˣ)
variable (orientation : ∀ g, signB (restriction g) = R.orientation g.1)

include restriction compatible cell_rigid facet_rigid orientation

/-- The combinatorial colour count equals the actual facet rotation order. -/
theorem facet_rotation_card :
    Fintype.card R.toSystem.facetRotation = Fintype.card signB.ker :=
  Fintype.card_congr
    (R.facetRotationEquiv restriction compatible cell_rigid facet_rigid signB orientation).toEquiv

/-- The article's relation tau = h*r, with the facet group parameter. -/
theorem cell_rotation_card :
    Fintype.card R.toSystem.Rotation = h * Fintype.card signB.ker := by
  rw [R.rotation_card,
    R.facet_rotation_card restriction compatible cell_rigid facet_rigid signB orientation]

/-- Boundary mass equals the original W with r supplied by the facet group. -/
theorem boundary_mass_eq_W (n m : ℕ) :
    ActionGroupoid.mass (RegularPresentation.Frames R.toSystem (Fin n))
      (RegularPresentation.BoundaryPresentations R.toSystem n m) ℚ =
      PolytopeTrees.W R.toSystem.Rotation n h (Fintype.card signB.ker) m := by
  rw [RegularPresentation.geometric_boundary_mass_eq_W,
    R.facet_rotation_card restriction compatible cell_rigid facet_rigid signB orientation]

end
end PolytopeCounting.FacetPairing.RegularFacet.OrientedFlags
