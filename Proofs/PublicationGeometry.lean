module

public import Proofs.EuclideanFacetTransporters

@[expose] public section

/-! # A pointwise statement of the geometric extension theorem

This interface states unique extension without mentioning the constructed
transporter system. Both source and target are the actual affine facet spaces.
-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell
noncomputable section
open GeometricFlags
attribute [local instance] Classical.propDecidable Classical.decEq

universe u
variable {V P : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]

/-- Every vertex-preserving intrinsic facet isometry has exactly one ambient
cell symmetry extending it, for every ordered pair of actual facets. -/
theorem facet_isometry_extends_uniquely (K : RegularCell V P)
    (i j : Fin K.h) (f : K.IntrinsicMap i j) :
    ∃! g : K.Group, ∀ x : K.FacetSpace i, (f.1 x : P) = g.1 x := by
  obtain ⟨g, hg⟩ := K.transportToMap_surjective i j f
  have hext : ∀ x : K.FacetSpace i, (f.1 x : P) = g.1.1 x := by
    intro x
    exact (congrArg (fun a : K.IntrinsicMap i j ↦ (a.1 x : P)) hg).symm
  refine ⟨g.1, hext, ?_⟩
  intro k hk
  apply Subtype.ext
  apply AffineIsometryEquiv.toAffineEquiv_injective
  apply AffineEquiv.ext_on ((K.facet_property i).span_with_centroid.trans K.full_span)
  intro x hx
  rcases hx with rfl | hx
  · exact (centroid_fixed K.vertices K.nonempty k).trans
      (centroid_fixed K.vertices K.nonempty g.1).symm
  · let x' : K.FacetSpace i := ⟨x, subset_affineSpan ℝ _ hx⟩
    exact (hk x').symm.trans (hext x')

end
end PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell
