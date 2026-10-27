module

public import Proofs.FacetOrientationCompatibility

@[expose] public section

/-!
# Concrete group actions and the facet-rotation palette

The action on geometric flags is an actual action on finite vertex-subset
chains. The restriction isomorphism supplies a finite palette of genuine
facet rotations and their unique ambient extensions. This palette is for the
facet stabilizer; an orientation-reversing map is not counted as a rotation.

-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry
noncomputable section
open GeometricFlags
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

section Flags
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]
variable {s : Finset E}

theorem symmetry_image_finset (g : symmetryGroup s) : s.image g.1 = s := by
  apply Finset.coe_injective
  simpa only [Finset.coe_image] using image_vertices s g

instance geometricFlagAction : MulAction (symmetryGroup s) (FullFlag s) where
  smul g A := A.map g.1.toAffineMap g.1.injective (symmetry_image_finset g)
  one_smul A := by
    apply Subtype.ext
    change mapChain (fun x : E ↦ x) A.1 = A.1
    simp [mapChain]
  mul_smul g k A := by
    apply Subtype.ext
    change mapChain (fun x ↦ g.1 (k.1 x)) A.1 = mapChain g.1 (mapChain k.1 A.1)
    rw [mapChain_comp]
    rfl

@[simp] theorem geometricFlagAction_tail (g : symmetryGroup s) (A : FullFlag s) :
    (g • A).1 = mapChain g.1 A.1 := rfl

theorem geometricFlagAction_trace (g : symmetryGroup s) (A : FullFlag s) :
    s :: (g • A).1 = mapChain g.1 (s :: A.1) := by
  simp only [mapChain_cons, symmetry_image_finset, geometricFlagAction_tail]

/-- The constructed action satisfies the usual transitivity formulation. -/
theorem flag_pretransitive (regular : IsFlagRegular s) (A B : FullFlag s) :
    ∃ g : symmetryGroup s, g • A = B := by
  obtain ⟨g, hg⟩ := regular A B
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact (List.cons.inj ((geometricFlagAction_trace g A).trans hg)).2

/-- Faithfulness on a single flag follows from its actual face centroids. -/
theorem actual_flag_rigid (span : affineSpan ℝ (s : Set E) = ⊤)
    (A : FullFlag s) : Function.Injective (fun g : symmetryGroup s ↦ g • A) := by
  intro g k he
  have ht : mapChain g.1 (s :: A.1) = mapChain k.1 (s :: A.1) := by
    rw [← geometricFlagAction_trace, ← geometricFlagAction_trace]
    exact congrArg (fun B : FullFlag s ↦ s :: B.1) he
  have hagree := A.maps_agree g.1.toAffineMap k.1.toAffineMap
    g.1.injective k.1.injective ht
  apply Subtype.ext
  ext x
  exact hagree (by rw [span]; trivial)

/-- The actual Euclidean symmetry group acts simply transitively on complete
geometric flags. The finite-group/flag correspondence is now constructed. -/
def symmetryFlagEquiv (span : affineSpan ℝ (s : Set E) = ⊤)
    (regular : IsFlagRegular s) (A : FullFlag s) :
    symmetryGroup s ≃ FullFlag s :=
  Equiv.ofBijective (fun g ↦ g • A)
    ⟨actual_flag_rigid span A, fun B ↦ flag_pretransitive regular A B⟩

theorem fullFlag_card (span : affineSpan ℝ (s : Set E) = ⊤)
    (regular : IsFlagRegular s) (A : FullFlag s) :
    Nat.card (FullFlag s) = Nat.card (symmetryGroup s) :=
  Nat.card_congr (symmetryFlagEquiv span regular A).symm

end Flags

namespace ExposedFacet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {s t : Finset E} (F : ExposedFacet s t)
include F

/-- The actual facet rotation group, formed using its intrinsic determinant. -/
abbrev IntrinsicFacetRotation : Type _ :=
  letI := F.span_nonempty
  (euclideanOrientation (spanVertices t)).ker

/-- The actual cell rotations preserving the given facet. -/
abbrev AmbientFacetRotation (F : ExposedFacet s t) : Type _ :=
  letI := F.span_nonempty
  ((euclideanOrientation s).comp (cellFacetStabilizer s t).subtype).ker

/-- A colour palette constructed from the true finite facet group. No palette
or equality of orders is a premise. -/
def geometricRotationPalette (regular : GeometricFlags.IsFlagRegular s) :
    Fin (Nat.card F.IntrinsicFacetRotation) ≃ F.AmbientFacetRotation := by
  letI := F.span_nonempty
  letI := facetFintype t
  letI : Fintype F.IntrinsicFacetRotation := Fintype.ofFinite _
  have hc : Nat.card F.IntrinsicFacetRotation = Fintype.card F.IntrinsicFacetRotation :=
    Nat.card_eq_fintype_card
  rw [hc]
  exact (Fintype.equivFin F.IntrinsicFacetRotation).symm.trans
    (F.rotationRestrictionEquiv regular).symm.toEquiv

/-- Unique continuation of an orientation-preserving intrinsic facet symmetry
as an orientation-preserving symmetry of the whole polytope. -/
theorem existsUnique_rotation_extension (regular : GeometricFlags.IsFlagRegular s) :
    letI := F.span_nonempty
    ∀ b : (euclideanOrientation (spanVertices t)).ker,
      ∃! g : ((euclideanOrientation s).comp (cellFacetStabilizer s t).subtype).ker,
        facetRestriction s t g.1 = b.1 := by
  letI := F.span_nonempty
  intro b
  let e := F.rotationRestrictionEquiv regular
  refine ⟨e.symm b, ?_, ?_⟩
  · exact congrArg Subtype.val (e.apply_symm_apply b)
  · intro g hg
    apply e.injective
    apply Subtype.ext
    exact hg.trans (congrArg Subtype.val (e.apply_symm_apply b)).symm

/-- Orientation-reversing maps extend with the same negative sign, not with a
positive sign. This separately records the convention relevant to gluings. -/
theorem negative_extension (regular : GeometricFlags.IsFlagRegular s) :
    letI := F.span_nonempty
    ∀ b : symmetryGroup (spanVertices t),
      euclideanOrientation (spanVertices t) b = -1 →
      ∃! g : cellFacetStabilizer s t,
        facetRestriction s t g = b ∧ euclideanOrientation s g.1 = -1 := by
  letI := F.span_nonempty
  intro b hb
  obtain ⟨g, hg, huniq⟩ := F.existsUnique_extension regular b
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · rw [← F.restriction_orientation g, hg, hb]
  · intro k hk
    exact huniq k hk.1

end ExposedFacet
end
end PolytopeCounting.FacetPairing.EuclideanGeometry
