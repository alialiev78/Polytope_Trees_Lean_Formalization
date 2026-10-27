module

public import Proofs.GeometricFlagTransport
public import Proofs.ExposedFacetRigidity

@[expose] public section

/-!
# Surjectivity of actual Euclidean facet restriction

For a finite full-dimensional flag-transitive polytope and an exposed facet,
every intrinsic Euclidean facet symmetry extends uniquely. The proof uses the
constructed supporting-face flags, their existence and centroid rigidity. The
input contains no assumed surjectivity, flag frame, or abstract action-system.

-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry
noncomputable section
open GeometricFlags
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {s t : Finset E}

namespace ExposedFacet
variable (F : ExposedFacet s t)
include F

/-- Any point off the supporting hyperplane completes the affine span. -/
theorem span_insert_of_off_plane {c : E} (hc : F.support c ≠ F.level) :
    affineSpan ℝ (insert c (t : Set E)) = ⊤ := by
  let A := affineSpan ℝ (insert c (t : Set E))
  obtain ⟨p, hp⟩ := F.nonempty
  have hpval := ((F.vertices p).mp hp).2
  have hden : F.support c - F.level ≠ 0 := sub_ne_zero.mpr hc
  have hcA : c ∈ A := subset_affineSpan ℝ _ (Set.mem_insert _ _)
  have hmono : affineSpan ℝ (t : Set E) ≤ A :=
    affineSpan_mono ℝ (Set.subset_insert c (t : Set E))
  have hpA : p ∈ A := hmono (subset_affineSpan ℝ _ hp)
  apply top_unique
  intro x _
  let a := (F.support x - F.level) / (F.support c - F.level)
  let y := x - a • (c - p)
  have hyval : F.support y = F.level := by
    dsimp [y]
    simp only [map_sub, map_smul, hpval, smul_eq_mul]
    dsimp [a]
    field_simp [hden]
    ring
  have hyA : y ∈ A := hmono ((F.span y).mpr hyval)
  have hxA := A.smul_vsub_vadd_mem a hcA hpA hyA
  have he : a • (c -ᵥ p) +ᵥ y = x := by
    change a • (c - p) + (x - a • (c - p)) = x
    abel
  exact he ▸ hxA

/-- Full affine span follows from the exposed-facet data already in the base. -/
theorem parent_span : affineSpan ℝ (s : Set E) = ⊤ := by
  apply top_unique
  rw [← F.span_with_centroid]
  apply affineSpan_le.mpr
  intro x hx
  rcases hx with rfl | hx
  · exact GeometricFlags.centroid_mem_span s F.cell_nonempty
  · exact subset_affineSpan ℝ _ (((F.vertices x).mp hx).1)

/-- The supporting-hyperplane facet in the existing project is a maximal
supporting face in the concrete geometric face lattice. -/
theorem isFacet : GeometricFlags.Facet s t := by
  let f : E →ᵃ[ℝ] ℝ := F.support.toAffineMap - AffineMap.const ℝ E F.level
  have ht : Supported s t := by
    refine ⟨F.nonempty, f, ?_, ?_, ?_⟩
    · intro x hx
      exact sub_nonpos.mpr (F.below x hx)
    · intro x
      simpa [f, sub_eq_zero] using F.vertices x
    · obtain ⟨x, hx, hlt⟩ := F.proper
      exact ⟨x, hx, sub_neg.mpr hlt⟩
  refine ⟨ht, ?_⟩
  intro u hu htu
  apply Finset.Subset.antisymm
  · intro x hxu
    by_contra hxt
    have hxs := hu.subset hxu
    have hne : F.support x ≠ F.level := by
      intro he
      exact hxt ((F.vertices x).mpr ⟨hxs, he⟩)
    have hspan : affineSpan ℝ (u : Set E) = ⊤ := by
      apply top_unique
      rw [← F.span_insert_of_off_plane hne]
      apply affineSpan_mono ℝ
      intro y hy
      rcases hy with rfl | hy
      · exact hxu
      · exact htu hy
    rcases hu with ⟨_, a, _, hv, z, hz, hlt⟩
    have hagree : Set.EqOn a (AffineMap.const ℝ E 0) (u : Set E) := by
      intro y hy
      exact ((hv y).mp hy).2
    have hzero := AffineMap.eqOn_affineSpan hagree
    have hzspan : z ∈ affineSpan ℝ (u : Set E) := by rw [hspan]; trivial
    have := hzero hzspan
    change a z = 0 at this
    linarith
  · exact htu

/-- The intrinsic facet vertices, included into ambient space, are exactly t. -/
theorem image_intrinsic_vertices :
    letI := F.span_nonempty
    (spanVertices t).image (Subtype.val : affineSpan ℝ (t : Set E) → E) = t := by
  letI := F.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set E)) := Classical.decEq _
  apply Finset.coe_injective
  simpa only [Finset.coe_image] using image_spanVertices t

/-- Extension of every actual intrinsic facet isometry from ordinary geometric
flag regularity. No extra rigidity or extension input is used. -/
theorem restriction_surjective (regular : GeometricFlags.IsFlagRegular s) :
    letI := F.span_nonempty
    Function.Surjective (facetRestriction s t) := by
  letI := F.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set E)) := Classical.decEq _
  let T := affineSpan ℝ (t : Set E)
  let sv := spanVertices t
  let inclusion : T →ᵃ[ℝ] E := T.subtype
  have hi : Function.Injective inclusion := Subtype.val_injective
  have hsv : sv.Nonempty := by
    obtain ⟨x, hx⟩ := F.nonempty
    exact ⟨⟨x, subset_affineSpan ℝ _ hx⟩, (mem_spanVertices t _).mpr hx⟩
  have him : sv.image inclusion = t := F.image_intrinsic_vertices
  obtain ⟨A⟩ := fullFlag_nonempty sv hsv
  intro b
  have hbim : sv.image b.1 = sv := by
    apply Finset.coe_injective
    simpa only [Finset.coe_image] using image_vertices sv b
  let B : FullFlag sv := A.map b.1.toAffineMap b.1.injective (by simpa using hbim)
  let A' : FullFlag t := A.map inclusion hi him
  let B' : FullFlag t := B.map inclusion hi him
  let AF : FullFlag s := ⟨t :: A'.1, CompleteChain.step F.isFacet A'.2⟩
  let BF : FullFlag s := ⟨t :: B'.1, CompleteChain.step F.isFacet B'.2⟩
  obtain ⟨g, hg⟩ := regular AF BF
  have htail : mapChain g.1 (t :: A'.1) = t :: B'.1 := (List.cons.inj hg).2
  have htimage : t.image g.1 = t := (List.cons.inj htail).1
  have hgt : ∀ x, g.1 x ∈ t ↔ x ∈ t :=
    preserves_finset_of_image g.1 g.1.injective htimage
  let a : cellFacetStabilizer s t := ⟨g, hgt⟩
  refine ⟨a, ?_⟩
  let f₁ : T →ᵃ[ℝ] E := g.1.toAffineMap.comp inclusion
  let f₂ : T →ᵃ[ℝ] E := inclusion.comp b.1.toAffineMap
  have hf₁ : Function.Injective f₁ := g.1.injective.comp hi
  have hf₂ : Function.Injective f₂ := hi.comp b.1.injective
  have hmaps : mapChain f₁ (sv :: A.1) = mapChain f₂ (sv :: A.1) := by
    have hwhole : mapChain g.1 (mapChain inclusion (sv :: A.1)) =
        mapChain inclusion (mapChain b.1 (sv :: A.1)) := by
      simpa [mapChain_cons, him, hbim, A', B', B, FullFlag.map] using htail
    simp only [mapChain_comp] at hwhole
    convert hwhole using 1 <;> rfl
  have heq := A.maps_agree f₁ f₂ hf₁ hf₂ hmaps
  apply Subtype.ext
  ext x : 1
  apply Subtype.ext
  have hx : x ∈ affineSpan ℝ (sv : Set T) := by rw [spanVertices_span t]; trivial
  exact heq hx

/-- Compatibility with the actual face action is a consequence of the
pointwise formula for restriction. It is not extra input to the extension. -/
theorem restriction_flag_compatible :
    letI := F.span_nonempty
    ∀ (g : cellFacetStabilizer s t)
      (l : List (Finset (affineSpan ℝ (t : Set E)))),
      mapChain (Subtype.val : affineSpan ℝ (t : Set E) → E)
        (mapChain (facetRestriction s t g).1 l) =
      mapChain g.1.1
        (mapChain (Subtype.val : affineSpan ℝ (t : Set E) → E) l) := by
  letI := F.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set E)) := Classical.decEq _
  intro g l
  rw [mapChain_comp, mapChain_comp]
  apply congrArg (fun f : affineSpan ℝ (t : Set E) → E ↦ mapChain f l)
  funext x
  exact facetRestriction_apply s t g x

/-- The facet is itself geometrically regular in its own affine space. -/
theorem intrinsic_regular (regular : GeometricFlags.IsFlagRegular s) :
    letI := F.span_nonempty
    GeometricFlags.IsFlagRegular (spanVertices t) := by
  letI := F.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set E)) := Classical.decEq _
  let T := affineSpan ℝ (t : Set E)
  let sv := spanVertices t
  let inclusion : T →ᵃ[ℝ] E := T.subtype
  have hi : Function.Injective inclusion := Subtype.val_injective
  have him : sv.image inclusion = t := F.image_intrinsic_vertices
  intro A B
  let A' : FullFlag t := A.map inclusion hi him
  let B' : FullFlag t := B.map inclusion hi him
  let AF : FullFlag s := ⟨t :: A'.1, CompleteChain.step F.isFacet A'.2⟩
  let BF : FullFlag s := ⟨t :: B'.1, CompleteChain.step F.isFacet B'.2⟩
  obtain ⟨g, hg⟩ := regular AF BF
  have htail : mapChain g.1 (t :: A'.1) = t :: B'.1 := (List.cons.inj hg).2
  have htimage : t.image g.1 = t := (List.cons.inj htail).1
  let a : cellFacetStabilizer s t :=
    ⟨g, preserves_finset_of_image g.1 g.1.injective htimage⟩
  refine ⟨facetRestriction s t a, ?_⟩
  apply mapChain_injective inclusion hi
  have hc := F.restriction_flag_compatible a (sv :: A.1)
  change mapChain inclusion (mapChain (facetRestriction s t a).1 (sv :: A.1)) =
    mapChain g.1 (mapChain inclusion (sv :: A.1)) at hc
  exact hc.trans (by simpa only [mapChain_cons, ← him, A', B', FullFlag.map] using htail)

/-- The missing group isomorphism, now with concrete geometric hypotheses. -/
def restrictionEquiv (regular : GeometricFlags.IsFlagRegular s) :
    letI := F.span_nonempty
    cellFacetStabilizer s t ≃* symmetryGroup (spanVertices t) := by
  letI := F.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set E)) := Classical.decEq _
  exact MulEquiv.ofBijective (facetRestriction s t)
    ⟨F.restriction_injective, F.restriction_surjective regular⟩

/-- Existence and uniqueness expressed without group-isomorphism terminology. -/
theorem existsUnique_extension (regular : GeometricFlags.IsFlagRegular s) :
    letI := F.span_nonempty
    ∀ b : symmetryGroup (spanVertices t),
      ∃! g : cellFacetStabilizer s t, facetRestriction s t g = b := by
  letI := F.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set E)) := Classical.decEq _
  intro b
  obtain ⟨g, hg⟩ := F.restriction_surjective regular b
  exact ⟨g, hg, fun k hk ↦ F.restriction_injective (hk.trans hg.symm)⟩

end ExposedFacet
end
end PolytopeCounting.FacetPairing.EuclideanGeometry
