module

public import Proofs.ConcreteGeometricFlagInterface
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

/-!
# Restriction for every actual supporting facet

This module removes the need to supply `ExposedFacet` certificates separately
for each facet. Facets are the maximal proper supporting vertex sets already
used by `GeometricFlags.IsFlagRegular`. The supporting hyperplane, intrinsic
restriction isomorphism, and determinant compatibility are derived.

-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry.GeometricFlags
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]
variable {s t : Finset P}

namespace Facet

/-- A normalized exposing affine functional; its choice is not extra data. -/
def form (H : Facet s t) : P →ᵃ[ℝ] ℝ := Classical.choose H.1.2

theorem form_below (H : Facet s t) : ∀ x ∈ s, H.form x ≤ 0 :=
  (Classical.choose_spec H.1.2).1

theorem form_vertices (H : Facet s t) (x : P) :
    x ∈ t ↔ x ∈ s ∧ H.form x = 0 :=
  (Classical.choose_spec H.1.2).2.1 x

theorem form_proper (H : Facet s t) : ∃ x ∈ s, H.form x < 0 :=
  (Classical.choose_spec H.1.2).2.2

theorem form_centroid_neg (H : Facet s t) : H.form (s.centroid ℝ id) < 0 :=
  supporting_centroid_strict H.1.parent_nonempty H.form H.form_below H.form_proper

theorem span_nonempty (H : Facet s t) : Nonempty (affineSpan ℝ (t : Set P)) := by
  obtain ⟨p, hp⟩ := H.1.1
  exact ⟨⟨p, subset_affineSpan ℝ _ hp⟩⟩

/-- The affine span of a maximal supporting face is exactly its supporting
hyperplane within the parent's affine span. No codimension hypothesis is used. -/
theorem relative_span (H : Facet s t) (x : P) :
    x ∈ affineSpan ℝ (t : Set P) ↔
      x ∈ affineSpan ℝ (s : Set P) ∧ H.form x = 0 := by
  constructor
  · intro hx
    refine ⟨affineSpan_mono ℝ (show (t : Set P) ⊆ s from H.1.subset) hx, ?_⟩
    have hz : Set.EqOn H.form (AffineMap.const ℝ P (0 : ℝ))
        (affineSpan ℝ (t : Set P)) := by
      apply AffineMap.eqOn_affineSpan
      intro y hy
      exact ((H.form_vertices y).mp hy).2
    exact hz hx
  · rintro ⟨hxs, hfx⟩
    by_contra hxt
    obtain ⟨p, hp⟩ := H.1.1
    obtain ⟨q, hq, hqx⟩ := separate_affine_subspace
      (affineSpan ℝ (t : Set P)) (subset_affineSpan ℝ _ hp) hxt
    let c := s.centroid ℝ id
    have hfc : H.form c ≠ 0 := ne_of_lt H.form_centroid_neg
    let k : P →ᵃ[ℝ] ℝ := q - (q c / H.form c) • H.form
    have hk : Set.EqOn k (AffineMap.const ℝ P (0 : ℝ))
        (affineSpan ℝ (insert c (t : Set P))) := by
      apply AffineMap.eqOn_affineSpan
      intro y hy
      rcases hy with rfl | hy
      · change q c - (q c / H.form c) * H.form c = 0
        field_simp [hfc]
        ring
      · have hqy := hq y (subset_affineSpan ℝ _ hy)
        have hfy := ((H.form_vertices y).mp hy).2
        simp [k, hqy, hfy]
    have hx' : x ∈ affineSpan ℝ (insert c (t : Set P)) := by
      rw [H.span_with_centroid]
      exact hxs
    have hkx := hk hx'
    change q x - (q c / H.form c) * H.form x = 0 at hkx
    rw [hfx, mul_zero, sub_zero] at hkx
    linarith

/-- The usual supporting-hyperplane equation for a full-dimensional parent. -/
theorem span_iff (H : Facet s t) (span : affineSpan ℝ (s : Set P) = ⊤) (x : P) :
    x ∈ affineSpan ℝ (t : Set P) ↔ H.form x = 0 := by
  rw [H.relative_span, span]
  simp

/-- The normal form is nonzero, and its kernel is the actual facet direction. -/
theorem direction_iff (H : Facet s t)
    (span : affineSpan ℝ (s : Set P) = ⊤) (w : V) :
    w ∈ (affineSpan ℝ (t : Set P)).direction ↔ H.form.linear w = 0 := by
  obtain ⟨p, hp⟩ := H.1.1
  have hpT := subset_affineSpan ℝ (t : Set P) hp
  have hp0 := ((H.form_vertices p).mp hp).2
  constructor
  · intro hw
    have hy := (affineSpan ℝ (t : Set P)).vadd_mem_of_mem_direction hw hpT
    have hf := (H.span_iff span (w +ᵥ p)).mp hy
    rw [H.form.map_vadd, hp0, vadd_eq_add, add_zero] at hf
    exact hf
  · intro hw
    have hy : w +ᵥ p ∈ affineSpan ℝ (t : Set P) := by
      rw [H.span_iff span, H.form.map_vadd, hp0, hw]
      simp
    simpa using (affineSpan ℝ (t : Set P)).vsub_mem_direction hy hpT

/-- Full-dimensional facets have codimension one, proved from the explicit
transverse splitting rather than assumed in `Facet`. -/
theorem direction_finrank [FiniteDimensional ℝ V] (H : Facet s t)
    (span : affineSpan ℝ (s : Set P) = ⊤) :
    Module.finrank ℝ V =
      Module.finrank ℝ (affineSpan ℝ (t : Set P)).direction + 1 := by
  obtain ⟨p, hp⟩ := H.1.1
  let v := s.centroid ℝ id -ᵥ p
  have hp0 := ((H.form_vertices p).mp hp).2
  have hv : H.form.linear v ≠ 0 := by
    change H.form.linear (s.centroid ℝ id -ᵥ p) ≠ 0
    rw [H.form.linearMap_vsub, hp0, vsub_eq_sub, sub_zero]
    exact ne_of_lt H.form_centroid_neg
  let e := splitTransverse (affineSpan ℝ (t : Set P)).direction
    H.form.linear (H.direction_iff span) v hv
  have he := e.finrank_eq
  simpa using he.symm

/-- Inclusion of intrinsic facet vertices retains exactly the original vertex set. -/
theorem image_intrinsic_vertices (H : Facet s t) :
    letI := H.span_nonempty
    (spanVertices t).image (Subtype.val : affineSpan ℝ (t : Set P) → P) = t := by
  letI := H.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set P)) := Classical.decEq _
  apply Finset.coe_injective
  simpa only [Finset.coe_image] using image_spanVertices t

theorem intrinsic_card (H : Facet s t) :
    letI := H.span_nonempty
    (spanVertices t).card = t.card := by
  letI := H.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set P)) := Classical.decEq _
  have hi := Finset.card_image_of_injective (spanVertices t)
    (Subtype.val_injective : Function.Injective
      (Subtype.val : affineSpan ℝ (t : Set P) → P))
  rw [H.image_intrinsic_vertices] at hi
  exact hi.symm

/-- Flag regularity descends to the actual affine span of each facet. -/
theorem intrinsic_regular (H : Facet s t) (regular : IsFlagRegular s) :
    letI := H.span_nonempty
    IsFlagRegular (spanVertices t) := by
  letI := H.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set P)) := Classical.decEq _
  let T := affineSpan ℝ (t : Set P)
  let sv := spanVertices t
  let inclusion : T →ᵃ[ℝ] P := T.subtype
  have hi : Function.Injective inclusion := Subtype.val_injective
  have him : sv.image inclusion = t := H.image_intrinsic_vertices
  intro A B
  let A' : FullFlag t := A.map inclusion hi him
  let B' : FullFlag t := B.map inclusion hi him
  let AF : FullFlag s := ⟨t :: A'.1, CompleteChain.step H A'.2⟩
  let BF : FullFlag s := ⟨t :: B'.1, CompleteChain.step H B'.2⟩
  obtain ⟨g, hg⟩ := regular AF BF
  have htail : mapChain g.1 (t :: A'.1) = t :: B'.1 := (List.cons.inj hg).2
  have himt : t.image g.1 = t := (List.cons.inj htail).1
  let a : cellFacetStabilizer s t :=
    ⟨g, preserves_finset_of_image g.1 g.1.injective himt⟩
  refine ⟨facetRestriction s t a, ?_⟩
  apply mapChain_injective inclusion hi
  rw [mapChain_comp]
  have hc : inclusion ∘ (facetRestriction s t a).1 = g.1 ∘ inclusion := by
    funext x
    exact facetRestriction_apply s t a x
  rw [hc, ← mapChain_comp]
  simpa only [mapChain_cons, ← him, A', B', FullFlag.map] using htail

/-- The actual restriction is faithful for every facet, not only for a
separately supplied supporting-hyperplane certificate. -/
theorem restriction_injective (H : Facet s t)
    (span : affineSpan ℝ (s : Set P) = ⊤) :
    letI := H.span_nonempty
    Function.Injective (facetRestriction s t) := by
  letI := H.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set P)) := Classical.decEq _
  exact facetRestriction_injective s t H.1.parent_nonempty
    (H.span_with_centroid.trans span)

/-- Surjectivity is obtained from actual flags and their centroid rigidity. -/
theorem restriction_surjective (H : Facet s t) (regular : IsFlagRegular s) :
    letI := H.span_nonempty
    Function.Surjective (facetRestriction s t) := by
  letI := H.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set P)) := Classical.decEq _
  let T := affineSpan ℝ (t : Set P)
  let sv := spanVertices t
  let inclusion : T →ᵃ[ℝ] P := T.subtype
  have hi : Function.Injective inclusion := Subtype.val_injective
  have hsv : sv.Nonempty := by
    obtain ⟨p, hp⟩ := H.1.1
    exact ⟨⟨p, subset_affineSpan ℝ _ hp⟩, (mem_spanVertices t _).mpr hp⟩
  have him : sv.image inclusion = t := H.image_intrinsic_vertices
  obtain ⟨A⟩ := fullFlag_nonempty sv hsv
  intro b
  have hbim : sv.image b.1 = sv := symmetry_image_finset b
  let B : FullFlag sv := A.map b.1.toAffineMap b.1.injective (by simpa using hbim)
  let A' : FullFlag t := A.map inclusion hi him
  let B' : FullFlag t := B.map inclusion hi him
  let AF : FullFlag s := ⟨t :: A'.1, CompleteChain.step H A'.2⟩
  let BF : FullFlag s := ⟨t :: B'.1, CompleteChain.step H B'.2⟩
  obtain ⟨g, hg⟩ := regular AF BF
  have htail : mapChain g.1 (t :: A'.1) = t :: B'.1 := (List.cons.inj hg).2
  have himt : t.image g.1 = t := (List.cons.inj htail).1
  let a : cellFacetStabilizer s t :=
    ⟨g, preserves_finset_of_image g.1 g.1.injective himt⟩
  refine ⟨a, ?_⟩
  let f₁ : T →ᵃ[ℝ] P := g.1.toAffineMap.comp inclusion
  let f₂ : T →ᵃ[ℝ] P := inclusion.comp b.1.toAffineMap
  have hm : mapChain f₁ (sv :: A.1) = mapChain f₂ (sv :: A.1) := by
    have hm' : mapChain g.1 (mapChain inclusion (sv :: A.1)) =
        mapChain inclusion (mapChain b.1 (sv :: A.1)) := by
      simpa [mapChain_cons, him, hbim, A', B', B, FullFlag.map] using htail
    simp only [mapChain_comp] at hm'
    convert hm' using 1 <;> rfl
  have he := A.maps_agree f₁ f₂ (g.1.injective.comp hi) (hi.comp b.1.injective) hm
  apply Subtype.ext
  ext x : 1
  apply Subtype.ext
  exact he (by rw [spanVertices_span t]; trivial)

def restrictionEquiv (H : Facet s t) (span : affineSpan ℝ (s : Set P) = ⊤)
    (regular : IsFlagRegular s) :
    letI := H.span_nonempty
    cellFacetStabilizer s t ≃* symmetryGroup (spanVertices t) := by
  letI := H.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set P)) := Classical.decEq _
  exact MulEquiv.ofBijective (facetRestriction s t)
    ⟨H.restriction_injective span, H.restriction_surjective regular⟩

theorem restriction_linear_apply (H : Facet s t) :
    letI := H.span_nonempty
    ∀ (g : cellFacetStabilizer s t)
      (w : (affineSpan ℝ (t : Set P)).direction),
      ((facetRestriction s t g).1.linear w : V) = g.1.1.linear w := by
  letI := H.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set P)) := Classical.decEq _
  intro g w
  obtain ⟨p, hp⟩ := H.1.1
  let p' : affineSpan ℝ (t : Set P) := ⟨p, subset_affineSpan ℝ _ hp⟩
  let b := (facetRestriction s t g).1
  have hb := congrArg (fun y : affineSpan ℝ (t : Set P) ↦ (y : P))
    (b.toAffineMap.map_vadd p' w)
  have hg := g.1.1.toAffineMap.map_vadd p (w : V)
  change g.1.1 ((w : V) +ᵥ p) = (b.linear w : V) +ᵥ g.1.1 p at hb
  exact (vadd_right_cancel_iff (g.1.1 p)).mp (hb.symm.trans hg)

/-- The intrinsic and ambient determinant agree: the transverse direction
between the two fixed centroids contributes the scalar 1. -/
theorem restriction_det [FiniteDimensional ℝ V] (H : Facet s t)
    (span : affineSpan ℝ (s : Set P) = ⊤) :
    letI := H.span_nonempty
    ∀ g : cellFacetStabilizer s t,
      LinearEquiv.det (facetRestriction s t g).1.linear =
        LinearEquiv.det g.1.1.linear := by
  letI := H.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set P)) := Classical.decEq _
  intro g
  let W := (affineSpan ℝ (t : Set P)).direction
  let c := s.centroid ℝ id
  let p := t.centroid ℝ id
  have hp0 : H.form p = 0 :=
    (H.span_iff span p).mp (centroid_mem_span t H.1.1)
  have hv : H.form.linear (c -ᵥ p) ≠ 0 := by
    rw [H.form.linearMap_vsub, hp0, vsub_eq_sub, sub_zero]
    exact ne_of_lt H.form_centroid_neg
  have hc : g.1.1 c = c := centroid_fixed s H.1.parent_nonempty g.1
  have hp : g.1.1 p = p := centroid_fixed t H.1.1 (facetAmbientHom s t g)
  have hf : g.1.1.toAffineMap.linear (c -ᵥ p) = c -ᵥ p := by
    rw [g.1.1.toAffineMap.linearMap_vsub]
    change g.1.1 c -ᵥ g.1.1 p = c -ᵥ p
    rw [hc, hp]
  have hd := det_eq_facet_of_fixed_transverse W H.form.linear
    (H.direction_iff span) (c -ᵥ p) hv g.1.1.toAffineMap.linear
    (facetRestriction s t g).1.toAffineMap.linear
    (H.restriction_linear_apply g) hf
  apply Units.ext
  simp only [LinearEquiv.coe_det]
  convert hd.symm using 1 <;> rfl

theorem restriction_orientation [FiniteDimensional ℝ V] (H : Facet s t)
    (span : affineSpan ℝ (s : Set P) = ⊤) :
    letI := H.span_nonempty
    ∀ g : cellFacetStabilizer s t,
      euclideanOrientation (spanVertices t) (facetRestriction s t g) =
        euclideanOrientation s g.1 := by
  letI := H.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set P)) := Classical.decEq _
  intro g
  simp only [euclideanOrientation_apply, H.restriction_det span g]

def rotationRestrictionEquiv [FiniteDimensional ℝ V] (H : Facet s t)
    (span : affineSpan ℝ (s : Set P) = ⊤) (regular : IsFlagRegular s) :
    letI := H.span_nonempty
    ((euclideanOrientation s).comp (cellFacetStabilizer s t).subtype).ker ≃*
      (euclideanOrientation (spanVertices t)).ker := by
  letI := H.span_nonempty
  letI : DecidableEq (affineSpan ℝ (t : Set P)) := Classical.decEq _
  exact RegularFacet.rotationRestrictionEquiv (H.restrictionEquiv span regular)
    ((euclideanOrientation s).comp (cellFacetStabilizer s t).subtype)
    (euclideanOrientation (spanVertices t)) (H.restriction_orientation span)

end Facet
end
end PolytopeCounting.FacetPairing.EuclideanGeometry.GeometricFlags
