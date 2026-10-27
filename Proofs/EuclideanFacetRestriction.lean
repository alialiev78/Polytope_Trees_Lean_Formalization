module

public import Proofs.FiniteEuclideanSymmetry

@[expose] public section

/-!
# Restriction of actual cell symmetries to an intrinsic facet

Facet symmetries act on the affine span of the facet, not on the entire ambient
space. The finite target group and the restriction homomorphism are constructed
from vertex sets. Injectivity follows when the facet vertices and cell centroid
affinely span the cell. Surjectivity is not asserted in this module.
-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MetricSpace E] [NormedAddTorsor V E]
variable (s t : Finset E)

/-- The facet vertices, regarded as points in their own affine span. -/
def spanVertices : Finset (affineSpan ℝ (t : Set E)) :=
  t.attach.map ⟨fun x ↦ ⟨x.1, subset_affineSpan ℝ (t : Set E) x.2⟩, by
    intro x y he
    exact Subtype.ext (congrArg (fun z : affineSpan ℝ (t : Set E) ↦ (z : E)) he)⟩

@[simp] theorem mem_spanVertices (x : affineSpan ℝ (t : Set E)) :
    x ∈ spanVertices t ↔ (x : E) ∈ t := by
  constructor
  · intro hx
    obtain ⟨y,_,hy⟩ := Finset.mem_map.mp hx
    exact congrArg Subtype.val hy ▸ y.2
  · intro hx
    exact Finset.mem_map.mpr ⟨⟨x.1,hx⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

theorem image_spanVertices :
    Subtype.val '' (spanVertices t : Set (affineSpan ℝ (t : Set E))) = t := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (mem_spanVertices t y).mp hy
  · intro hx
    exact ⟨⟨x,subset_affineSpan ℝ (t : Set E) hx⟩,
      (mem_spanVertices t _).mpr hx,rfl⟩

variable [Nonempty (affineSpan ℝ (t : Set E))]

/-- No spanning hypothesis is needed for the intrinsic facet vertex set. -/
theorem spanVertices_span :
    affineSpan ℝ (spanVertices t : Set (affineSpan ℝ (t : Set E))) = ⊤ := by
  apply top_unique
  intro x _
  have hm : (affineSpan ℝ (spanVertices t : Set (affineSpan ℝ (t : Set E)))).map
      (affineSpan ℝ (t : Set E)).subtype = affineSpan ℝ (t : Set E) := by
    rw [AffineSubspace.map_span]
    congr 1
    exact image_spanVertices t
  have hx : (x : E) ∈ (affineSpan ℝ (spanVertices t : Set (affineSpan ℝ (t : Set E)))).map
      (affineSpan ℝ (t : Set E)).subtype := by rw [hm]; exact x.2
  obtain ⟨y,hy,he⟩ := hx
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

@[instance_reducible]
def facetFintype : Fintype (symmetryGroup (spanVertices t)) :=
  fintypeSymmetries (spanVertices t) (spanVertices_span t)

/-- Cell symmetries which preserve this facet vertex set. -/
def cellFacetStabilizer : Subgroup (symmetryGroup s) :=
  (symmetryGroup t).comap (symmetryGroup s).subtype

def facetAmbientHom : cellFacetStabilizer s t →* symmetryGroup t where
  toFun g := ⟨g.1.1,g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The geometric restriction homomorphism is built, not supplied. -/
def facetRestriction : cellFacetStabilizer s t →* symmetryGroup (spanVertices t) where
  toFun g := ⟨restriction t (facetAmbientHom s t g), by
    intro x
    simp only [mem_spanVertices, restriction_apply]
    exact (facetAmbientHom s t g).2 x⟩
  map_one' := by
    apply Subtype.ext
    exact (restrictionHom t).map_one
  map_mul' g k := by
    apply Subtype.ext
    exact (restrictionHom t).map_mul (facetAmbientHom s t g) (facetAmbientHom s t k)

@[simp] theorem facetRestriction_apply (g : cellFacetStabilizer s t)
    (x : affineSpan ℝ (t : Set E)) :
    ((facetRestriction s t g).1 x : E) = g.1.1 x := rfl

/-- This is injectivity for actual Euclidean maps. The geometric spanning
condition is explicit; it is not used to claim surjectivity or regularity. -/
theorem facetRestriction_injective (hs : s.Nonempty)
    (span : affineSpan ℝ (insert (s.centroid ℝ id) (t : Set E)) = ⊤) :
    Function.Injective (facetRestriction s t) := by
  intro g k he
  apply Subtype.ext
  apply Subtype.ext
  apply AffineIsometryEquiv.toAffineEquiv_injective
  apply AffineEquiv.ext_on span
  intro x hx
  rcases hx with hx | hx
  · subst x
    exact (centroid_fixed s hs g.1).trans (centroid_fixed s hs k.1).symm
  · let y : affineSpan ℝ (t : Set E) := ⟨x,subset_affineSpan ℝ (t : Set E) hx⟩
    exact congrArg (fun f : symmetryGroup (spanVertices t) ↦ (f.1 y : E)) he

end
end PolytopeCounting.FacetPairing.EuclideanGeometry
