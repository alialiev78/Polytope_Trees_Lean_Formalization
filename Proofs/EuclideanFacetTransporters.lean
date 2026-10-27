module

public import Proofs.AllFacetsOrientedFlags

@[expose] public section

/-!
# All ordered facet pairs: actual intrinsic isometries and palettes

Every vertex-preserving affine isometry between two intrinsic facet spaces
extends uniquely to a cell symmetry. Negative maps are defined using positive
cell charts, and their sign is proved to equal the sign of their unique
ambient extension. Thus the palette represents all such maps, not a selected
subset. The one-facet rotation parameter is derived from its actual group.

-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell
noncomputable section
open GeometricFlags
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

universe u
variable {V P : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
variable (K : RegularCell V P)

def facetVertices (i : Fin K.h) : Finset P := ((facetIndex K.vertices).symm i).1

theorem facet_property (i : Fin K.h) : Facet K.vertices (K.facetVertices i) :=
  ((facetIndex K.vertices).symm i).isFacet

abbrev FacetSpace (i : Fin K.h) := affineSpan ℝ (K.facetVertices i : Set P)

instance facetSpaceNonempty (i : Fin K.h) : Nonempty (K.FacetSpace i) :=
  (K.facet_property i).span_nonempty

/-- All affine isometries preserving the vertex sets of the two intrinsic
facets. There is no assumed ambient extension in this definition. -/
abbrev IntrinsicMap (i j : Fin K.h) :=
  {f : K.FacetSpace i ≃ᵃⁱ[ℝ] K.FacetSpace j //
    ∀ x, f x ∈ spanVertices (K.facetVertices j) ↔
      x ∈ spanVertices (K.facetVertices i)}


noncomputable instance intrinsicGroupFintype (i : Fin K.h) :
    Fintype (symmetryGroup (spanVertices (K.facetVertices i))) :=
  facetFintype (K.facetVertices i)

theorem facet_image (g : K.Group) (i : Fin K.h) :
    (K.facetVertices i).image g.1 = K.facetVertices (K.system.facet g i) := by
  simp only [facetVertices, system_facet, indexedFacetAction_apply,
    Equiv.symm_apply_apply, mapFacet_val]

theorem facet_fix_iff (g : K.Group) (i : Fin K.h) :
    K.system.facet g i = i ↔
      ∀ x, g.1 x ∈ K.facetVertices i ↔ x ∈ K.facetVertices i := by
  have h := indexedFacetAction_fix_iff K.vertices g ((facetIndex K.vertices).symm i)
  simpa only [Equiv.apply_symm_apply, facetVertices, system_facet] using h

abbrev Transporter (i j : Fin K.h) := {g : K.Group // K.system.facet g i = j}

/-- Restrict an ambient transporter to the two actual affine facet spaces. -/
def facetTransport (i j : Fin K.h) (g : K.Group) (hg : K.system.facet g i = j) :
    K.FacetSpace i ≃ᵃⁱ[ℝ] K.FacetSpace j := by
  have him : (K.facetVertices i).image g.1 = K.facetVertices j := by
    rw [K.facet_image, hg]
  have hspan : (affineSpan ℝ (K.facetVertices i : Set P)).map g.1.toAffineMap =
      affineSpan ℝ (K.facetVertices j : Set P) := by
    rw [AffineSubspace.map_span]
    congr 1
    change g.1 '' (K.facetVertices i : Set P) = (K.facetVertices j : Set P)
    simpa only [Finset.coe_image] using
      congrArg (fun a : Finset P ↦ (a : Set P)) him
  exact ((affineSpan ℝ (K.facetVertices i : Set P)).isometryEquivMap
    g.1.toAffineIsometry).trans (AffineIsometryEquiv.ofEq _ _ hspan)

@[simp] theorem facetTransport_apply (i j : Fin K.h) (g : K.Group)
    (hg : K.system.facet g i = j) (x : K.FacetSpace i) :
    (K.facetTransport i j g hg x : P) = g.1 x := rfl


def transportToMap {i j : Fin K.h} (g : K.Transporter i j) : K.IntrinsicMap i j :=
  ⟨K.facetTransport i j g.1 g.2, by
    intro x
    simp only [mem_spanVertices, facetTransport_apply]
    have him : (K.facetVertices i).image g.1.1 = K.facetVertices j := by
      rw [K.facet_image, g.2]
    exact preserves_finset_of_image g.1.1 g.1.1.injective him x⟩

def positiveTransport (i j : Fin K.h) : K.Transporter i j :=
  ⟨K.system.chart j * (K.system.chart i)⁻¹, by
    simp only [map_mul, Equiv.Perm.mul_apply, K.system.chart_inv_target,
      K.system.chart_base]⟩

@[simp] theorem positiveTransport_sign (i j : Fin K.h) :
    euclideanOrientation K.vertices (K.positiveTransport i j).1 = 1 := by
  change K.system.orientation (K.system.chart j * (K.system.chart i)⁻¹) = 1
  simp only [map_mul, map_inv, K.system.chart_sign, inv_one, mul_one]

/-- Move an arbitrary intrinsic map back along a positive geometric chart. -/
def intrinsicReturn {i j : Fin K.h} (f : K.IntrinsicMap i j) :
    symmetryGroup (spanVertices (K.facetVertices i)) :=
  ⟨f.1.trans (K.transportToMap (K.positiveTransport i j)).1.symm, by
    intro x
    let a := K.transportToMap (K.positiveTransport i j)
    have ha := a.2 (a.1.symm (f.1 x))
    rw [a.1.apply_symm_apply] at ha
    exact ha.symm.trans (f.2 x)⟩

/-- A transporter is completely determined by its restriction to one facet,
since every cell symmetry also fixes the cell centroid. -/
theorem transportToMap_injective (i j : Fin K.h) :
    Function.Injective (K.transportToMap (i := i) (j := j)) := by
  intro g k he
  apply Subtype.ext
  apply Subtype.ext
  apply AffineIsometryEquiv.toAffineEquiv_injective
  apply AffineEquiv.ext_on ((K.facet_property i).span_with_centroid.trans K.full_span)
  intro x hx
  rcases hx with rfl | hx
  · exact (centroid_fixed K.vertices K.nonempty g.1).trans
      (centroid_fixed K.vertices K.nonempty k.1).symm
  · let x' : K.FacetSpace i := ⟨x, subset_affineSpan ℝ _ hx⟩
    exact congrArg (fun F : K.IntrinsicMap i j ↦ (F.1 x' : P)) he

/-- The facet extension theorem closes the all-pairs surjectivity gap. -/
theorem transportToMap_surjective (i j : Fin K.h) :
    Function.Surjective (K.transportToMap (i := i) (j := j)) := by
  intro f
  let a := K.positiveTransport i j
  let b := K.intrinsicReturn f
  obtain ⟨k, hk⟩ := (K.facet_property i).restriction_surjective K.regular b
  have hkfix : K.system.facet k.1 i = i := (K.facet_fix_iff k.1 i).mpr k.2
  let g : K.Transporter i j := ⟨a.1 * k.1, by
    rw [map_mul, Equiv.Perm.mul_apply, hkfix, a.2]⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  ext x : 1
  apply Subtype.ext
  have hp := congrArg (fun z : symmetryGroup (spanVertices (K.facetVertices i)) ↦
    (z.1 x : P)) hk
  change k.1.1 x = ((K.transportToMap a).1.symm (f.1 x) : P) at hp
  change a.1.1 (k.1.1 x) = (f.1 x : P)
  rw [hp]
  exact congrArg (fun y : K.FacetSpace j ↦ (y : P))
    ((K.transportToMap a).1.apply_symm_apply (f.1 x))

def intrinsicTransportEquiv (i j : Fin K.h) :
    K.Transporter i j ≃ K.IntrinsicMap i j :=
  Equiv.ofBijective K.transportToMap
    ⟨K.transportToMap_injective i j, K.transportToMap_surjective i j⟩

theorem intrinsicMap_existsUnique_extension (i j : Fin K.h) (f : K.IntrinsicMap i j) :
    ∃! g : K.Transporter i j, K.transportToMap g = f := by
  let e := K.intrinsicTransportEquiv i j
  exact ⟨e.symm f, e.apply_symm_apply f,
    fun g hg ↦ e.injective (hg.trans (e.apply_symm_apply f).symm)⟩

/-- Orientation between different intrinsic facet spaces, measured against a
positive cell transporter. The subsequent theorem proves independence of this
choice by identifying it with the unique extension's actual determinant sign. -/
def intrinsicMapSign {i j : Fin K.h} (f : K.IntrinsicMap i j) : ℤˣ :=
  euclideanOrientation (spanVertices (K.facetVertices i)) (K.intrinsicReturn f)

@[simp] theorem intrinsicMapSign_transport {i j : Fin K.h} (g : K.Transporter i j) :
    K.intrinsicMapSign (K.transportToMap g) = euclideanOrientation K.vertices g.1 := by
  let a := K.positiveTransport i j
  have hfix : K.system.facet (a.1⁻¹ * g.1) i = i := by
    rw [map_mul, Equiv.Perm.mul_apply, g.2, map_inv]
    exact (K.system.facet a.1).symm_apply_eq.mpr a.2.symm
  let k : cellFacetStabilizer K.vertices (K.facetVertices i) :=
    ⟨a.1⁻¹ * g.1, (K.facet_fix_iff _ i).mp hfix⟩
  have hk : facetRestriction K.vertices (K.facetVertices i) k =
      K.intrinsicReturn (K.transportToMap g) := by
    apply Subtype.ext
    ext x : 1
    apply Subtype.ext
    change a.1.1.symm (g.1.1 x) =
      ((K.transportToMap a).1.symm ((K.transportToMap g).1 x) : P)
    apply a.1.1.injective
    rw [a.1.1.apply_symm_apply]
    exact (congrArg (fun z : K.FacetSpace j ↦ (z : P))
      ((K.transportToMap a).1.apply_symm_apply ((K.transportToMap g).1 x))).symm
  change euclideanOrientation (spanVertices (K.facetVertices i))
    (K.intrinsicReturn (K.transportToMap g)) = _
  rw [← hk, (K.facet_property i).restriction_orientation K.full_span]
  change euclideanOrientation K.vertices (a.1⁻¹ * g.1) = _
  rw [map_mul, map_inv, K.positiveTransport_sign, inv_one, one_mul]

/-- Independence under any other positive ambient chart, not just the chosen
one. The same sign is obtained by returning to the source along that chart. -/
theorem intrinsicMapSign_independent {i j : Fin K.h} (f : K.IntrinsicMap i j)
    (a : K.Transporter i j) (apos : euclideanOrientation K.vertices a.1 = 1)
    (b : symmetryGroup (spanVertices (K.facetVertices i)))
    (hb : b.1 = f.1.trans (K.transportToMap a).1.symm) :
    euclideanOrientation (spanVertices (K.facetVertices i)) b = K.intrinsicMapSign f := by
  let g := (K.intrinsicTransportEquiv i j).symm f
  have hg : K.transportToMap g = f := (K.intrinsicTransportEquiv i j).apply_symm_apply f
  have hfix : K.system.facet (a.1⁻¹ * g.1) i = i := by
    rw [map_mul, Equiv.Perm.mul_apply, g.2, map_inv]
    exact (K.system.facet a.1).symm_apply_eq.mpr a.2.symm
  let k : cellFacetStabilizer K.vertices (K.facetVertices i) :=
    ⟨a.1⁻¹ * g.1, (K.facet_fix_iff _ i).mp hfix⟩
  have hk : facetRestriction K.vertices (K.facetVertices i) k = b := by
    apply Subtype.ext
    rw [hb, ← hg]
    ext x : 1
    apply Subtype.ext
    change a.1.1.symm (g.1.1 x) =
      ((K.transportToMap a).1.symm ((K.transportToMap g).1 x) : P)
    apply a.1.1.injective
    rw [a.1.1.apply_symm_apply]
    exact (congrArg (fun z : K.FacetSpace j ↦ (z : P))
      ((K.transportToMap a).1.apply_symm_apply ((K.transportToMap g).1 x))).symm
  rw [← hk, (K.facet_property i).restriction_orientation K.full_span, ← hg,
    K.intrinsicMapSign_transport]
  change euclideanOrientation K.vertices (a.1⁻¹ * g.1) = _
  simp [map_mul, map_inv, apos]

abbrev NegativeIntrinsicMap (i j : Fin K.h) :=
  {f : K.IntrinsicMap i j // K.intrinsicMapSign f = -1}

/-- Signed transporters and all orientation-reversing intrinsic maps agree. -/
def negativeMapEquiv (i j : Fin K.h) :
    K.system.Gluing i j ≃ K.NegativeIntrinsicMap i j where
  toFun g := ⟨K.transportToMap ⟨g.1, g.2.1⟩, by
    rw [K.intrinsicMapSign_transport]
    exact g.2.2⟩
  invFun f :=
    let g := (K.intrinsicTransportEquiv i j).symm f.1
    ⟨g.1, g.2, by
      have hg : K.transportToMap g = f.1 :=
        (K.intrinsicTransportEquiv i j).apply_symm_apply f.1
      have hs := K.intrinsicMapSign_transport g
      rw [hg, f.2] at hs
      exact hs.symm⟩
  left_inv g := by
    apply Subtype.ext
    exact congrArg (fun t : K.Transporter i j ↦ t.1)
      ((K.intrinsicTransportEquiv i j).symm_apply_apply ⟨g.1, g.2.1⟩)
  right_inv f := by
    apply Subtype.ext
    exact (K.intrinsicTransportEquiv i j).apply_symm_apply f.1

/-- The intrinsic base-facet group supplies r. -/
abbrev FacetRotation :=
  (euclideanOrientation (spanVertices (K.facetVertices K.system.base))).ker
abbrev r : ℕ := Fintype.card K.FacetRotation
abbrev tau : ℕ := Fintype.card K.system.Rotation

/-- Repackage the old indexed stabilizer as the actual geometric stabilizer. -/
def indexedPositiveStabilizerEquiv : K.system.facetRotation ≃*
    ((euclideanOrientation K.vertices).comp
      (cellFacetStabilizer K.vertices (K.facetVertices K.system.base)).subtype).ker where
  toFun g := ⟨⟨g.1, (K.facet_fix_iff g.1 K.system.base).mp g.2.1⟩, g.2.2⟩
  invFun g := ⟨g.1.1, ⟨(K.facet_fix_iff g.1.1 K.system.base).mpr g.1.2, g.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def facetRotationEquiv : K.system.facetRotation ≃* K.FacetRotation :=
  K.indexedPositiveStabilizerEquiv.trans
    ((K.facet_property K.system.base).rotationRestrictionEquiv K.full_span K.regular)

theorem r_eq_indexed_stabilizer : K.r = Fintype.card K.system.facetRotation :=
  (Fintype.card_congr K.facetRotationEquiv.toEquiv).symm

/-- Every ordered facet pair has exactly r negative intrinsic isometries. -/
def allFacetPalette (i j : Fin K.h) : Fin K.r ≃ K.NegativeIntrinsicMap i j :=
  (Fintype.equivFin K.FacetRotation).symm.trans
    (K.facetRotationEquiv.symm.toEquiv.trans
      ((K.system.gluingEquiv i j).trans (K.negativeMapEquiv i j)))

noncomputable instance negativeMapFintype (i j : Fin K.h) :
    Fintype (K.NegativeIntrinsicMap i j) :=
  Fintype.ofEquiv (Fin K.r) (K.allFacetPalette i j)

theorem allFacetMap_card (i j : Fin K.h) :
    Fintype.card (K.NegativeIntrinsicMap i j) = K.r := by
  rw [← Fintype.card_congr (K.allFacetPalette i j), Fintype.card_fin]

/-- The geometric parameter identity of the manuscript. -/
theorem tau_eq_h_mul_r : K.tau = K.h * K.r := by
  change Fintype.card K.system.Rotation = _
  rw [K.system.rotation_card, K.r_eq_indexed_stabilizer]

end
end PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell
