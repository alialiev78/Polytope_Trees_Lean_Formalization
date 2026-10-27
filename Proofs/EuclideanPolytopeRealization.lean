module

public import Proofs.EuclideanRegularPolytopeMass
public import Proofs.FacetPairingRealization

@[expose] public section

/-!
# Quotient realizations of the concrete regular-polytope presentations

Cells are the convex hulls of the actual vertex set. Every seam uses the
actual affine isometry represented by its transporter. The conjugation action
is characterized by pointwise affine squares on actual facets and descends to
homeomorphisms of the quotient. Neither the converse for arbitrary quotient
homeomorphisms nor manifold admissibility is asserted.

-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell
noncomputable section
open GeometricFlags RegularPresentation Renaming.WreathRenaming
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (K : RegularCell E E)

abbrev Polytope := convexHull ℝ (K.vertices : Set E)
abbrev FacetHull (i : Fin K.h) := convexHull ℝ (K.facetVertices i : Set E)
abbrev PolytopePoint := {x : E // x ∈ K.Polytope}

theorem facetHull_subset (i : Fin K.h) : K.FacetHull i ⊆ K.Polytope :=
  convexHull_mono (by exact_mod_cast (K.facet_property i).1.subset)

theorem polytope_map_mem (g : K.Group) {x : E} (hx : x ∈ K.Polytope) :
    g.1 x ∈ K.Polytope := by
  change g.1 x ∈ convexHull ℝ (K.vertices : Set E)
  rw [← image_convexHull K.vertices g]
  exact ⟨x, hx, rfl⟩

theorem facetHull_image (g : K.Group) (i : Fin K.h) :
    g.1 '' K.FacetHull i = K.FacetHull (K.system.facet g i) := by
  change g.1.toAffineMap '' convexHull ℝ (K.facetVertices i : Set E) = _
  rw [AffineMap.image_convexHull]
  congr 1
  change g.1 '' (K.facetVertices i : Set E) =
    (K.facetVertices (K.system.facet g i) : Set E)
  simpa only [Finset.coe_image] using
    congrArg (fun s : Finset E ↦ (s : Set E)) (K.facet_image g i)

theorem facetHull_map_mem (g : K.Group) (i : Fin K.h) {x : E}
    (hx : x ∈ K.FacetHull i) : g.1 x ∈ K.FacetHull (K.system.facet g i) := by
  rw [← K.facetHull_image g i]
  exact ⟨x, hx, rfl⟩

/-- Restrict the actual symmetry, rather than a combinatorial vertex map. -/
def polytopeHomeomorph (g : K.Group) : K.PolytopePoint ≃ₜ K.PolytopePoint where
  toFun x := ⟨g.1 x, K.polytope_map_mem g x.2⟩
  invFun x := ⟨g.1.symm x, K.polytope_map_mem g⁻¹ x.2⟩
  left_inv x := Subtype.ext (g.1.symm_apply_apply x)
  right_inv x := Subtype.ext (g.1.apply_symm_apply x)
  continuous_toFun := (g.1.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (g.1.symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem polytopeHomeomorph_apply (g : K.Group) (x : K.PolytopePoint) :
    (K.polytopeHomeomorph g x : E) = g.1 x := rfl

@[simp] theorem polytopeHomeomorph_inv (g : K.Group) :
    K.polytopeHomeomorph g⁻¹ = (K.polytopeHomeomorph g).symm := rfl

/-- Pointwise affine compatibility is specified independently of orbits. -/
def PolytopeAffineCompatible {C : Type} [DecidableEq C]
    (g : Frames K.system C) (D Q : Presentation K.system C) : Prop :=
  Q.matching = Renaming.MatchingTransport.renamePartial (slotsPerm K.system g) D.matching ∧
  ∀ a b, s(a,b) ∈ D.matching.seams → ∀ x : E, x ∈ K.FacetHull a.2 →
    (Q.maps (slotsPerm K.system g a) (slotsPerm K.system g b)).1
        ((vertexPerm K.system g a.1).1 x) =
      (vertexPerm K.system g b.1).1 ((D.maps a b).1 x)

/-- Restriction to the facet plus the common fixed centroid determines the
whole ambient affine map. This proves the converse direction, not just the
sufficiency of table conjugation. -/
theorem polytopeAffineCompatible_iff_compatible {C : Type} [DecidableEq C]
    (g : Frames K.system C) (D Q : Presentation K.system C) :
    K.PolytopeAffineCompatible g D Q ↔ Compatible K.system g D Q := by
  constructor
  · rintro ⟨hm, hsquare⟩
    refine ⟨hm, ?_⟩
    intro a b hab
    let u := vertexPerm K.system g a.1
    let v := vertexPerm K.system g b.1
    let q := Q.maps (slotsPerm K.system g a) (slotsPerm K.system g b)
    let p := D.maps a b
    have he : q * u = v * p := by
      apply Subtype.ext
      apply AffineIsometryEquiv.toAffineEquiv_injective
      apply AffineEquiv.ext_on
        ((K.facet_property a.2).span_with_centroid.trans K.full_span)
      intro x hx
      rcases hx with rfl | hx
      · exact (centroid_fixed K.vertices K.nonempty (q * u)).trans
          (centroid_fixed K.vertices K.nonempty (v * p)).symm
      · exact hsquare a b hab x (subset_convexHull ℝ _ hx)
    change q = v * p * u⁻¹
    calc
      q = (q * u) * u⁻¹ := by simp [mul_assoc]
      _ = v * p * u⁻¹ := by rw [he]
  · rintro ⟨hm, ht⟩
    refine ⟨hm, ?_⟩
    intro a b hab x hx
    rw [ht a b hab]
    change (vertexPerm K.system g b.1).1 ((D.maps a b).1
        ((vertexPerm K.system g a.1).1.symm ((vertexPerm K.system g a.1).1 x))) = _
    rw [(vertexPerm K.system g a.1).1.symm_apply_apply]

theorem polytopeAffineCompatible_iff_action {C : Type} [DecidableEq C]
    (g : Frames K.system C) (D Q : Presentation K.system C) :
    K.PolytopeAffineCompatible g D Q ↔ g • D = Q :=
  (K.polytopeAffineCompatible_iff_compatible g D Q).trans
    (RegularPresentation.compatible_iff K.system g D Q)

abbrev PolytopeAffineIso {C : Type} [DecidableEq C]
    (D Q : Presentation K.system C) :=
  {g : Frames K.system C // K.PolytopeAffineCompatible g D Q}

def polytopeAffineAutomorphismsEquivStabilizer {C : Type} [DecidableEq C]
    (D : Presentation K.system C) :
    K.PolytopeAffineIso D D ≃ MulAction.stabilizer (Frames K.system C) D where
  toFun g := ⟨g.1, (K.polytopeAffineCompatible_iff_action g.1 D D).mp g.2⟩
  invFun g := ⟨g.1, (K.polytopeAffineCompatible_iff_action g.1 D D).mpr g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev PolytopeCellPoints (C : Type) := Σ _ : C, K.PolytopePoint

def polytopeFrameHomeomorph {C : Type} [DecidableEq C]
    (g : Frames K.system C) : K.PolytopeCellPoints C ≃ₜ K.PolytopeCellPoints C where
  toFun x := ⟨g.cell x.1, K.polytopeHomeomorph (vertexPerm K.system g x.1) x.2⟩
  invFun x := ⟨g.cell.symm x.1,
    (K.polytopeHomeomorph (vertexPerm K.system g (g.cell.symm x.1))).symm x.2⟩
  left_inv x := by rcases x with ⟨c, x⟩; simp
  right_inv x := by rcases x with ⟨c, x⟩; simp
  continuous_toFun := continuous_sigma (fun c ↦
    (continuous_sigmaMk (i := g.cell c)).comp
      (K.polytopeHomeomorph (vertexPerm K.system g c)).continuous)
  continuous_invFun := continuous_sigma (fun c ↦
    (continuous_sigmaMk (i := g.cell.symm c)).comp
      (K.polytopeHomeomorph (vertexPerm K.system g (g.cell.symm c))).symm.continuous)

@[simp] theorem polytopeFrameHomeomorph_inv {C : Type} [DecidableEq C]
    (g : Frames K.system C) :
    K.polytopeFrameHomeomorph g⁻¹ = (K.polytopeFrameHomeomorph g).symm := by
  apply Homeomorph.ext
  intro x
  rcases x with ⟨c, x⟩
  rfl

/-- The generating relation uses exactly the actual seams and their affine
maps on points of actual facets. No extra identifications are inserted. -/
def PolytopeGlueRel {C : Type} [DecidableEq C] (D : Presentation K.system C)
    (x y : K.PolytopeCellPoints C) : Prop :=
  ∃ a b : Slots C K.h, ∃ hab : s(a,b) ∈ D.matching.seams,
    ∃ z : K.PolytopePoint, z.1 ∈ K.FacetHull a.2 ∧
      x = ⟨a.1, z⟩ ∧ y = ⟨b.1, K.polytopeHomeomorph (D.maps a b) z⟩

abbrev PolytopeRealization {C : Type} [DecidableEq C]
    (D : Presentation K.system C) := Quot (K.PolytopeGlueRel D)

def polytopeCell {C : Type} [DecidableEq C]
    (D : Presentation K.system C) (c : C) (x : K.PolytopePoint) :
    K.PolytopeRealization D := Quot.mk _ ⟨c, x⟩

theorem continuous_polytopeCell {C : Type} [DecidableEq C]
    (D : Presentation K.system C) (c : C) : Continuous (K.polytopeCell D c) :=
  continuous_quot_mk.comp continuous_sigmaMk

theorem polytopeGlueRel_rename {C : Type} [DecidableEq C]
    (g : Frames K.system C) (D : Presentation K.system C)
    (x y : K.PolytopeCellPoints C) (hxy : K.PolytopeGlueRel D x y) :
    K.PolytopeGlueRel (rename K.system g D)
      (K.polytopeFrameHomeomorph g x) (K.polytopeFrameHomeomorph g y) := by
  rcases hxy with ⟨a, b, hab, z, hz, rfl, rfl⟩
  let u := vertexPerm K.system g a.1
  let v := vertexPerm K.system g b.1
  let z' := K.polytopeHomeomorph u z
  have hnew : s(slotsPerm K.system g a, slotsPerm K.system g b) ∈
      (rename K.system g D).matching.seams :=
    (pair_mem_rename (slotsPerm K.system g) D.matching a b).mpr hab
  have hz' : (z' : E) ∈ K.FacetHull (slotsPerm K.system g a).2 :=
    K.facetHull_map_mem u a.2 hz
  refine ⟨slotsPerm K.system g a, slotsPerm K.system g b, hnew, z', hz', rfl, ?_⟩
  change (⟨g.cell b.1, K.polytopeHomeomorph v
      (K.polytopeHomeomorph (D.maps a b) z)⟩ : K.PolytopeCellPoints C) =
    ⟨g.cell b.1, K.polytopeHomeomorph
      ((rename K.system g D).maps (slotsPerm K.system g a) (slotsPerm K.system g b)) z'⟩
  congr 1
  apply Subtype.ext
  rw [rename_maps_at K.system g D a b hab]
  change v.1 ((D.maps a b).1 z) = v.1 ((D.maps a b).1 (u.1.symm (u.1 z)))
  rw [u.1.symm_apply_apply]

/-- The actual group action descends, with no relation-compatibility premise. -/
def polytopeRealizationHomeomorph {C : Type} [DecidableEq C]
    (g : Frames K.system C) (D : Presentation K.system C) :
    K.PolytopeRealization D ≃ₜ K.PolytopeRealization (rename K.system g D) :=
  Realization.quotientHomeomorph (K.PolytopeGlueRel D)
    (K.PolytopeGlueRel (rename K.system g D)) (K.polytopeFrameHomeomorph g)
    (K.polytopeGlueRel_rename g D) (by
      intro x y hxy
      have hh := K.polytopeGlueRel_rename g⁻¹ (rename K.system g D) x y hxy
      simpa only [← rename_mul, inv_mul_cancel, rename_one,
        K.polytopeFrameHomeomorph_inv] using hh)

@[simp] theorem polytopeRealizationHomeomorph_cell {C : Type} [DecidableEq C]
    (g : Frames K.system C) (D : Presentation K.system C) (c : C)
    (x : K.PolytopePoint) :
    K.polytopeRealizationHomeomorph g D (K.polytopeCell D c x) =
      K.polytopeCell (rename K.system g D) (g.cell c)
        (K.polytopeHomeomorph (vertexPerm K.system g c) x) := rfl

def polytopeAffineIsoHomeomorph {C : Type} [DecidableEq C]
    {D Q : Presentation K.system C} (e : K.PolytopeAffineIso D Q) :
    K.PolytopeRealization D ≃ₜ K.PolytopeRealization Q := by
  have he : rename K.system e.1 D = Q :=
    (K.polytopeAffineCompatible_iff_action e.1 D Q).mp e.2
  rw [← he]
  exact K.polytopeRealizationHomeomorph e.1 D

end
end PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell
