module

public import Proofs.GeometricFacetExtension
public import Proofs.RegularFlagRestriction
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

/-!
# The actual determinant of a facet restriction

The cell centroid and the facet centroid are fixed. Their difference supplies
a fixed line complementary to the facet direction. Relative to that direct-sum
decomposition the ambient linear map is diag(facet-linear-map, 1). Hence the
ambient and intrinsic determinants, and their orientation signs, coincide.
This does not identify a reflected facet map with an ambient rotation.

-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

section Linear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The explicit splitting by a nonzero transverse vector. Orthogonality is
unnecessary; the determinant is invariant under this change of coordinates. -/
def splitTransverse (W : Submodule ℝ E) (l : E →ₗ[ℝ] ℝ)
    (hW : ∀ x, x ∈ W ↔ l x = 0) (v : E) (hv : l v ≠ 0) :
    (W × ℝ) ≃ₗ[ℝ] E where
  toFun z := (z.1 : E) + z.2 • v
  invFun x := (⟨x - (l x / l v) • v, by
    apply (hW _).mpr
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp [hv]
    ring⟩, l x / l v)
  left_inv := by
    rintro ⟨w, a⟩
    have hw : l (w : E) = 0 := (hW _).mp w.2
    have hcoord : l ((w : E) + a • v) / l v = a := by
      simp [map_add, map_smul, hw, smul_eq_mul, hv]
    apply Prod.ext
    · apply Subtype.ext
      change (w : E) + a • v - (l ((w : E) + a • v) / l v) • v = w
      rw [hcoord]
      abel
    · exact hcoord
  right_inv := by
    intro x
    change x - (l x / l v) • v + (l x / l v) • v = x
    abel
  map_add' := by
    rintro ⟨w, a⟩ ⟨w', a'⟩
    change ((w : E) + (w' : E)) + (a + a') • v =
      ((w : E) + a • v) + ((w' : E) + a' • v)
    rw [add_smul]
    abel
  map_smul' := by
    intro a z
    change a • (z.1 : E) + (a * z.2) • v =
      a • ((z.1 : E) + z.2 • v)
    rw [smul_add, smul_smul]

/-- A determinant lemma whose compatibility assumptions are instantiated below
by the actual geometric restriction, not left in the endpoint theorem. -/
theorem det_eq_facet_of_fixed_transverse [FiniteDimensional ℝ E]
    (W : Submodule ℝ E) (l : E →ₗ[ℝ] ℝ)
    (hW : ∀ x, x ∈ W ↔ l x = 0) (v : E) (hv : l v ≠ 0)
    (L : E →ₗ[ℝ] E) (K : W →ₗ[ℝ] W)
    (hK : ∀ w : W, (K w : E) = L w) (hfix : L v = v) :
    LinearMap.det L = LinearMap.det K := by
  let e := splitTransverse W l hW v hv
  let D := LinearMap.prodMap K (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  have hdiag : ∀ z : W × ℝ, L (e z) = e (D z) := by
    rintro ⟨w, a⟩
    change L ((w : E) + a • v) = (K w : E) + a • v
    rw [map_add, map_smul, hfix, hK]
  have hconj : L = e.toLinearMap ∘ₗ D ∘ₗ e.symm.toLinearMap := by
    ext x
    change L x = e (D (e.symm x))
    simpa using hdiag (e.symm x)
  calc
    LinearMap.det L = LinearMap.det D := by
      rw [hconj, LinearMap.det_conj]
    _ = LinearMap.det K := by
      dsimp [D]
      rw [LinearMap.det_prodMap, LinearMap.det_id, mul_one]

end Linear

section Sign
variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- Orientation is the sign of a real nonzero determinant, not a freely chosen
character on an abstract group. -/
def realUnitSign : ℝˣ →* ℤˣ where
  toFun u := if 0 < (u : ℝ) then 1 else -1
  map_one' := by simp
  map_mul' u v := by
    have hu : (u : ℝ) ≠ 0 := Units.ne_zero u
    have hv : (v : ℝ) ≠ 0 := Units.ne_zero v
    by_cases hup : 0 < (u : ℝ) <;> by_cases hvp : 0 < (v : ℝ)
    · simp [hup, hvp, mul_pos hup hvp]
    · have hvn : (v : ℝ) < 0 := lt_of_le_of_ne (le_of_not_gt hvp) hv
      simp [hup, hvp, not_lt.mpr (mul_neg_of_pos_of_neg hup hvn).le]
    · have hun : (u : ℝ) < 0 := lt_of_le_of_ne (le_of_not_gt hup) hu
      simp [hup, hvp, not_lt.mpr (mul_neg_of_neg_of_pos hun hvp).le]
    · have hun : (u : ℝ) < 0 := lt_of_le_of_ne (le_of_not_gt hup) hu
      have hvn : (v : ℝ) < 0 := lt_of_le_of_ne (le_of_not_gt hvp) hv
      simp [hup, hvp, mul_pos_of_neg_of_neg hun hvn]

/-- Linear parts of the actual affine isometries. -/
def symmetryLinearHom (s : Finset P) : symmetryGroup s →* (V ≃ₗ[ℝ] V) where
  toFun g := g.1.linear
  map_one' := rfl
  map_mul' _ _ := rfl

def euclideanOrientation (s : Finset P) : symmetryGroup s →* ℤˣ :=
  realUnitSign.comp (LinearEquiv.det.comp (symmetryLinearHom s))

@[simp] theorem euclideanOrientation_apply (s : Finset P) (g : symmetryGroup s) :
    euclideanOrientation s g = realUnitSign (LinearEquiv.det g.1.linear) := rfl

theorem euclideanOrientation_eq_one_iff (s : Finset P) (g : symmetryGroup s) :
    euclideanOrientation s g = 1 ↔
      0 < LinearMap.det g.1.toAffineMap.linear := by
  change (if 0 < (LinearEquiv.det g.1.linear : ℝ) then (1 : ℤˣ) else -1) = 1 ↔ _
  rw [LinearEquiv.coe_det]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

end Sign

namespace ExposedFacet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {s t : Finset E} (F : ExposedFacet s t)
include F

/-- The direction of the real facet is the kernel of its supporting form. -/
theorem direction_iff (w : E) :
    w ∈ (affineSpan ℝ (t : Set E)).direction ↔ F.support w = 0 := by
  obtain ⟨p, hp⟩ := F.nonempty
  have hpT := subset_affineSpan ℝ (t : Set E) hp
  have hpval := ((F.vertices p).mp hp).2
  constructor
  · intro hw
    have hwp := (affineSpan ℝ (t : Set E)).vadd_mem_of_mem_direction hw hpT
    have hval := (F.span (w + p)).mp hwp
    rw [map_add, hpval] at hval
    linarith
  · intro hw
    have hwp : w + p ∈ affineSpan ℝ (t : Set E) := by
      apply (F.span _).mpr
      simp [map_add, hw, hpval]
    have h := (affineSpan ℝ (t : Set E)).vsub_mem_direction hwp hpT
    simpa using h

/-- The intrinsic linear map really is the ambient linear map restricted to
the tangent direction. This is deduced from equality on facet points. -/
theorem restriction_linear_apply :
    letI := F.span_nonempty
    ∀ (g : cellFacetStabilizer s t)
      (w : (affineSpan ℝ (t : Set E)).direction),
      ((facetRestriction s t g).1.linear w : E) = g.1.1.linear w := by
  letI := F.span_nonempty
  intro g w
  obtain ⟨p, hp⟩ := F.nonempty
  let p' : affineSpan ℝ (t : Set E) := ⟨p, subset_affineSpan ℝ _ hp⟩
  let b := (facetRestriction s t g).1
  have hb := congrArg (Subtype.val : affineSpan ℝ (t : Set E) → E)
    (b.toAffineMap.map_vadd p' w)
  have hg := g.1.1.toAffineMap.map_vadd p (w : E)
  change g.1.1 ((w : E) + p) = (b.linear w : E) + g.1.1 p at hb
  change g.1.1 ((w : E) + p) = g.1.1.linear w + g.1.1 p at hg
  exact add_right_cancel (hb.symm.trans hg)

/-- Determinant compatibility for every facet stabilizer; regularity is not
needed here. The fixed transverse vector is the difference of the centroids. -/
theorem restriction_det [FiniteDimensional ℝ E] :
    letI := F.span_nonempty
    ∀ g : cellFacetStabilizer s t,
      LinearEquiv.det (facetRestriction s t g).1.linear =
        LinearEquiv.det g.1.1.linear := by
  letI := F.span_nonempty
  intro g
  let W := (affineSpan ℝ (t : Set E)).direction
  let c := s.centroid ℝ id
  let p := t.centroid ℝ id
  have hp : p ∈ affineSpan ℝ (t : Set E) :=
    GeometricFlags.centroid_mem_span t F.nonempty
  have hpval : F.support p = F.level := (F.span p).mp hp
  have hv : F.support (c - p) ≠ 0 := by
    rw [map_sub, hpval]
    exact sub_ne_zero.mpr (ne_of_lt F.centroid_strict)
  have hcfix : g.1.1 c = c := centroid_fixed s F.cell_nonempty g.1
  have hpfix : g.1.1 p = p := centroid_fixed t F.nonempty (facetAmbientHom s t g)
  have hfix : g.1.1.toAffineMap.linear (c - p) = c - p := by
    change g.1.1.toAffineMap.linear (c -ᵥ p) = c -ᵥ p
    rw [g.1.1.toAffineMap.linearMap_vsub]
    change g.1.1 c -ᵥ g.1.1 p = c -ᵥ p
    rw [hcfix, hpfix]
  have hd := det_eq_facet_of_fixed_transverse W F.support F.direction_iff
    (c - p) hv g.1.1.toAffineMap.linear
    (facetRestriction s t g).1.toAffineMap.linear
    (F.restriction_linear_apply g) hfix
  apply Units.ext
  simp only [LinearEquiv.coe_det]
  convert hd.symm using 1 <;> rfl

/-- This discharges, for the actual geometric restriction, the orientation
compatibility assumed by the old abstract restriction interface. -/
theorem restriction_orientation [FiniteDimensional ℝ E] :
    letI := F.span_nonempty
    ∀ g : cellFacetStabilizer s t,
      euclideanOrientation (spanVertices t) (facetRestriction s t g) =
        euclideanOrientation s g.1 := by
  letI := F.span_nonempty
  intro g
  simp only [euclideanOrientation_apply, F.restriction_det g]

/-- The resulting isomorphism of the actual orientation-preserving groups. -/
def rotationRestrictionEquiv [FiniteDimensional ℝ E]
    (regular : GeometricFlags.IsFlagRegular s) :
    letI := F.span_nonempty
    ((euclideanOrientation s).comp (cellFacetStabilizer s t).subtype).ker ≃*
      (euclideanOrientation (spanVertices t)).ker := by
  letI := F.span_nonempty
  exact RegularFacet.rotationRestrictionEquiv (F.restrictionEquiv regular)
    ((euclideanOrientation s).comp (cellFacetStabilizer s t).subtype)
    (euclideanOrientation (spanVertices t)) F.restriction_orientation

/-- Both full-group and rotation-group orders now use intrinsic facet
symmetries, with neither rigidity nor orientation compatibility as a premise. -/
theorem rotation_stabilizer_card [FiniteDimensional ℝ E]
    (regular : GeometricFlags.IsFlagRegular s) :
    letI := F.span_nonempty
    Nat.card (((euclideanOrientation s).comp (cellFacetStabilizer s t).subtype).ker) =
      Nat.card ((euclideanOrientation (spanVertices t)).ker) := by
  letI := F.span_nonempty
  exact Nat.card_congr (F.rotationRestrictionEquiv regular).toEquiv

end ExposedFacet
end
end PolytopeCounting.FacetPairing.EuclideanGeometry
