module

public import Proofs.AffineFlagRigidity
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# Actual Euclidean symmetry groups of finite vertex configurations

The group is defined directly from affine isometries preserving the vertex set.
Its finiteness is proved from affine spanning, not assumed. Restriction to the
affine span of an invariant vertex set is constructed as an affine isometry.
-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

section Affine

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MetricSpace E] [NormedAddTorsor V E]

/-- All Euclidean symmetries of a finite vertex configuration. -/
def symmetryGroup (s : Finset E) : Subgroup (E ≃ᵃⁱ[ℝ] E) where
  carrier := {g | ∀ x, g x ∈ s ↔ x ∈ s}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro g k hg hk x
    exact (hg (k x)).trans (hk x)
  inv_mem' := by
    intro g hg x
    exact (hg (g.symm x)).symm.trans (by rw [g.apply_symm_apply])

variable (s : Finset E)

def vertexPermutation (g : symmetryGroup s) : Equiv.Perm {x : E // x ∈ s} where
  toFun x := ⟨g.1 x.1,(g.2 x.1).mpr x.2⟩
  invFun x := ⟨g.1.symm x.1, by
    apply (g.2 (g.1.symm x.1)).mp
    simpa only [g.1.apply_symm_apply] using x.2⟩
  left_inv x := by apply Subtype.ext; exact g.1.symm_apply_apply x.1
  right_inv x := by apply Subtype.ext; exact g.1.apply_symm_apply x.1

/-- Actual ambient symmetries are determined by their vertex permutation. -/
theorem vertexPermutation_injective (span : affineSpan ℝ (s : Set E) = ⊤) :
    Function.Injective (vertexPermutation s) := by
  intro g k he
  apply Subtype.ext
  apply AffineIsometryEquiv.toAffineEquiv_injective
  apply AffineEquiv.ext_on span
  intro x hx
  exact congrArg Subtype.val (Equiv.congr_fun he ⟨x,hx⟩)

theorem finiteSymmetries (span : affineSpan ℝ (s : Set E) = ⊤) : Finite (symmetryGroup s) :=
  Finite.of_injective (vertexPermutation s) (vertexPermutation_injective s span)

@[instance_reducible]
def fintypeSymmetries (span : affineSpan ℝ (s : Set E) = ⊤) : Fintype (symmetryGroup s) := by
  letI := finiteSymmetries s span
  exact Fintype.ofFinite _

theorem image_vertices (g : symmetryGroup s) : g.1 '' (s : Set E) = s := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (g.2 y).mpr hy
  · intro hx
    exact ⟨g.1.symm x, by
      apply (g.2 (g.1.symm x)).mp
      simpa using hx, g.1.apply_symm_apply x⟩

theorem map_span (g : symmetryGroup s) :
    (affineSpan ℝ (s : Set E)).map g.1.toAffineMap = affineSpan ℝ (s : Set E) := by
  rw [AffineSubspace.map_span]
  congr 1
  exact image_vertices s g


/-- A cell symmetry fixes the centroid of its entire vertex set. -/
theorem centroid_fixed (hs : s.Nonempty) (g : symmetryGroup s) :
    g.1 (s.centroid ℝ id) = s.centroid ℝ id := by
  change g.1.toAffineMap (s.affineCombination ℝ id (s.centroidWeights ℝ)) = _
  rw [Finset.map_affineCombination _ _ _ (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  change s.centroid ℝ (fun x ↦ g.1 x) = s.centroid ℝ id
  apply Finset.centroid_eq_of_inj_on_of_image_eq
  · intro x _ y _ he
    exact g.1.injective he
  · intro x _ y _ he
    exact he
  · simpa using image_vertices s g

/-- Restriction is a genuine isometry of the facet's affine span. -/
def restriction [Nonempty (affineSpan ℝ (s : Set E))] (g : symmetryGroup s) :
    affineSpan ℝ (s : Set E) ≃ᵃⁱ[ℝ] affineSpan ℝ (s : Set E) :=
  ((affineSpan ℝ (s : Set E)).isometryEquivMap g.1.toAffineIsometry).trans
    (AffineIsometryEquiv.ofEq _ _ (map_span s g))

@[simp] theorem restriction_apply [Nonempty (affineSpan ℝ (s : Set E))]
    (g : symmetryGroup s) (x : affineSpan ℝ (s : Set E)) :
    (restriction s g x : E) = g.1 x := rfl

/-- Multiplication is preserved by restriction, with no supplied homomorphism. -/
def restrictionHom [Nonempty (affineSpan ℝ (s : Set E))] :
    symmetryGroup s →* (affineSpan ℝ (s : Set E) ≃ᵃⁱ[ℝ] affineSpan ℝ (s : Set E)) where
  toFun := restriction s
  map_one' := by ext x; rfl
  map_mul' g k := by ext x; rfl

end Affine

section Vector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (s : Finset E)

/-- These vertex symmetries preserve the actual convex polytope. -/
theorem image_convexHull (g : symmetryGroup s) :
    g.1 '' convexHull ℝ (s : Set E) = convexHull ℝ (s : Set E) := by
  change g.1.toAffineMap '' convexHull ℝ (s : Set E) = _
  rw [AffineMap.image_convexHull]
  congr 1
  exact image_vertices s g

end Vector

end
end PolytopeCounting.FacetPairing.EuclideanGeometry
