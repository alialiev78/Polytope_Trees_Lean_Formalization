module

public import Proofs.EuclideanFacetRestriction

@[expose] public section

/-!
# Rigidity of restriction to an exposed facet

An exposed facet is described by a supporting linear functional: its vertices
are exactly the maximizing cell vertices and span the supporting hyperplane.
The cell centroid lies strictly inside the supporting half-space. Consequently
it and the facet span the ambient space, proving that geometric restriction is
injective without a supplied flag-rigidity hypothesis.
-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {s t : Finset E}

/-- Standard supporting-hyperplane data for a proper facet of `convexHull s`. -/
structure ExposedFacet (s t : Finset E) where
  nonempty : t.Nonempty
  support : E →ₗ[ℝ] ℝ
  level : ℝ
  below : ∀ x ∈ s, support x ≤ level
  vertices : ∀ x, x ∈ t ↔ x ∈ s ∧ support x = level
  proper : ∃ x ∈ s, support x < level
  span : ∀ x, x ∈ affineSpan ℝ (t : Set E) ↔ support x = level

namespace ExposedFacet
variable (F : ExposedFacet s t)
include F

theorem cell_nonempty : s.Nonempty := by
  obtain ⟨x,hx,_⟩ := F.proper
  exact ⟨x,hx⟩

theorem span_nonempty : Nonempty (affineSpan ℝ (t : Set E)) := by
  obtain ⟨x,hx⟩ := F.nonempty
  exact ⟨⟨x,subset_affineSpan ℝ (t : Set E) hx⟩⟩

theorem centroid_strict : F.support (s.centroid ℝ id) < F.level := by
  have hp : (0 : ℝ) < s.card := by exact_mod_cast F.cell_nonempty.card_pos
  have hsum : (∑ x ∈ s, F.support x) < (s.card : ℝ) * F.level := by
    calc
      (∑ x ∈ s, F.support x) < ∑ _x ∈ s, F.level := Finset.sum_lt_sum F.below F.proper
      _ = _ := by simp
  rw [Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination _ _ _
      (s.sum_centroidWeights_eq_one_of_nonempty ℝ F.cell_nonempty)]
  simp only [map_sum, map_smul, Finset.centroidWeights_apply, id_eq, smul_eq_mul,
    ← Finset.mul_sum]
  exact (inv_mul_lt_iff₀ hp).mpr hsum

/-- The centroid and the facet span the entire ambient affine space. -/
theorem span_with_centroid :
    affineSpan ℝ (insert (s.centroid ℝ id) (t : Set E)) = ⊤ := by
  let c := s.centroid ℝ id
  let A := affineSpan ℝ (insert c (t : Set E))
  obtain ⟨p,hp⟩ := F.nonempty
  have hpval : F.support p = F.level := (F.vertices p).mp hp |>.2
  have hden : F.support c - F.level ≠ 0 := sub_ne_zero.mpr (ne_of_lt F.centroid_strict)
  have hc : c ∈ A := subset_affineSpan ℝ _ (Set.mem_insert _ _)
  have hmono : affineSpan ℝ (t : Set E) ≤ A :=
    affineSpan_mono ℝ (Set.subset_insert c (t : Set E))
  have hpA : p ∈ A := hmono (subset_affineSpan ℝ (t : Set E) hp)
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
  have hxA := A.smul_vsub_vadd_mem a hc hpA hyA
  have he : a • (c -ᵥ p) +ᵥ y = x := by
    change a • (c-p) + (x - a • (c-p)) = x
    abel
  rw [he] at hxA
  exact hxA

/-- For an actual exposed facet, restriction of cell symmetries is faithful. -/
theorem restriction_injective :
    letI := F.span_nonempty
    Function.Injective (facetRestriction s t) := by
  let := F.span_nonempty
  exact facetRestriction_injective s t F.cell_nonempty F.span_with_centroid

end ExposedFacet
end
end PolytopeCounting.FacetPairing.EuclideanGeometry
