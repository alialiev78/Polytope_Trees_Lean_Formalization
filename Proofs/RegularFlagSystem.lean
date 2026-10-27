module

public import Proofs.RegularFlagRestriction

@[expose] public section

/-!
# From oriented regular flags to a signed facet system

Regularity is transitivity on flags. Changing a lower-dimensional face in a
flag keeps its facet and reverses flag orientation. These incidence hypotheses
suffice to derive positive facet transitivity and a negative facet stabilizer;
neither condition on the resulting palette is postulated here.
-/

namespace PolytopeCounting.FacetPairing.RegularFacet
noncomputable section
attribute [local instance] Classical.propDecidable

variable {G F : Type*} [Group G] [MulAction G F] {h : ℕ}

structure OrientedFlags (G F : Type*) [Group G] [MulAction G F] (h : ℕ) where
  facetAction : G →* Equiv.Perm (Fin h)
  orientation : G →* ℤˣ
  facetOf : F → Fin h
  facet_surjective : Function.Surjective facetOf
  facet_equivariant : ∀ g f, facetOf (g • f) = facetAction g (facetOf f)
  base : F
  transitive : ∀ f, ∃ g : G, g • base = f
  flagSign : F → ℤˣ
  base_positive : flagSign base = 1
  sign_equivariant : ∀ g f, flagSign (g • f) = orientation g * flagSign f
  adjacent : F → F
  adjacent_facet : ∀ f, facetOf (adjacent f) = facetOf f
  adjacent_sign : ∀ f, flagSign (adjacent f) = - flagSign f

namespace OrientedFlags
variable (R : OrientedFlags G F h)

theorem positive_flag (i : Fin h) : ∃ f, R.facetOf f = i ∧ R.flagSign f = 1 := by
  obtain ⟨f,hf⟩ := R.facet_surjective i
  rcases Int.units_eq_one_or (R.flagSign f) with hs | hs
  · exact ⟨f,hf,hs⟩
  · exact ⟨R.adjacent f, (R.adjacent_facet f).trans hf, by rw [R.adjacent_sign, hs]; simp⟩

/-- The hypotheses defining a signed facet system follow from flag regularity. -/
def toSystem : System G h where
  facet := R.facetAction
  orientation := R.orientation
  base := R.facetOf R.base
  transitive i := by
    obtain ⟨f,hf,hs⟩ := R.positive_flag i
    obtain ⟨g,hg⟩ := R.transitive f
    refine ⟨g, ?_, ?_⟩
    · rw [← R.facet_equivariant, hg, hf]
    · have he := R.sign_equivariant g R.base
      rw [hg, hs, R.base_positive, mul_one] at he
      exact he.symm
  reflection := by
    obtain ⟨g,hg⟩ := R.transitive (R.adjacent R.base)
    refine ⟨g, ?_, ?_⟩
    · rw [← R.facet_equivariant, hg, R.adjacent_facet]
    · have he := R.sign_equivariant g R.base
      rw [hg, R.adjacent_sign, R.base_positive, mul_one] at he
      exact he.symm

variable [Fintype G]

theorem gluing_card (i j : Fin h) :
    Fintype.card (R.toSystem.Gluing i j) = Fintype.card R.toSystem.facetRotation :=
  R.toSystem.gluing_card i j

theorem rotation_card :
    Fintype.card R.toSystem.Rotation = h * Fintype.card R.toSystem.facetRotation :=
  R.toSystem.rotation_card

end OrientedFlags
end
end PolytopeCounting.FacetPairing.RegularFacet
