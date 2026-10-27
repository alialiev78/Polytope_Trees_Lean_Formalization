module

public import Proofs.RegularFacetPalette

@[expose] public section

/-!
# Extension of facet symmetries from regular flag actions

This is the restriction/extension argument: it assumes transitivity on flags
and uniqueness of a symmetry from its action on one flag, rather than assuming
that restriction is bijective. The interpretation of these flags as geometric
flags of every Euclidean regular polytope is a separate input.
-/

namespace PolytopeCounting.FacetPairing.RegularFacet
noncomputable section

variable {A B F : Type*} [Group A] [Group B] [MulAction A F] [MulAction B F]

/-- A compatible restriction homomorphism is bijective when the source is
transitive on flags and both groups act freely on a chosen flag. -/
theorem restriction_bijective_of_flags (restriction : A →* B) (flag : F)
    (compatible : ∀ a : A, restriction a • flag = a • flag)
    (transitive : ∀ f : F, ∃ a : A, a • flag = f)
    (source_rigid : Function.Injective (fun a : A ↦ a • flag))
    (target_rigid : Function.Injective (fun b : B ↦ b • flag)) :
    Function.Bijective restriction := by
  constructor
  · intro a b hab
    apply source_rigid
    change a • flag = b • flag
    rw [← compatible a, ← compatible b, hab]
  · intro b
    obtain ⟨a,ha⟩ := transitive (b • flag)
    exact ⟨a, target_rigid ((compatible a).trans ha)⟩

def restrictionEquivOfFlags (restriction : A →* B) (flag : F)
    (compatible : ∀ a : A, restriction a • flag = a • flag)
    (transitive : ∀ f : F, ∃ a : A, a • flag = f)
    (source_rigid : Function.Injective (fun a : A ↦ a • flag))
    (target_rigid : Function.Injective (fun b : B ↦ b • flag)) : A ≃* B :=
  MulEquiv.ofBijective restriction
    (restriction_bijective_of_flags restriction flag compatible transitive source_rigid target_rigid)

/-- Restriction identifies rotation groups as soon as it preserves orientation. -/
def rotationRestrictionEquiv (e : A ≃* B) (sA : A →* ℤˣ) (sB : B →* ℤˣ)
    (orientation : ∀ a, sB (e a) = sA a) : sA.ker ≃* sB.ker where
  toFun a := ⟨e a.1, by change sB (e a.1) = 1; rw [orientation]; exact a.2⟩
  invFun b := ⟨e.symm b.1, by
    change sA (e.symm b.1) = 1
    rw [← orientation, e.apply_symm_apply]; exact b.2⟩
  left_inv a := by apply Subtype.ext; exact e.symm_apply_apply a.1
  right_inv b := by apply Subtype.ext; exact e.apply_symm_apply b.1
  map_mul' a b := by apply Subtype.ext; exact e.map_mul a.1 b.1

end
end PolytopeCounting.FacetPairing.RegularFacet
