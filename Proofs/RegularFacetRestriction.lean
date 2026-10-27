module

public import Proofs.RegularFlagSystem

@[expose] public section

/-!
# A facet restriction theorem derived from full flag regularity

The transitivity needed by `restrictionEquivOfFlags` is discharged for a
facet stabilizer using full flag transitivity. Only the usual flag rigidity
and compatibility of geometric restriction are supplied by an application.
-/

namespace PolytopeCounting.FacetPairing.RegularFacet.OrientedFlags
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

variable {G F : Type*} [Group G] [MulAction G F] {h : ℕ}
variable (R : OrientedFlags G F h)

def stabilizer : Subgroup G where
  carrier := {g | R.facetAction g (R.facetOf R.base) = R.facetOf R.base}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change R.facetAction a (R.facetOf R.base) = R.facetOf R.base at ha
    change R.facetAction b (R.facetOf R.base) = R.facetOf R.base at hb
    simp [map_mul, Equiv.Perm.mul_apply,ha,hb]
  inv_mem' := by
    intro a ha
    change R.facetAction a⁻¹ (R.facetOf R.base) = R.facetOf R.base
    rw [map_inv]
    exact (R.facetAction a).symm_apply_eq.mpr ha.symm

abbrev FacetFlags := {f : F // R.facetOf f = R.facetOf R.base}

def facetBase : R.FacetFlags := ⟨R.base,rfl⟩

instance : MulAction R.stabilizer R.FacetFlags where
  smul g f := ⟨g.1 • f.1, by rw [R.facet_equivariant,f.2]; exact g.2⟩
  one_smul f := by apply Subtype.ext; exact one_smul G f.1
  mul_smul g k f := by apply Subtype.ext; exact mul_smul g.1 k.1 f.1

theorem facet_transitive (f : R.FacetFlags) :
    ∃ g : R.stabilizer, g • R.facetBase = f := by
  obtain ⟨g,hg⟩ := R.transitive f.1
  have hm : g ∈ R.stabilizer := by
    change R.facetAction g (R.facetOf R.base) = R.facetOf R.base
    rw [← R.facet_equivariant,hg,f.2]
  exact ⟨⟨g,hm⟩, Subtype.ext hg⟩

theorem facet_rigid
    (rigid : Function.Injective (fun g : G ↦ g • R.base)) :
    Function.Injective (fun g : R.stabilizer ↦ g • R.facetBase) := by
  intro g k he
  apply Subtype.ext
  apply rigid
  exact congrArg Subtype.val he

variable {B : Type*} [Group B] [MulAction B R.FacetFlags]

/-- Every facet symmetry extends uniquely. Bijectivity is a conclusion, not
an input. In a geometric application `restriction` is restriction of a cell
isometry to its facet. -/
def restrictionEquiv (restriction : R.stabilizer →* B)
    (compatible : ∀ g, restriction g • R.facetBase = g • R.facetBase)
    (cell_rigid : Function.Injective (fun g : G ↦ g • R.base))
    (facet_rigid : Function.Injective (fun b : B ↦ b • R.facetBase)) :
    R.stabilizer ≃* B :=
  restrictionEquivOfFlags restriction R.facetBase compatible R.facet_transitive
    (R.facet_rigid cell_rigid) facet_rigid

/-- Repackaging a positive facet stabilizer as the kernel of its orientation. -/
def positiveStabilizerEquiv : R.toSystem.facetRotation ≃*
    (R.orientation.comp R.stabilizer.subtype).ker where
  toFun g := ⟨⟨g.1,g.2.1⟩,g.2.2⟩
  invFun g := ⟨g.1.1,⟨g.1.2,g.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The parameter r really is the order of the facet rotation group whenever
the geometric flag action and orientation-compatible restriction are given. -/
def facetRotationEquiv (restriction : R.stabilizer →* B)
    (compatible : ∀ g, restriction g • R.facetBase = g • R.facetBase)
    (cell_rigid : Function.Injective (fun g : G ↦ g • R.base))
    (facet_rigid : Function.Injective (fun b : B ↦ b • R.facetBase))
    (signB : B →* ℤˣ)
    (orientation : ∀ g, signB (restriction g) = R.orientation g.1) :
    R.toSystem.facetRotation ≃* signB.ker :=
  R.positiveStabilizerEquiv.trans
    (rotationRestrictionEquiv
      (R.restrictionEquiv restriction compatible cell_rigid facet_rigid)
      (R.orientation.comp R.stabilizer.subtype) signB orientation)

end
end PolytopeCounting.FacetPairing.RegularFacet.OrientedFlags
