module

public import Proofs.GeometricPresentationMass

@[expose] public section

/-!
# Facet palettes from signed symmetry groups

The input is a finite symmetry group acting on facets, with an orientation
character. Positive symmetries are facet-transitive and a negative symmetry
fixes a reference facet. No palette or gluing cardinality is assumed.

For a geometric application the group must act faithfully by actual cell
symmetries, and restriction must identify the transporters with the intended
facet isometries. This file proves the group-theoretic step, not that geometric
extension theorem for an arbitrary Euclidean regular polytope.
-/

namespace PolytopeCounting.FacetPairing.RegularFacet
noncomputable section
open scoped BigOperators

variable {G : Type*} [Group G] {h : ℕ}

structure System (G : Type*) [Group G] (h : ℕ) where
  facet : G →* Equiv.Perm (Fin h)
  orientation : G →* ℤˣ
  base : Fin h
  transitive : ∀ i, ∃ g : G, facet g base = i ∧ orientation g = 1
  reflection : ∃ g : G, facet g base = base ∧ orientation g = -1

namespace System

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

variable (S : System G h)

abbrev Rotation := S.orientation.ker

/-- Positive symmetries fixing the reference facet. -/
def facetRotation : Subgroup G where
  carrier := {g | S.facet g S.base = S.base ∧ S.orientation g = 1}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha,sa⟩ ⟨hb,sb⟩
    simp [map_mul, Equiv.Perm.mul_apply, ha, hb, sa, sb]
  inv_mem' := by
    rintro a ⟨ha,sa⟩
    constructor
    · rw [map_inv]
      exact (S.facet a).symm_apply_eq.mpr ha.symm
    · simp [map_inv,sa]

abbrev Gluing (i j : Fin h) :=
  {g : G // S.facet g i = j ∧ S.orientation g = -1}

def chart (i : Fin h) : G := Classical.choose (S.transitive i)
@[simp] theorem chart_base (i : Fin h) : S.facet (S.chart i) S.base = i :=
  (Classical.choose_spec (S.transitive i)).1
@[simp] theorem chart_sign (i : Fin h) : S.orientation (S.chart i) = 1 :=
  (Classical.choose_spec (S.transitive i)).2

def mirror : G := Classical.choose S.reflection
@[simp] theorem mirror_base : S.facet S.mirror S.base = S.base :=
  (Classical.choose_spec S.reflection).1
@[simp] theorem mirror_sign : S.orientation S.mirror = -1 :=
  (Classical.choose_spec S.reflection).2

@[simp] theorem chart_inv_target (i : Fin h) : S.facet (S.chart i)⁻¹ i = S.base := by
  rw [map_inv]
  exact (S.facet (S.chart i)).symm_apply_eq.mpr (S.chart_base i).symm

@[simp] theorem mirror_inv_base : S.facet S.mirror⁻¹ S.base = S.base := by
  rw [map_inv]
  exact (S.facet S.mirror).symm_apply_eq.mpr S.mirror_base.symm

/-- Every admissible transporter, not just a selected collection, is encoded. -/
def gluingEquiv (i j : Fin h) : S.facetRotation ≃ S.Gluing i j where
  toFun k := ⟨S.chart j * S.mirror * k.1 * (S.chart i)⁻¹, by
    constructor
    · simp only [map_mul, Equiv.Perm.mul_apply, chart_inv_target]
      rw [k.2.1, S.mirror_base, S.chart_base]
    · simp [map_mul, map_inv, k.2.2]⟩
  invFun g := ⟨S.mirror⁻¹ * (S.chart j)⁻¹ * g.1 * S.chart i, by
    constructor
    · simp only [map_mul, Equiv.Perm.mul_apply, chart_base]
      rw [g.2.1, S.chart_inv_target, S.mirror_inv_base]
    · simp [map_mul, map_inv, g.2.2]⟩
  left_inv k := by apply Subtype.ext; dsimp; group
  right_inv g := by apply Subtype.ext; dsimp; group

/-- The same stabilizer accounts for cell rotations: tau = h * r. -/
def rotationEquiv : S.Rotation ≃ Fin h × S.facetRotation where
  toFun g := ⟨S.facet g.1 S.base, ⟨(S.chart (S.facet g.1 S.base))⁻¹ * g.1, by
    constructor
    · simpa only [map_mul, Equiv.Perm.mul_apply] using
        S.chart_inv_target (S.facet g.1 S.base)
    · simp [map_mul, map_inv, show S.orientation g.1 = 1 from g.2]⟩⟩
  invFun x := ⟨S.chart x.1 * x.2.1, by
    change S.orientation (S.chart x.1 * x.2.1) = 1
    simp [map_mul, x.2.2.2]⟩
  left_inv g := by apply Subtype.ext; dsimp; group
  right_inv x := by
    rcases x with ⟨i,k⟩
    have hi : S.facet (S.chart i * k.1) S.base = i := by
      simp only [map_mul, Equiv.Perm.mul_apply, k.2.1, chart_base]
    apply Prod.ext
    · exact hi
    · apply Subtype.ext
      change (S.chart (S.facet (S.chart i * k.1) S.base))⁻¹ * (S.chart i * k.1) = k.1
      rw [hi]; group

variable [Fintype G]

/-- A palette is now constructed, not supplied as a hypothesis. -/
def palette (i j : Fin h) : Fin (Fintype.card S.facetRotation) ≃ S.Gluing i j :=
  (Fintype.equivFin S.facetRotation).symm.trans (S.gluingEquiv i j)

theorem gluing_card (i j : Fin h) :
    Fintype.card (S.Gluing i j) = Fintype.card S.facetRotation :=
  (Fintype.card_congr (S.gluingEquiv i j)).symm

theorem rotation_card : Fintype.card S.Rotation = h * Fintype.card S.facetRotation := by
  rw [Fintype.card_congr S.rotationEquiv, Fintype.card_prod, Fintype.card_fin]

end System
end
end PolytopeCounting.FacetPairing.RegularFacet
