module

public import Proofs.RegularPolytopeReflections
public import Proofs.RegularPolytopeMass

@[expose] public section

/-!
# All facets and the concrete `OrientedFlags` structure

The facet type is the finite set of maximal proper supporting vertex sets.
Its indexing, geometric group action, flag orientation, and within-facet
orientation flip are constructed from a nonempty spanning flag-regular cell.
The flip is transported from a negative involution in the base facet
stabilizer. The old interface requires facet preservation and sign reversal,
not that the flip be an elementary rank-adjacency operation; we do not claim
the latter here.

No oriented flag system, negative stabilizer, or palette is a premise.
-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry
noncomputable section
open GeometricFlags
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

universe u
variable {V P : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

namespace GeometricFlags

def facetSets (s : Finset P) : Finset (Finset P) := s.powerset.filter (Facet s)
abbrev Facets (s : Finset P) := {t : Finset P // t ∈ facetSets s}

@[simp] theorem mem_facetSets {s t : Finset P} : t ∈ facetSets s ↔ Facet s t := by
  exact ⟨fun h ↦ (Finset.mem_filter.mp h).2,
    fun h ↦ Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1.subset, h⟩⟩

def Facets.ofFacet {s t : Finset P} (H : Facet s t) : Facets s :=
  ⟨t, mem_facetSets.mpr H⟩

theorem Facets.isFacet {s : Finset P} (t : Facets s) : Facet s t.1 :=
  mem_facetSets.mp t.2

/-- Indexing is of the actual finite facet set, not an input list of slots. -/
abbrev facetCount (s : Finset P) : ℕ := Fintype.card (Facets s)
def facetIndex (s : Finset P) : Facets s ≃ Fin (facetCount s) := Fintype.equivFin _

def mapFacet {s : Finset P} (g : symmetryGroup s) (t : Facets s) : Facets s :=
  Facets.ofFacet (s := s) (t := t.1.image g.1) (by
    have h := t.isFacet.map g.1.toAffineMap g.1.injective
    change Facet (s.image g.1) (t.1.image g.1) at h
    rw [symmetry_image_finset] at h
    exact h)

@[simp] theorem mapFacet_val {s : Finset P} (g : symmetryGroup s) (t : Facets s) :
    (mapFacet g t).1 = t.1.image g.1 := rfl

def facetPerm (s : Finset P) (g : symmetryGroup s) : Equiv.Perm (Facets s) where
  toFun := mapFacet g
  invFun := mapFacet g⁻¹
  left_inv t := by
    apply Subtype.ext
    change (t.1.image g.1).image g.1.symm = t.1
    simp [Finset.image_image, Function.comp_def]
  right_inv t := by
    apply Subtype.ext
    change (t.1.image g.1.symm).image g.1 = t.1
    simp [Finset.image_image, Function.comp_def]

def indexedFacetAction (s : Finset P) : symmetryGroup s →* Equiv.Perm (Fin (facetCount s)) where
  toFun g := ((facetIndex s).symm.trans (facetPerm s g)).trans (facetIndex s)
  map_one' := by
    apply Equiv.ext
    intro i
    apply (facetIndex s).symm.injective
    apply Subtype.ext
    simp [facetPerm, mapFacet, Facets.ofFacet]
  map_mul' g k := by
    apply Equiv.ext
    intro i
    apply (facetIndex s).symm.injective
    apply Subtype.ext
    simp [facetPerm, mapFacet, Facets.ofFacet, Finset.image_image, Function.comp_def]

@[simp] theorem indexedFacetAction_apply (s : Finset P) (g : symmetryGroup s)
    (i : Fin (facetCount s)) :
    indexedFacetAction s g i = facetIndex s (mapFacet g ((facetIndex s).symm i)) := rfl

theorem indexedFacetAction_fix_iff (s : Finset P) (g : symmetryGroup s) (t : Facets s) :
    indexedFacetAction s g (facetIndex s t) = facetIndex s t ↔
      ∀ x, g.1 x ∈ t.1 ↔ x ∈ t.1 := by
  rw [indexedFacetAction_apply, (facetIndex s).symm_apply_apply,
    (facetIndex s).injective.eq_iff]
  constructor
  · intro he
    exact preserves_finset_of_image g.1 g.1.injective (congrArg Subtype.val he)
  · intro hp
    apply Subtype.ext
    exact symmetry_image_finset (s := t.1) ⟨g.1, hp⟩

/-- A complete flag of a nonsingleton cell has a first proper facet. -/
theorem FullFlag.first_isFacet {s : Finset P} (big : 1 < s.card) (A : FullFlag s) :
    Facet s (A.1.headD ∅) := by
  rcases A with ⟨l, hl⟩
  cases l with
  | nil =>
    cases hl with
    | point p => simp at big
  | cons t l =>
    cases hl with
    | step H ht => exact H

def flagFacet {s : Finset P} (big : 1 < s.card) (A : FullFlag s) : Facets s :=
  Facets.ofFacet (A.first_isFacet big)

theorem flagFacet_surjective {s : Finset P} (big : 1 < s.card) :
    Function.Surjective (flagFacet big) := by
  intro t
  obtain ⟨B⟩ := fullFlag_nonempty t.1 t.isFacet.1.1
  let A : FullFlag s := ⟨t.1 :: B.1, CompleteChain.step t.isFacet B.2⟩
  exact ⟨A, Subtype.ext rfl⟩

theorem flagFacet_equivariant {s : Finset P} (big : 1 < s.card)
    (g : symmetryGroup s) (A : FullFlag s) :
    flagFacet big (g • A) = mapFacet g (flagFacet big A) := by
  apply Subtype.ext
  rcases A with ⟨l, hl⟩
  cases l with
  | nil =>
    cases hl with
    | point p => simp at big
  | cons t l => rfl

def indexedFlagFacet {s : Finset P} (big : 1 < s.card) (A : FullFlag s) :
    Fin (facetCount s) := facetIndex s (flagFacet big A)

theorem indexedFlagFacet_equivariant {s : Finset P} (big : 1 < s.card)
    (g : symmetryGroup s) (A : FullFlag s) :
    indexedFlagFacet big (g • A) = indexedFacetAction s g (indexedFlagFacet big A) := by
  simp only [indexedFlagFacet, indexedFacetAction_apply, Equiv.symm_apply_apply,
    flagFacet_equivariant]

end GeometricFlags

/-- Ordinary geometric input: a finite spanning cell, Euclidean flag
regularity, and dimension at least two. None of the remaining interface fields
(palettes, orientation flips, restriction isomorphisms) is bundled as input. -/
structure RegularCell (V P : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V] where
  vertices : Finset P
  nonempty : vertices.Nonempty
  full_span : affineSpan ℝ (vertices : Set P) = ⊤
  regular : GeometricFlags.IsFlagRegular vertices
  dimension : 2 ≤ Module.finrank ℝ V

namespace RegularCell
variable [FiniteDimensional ℝ V] (K : RegularCell V P)

abbrev Group := symmetryGroup K.vertices
abbrev Flags := FullFlag K.vertices
abbrev Facets := GeometricFlags.Facets K.vertices
abbrev h := GeometricFlags.facetCount K.vertices

noncomputable instance groupFintype : Fintype K.Group :=
  fintypeSymmetries K.vertices K.full_span

theorem many_vertices : 1 < K.vertices.card :=
  nontrivial_vertex_set K.nonempty K.full_span (by have := K.dimension; omega)

def baseFlag : K.Flags := Classical.choice (fullFlag_nonempty K.vertices K.nonempty)
def baseFacet : K.Facets := flagFacet K.many_vertices K.baseFlag

def frameEquiv : K.Group ≃ K.Flags :=
  symmetryFlagEquiv K.full_span K.regular K.baseFlag

def flagFrame (A : K.Flags) : K.Group := K.frameEquiv.symm A

@[simp] theorem flagFrame_apply (A : K.Flags) : K.flagFrame A • K.baseFlag = A :=
  K.frameEquiv.apply_symm_apply A

@[simp] theorem flagFrame_base : K.flagFrame K.baseFlag = 1 := by
  apply K.frameEquiv.injective
  change K.flagFrame K.baseFlag • K.baseFlag = (1 : K.Group) • K.baseFlag
  rw [K.flagFrame_apply, one_smul]

@[simp] theorem flagFrame_smul (g : K.Group) (A : K.Flags) :
    K.flagFrame (g • A) = g * K.flagFrame A := by
  apply K.frameEquiv.injective
  change K.flagFrame (g • A) • K.baseFlag = (g * K.flagFrame A) • K.baseFlag
  rw [K.flagFrame_apply, mul_smul, K.flagFrame_apply]

/-- The mirror is an actual negative involution fixing the chosen facet. -/
def baseMirror : cellFacetStabilizer K.vertices K.baseFacet.1 :=
  Classical.choose (K.baseFacet.isFacet.exists_negative_stabilizer
    K.full_span K.regular K.dimension)

@[simp] theorem baseMirror_sign : euclideanOrientation K.vertices K.baseMirror.1 = -1 :=
  (Classical.choose_spec (K.baseFacet.isFacet.exists_negative_stabilizer
    K.full_span K.regular K.dimension)).1

@[simp] theorem baseMirror_square : K.baseMirror * K.baseMirror = 1 :=
  (Classical.choose_spec (K.baseFacet.isFacet.exists_negative_stabilizer
    K.full_span K.regular K.dimension)).2

def flagSign (A : K.Flags) : ℤˣ := euclideanOrientation K.vertices (K.flagFrame A)

theorem flagSign_equivariant (g : K.Group) (A : K.Flags) :
    K.flagSign (g • A) = euclideanOrientation K.vertices g * K.flagSign A := by
  simp only [flagSign, K.flagFrame_smul, map_mul]

/-- A geometric involution inside each facet fibre. It reverses orientation;
no assertion of elementary rank-adjacency is needed by `OrientedFlags`. -/
def flagFlip (A : K.Flags) : K.Flags :=
  (K.flagFrame A * K.baseMirror.1) • K.baseFlag

theorem flagFlip_facet (A : K.Flags) :
    indexedFlagFacet K.many_vertices (K.flagFlip A) =
      indexedFlagFacet K.many_vertices A := by
  have hf : indexedFacetAction K.vertices K.baseMirror.1
      (indexedFlagFacet K.many_vertices K.baseFlag) =
        indexedFlagFacet K.many_vertices K.baseFlag := by
    exact (indexedFacetAction_fix_iff K.vertices K.baseMirror.1 K.baseFacet).mpr
      K.baseMirror.2
  unfold flagFlip
  rw [indexedFlagFacet_equivariant, map_mul, Equiv.Perm.mul_apply, hf,
    ← indexedFlagFacet_equivariant, K.flagFrame_apply]

theorem flagFlip_sign (A : K.Flags) : K.flagSign (K.flagFlip A) = -K.flagSign A := by
  simp only [flagFlip, flagSign, K.flagFrame_smul, K.flagFrame_base,
    mul_one, map_mul, K.baseMirror_sign, mul_neg_one]

theorem flagFlip_involutive : Function.Involutive K.flagFlip := by
  intro A
  have hs : K.baseMirror.1 * K.baseMirror.1 = (1 : K.Group) :=
    congrArg Subtype.val K.baseMirror_square
  simp [flagFlip, K.flagFrame_smul, K.flagFrame_base, mul_assoc, hs, K.flagFrame_apply]

/-- The old complete oriented flag structure, instantiated from actual
Euclidean geometry. No one of its formerly supplied fields remains a premise. -/
def orientedFlags : RegularFacet.OrientedFlags K.Group K.Flags K.h where
  facetAction := indexedFacetAction K.vertices
  orientation := euclideanOrientation K.vertices
  facetOf := indexedFlagFacet K.many_vertices
  facet_surjective := (facetIndex K.vertices).surjective.comp
    (flagFacet_surjective K.many_vertices)
  facet_equivariant := indexedFlagFacet_equivariant K.many_vertices
  base := K.baseFlag
  transitive A := ⟨K.flagFrame A, K.flagFrame_apply A⟩
  flagSign := K.flagSign
  base_positive := by simp only [flagSign, K.flagFrame_base, map_one]
  sign_equivariant := K.flagSign_equivariant
  adjacent := K.flagFlip
  adjacent_facet := K.flagFlip_facet
  adjacent_sign := K.flagFlip_sign

/-- The signed system used by all existing enumeration theorems. -/
def system : RegularFacet.System K.Group K.h := K.orientedFlags.toSystem

@[simp] theorem system_facet : K.system.facet = indexedFacetAction K.vertices := rfl
@[simp] theorem system_orientation : K.system.orientation = euclideanOrientation K.vertices := rfl
@[simp] theorem system_base : K.system.base = facetIndex K.vertices K.baseFacet := rfl

theorem positive_facet_transitive (i : Fin K.h) :
    ∃ g : K.Group, indexedFacetAction K.vertices g K.system.base = i ∧
      euclideanOrientation K.vertices g = 1 := K.system.transitive i

theorem negative_facet_stabilizer :
    ∃ g : K.Group, indexedFacetAction K.vertices g K.system.base = K.system.base ∧
      euclideanOrientation K.vertices g = -1 := K.system.reflection

end RegularCell
end
end PolytopeCounting.FacetPairing.EuclideanGeometry
