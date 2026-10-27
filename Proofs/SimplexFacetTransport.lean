module

public import Proofs.SimplexPairingRealization
public import Proofs.RenamingAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic

@[expose] public section

/-!
# Actual affine facet maps and their change of vertex frames

A gluing between facets opposite i and j is recorded by its unique completed
vertex permutation g with g(i)=j. We select odd completed permutations;
orientation-preserving cell renamings are even permutations. The induced
transport is v*g*u^{-1}, NOT unchanged seam colours.

The distinction is demonstrated by a finite tetrahedral counterexample. The
old colour-preserving action is left unchanged; it cannot be advertised as
the geometric action for arbitrary interpretations of colours.
-/

namespace PolytopeCounting.FacetPairing.GeometricFacet
noncomputable section
open Convexity SimplexRealization

abbrev Vertex (h : ℕ) := Fin h
abbrev LocalRotation (h : ℕ) := alternatingGroup (Vertex h)

/-- Completed permutation representing an orientation-compatible facet map. -/
abbrev OddFacetMap {h : ℕ} (i j : Vertex h) :=
  {g : Equiv.Perm (Vertex h) // g i=j ∧ Equiv.Perm.sign g = -1}

def inverse {h : ℕ} {i j : Vertex h} (g : OddFacetMap i j) : OddFacetMap j i :=
  ⟨g.1⁻¹, by
    constructor
    · exact g.1.symm_apply_eq.mpr g.2.1.symm
    · simp [map_inv, g.2.2]⟩

@[simp] theorem inverse_val {h : ℕ} {i j : Vertex h} (g : OddFacetMap i j) :
    (inverse g).1 = g.1⁻¹ := rfl

@[simp] theorem inverse_inverse {h : ℕ} {i j : Vertex h} (g : OddFacetMap i j) :
    inverse (inverse g) = g := by
  apply Subtype.ext; simp

theorem sign_rotation {h : ℕ} (u : LocalRotation h) :
    Equiv.Perm.sign (u : Equiv.Perm (Vertex h))=1 :=
  Equiv.Perm.mem_alternatingGroup.mp u.2

/-- Change source and target vertex frames independently. -/
def transport {h : ℕ} {i j : Vertex h} (u v : LocalRotation h)
    (g : OddFacetMap i j) : OddFacetMap (u.1 i) (v.1 j) :=
  ⟨v.1*g.1*u.1⁻¹, by
    constructor
    · simp [Equiv.Perm.mul_apply, g.2.1]
    · simp [map_mul, map_inv, sign_rotation, g.2.2]⟩

@[simp] theorem transport_val {h : ℕ} {i j : Vertex h}
    (u v : LocalRotation h) (g : OddFacetMap i j) :
    (transport u v g).1 = v.1*g.1*u.1⁻¹ := rfl

theorem transport_identity {h : ℕ} {i j : Vertex h} (g : OddFacetMap i j) :
    (transport 1 1 g).1 = g.1 := by simp

theorem transport_composition {h : ℕ} {i j : Vertex h}
    (u₁ v₁ u₂ v₂ : LocalRotation h) (g : OddFacetMap i j) :
    (transport u₂ v₂ (transport u₁ v₁ g)).1 =
      (transport (u₂*u₁) (v₂*v₁) g).1 := by
  simp [transport, mul_assoc]

theorem transport_inverse {h : ℕ} {i j : Vertex h}
    (u v : LocalRotation h) (g : OddFacetMap i j) :
    (transport v u (inverse g)).1 = ((transport u v g).1)⁻¹ := by
  simp [transport, mul_assoc]

abbrev FacetVertices {h : ℕ} (i : Vertex h) := {x : Vertex h // x ≠ i}
abbrev CellSimplex (h : ℕ) := StdSimplex ℝ (Vertex h)
abbrev FacetSimplex {h : ℕ} (i : Vertex h) := StdSimplex ℝ (FacetVertices i)

/-- Restrict a completed permutation to the vertices of its source facet. -/
def facetVertexEquiv {h : ℕ} {i j : Vertex h} (g : Equiv.Perm (Vertex h))
    (hg : g i=j) : FacetVertices i ≃ FacetVertices j where
  toFun x := ⟨g x.1, by
    intro hx
    exact x.2 (g.injective (hx.trans hg.symm))⟩
  invFun y := ⟨g.symm y.1, by
    intro hy
    apply y.2
    calc
      y.1 = g (g.symm y.1) := (g.apply_symm_apply y.1).symm
      _ = g i := congrArg g hy
      _ = j := hg⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

def facetInclusion {h : ℕ} (i : Vertex h) : FacetSimplex i → CellSimplex h :=
  StdSimplex.map Subtype.val

theorem continuous_facetInclusion {h : ℕ} (i : Vertex h) :
    Continuous (facetInclusion i) := StdSimplex.continuous_map ℝ Subtype.val

def facetHomeomorph {h : ℕ} {i j : Vertex h} (g : OddFacetMap i j) :
    FacetSimplex i ≃ₜ FacetSimplex j := simplexHomeomorph (facetVertexEquiv g.1 g.2.1)

/-- This is a geometric commutative square, not just a count of permutations. -/
theorem facetInclusion_natural {h : ℕ} {i j : Vertex h}
    (g : Equiv.Perm (Vertex h)) (hg : g i=j) (x : FacetSimplex i) :
    facetInclusion j (simplexHomeomorph (facetVertexEquiv g hg) x) =
      simplexHomeomorph g (facetInclusion i x) := by
  change StdSimplex.map _ (StdSimplex.map _ x) = StdSimplex.map _ (StdSimplex.map _ x)
  simp only [StdSimplex.map_map]
  rfl

/-- Exact compatibility of the gluing with independent source/target rotations. -/
theorem transported_gluing_square {h : ℕ} {i j : Vertex h}
    (u v : LocalRotation h) (g : OddFacetMap i j) (x : CellSimplex h) :
    simplexHomeomorph (transport u v g).1 (simplexHomeomorph u.1 x) =
      simplexHomeomorph v.1 (simplexHomeomorph g.1 x) := by
  change StdSimplex.map _ (StdSimplex.map _ x) = StdSimplex.map _ (StdSimplex.map _ x)
  rw [StdSimplex.map_map, StdSimplex.map_map]
  congr 1
  funext y
  simp [transport, Equiv.Perm.mul_apply]

/-- A completed vertex map is determined by its genuine affine action on a
facet, together with the image of the missing vertex. This converse is what
prevents the geometric compatibility condition from being merely a relabelling
of the combinatorial action. -/
theorem completed_map_determined_on_facet {h : ℕ} (i : Vertex h)
    (p q : Equiv.Perm (Vertex h)) (hi : p i=q i)
    (hf : ∀ x : FacetSimplex i,
      simplexHomeomorph p (facetInclusion i x) =
        simplexHomeomorph q (facetInclusion i x)) : p=q := by
  apply Equiv.ext
  intro v
  by_cases hv : v=i
  · simpa only [hv] using hi
  · let x : FacetSimplex i := StdSimplex.single ⟨v,hv⟩
    have he := hf x
    change StdSimplex.map p (StdSimplex.map Subtype.val x) =
      StdSimplex.map q (StdSimplex.map Subtype.val x) at he
    dsimp [x] at he
    simp only [StdSimplex.map_single] at he
    exact StdSimplex.single_injective he

/-- One explicit incompatibility of unchanged colours, already for tetrahedra. -/
def tetrahedronFrame : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 2 * Equiv.swap 2 3

def tetrahedronGluing : Equiv.Perm (Fin 4) := Equiv.swap 1 2

theorem tetrahedronFrame_even_fixed_facet :
    Equiv.Perm.sign tetrahedronFrame=1 ∧ tetrahedronFrame 0=0 := by decide

theorem tetrahedronGluing_odd_fixed_facet :
    Equiv.Perm.sign tetrahedronGluing = -1 ∧ tetrahedronGluing 0=0 := by decide

theorem fixed_colour_is_not_geometric_transport :
    tetrahedronGluing*tetrahedronFrame⁻¹ ≠ tetrahedronGluing := by decide

theorem fixed_colour_square_fails :
    tetrahedronGluing (tetrahedronFrame 1) ≠ tetrahedronGluing 1 := by decide

/-- The finite palette has the intended cardinality in the paper's main case. -/
theorem tetrahedron_palette_card :
    ∀ i j : Fin 4, Fintype.card (OddFacetMap i j)=3 := by decide

theorem tetrahedron_rotation_card : Fintype.card (LocalRotation 4)=12 := by decide

end
end PolytopeCounting.FacetPairing.GeometricFacet
