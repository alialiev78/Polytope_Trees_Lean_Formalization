module

public import Proofs.FacetPairingRealization
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import Mathlib.Data.Fin.SuccPred

@[expose] public section

/-!
# Actual Euclidean simplex charts for the finite pairing model

A `d`-simplex is Mathlib's real standard simplex on `Fin (d+1)`.
The chart of facet `i` inserts zero barycentric weight at vertex `i`.
A seam colour specifies a permutation of the `d` vertices of the common
model facet.  The induced map of facets is a genuine homeomorphism.

No abstract simplicial complex or manifold property is claimed for arbitrary
quotients.  The result realizes the given pairing by gluing actual simplices.
The old group actions still require a separate equivariance theorem.
-/

namespace PolytopeCounting.FacetPairing.SimplexRealization

noncomputable section
open Convexity

/-- The geometric simplex of dimension `d`. -/
abbrev Simplex (d : ℕ) := StdSimplex ℝ (Fin (d + 1))

/-- Permuting vertices induces a homeomorphism of the standard simplex. -/
def simplexHomeomorph {A B : Type*} (e : A ≃ B) :
    StdSimplex ℝ A ≃ₜ StdSimplex ℝ B where
  toFun := StdSimplex.map e
  invFun := StdSimplex.map e.symm
  left_inv x := by
    rw [StdSimplex.map_map]
    simp only [Function.comp_def, Equiv.symm_apply_apply]
    exact StdSimplex.map_id x
  right_inv x := by
    rw [StdSimplex.map_map]
    simp only [Function.comp_def, Equiv.apply_symm_apply]
    exact StdSimplex.map_id x
  continuous_toFun := StdSimplex.continuous_map ℝ e
  continuous_invFun := StdSimplex.continuous_map ℝ e.symm

/-- Chart onto the facet opposite vertex `i`. -/
def facetChart {d : ℕ} (i : Fin (d + 1)) :
    StdSimplex ℝ (Fin d) → Simplex d :=
  StdSimplex.map i.succAbove

theorem continuous_facetChart {d : ℕ} (i : Fin (d + 1)) :
    Continuous (facetChart i) :=
  StdSimplex.continuous_map ℝ i.succAbove

/-- The chart image is exactly the intended facet, not an arbitrary subset. -/
theorem range_facetChart {d : ℕ} (i : Fin (d + 1)) :
    Set.range (facetChart i) = {x : Simplex d | x.weights i = 0} := by
  ext x
  change x ∈ Set.range (StdSimplex.map i.succAbove) ↔ x.weights i = 0
  rw [StdSimplex.mem_range_map_iff]
  simp [Fin.range_succAbove]

/-- The original finite colour is interpreted by a vertex permutation.
Any injective palette of allowable permutations can be supplied; injectivity
is not needed merely for existence and connectedness of the quotient. -/
def charts (C : Type*) [DecidableEq C] (d r : ℕ)
    (palette : Fin r → Equiv.Perm (Fin d)) :
    Realization.Charts (facets := fun _ : C ↦ d + 1) (r := r)
      (fun _ : C ↦ Simplex d) (StdSimplex ℝ (Fin d)) where
  face slot := facetChart slot.2
  continuous_face slot := continuous_facetChart slot.2
  twist colour := simplexHomeomorph (palette colour)

/-- Actual simplex gluing determined by an existing coloured matching. -/
abbrev Space {C : Type*} [DecidableEq C] {d r : ℕ}
    (P : ColoredMatching (CellDart C (fun _ ↦ d + 1)) r)
    (palette : Fin r → Equiv.Perm (Fin d)) :=
  Realization.Space P (charts C d r palette)

/-- For positive dimension, dual connectedness implies connectedness of the
actual quotient of Euclidean simplices. -/
theorem connectedSpace {C : Type*} [DecidableEq C] [Nonempty C]
    {d r : ℕ} (hd : 0 < d)
    (P : ColoredMatching (CellDart C (fun _ ↦ d + 1)) r)
    (palette : Fin r → Equiv.Perm (Fin d))
    (hP : P.IsConnected (fun _ ↦ d + 1)) :
    ConnectedSpace (Space P palette) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact Realization.connectedSpace P (charts C d r palette) hP

/-- In particular, the concrete connected carriers counted in the paper have
connected simplex realizations.  Labels do not alter the gluing relation. -/
theorem connectedDiagram_realization {n d r m : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (D : UnrootedDiagram n (d + 1) r m)
    (palette : Fin r → Equiv.Perm (Fin d)) :
    ConnectedSpace (Space D.raw.pairing palette) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact connectedSpace hd D.raw.pairing palette D.connected

end
end PolytopeCounting.FacetPairing.SimplexRealization
