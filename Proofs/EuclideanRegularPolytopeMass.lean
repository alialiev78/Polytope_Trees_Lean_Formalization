module

public import Proofs.EuclideanFacetTransporters
public import Solution

@[expose] public section

/-!
# Geometric mass from the vertex set of a regular Euclidean polytope

The input is `RegularCell`: actual vertices, affine spanning, flag regularity,
and dimension at least two. The signed facet system and every gluing palette
are constructed, not supplied. Counts are action-groupoid masses of affine
cell/gluing presentations. They are not counts of homeomorphism classes.

-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell
noncomputable section
open RegularPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

variable {V P : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
variable (K : RegularCell V P)

/-- The actual conjugation action is the action being counted. The old
unchanged-colour action is not used to define this geometric mass. -/
def boundaryMass (n m : ℕ) : ℚ :=
  ActionGroupoid.mass (Frames K.system (Fin n))
    (BoundaryPresentations K.system n m) ℚ

theorem h_pos : 0 < K.h := by
  letI : Nonempty K.Facets := ⟨K.baseFacet⟩
  exact Fintype.card_pos

theorem r_pos : 0 < K.r := Fintype.card_pos

theorem tau_pos : 0 < K.tau := Fintype.card_pos

/-- The old all-facets mass theorem now has a concrete geometric instance.
No `System`, `OrientedFlags`, `Palette`, extension or determinant certificate
occurs among the parameters of this theorem. -/
theorem geometric_boundary_mass_eq_W (n m : ℕ) :
    K.boundaryMass n m = PolytopeTrees.W K.system.Rotation n K.h K.r m := by
  unfold boundaryMass
  rw [RegularPresentation.geometric_boundary_mass_eq_W,
    ← K.r_eq_indexed_stabilizer]

/-- Formula (46), with ordinary geometric inputs and explicit support/parity.
It includes n=0, empty boundary, loops and repeated cell adjacencies. -/
theorem geometric_boundary_mass_formula (n m e : ℕ)
    (hs : K.h * n = m + 2 * e) :
    K.boundaryMass n m =
      1 / ((n.factorial : ℚ) * (K.tau : ℚ) ^ n) *
      ((K.r : ℚ) / 2) ^ e * ((K.h * n).factorial : ℚ) /
      ((m.factorial : ℚ) * (e.factorial : ℚ)) := by
  rw [K.geometric_boundary_mass_eq_W]
  exact PolytopeTrees.W_formula K.system.Rotation n K.h K.r m e hs

/-- Formula (46) with tau eliminated using the geometric stabilizer identity. -/
theorem geometric_boundary_mass_formula_hr (n m e : ℕ)
    (hs : K.h * n = m + 2 * e) :
    K.boundaryMass n m =
      1 / ((n.factorial : ℚ) * ((K.h * K.r : ℕ) : ℚ) ^ n) *
      ((K.r : ℚ) / 2) ^ e * ((K.h * n).factorial : ℚ) /
      ((m.factorial : ℚ) * (e.factorial : ℚ)) := by
  rw [K.geometric_boundary_mass_formula n m e hs, K.tau_eq_h_mul_r]

/-- The free-facet recurrence of the article for actual geometric masses. -/
theorem geometric_boundary_mass_recurrence (n m e : ℕ)
    (hs : K.h * n = m + 2 * (e + 1)) :
    (2 * (e + 1) : ℚ) * K.boundaryMass n m =
      (K.r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        K.boundaryMass n (m + 2) := by
  simp only [K.geometric_boundary_mass_eq_W]
  exact PolytopeTrees.W_recurrence K.system.Rotation n K.h K.r m e hs

end
end PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell
