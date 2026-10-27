module

public import Proofs.RegularFacetPalette

@[expose] public section

/-! A uniform geometric palette for every simplex with at least three vertices.
The number of allowed maps is `(h-1)!/2`; no palette hypothesis is retained. -/

namespace PolytopeCounting.FacetPairing.GeometricFacet
noncomputable section
attribute [local instance] Classical.propDecidable
open RegularFacet

/-- Even permutations are transitive when there are at least three vertices. -/
def simplexSystem (h : ℕ) (hh : 3 ≤ h) : System (Equiv.Perm (Fin h)) h where
  facet := MonoidHom.id _
  orientation := Equiv.Perm.sign
  base := ⟨0, by omega⟩
  transitive i := by
    let z : Fin h := ⟨0, by omega⟩
    change ∃ g : Equiv.Perm (Fin h), g z = i ∧ Equiv.Perm.sign g = 1
    by_cases hi : i = z
    · exact ⟨1, by simp [hi]⟩
    obtain ⟨j,hjz,hji⟩ := Fin.exists_ne_and_ne_of_two_lt z i (by omega)
    refine ⟨Equiv.swap i j * Equiv.swap z j, ?_, ?_⟩
    · simp [Equiv.Perm.mul_apply]
    · simp [map_mul, Equiv.Perm.sign_swap hji.symm, Equiv.Perm.sign_swap hjz.symm]
  reflection := by
    let a : Fin h := ⟨1, by omega⟩
    let b : Fin h := ⟨2, by omega⟩
    refine ⟨Equiv.swap a b, ?_, ?_⟩
    · change Equiv.swap a b ⟨0, by omega⟩ = ⟨0, by omega⟩
      apply Equiv.swap_apply_of_ne_of_ne <;> simp [a,b,Fin.ext_iff]
    · exact Equiv.Perm.sign_swap (by simp [a,b,Fin.ext_iff])

theorem simplex_rotation_card (h : ℕ) (hh : 3 ≤ h) :
    Fintype.card (simplexSystem h hh).Rotation = h.factorial / 2 := by
  have : Nontrivial (Fin h) := Fin.nontrivial_iff_two_le.mpr (by omega)
  simpa [simplexSystem, System.Rotation] using (card_alternatingGroup (α := Fin h))

theorem simplex_facet_rotation_card (h : ℕ) (hh : 3 ≤ h) :
    Fintype.card (simplexSystem h hh).facetRotation = (h-1).factorial / 2 := by
  have : Nontrivial (Fin h) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have ht : 2 * Fintype.card (simplexSystem h hh).Rotation = h.factorial := by
    simpa [simplexSystem, System.Rotation, Fintype.card_perm] using (two_mul_card_alternatingGroup (α := Fin h))
  rw [(simplexSystem h hh).rotation_card] at ht
  have hf : h.factorial = h * (h-1).factorial := by
    conv_lhs => rw [show h = (h-1)+1 by omega, Nat.factorial_succ]
    congr 1; omega
  rw [hf] at ht
  have hc : h * (2 * Fintype.card (simplexSystem h hh).facetRotation) =
      h * (h-1).factorial := by nlinarith [ht]
  have he := Nat.eq_of_mul_eq_mul_left (by omega : 0 < h) hc
  omega

theorem simplex_palette_card (h : ℕ) (hh : 3 ≤ h) (i j : Fin h) :
    Fintype.card (OddFacetMap i j) = (h-1).factorial / 2 := by
  change Fintype.card ((simplexSystem h hh).Gluing i j) = _
  rw [(simplexSystem h hh).gluing_card, simplex_facet_rotation_card]

/-- This has exactly the original geometric `Palette` type. -/
def simplexPalette (h : ℕ) (hh : 3 ≤ h) :
    GeometricPresentation.Palette h ((h-1).factorial / 2) := fun i j ↦
  (Fintype.equivFinOfCardEq (simplex_palette_card h hh i j)).symm

theorem simplex_geometric_mass (h : ℕ) (hh : 3 ≤ h) (n m : ℕ) :
    ActionGroupoid.mass (GeometricPresentation.Frames (Fin n) h)
      (GeometricPresentation.BoundaryPresentations n h m) ℚ =
      PolytopeTrees.W (LocalRotation h) n h ((h-1).factorial / 2) m :=
  GeometricPresentation.geometric_boundary_mass_eq_W (simplexPalette h hh) n m

end
end PolytopeCounting.FacetPairing.GeometricFacet
