module

public import Proofs.CoreComponentDecomposition
public import Proofs.MainConnectedCoefficients

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-! # Boundary-normalized counts for the concrete Xi carrier

Finite-fibre counting removes the boundary labellings. Component decomposition
then gives a sum over actual subsets and matchings. `ConcreteXiConvolution`
uses this identity to prove the public Cauchy product.
-/

namespace PolytopeCounting.FacetPairing.CoreComponents

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators

universe uD uC

variable {D : Type uD} [Fintype D] [DecidableEq D]

/-- The finite number of boundary labellings, including unsupported sizes. -/
theorem card_labels (B : Type*) [Fintype B] [DecidableEq B] (m : ℕ) :
    Fintype.card (B ≃ Fin m) =
      if Fintype.card B = m then m.factorial else 0 := by
  classical
  by_cases hm : Fintype.card B = m
  · rw [if_pos hm]
    exact FiniteCounting.card_boundaryLabellings B hm
  · letI : IsEmpty (B ≃ Fin m) := ⟨fun e ↦ by
      apply hm
      simpa using Fintype.card_congr e⟩
    simp [hm, Fintype.card_eq_zero]

/-- Removing all boundary labels from a concrete carrier. The residual
cell-symmetry action need not be free; no orbit counting occurs here. -/
theorem normalized_labelled_card (r m : ℕ) :
    (Fintype.card (BoundaryLabelledPairing D r m) : ℚ) / (m.factorial : ℚ) =
      ∑ P : ColoredMatching D r, if Fintype.card P.Boundary = m then 1 else 0 := by
  classical
  have hfac : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  calc
    _ = ∑ P : ColoredMatching D r,
        (Fintype.card (P.Boundary ≃ Fin m) : ℚ) / (m.factorial : ℚ) := by
      rw [Fintype.card_congr BoundaryLabelledPairing.dataEquiv, Fintype.card_sigma]
      simp only [Nat.cast_sum, Finset.sum_div]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P _
      rw [card_labels]
      split_ifs <;> simp [hfac]

variable {Cell : Type uC} [Fintype Cell] [DecidableEq Cell]
  {facets : Cell → ℕ} {r : ℕ}

/-- Boundary-normalized cardinality after separating the actual root
component. Both boundaries may be empty. -/
theorem normalized_card_components (a : Cell) (m : ℕ) :
    (Fintype.card (BoundaryLabelledPairing (CellDart Cell facets) r m) : ℚ) /
        (m.factorial : ℚ) =
      ∑ X : Pieces (facets := facets) (r := r) a,
        if Fintype.card X.2.1.1.Boundary + Fintype.card X.2.1.2.Boundary = m
          then 1 else 0 := by
  classical
  have hfac : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  rw [card_labelled_components a m]
  simp only [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro X _
  rw [card_labels]
  simp only [Fintype.card_sum]
  split_ifs <;> simp [hfac]

/-- Exact component sum for the *existing* Xi coefficient. This theorem
has no component-equivalence, generating-function, or cardinality input. -/
theorem XiHatCount_component_sum (h h₀ r tau n m : ℕ) (c : ℚ) :
    ConcreteXi.XiHatCount h h₀ r tau c n m =
      c / ((n.factorial : ℚ) * (tau : ℚ) ^ n) *
        ∑ X : Pieces (facets := rootedFacets h₀ h) (r := r) (baseCell n),
          if Fintype.card X.2.1.1.Boundary + Fintype.card X.2.1.2.Boundary = m
            then 1 else 0 := by
  unfold ConcreteXi.XiHatCount
  rw [mul_div_assoc]
  rw [normalized_card_components (baseCell n) m]

/-- The component-counting identity also applies to the actual non-free
action-groupoid mass of the original rooted carrier. -/
theorem XiHatMass_component_sum
    (L : Type*) [Group L] [Fintype L]
    (h h₀ r n m : ℕ) [MulAction L (Fin h)] (c : ℚ) :
    ConcreteXi.XiHatMass L h h₀ r c n m =
      c / ((n.factorial : ℚ) * (Fintype.card L : ℚ) ^ n) *
        ∑ X : Pieces (facets := rootedFacets h₀ h) (r := r) (baseCell n),
          if Fintype.card X.2.1.1.Boundary + Fintype.card X.2.1.2.Boundary = m
            then 1 else 0 := by
  rw [ConcreteXi.XiHatMass_eq_count]
  exact XiHatCount_component_sum h h₀ r (Fintype.card L) n m c

end
end PolytopeCounting.FacetPairing.CoreComponents
