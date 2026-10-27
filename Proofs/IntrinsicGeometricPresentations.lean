module

public import Proofs.EuclideanPolytopeRealization

@[expose] public section

/-!
# Presentations whose seam data are the intrinsic geometric maps themselves

This carrier contains the matching and one actual negative affine isometry
between each pair of intrinsic facet spaces. It does not store an additional
ambient extension or an arbitrary colour. Uniqueness of geometric extension
identifies it equivariantly with the constructed transporter presentation.
The final mass formula therefore applies to these concrete geometric data.

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

abbrev IntrinsicSeamMaps {C : Type} [DecidableEq C]
    (M : PartialMatching (Slots C K.h)) :=
  (e : M.Seam) → K.NegativeIntrinsicMap e.1.out.1.2 e.1.out.2.2

abbrev IntrinsicPresentation (C : Type) [DecidableEq C] :=
  Σ M : PartialMatching (Slots C K.h), K.IntrinsicSeamMaps M

/-- Each intrinsic seam map is extended uniquely; this creates no extra
choices in the carrier. -/
def intrinsicSeamDataEquiv (C : Type) [DecidableEq C] :
    SeamData K.system C ≃ K.IntrinsicPresentation C where
  toFun D := ⟨D.1, fun e ↦ K.negativeMapEquiv _ _ (D.2 e)⟩
  invFun D := ⟨D.1, fun e ↦ (K.negativeMapEquiv _ _).symm (D.2 e)⟩
  left_inv D := by
    rcases D with ⟨M, f⟩
    simp only [Equiv.symm_apply_apply]
  right_inv D := by
    rcases D with ⟨M, f⟩
    simp only [Equiv.apply_symm_apply]

def intrinsicPresentationEquiv (C : Type) [DecidableEq C] :
    Presentation K.system C ≃ K.IntrinsicPresentation C :=
  (seamDataEquiv K.system).trans (K.intrinsicSeamDataEquiv C)

@[simp] theorem intrinsicPresentationEquiv_matching {C : Type} [DecidableEq C]
    (D : Presentation K.system C) : (K.intrinsicPresentationEquiv C D).1 = D.matching := rfl

@[simp] theorem intrinsicPresentationEquiv_symm_matching {C : Type} [DecidableEq C]
    (D : K.IntrinsicPresentation C) :
    ((K.intrinsicPresentationEquiv C).symm D).matching = D.1 := rfl

/-- This is the geometric conjugation action, transported along the unique
extension equivalence; it is not the old colour-preserving action. -/
instance intrinsicPresentationAction (C : Type) [DecidableEq C] :
    MulAction (Frames K.system C) (K.IntrinsicPresentation C) where
  smul g D := K.intrinsicPresentationEquiv C
    (g • (K.intrinsicPresentationEquiv C).symm D)
  one_smul D := by
    change K.intrinsicPresentationEquiv C
      (1 • (K.intrinsicPresentationEquiv C).symm D) = D
    rw [one_smul, Equiv.apply_symm_apply]
  mul_smul g k D := by
    change K.intrinsicPresentationEquiv C ((g * k) • (K.intrinsicPresentationEquiv C).symm D) =
      K.intrinsicPresentationEquiv C (g • (K.intrinsicPresentationEquiv C).symm
        (K.intrinsicPresentationEquiv C (k • (K.intrinsicPresentationEquiv C).symm D)))
    rw [Equiv.symm_apply_apply, mul_smul]

@[simp] theorem intrinsicPresentationEquiv_smul {C : Type} [DecidableEq C]
    (g : Frames K.system C) (D : Presentation K.system C) :
    K.intrinsicPresentationEquiv C (g • D) = g • K.intrinsicPresentationEquiv C D := by
  change _ = K.intrinsicPresentationEquiv C
    (g • (K.intrinsicPresentationEquiv C).symm (K.intrinsicPresentationEquiv C D))
  rw [Equiv.symm_apply_apply]

noncomputable instance intrinsicPresentationFintype (C : Type) [DecidableEq C] [Fintype C] :
    Fintype (K.IntrinsicPresentation C) :=
  Fintype.ofEquiv (Presentation K.system C) (K.intrinsicPresentationEquiv C)

abbrev IntrinsicBoundaryPresentations (n m : ℕ) :=
  {D : K.IntrinsicPresentation (Fin n) // Fintype.card D.1.Boundary = m}

noncomputable instance intrinsicBoundaryFintype (n m : ℕ) :
    Fintype (K.IntrinsicBoundaryPresentations n m) := Fintype.ofFinite _

instance intrinsicBoundaryAction (n m : ℕ) :
    MulAction (Frames K.system (Fin n)) (K.IntrinsicBoundaryPresentations n m) where
  smul g D := ⟨g • D.1, by
    have h := Fintype.card_congr (Renaming.MatchingTransport.boundaryEquiv
      (slotsPerm K.system g) D.1.1)
    exact h.symm.trans D.2⟩
  one_smul D := Subtype.ext (one_smul _ _)
  mul_smul g k D := Subtype.ext (mul_smul _ _ _)

def intrinsicBoundaryEquiv (n m : ℕ) :
    BoundaryPresentations K.system n m ≃ K.IntrinsicBoundaryPresentations n m where
  toFun D := ⟨K.intrinsicPresentationEquiv (Fin n) D.1, D.2⟩
  invFun D := ⟨(K.intrinsicPresentationEquiv (Fin n)).symm D.1, D.2⟩
  left_inv D := Subtype.ext ((K.intrinsicPresentationEquiv (Fin n)).symm_apply_apply D.1)
  right_inv D := Subtype.ext ((K.intrinsicPresentationEquiv (Fin n)).apply_symm_apply D.1)

@[simp] theorem intrinsicBoundaryEquiv_smul (n m : ℕ)
    (g : Frames K.system (Fin n)) (D : BoundaryPresentations K.system n m) :
    K.intrinsicBoundaryEquiv n m (g • D) = g • K.intrinsicBoundaryEquiv n m D := by
  apply Subtype.ext
  exact K.intrinsicPresentationEquiv_smul g D.1

/-- Individual geometric stabilizers agree, not only total cardinalities. -/
def intrinsicBoundaryStabilizerEquiv (n m : ℕ) (D : BoundaryPresentations K.system n m) :
    MulAction.stabilizer (Frames K.system (Fin n)) D ≃*
      MulAction.stabilizer (Frames K.system (Fin n)) (K.intrinsicBoundaryEquiv n m D) where
  toFun g := ⟨g.1, by
    change g.1 • K.intrinsicBoundaryEquiv n m D = K.intrinsicBoundaryEquiv n m D
    rw [← K.intrinsicBoundaryEquiv_smul]
    exact congrArg (K.intrinsicBoundaryEquiv n m) g.2⟩
  invFun g := ⟨g.1, by
    apply (K.intrinsicBoundaryEquiv n m).injective
    rw [K.intrinsicBoundaryEquiv_smul]
    exact g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def intrinsicBoundaryMass (n m : ℕ) : ℚ :=
  ActionGroupoid.mass (Frames K.system (Fin n))
    (K.IntrinsicBoundaryPresentations n m) ℚ

theorem intrinsicBoundaryMass_eq_boundaryMass (n m : ℕ) :
    K.intrinsicBoundaryMass n m = K.boundaryMass n m := by
  unfold intrinsicBoundaryMass boundaryMass
  rw [ActionGroupoid.mass_eq_card_div_card, ActionGroupoid.mass_eq_card_div_card,
    ← Fintype.card_congr (K.intrinsicBoundaryEquiv n m)]

/-- The final geometric count has no supplied palette or abstract flag system. -/
theorem intrinsic_boundary_mass_eq_W (n m : ℕ) :
    K.intrinsicBoundaryMass n m = PolytopeTrees.W K.system.Rotation n K.h K.r m := by
  rw [K.intrinsicBoundaryMass_eq_boundaryMass, K.geometric_boundary_mass_eq_W]

theorem intrinsic_boundary_mass_formula (n m e : ℕ)
    (hs : K.h * n = m + 2 * e) :
    K.intrinsicBoundaryMass n m =
      1 / ((n.factorial : ℚ) * (K.tau : ℚ) ^ n) *
      ((K.r : ℚ) / 2) ^ e * ((K.h * n).factorial : ℚ) /
      ((m.factorial : ℚ) * (e.factorial : ℚ)) := by
  rw [K.intrinsicBoundaryMass_eq_boundaryMass]
  exact K.geometric_boundary_mass_formula n m e hs

theorem intrinsic_boundary_mass_recurrence (n m e : ℕ)
    (hs : K.h * n = m + 2 * (e + 1)) :
    (2 * (e + 1) : ℚ) * K.intrinsicBoundaryMass n m =
      (K.r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        K.intrinsicBoundaryMass n (m + 2) := by
  simp only [K.intrinsicBoundaryMass_eq_boundaryMass]
  exact K.geometric_boundary_mass_recurrence n m e hs

end
end PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell
