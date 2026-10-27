module

public import Proofs.RegularPresentationAction
public import Proofs.FiniteBoundaryConvolution
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact mass for a general signed facet system

The is derived from the symmetry group. The action is the genuine
conjugation action on seam transporters, not the unchanged-colour action.
The theorem applies to any finite signed facet system; its Euclidean
interpretation requires the geometric restriction/extension bridge.
-/

namespace PolytopeCounting.FacetPairing.RegularPresentation
noncomputable section
open RegularFacet Renaming Renaming.MatchingTransport ComponentConvolution
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u
variable {G : Type} [Group G] [Fintype G] {h : ℕ}
variable (S : System G h)
variable {C : Type u} [DecidableEq C]

abbrev SeamMaps (M : PartialMatching (Slots C h)) :=
  (e : M.Seam) → S.Gluing e.1.out.1.2 e.1.out.2.2

abbrev SeamData (C : Type u) [DecidableEq C] :=
  Σ M : PartialMatching (Slots C h), SeamMaps S M

theorem seam_rep (M : PartialMatching (Slots C h)) (e : M.Seam) :
    s(e.1.out.1,e.1.out.2)=e.1 := by rw [Sym2.mk,e.1.out_eq]

theorem seam_orientations (M : PartialMatching (Slots C h))
    (e : M.Seam) (a b : Slots C h) (he : s(a,b)=e.1) :
    (a=e.1.out.1 ∧ b=e.1.out.2) ∨ (a=e.1.out.2 ∧ b=e.1.out.1) :=
  Sym2.eq_iff.mp (he.trans (seam_rep M e).symm)

def seamMapTable (M : PartialMatching (Slots C h)) (f : SeamMaps S M)
    (a b : Slots C h) : G :=
  if hab : s(a,b) ∈ M.seams then
    let e : M.Seam := ⟨s(a,b),hab⟩
    if a=e.1.out.1 then (f e).1 else ((f e).1)⁻¹
  else 1

omit [Fintype G] in
theorem seamMapTable_forward (M : PartialMatching (Slots C h)) (f : SeamMaps S M)
    (e : M.Seam) : seamMapTable S M f e.1.out.1 e.1.out.2=(f e).1 := by
  have hm : s(e.1.out.1,e.1.out.2) ∈ M.seams := by rw [seam_rep]; exact e.2
  have he : (⟨s(e.1.out.1,e.1.out.2),hm⟩ : M.Seam)=e :=
    Subtype.ext (seam_rep M e)
  unfold seamMapTable
  rw [dite_eq_left hm]
  change (if e.1.out.1 = (⟨s(e.1.out.1,e.1.out.2),hm⟩ : M.Seam).1.out.1 then
    (f ⟨s(e.1.out.1,e.1.out.2),hm⟩).1 else
    ((f ⟨s(e.1.out.1,e.1.out.2),hm⟩).1)⁻¹) = _
  rw [he, ite_eq_left rfl]

omit [Fintype G] in
theorem seamMapTable_backward (M : PartialMatching (Slots C h)) (f : SeamMaps S M)
    (e : M.Seam) : seamMapTable S M f e.1.out.2 e.1.out.1=((f e).1)⁻¹ := by
  have hm : s(e.1.out.2,e.1.out.1) ∈ M.seams := by
    rw [Sym2.eq_swap,seam_rep]; exact e.2
  have he : (⟨s(e.1.out.2,e.1.out.1),hm⟩ : M.Seam)=e := by
    apply Subtype.ext
    change s(e.1.out.2,e.1.out.1) = e.1
    rw [Sym2.eq_swap,seam_rep]
  have hn := (M.exposed_endpoints_ne e).symm
  change e.1.out.2 ≠ e.1.out.1 at hn
  unfold seamMapTable
  rw [dite_eq_left hm]
  change (if e.1.out.2 = (⟨s(e.1.out.2,e.1.out.1),hm⟩ : M.Seam).1.out.1 then
    (f ⟨s(e.1.out.2,e.1.out.1),hm⟩).1 else
    ((f ⟨s(e.1.out.2,e.1.out.1),hm⟩).1)⁻¹) = _
  rw [he, ite_eq_right hn]

def presentationFromSeams (M : PartialMatching (Slots C h)) (f : SeamMaps S M) :
    Presentation S C where
  matching := M
  maps := seamMapTable S M f
  off_seam a b hab := by simp [seamMapTable,hab]
  reverse_map a b := by
    by_cases hab : s(a,b) ∈ M.seams
    · let e : M.Seam := ⟨s(a,b),hab⟩
      rcases seam_orientations M e a b rfl with ⟨ha,hb⟩|⟨ha,hb⟩
      · rw [ha,hb,seamMapTable_forward,seamMapTable_backward]
      · rw [ha,hb,seamMapTable_forward,seamMapTable_backward,inv_inv]
    · have hba : s(b,a) ∉ M.seams := by simpa only [Sym2.eq_swap] using hab
      simp [seamMapTable,hab,hba]
  endpoint a b hab := by
    let e : M.Seam := ⟨s(a,b),hab⟩
    rcases seam_orientations M e a b rfl with ⟨ha,hb⟩|⟨ha,hb⟩
    · rw [ha,hb,seamMapTable_forward]; exact (f e).2.1
    · rw [ha,hb,seamMapTable_backward, map_inv]
      exact (S.facet (f e).1).symm_apply_eq.mpr (f e).2.1.symm
  odd_map a b hab := by
    let e : M.Seam := ⟨s(a,b),hab⟩
    rcases seam_orientations M e a b rfl with ⟨ha,hb⟩|⟨ha,hb⟩
    · rw [ha,hb,seamMapTable_forward]; exact (f e).2.2
    · rw [ha,hb,seamMapTable_backward]
      simp [map_inv,(f e).2.2]

def mapsFromPresentation (P : Presentation S C) : SeamMaps S P.matching := fun e ↦
  ⟨P.maps e.1.out.1 e.1.out.2, by
    have hm : s(e.1.out.1,e.1.out.2) ∈ P.matching.seams := by
      rw [seam_rep]; exact e.2
    exact ⟨P.endpoint _ _ hm,P.odd_map _ _ hm⟩⟩

/-- No invisible off-seam choices occur in either direction of the encoding. -/
def seamDataEquiv : Presentation S C ≃ SeamData S C where
  toFun P := ⟨P.matching,mapsFromPresentation S P⟩
  invFun D := presentationFromSeams S D.1 D.2
  left_inv P := by
    apply Presentation.ext S
    · rfl
    funext a b
    by_cases hab : s(a,b) ∈ P.matching.seams
    · let e : P.matching.Seam := ⟨s(a,b),hab⟩
      rcases seam_orientations P.matching e a b rfl with ⟨ha,hb⟩|⟨ha,hb⟩
      · rw [ha,hb]
        exact seamMapTable_forward S P.matching (mapsFromPresentation S P) e
      · rw [ha,hb]
        change seamMapTable S _ _ _ _ = _
        rw [seamMapTable_backward]
        exact (P.reverse_map _ _).symm
    · change seamMapTable S _ _ a b = P.maps a b
      simp [seamMapTable,hab,P.off_seam a b hab]
  right_inv D := by
    rcases D with ⟨M,f⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    funext e
    apply Subtype.ext
    exact seamMapTable_forward S M f e

def colouredSeamDataEquiv :
    ColoredMatching (Slots C h) (Fintype.card S.facetRotation) ≃ SeamData S C where
  toFun P := ⟨P.matching,fun e ↦ S.palette _ _ (P.color e)⟩
  invFun D := ⟨D.1,fun e ↦ (S.palette _ _).symm (D.2 e)⟩
  left_inv P := by
    cases P
    simp
  right_inv D := by
    rcases D with ⟨M,f⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    funext e
    exact (S.palette _ _).apply_symm_apply (f e)

/-- A carrier equivalence. The old colour-preserving action is NOT used here. -/
def colouredPresentationEquiv :
    ColoredMatching (Slots C h) (Fintype.card S.facetRotation) ≃ Presentation S C :=
  (colouredSeamDataEquiv S).trans (seamDataEquiv S).symm

@[simp] theorem colouredPresentation_matching 
    (P : ColoredMatching (Slots C h) (Fintype.card S.facetRotation)) :
    (colouredPresentationEquiv S P).matching=P.matching := rfl

abbrev BoundaryPresentations (n m : ℕ) :=
  {P : Presentation S (Fin n) // Fintype.card P.matching.Boundary=m}

noncomputable instance (n m : ℕ) : Fintype (BoundaryPresentations S n m) := Fintype.ofFinite _

instance boundaryMulAction (n m : ℕ) : MulAction (Frames S (Fin n)) (BoundaryPresentations S n m) where
  smul g P := ⟨g • P.1,by
    have hc := Fintype.card_congr (boundaryEquiv (slotsPerm S g) P.1.matching)
    exact hc.symm.trans P.2⟩
  one_smul P := Subtype.ext (one_smul _ _)
  mul_smul g k P := Subtype.ext (mul_smul _ _ _)

/-- Encoding preserves the free-facet statistic exactly. -/
def boundaryEncoding (n m : ℕ) :
    {P : ColoredMatching (Dart n h) (Fintype.card S.facetRotation) // Fintype.card P.matching.Boundary=m} ≃
      BoundaryPresentations S n m where
  toFun P := ⟨colouredPresentationEquiv S P.1,P.2⟩
  invFun P := ⟨(colouredPresentationEquiv S).symm P.1,P.2⟩
  left_inv P := by apply Subtype.ext; simp
  right_inv P := by apply Subtype.ext; simp

/-- The sum of reciprocal genuine geometric automorphism orders equals the
old normalized coefficient. This is an equality of total masses only. -/
theorem geometric_boundary_mass_eq_W (n m : ℕ) :
    ActionGroupoid.mass (Frames S (Fin n)) (BoundaryPresentations S n m) ℚ =
      PolytopeTrees.W S.Rotation n h (Fintype.card S.facetRotation) m := by
  rw [ActionGroupoid.mass_eq_card_div_card,Renaming.WreathRenaming.card]
  simp only [Fintype.card_fin]
  rw [W_eq_allCount]
  congr 1
  rw [← Fintype.card_congr (boundaryEncoding S n m)]
  change (Fintype.card {P : ColoredMatching (Dart n h) (Fintype.card S.facetRotation) //
      Fintype.card P.matching.Boundary=m} : ℚ) = allCount n h (Fintype.card S.facetRotation) m
  rw [Fintype.card_subtype]
  unfold allCount sizeCount
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

end
end PolytopeCounting.FacetPairing.RegularPresentation
