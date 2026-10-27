module

public import Proofs.GeometricRealizationEquivariance
public import Proofs.FiniteBoundaryConvolution
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact finite mass of affine simplex-gluing presentations

We construct both directions of the encoding by one allowed permutation per
unordered seam. Reversing a seam inverts its permutation. The encoding is a
bijection of finite carriers; it is NOT claimed equivariant for the old action
which leaves colours unchanged.

For the newly proved geometric action, orbit--stabilizer then gives the same
TOTAL inverse-automorphism-weighted count. Individual old coloured orbits and
individual old stabilizers are not identified with geometric ones.

The uniform-palette theorem is instantiated without a palette hypothesis for
tetrahedra: every ordered pair of facets has three allowable maps and the
rotation group has order twelve.
-/

namespace PolytopeCounting.FacetPairing.GeometricPresentation
noncomputable section
open GeometricFacet Renaming Renaming.MatchingTransport ComponentConvolution
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u
variable {C : Type u} [DecidableEq C] {h r : ℕ}

abbrev SeamMaps (M : PartialMatching (Slots C h)) :=
  (e : M.Seam) → OddFacetMap e.1.out.1.2 e.1.out.2.2

abbrev SeamData (C : Type u) [DecidableEq C] (h : ℕ) :=
  Σ M : PartialMatching (Slots C h), SeamMaps M

theorem seam_rep (M : PartialMatching (Slots C h)) (e : M.Seam) :
    s(e.1.out.1,e.1.out.2)=e.1 := by rw [Sym2.mk,e.1.out_eq]

theorem seam_orientations (M : PartialMatching (Slots C h))
    (e : M.Seam) (a b : Slots C h) (he : s(a,b)=e.1) :
    (a=e.1.out.1 ∧ b=e.1.out.2) ∨ (a=e.1.out.2 ∧ b=e.1.out.1) :=
  Sym2.eq_iff.mp (he.trans (seam_rep M e).symm)

def seamMapTable (M : PartialMatching (Slots C h)) (f : SeamMaps M)
    (a b : Slots C h) : Equiv.Perm (Fin h) :=
  if hab : s(a,b) ∈ M.seams then
    let e : M.Seam := ⟨s(a,b),hab⟩
    if a=e.1.out.1 then (f e).1 else ((f e).1)⁻¹
  else 1

theorem seamMapTable_forward (M : PartialMatching (Slots C h)) (f : SeamMaps M)
    (e : M.Seam) : seamMapTable M f e.1.out.1 e.1.out.2=(f e).1 := by
  have hm : s(e.1.out.1,e.1.out.2) ∈ M.seams := by rw [seam_rep]; exact e.2
  have he : (⟨s(e.1.out.1,e.1.out.2),hm⟩ : M.Seam)=e :=
    Subtype.ext (seam_rep M e)
  unfold seamMapTable
  rw [dif_pos hm]
  change (if e.1.out.1 = (⟨s(e.1.out.1,e.1.out.2),hm⟩ : M.Seam).1.out.1 then
    (f ⟨s(e.1.out.1,e.1.out.2),hm⟩).1 else
    ((f ⟨s(e.1.out.1,e.1.out.2),hm⟩).1)⁻¹) = _
  rw [he, if_pos rfl]

theorem seamMapTable_backward (M : PartialMatching (Slots C h)) (f : SeamMaps M)
    (e : M.Seam) : seamMapTable M f e.1.out.2 e.1.out.1=((f e).1)⁻¹ := by
  have hm : s(e.1.out.2,e.1.out.1) ∈ M.seams := by
    rw [Sym2.eq_swap,seam_rep]; exact e.2
  have he : (⟨s(e.1.out.2,e.1.out.1),hm⟩ : M.Seam)=e := by
    apply Subtype.ext
    change s(e.1.out.2,e.1.out.1) = e.1
    rw [Sym2.eq_swap,seam_rep]
  have hn := (M.exposed_endpoints_ne e).symm
  change e.1.out.2 ≠ e.1.out.1 at hn
  unfold seamMapTable
  rw [dif_pos hm]
  change (if e.1.out.2 = (⟨s(e.1.out.2,e.1.out.1),hm⟩ : M.Seam).1.out.1 then
    (f ⟨s(e.1.out.2,e.1.out.1),hm⟩).1 else
    ((f ⟨s(e.1.out.2,e.1.out.1),hm⟩).1)⁻¹) = _
  rw [he, if_neg hn]

def presentationFromSeams (M : PartialMatching (Slots C h)) (f : SeamMaps M) :
    Presentation C h where
  matching := M
  maps := seamMapTable M f
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
    · rw [ha,hb,seamMapTable_backward]
      exact (f e).1.symm_apply_eq.mpr (f e).2.1.symm
  odd_map a b hab := by
    let e : M.Seam := ⟨s(a,b),hab⟩
    rcases seam_orientations M e a b rfl with ⟨ha,hb⟩|⟨ha,hb⟩
    · rw [ha,hb,seamMapTable_forward]; exact (f e).2.2
    · rw [ha,hb,seamMapTable_backward]
      simp [map_inv,(f e).2.2]

def mapsFromPresentation (P : Presentation C h) : SeamMaps P.matching := fun e ↦
  ⟨P.maps e.1.out.1 e.1.out.2, by
    have hm : s(e.1.out.1,e.1.out.2) ∈ P.matching.seams := by
      rw [seam_rep]; exact e.2
    exact ⟨P.endpoint _ _ hm,P.odd_map _ _ hm⟩⟩

/-- No invisible off-seam choices occur in either direction of the encoding. -/
def seamDataEquiv : Presentation C h ≃ SeamData C h where
  toFun P := ⟨P.matching,mapsFromPresentation P⟩
  invFun D := presentationFromSeams D.1 D.2
  left_inv P := by
    apply Presentation.ext
    · rfl
    funext a b
    by_cases hab : s(a,b) ∈ P.matching.seams
    · let e : P.matching.Seam := ⟨s(a,b),hab⟩
      rcases seam_orientations P.matching e a b rfl with ⟨ha,hb⟩|⟨ha,hb⟩
      · rw [ha,hb]
        exact seamMapTable_forward P.matching (mapsFromPresentation P) e
      · rw [ha,hb]
        change seamMapTable _ _ _ _ = _
        rw [seamMapTable_backward]
        exact (P.reverse_map _ _).symm
    · change seamMapTable _ _ a b = P.maps a b
      simp [seamMapTable,hab,P.off_seam a b hab]
  right_inv D := by
    rcases D with ⟨M,f⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    funext e
    apply Subtype.ext
    exact seamMapTable_forward M f e

/-- A genuine bijective palette, not just a map from colours to homeomorphisms. -/
abbrev Palette (h r : ℕ) := (i j : Fin h) → Fin r ≃ OddFacetMap i j

def colouredSeamDataEquiv (palette : Palette h r) :
    ColoredMatching (Slots C h) r ≃ SeamData C h where
  toFun P := ⟨P.matching,fun e ↦ palette _ _ (P.color e)⟩
  invFun D := ⟨D.1,fun e ↦ (palette _ _).symm (D.2 e)⟩
  left_inv P := by
    cases P
    simp
  right_inv D := by
    rcases D with ⟨M,f⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    funext e
    exact (palette _ _).apply_symm_apply (f e)

/-- A carrier equivalence. The old colour-preserving action is NOT used here. -/
def colouredPresentationEquiv (palette : Palette h r) :
    ColoredMatching (Slots C h) r ≃ Presentation C h :=
  (colouredSeamDataEquiv palette).trans seamDataEquiv.symm

@[simp] theorem colouredPresentation_matching (palette : Palette h r)
    (P : ColoredMatching (Slots C h) r) :
    (colouredPresentationEquiv palette P).matching=P.matching := rfl

/-- Coloured presentations equipped with the correct, transported geometric
action. A separate wrapper avoids silently changing the original global action. -/
structure GeometricColours (C : Type u) [DecidableEq C] (h r : ℕ) where
  pairing : ColoredMatching (Slots C h) r

def geometricColoursEquiv (palette : Palette h r) :
    GeometricColours C h r ≃ Presentation C h where
  toFun P := colouredPresentationEquiv palette P.pairing
  invFun P := ⟨(colouredPresentationEquiv palette).symm P⟩
  left_inv P := by cases P; simp
  right_inv P := (colouredPresentationEquiv palette).apply_symm_apply P

/-- An explicit action indexed by the chosen palette; kept as a definition to
avoid ambiguous global instances from different encodings. -/
@[instance_reducible]
def colourMulAction (palette : Palette h r) : MulAction (Frames C h) (GeometricColours C h r) where
  smul g P := (geometricColoursEquiv palette).symm (g • geometricColoursEquiv palette P)
  one_smul P := by
    change (geometricColoursEquiv palette).symm (1 • geometricColoursEquiv palette P) = P
    rw [one_smul]
    exact (geometricColoursEquiv palette).symm_apply_apply P
  mul_smul g k P := by
    change (geometricColoursEquiv palette).symm ((g * k) • geometricColoursEquiv palette P) =
      (geometricColoursEquiv palette).symm (g • geometricColoursEquiv palette
        ((geometricColoursEquiv palette).symm (k • geometricColoursEquiv palette P)))
    rw [Equiv.apply_symm_apply, mul_smul]

theorem colour_equivariant (palette : Palette h r) (g : Frames C h)
    (P : GeometricColours C h r) :
    letI := colourMulAction (C := C) palette
    geometricColoursEquiv palette (g • P)=g • geometricColoursEquiv palette P := by
  dsimp [colourMulAction]
  exact (geometricColoursEquiv palette).apply_symm_apply _

/-- Stabilizers, hence individual weights, correspond for this corrected
coloured action. This statement is deliberately not about the old action. -/
def colouredStabilizerEquiv (palette : Palette h r) (P : GeometricColours C h r) :
    letI := colourMulAction (C := C) palette
    MulAction.stabilizer (Frames C h) P ≃
      MulAction.stabilizer (Frames C h) (geometricColoursEquiv palette P) := by
  letI := colourMulAction (C := C) palette
  refine {toFun := fun g ↦ ⟨g.1,?_⟩,
          invFun := fun g ↦ ⟨g.1,?_⟩,
          left_inv := fun _ ↦ rfl,
          right_inv := fun _ ↦ rfl}
  · change g.1 • geometricColoursEquiv palette P = geometricColoursEquiv palette P
    rw [← colour_equivariant palette g.1 P,g.2]
  · apply (geometricColoursEquiv palette).injective
    rw [colour_equivariant palette g.1 P]
    exact g.2

abbrev BoundaryPresentations (n h m : ℕ) :=
  {P : Presentation (Fin n) h // Fintype.card P.matching.Boundary=m}

noncomputable instance (n h m : ℕ) : Fintype (BoundaryPresentations n h m) := Fintype.ofFinite _

instance boundaryMulAction (n h m : ℕ) : MulAction (Frames (Fin n) h) (BoundaryPresentations n h m) where
  smul g P := ⟨g • P.1,by
    have hc := Fintype.card_congr (boundaryEquiv (slotsPerm g) P.1.matching)
    exact hc.symm.trans P.2⟩
  one_smul P := Subtype.ext (one_smul _ _)
  mul_smul g k P := Subtype.ext (mul_smul _ _ _)

/-- Encoding preserves the free-facet statistic exactly. -/
def boundaryEncoding (palette : Palette h r) (n m : ℕ) :
    {P : ColoredMatching (Dart n h) r // Fintype.card P.matching.Boundary=m} ≃
      BoundaryPresentations n h m where
  toFun P := ⟨colouredPresentationEquiv palette P.1,P.2⟩
  invFun P := ⟨(colouredPresentationEquiv palette).symm P.1,P.2⟩
  left_inv P := by apply Subtype.ext; simp
  right_inv P := by apply Subtype.ext; simp

/-- The sum of reciprocal genuine geometric automorphism orders equals the
old normalized coefficient. This is an equality of total masses only. -/
theorem geometric_boundary_mass_eq_W (palette : Palette h r) (n m : ℕ) :
    ActionGroupoid.mass (Frames (Fin n) h) (BoundaryPresentations n h m) ℚ =
      PolytopeTrees.W (LocalRotation h) n h r m := by
  rw [ActionGroupoid.mass_eq_card_div_card,Renaming.WreathRenaming.card]
  simp only [Fintype.card_fin]
  rw [W_eq_allCount]
  congr 1
  rw [← Fintype.card_congr (boundaryEncoding palette n m)]
  change (Fintype.card {P : ColoredMatching (Dart n h) r //
      Fintype.card P.matching.Boundary=m} : ℚ) = allCount n h r m
  rw [Fintype.card_subtype]
  unfold allCount sizeCount
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- A concrete palette with no unproved cardinality assumption. -/
def tetrahedronPalette : Palette 4 3 := fun i j ↦
  (Fintype.equivFinOfCardEq (tetrahedron_palette_card i j)).symm

theorem tetrahedron_geometric_mass (n m : ℕ) :
    ActionGroupoid.mass (Frames (Fin n) 4) (BoundaryPresentations n 4 m) ℚ =
      PolytopeTrees.W (LocalRotation 4) n 4 3 m :=
  geometric_boundary_mass_eq_W tetrahedronPalette n m

end
end PolytopeCounting.FacetPairing.GeometricPresentation
