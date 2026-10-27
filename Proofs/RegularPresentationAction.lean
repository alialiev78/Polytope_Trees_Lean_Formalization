module

public import Proofs.RegularFacetPalette
public import Proofs.ActionGroupoidMass
public import Mathlib.Tactic

@[expose] public section

/-!
# Geometric presentation action for a signed facet symmetry system

Seam maps are actual group elements with specified facet endpoints and negative
orientation. Local positive symmetries act by two-sided conjugation. No
colour-preserving action is substituted for this action.
-/

namespace PolytopeCounting.FacetPairing.RegularPresentation
noncomputable section
open RegularFacet Renaming Renaming.WreathRenaming Renaming.MatchingTransport

universe u
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
variable {G : Type} [Group G] {h : ℕ}
variable (S : System G h)
variable {C : Type u} [DecidableEq C]

instance rotationAction : MulAction S.Rotation (Fin h) where
  smul g i := S.facet g.1 i
  one_smul i := by change S.facet 1 i = i; simp
  mul_smul g k i := by change S.facet (g.1 * k.1) i = S.facet g.1 (S.facet k.1 i); simp [map_mul, Equiv.Perm.mul_apply]

@[simp] theorem sign_rotation (u : S.Rotation) : S.orientation u.1 = 1 := u.2

abbrev Slots (C : Type u) (h : ℕ) := CellDart C (fun _ ↦ h)
abbrev Frames (C : Type u) := WreathRenaming C S.Rotation

/-- Completed vertex-map table. Only entries on actual seams are free. -/
structure Presentation (C : Type u) [DecidableEq C] where
  matching : PartialMatching (Slots C h)
  maps : Slots C h → Slots C h → G
  off_seam : ∀ a b, s(a,b) ∉ matching.seams → maps a b=1
  reverse_map : ∀ a b, maps b a=(maps a b)⁻¹
  endpoint : ∀ a b, s(a,b) ∈ matching.seams → S.facet (maps a b) a.2=b.2
  odd_map : ∀ a b, s(a,b) ∈ matching.seams → S.orientation (maps a b) = -1

@[ext] theorem Presentation.ext {P Q : Presentation S C}
    (hm : P.matching=Q.matching) (hg : P.maps=Q.maps) : P=Q := by
  cases P; cases Q; simp_all

instance [Fintype G] [Fintype C] : Finite (Presentation S C) :=
  Finite.of_injective (fun P : Presentation S C ↦ (P.matching,P.maps)) (by
    intro P Q he
    exact Presentation.ext S (congrArg Prod.fst he) (congrArg Prod.snd he))

noncomputable instance [Fintype G] [Fintype C] : Fintype (Presentation S C) := Fintype.ofFinite _

abbrev slotsPerm (g : Frames S C) : Equiv.Perm (Slots C h) := dartPerm (Fin h) g
abbrev vertexPerm (g : Frames S C) (c : C) : G := (g.slot c).1

theorem pair_mem_rename (σ : Equiv.Perm (Slots C h))
    (M : PartialMatching (Slots C h)) (a b : Slots C h) :
    s(σ a,σ b) ∈ (renamePartial σ M).seams ↔ s(a,b) ∈ M.seams := by
  constructor
  · intro he
    rcases Finset.mem_map.mp he with ⟨e, he, heq⟩
    have heq' := congrArg (Sym2.map σ.symm) heq
    simp only [Sym2.map_mk, Equiv.symm_apply_apply] at heq'
    simpa [← heq'] using he
  · intro he
    exact Finset.mem_map.mpr ⟨s(a,b),he,by simp⟩

/-- Raw transported map table, with no data in nonseam entries. -/
def renamedMaps (g : Frames S C) (P : Presentation S C)
    (a b : Slots C h) : G :=
  if s((slotsPerm S g).symm a,(slotsPerm S g).symm b) ∈ P.matching.seams then
    vertexPerm S g ((slotsPerm S g).symm b).1 *
      P.maps ((slotsPerm S g).symm a) ((slotsPerm S g).symm b) *
      (vertexPerm S g ((slotsPerm S g).symm a).1)⁻¹
  else 1

@[simp] theorem renamedMaps_at (g : Frames S C) (P : Presentation S C)
    (a b : Slots C h) :
    renamedMaps S g P (slotsPerm S g a) (slotsPerm S g b) =
      if s(a,b) ∈ P.matching.seams then
        vertexPerm S g b.1*P.maps a b*(vertexPerm S g a.1)⁻¹ else 1 := by
  simp [renamedMaps]

/-- The geometric action is constructed on the existing matching carrier. -/
def rename (g : Frames S C) (P : Presentation S C) : Presentation S C where
  matching := renamePartial (slotsPerm S g) P.matching
  maps := renamedMaps S g P
  off_seam a b hab := by
    obtain ⟨a,rfl⟩ := (slotsPerm S g).surjective a
    obtain ⟨b,rfl⟩ := (slotsPerm S g).surjective b
    have hnot : s(a,b) ∉ P.matching.seams := by
      simpa only [pair_mem_rename] using hab
    rw [renamedMaps_at, ite_eq_right hnot]
  reverse_map a b := by
    obtain ⟨a,rfl⟩ := (slotsPerm S g).surjective a
    obtain ⟨b,rfl⟩ := (slotsPerm S g).surjective b
    rw [renamedMaps_at, renamedMaps_at]
    by_cases hab : s(a,b) ∈ P.matching.seams
    · have hba : s(b,a) ∈ P.matching.seams := by simpa [Sym2.eq_swap] using hab
      rw [ite_eq_left hab, ite_eq_left hba, P.reverse_map a b]
      simp only [mul_inv_rev, inv_inv, mul_assoc]
    · have hba : s(b,a) ∉ P.matching.seams := by simpa [Sym2.eq_swap] using hab
      simp [hab,hba]
  endpoint a b hab := by
    obtain ⟨a,rfl⟩ := (slotsPerm S g).surjective a
    obtain ⟨b,rfl⟩ := (slotsPerm S g).surjective b
    have hold := (pair_mem_rename (slotsPerm S g) P.matching a b).mp hab
    rw [renamedMaps_at, ite_eq_left hold]
    change S.facet (vertexPerm S g b.1 * P.maps a b * (vertexPerm S g a.1)⁻¹)
      (S.facet (vertexPerm S g a.1) a.2) = S.facet (vertexPerm S g b.1) b.2
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply,
      P.endpoint a b hold]
  odd_map a b hab := by
    obtain ⟨a,rfl⟩ := (slotsPerm S g).surjective a
    obtain ⟨b,rfl⟩ := (slotsPerm S g).surjective b
    have hold := (pair_mem_rename (slotsPerm S g) P.matching a b).mp hab
    rw [renamedMaps_at, ite_eq_left hold]
    simp [map_mul,map_inv,vertexPerm,sign_rotation,P.odd_map a b hold]

@[simp] theorem rename_matching (g : Frames S C) (P : Presentation S C) :
    (rename S g P).matching=renamePartial (slotsPerm S g) P.matching := rfl

@[simp] theorem rename_maps_at (g : Frames S C) (P : Presentation S C)
    (a b : Slots C h) (hab : s(a,b) ∈ P.matching.seams) :
    (rename S g P).maps (slotsPerm S g a) (slotsPerm S g b)=
      vertexPerm S g b.1*P.maps a b*(vertexPerm S g a.1)⁻¹ := by
  exact (renamedMaps_at S g P a b).trans (ite_eq_left hab)

@[simp] theorem rename_one (P : Presentation S C) : rename S 1 P=P := by
  apply Presentation.ext S
  · simp [rename,slotsPerm]
  · funext a b
    by_cases hab : s(a,b) ∈ P.matching.seams
    · simp [rename,renamedMaps,slotsPerm,vertexPerm,dartPerm,hab]
    · simp [rename,renamedMaps,slotsPerm,dartPerm,hab,P.off_seam a b hab]

@[simp] theorem rename_mul (g k : Frames S C) (P : Presentation S C) :
    rename S (g*k) P=rename S g (rename S k P) := by
  apply Presentation.ext S
  · simp [rename,slotsPerm,dartPerm_mul,renamePartial_mul]
  · funext a b
    obtain ⟨a,rfl⟩ := (slotsPerm S (g*k)).surjective a
    obtain ⟨b,rfl⟩ := (slotsPerm S (g*k)).surjective b
    have hσ (x : Slots C h) : slotsPerm S (g*k) x=slotsPerm S g (slotsPerm S k x) := by
      rw [slotsPerm,dartPerm_mul]; rfl
    by_cases hab : s(a,b) ∈ P.matching.seams
    · have hk : s(slotsPerm S k a,slotsPerm S k b) ∈ (rename S k P).matching.seams :=
        (pair_mem_rename (slotsPerm S k) P.matching a b).mpr hab
      rw [rename_maps_at S (g*k) P a b hab,hσ,hσ,
        rename_maps_at S g (rename S k P) _ _ hk,rename_maps_at S k P a b hab]
      simp [vertexPerm,slotsPerm,dartPerm,slot_mul,mul_assoc]
    · have hl : s(slotsPerm S (g*k) a,slotsPerm S (g*k) b) ∉
          (rename S (g*k) P).matching.seams := by
        simpa only [rename_matching,pair_mem_rename] using hab
      have hk : s(slotsPerm S k a,slotsPerm S k b) ∉ (rename S k P).matching.seams := by
        simpa only [rename_matching,pair_mem_rename] using hab
      have hg : s(slotsPerm S g (slotsPerm S k a),slotsPerm S g (slotsPerm S k b)) ∉
          (rename S g (rename S k P)).matching.seams := by
        simpa only [rename_matching,pair_mem_rename] using hk
      rw [(rename S (g*k) P).off_seam _ _ hl,hσ,hσ,
        (rename S g (rename S k P)).off_seam _ _ hg]

instance : MulAction (Frames S C) (Presentation S C) where
  smul := rename S
  one_smul := rename_one S
  mul_smul := rename_mul S

/-- A cellwise affine presentation isomorphism, specified before taking a
quotient space. This is intentionally NOT an arbitrary homeomorphism. -/
def Compatible (g : Frames S C) (P Q : Presentation S C) : Prop :=
  Q.matching=renamePartial (slotsPerm S g) P.matching ∧
  ∀ a b, s(a,b) ∈ P.matching.seams →
    Q.maps (slotsPerm S g a) (slotsPerm S g b)=
      vertexPerm S g b.1*P.maps a b*(vertexPerm S g a.1)⁻¹

/-- The independently stated geometric compatibility is exactly the action. -/
theorem compatible_iff (g : Frames S C) (P Q : Presentation S C) :
    Compatible S g P Q ↔ g • P=Q := by
  constructor
  · rintro ⟨hm,hg⟩
    apply Presentation.ext S hm.symm
    funext a b
    obtain ⟨a,rfl⟩ := (slotsPerm S g).surjective a
    obtain ⟨b,rfl⟩ := (slotsPerm S g).surjective b
    by_cases hab : s(a,b) ∈ P.matching.seams
    · exact (rename_maps_at S g P a b hab).trans (hg a b hab).symm
    · have hnot : s(slotsPerm S g a,slotsPerm S g b) ∉ Q.matching.seams := by
        rw [hm]; simpa only [pair_mem_rename] using hab
      have hnot' : s(slotsPerm S g a,slotsPerm S g b) ∉ (rename S g P).matching.seams := by
        simpa only [rename_matching,pair_mem_rename] using hab
      exact ((rename S g P).off_seam _ _ hnot').trans (Q.off_seam _ _ hnot).symm
  · rintro rfl
    exact ⟨rfl,fun a b hab ↦ rename_maps_at S g P a b hab⟩

abbrev GeometricIso (P Q : Presentation S C) := {g : Frames S C // Compatible S g P Q}

/-- Actual presentation automorphisms correspond one-for-one to stabilizer
elements, with no free-action assumption. -/
def automorphismsEquivStabilizer (P : Presentation S C) :
    GeometricIso S P P ≃ MulAction.stabilizer (Frames S C) P where
  toFun g := ⟨g.1,(compatible_iff S _ _ _).mp g.2⟩
  invFun g := ⟨g.1,(compatible_iff S _ _ _).mpr g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equivalence classes of geometric presentations, rather than bare spaces. -/
abbrev Classes (C : Type u) [DecidableEq C] :=
  MulAction.orbitRel.Quotient (Frames S C) (Presentation S C)

/-- This mass theorem is for the newly constructed geometric action. -/
theorem geometric_mass_eq_card [Fintype G] [Fintype C] :
    ActionGroupoid.mass (Frames S C) (Presentation S C) ℚ =
      (Fintype.card (Presentation S C) : ℚ) /
        (((Fintype.card C).factorial*(Fintype.card S.Rotation)^(Fintype.card C) : ℕ) : ℚ) := by
  rw [ActionGroupoid.mass_eq_card_div_card,Renaming.WreathRenaming.card]

end
end PolytopeCounting.FacetPairing.RegularPresentation
