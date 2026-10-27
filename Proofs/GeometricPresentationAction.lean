module

public import Proofs.SimplexFacetTransport
public import Proofs.ActionGroupoidMass
public import Mathlib.Tactic

@[expose] public section

/-!
# The geometric action on simplex-gluing presentations

Objects retain the original partial matching and the actual affine map of
EVERY seam. The map in the reverse direction is its inverse. Off seams the
map table is fixed to the identity, so no invisible parameters are added.

Independent even vertex permutations act by two-sided conjugation on maps.
The resulting action is proved, not supplied as an equivariance certificate.
It need not be the old colour-preserving action.
-/

namespace PolytopeCounting.FacetPairing.GeometricPresentation
noncomputable section
open GeometricFacet Renaming Renaming.WreathRenaming Renaming.MatchingTransport

universe u
variable {C : Type u} [DecidableEq C] {h : ℕ}
abbrev Slots (C : Type u) (h : ℕ) := CellDart C (fun _ ↦ h)
abbrev Frames (C : Type u) (h : ℕ) := WreathRenaming C (LocalRotation h)

/-- Completed vertex-map table. Only entries on actual seams are free. -/
structure Presentation (C : Type u) [DecidableEq C] (h : ℕ) where
  matching : PartialMatching (Slots C h)
  maps : Slots C h → Slots C h → Equiv.Perm (Fin h)
  off_seam : ∀ a b, s(a,b) ∉ matching.seams → maps a b=1
  reverse_map : ∀ a b, maps b a=(maps a b)⁻¹
  endpoint : ∀ a b, s(a,b) ∈ matching.seams → maps a b a.2=b.2
  odd_map : ∀ a b, s(a,b) ∈ matching.seams → Equiv.Perm.sign (maps a b) = -1

@[ext] theorem Presentation.ext {P Q : Presentation C h}
    (hm : P.matching=Q.matching) (hg : P.maps=Q.maps) : P=Q := by
  cases P; cases Q; simp_all

instance [Fintype C] : Finite (Presentation C h) :=
  Finite.of_injective (fun P : Presentation C h ↦ (P.matching,P.maps)) (by
    intro P Q he
    exact Presentation.ext (congrArg Prod.fst he) (congrArg Prod.snd he))

noncomputable instance [Fintype C] : Fintype (Presentation C h) := Fintype.ofFinite _

abbrev slotsPerm (g : Frames C h) : Equiv.Perm (Slots C h) := dartPerm (Fin h) g
abbrev vertexPerm (g : Frames C h) (c : C) : Equiv.Perm (Fin h) := (g.slot c).1

theorem pair_mem_rename (σ : Equiv.Perm (Slots C h))
    (M : PartialMatching (Slots C h)) (a b : Slots C h) :
    s(σ a,σ b) ∈ (renamePartial σ M).seams ↔ s(a,b) ∈ M.seams := by
  constructor
  · intro he
    rcases Finset.mem_map.mp he with ⟨e, he, heq⟩
    have heq' := congrArg (Sym2.map σ.symm) heq
    simp only [sym2_map_inv_map, Sym2.map_mk, Equiv.symm_apply_apply] at heq'
    simpa [← heq'] using he
  · intro he
    exact Finset.mem_map.mpr ⟨s(a,b),he,by simp⟩

/-- Raw transported map table, with no data in nonseam entries. -/
def renamedMaps (g : Frames C h) (P : Presentation C h)
    (a b : Slots C h) : Equiv.Perm (Fin h) :=
  if s((slotsPerm g).symm a,(slotsPerm g).symm b) ∈ P.matching.seams then
    vertexPerm g ((slotsPerm g).symm b).1 *
      P.maps ((slotsPerm g).symm a) ((slotsPerm g).symm b) *
      (vertexPerm g ((slotsPerm g).symm a).1)⁻¹
  else 1

@[simp] theorem renamedMaps_at (g : Frames C h) (P : Presentation C h)
    (a b : Slots C h) :
    renamedMaps g P (slotsPerm g a) (slotsPerm g b) =
      if s(a,b) ∈ P.matching.seams then
        vertexPerm g b.1*P.maps a b*(vertexPerm g a.1)⁻¹ else 1 := by
  simp [renamedMaps]

/-- The geometric action is constructed on the existing matching carrier. -/
def rename (g : Frames C h) (P : Presentation C h) : Presentation C h where
  matching := renamePartial (slotsPerm g) P.matching
  maps := renamedMaps g P
  off_seam a b hab := by
    obtain ⟨a,rfl⟩ := (slotsPerm g).surjective a
    obtain ⟨b,rfl⟩ := (slotsPerm g).surjective b
    have hnot : s(a,b) ∉ P.matching.seams := by
      simpa only [pair_mem_rename] using hab
    rw [renamedMaps_at, if_neg hnot]
  reverse_map a b := by
    obtain ⟨a,rfl⟩ := (slotsPerm g).surjective a
    obtain ⟨b,rfl⟩ := (slotsPerm g).surjective b
    rw [renamedMaps_at, renamedMaps_at]
    by_cases hab : s(a,b) ∈ P.matching.seams
    · have hba : s(b,a) ∈ P.matching.seams := by simpa [Sym2.eq_swap] using hab
      rw [if_pos hab, if_pos hba, P.reverse_map a b]
      simp only [mul_inv_rev, inv_inv, mul_assoc]
    · have hba : s(b,a) ∉ P.matching.seams := by simpa [Sym2.eq_swap] using hab
      simp [hab,hba]
  endpoint a b hab := by
    obtain ⟨a,rfl⟩ := (slotsPerm g).surjective a
    obtain ⟨b,rfl⟩ := (slotsPerm g).surjective b
    have hold := (pair_mem_rename (slotsPerm g) P.matching a b).mp hab
    rw [renamedMaps_at, if_pos hold]
    change vertexPerm g b.1 (P.maps a b
      ((vertexPerm g a.1).symm (vertexPerm g a.1 a.2))) = vertexPerm g b.1 b.2
    rw [Equiv.symm_apply_apply, P.endpoint a b hold]
  odd_map a b hab := by
    obtain ⟨a,rfl⟩ := (slotsPerm g).surjective a
    obtain ⟨b,rfl⟩ := (slotsPerm g).surjective b
    have hold := (pair_mem_rename (slotsPerm g) P.matching a b).mp hab
    rw [renamedMaps_at, if_pos hold]
    simp [map_mul,map_inv,vertexPerm,sign_rotation,P.odd_map a b hold]

@[simp] theorem rename_matching (g : Frames C h) (P : Presentation C h) :
    (rename g P).matching=renamePartial (slotsPerm g) P.matching := rfl

@[simp] theorem rename_maps_at (g : Frames C h) (P : Presentation C h)
    (a b : Slots C h) (hab : s(a,b) ∈ P.matching.seams) :
    (rename g P).maps (slotsPerm g a) (slotsPerm g b)=
      vertexPerm g b.1*P.maps a b*(vertexPerm g a.1)⁻¹ := by
  exact (renamedMaps_at g P a b).trans (if_pos hab)

@[simp] theorem rename_one (P : Presentation C h) : rename 1 P=P := by
  apply Presentation.ext
  · simp [rename,slotsPerm]
  · funext a b
    by_cases hab : s(a,b) ∈ P.matching.seams
    · simp [rename,renamedMaps,slotsPerm,vertexPerm,dartPerm,hab]
    · simp [rename,renamedMaps,slotsPerm,vertexPerm,dartPerm,hab,P.off_seam a b hab]

@[simp] theorem rename_mul (g k : Frames C h) (P : Presentation C h) :
    rename (g*k) P=rename g (rename k P) := by
  apply Presentation.ext
  · simp [rename,slotsPerm,dartPerm_mul,renamePartial_mul]
  · funext a b
    obtain ⟨a,rfl⟩ := (slotsPerm (g*k)).surjective a
    obtain ⟨b,rfl⟩ := (slotsPerm (g*k)).surjective b
    have hσ (x : Slots C h) : slotsPerm (g*k) x=slotsPerm g (slotsPerm k x) := by
      rw [slotsPerm,dartPerm_mul]; rfl
    by_cases hab : s(a,b) ∈ P.matching.seams
    · have hk : s(slotsPerm k a,slotsPerm k b) ∈ (rename k P).matching.seams :=
        (pair_mem_rename (slotsPerm k) P.matching a b).mpr hab
      rw [rename_maps_at (g*k) P a b hab,hσ,hσ,
        rename_maps_at g (rename k P) _ _ hk,rename_maps_at k P a b hab]
      simp [vertexPerm,slotsPerm,dartPerm,slot_mul,mul_assoc]
    · have hl : s(slotsPerm (g*k) a,slotsPerm (g*k) b) ∉
          (rename (g*k) P).matching.seams := by
        simpa only [rename_matching,pair_mem_rename] using hab
      have hk : s(slotsPerm k a,slotsPerm k b) ∉ (rename k P).matching.seams := by
        simpa only [rename_matching,pair_mem_rename] using hab
      have hg : s(slotsPerm g (slotsPerm k a),slotsPerm g (slotsPerm k b)) ∉
          (rename g (rename k P)).matching.seams := by
        simpa only [rename_matching,pair_mem_rename] using hk
      rw [(rename (g*k) P).off_seam _ _ hl,hσ,hσ,
        (rename g (rename k P)).off_seam _ _ hg]

instance : MulAction (Frames C h) (Presentation C h) where
  smul := rename
  one_smul := rename_one
  mul_smul := rename_mul

/-- A cellwise affine presentation isomorphism, specified before taking a
quotient space. This is intentionally NOT an arbitrary homeomorphism. -/
def Compatible (g : Frames C h) (P Q : Presentation C h) : Prop :=
  Q.matching=renamePartial (slotsPerm g) P.matching ∧
  ∀ a b, s(a,b) ∈ P.matching.seams →
    Q.maps (slotsPerm g a) (slotsPerm g b)=
      vertexPerm g b.1*P.maps a b*(vertexPerm g a.1)⁻¹

/-- The independently stated geometric compatibility is exactly the action. -/
theorem compatible_iff (g : Frames C h) (P Q : Presentation C h) :
    Compatible g P Q ↔ g • P=Q := by
  constructor
  · rintro ⟨hm,hg⟩
    apply Presentation.ext hm.symm
    funext a b
    obtain ⟨a,rfl⟩ := (slotsPerm g).surjective a
    obtain ⟨b,rfl⟩ := (slotsPerm g).surjective b
    by_cases hab : s(a,b) ∈ P.matching.seams
    · exact (rename_maps_at g P a b hab).trans (hg a b hab).symm
    · have hnot : s(slotsPerm g a,slotsPerm g b) ∉ Q.matching.seams := by
        rw [hm]; simpa only [pair_mem_rename] using hab
      have hnot' : s(slotsPerm g a,slotsPerm g b) ∉ (rename g P).matching.seams := by
        simpa only [rename_matching,pair_mem_rename] using hab
      exact ((rename g P).off_seam _ _ hnot').trans (Q.off_seam _ _ hnot).symm
  · rintro rfl
    exact ⟨rfl,fun a b hab ↦ rename_maps_at g P a b hab⟩

abbrev GeometricIso (P Q : Presentation C h) := {g : Frames C h // Compatible g P Q}

/-- Actual presentation automorphisms correspond one-for-one to stabilizer
elements, with no free-action assumption. -/
def automorphismsEquivStabilizer (P : Presentation C h) :
    GeometricIso P P ≃ MulAction.stabilizer (Frames C h) P where
  toFun g := ⟨g.1,(compatible_iff _ _ _).mp g.2⟩
  invFun g := ⟨g.1,(compatible_iff _ _ _).mpr g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equivalence classes of geometric presentations, rather than bare spaces. -/
abbrev Classes (C : Type u) [DecidableEq C] (h : ℕ) :=
  MulAction.orbitRel.Quotient (Frames C h) (Presentation C h)

/-- This mass theorem is for the newly constructed geometric action. -/
theorem geometric_mass_eq_card [Fintype C] :
    ActionGroupoid.mass (Frames C h) (Presentation C h) ℚ =
      (Fintype.card (Presentation C h) : ℚ) /
        (((Fintype.card C).factorial*(Fintype.card (LocalRotation h))^(Fintype.card C) : ℕ) : ℚ) := by
  rw [ActionGroupoid.mass_eq_card_div_card,Renaming.WreathRenaming.card]

end
end PolytopeCounting.FacetPairing.GeometricPresentation
