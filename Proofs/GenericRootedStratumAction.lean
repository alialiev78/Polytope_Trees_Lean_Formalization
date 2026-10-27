module

public import Proofs.RenamingAction
public import Proofs.ActionGroupoidMass

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Generic local-symmetry action on fixed-base rooted strata

The base cell and its facet slots are fixed pointwise.  An arbitrary finite
local group `L` acts on the `h` slots of each ordinary cell, while ordinary
cells are permuted.  This is the rooted counterpart of
`GenericStratumAction` and gives the manuscript denominator
`n! * |L|^n`, hence `n! * tau^n` after naming `tau = |L|`.
-/

namespace PolytopeCounting
namespace Renaming
namespace GenericRootedStratumAction

open FacetPairing MatchingTransport

noncomputable section

universe uL uK

variable {L : Type uL}

/-- The cell permutation induced by a wreath renaming fixes the base. -/
def cellPerm {n : ℕ} [Group L]
    (a : WreathRenaming (Fin n) L) : Equiv.Perm (RootedCell n) :=
  (Equiv.refl Unit).sumCongr a.cell

@[simp] theorem cellPerm_base {n : ℕ} [Group L]
    (a : WreathRenaming (Fin n) L) :
    cellPerm a (baseCell n) = baseCell n := rfl

@[simp] theorem cellPerm_ordinary {n : ℕ} [Group L]
    (a : WreathRenaming (Fin n) L) (i : Fin n) :
    cellPerm a (Sum.inr i) = Sum.inr (a.cell i) := rfl

/-- The fibre permutation of facet slots above one rooted cell. -/
def facetPermAt {n h₀ h : ℕ} [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L) (u : RootedCell n) :
    Fin (rootedFacets h₀ h u) ≃
      Fin (rootedFacets h₀ h (cellPerm a u)) :=
  match u with
  | Sum.inl _ => Equiv.refl (Fin h₀)
  | Sum.inr i => (MulAction.toPerm (a.slot i) : Equiv.Perm (Fin h))

/-- The base-preserving rooted dart permutation for an arbitrary local
symmetry group. -/
def dartPerm {n h₀ h : ℕ} [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L) :
    Equiv.Perm (RootedDart n h₀ h) where
  toFun x := ⟨cellPerm a x.1, facetPermAt a x.1 x.2⟩
  invFun x :=
    match x with
    | ⟨Sum.inl u, i⟩ => ⟨Sum.inl u, i⟩
    | ⟨Sum.inr j, i⟩ => by
        change Fin h at i
        exact ⟨Sum.inr (a.cell⁻¹ j),
          (a.slot (a.cell⁻¹ j))⁻¹ • i⟩
  left_inv x := by
    rcases x with ⟨u, i⟩
    cases u with
    | inl u => rfl
    | inr c =>
        change Fin h at i
        apply Sigma.ext
        · simp [cellPerm]
        · apply heq_of_eq
          change (a.slot (a.cell⁻¹ (a.cell c)))⁻¹ •
              (a.slot c • (i : Fin h)) = i
          have hc : a.cell⁻¹ (a.cell c) = c := a.cell.symm_apply_apply c
          rw [hc]
          exact inv_smul_smul _ _
  right_inv x := by
    rcases x with ⟨u, i⟩
    cases u with
    | inl u => rfl
    | inr c =>
        change Fin h at i
        apply Sigma.ext
        · simp [cellPerm]
        · apply heq_of_eq
          exact smul_inv_smul (a.slot (a.cell⁻¹ c)) i

@[simp] theorem dartPerm_apply {n h₀ h : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L) (u : RootedCell n)
    (i : Fin (rootedFacets h₀ h u)) :
    dartPerm a ⟨u, i⟩ = ⟨cellPerm a u, facetPermAt a u i⟩ := rfl

@[simp] theorem dartPerm_one (n h₀ h : ℕ)
    [Group L] [MulAction L (Fin h)] :
    dartPerm (L := L) (h₀ := h₀) (h := h)
      (1 : WreathRenaming (Fin n) L) = 1 := by
  apply Equiv.ext
  rintro ⟨u, i⟩
  cases u with
  | inl u => rfl
  | inr c =>
      change Fin h at i
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        exact one_smul L i

@[simp] theorem dartPerm_mul {n h₀ h : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a b : WreathRenaming (Fin n) L) :
    dartPerm (h₀ := h₀) (h := h) (a * b) =
      dartPerm (h₀ := h₀) (h := h) a *
        dartPerm (h₀ := h₀) (h := h) b := by
  apply Equiv.ext
  rintro ⟨u, i⟩
  cases u with
  | inl u => rfl
  | inr c =>
      change Fin h at i
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        exact mul_smul (a.slot (b.cell c)) (b.slot c) i

/-- Generic base-preserving renaming preserves adjacency. -/
theorem adjacent_renameRooted {n h₀ h r : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L)
    (P : ColoredMatching (RootedDart n h₀ h) r)
    {u v : RootedCell n}
    (huv : P.Adjacent (rootedFacets h₀ h) u v) :
    (renameColored (dartPerm a) P).Adjacent (rootedFacets h₀ h)
      (cellPerm a u) (cellPerm a v) := by
  rcases huv with ⟨i, j, hij⟩
  refine ⟨facetPermAt a u i, facetPermAt a v j, ?_⟩
  change s(⟨cellPerm a u, facetPermAt a u i⟩,
      ⟨cellPerm a v, facetPermAt a v j⟩) ∈
    (renamePartial (dartPerm a) P.matching).seams
  apply Finset.mem_map.mpr
  exact ⟨s(⟨u, i⟩, ⟨v, j⟩), hij, rfl⟩

/-- Generic base-preserving renaming preserves connectivity. -/
theorem connected_renameRooted {n h₀ h r : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L)
    (P : ColoredMatching (RootedDart n h₀ h) r)
    (hP : P.IsConnected (rootedFacets h₀ h)) :
    (renameColored (dartPerm a) P).IsConnected (rootedFacets h₀ h) := by
  intro u v
  have oldPath := hP ((cellPerm a).symm u) ((cellPerm a).symm v)
  have newPath := oldPath.lift (cellPerm a)
    (fun _ _ hxy ↦ adjacent_renameRooted a P hxy)
  simpa [Function.onFun] using newPath

/-- Rename a connected rooted diagram by a generic local group. -/
def renameRootedDiagram {n h₀ h r m : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L) (P : RootedDiagram n h₀ h r m) :
    RootedDiagram n h₀ h r m where
  raw := renameLabelled (dartPerm a) P.raw
  connected := connected_renameRooted a P.raw.pairing P.connected

@[simp] theorem renameRootedDiagram_one {n h₀ h r m : ℕ}
    [Group L] [MulAction L (Fin h)] (P : RootedDiagram n h₀ h r m) :
    renameRootedDiagram (L := L) 1 P = P := by
  apply ConnectedDiagram.raw_injective
  change renameLabelled (dartPerm (h₀ := h₀)
    (1 : WreathRenaming (Fin n) L)) P.raw = P.raw
  rw [dartPerm_one]
  exact renameLabelled_one P.raw

@[simp] theorem renameRootedDiagram_mul {n h₀ h r m : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a b : WreathRenaming (Fin n) L) (P : RootedDiagram n h₀ h r m) :
    renameRootedDiagram (a * b) P =
      renameRootedDiagram a (renameRootedDiagram b P) := by
  apply ConnectedDiagram.raw_injective
  change renameLabelled (dartPerm (h₀ := h₀) (a * b)) P.raw =
    renameLabelled (dartPerm a) (renameLabelled (dartPerm b) P.raw)
  rw [dartPerm_mul]
  exact renameLabelled_mul _ _ P.raw

instance genericSMulRootedDiagram
    (n h₀ h r m : ℕ) (L : Type uL)
    [Group L] [MulAction L (Fin h)] :
    SMul (WreathRenaming (Fin n) L) (RootedDiagram n h₀ h r m) where
  smul := renameRootedDiagram

instance genericMulActionRootedDiagram
    (n h₀ h r m : ℕ) (L : Type uL)
    [Group L] [MulAction L (Fin h)] :
    MulAction (WreathRenaming (Fin n) L) (RootedDiagram n h₀ h r m) where
  one_smul := renameRootedDiagram_one
  mul_smul := renameRootedDiagram_mul

theorem edgeCount_renameRootedDiagram {n h₀ h r m : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L) (P : RootedDiagram n h₀ h r m) :
    (renameRootedDiagram a P).edgeCount = P.edgeCount := by
  simp [ConnectedDiagram.edgeCount, BoundaryLabelledPairing.edgeCount,
    ColoredMatching.edgeCount, renameRootedDiagram, renameLabelled,
    renameColored]

/-- Generic base-preserving renaming preserves rooted rank strata. -/
def renameRootedStratum {n h₀ h r m b : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L) (P : RootedStratum n h₀ h r m b) :
    RootedStratum n h₀ h r m b :=
  ⟨renameRootedDiagram a P.1, by
    unfold ConnectedDiagram.HasCircuitRank
    rw [edgeCount_renameRootedDiagram]
    exact P.2⟩

@[simp] theorem renameRootedStratum_one {n h₀ h r m b : ℕ}
    [Group L] [MulAction L (Fin h)] (P : RootedStratum n h₀ h r m b) :
    renameRootedStratum (L := L) 1 P = P := by
  apply Subtype.ext
  exact renameRootedDiagram_one (L := L) P.1

@[simp] theorem renameRootedStratum_mul {n h₀ h r m b : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a c : WreathRenaming (Fin n) L) (P : RootedStratum n h₀ h r m b) :
    renameRootedStratum (a * c) P =
      renameRootedStratum a (renameRootedStratum c P) := by
  apply Subtype.ext
  exact renameRootedDiagram_mul a c P.1

instance genericSMulRootedStratum
    (n h₀ h r m b : ℕ) (L : Type uL)
    [Group L] [MulAction L (Fin h)] :
    SMul (WreathRenaming (Fin n) L) (RootedStratum n h₀ h r m b) where
  smul := renameRootedStratum

instance genericMulActionRootedStratum
    (n h₀ h r m b : ℕ) (L : Type uL)
    [Group L] [MulAction L (Fin h)] :
    MulAction (WreathRenaming (Fin n) L) (RootedStratum n h₀ h r m b) where
  one_smul := renameRootedStratum_one
  mul_smul := renameRootedStratum_mul

local instance rootedStratumFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedStratum n h₀ h r m b) := Fintype.ofFinite _

/-- Non-free groupoid mass of a rooted stratum for arbitrary local symmetry
group `L`. -/
theorem mass_genericWreath_rootedStratum
    (n h₀ h r m b : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (K : Type uK) [Field K] [CharZero K] :
    ActionGroupoid.mass (WreathRenaming (Fin n) L)
        (RootedStratum n h₀ h r m b) K =
      (Fintype.card (RootedStratum n h₀ h r m b) : K) /
        ((n.factorial * (Fintype.card L) ^ n : ℕ) : K) := by
  rw [ActionGroupoid.mass_eq_card_div_card, WreathRenaming.card]
  simp only [Fintype.card_fin]

/-- Named-order specialization `tau = |L|`. -/
theorem mass_genericWreath_rootedStratum_of_card
    (n h₀ h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (K : Type uK) [Field K] [CharZero K]
    (hcard : Fintype.card L = tau) :
    ActionGroupoid.mass (WreathRenaming (Fin n) L)
        (RootedStratum n h₀ h r m b) K =
      (Fintype.card (RootedStratum n h₀ h r m b) : K) /
        ((n.factorial * tau ^ n : ℕ) : K) := by
  simpa only [hcard] using
    (mass_genericWreath_rootedStratum (L := L) n h₀ h r m b K)


end
end GenericRootedStratumAction
end Renaming
end PolytopeCounting
