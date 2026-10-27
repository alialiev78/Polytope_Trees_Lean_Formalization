module

public import Proofs.RenamingAction

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Generic local-symmetry action on connected unrooted strata

Let `L` be a group acting on the `h` facet slots. A cell permutation together
with one element of `L` at every cell acts on connected, boundary-labelled,
coloured diagrams.

Every preservation statement below is proved from the dart transport in
`RenamingAction`: adjacency, connectedness, edge count, and circuit rank.
-/

namespace PolytopeCounting
namespace Renaming
namespace GenericStratumAction

open FacetPairing
open MatchingTransport

universe uL

variable {L : Type uL}

/-- Forward preservation of adjacency for an arbitrary local slot action. -/
theorem adjacent_renameUnrooted {n h r : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L)
    (P : ColoredMatching (FacetPairing.Dart n h) r)
    {u v : Fin n}
    (huv : P.Adjacent (fun _ ↦ h) u v) :
    (renameColored (WreathRenaming.dartPerm (Fin h) a) P).Adjacent
      (fun _ ↦ h) (a.cell u) (a.cell v) := by
  rcases huv with ⟨i, j, hij⟩
  refine ⟨a.slot u • i, a.slot v • j, ?_⟩
  change s(⟨a.cell u, a.slot u • i⟩, ⟨a.cell v, a.slot v • j⟩) ∈
    (renamePartial (WreathRenaming.dartPerm (Fin h) a) P.matching).seams
  apply Finset.mem_map.mpr
  exact ⟨s(⟨u, i⟩, ⟨v, j⟩), hij, rfl⟩

/-- Adjacency is not merely preserved: it is reflected by every renaming. -/
theorem adjacent_renameUnrooted_iff {n h r : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L)
    (P : ColoredMatching (FacetPairing.Dart n h) r)
    {u v : Fin n} :
    (renameColored (WreathRenaming.dartPerm (Fin h) a) P).Adjacent
        (fun _ ↦ h) (a.cell u) (a.cell v) ↔
      P.Adjacent (fun _ ↦ h) u v := by
  constructor
  · intro huv
    have hback := adjacent_renameUnrooted
      (L := L) (a := a⁻¹)
      (P := renameColored (WreathRenaming.dartPerm (Fin h) a) P) huv
    have hclean :
        P.Adjacent (fun _ ↦ h) (a⁻¹.cell (a.cell u)) (a⁻¹.cell (a.cell v)) := by
      simpa only [← renameColored_mul, ← WreathRenaming.dartPerm_mul,
        inv_mul_cancel, WreathRenaming.dartPerm_one, renameColored_one] using hback
    have hu : a⁻¹.cell (a.cell u) = u := by
      change a.cell.symm (a.cell u) = u
      exact a.cell.symm_apply_apply u
    have hv : a⁻¹.cell (a.cell v) = v := by
      change a.cell.symm (a.cell v) = v
      exact a.cell.symm_apply_apply v
    simpa only [hu, hv] using hclean
  · exact adjacent_renameUnrooted (L := L) a P

/-- Generic wreath renaming preserves dual connectivity. -/
theorem connected_renameUnrooted {n h r : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L)
    (P : ColoredMatching (FacetPairing.Dart n h) r)
    (hP : P.IsConnected (fun _ ↦ h)) :
    (renameColored (WreathRenaming.dartPerm (Fin h) a) P).IsConnected
      (fun _ ↦ h) := by
  intro u v
  have oldPath := hP (a.cell.symm u) (a.cell.symm v)
  have newPath := oldPath.lift a.cell
    (fun _ _ hxy ↦ adjacent_renameUnrooted (L := L) a P hxy)
  simpa [Function.onFun] using newPath

/-- Rename a connected unrooted diagram using an arbitrary local group. -/
def renameUnrootedDiagram {n h r m : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L)
    (P : FacetPairing.UnrootedDiagram n h r m) :
    FacetPairing.UnrootedDiagram n h r m where
  raw := renameLabelled (WreathRenaming.dartPerm (Fin h) a) P.raw
  connected := connected_renameUnrooted (L := L) a P.raw.pairing P.connected

@[simp]
theorem raw_renameUnrootedDiagram {n h r m : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L)
    (P : FacetPairing.UnrootedDiagram n h r m) :
    (renameUnrootedDiagram a P).raw =
      renameLabelled (WreathRenaming.dartPerm (Fin h) a) P.raw := rfl

@[simp]
theorem renameUnrootedDiagram_one {n h r m : ℕ}
    [Group L] [MulAction L (Fin h)]
    (P : FacetPairing.UnrootedDiagram n h r m) :
    renameUnrootedDiagram (L := L) 1 P = P := by
  apply FacetPairing.ConnectedDiagram.raw_injective
  change renameLabelled
    (WreathRenaming.dartPerm (Fin h) (1 : WreathRenaming (Fin n) L))
      P.raw = P.raw
  rw [WreathRenaming.dartPerm_one]
  exact renameLabelled_one P.raw

@[simp]
theorem renameUnrootedDiagram_mul {n h r m : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a c : WreathRenaming (Fin n) L)
    (P : FacetPairing.UnrootedDiagram n h r m) :
    renameUnrootedDiagram (a * c) P =
      renameUnrootedDiagram a (renameUnrootedDiagram c P) := by
  apply FacetPairing.ConnectedDiagram.raw_injective
  change renameLabelled (WreathRenaming.dartPerm (Fin h) (a * c)) P.raw =
    renameLabelled (WreathRenaming.dartPerm (Fin h) a)
      (renameLabelled (WreathRenaming.dartPerm (Fin h) c) P.raw)
  rw [WreathRenaming.dartPerm_mul]
  exact renameLabelled_mul _ _ P.raw

instance genericSMulUnrootedDiagram
    (n h r m : ℕ) (L : Type uL) [Group L] [MulAction L (Fin h)] :
    SMul (WreathRenaming (Fin n) L)
      (FacetPairing.UnrootedDiagram n h r m) where
  smul := renameUnrootedDiagram

instance genericMulActionUnrootedDiagram
    (n h r m : ℕ) (L : Type uL) [Group L] [MulAction L (Fin h)] :
    MulAction (WreathRenaming (Fin n) L)
      (FacetPairing.UnrootedDiagram n h r m) where
  one_smul := renameUnrootedDiagram_one
  mul_smul := renameUnrootedDiagram_mul

/-- Dart transport preserves the number of seams. -/
theorem edgeCount_renameUnrootedDiagram {n h r m : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L)
    (P : FacetPairing.UnrootedDiagram n h r m) :
    (renameUnrootedDiagram a P).edgeCount = P.edgeCount := by
  simp [FacetPairing.ConnectedDiagram.edgeCount,
    FacetPairing.BoundaryLabelledPairing.edgeCount,
    FacetPairing.ColoredMatching.edgeCount, renameUnrootedDiagram,
    renameLabelled, renameColored]

/-- Circuit rank is preserved and reflected, stated independently of the
subtype construction below. -/
theorem hasCircuitRank_renameUnrootedDiagram_iff {n h r m b : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L)
    (P : FacetPairing.UnrootedDiagram n h r m) :
    (renameUnrootedDiagram a P).HasCircuitRank b ↔
      P.HasCircuitRank b := by
  unfold FacetPairing.ConnectedDiagram.HasCircuitRank
  rw [edgeCount_renameUnrootedDiagram]

/-- The generic local-group action preserves every circuit-rank stratum. -/
def renameUnrootedStratum {n h r m b : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a : WreathRenaming (Fin n) L)
    (P : FacetPairing.UnrootedStratum n h r m b) :
    FacetPairing.UnrootedStratum n h r m b :=
  ⟨renameUnrootedDiagram a P.1, by
    unfold FacetPairing.ConnectedDiagram.HasCircuitRank
    rw [edgeCount_renameUnrootedDiagram]
    exact P.2⟩

@[simp]
theorem renameUnrootedStratum_one {n h r m b : ℕ}
    [Group L] [MulAction L (Fin h)]
    (P : FacetPairing.UnrootedStratum n h r m b) :
    renameUnrootedStratum (L := L) 1 P = P := by
  apply Subtype.ext
  exact renameUnrootedDiagram_one (L := L) P.1

@[simp]
theorem renameUnrootedStratum_mul {n h r m b : ℕ}
    [Group L] [MulAction L (Fin h)]
    (a c : WreathRenaming (Fin n) L)
    (P : FacetPairing.UnrootedStratum n h r m b) :
    renameUnrootedStratum (a * c) P =
      renameUnrootedStratum a (renameUnrootedStratum c P) := by
  apply Subtype.ext
  exact renameUnrootedDiagram_mul a c P.1

instance genericSMulUnrootedStratum
    (n h r m b : ℕ) (L : Type uL) [Group L] [MulAction L (Fin h)] :
    SMul (WreathRenaming (Fin n) L)
      (FacetPairing.UnrootedStratum n h r m b) where
  smul := renameUnrootedStratum

instance genericMulActionUnrootedStratum
    (n h r m b : ℕ) (L : Type uL) [Group L] [MulAction L (Fin h)] :
    MulAction (WreathRenaming (Fin n) L)
      (FacetPairing.UnrootedStratum n h r m b) where
  one_smul := renameUnrootedStratum_one
  mul_smul := renameUnrootedStratum_mul


end GenericStratumAction
end Renaming
end PolytopeCounting
