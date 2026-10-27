module

public import Proofs.BridgePartition

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# The bridge dichotomy for a marked seam

This file specializes the abstract one-edge deletion theorem to the concrete
facet-pairing model.  It proves, rather than assumes, that the dual adjacency
before deletion is exactly the adjacency after deletion plus the one
undirected edge determined by the marked seam's endpoint cells.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace ColoredMatching

universe uC

variable {Cell : Type uC} [DecidableEq Cell]
  {facets : Cell → ℕ} {r : ℕ}

/-- Cell containing the first dart in the chosen representative of a seam. -/
noncomputable def leftCell
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam) : Cell :=
  e.1.out.1.1

/-- Cell containing the second dart in the chosen representative of a seam. -/
noncomputable def rightCell
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam) : Cell :=
  e.1.out.2.1

theorem seam_out_repr (P : ColoredMatching (CellDart Cell facets) r)
    (e : P.Seam) : s(e.1.out.1, e.1.out.2) = e.1 := by
  rw [Sym2.mk, e.1.out_eq]

/-- Erasing one marked seam changes the dual adjacency by exactly one
undirected edge between its endpoint cells. -/
theorem adjacent_eq_addEdge_erase
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam) :
    P.Adjacent facets =
      BridgePartition.AddEdge ((P.erase e).Adjacent facets)
        (P.leftCell e) (P.rightCell e) := by
  funext u v
  apply propext
  constructor
  · rintro ⟨i, j, hij⟩
    by_cases heq : s(⟨u, i⟩, ⟨v, j⟩) = e.1
    · have heq' :
          s(⟨u, i⟩, ⟨v, j⟩) = s(e.1.out.1, e.1.out.2) :=
          heq.trans (P.seam_out_repr e).symm
      have hor :
          (⟨u, i⟩ = e.1.out.1 ∧ ⟨v, j⟩ = e.1.out.2) ∨
          (⟨u, i⟩ = e.1.out.2 ∧ ⟨v, j⟩ = e.1.out.1) := by
        simpa only [Sym2.eq, Sym2.rel_iff] using heq'
      rcases hor with ⟨hui, hvj⟩ | ⟨hui, hvj⟩
      · exact Or.inr (Or.inl ⟨congrArg Sigma.fst hui,
          congrArg Sigma.fst hvj⟩)
      · exact Or.inr (Or.inr ⟨congrArg Sigma.fst hui,
          congrArg Sigma.fst hvj⟩)
    · exact Or.inl ⟨i, j, Finset.mem_erase.mpr ⟨heq, hij⟩⟩
  · rintro (hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · obtain ⟨i, j, hij⟩ := hold
      exact ⟨i, j, Finset.mem_of_mem_erase hij⟩
    · refine ⟨e.1.out.1.2, e.1.out.2.2, ?_⟩
      simpa [leftCell, rightCell, P.seam_out_repr e] using e.2
    · refine ⟨e.1.out.2.2, e.1.out.1.2, ?_⟩
      rw [Sym2.eq_swap]
      simpa [leftCell, rightCell, P.seam_out_repr e] using e.2

/-- A marked seam is non-bridging precisely when its deletion leaves the
dual graph connected.  This is a definition with a named iff for recurrence
proofs, so neither branch is hidden in prose. -/
def IsNonbridge
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam) : Prop :=
  (P.erase e).IsConnected facets

def IsBridge
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam) : Prop :=
  ¬(P.erase e).IsConnected facets

theorem isNonbridge_iff_connected_after_erase
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam) :
    P.IsNonbridge e ↔ (P.erase e).IsConnected facets := Iff.rfl

theorem isBridge_iff_not_connected_after_erase
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam) :
    P.IsBridge e ↔ ¬(P.erase e).IsConnected facets := Iff.rfl

theorem nonbridge_or_bridge
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam) :
    P.IsNonbridge e ∨ P.IsBridge e := by
  exact Classical.em ((P.erase e).IsConnected facets)

/-- If the original dual graph is connected and deletion disconnects it,
the endpoint reachability classes give the exact bridge partition. -/
theorem bridge_partition
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam)
    (hconnected : P.IsConnected facets) (hbridge : P.IsBridge e) :
    BridgePartition.Certificate ((P.erase e).Adjacent facets)
      (P.leftCell e) (P.rightCell e) := by
  apply BridgePartition.bridge_certificate
    ((P.erase e).adjacent_symm facets)
  constructor
  · intro u v
    rw [← P.adjacent_eq_addEdge_erase e]
    exact hconnected u v
  · exact hbridge

/-- Full marked-seam deletion dichotomy for a connected diagram. -/
theorem connected_erase_or_bridge_partition
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam)
    (hconnected : P.IsConnected facets) :
    (P.erase e).IsConnected facets ∨
      BridgePartition.Certificate ((P.erase e).Adjacent facets)
        (P.leftCell e) (P.rightCell e) := by
  by_cases h : (P.erase e).IsConnected facets
  · exact Or.inl h
  · exact Or.inr (P.bridge_partition e hconnected h)

/-- In the bridge branch, the two dual component sizes add to the original
number of cells and each is positive. -/
theorem bridge_component_sizes
    [Fintype Cell]
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam)
    (hconnected : P.IsConnected facets) (hbridge : P.IsBridge e) :
    let old := (P.erase e).Adjacent facets
    letI := Classical.decPred
      (fun x ↦ x ∈ BridgePartition.LeftClass old (P.leftCell e))
    letI := Classical.decPred
      (fun x ↦ x ∈ BridgePartition.RightClass old (P.rightCell e))
    let n₁ := Fintype.card (BridgePartition.LeftClass old (P.leftCell e))
    let n₂ := Fintype.card (BridgePartition.RightClass old (P.rightCell e))
    n₁ + n₂ = Fintype.card Cell ∧ 0 < n₁ ∧ 0 < n₂ := by
  dsimp only
  let C := P.bridge_partition e hconnected hbridge
  refine ⟨?_, BridgePartition.left_class_size_pos,
    BridgePartition.right_class_size_pos⟩
  exact BridgePartition.class_sizes_add C

end ColoredMatching
end FacetPairing
end PolytopeCounting
