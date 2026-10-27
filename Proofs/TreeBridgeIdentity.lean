module

public import Proofs.CircuitRankComponents
public import Proofs.PointedDecomposition

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Rank-zero connected diagrams have only bridge seams

For a connected finite pairing, deleting a seam leaves one fewer seam.  If
the deletion were still connected, the simple-dual-graph inequality from
`CircuitRankComponents` would force the number of cells to be at most the
original number of seams.  In circuit rank zero the defining equation says
that the number of cells is *one more* than the number of seams.  Hence every
seam is a bridge.

The remainder of this file packages that observation for the literal
pointed unrooted and rooted strata.  It gives exact equivalences with the
bridge-pointed subtypes, proves the nonbridge-pointed tree strata empty, and
derives the `(n - 1)` and `n` pointing factors needed on the left sides of
the tree recurrences.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace TreeBridgeIdentity

noncomputable section

open PointedDecomposition

universe uC

variable {Cell : Type uC} [Fintype Cell] [DecidableEq Cell]
  {facets : Cell → ℕ} {r m : ℕ}

/-! ## The generic rank-zero bridge theorem -/

/-- Every seam of a finite connected circuit-rank-zero diagram is a bridge.

This proof uses only the exact one-seam erasure count, connectedness after
erasure in the contrary branch, and `card_cells_le_seams_add_one`.  It does
not assume simplicity of the dual multigraph. -/
theorem every_seam_isBridge_of_rank_zero
    (P : ConnectedDiagram Cell facets r m)
    (hrank : P.HasCircuitRank 0)
    (e : P.raw.pairing.Seam) :
    P.raw.pairing.IsBridge e := by
  intro herasedConnected
  have hLower := card_cells_le_seams_add_one
    (P.raw.pairing.erase e) herasedConnected
  have hErase :
      (P.raw.pairing.erase e).matching.seams.card + 1 =
        P.raw.pairing.matching.seams.card := by
    exact P.raw.pairing.matching.card_seams_erase e
  have hRank :
      P.raw.pairing.matching.seams.card + 1 = Fintype.card Cell := by
    simpa [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
      BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount] using hrank
  omega

/-- Unrooted specialization of `every_seam_isBridge_of_rank_zero`. -/
theorem unrooted_tree_every_seam_isBridge
    (P : UnrootedStratum n h r m 0)
    (e : P.1.raw.pairing.Seam) :
    P.1.raw.pairing.IsBridge e :=
  every_seam_isBridge_of_rank_zero P.1 P.2 e

/-- Rooted specialization of `every_seam_isBridge_of_rank_zero`; the fixed
base cell is simply one of the vertices for the graph inequality. -/
theorem rooted_tree_every_seam_isBridge
    (P : RootedStratum n h₀ h r m 0)
    (e : P.1.raw.pairing.Seam) :
    P.1.raw.pairing.IsBridge e :=
  every_seam_isBridge_of_rank_zero P.1 P.2 e

/-! ## Exact pointed equivalences -/

/-- Pointing a rank-zero unrooted diagram already lands in the bridge
subtype; forgetting the proof is the inverse equivalence. -/
def unrootedTreePointedEquivBridge (n h r m : ℕ) :
    UnrootedPointed n h r m 0 ≃ UnrootedBridgePointed n h r m 0 where
  toFun z := ⟨z, unrooted_tree_every_seam_isBridge z.1 z.2⟩
  invFun z := z.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

/-- Pointing a rank-zero rooted diagram already lands in the bridge subtype. -/
def rootedTreePointedEquivBridge (n h₀ h r m : ℕ) :
    RootedPointed n h₀ h r m 0 ≃ RootedBridgePointed n h₀ h r m 0 where
  toFun z := ⟨z, rooted_tree_every_seam_isBridge z.1 z.2⟩
  invFun z := z.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

/-! ## The nonbridge tree branch is empty -/

/-- There is no nonbridge-pointed unrooted rank-zero diagram. -/
theorem unrootedTreeNonbridgePointed_isEmpty (n h r m : ℕ) :
    IsEmpty (UnrootedNonbridgePointed n h r m 0) :=
  ⟨fun z ↦
    (unrooted_tree_every_seam_isBridge z.1.1 z.1.2) z.2⟩

/-- There is no nonbridge-pointed rooted rank-zero diagram. -/
theorem rootedTreeNonbridgePointed_isEmpty (n h₀ h r m : ℕ) :
    IsEmpty (RootedNonbridgePointed n h₀ h r m 0) :=
  ⟨fun z ↦
    (rooted_tree_every_seam_isBridge z.1.1 z.1.2) z.2⟩

noncomputable local instance unrootedStratumFintype
    (n h r m : ℕ) : Fintype (UnrootedStratum n h r m 0) :=
  Fintype.ofFinite _

noncomputable local instance rootedStratumFintype
    (n h₀ h r m : ℕ) : Fintype (RootedStratum n h₀ h r m 0) :=
  Fintype.ofFinite _

noncomputable local instance unrootedNonbridgePointedFintype
    (n h r m : ℕ) : Fintype (UnrootedNonbridgePointed n h r m 0) :=
  Fintype.ofFinite _

noncomputable local instance unrootedBridgePointedFintype
    (n h r m : ℕ) : Fintype (UnrootedBridgePointed n h r m 0) :=
  Fintype.ofFinite _

noncomputable local instance rootedNonbridgePointedFintype
    (n h₀ h r m : ℕ) : Fintype (RootedNonbridgePointed n h₀ h r m 0) :=
  Fintype.ofFinite _

noncomputable local instance rootedBridgePointedFintype
    (n h₀ h r m : ℕ) : Fintype (RootedBridgePointed n h₀ h r m 0) :=
  Fintype.ofFinite _

/-- Cardinal form of the empty unrooted nonbridge tree branch. -/
theorem card_unrootedTreeNonbridgePointed (n h r m : ℕ) :
    Fintype.card (UnrootedNonbridgePointed n h r m 0) = 0 := by
  letI : IsEmpty (UnrootedNonbridgePointed n h r m 0) :=
    unrootedTreeNonbridgePointed_isEmpty n h r m
  exact Fintype.card_eq_zero

/-- Cardinal form of the empty rooted nonbridge tree branch. -/
theorem card_rootedTreeNonbridgePointed (n h₀ h r m : ℕ) :
    Fintype.card (RootedNonbridgePointed n h₀ h r m 0) = 0 := by
  letI : IsEmpty (RootedNonbridgePointed n h₀ h r m 0) :=
    rootedTreeNonbridgePointed_isEmpty n h₀ h r m
  exact Fintype.card_eq_zero

/-! ## Exact tree pointing factors -/

/-- The unrooted bridge-pointed rank-zero stratum has the full tree pointing
factor `(n - 1)`. -/
theorem card_unrootedTreeBridgePointed (n h r m : ℕ) :
    Fintype.card (UnrootedBridgePointed n h r m 0) =
      (n - 1) * Fintype.card (UnrootedStratum n h r m 0) := by
  calc
    Fintype.card (UnrootedBridgePointed n h r m 0) =
        Fintype.card (UnrootedPointed n h r m 0) :=
      Fintype.card_congr (unrootedTreePointedEquivBridge n h r m).symm
    _ = (n - 1) * Fintype.card (UnrootedStratum n h r m 0) := by
      simpa using PointedDecomposition.card_unrootedPointed n h r m 0

/-- The rooted bridge-pointed rank-zero stratum has the full tree pointing
factor `n`; the base cell accounts for the shift from the unrooted formula. -/
theorem card_rootedTreeBridgePointed (n h₀ h r m : ℕ) :
    Fintype.card (RootedBridgePointed n h₀ h r m 0) =
      n * Fintype.card (RootedStratum n h₀ h r m 0) := by
  calc
    Fintype.card (RootedBridgePointed n h₀ h r m 0) =
        Fintype.card (RootedPointed n h₀ h r m 0) :=
      Fintype.card_congr (rootedTreePointedEquivBridge n h₀ h r m).symm
    _ = n * Fintype.card (RootedStratum n h₀ h r m 0) := by
      simpa using PointedDecomposition.card_rootedPointed n h₀ h r m 0


end
end TreeBridgeIdentity
end FacetPairing
end PolytopeCounting
