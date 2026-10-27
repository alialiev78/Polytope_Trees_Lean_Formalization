module

public import Proofs.BridgeRestriction
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Circuit ranks of connected facet-pairing diagrams and bridge components

This module supplies the missing nonnegativity argument for the usual circuit
rank `edges + 1 - vertices`.  The dual object in `FacetPairingModel` is a
multigraph: loops and parallel seams are allowed.  We pass to the simple dual
graph by deleting loops and collapsing parallel seams.  A choice of one actual
seam above every simple dual edge embeds the edge set into the seam set.  Thus
Mathlib's spanning-tree inequality gives

`number of cells <= number of seams + 1`

for every finite connected coloured matching.  No freeness, labelling, or
geometric-realizability hypothesis is used.

The last part applies this result to the two restrictions obtained by cutting
a bridge and combines it with the already proved seam and cell partitions.
-/

namespace PolytopeCounting
namespace FacetPairing

noncomputable section

universe uC

variable {Cell : Type uC} [Fintype Cell] [DecidableEq Cell]
  {facets : Cell → ℕ} {r : ℕ}

/-! ## The simple dual graph and a seam selector -/

/-- The simple dual graph: loops are discarded by `fromRel`, while parallel
seams give the same simple edge. -/
def dualSimpleGraph
    (P : ColoredMatching (CellDart Cell facets) r) : SimpleGraph Cell :=
  SimpleGraph.fromRel (P.Adjacent facets)

/-- Since dual adjacency is symmetric, the adjacency relation of the simple
dual graph is just non-loop dual adjacency. -/
theorem dualSimpleGraph_adj_iff
    (P : ColoredMatching (CellDart Cell facets) r) (u v : Cell) :
    (dualSimpleGraph P).Adj u v ↔ u ≠ v ∧ P.Adjacent facets u v := by
  rw [dualSimpleGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, huv | hvu⟩
    · exact ⟨hne, huv⟩
    · exact ⟨hne, P.adjacent_symm facets hvu⟩
  · rintro ⟨hne, huv⟩
    exact ⟨hne, Or.inl huv⟩

/-- The unordered pair of cells underlying a seam. -/
def seamCellPair (e : Sym2 (CellDart Cell facets)) : Sym2 Cell :=
  Sym2.map Sigma.fst e

/-- Every edge of the simple dual graph is represented by an actual seam.
This is the precise choice statement that collapses parallel seams. -/
theorem exists_seam_over_dualEdge
    (P : ColoredMatching (CellDart Cell facets) r)
    (e : (dualSimpleGraph P).edgeSet) :
    ∃ s : P.Seam, seamCellPair s.1 = e.1 := by
  have hedge : (dualSimpleGraph P).Adj e.1.out.1 e.1.out.2 := by
    have he := e.2
    rw [← e.1.out_eq] at he
    exact he
  have hadj : P.Adjacent facets e.1.out.1 e.1.out.2 :=
    (dualSimpleGraph_adj_iff P _ _).mp hedge |>.2
  obtain ⟨i, j, hij⟩ := hadj
  refine ⟨⟨s(⟨e.1.out.1, i⟩, ⟨e.1.out.2, j⟩), hij⟩, ?_⟩
  simp only [seamCellPair, Sym2.map_mk]
  exact e.1.out_eq

/-- Choose one concrete seam over each simple dual edge. -/
def seamOfDualEdge
    (P : ColoredMatching (CellDart Cell facets) r) :
    (dualSimpleGraph P).edgeSet → P.Seam :=
  fun e ↦ Classical.choose (exists_seam_over_dualEdge P e)

@[simp]
theorem seamCellPair_seamOfDualEdge
    (P : ColoredMatching (CellDart Cell facets) r)
    (e : (dualSimpleGraph P).edgeSet) :
    seamCellPair (seamOfDualEdge P e).1 = e.1 :=
  Classical.choose_spec (exists_seam_over_dualEdge P e)

/-- Selecting one seam over each simple edge is injective, even though the
opposite projection from seams to edges need not be injective because of
parallel seams. -/
theorem seamOfDualEdge_injective
    (P : ColoredMatching (CellDart Cell facets) r) :
    Function.Injective (seamOfDualEdge P) := by
  intro e f hef
  apply Subtype.ext
  rw [← seamCellPair_seamOfDualEdge P e,
    ← seamCellPair_seamOfDualEdge P f, hef]

/-! ## Connectedness and the circuit-rank inequality -/

/-- A path for the multigraph adjacency becomes a path in the simple dual
graph.  A loop step becomes a reflexive step; a non-loop step becomes a
simple edge. -/
theorem reflTransGen_dualSimpleGraph_of_adjacent
    (P : ColoredMatching (CellDart Cell facets) r) {u v : Cell}
    (h : Relation.ReflTransGen (P.Adjacent facets) u v) :
    Relation.ReflTransGen (dualSimpleGraph P).Adj u v := by
  induction h with
  | refl => exact .refl
  | @tail x y hpath hxy ih =>
      by_cases hEq : x = y
      · subst y
        simpa using ih
      · exact ih.tail ((dualSimpleGraph_adj_iff P x y).mpr ⟨hEq, hxy⟩)

/-- Connectedness in the concrete multigraph sense implies preconnectedness
of the associated simple graph. -/
theorem dualSimpleGraph_preconnected
    (P : ColoredMatching (CellDart Cell facets) r)
    (hconnected : P.IsConnected facets) :
    (dualSimpleGraph P).Preconnected := by
  intro u v
  rw [SimpleGraph.reachable_iff_reflTransGen]
  exact reflTransGen_dualSimpleGraph_of_adjacent P (hconnected u v)

/-- A nonempty connected pairing has a connected simple dual graph. -/
theorem dualSimpleGraph_connected [Nonempty Cell]
    (P : ColoredMatching (CellDart Cell facets) r)
    (hconnected : P.IsConnected facets) :
    (dualSimpleGraph P).Connected where
  preconnected := dualSimpleGraph_preconnected P hconnected

/-- The simple dual edge set has cardinality at most the concrete seam set.
This is where loops and parallel seams are handled: they may increase the
right side, never the left side. -/
theorem card_dualEdges_le_seams
    (P : ColoredMatching (CellDart Cell facets) r) :
    Nat.card (dualSimpleGraph P).edgeSet ≤ P.matching.seams.card := by
  have h := Nat.card_le_card_of_injective
    (f := seamOfDualEdge P) (seamOfDualEdge_injective P)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h

/-- Every finite connected coloured matching has at least `vertices - 1`
seams.  This theorem is valid for the empty cell type too; that degenerate
case is discharged directly rather than pretending the empty graph is
`SimpleGraph.Connected`. -/
theorem card_cells_le_seams_add_one
    (P : ColoredMatching (CellDart Cell facets) r)
    (hconnected : P.IsConnected facets) :
    Fintype.card Cell ≤ P.matching.seams.card + 1 := by
  cases isEmpty_or_nonempty Cell with
  | inl hEmpty =>
      letI : IsEmpty Cell := hEmpty
      simp
  | inr hNonempty =>
      letI : Nonempty Cell := hNonempty
      have hgraph :=
        (dualSimpleGraph_connected P hconnected).card_vert_le_card_edgeSet_add_one
      have hedges := card_dualEdges_le_seams P
      rw [Nat.card_eq_fintype_card] at hgraph
      omega

/-- Circuit rank of a finite connected pairing.  It is defined by truncated
subtraction, with nonnegativity proved in `card_cells_le_seams_add_one`. -/
def circuitRank
    (P : ColoredMatching (CellDart Cell facets) r) : ℕ :=
  P.matching.seams.card + 1 - Fintype.card Cell

/-- Subtraction-free characterization of `circuitRank`. -/
theorem circuitRank_spec
    (P : ColoredMatching (CellDart Cell facets) r)
    (hconnected : P.IsConnected facets) :
    P.matching.seams.card + 1 = Fintype.card Cell + circuitRank P := by
  unfold circuitRank
  have h := card_cells_le_seams_add_one P hconnected
  omega

/-! ## Circuit ranks of the two bridge restrictions -/

/-- The ranks of both concrete connected restrictions exist, satisfy their
subtraction-free defining equations, and add to the rank of the original
connected diagram.  This is the circuit-rank bookkeeping needed in the bridge
branch of the cut--join recurrence. -/
theorem erase_bridge_component_ranks
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam)
    (hconnected : P.IsConnected facets) (hbridge : P.IsBridge e) :
    let Q := P.erase e
    let S := BridgePartition.LeftClass (Q.Adjacent facets) (P.leftCell e)
    let T := BridgePartition.RightClass (Q.Adjacent facets) (P.rightCell e)
    letI := Classical.decPred (fun x ↦ x ∈ S)
    letI := Classical.decPred (fun x ↦ x ∈ T)
    let L := Q.restrict S
    let R := Q.restrict T
    ∃ s t : ℕ,
      L.matching.seams.card + 1 = Fintype.card S + s ∧
      R.matching.seams.card + 1 = Fintype.card T + t ∧
      s + t = circuitRank P := by
  dsimp only
  let Q := P.erase e
  let C := P.bridge_partition e hconnected hbridge
  let S := BridgePartition.LeftClass (Q.Adjacent facets) (P.leftCell e)
  let T := BridgePartition.RightClass (Q.Adjacent facets) (P.rightCell e)
  letI := Classical.decPred (fun x ↦ x ∈ S)
  letI := Classical.decPred (fun x ↦ x ∈ T)
  let L := Q.restrict S
  let R := Q.restrict T
  let s := circuitRank L
  let t := circuitRank R
  have hLconn : L.IsConnected (fun c : S ↦ facets c.1) := by
    exact bridge_left_restriction_connected Q _ _ C
  have hRconn : R.IsConnected (fun c : T ↦ facets c.1) := by
    exact bridge_right_restriction_connected Q _ _ C
  have hLrank : L.matching.seams.card + 1 = Fintype.card S + s := by
    exact circuitRank_spec L hLconn
  have hRrank : R.matching.seams.card + 1 = Fintype.card T + t := by
    exact circuitRank_spec R hRconn
  have hVertices : Fintype.card S + Fintype.card T = Fintype.card Cell := by
    exact BridgePartition.class_sizes_add C
  have hRestrictedEdges :
      L.matching.seams.card + R.matching.seams.card = Q.matching.seams.card := by
    exact bridge_restricted_seam_counts_add Q _ _ C
  have hErasedEdges : Q.matching.seams.card + 1 = P.matching.seams.card := by
    exact P.matching.card_seams_erase e
  have hEdges :
      L.matching.seams.card + R.matching.seams.card + 1 =
        P.matching.seams.card := by
    omega
  have hOriginalRank :
      P.matching.seams.card + 1 = Fintype.card Cell + circuitRank P :=
    circuitRank_spec P hconnected
  have hAdd : s + t = circuitRank P :=
    BridgePartition.circuitRanks_add hVertices hEdges hOriginalRank hLrank hRrank
  exact ⟨s, t, hLrank, hRrank, hAdd⟩

end
end FacetPairing
end PolytopeCounting
