module

public import Proofs.BridgeLabelledRestriction
public import Proofs.MarkedSeamBridge

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Joining two connected components creates a bridge

This module supplies the converse of bridge restriction.  Start with two
disjoint, covering cell sets, connected coloured matchings on the two
restricted dart types, and one free dart on each side.  Reassemble the two
components and join those free darts.  The result is connected, while
erasing the new seam recovers the disconnected reassembly.  Thus the new
seam is a genuine bridge.
-/

namespace PolytopeCounting
namespace FacetPairing

noncomputable section

universe uC

variable {Cell : Type uC} [Fintype Cell] [DecidableEq Cell]
  {facets : Cell → ℕ} {r : ℕ}

namespace JoinComponentsBridge

variable (S T : Set Cell) (hcover : S ∪ T = Set.univ)
  (hdisj : Disjoint S T)
  (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
  (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
  (hP : P.IsConnected (fun c : S ↦ facets c.1))
  (hQ : Q.IsConnected (fun c : T ↦ facets c.1))
  (x : P.Boundary) (y : Q.Boundary) (c : Fin r)

/-- The disjoint coloured union before inserting the bridge. -/
abbrev cutMatching : ColoredMatching (CellDart Cell facets) r :=
  reassembleColored S T hdisj P Q

/-- The selected free dart of the left component, included ambiently. -/
abbrev leftBoundary : (cutMatching S T hdisj P Q).Boundary :=
  includeLeftBoundary S T hdisj P Q x

/-- The selected free dart of the right component, included ambiently. -/
abbrev rightBoundary : (cutMatching S T hdisj P Q).Boundary :=
  includeRightBoundary S T hdisj P Q y

theorem boundary_ne :
    (leftBoundary S T hdisj P Q x).1 ≠
      (rightBoundary S T hdisj P Q y).1 := by
  intro heq
  have hcell : x.1.1.1 = y.1.1.1 := by
    exact congrArg Sigma.fst heq
  exact Set.disjoint_left.mp hdisj x.1.1.2 (hcell ▸ y.1.1.2)

/-- The ambient pairing obtained by inserting the cross-component seam. -/
abbrev joined : ColoredMatching (CellDart Cell facets) r :=
  (cutMatching S T hdisj P Q).join
    (leftBoundary S T hdisj P Q x)
    (rightBoundary S T hdisj P Q y)
    (boundary_ne S T hdisj P Q x y) c

/-- The inserted seam, marked in the joined matching. -/
abbrev bridgeSeam : (joined S T hdisj P Q x y c).Seam :=
  (cutMatching S T hdisj P Q).matching.newSeam
    (leftBoundary S T hdisj P Q x)
    (rightBoundary S T hdisj P Q y)
    (boundary_ne S T hdisj P Q x y)

/-- An ambient adjacency of the cut matching whose endpoints lie on the
left side induces a left-component adjacency. -/
theorem left_adjacent_of_cut_adjacent
    {u v : Cell} (hu : u ∈ S) (hv : v ∈ S)
    (hadj : (cutMatching S T hdisj P Q).Adjacent facets u v) :
    P.Adjacent (fun z : S ↦ facets z.1) ⟨u, hu⟩ ⟨v, hv⟩ := by
  have hr :=
    (cutMatching S T hdisj P Q).adjacent_restrict_iff S
      ⟨u, hu⟩ ⟨v, hv⟩
  rw [ColoredMatching.restrict_reassembleColored_left S T hdisj P Q] at hr
  exact hr.mpr hadj

/-- Right-side analogue of `left_adjacent_of_cut_adjacent`. -/
theorem right_adjacent_of_cut_adjacent
    {u v : Cell} (hu : u ∈ T) (hv : v ∈ T)
    (hadj : (cutMatching S T hdisj P Q).Adjacent facets u v) :
    Q.Adjacent (fun z : T ↦ facets z.1) ⟨u, hu⟩ ⟨v, hv⟩ := by
  have hr :=
    (cutMatching S T hdisj P Q).adjacent_restrict_iff T
      ⟨u, hu⟩ ⟨v, hv⟩
  rw [ColoredMatching.restrict_reassembleColored_right S T hdisj P Q] at hr
  exact hr.mpr hadj

/-- Every left-component adjacency is an adjacency of the joined ambient
matching. -/
theorem joined_adjacent_of_left_adjacent
    {u v : S}
    (hadj : P.Adjacent (fun z : S ↦ facets z.1) u v) :
    (joined S T hdisj P Q x y c).Adjacent facets u.1 v.1 := by
  have hcut : (cutMatching S T hdisj P Q).Adjacent facets u.1 v.1 := by
    have hr :=
      (cutMatching S T hdisj P Q).adjacent_restrict_iff S u v
    rw [ColoredMatching.restrict_reassembleColored_left S T hdisj P Q] at hr
    exact hr.mp hadj
  obtain ⟨i, j, hij⟩ := hcut
  exact ⟨i, j, Finset.mem_insert_of_mem hij⟩

/-- Every right-component adjacency is an adjacency of the joined ambient
matching. -/
theorem joined_adjacent_of_right_adjacent
    {u v : T}
    (hadj : Q.Adjacent (fun z : T ↦ facets z.1) u v) :
    (joined S T hdisj P Q x y c).Adjacent facets u.1 v.1 := by
  have hcut : (cutMatching S T hdisj P Q).Adjacent facets u.1 v.1 := by
    have hr :=
      (cutMatching S T hdisj P Q).adjacent_restrict_iff T u v
    rw [ColoredMatching.restrict_reassembleColored_right S T hdisj P Q] at hr
    exact hr.mp hadj
  obtain ⟨i, j, hij⟩ := hcut
  exact ⟨i, j, Finset.mem_insert_of_mem hij⟩

/-- Lift a path inside the left component to the joined ambient graph. -/
theorem joined_path_left (hP : P.IsConnected (fun c : S ↦ facets c.1))
    (u v : S) :
    Relation.ReflTransGen
      ((joined S T hdisj P Q x y c).Adjacent facets) u.1 v.1 :=
  (hP u v).lift (fun z : S ↦ z.1)
    (fun _ _ hadj ↦
      joined_adjacent_of_left_adjacent S T hdisj P Q x y c hadj)

/-- Lift a path inside the right component to the joined ambient graph. -/
theorem joined_path_right (hQ : Q.IsConnected (fun c : T ↦ facets c.1))
    (u v : T) :
    Relation.ReflTransGen
      ((joined S T hdisj P Q x y c).Adjacent facets) u.1 v.1 :=
  (hQ u v).lift (fun z : T ↦ z.1)
    (fun _ _ hadj ↦
      joined_adjacent_of_right_adjacent S T hdisj P Q x y c hadj)

/-- The inserted seam supplies the cross-side adjacency. -/
theorem joined_cross_adjacent :
    (joined S T hdisj P Q x y c).Adjacent facets x.1.1.1 y.1.1.1 := by
  refine ⟨x.1.2, y.1.2, ?_⟩
  exact Finset.mem_insert_self
    ((cutMatching S T hdisj P Q).matching.joinPair
      (leftBoundary S T hdisj P Q x)
      (rightBoundary S T hdisj P Q y))
    (cutMatching S T hdisj P Q).matching.seams

/-- Joining one free dart from each connected component makes the ambient
dual graph connected. -/
theorem joined_connected (hcover : S ∪ T = Set.univ)
    (hP : P.IsConnected (fun c : S ↦ facets c.1))
    (hQ : Q.IsConnected (fun c : T ↦ facets c.1)) :
    (joined S T hdisj P Q x y c).IsConnected facets := by
  intro u v
  have side (z : Cell) : z ∈ S ∨ z ∈ T := by
    have hz : z ∈ S ∪ T := by rw [hcover]; exact Set.mem_univ z
    simpa only [Set.mem_union] using hz
  rcases side u with huS | huT
  · rcases side v with hvS | hvT
    · exact joined_path_left S T hdisj P Q x y c hP
        ⟨u, huS⟩ ⟨v, hvS⟩
    · exact (joined_path_left S T hdisj P Q x y c hP
          ⟨u, huS⟩ ⟨x.1.1.1, x.1.1.2⟩).trans <|
        (Relation.ReflTransGen.single
          (joined_cross_adjacent S T hdisj P Q x y c)).trans <|
        joined_path_right S T hdisj P Q x y c hQ
          ⟨y.1.1.1, y.1.1.2⟩ ⟨v, hvT⟩
  · rcases side v with hvS | hvT
    · exact (joined_path_right S T hdisj P Q x y c hQ
          ⟨u, huT⟩ ⟨y.1.1.1, y.1.1.2⟩).trans <|
        (Relation.ReflTransGen.single
          ((joined S T hdisj P Q x y c).adjacent_symm facets
            (joined_cross_adjacent S T hdisj P Q x y c))).trans <|
        joined_path_left S T hdisj P Q x y c hP
          ⟨x.1.1.1, x.1.1.2⟩ ⟨v, hvS⟩
    · exact joined_path_right S T hdisj P Q x y c hQ
        ⟨u, huT⟩ ⟨v, hvT⟩

/-- Erasing the inserted coloured seam recovers the exact cut matching. -/
theorem erase_bridgeSeam :
    (joined S T hdisj P Q x y c).erase
      (bridgeSeam S T hdisj P Q x y c) = cutMatching S T hdisj P Q := by
  exact ColoredMatching.erase_join_newSeam
    (cutMatching S T hdisj P Q)
    (leftBoundary S T hdisj P Q x)
    (rightBoundary S T hdisj P Q y)
    (boundary_ne S T hdisj P Q x y) c

/-- If the unjoined reassembly is disconnected, the inserted seam is a
genuine bridge. -/
theorem bridgeSeam_isBridge
    (hcut : ¬(cutMatching S T hdisj P Q).IsConnected facets) :
    (joined S T hdisj P Q x y c).IsBridge
      (bridgeSeam S T hdisj P Q x y c) := by
  intro hconn
  rw [erase_bridgeSeam S T hdisj P Q x y c] at hconn
  exact hcut hconn

/-- The inserted bridge increases the seam count by exactly one. -/
theorem card_seams_joined :
    (joined S T hdisj P Q x y c).matching.seams.card =
      (cutMatching S T hdisj P Q).matching.seams.card + 1 := by
  exact PartialMatching.card_seams_join
    (cutMatching S T hdisj P Q).matching
    (leftBoundary S T hdisj P Q x)
    (rightBoundary S T hdisj P Q y)
    (boundary_ne S T hdisj P Q x y)


end JoinComponentsBridge
end
end FacetPairing
end PolytopeCounting
