module

public import Proofs.FacetPairingModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-!
# Deleting one edge: the bridge partition

The central theorem in this file is independent of finite cardinality.  Let
`old` be a symmetric adjacency relation and add one undirected edge `a--b`.
If the enlarged relation is connected while `old` is not, then the old graph
has exactly two reachability classes: the class of `a` and the class of `b`.

This is the precise relation-theoretic statement used after erasing a marked
seam.  It handles loops and parallel edges correctly.  In particular, if an
old path already joins `a` to `b` (which happens for a parallel edge), erasing
the marked edge cannot disconnect the graph.
-/

namespace PolytopeCounting
namespace BridgePartition

universe u

variable {V : Type u}

/-- Add one undirected edge with endpoints `a` and `b` to `old`. -/
def AddEdge (old : V → V → Prop) (a b : V) (x y : V) : Prop :=
  old x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)

theorem addEdge_symm {old : V → V → Prop} (hold : Symmetric old)
    (a b : V) : Symmetric (AddEdge old a b) := by
  intro x y hxy
  rcases hxy with hxy | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (hold hxy)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- Reachability for a symmetric relation is symmetric.  We prove this
directly so the deletion proof does not depend on any graph wrapper. -/
theorem rtc_symm {old : V → V → Prop} (hold : Symmetric old)
    {x y : V} (hxy : Relation.ReflTransGen old x y) :
    Relation.ReflTransGen old y x := by
  induction hxy with
  | refl => exact .refl
  | tail hpath hstep ih =>
      exact (Relation.ReflTransGen.single (hold hstep)).trans ih

/-- Old paths remain paths after the extra edge is added. -/
theorem rtc_mono_addEdge {old : V → V → Prop} {a b x y : V}
    (hxy : Relation.ReflTransGen old x y) :
    Relation.ReflTransGen (AddEdge old a b) x y :=
  Relation.ReflTransGen.mono (fun _ _ h ↦ Or.inl h) _ _ hxy

/-- If an old path joins the two endpoints, every path using the added edge
can be rewritten as an old path. -/
theorem collapse_added_edge {old : V → V → Prop}
    (hold : Symmetric old) {a b x y : V}
    (hab : Relation.ReflTransGen old a b)
    (hxy : Relation.ReflTransGen (AddEdge old a b) x y) :
    Relation.ReflTransGen old x y := by
  induction hxy with
  | refl => exact .refl
  | @tail u v hpath hstep ih =>
      rcases hstep with hOld | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih.tail hOld
      · exact ih.trans hab
      · exact ih.trans (rtc_symm hold hab)

/-- Along a path in the graph with the extra edge, every vertex reached from
`a` belongs to the old class of `a` or to the old class of `b`. -/
theorem endpoint_class_cover_of_path {old : V → V → Prop}
    {a b x : V} (hax : Relation.ReflTransGen (AddEdge old a b) a x) :
    Relation.ReflTransGen old a x ∨ Relation.ReflTransGen old b x := by
  induction hax with
  | refl => exact Or.inl .refl
  | @tail u v hpath hstep ih =>
      rcases hstep with hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih.elim
          (fun hau ↦ Or.inl (hau.tail hold))
          (fun hbu ↦ Or.inr (hbu.tail hold))
      · exact Or.inr .refl
      · exact Or.inl .refl

/-- Connectedness is written explicitly as universal reachability. -/
def Connected (r : V → V → Prop) : Prop :=
  ∀ x y : V, Relation.ReflTransGen r x y

/-- An edge is a bridge relative to `old` when adding it gives a connected
graph but deleting it (returning to `old`) does not. -/
def IsBridge (old : V → V → Prop) (a b : V) : Prop :=
  Connected (AddEdge old a b) ∧ ¬Connected old

/-- If deleting the edge disconnects the connected enlarged graph, its
endpoints cannot still be joined by an old path. -/
theorem endpoints_not_reachable {old : V → V → Prop}
    (hold : Symmetric old) {a b : V} (hbridge : IsBridge old a b) :
    ¬ Relation.ReflTransGen old a b := by
  intro hab
  apply hbridge.2
  intro x y
  exact collapse_added_edge hold hab (hbridge.1 x y)

/-- Reachability classes determined by the exposed endpoints. -/
def LeftClass (old : V → V → Prop) (a : V) : Set V :=
  {x | Relation.ReflTransGen old a x}

def RightClass (old : V → V → Prop) (b : V) : Set V :=
  {x | Relation.ReflTransGen old b x}

@[simp] theorem mem_leftClass {old : V → V → Prop} {a x : V} :
    x ∈ LeftClass old a ↔ Relation.ReflTransGen old a x := Iff.rfl

@[simp] theorem mem_rightClass {old : V → V → Prop} {b x : V} :
    x ∈ RightClass old b ↔ Relation.ReflTransGen old b x := Iff.rfl

/-- Every vertex lies in one of the two endpoint classes. -/
theorem classes_cover {old : V → V → Prop} {a b : V}
    (hconnected : Connected (AddEdge old a b)) :
    LeftClass old a ∪ RightClass old b = Set.univ := by
  ext x
  simp only [Set.mem_union, mem_leftClass, mem_rightClass, Set.mem_univ,
    iff_true]
  exact endpoint_class_cover_of_path (hconnected a x)

/-- Under the bridge hypothesis, the endpoint classes are disjoint. -/
theorem classes_disjoint {old : V → V → Prop}
    (hold : Symmetric old) {a b : V} (hbridge : IsBridge old a b) :
    Disjoint (LeftClass old a) (RightClass old b) := by
  rw [Set.disjoint_left]
  intro x hax hbx
  exact endpoints_not_reachable hold hbridge
    (hax.trans (rtc_symm hold hbx))

/-- No old edge crosses from the left class to the right class. -/
theorem no_edge_left_right {old : V → V → Prop}
    (hold : Symmetric old) {a b : V} (hbridge : IsBridge old a b)
    {x y : V} (hx : x ∈ LeftClass old a)
    (hy : y ∈ RightClass old b) : ¬ old x y := by
  intro hxy
  apply endpoints_not_reachable hold hbridge
  exact (hx.tail hxy).trans (rtc_symm hold hy)

/-- There is likewise no old edge in the reverse direction. -/
theorem no_edge_right_left {old : V → V → Prop}
    (hold : Symmetric old) {a b : V} (hbridge : IsBridge old a b)
    {x y : V} (hx : x ∈ RightClass old b)
    (hy : y ∈ LeftClass old a) : ¬ old x y := by
  intro hxy
  exact no_edge_left_right hold hbridge hy hx (hold hxy)

/-- Any two vertices in the left class are joined by an old ambient path. -/
theorem left_class_ambient_connected {old : V → V → Prop}
    (hold : Symmetric old) {a x y : V}
    (hx : x ∈ LeftClass old a) (hy : y ∈ LeftClass old a) :
    Relation.ReflTransGen old x y :=
  (rtc_symm hold hx).trans hy

/-- Any two vertices in the right class are joined by an old ambient path. -/
theorem right_class_ambient_connected {old : V → V → Prop}
    (hold : Symmetric old) {b x y : V}
    (hx : x ∈ RightClass old b) (hy : y ∈ RightClass old b) :
    Relation.ReflTransGen old x y :=
  (rtc_symm hold hx).trans hy

/-- Lift an ambient path to the reachability class of its initial vertex. -/
theorem lift_path_to_class {old : V → V → Prop} {a x y : V}
    (hax : Relation.ReflTransGen old a x)
    (hxy : Relation.ReflTransGen old x y) :
    Relation.ReflTransGen
      (fun u v : LeftClass old a ↦ old u.1 v.1)
      ⟨x, hax⟩ ⟨y, hax.trans hxy⟩ := by
  induction hxy with
  | refl => exact .refl
  | tail hpath hstep ih => exact ih.tail hstep

/-- The relation induced on the left class is connected. -/
theorem left_induced_connected {old : V → V → Prop}
    (hold : Symmetric old) {a : V} :
    ∀ x y : LeftClass old a,
      Relation.ReflTransGen
        (fun u v : LeftClass old a ↦ old u.1 v.1) x y := by
  intro x y
  have hxy : Relation.ReflTransGen old x.1 y.1 :=
    left_class_ambient_connected hold x.2 y.2
  have hp := lift_path_to_class x.2 hxy
  exact hp

/-- The relation induced on the right class is connected. -/
theorem right_induced_connected {old : V → V → Prop}
    (hold : Symmetric old) {b : V} :
    ∀ x y : RightClass old b,
      Relation.ReflTransGen
        (fun u v : RightClass old b ↦ old u.1 v.1) x y := by
  intro x y
  have hxy : Relation.ReflTransGen old x.1 y.1 :=
    right_class_ambient_connected hold x.2 y.2
  have hp := lift_path_to_class x.2 hxy
  exact hp

/-- Complete deletion certificate: exactly two disjoint, covering,
edge-separated, internally connected reachability classes. -/
structure Certificate (old : V → V → Prop) (a b : V) : Prop where
  cover : LeftClass old a ∪ RightClass old b = Set.univ
  disjoint : Disjoint (LeftClass old a) (RightClass old b)
  no_left_right : ∀ x : LeftClass old a, ∀ y : RightClass old b,
    ¬ old x.1 y.1
  left_connected : ∀ x y : LeftClass old a,
    Relation.ReflTransGen old x.1 y.1
  right_connected : ∀ x y : RightClass old b,
    Relation.ReflTransGen old x.1 y.1
  left_induced_connected : ∀ x y : LeftClass old a,
    Relation.ReflTransGen
      (fun u v : LeftClass old a ↦ old u.1 v.1) x y
  right_induced_connected : ∀ x y : RightClass old b,
    Relation.ReflTransGen
      (fun u v : RightClass old b ↦ old u.1 v.1) x y

theorem bridge_certificate {old : V → V → Prop}
    (hold : Symmetric old) {a b : V} (hbridge : IsBridge old a b) :
    Certificate old a b where
  cover := classes_cover hbridge.1
  disjoint := classes_disjoint hold hbridge
  no_left_right := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    exact no_edge_left_right hold hbridge hx hy
  left_connected := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    exact left_class_ambient_connected hold hx hy
  right_connected := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    exact right_class_ambient_connected hold hx hy
  left_induced_connected := left_induced_connected hold
  right_induced_connected := right_induced_connected hold

/-- The disjoint union of the two certified classes is equivalent to the
whole vertex type.  This is the set-theoretic content behind the component
size identity, without importing cardinal arithmetic for arbitrary sets. -/
noncomputable def classSumEquiv {old : V → V → Prop} {a b : V}
    (C : Certificate old a b) :
    LeftClass old a ⊕ RightClass old b ≃ V :=
  by
    classical
    exact (Equiv.Set.union C.disjoint).symm.trans
      ((Set.equivOfEq C.cover).trans (Equiv.Set.univ V))

/-- For a finite vertex type, the two component sizes add to the total
number of vertices. -/
theorem class_sizes_add [Fintype V] {old : V → V → Prop} {a b : V}
    (C : Certificate old a b) :
    letI := Classical.decPred (fun x ↦ x ∈ LeftClass old a)
    letI := Classical.decPred (fun x ↦ x ∈ RightClass old b)
    Fintype.card (LeftClass old a) + Fintype.card (RightClass old b) =
      Fintype.card V := by
  classical
  simpa only [Fintype.card_sum] using Fintype.card_congr (classSumEquiv C)

/-- Both classes produced by a bridge are nonempty: they contain their
respective exposed endpoints. -/
theorem left_class_size_pos [Fintype V] {old : V → V → Prop} {a : V} :
    letI := Classical.decPred (fun x ↦ x ∈ LeftClass old a)
    0 < Fintype.card (LeftClass old a) := by
  classical
  exact Fintype.card_pos_iff.mpr ⟨⟨a, Relation.ReflTransGen.refl⟩⟩

theorem right_class_size_pos [Fintype V] {old : V → V → Prop} {b : V} :
    letI := Classical.decPred (fun x ↦ x ∈ RightClass old b)
    0 < Fintype.card (RightClass old b) := by
  classical
  exact Fintype.card_pos_iff.mpr ⟨⟨b, Relation.ReflTransGen.refl⟩⟩

/-- Circuit ranks add across a bridge.  This is the subtraction-free
arithmetic form used after the two restricted components have been built. -/
theorem circuitRanks_add
    {vertices edges rank vertices₁ edges₁ rank₁ vertices₂ edges₂ rank₂ : ℕ}
    (hVertices : vertices₁ + vertices₂ = vertices)
    (hEdges : edges₁ + edges₂ + 1 = edges)
    (hRank : edges + 1 = vertices + rank)
    (hRank₁ : edges₁ + 1 = vertices₁ + rank₁)
    (hRank₂ : edges₂ + 1 = vertices₂ + rank₂) :
    rank₁ + rank₂ = rank := by
  omega

/-- The two alternatives used by cut--join: deleting the marked edge leaves
the graph connected, or it produces the certified two-class partition. -/
theorem connected_or_bridge_certificate {old : V → V → Prop}
    (hold : Symmetric old) {a b : V}
    (hconnected : Connected (AddEdge old a b)) :
    Connected old ∨ Certificate old a b := by
  by_cases h : Connected old
  · exact Or.inl h
  · exact Or.inr (bridge_certificate hold ⟨hconnected, h⟩)

end BridgePartition
end PolytopeCounting
