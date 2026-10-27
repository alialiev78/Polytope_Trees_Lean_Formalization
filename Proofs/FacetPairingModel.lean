module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Sym.Sym2
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Unrestricted coloured facet-pairing diagrams

This file gives a concrete finite model for the unrestricted objects used in
the cut--join argument.  A seam is an unordered pair (`Sym2`) of darts.  A
partial matching is a finite set of off-diagonal, pairwise dart-disjoint
seams.  No geometric-realizability, embedding, or manifold condition is built
into this model.

The definitions deliberately include loops and parallel dual edges: the two
darts in a seam must be distinct, but they may belong to the same cell, and
different seams may connect the same pair of cells.
-/

open scoped BigOperators

namespace PolytopeCounting
namespace FacetPairing

universe uD uC

/-! ## Darts and cell types -/

/-- A dart is a cell together with one of its facet slots. -/
abbrev CellDart (Cell : Type uC) (facets : Cell → ℕ) :=
  Σ c : Cell, Fin (facets c)

/-- Cells of an unrooted diagram. -/
abbrev UnrootedCell (n : ℕ) := Fin n

/-- Darts of `n` ordinary cells, each having `h` facets. -/
abbrev Dart (n h : ℕ) := CellDart (UnrootedCell n) (fun _ ↦ h)

/-- A rooted diagram has one distinguished base cell and `n` ordinary cells. -/
abbrev RootedCell (n : ℕ) := Sum Unit (Fin n)

/-- The distinguished base cell. -/
def baseCell (n : ℕ) : RootedCell n := Sum.inl ()

/-- Number of facets on each cell in a rooted diagram. -/
def rootedFacets (h₀ h : ℕ) : RootedCell n → ℕ
  | Sum.inl _ => h₀
  | Sum.inr _ => h

/-- Darts of one `h₀`-faceted base cell and `n` `h`-faceted ordinary cells. -/
abbrev RootedDart (n h₀ h : ℕ) := CellDart (RootedCell n) (rootedFacets h₀ h)

@[simp] theorem card_unrootedCell (n : ℕ) :
    Fintype.card (UnrootedCell n) = n := by
  simp

@[simp] theorem card_rootedCell (n : ℕ) :
    Fintype.card (RootedCell n) = n + 1 := by
  simp [RootedCell, Nat.add_comm]

@[simp] theorem card_dart (n h : ℕ) :
    Fintype.card (Dart n h) = n * h := by
  simp [Dart, CellDart]

@[simp] theorem card_rootedDart (n h₀ h : ℕ) :
    Fintype.card (RootedDart n h₀ h) = h₀ + n * h := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  simp [RootedCell, rootedFacets]

/-! ## Partial matchings -/

/-- A finite partial matching on `D`.

`unique_incidence` says that a dart lies in at most one seam.  It is stated
directly in terms of membership in an unordered pair; this form is convenient
for cut and join proofs. -/
structure PartialMatching (D : Type uD) [DecidableEq D] where
  seams : Finset (Sym2 D)
  offDiagonal : ∀ e ∈ seams, ¬e.IsDiag
  unique_incidence :
    ∀ d e, e ∈ seams → d ∈ e →
      ∀ f, f ∈ seams → d ∈ f → e = f

namespace PartialMatching

variable {D : Type uD} [DecidableEq D]

@[ext]
theorem ext {M N : PartialMatching D} (h : M.seams = N.seams) : M = N := by
  cases M
  cases N
  simp_all

/-- The matching type is finite whenever the dart type is finite. -/
instance instFinite [Fintype D] : Finite (PartialMatching D) :=
  Finite.of_injective PartialMatching.seams fun _ _ h ↦ PartialMatching.ext h

/-- A concrete `Fintype` instance, used by the later cardinality files. -/
noncomputable instance instFintype [Fintype D] : Fintype (PartialMatching D) :=
  Fintype.ofFinite (PartialMatching D)

/-- The finite type of seams of a matching. -/
abbrev Seam (M : PartialMatching D) := {e : Sym2 D // e ∈ M.seams}

/-- Darts used by at least one seam. -/
def occupied (M : PartialMatching D) : Finset D :=
  M.seams.biUnion Sym2.toFinset

@[simp]
theorem mem_occupied_iff (M : PartialMatching D) (d : D) :
    d ∈ M.occupied ↔ ∃ e ∈ M.seams, d ∈ e := by
  simp [occupied]

/-- Pairwise disjointness of the two-element seam supports. -/
theorem pairwiseDisjoint_toFinset (M : PartialMatching D) :
    (M.seams : Set (Sym2 D)).PairwiseDisjoint Sym2.toFinset := by
  intro e he f hf hne
  change Disjoint e.toFinset f.toFinset
  rw [Finset.disjoint_left]
  intro d hde hdf
  have hed : d ∈ e := Sym2.mem_toFinset.mp hde
  have hfd : d ∈ f := Sym2.mem_toFinset.mp hdf
  exact hne (M.unique_incidence d e he hed f hf hfd)

/-- Every seam contributes exactly two occupied darts. -/
theorem card_occupied (M : PartialMatching D) :
    M.occupied.card = 2 * M.seams.card := by
  rw [occupied, Finset.card_biUnion M.pairwiseDisjoint_toFinset]
  calc
    ∑ e ∈ M.seams, e.toFinset.card = ∑ _e ∈ M.seams, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      exact Sym2.card_toFinset_of_not_isDiag e (M.offDiagonal e he)
    _ = 2 * M.seams.card := by simp [Nat.mul_comm]

/-- The unused darts, represented as a finset when `D` is finite. -/
def boundaryFinset [Fintype D] (M : PartialMatching D) : Finset D :=
  Finset.univ \ M.occupied

/-- The boundary type of a matching.  This predicate definition also makes
sense before a `Fintype D` instance is chosen. -/
abbrev Boundary (M : PartialMatching D) := {d : D // d ∉ M.occupied}

@[simp]
theorem mem_boundaryFinset_iff [Fintype D] (M : PartialMatching D) (d : D) :
    d ∈ M.boundaryFinset ↔ d ∉ M.occupied := by
  simp [boundaryFinset]

theorem occupied_subset_univ [Fintype D] (M : PartialMatching D) :
    M.occupied ⊆ (Finset.univ : Finset D) := by
  intro d _
  simp

/-- The balance equation `boundary + 2 * seams = all darts`. -/
theorem card_boundary_add_twice_seams [Fintype D] (M : PartialMatching D) :
    Fintype.card M.Boundary + 2 * M.seams.card = Fintype.card D := by
  rw [Fintype.card_subtype]
  change (Finset.univ.filter fun d ↦ d ∉ M.occupied).card +
    2 * M.seams.card = Fintype.card D
  rw [show Finset.univ.filter (fun d ↦ d ∉ M.occupied) =
      M.boundaryFinset by ext d; simp [boundaryFinset]]
  rw [boundaryFinset, Finset.card_sdiff, Finset.inter_univ]
  rw [M.card_occupied]
  simpa using Nat.sub_add_cancel (by
    rw [← M.card_occupied]
    simpa using Finset.card_le_card M.occupied_subset_univ)

/-- A dart in the boundary is in no old seam. -/
theorem boundary_not_mem_seam (M : PartialMatching D) (x : M.Boundary)
    {e : Sym2 D} (he : e ∈ M.seams) : x.1 ∉ e := by
  intro hxe
  have hxocc : x.1 ∈ M.occupied := (M.mem_occupied_iff x.1).2 ⟨e, he, hxe⟩
  exact x.2 hxocc

/-! ### Erasing one seam -/

/-- Erase a distinguished seam. -/
def erase (M : PartialMatching D) (e : M.Seam) : PartialMatching D where
  seams := M.seams.erase e.1
  offDiagonal f hf := M.offDiagonal f (Finset.mem_of_mem_erase hf)
  unique_incidence d f hf hdf g hg hdg :=
    M.unique_incidence d f (Finset.mem_of_mem_erase hf) hdf
      g (Finset.mem_of_mem_erase hg) hdg

@[simp]
theorem seams_erase (M : PartialMatching D) (e : M.Seam) :
    (M.erase e).seams = M.seams.erase e.1 := rfl

@[simp]
theorem card_seams_erase (M : PartialMatching D) (e : M.Seam) :
    (M.erase e).seams.card + 1 = M.seams.card := by
  simpa [erase] using Finset.card_erase_add_one e.2

/-- Either endpoint of an erased seam becomes a boundary dart. -/
def endpointBoundaryAfterErase (M : PartialMatching D) (e : M.Seam)
    (d : D) (hd : d ∈ e.1) : (M.erase e).Boundary := by
  refine ⟨d, ?_⟩
  intro hocc
  obtain ⟨f, hf, hdf⟩ := ((M.erase e).mem_occupied_iff d).1 hocc
  have hfOld : f ∈ M.seams := Finset.mem_of_mem_erase hf
  have hef : e.1 = f := M.unique_incidence d e.1 e.2 hd f hfOld hdf
  have hne : f ≠ e.1 := (Finset.mem_erase.mp hf).1
  exact hne hef.symm

/-- First endpoint exposed by erasing a seam. -/
noncomputable def leftBoundaryAfterErase (M : PartialMatching D) (e : M.Seam) :
    (M.erase e).Boundary :=
  M.endpointBoundaryAfterErase e e.1.out.1 (Sym2.out_fst_mem e.1)

/-- Second endpoint exposed by erasing a seam. -/
noncomputable def rightBoundaryAfterErase (M : PartialMatching D) (e : M.Seam) :
    (M.erase e).Boundary :=
  M.endpointBoundaryAfterErase e e.1.out.2 (Sym2.out_snd_mem e.1)

theorem exposed_endpoints_ne (M : PartialMatching D) (e : M.Seam) :
    (M.leftBoundaryAfterErase e).1 ≠ (M.rightBoundaryAfterErase e).1 := by
  have hrepr : s(e.1.out.1, e.1.out.2) = e.1 := by
    rw [Sym2.mk, e.1.out_eq]
  intro hout
  apply M.offDiagonal e.1 e.2
  rw [← hrepr, Sym2.mk_isDiag_iff]
  exact hout

/-! ### Joining two boundary darts -/

/-- The unordered seam determined by two boundary darts. -/
def joinPair (M : PartialMatching D) (x y : M.Boundary) : Sym2 D :=
  s(x.1, y.1)

theorem joinPair_not_mem (M : PartialMatching D) (x y : M.Boundary) :
    M.joinPair x y ∉ M.seams := by
  intro hmem
  exact M.boundary_not_mem_seam x hmem (by
    simp [joinPair])

theorem joinPair_disjoint_old (M : PartialMatching D) (x y : M.Boundary)
    {e : Sym2 D} (he : e ∈ M.seams) :
    Disjoint (M.joinPair x y).toFinset e.toFinset := by
  rw [Finset.disjoint_left]
  intro d hdnew hdold
  have hdnew' : d = x.1 ∨ d = y.1 := by
    simpa [joinPair] using (Sym2.mem_toFinset.mp hdnew)
  have hdold' : d ∈ e := Sym2.mem_toFinset.mp hdold
  rcases hdnew' with rfl | rfl
  · exact M.boundary_not_mem_seam x he hdold'
  · exact M.boundary_not_mem_seam y he hdold'

/-- Join two distinct boundary darts by one new seam. -/
def join (M : PartialMatching D) (x y : M.Boundary) (hxy : x.1 ≠ y.1) :
    PartialMatching D where
  seams := insert (M.joinPair x y) M.seams
  offDiagonal e he := by
    rcases Finset.mem_insert.mp he with rfl | heOld
    · simpa [joinPair, Sym2.mk_isDiag_iff] using hxy
    · exact M.offDiagonal e heOld
  unique_incidence d e he hde f hf hdf := by
    rcases Finset.mem_insert.mp he with rfl | heOld
    · rcases Finset.mem_insert.mp hf with rfl | hfOld
      · rfl
      · exact False.elim ((Finset.disjoint_left.mp
          (M.joinPair_disjoint_old x y hfOld))
            (Sym2.mem_toFinset.mpr hde) (Sym2.mem_toFinset.mpr hdf))
    · rcases Finset.mem_insert.mp hf with rfl | hfOld
      · exact False.elim ((Finset.disjoint_left.mp
          (M.joinPair_disjoint_old x y heOld).symm)
            (Sym2.mem_toFinset.mpr hde) (Sym2.mem_toFinset.mpr hdf))
      · exact M.unique_incidence d e heOld hde f hfOld hdf

@[simp]
theorem seams_join (M : PartialMatching D) (x y : M.Boundary)
    (hxy : x.1 ≠ y.1) :
    (M.join x y hxy).seams = insert (M.joinPair x y) M.seams := rfl

@[simp]
theorem card_seams_join (M : PartialMatching D) (x y : M.Boundary)
    (hxy : x.1 ≠ y.1) :
    (M.join x y hxy).seams.card = M.seams.card + 1 := by
  simp [join, M.joinPair_not_mem x y]

/-- The newly inserted seam as a member of the joined matching. -/
def newSeam (M : PartialMatching D) (x y : M.Boundary)
    (hxy : x.1 ≠ y.1) : (M.join x y hxy).Seam :=
  ⟨M.joinPair x y, Finset.mem_insert_self ..⟩

/-- Erasing the seam just inserted by `join` recovers the old matching. -/
theorem erase_join_newSeam (M : PartialMatching D) (x y : M.Boundary)
    (hxy : x.1 ≠ y.1) :
    (M.join x y hxy).erase (M.newSeam x y hxy) = M := by
  apply PartialMatching.ext
  simp [erase, join, newSeam, M.joinPair_not_mem x y]

/-- Joining the endpoints exposed by `erase` recovers the old matching. -/
theorem join_erase_endpoints (M : PartialMatching D) (e : M.Seam) :
    (M.erase e).join (M.leftBoundaryAfterErase e)
      (M.rightBoundaryAfterErase e) (M.exposed_endpoints_ne e) = M := by
  apply PartialMatching.ext
  have hout : s(e.1.out.1, e.1.out.2) = e.1 := by
    rw [Sym2.mk, e.1.out_eq]
  simp [join, erase, joinPair, leftBoundaryAfterErase,
    rightBoundaryAfterErase, endpointBoundaryAfterErase, hout, e.2]

end PartialMatching

/-! ## Colours, boundary labels, and dual connectivity -/

/-- Each seam of a matching carries one of `r` gluing colours. -/
structure ColoredMatching (D : Type uD) [DecidableEq D] (r : ℕ) where
  matching : PartialMatching D
  color : matching.Seam → Fin r

namespace ColoredMatching

variable {D : Type uD} [DecidableEq D] {r : ℕ}

/-- Forget-proof encoding used to establish finiteness. -/
def toData (P : ColoredMatching D r) :
    Σ M : PartialMatching D, M.Seam → Fin r :=
  ⟨P.matching, P.color⟩

theorem toData_injective : Function.Injective (toData :
    ColoredMatching D r → Σ M : PartialMatching D, M.Seam → Fin r) := by
  intro P Q h
  cases P
  cases Q
  cases h
  rfl

instance instFinite [Fintype D] : Finite (ColoredMatching D r) :=
  Finite.of_injective toData toData_injective

noncomputable instance instFintype [Fintype D] : Fintype (ColoredMatching D r) :=
  Fintype.ofFinite (ColoredMatching D r)

abbrev Seam (P : ColoredMatching D r) := P.matching.Seam
abbrev Boundary (P : ColoredMatching D r) := P.matching.Boundary

def edgeCount (P : ColoredMatching D r) : ℕ := P.matching.seams.card

/-- Erase a coloured seam and restrict the old colour function. -/
def erase (P : ColoredMatching D r) (e : P.Seam) : ColoredMatching D r where
  matching := P.matching.erase e
  color f := P.color ⟨f.1, Finset.mem_of_mem_erase f.2⟩

/-- Join two boundary darts and assign the specified colour to the new seam. -/
def join (P : ColoredMatching D r) (x y : P.Boundary) (hxy : x.1 ≠ y.1)
    (c : Fin r) : ColoredMatching D r where
  matching := P.matching.join x y hxy
  color e := if he : e.1 = P.matching.joinPair x y then c
    else P.color ⟨e.1, (Finset.mem_insert.mp e.2).resolve_left he⟩

@[ext (iff := false)]
theorem ext {P Q : ColoredMatching D r}
    (hm : P.matching = Q.matching)
    (hc : ∀ e : P.matching.Seam,
      P.color e = Q.color ⟨e.1, hm ▸ e.2⟩) : P = Q := by
  cases P with
  | mk PM Pc =>
      cases Q with
      | mk QM Qc =>
          dsimp only at hm hc
          subst QM
          congr
          funext e
          exact hc e

/-- The newly joined seam carries the colour explicitly assigned to it. -/
@[simp]
theorem color_join_newSeam (P : ColoredMatching D r)
    (x y : P.Boundary) (hxy : x.1 ≠ y.1) (c : Fin r) :
    (P.join x y hxy c).color (P.matching.newSeam x y hxy) = c := by
  simp [join, PartialMatching.newSeam]

/-- Erasing a coloured seam remembers its old colour and reinserting the
same two exposed endpoints with that colour recovers the original coloured
matching. -/
theorem join_erase_endpoints (P : ColoredMatching D r) (e : P.Seam) :
    (P.erase e).join
      (P.matching.leftBoundaryAfterErase e)
      (P.matching.rightBoundaryAfterErase e)
      (P.matching.exposed_endpoints_ne e)
      (P.color e) = P := by
  refine ColoredMatching.ext ?_ ?_
  · exact P.matching.join_erase_endpoints e
  · intro f
    -- After the matching equality is substituted, the old seam is the
    -- distinguished inserted seam exactly when `f=e`; all other colours are
    -- inherited through `erase`.
    rcases eq_or_ne f.1 e.1 with hfe | hfe
    · simp [join, erase, PartialMatching.joinPair,
        PartialMatching.leftBoundaryAfterErase,
        PartialMatching.rightBoundaryAfterErase,
        PartialMatching.endpointBoundaryAfterErase, e.1.out_eq, hfe]
    · simp [join, erase, PartialMatching.joinPair,
        PartialMatching.leftBoundaryAfterErase,
        PartialMatching.rightBoundaryAfterErase,
        PartialMatching.endpointBoundaryAfterErase, e.1.out_eq, hfe]

/-- Inserting a coloured seam and then erasing that very seam recovers the
original coloured matching. -/
theorem erase_join_newSeam (P : ColoredMatching D r)
    (x y : P.Boundary) (hxy : x.1 ≠ y.1) (c : Fin r) :
    (P.join x y hxy c).erase (P.matching.newSeam x y hxy) = P := by
  refine ColoredMatching.ext ?_ ?_
  · exact P.matching.erase_join_newSeam x y hxy
  · intro e
    have hne : e.1 ≠ P.matching.joinPair x y :=
      (Finset.mem_erase.mp e.2).1
    simp [erase, join, PartialMatching.newSeam,
      hne]

/-- Two cells are adjacent when a seam joins one of their darts. -/
def Adjacent {Cell : Type uC} [DecidableEq Cell] (facets : Cell → ℕ)
    (P : ColoredMatching (CellDart Cell facets) r) (u v : Cell) : Prop :=
  ∃ i : Fin (facets u), ∃ j : Fin (facets v),
    s(⟨u, i⟩, ⟨v, j⟩) ∈ P.matching.seams

theorem adjacent_symm {Cell : Type uC} [DecidableEq Cell] (facets : Cell → ℕ)
    (P : ColoredMatching (CellDart Cell facets) r) :
    Symmetric (P.Adjacent facets) := by
  intro u v huv
  obtain ⟨i, j, hij⟩ := huv
  refine ⟨j, i, ?_⟩
  rw [Sym2.eq_swap]
  exact hij

/-- Connectivity of the dual multigraph, expressed without imposing
simplicity: loops and parallel seams are allowed. -/
def IsConnected {Cell : Type uC} [DecidableEq Cell] (facets : Cell → ℕ)
    (P : ColoredMatching (CellDart Cell facets) r) : Prop :=
  ∀ u v : Cell, Relation.ReflTransGen (P.Adjacent facets) u v

end ColoredMatching

/-- A coloured pairing with a bijective labelling of every boundary dart. -/
structure BoundaryLabelledPairing (D : Type uD) [DecidableEq D] (r m : ℕ) where
  pairing : ColoredMatching D r
  label : pairing.Boundary ≃ Fin m

namespace BoundaryLabelledPairing

variable {D : Type uD} [DecidableEq D] {r m : ℕ}

def toData (P : BoundaryLabelledPairing D r m) :
    Σ Q : ColoredMatching D r, Q.Boundary ≃ Fin m :=
  ⟨P.pairing, P.label⟩

theorem toData_injective : Function.Injective (toData :
    BoundaryLabelledPairing D r m →
      Σ Q : ColoredMatching D r, Q.Boundary ≃ Fin m) := by
  intro P Q h
  cases P
  cases Q
  cases h
  rfl

instance instFinite [Fintype D] : Finite (BoundaryLabelledPairing D r m) :=
  Finite.of_injective toData toData_injective

noncomputable instance instFintype [Fintype D] :
    Fintype (BoundaryLabelledPairing D r m) :=
  Fintype.ofFinite (BoundaryLabelledPairing D r m)

def edgeCount (P : BoundaryLabelledPairing D r m) : ℕ :=
  P.pairing.edgeCount

/-- The master dart-balance identity.  In particular, when `m = 0` the
labelling field is an equivalence between two empty types and has one value. -/
theorem boundary_balance [Fintype D] (P : BoundaryLabelledPairing D r m) :
    m + 2 * P.edgeCount = Fintype.card D := by
  have hcard : Fintype.card P.pairing.Boundary = m := by
    simpa using Fintype.card_congr P.label
  simpa [edgeCount, ColoredMatching.edgeCount, hcard] using
    P.pairing.matching.card_boundary_add_twice_seams

/-- A literal boundary labelling by `Fin 0` exists only for a closed
matching. -/
theorem boundary_isEmpty_of_zero_labels
    (P : BoundaryLabelledPairing D r 0) : IsEmpty P.pairing.Boundary :=
  Function.isEmpty P.label

/-- Conversely a closed coloured matching has its canonical, unique
labelling by `Fin 0`. -/
noncomputable def ofClosedZero
    (P : ColoredMatching D r) [IsEmpty P.Boundary] :
    BoundaryLabelledPairing D r 0 where
  pairing := P
  label := Equiv.equivOfIsEmpty P.Boundary (Fin 0)

/-- The boundary labelling of a closed object is unique.  Thus the case
`m=0` contributes one labelling and does not annihilate the count. -/
theorem zero_label_unique (P Q : BoundaryLabelledPairing D r 0)
    (hpair : P.pairing = Q.pairing) : P = Q := by
  cases P with
  | mk PP PL =>
      cases Q with
      | mk QP QL =>
          dsimp only at hpair
          subst QP
          congr
          ext x
          exact Fin.elim0 (PL x)

end BoundaryLabelledPairing

/-! ## Connected diagrams and rank strata -/

/-- A connected, boundary-labelled coloured pairing on cell darts. -/
structure ConnectedDiagram (Cell : Type uC) [DecidableEq Cell]
    (facets : Cell → ℕ) (r m : ℕ) where
  raw : BoundaryLabelledPairing (CellDart Cell facets) r m
  connected : raw.pairing.IsConnected facets

namespace ConnectedDiagram

variable {Cell : Type uC} [DecidableEq Cell]
  {facets : Cell → ℕ} {r m : ℕ}

theorem raw_injective : Function.Injective
    (ConnectedDiagram.raw : ConnectedDiagram Cell facets r m →
      BoundaryLabelledPairing (CellDart Cell facets) r m) := by
  intro P Q h
  cases P
  cases Q
  cases h
  rfl

instance instFinite [Fintype Cell] : Finite (ConnectedDiagram Cell facets r m) :=
  Finite.of_injective ConnectedDiagram.raw raw_injective

noncomputable instance instFintype [Fintype Cell] :
    Fintype (ConnectedDiagram Cell facets r m) :=
  Fintype.ofFinite (ConnectedDiagram Cell facets r m)

def edgeCount (P : ConnectedDiagram Cell facets r m) : ℕ :=
  P.raw.edgeCount

/-- The cycle-rank stratum, in subtraction-free form `e + 1 = v + b`. -/
def HasCircuitRank [Fintype Cell]
    (P : ConnectedDiagram Cell facets r m) (b : ℕ) : Prop :=
  P.edgeCount + 1 = Fintype.card Cell + b

end ConnectedDiagram

/-- Unrooted unrestricted diagrams. -/
abbrev UnrootedPairing (n h r m : ℕ) :=
  BoundaryLabelledPairing (Dart n h) r m

/-! The corresponding rooted raw pairing, before imposing connectivity. -/
abbrev RootedPairing (n h₀ h r m : ℕ) :=
  BoundaryLabelledPairing (RootedDart n h₀ h) r m

/-! Connected unrooted unrestricted diagrams. -/
abbrev UnrootedDiagram (n h r m : ℕ) :=
  ConnectedDiagram (UnrootedCell n) (fun _ ↦ h) r m

/-- Rooted unrestricted diagrams: the base cell is part of the connected
diagram but is never permuted with the ordinary cells at the type level. -/
abbrev RootedDiagram (n h₀ h r m : ℕ) :=
  ConnectedDiagram (RootedCell n) (rootedFacets h₀ h) r m

/-- Unrooted diagrams in circuit-rank stratum `b`. -/
abbrev UnrootedStratum (n h r m b : ℕ) :=
  {P : UnrootedDiagram n h r m // P.HasCircuitRank b}

/-- Rooted diagrams in circuit-rank stratum `b`. -/
abbrev RootedStratum (n h₀ h r m b : ℕ) :=
  {P : RootedDiagram n h₀ h r m // P.HasCircuitRank b}

theorem unrooted_balance (P : UnrootedDiagram n h r m) :
    m + 2 * P.edgeCount = n * h := by
  simpa [ConnectedDiagram.edgeCount] using P.raw.boundary_balance

theorem rooted_balance (P : RootedDiagram n h₀ h r m) :
    m + 2 * P.edgeCount = h₀ + n * h := by
  simpa only [ConnectedDiagram.edgeCount, ← card_rootedDart n h₀ h] using
    P.raw.boundary_balance

/-- For an unrooted rank-`b` diagram, the usual boundary formula in a form
that does not use truncated natural-number subtraction. -/
theorem unrooted_rank_balance (P : UnrootedStratum n h r m b) :
    m + 2 * (n + b) = n * h + 2 := by
  have hrank := P.2
  have hbal := unrooted_balance P.1
  simp only [ConnectedDiagram.HasCircuitRank, card_unrootedCell] at hrank
  omega

/-- Rooted rank-`b` balance.  At `b = 0` it is exactly
`m = h₀ + (h-2)n`, again expressed without subtraction. -/
theorem rooted_rank_balance (P : RootedStratum n h₀ h r m b) :
    m + 2 * (n + b) = h₀ + n * h := by
  have hrank := P.2
  have hbal := rooted_balance P.1
  simp only [ConnectedDiagram.HasCircuitRank, card_rootedCell] at hrank
  omega

end FacetPairing
end PolytopeCounting

/-- Transport a finite path along an inclusion of edge relations. -/
theorem Relation.ReflTransGen.mapRelation {α : Type*} {R S : α → α → Prop}
    {a b : α} (h : Relation.ReflTransGen R a b)
    (hrs : ∀ x y, R x y → S x y) : Relation.ReflTransGen S a b :=
  Relation.ReflTransGen.mono hrs a b h
