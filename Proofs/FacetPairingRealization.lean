module

public import Proofs.FacetPairingModel
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

/-!
# A topological realization of the existing coloured facet-pairing model

This module does not replace the finite model.  It supplies its missing
geometric input explicitly: a space for each cell, a common model facet,
continuous facet charts, and a homeomorphism for each seam colour.

The output is the topological quotient of the disjoint union of cells by
exactly the identifications prescribed by the original matching.  We prove
its universal property and connectedness from connectedness of the original
dual multigraph.  Loops, repeated dual edges, and an arbitrary distinguished
core cause no special exceptions.

No manifold, embedding, PL-homeomorphism classification, or equality between
geometric automorphism groups and the existing slot-renaming groups is asserted.
In particular, a free dart is not identified here with a topological boundary
component.  Equivariance requires compatible geometric maps; it cannot be
inferred from the cardinality of the palette alone.
-/

namespace PolytopeCounting.FacetPairing.Realization

noncomputable section
universe u v w z

variable {C : Type u} [DecidableEq C] {facets : C → ℕ} {r : ℕ}
variable (P : ColoredMatching (CellDart C facets) r)
variable (X : C → Type v) [∀ c, TopologicalSpace (X c)]
variable (F : Type w) [TopologicalSpace F]

/-- Geometric data needed to interpret the finite palette of seam colours. -/
structure Charts where
  face : (d : CellDart C facets) → F → X d.1
  continuous_face : ∀ d, Continuous (face d)
  twist : Fin r → F ≃ₜ F

variable {X F} (G : Charts (facets := facets) (r := r) X F)

/-- The disjoint union before gluing.  This retains every cell copy. -/
abbrev Points (X : C → Type v) := Sigma X

/-- A fixed representative of each unordered seam is used only to orient its
geometric gluing map.  The colour is read from the original `ColoredMatching`. -/
def seamLeft (e : P.matching.Seam) (x : F) : Points X :=
  ⟨e.1.out.1.1, G.face e.1.out.1 x⟩

def seamRight (e : P.matching.Seam) (x : F) : Points X :=
  ⟨e.1.out.2.1, G.face e.1.out.2 (G.twist (P.color e) x)⟩

/-- Only the original seams generate identifications.  Equivalence closure is
performed by `Quot`, not by inserting additional seams into the finite object. -/
def GlueRel (a b : Points X) : Prop :=
  ∃ e : P.matching.Seam, ∃ x : F,
    a = seamLeft P G e x ∧ b = seamRight P G e x

abbrev Space := Quot (GlueRel P G)

/-- Each cell maps continuously to the quotient. -/
def cell (c : C) (x : X c) : Space P G :=
  Quot.mk _ ⟨c, x⟩

theorem continuous_cell (c : C) : Continuous (cell P G c) :=
  continuous_quot_mk.comp continuous_sigmaMk

/-- The two copies of every glued point agree in the realization. -/
theorem seam_identification (e : P.matching.Seam) (x : F) :
    Quot.mk (GlueRel P G) (seamLeft P G e x) =
      Quot.mk (GlueRel P G) (seamRight P G e x) :=
  Quot.sound ⟨e, x, rfl, rfl⟩

section UniversalProperty
variable {Y : Type z} [TopologicalSpace Y]
variable (f : (c : C) → X c → Y)

/-- Compatibility is tested on the actual coloured seams, not on all pairs
of facets and not on all possible colours at once. -/
def Compatible : Prop :=
  ∀ (e : P.matching.Seam) (x : F),
    f e.1.out.1.1 (G.face e.1.out.1 x) =
      f e.1.out.2.1 (G.face e.1.out.2 (G.twist (P.color e) x))

/-- The map induced by compatible cellwise maps. -/
def descend (hf : Compatible P G f) : Space P G → Y :=
  Quot.lift (fun x : Points X ↦ f x.1 x.2) (by
    intro a b hab
    rcases hab with ⟨e, x, rfl, rfl⟩
    exact hf e x)

@[simp] theorem descend_cell (hf : Compatible P G f) (c : C) (x : X c) :
    descend P G f hf (cell P G c x) = f c x := rfl

/-- The defining quotient topology gives the continuous universal property. -/
theorem continuous_descend (hf : Compatible P G f)
    (hc : ∀ c, Continuous (f c)) : Continuous (descend P G f hf) := by
  apply continuous_quot_lift
  exact continuous_sigma hc

/-- The compatible extension is unique even among all set-theoretic maps. -/
theorem descend_unique (hf : Compatible P G f) (g : Space P G → Y)
    (hg : ∀ c x, g (cell P G c x) = f c x) :
    g = descend P G f hf := by
  funext q
  refine Quot.inductionOn q ?_
  intro p
  exact hg p.1 p.2

end UniversalProperty

/-- The realization is covered by the images of the original cells. -/
theorem cells_cover : (⋃ c, Set.range (cell P G c)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  refine Quot.inductionOn q ?_
  intro p
  exact Set.mem_iUnion.mpr ⟨p.1, p.2, rfl⟩

/-- Two cells incident to an original seam have intersecting images.
The argument permits the two cells to be equal. -/
theorem adjacent_cell_images [Nonempty F] (a b : C)
    (hab : P.Adjacent facets a b) :
    (Set.range (cell P G a) ∩ Set.range (cell P G b)).Nonempty := by
  rcases hab with ⟨i, j, hij⟩
  let e : P.matching.Seam := ⟨s(⟨a, i⟩, ⟨b, j⟩), hij⟩
  let x : F := Classical.choice inferInstance
  have ho : s(e.1.out.1, e.1.out.2) = s(⟨a, i⟩, ⟨b, j⟩) := by
    change s(e.1.out.1, e.1.out.2) = e.1
    rw [Sym2.mk, e.1.out_eq]
  have hgl := seam_identification P G e x
  have hp :
      (Set.range (cell P G e.1.out.1.1) ∩
       Set.range (cell P G e.1.out.2.1)).Nonempty := by
    refine ⟨Quot.mk _ (seamLeft P G e x), ?_, ?_⟩
    · exact ⟨G.face e.1.out.1 x, rfl⟩
    · exact ⟨G.face e.1.out.2 (G.twist (P.color e) x), hgl.symm⟩
  rcases Sym2.eq_iff.mp ho with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have ha : e.1.out.1.1 = a := congrArg Sigma.fst h₁
    have hb : e.1.out.2.1 = b := congrArg Sigma.fst h₂
    rw [ha, hb] at hp
    exact hp
  · have hb : e.1.out.1.1 = b := congrArg Sigma.fst h₁
    have ha : e.1.out.2.1 = a := congrArg Sigma.fst h₂
    rw [ha, hb, Set.inter_comm] at hp
    exact hp

/-- A direct bridge from the old dual-graph connectivity predicate to
connectedness of a genuine topological quotient.  No topology of a manifold
is inferred from this theorem. -/
theorem connectedSpace [Nonempty C] [Nonempty F]
    [∀ c, ConnectedSpace (X c)] (hP : P.IsConnected facets) :
    ConnectedSpace (Space P G) := by
  apply connectedSpace_iff_univ.mpr
  rw [← cells_cover P G]
  apply IsConnected.iUnion_of_reflTransGen
  · intro c
    exact isConnected_range (continuous_cell P G c)
  · intro a b
    exact (hP a b).mapRelation (fun u v huv ↦ adjacent_cell_images P G u v huv)

/-- In particular every old `ConnectedDiagram` has a connected realization
once connected cell charts and nonempty facet spaces have been supplied. -/
theorem connectedDiagram_realization [Nonempty C] [Nonempty F]
    [∀ c, ConnectedSpace (X c)] {m : ℕ}
    (D : ConnectedDiagram C facets r m) :
    ConnectedSpace (Space D.raw.pairing G) :=
  connectedSpace D.raw.pairing G D.connected

/-! ### Transport with compatible geometric data -/

/-- A homeomorphism of the disjoint unions descends when it takes each
generating relation to a generating relation, in both directions.  This is the
compatibility that a proposed geometric renaming action still has to satisfy. -/
def quotientHomeomorph {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B]
    (R : A → A → Prop) (S : B → B → Prop) (e : A ≃ₜ B)
    (hforward : ∀ a b, R a b → S (e a) (e b))
    (hbackward : ∀ a b, S a b → R (e.symm a) (e.symm b)) :
    Quot R ≃ₜ Quot S where
  toFun := Quot.map e hforward
  invFun := Quot.map e.symm hbackward
  left_inv q := by
    refine Quot.inductionOn q ?_
    intro a
    change Quot.mk R (e.symm (e a)) = Quot.mk R a
    rw [e.symm_apply_apply]
  right_inv q := by
    refine Quot.inductionOn q ?_
    intro a
    change Quot.mk S (e (e.symm a)) = Quot.mk S a
    rw [e.apply_symm_apply]
  continuous_toFun := continuous_quot_map hforward e.continuous
  continuous_invFun := continuous_quot_map hbackward e.symm.continuous

end
end PolytopeCounting.FacetPairing.Realization
