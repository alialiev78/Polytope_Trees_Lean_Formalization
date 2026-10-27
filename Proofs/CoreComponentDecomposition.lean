module

public import Proofs.ColoredReassembly
public import Proofs.BridgeLabelledRestriction
public import Proofs.LabelledReindexing
public import Proofs.FiniteCounting
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Separate the component containing a distinguished cell

This is a component decomposition of an arbitrary pairing, not a bridge
cut. The complement may be disconnected or empty. No distinguished seam
is required, and no new boundary darts are created.

The construction is an explicit equivalence, including seam colours and
all bijective boundary labels. Its source is a disjoint union over the
actual subsets of the ambient cell set. Reindexing those subsets by their
cardinalities and performing the `n! tau^n` cancellation is a separate step
before obtaining the numerical identity `Xi = W * Psi`.
-/

namespace PolytopeCounting.FacetPairing.CoreComponents

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators

universe uC uA

variable {Cell : Type uC} [Fintype Cell] [DecidableEq Cell]
  {facets : Cell → ℕ} {r : ℕ}

abbrev Matching := ColoredMatching (CellDart Cell facets) r

/-- The actual reachability class of the distinguished cell. -/
def rootSet (P : Matching (facets := facets) (r := r)) (a : Cell) : Set Cell :=
  BridgePartition.LeftClass (P.Adjacent facets) a

@[simp] theorem root_mem_rootSet
    (P : Matching (facets := facets) (r := r)) (a : Cell) :
    a ∈ rootSet P a := Relation.ReflTransGen.refl

theorem complement_cover (S : Set Cell) : S ∪ Sᶜ = Set.univ := by
  ext x
  simp

theorem complement_disjoint (S : Set Cell) : Disjoint S Sᶜ := by
  exact Set.disjoint_left.mpr (fun _ hx hxc ↦ hxc hx)

/-- No seam joins the root component to its complement. -/
theorem root_noCrossing
    (P : Matching (facets := facets) (r := r)) (a : Cell) :
    NoCrossing P (rootSet P a) (rootSet P a)ᶜ := by
  intro u hu v hv huv
  exact hv (hu.tail huv)

/-- Every seam is entirely in the root component or entirely in the
possibly disconnected complement. -/
theorem root_internal
    (P : Matching (facets := facets) (r := r)) (a : Cell) :
    ColoredMatching.ComponentInternal (rootSet P a) (rootSet P a)ᶜ P := by
  intro e he
  exact seam_internal_left_or_right P (rootSet P a) (rootSet P a)ᶜ
    (complement_cover _) (root_noCrossing P a) e he

/-- Restricting to the root reachability class gives a connected pairing. -/
theorem root_restriction_connected
    (P : Matching (facets := facets) (r := r)) (a : Cell) :
    (P.restrict (rootSet P a)).IsConnected
      (fun c : rootSet P a ↦ facets c.1) := by
  apply P.restrict_isConnected_of_induced
  exact BridgePartition.left_induced_connected (P.adjacent_symm facets)

/-- Uniqueness of the root component. A connected side containing the root
and having no crossing seam must be its whole reachability class. -/
theorem rootSet_eq_of_connected_partition
    (P : Matching (facets := facets) (r := r)) (a : Cell) (S : Set Cell)
    (ha : a ∈ S)
    (hconn : (P.restrict S).IsConnected (fun c : S ↦ facets c.1))
    (hint : ColoredMatching.ComponentInternal S Sᶜ P) :
    rootSet P a = S := by
  have hno := ColoredMatching.noCrossing_of_internal
    P S Sᶜ (complement_disjoint S) hint
  ext v
  constructor
  · intro hv
    change Relation.ReflTransGen (P.Adjacent facets) a v at hv
    induction hv with
    | refl => exact ha
    | @tail u v hpath hstep ih =>
        by_contra hvS
        exact hno ih hvS hstep
  · intro hv
    have hp := hconn (⟨a, ha⟩ : S) (⟨v, hv⟩ : S)
    have hq := hp.lift (fun c : S ↦ c.1)
      (fun x y hxy ↦ (P.adjacent_restrict_iff S x y).mp hxy)
    exact hq

/-- Component data over a fixed subset. Connectedness is required only on
the first side. The membership condition prevents an empty root side. -/
def ComponentPair (a : Cell) (S : Set Cell) :=
  {X : ColoredMatching (RestrictedDart (facets := facets) S) r ×
      ColoredMatching (RestrictedDart (facets := facets) Sᶜ) r //
    a ∈ S ∧ X.1.IsConnected (fun c : S ↦ facets c.1)}

/-- A disjoint union over literal ambient cell subsets; each summand is a
connected root component and an arbitrary remaining pairing. -/
abbrev Pieces (a : Cell) :=
  Σ S : Set Cell, ComponentPair (facets := facets) (r := r) a S

instance componentPairFintype (a : Cell) (S : Set Cell) :
    Fintype (ComponentPair (facets := facets) (r := r) a S) := by
  unfold ComponentPair
  exact Fintype.ofFinite _

instance piecesFintype (a : Cell) :
    Fintype (Pieces (facets := facets) (r := r) a) := Fintype.ofFinite _

/-- Assemble the two sides without adding a seam. -/
def assembleAt (a : Cell) (S : Set Cell)
    (X : ComponentPair (facets := facets) (r := r) a S) :
    Matching (facets := facets) (r := r) :=
  reassembleColored S Sᶜ (complement_disjoint S) X.1.1 X.1.2

/-- The specified root component is recovered from an assembled pair. -/
theorem rootSet_assembleAt (a : Cell) (S : Set Cell)
    (X : ComponentPair (facets := facets) (r := r) a S) :
    rootSet (assembleAt a S X) a = S := by
  apply rootSet_eq_of_connected_partition _ a S X.2.1
  · change ((reassembleColored S Sᶜ (complement_disjoint S)
        X.1.1 X.1.2).restrict S).IsConnected (fun c : S ↦ facets c.1)
    rw [ColoredMatching.restrict_reassembleColored_left]
    exact X.2.2
  · intro e he
    exact seamInternal_reassembleMatching S Sᶜ (complement_disjoint S)
      X.1.1.matching X.1.2.matching e he

/-- Fixed-subset restriction and reassembly are inverse, including all
colours. Neither side carries an arbitrarily supplied equivalence. -/
def componentPairEquiv (a : Cell) (S : Set Cell) :
    ComponentPair (facets := facets) (r := r) a S ≃
      {P : Matching (facets := facets) (r := r) // rootSet P a = S} where
  toFun X := ⟨assembleAt a S X, rootSet_assembleAt a S X⟩
  invFun P := ⟨(P.1.restrict S, P.1.restrict Sᶜ), by
    constructor
    · rw [← P.2]
      exact root_mem_rootSet P.1 a
    · have hc := root_restriction_connected P.1 a
      rw [P.2] at hc
      exact hc⟩
  left_inv X := by
    apply Subtype.ext
    apply Prod.ext
    · exact ColoredMatching.restrict_reassembleColored_left
        S Sᶜ (complement_disjoint S) X.1.1 X.1.2
    · exact ColoredMatching.restrict_reassembleColored_right
        S Sᶜ (complement_disjoint S) X.1.1 X.1.2
  right_inv P := by
    apply Subtype.ext
    apply ColoredMatching.reassembleColored_restrict
      P.1 S Sᶜ (complement_disjoint S)
    have hi := root_internal P.1 a
    rw [P.2] at hi
    exact hi

/-- Recording the already determined root component adds no information. -/
def locatedEquiv (a : Cell) :
    (Σ S : Set Cell,
      {P : Matching (facets := facets) (r := r) // rootSet P a = S}) ≃
        Matching (facets := facets) (r := r) where
  toFun X := X.2.1
  invFun P := ⟨rootSet P a, ⟨P, rfl⟩⟩
  left_inv X := by
    rcases X with ⟨S, P, hP⟩
    cases hP
    rfl
  right_inv P := rfl

/-- The actual root-component decomposition for every ambient matching. -/
def componentsEquiv (a : Cell) :
    Pieces (facets := facets) (r := r) a ≃
      Matching (facets := facets) (r := r) :=
  (Equiv.sigmaCongrRight (fun S ↦ componentPairEquiv a S)).trans
    (locatedEquiv a)

@[simp] theorem componentsEquiv_apply (a : Cell)
    (X : Pieces (facets := facets) (r := r) a) :
    componentsEquiv a X = assembleAt a X.1 X.2 := rfl

/-- Boundary darts are partitioned, not newly created, by component
separation. This is different from a cut along a bridge. -/
def componentBoundaryEquiv (a : Cell)
    (X : Pieces (facets := facets) (r := r) a) :
    (componentsEquiv a X).Boundary ≃ X.2.1.1.Boundary ⊕ X.2.1.2.Boundary :=
  boundaryReassembleEquiv X.1 X.1ᶜ (complement_cover X.1)
    (complement_disjoint X.1) X.2.1.1 X.2.1.2

theorem boundary_card_components (a : Cell)
    (X : Pieces (facets := facets) (r := r) a) :
    Fintype.card (componentsEquiv a X).Boundary =
      Fintype.card X.2.1.1.Boundary + Fintype.card X.2.1.2.Boundary := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (componentBoundaryEquiv a X)

/-- The exact same equivalence with all boundary labels retained. The
single global label map is a bijection from the sum of the two boundaries;
no freeness assumption is used, even when the boundary is empty. -/
def labelledComponentsEquiv (a : Cell) (m : ℕ) :
    (Σ X : Pieces (facets := facets) (r := r) a,
      (X.2.1.1.Boundary ⊕ X.2.1.2.Boundary) ≃ Fin m) ≃
        BoundaryLabelledPairing (CellDart Cell facets) r m :=
  (Equiv.sigmaCongr (componentsEquiv a)
    (fun X ↦ BoundaryLabelledPairing.labelTransportEquiv
      (componentBoundaryEquiv a X).symm)).trans
        BoundaryLabelledPairing.dataEquiv.symm

/-- Exact labelled cardinality consequence of the constructed equivalence. -/
theorem card_labelled_components (a : Cell) (m : ℕ) :
    Fintype.card (BoundaryLabelledPairing (CellDart Cell facets) r m) =
      ∑ X : Pieces (facets := facets) (r := r) a,
        Fintype.card ((X.2.1.1.Boundary ⊕ X.2.1.2.Boundary) ≃ Fin m) := by
  rw [← Fintype.card_congr (labelledComponentsEquiv a m)]
  exact Fintype.card_sigma

/-- A boundary weight factors across the connected root component and the
arbitrary complement. This is the finite, weighted component identity
underlying the Cauchy product, before canonical size reindexing. -/
theorem boundary_weighted_decomposition
    {A : Type uA} [CommSemiring A] (a : Cell) (z : A) :
    (∑ P : Matching (facets := facets) (r := r), z ^ Fintype.card P.Boundary) =
      ∑ X : Pieces (facets := facets) (r := r) a,
        z ^ Fintype.card X.2.1.1.Boundary *
          z ^ Fintype.card X.2.1.2.Boundary := by
  calc
    _ = ∑ X : Pieces (facets := facets) (r := r) a,
        z ^ Fintype.card (componentsEquiv a X).Boundary := by
      symm
      apply Fintype.sum_equiv (componentsEquiv a)
      intro X
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro X _
      rw [boundary_card_components, pow_add]

end
end PolytopeCounting.FacetPairing.CoreComponents
