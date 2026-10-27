module

public import Proofs.ComponentReindexing
public import Proofs.BoundaryCut

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Boundary labels across a fixed bridge partition

`BridgeRestriction` reconstructs every seam and every seam colour from the
two sides of a fixed no-crossing partition.  This file adds the dependent
boundary layer.  Its central construction is an explicit equivalence

```
  boundary (reassemble P Q)  ≃  boundary P ⊕ boundary Q.
```

Consequently boundary labels can be allocated to the two components and
reassembled without a cardinality-only argument.  The label targets below
are arbitrary finite types; specializing them to `Fin m₁` and `Fin m₂`
gives the label split used in bridge convolutions, including either empty
side.
-/

namespace PolytopeCounting
namespace FacetPairing

noncomputable section

universe uC uA uB

variable {Cell : Type uC} [Fintype Cell] [DecidableEq Cell]
  {facets : Cell → ℕ} {r : ℕ}

/-! ## The boundary of a reassembly is a disjoint sum -/

/-- Include a free dart of the left component as a free ambient dart. -/
def includeLeftBoundary
    (S T : Set Cell) (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (x : P.Boundary) :
    (reassembleColored S T hdisj P Q).Boundary := by
  refine ⟨includeDart (facets := facets) S x.1, ?_⟩
  intro hocc
  obtain ⟨e, he, hde⟩ :=
    ((reassembleColored S T hdisj P Q).matching.mem_occupied_iff _).mp hocc
  rw [show (reassembleColored S T hdisj P Q).matching.seams =
      (reassembleMatching S T hdisj P.matching Q.matching).seams from rfl,
    seams_reassembleMatching] at he
  rcases Finset.mem_union.mp he with heS | heT
  · obtain ⟨eS, heSP, rfl⟩ := Finset.mem_map.mp heS
    obtain ⟨dS, hdS, hdx⟩ := Sym2.mem_map.mp hde
    have hdEq : dS = x.1 :=
      includeDart_injective (facets := facets) S hdx
    apply x.2
    exact (P.matching.mem_occupied_iff x.1).mpr
      ⟨eS, heSP, by simpa only [hdEq] using hdS⟩
  · obtain ⟨eT, heTQ, rfl⟩ := Finset.mem_map.mp heT
    obtain ⟨dT, _hdT, hdx⟩ := Sym2.mem_map.mp hde
    have hcell : dT.1.1 = x.1.1.1 := congrArg Sigma.fst hdx
    exact Set.disjoint_left.mp hdisj x.1.1.2 (hcell ▸ dT.1.2)

/-- Include a free dart of the right component as a free ambient dart. -/
def includeRightBoundary
    (S T : Set Cell) (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (x : Q.Boundary) :
    (reassembleColored S T hdisj P Q).Boundary := by
  refine ⟨includeDart (facets := facets) T x.1, ?_⟩
  intro hocc
  obtain ⟨e, he, hde⟩ :=
    ((reassembleColored S T hdisj P Q).matching.mem_occupied_iff _).mp hocc
  rw [show (reassembleColored S T hdisj P Q).matching.seams =
      (reassembleMatching S T hdisj P.matching Q.matching).seams from rfl,
    seams_reassembleMatching] at he
  rcases Finset.mem_union.mp he with heS | heT
  · obtain ⟨eS, heSP, rfl⟩ := Finset.mem_map.mp heS
    obtain ⟨dS, _hdS, hdx⟩ := Sym2.mem_map.mp hde
    have hcell : dS.1.1 = x.1.1.1 := congrArg Sigma.fst hdx
    exact Set.disjoint_left.mp hdisj (hcell ▸ dS.1.2) x.1.1.2
  · obtain ⟨eT, heTQ, rfl⟩ := Finset.mem_map.mp heT
    obtain ⟨dT, hdT, hdx⟩ := Sym2.mem_map.mp hde
    have hdEq : dT = x.1 :=
      includeDart_injective (facets := facets) T hdx
    apply x.2
    exact (Q.matching.mem_occupied_iff x.1).mpr
      ⟨eT, heTQ, by simpa only [hdEq] using hdT⟩

@[simp]
theorem includeLeftBoundary_val
    (S T : Set Cell) (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (x : P.Boundary) :
    (includeLeftBoundary S T hdisj P Q x).1 =
      includeDart (facets := facets) S x.1 := rfl

@[simp]
theorem includeRightBoundary_val
    (S T : Set Cell) (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (x : Q.Boundary) :
    (includeRightBoundary S T hdisj P Q x).1 =
      includeDart (facets := facets) T x.1 := rfl

/-- A free ambient dart of a reassembly comes from exactly one component.
The proof uses coverage for existence and disjointness for uniqueness. -/
noncomputable def boundaryReassembleEquiv
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r) :
    (reassembleColored S T hdisj P Q).Boundary ≃
      P.Boundary ⊕ Q.Boundary := by
  classical
  refine {
  toFun := fun z ↦ if hzS : z.1.1 ∈ S then
      Sum.inl ⟨restrictDart S z.1 hzS, by
        intro hocc
        obtain ⟨e, he, hde⟩ := (P.matching.mem_occupied_iff _).mp hocc
        apply z.2
        apply ((reassembleColored S T hdisj P Q).matching.mem_occupied_iff _).mpr
        refine ⟨includeSeam (facets := facets) S e,
          ?_, Sym2.mem_map.mpr ⟨_, hde,
            includeDart_restrictDart S z.1 hzS⟩⟩
        rw [show (reassembleColored S T hdisj P Q).matching.seams =
            (reassembleMatching S T hdisj P.matching Q.matching).seams from rfl,
          seams_reassembleMatching]
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_map.mpr ⟨e, he, rfl⟩))⟩
    else
      Sum.inr ⟨restrictDart T z.1 (by
        have hz : z.1.1 ∈ S ∪ T := by rw [hcover]; exact Set.mem_univ _
        exact (by simpa only [Set.mem_union] using hz :
          z.1.1 ∈ S ∨ z.1.1 ∈ T) |>.resolve_left hzS), by
        intro hocc
        obtain ⟨e, he, hde⟩ := (Q.matching.mem_occupied_iff _).mp hocc
        apply z.2
        apply ((reassembleColored S T hdisj P Q).matching.mem_occupied_iff _).mpr
        let hzT : z.1.1 ∈ T := by
          have hz : z.1.1 ∈ S ∪ T := by rw [hcover]; exact Set.mem_univ _
          exact (by simpa only [Set.mem_union] using hz :
            z.1.1 ∈ S ∨ z.1.1 ∈ T) |>.resolve_left hzS
        refine ⟨includeSeam (facets := facets) T e,
          ?_, Sym2.mem_map.mpr ⟨_, hde,
            includeDart_restrictDart T z.1 hzT⟩⟩
        rw [show (reassembleColored S T hdisj P Q).matching.seams =
            (reassembleMatching S T hdisj P.matching Q.matching).seams from rfl,
          seams_reassembleMatching]
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_map.mpr ⟨e, he, rfl⟩))⟩,
  invFun := fun z ↦ match z with
    | Sum.inl x => includeLeftBoundary S T hdisj P Q x
    | Sum.inr x => includeRightBoundary S T hdisj P Q x,
  left_inv := by
    intro z
    by_cases hzS : z.1.1 ∈ S
    · apply Subtype.ext
      simp only [dif_pos hzS]
      exact includeDart_restrictDart S z.1 hzS
    · let hzT : z.1.1 ∈ T := by
        have hz : z.1.1 ∈ S ∪ T := by rw [hcover]; exact Set.mem_univ _
        exact (by simpa only [Set.mem_union] using hz :
          z.1.1 ∈ S ∨ z.1.1 ∈ T) |>.resolve_left hzS
      apply Subtype.ext
      simp only [dif_neg hzS]
      exact includeDart_restrictDart T z.1 hzT
  right_inv := by
    intro z
    cases z with
    | inl x =>
        simp only [includeLeftBoundary_val, includeDart]
        rw [dif_pos x.1.1.2]
        congr 1
    | inr x =>
        have hnot : x.1.1.1 ∉ S := by
          intro hxS
          exact Set.disjoint_left.mp hdisj hxS x.1.1.2
        simp only [includeRightBoundary_val, includeDart]
        rw [dif_neg hnot]
        congr 1
  }

@[simp]
theorem boundaryReassembleEquiv_symm_inl
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (x : P.Boundary) :
    (boundaryReassembleEquiv S T hcover hdisj P Q).symm (Sum.inl x) =
      includeLeftBoundary S T hdisj P Q x := rfl

@[simp]
theorem boundaryReassembleEquiv_symm_inr
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (x : Q.Boundary) :
    (boundaryReassembleEquiv S T hcover hdisj P Q).symm (Sum.inr x) =
      includeRightBoundary S T hdisj P Q x := rfl

@[simp]
theorem boundaryReassembleEquiv_includeLeft
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (x : P.Boundary) :
    boundaryReassembleEquiv S T hcover hdisj P Q
        (includeLeftBoundary S T hdisj P Q x) = Sum.inl x := by
  exact (boundaryReassembleEquiv S T hcover hdisj P Q).apply_eq_iff_eq_symm_apply.mpr
    rfl

@[simp]
theorem boundaryReassembleEquiv_includeRight
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (x : Q.Boundary) :
    boundaryReassembleEquiv S T hcover hdisj P Q
        (includeRightBoundary S T hdisj P Q x) = Sum.inr x := by
  exact (boundaryReassembleEquiv S T hcover hdisj P Q).apply_eq_iff_eq_symm_apply.mpr
    rfl

/-! ## Fixed allocations of boundary labels -/

/-- A coloured matching whose free darts are bijectively labelled by an
arbitrary type.  `BoundaryLabelledPairing` is the specialization `Label =
Fin m`. -/
abbrev TypedBoundaryLabelledPairing
    (D : Type*) [DecidableEq D] (r : ℕ) (Label : Type*) :=
  Σ P : ColoredMatching D r, P.Boundary ≃ Label

/-- Component data with a fixed left/right label allocation.  Writing the
base as a product makes its relationship with coloured reassembly literal. -/
abbrev FixedComponentLabelData
    (S T : Set Cell) (A : Type uA) (B : Type uB) :=
  Σ X : ColoredMatching (RestrictedDart (facets := facets) S) r ×
      ColoredMatching (RestrictedDart (facets := facets) T) r,
    (X.1.Boundary ≃ A) × (X.2.Boundary ≃ B)

/-- Ambient no-crossing data carrying the same fixed label allocation on
its two induced restrictions. -/
abbrev FixedAmbientLabelData
    (S T : Set Cell) (A : Type uA) (B : Type uB) :=
  Σ P : {P : ColoredMatching (CellDart Cell facets) r //
      IsInternalToPartition S T P},
    ((P.1.restrict S).Boundary ≃ A) ×
      ((P.1.restrict T).Boundary ≃ B)

/-- Equality of coloured matchings transports their dependent boundary
label equivalences. -/
def boundaryLabelsOfEq {D : Type*} [DecidableEq D]
    {P Q : ColoredMatching D r} (h : P = Q) (A : Type*) :
    (P.Boundary ≃ A) ≃ (Q.Boundary ≃ A) := by
  subst Q
  exact Equiv.refl _

/-- Equality of coloured matchings induces the identity-on-darts
equivalence of their boundary subtypes. -/
def boundaryEquivOfEq {D : Type*} [DecidableEq D]
    {P Q : ColoredMatching D r} (h : P = Q) : P.Boundary ≃ Q.Boundary := by
  subst Q
  exact Equiv.refl _

/-- For a fixed partition and a fixed allocation of label types, restriction
and reassembly are mutually inverse including every boundary label. -/
def fixedLabelRestrictionEquiv
    (S T : Set Cell) (hdisj : Disjoint S T)
    (A : Type uA) (B : Type uB) :
    FixedComponentLabelData (facets := facets) (r := r) S T A B ≃
      FixedAmbientLabelData (facets := facets) (r := r) S T A B :=
  Equiv.sigmaCongr
    (reassembleColoredEquiv (facets := facets) (r := r) S T hdisj)
    (fun X ↦ Equiv.prodCongr
      (boundaryLabelsOfEq
        (ColoredMatching.restrict_reassembleColored_left
          S T hdisj X.1 X.2).symm A)
      (boundaryLabelsOfEq
        (ColoredMatching.restrict_reassembleColored_right
          S T hdisj X.1 X.2).symm B))

/-- A fixed component allocation gives one global boundary labelling by the
sum of the two label types. -/
def reassembleAllocatedBoundaryLabel
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (X : FixedComponentLabelData (facets := facets) (r := r) S T A B) :
    (reassembleColored S T hdisj X.1.1 X.1.2).Boundary ≃ A ⊕ B :=
  (boundaryReassembleEquiv S T hcover hdisj X.1.1 X.1.2).trans
    (Equiv.sumCongr X.2.1 X.2.2)

/-- Specialization to two ordinary numeric label blocks. -/
def reassembleFinBoundaryLabel
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (X : FixedComponentLabelData (facets := facets) (r := r)
      S T (Fin m₁) (Fin m₂)) :
    (reassembleColored S T hdisj X.1.1 X.1.2).Boundary ≃
      Fin m₁ ⊕ Fin m₂ :=
  reassembleAllocatedBoundaryLabel S T hcover hdisj X

/-- Reassemble two ordinary boundary-labelled component pairings.  The
result uses the standard consecutive label set `Fin (m₁ + m₂)`; the left
block comes first and the right block second. -/
def reassembleBoundaryLabelled
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : BoundaryLabelledPairing
      (RestrictedDart (facets := facets) S) r m₁)
    (Q : BoundaryLabelledPairing
      (RestrictedDart (facets := facets) T) r m₂) :
    BoundaryLabelledPairing (CellDart Cell facets) r (m₁ + m₂) where
  pairing := reassembleColored S T hdisj P.pairing Q.pairing
  label := (boundaryReassembleEquiv S T hcover hdisj P.pairing Q.pairing).trans <|
    (Equiv.sumCongr P.label Q.label).trans PartialMatching.finSumEquiv

@[simp]
theorem reassembleBoundaryLabelled_pairing
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : BoundaryLabelledPairing
      (RestrictedDart (facets := facets) S) r m₁)
    (Q : BoundaryLabelledPairing
      (RestrictedDart (facets := facets) T) r m₂) :
    (reassembleBoundaryLabelled S T hcover hdisj P Q).pairing =
      reassembleColored S T hdisj P.pairing Q.pairing := rfl

@[simp]
theorem reassembleBoundaryLabelled_label_left
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : BoundaryLabelledPairing
      (RestrictedDart (facets := facets) S) r m₁)
    (Q : BoundaryLabelledPairing
      (RestrictedDart (facets := facets) T) r m₂)
    (x : P.pairing.Boundary) :
    (reassembleBoundaryLabelled S T hcover hdisj P Q).label
        (includeLeftBoundary S T hdisj P.pairing Q.pairing x) =
      PartialMatching.finSumEquiv (Sum.inl (P.label x)) := by
  simp [reassembleBoundaryLabelled]

@[simp]
theorem reassembleBoundaryLabelled_label_right
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : BoundaryLabelledPairing
      (RestrictedDart (facets := facets) S) r m₁)
    (Q : BoundaryLabelledPairing
      (RestrictedDart (facets := facets) T) r m₂)
    (x : Q.pairing.Boundary) :
    (reassembleBoundaryLabelled S T hcover hdisj P Q).label
        (includeRightBoundary S T hdisj P.pairing Q.pairing x) =
      PartialMatching.finSumEquiv (Sum.inr (Q.label x)) := by
  simp [reassembleBoundaryLabelled]

/-! ## The two new stars of an actual bridge deletion -/

/-- In a genuine bridge deletion, the first exposed endpoint lies in the
left component and the second exposed endpoint lies in the right component.
This is the precise one-new-star-per-component statement. -/
theorem bridge_exposed_endpoints_on_opposite_sides
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam)
    (hconnected : P.IsConnected facets) (hbridge : P.IsBridge e) :
    let Q := P.erase e
    let C := P.bridge_partition e hconnected hbridge
    let S := BridgePartition.LeftClass
      (Q.Adjacent facets) (P.leftCell e)
    let T := BridgePartition.RightClass
      (Q.Adjacent facets) (P.rightCell e)
    (P.matching.leftBoundaryAfterErase e).1.1 ∈ S ∧
      (P.matching.rightBoundaryAfterErase e).1.1 ∈ T := by
  dsimp only
  exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- After cutting an actual bridge of a boundary-labelled connected object,
the two concrete component boundaries together receive exactly the old
`m` labels plus the two canonical star labels.  The previous theorem proves
that the two stars occur on opposite components. -/
def bridgeCutComponentBoundaryLabel
    (P : BoundaryLabelledPairing (CellDart Cell facets) r m)
    (e : P.pairing.Seam)
    (hconnected : P.pairing.IsConnected facets)
    (hbridge : P.pairing.IsBridge e) :
    let Q := P.pairing.erase e
    let C := P.pairing.bridge_partition e hconnected hbridge
    let S := BridgePartition.LeftClass
      (Q.Adjacent facets) (P.pairing.leftCell e)
    let T := BridgePartition.RightClass
      (Q.Adjacent facets) (P.pairing.rightCell e)
    (Q.restrict S).Boundary ⊕ (Q.restrict T).Boundary ≃ Fin (m + 2) := by
  dsimp only
  let Q := P.pairing.erase e
  let C := P.pairing.bridge_partition e hconnected hbridge
  let S := BridgePartition.LeftClass
    (Q.Adjacent facets) (P.pairing.leftCell e)
  let T := BridgePartition.RightClass
    (Q.Adjacent facets) (P.pairing.rightCell e)
  let hreassemble :
      reassembleColored S T C.disjoint (Q.restrict S) (Q.restrict T) = Q :=
    erase_bridge_reassemble_exact P.pairing e hconnected hbridge
  exact (boundaryReassembleEquiv S T C.cover C.disjoint
      (Q.restrict S) (Q.restrict T)).symm |>.trans <|
    (boundaryEquivOfEq hreassemble).trans
      (P.pairing.matching.cutBoundaryLabel e P.label)

/-! ## Counting the allocation types -/

@[simp]
theorem card_sum_boundary_reassembly
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    [Fintype S] [Fintype T]
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r) :
    Fintype.card (reassembleColored S T hdisj P Q).Boundary =
      Fintype.card P.Boundary + Fintype.card Q.Boundary := by
  simpa using Fintype.card_congr
    (boundaryReassembleEquiv S T hcover hdisj P Q)


end
end FacetPairing
end PolytopeCounting
