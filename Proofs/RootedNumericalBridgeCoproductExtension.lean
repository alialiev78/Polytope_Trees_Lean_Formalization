module

public import Proofs.RootedNumericalBridgeCoproduct
public import Proofs.JoinComponentsBridge
public import Proofs.LabelledReindexing
public import Proofs.NumericalBridgeCut
public import Proofs.NonbridgeExact
public import Proofs.StarJoinLabelCoherence
public import Proofs.AllocationLabelImage
public import Proofs.ColoredRawCutJoin

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Explicit allocation reindexing for the rooted numerical bridge coproduct

This private development extends the kernel-clean allocation/cardinality
module while the shared source is frozen.  Every equivalence below is
chosen once and is then used in both directions of reconstruction.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

open RootedGlobalBridgeCut PointedDecomposition LabelledCutJoin
open NumericalBridgeCut

/-- A finset and its complement form an explicit decomposition of a finite
ambient type. -/
def finsetSumComplementEquiv {X : Type*} [Fintype X] [DecidableEq X]
    (A : Finset X) :
    {x : X // x ∈ A} ⊕ {x : X // x ∉ A} ≃ X where
  toFun z := z.elim Subtype.val Subtype.val
  invFun x := if hx : x ∈ A then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, hx⟩
  left_inv z := by
    rcases z with x | x
    · simp [x.2]
    · simp [x.2]
  right_inv x := by
    by_cases hx : x ∈ A <;> simp [hx]

theorem card_complement {X : Type*} [Fintype X] [DecidableEq X]
    (A : Finset X) :
    Fintype.card {x : X // x ∉ A} = Fintype.card X - A.card := by
  have h := Fintype.card_congr (finsetSumComplementEquiv A)
  rw [Fintype.card_sum, Fintype.card_coe] at h
  omega

def complementEquivFin {X : Type*} [Fintype X] [DecidableEq X]
    (A : Finset X) :
    {x : X // x ∉ A} ≃ Fin (Fintype.card X - A.card) :=
  (Fintype.equivFin {x : X // x ∉ A}).trans
    (finCongr (card_complement A))

/-- Base-side literal cells: the distinguished base plus the allocated
ordinary cells. -/
abbrev baseCellSet (d : Coproduct n h₀ h r m b) : Set (RootedCell n) :=
  {c | match c with
    | Sum.inl _ => True
    | Sum.inr i => i ∈ d.2.2.2.1.1}

/-- The complementary component contains precisely the unallocated
ordinary cells and never the base. -/
abbrev otherCellSet (d : Coproduct n h₀ h r m b) : Set (RootedCell n) :=
  {c | match c with
    | Sum.inl _ => False
    | Sum.inr i => i ∉ d.2.2.2.1.1}

theorem cellSets_cover (d : Coproduct n h₀ h r m b) :
    baseCellSet d ∪ otherCellSet d = Set.univ := by
  classical
  ext c
  rcases c with u | i
  · simp [baseCellSet, otherCellSet]
  · simp only [baseCellSet, otherCellSet, Set.mem_union, Set.mem_setOf_eq,
      Set.mem_univ, iff_true]
    exact Classical.em _

theorem cellSets_disjoint (d : Coproduct n h₀ h r m b) :
    Disjoint (baseCellSet d) (otherCellSet d) := by
  classical
  rw [Set.disjoint_left]
  intro c hc hd
  rcases c with u | i
  · exact hd
  · exact hd hc

/-- The base-side cell subtype is canonically the standard rooted cell type
on `ℓ` ordinary cells. -/
def baseCellEquiv (d : Coproduct n h₀ h r m b) :
    baseCellSet d ≃ RootedCell d.1.1 := by
  let eA : {i : Fin n // i ∈ d.2.2.2.1.1} ≃ Fin d.1.1 :=
    (Fintype.equivFin _).trans (finCongr (by
      simpa using d.2.2.2.1.2))
  refine
    { toFun := fun c ↦ match h : c.1 with
        | Sum.inl u => Sum.inl u
        | Sum.inr i => Sum.inr (eA ⟨i, by simpa only [baseCellSet, Set.mem_setOf_eq, h] using c.2⟩)
      invFun := fun c ↦ match c with
        | Sum.inl u => ⟨Sum.inl u, by simp [baseCellSet]⟩
        | Sum.inr i => ⟨Sum.inr (eA.symm i).1, by
            simpa only [baseCellSet, Set.mem_setOf_eq] using (eA.symm i).2⟩
      left_inv := by
        rintro ⟨c, hc⟩
        rcases c with u | i
        · rfl
        · apply Subtype.ext
          simp
      right_inv := by
        intro c
        rcases c with u | i
        · rfl
        · simp }

/-- The away-side cell subtype is canonically `Fin (n-ℓ)`. -/
def otherCellEquiv (d : Coproduct n h₀ h r m b) :
    otherCellSet d ≃ Fin (n - d.1.1) := by
  let eA : {i : Fin n // i ∉ d.2.2.2.1.1} ≃ Fin (n - d.1.1) :=
    (complementEquivFin d.2.2.2.1.1).trans
      (finCongr (by rw [Fintype.card_fin, d.2.2.2.1.2]))
  refine
    { toFun := fun c ↦ match h : c.1 with
        | Sum.inl u => False.elim (by simpa only [otherCellSet, Set.mem_setOf_eq, h] using c.2)
        | Sum.inr i => eA ⟨i, by simpa only [otherCellSet, Set.mem_setOf_eq, h] using c.2⟩
      invFun := fun i ↦ ⟨Sum.inr (eA.symm i).1, by
        simpa only [otherCellSet, Set.mem_setOf_eq] using (eA.symm i).2⟩
      left_inv := by
        rintro ⟨c, hc⟩
        rcases c with u | i
        · exact False.elim hc
        · apply Subtype.ext
          simp
      right_inv := by intro i; simp }

/-- Fibre equivalence used on base-component darts. -/
def baseFacetEquiv (d : Coproduct n h₀ h r m b) (c : baseCellSet d) :
    Fin (rootedFacets h₀ h c.1) ≃
      Fin (rootedFacets h₀ h (baseCellEquiv d c)) :=
  finCongr (by
    rcases c with ⟨c, hc⟩
    rcases c with u | i
    · rfl
    · rfl)

/-- The base-side dart equivalence respects the exceptional base arity
`h₀` and ordinary arity `h`. -/
def baseDartEquiv (d : Coproduct n h₀ h r m b) :
    RestrictedDart (facets := rootedFacets h₀ h) (baseCellSet d) ≃
      RootedDart d.1.1 h₀ h :=
  Equiv.sigmaCongr (baseCellEquiv d) (baseFacetEquiv d)

/-- Fibre equivalence used on away-component darts. -/
def otherFacetEquiv (d : Coproduct n h₀ h r m b) (c : otherCellSet d) :
    Fin (rootedFacets h₀ h c.1) ≃ Fin h :=
  finCongr (by
    rcases c with ⟨c, hc⟩
    rcases c with u | i
    · exact False.elim hc
    · rfl)

/-- All away-side cells are ordinary, so their restricted darts have the
uniform standard arity `h`. -/
def otherDartEquiv (d : Coproduct n h₀ h r m b) :
    RestrictedDart (facets := rootedFacets h₀ h) (otherCellSet d) ≃
      Dart (n - d.1.1) h :=
  Equiv.sigmaCongr (otherCellEquiv d) (otherFacetEquiv d)

/-! ## Reconstruction of an independently indexed cut object -/

/-- The cell allocation stored in the dependent coproduct. -/
abbrev cells (d : Coproduct n h₀ h r m b) := d.2.2.2.1

/-- The oriented boundary allocation stored in the coproduct. -/
abbrev labels (d : Coproduct n h₀ h r m b) := d.2.2.2.2.1

/-- Canonical rooted component on the base side. -/
abbrev baseComponent (d : Coproduct n h₀ h r m b) :=
  d.2.2.2.2.2.1

/-- Canonical unrooted component away from the base. -/
abbrev otherComponent (d : Coproduct n h₀ h r m b) :=
  d.2.2.2.2.2.2.1

/-- Colour of the bridge which will be reinserted. -/
abbrev bridgeColor (d : Coproduct n h₀ h r m b) :=
  d.2.2.2.2.2.2.2

/-- Undo the chosen rooted dart reindexing on the base component. -/
def baseRestrictedPairing (d : Coproduct n h₀ h r m b) :
    BoundaryLabelledPairing
      (RestrictedDart (facets := rootedFacets h₀ h) (baseCellSet d)) r
      (d.2.1.1 + 1) :=
  (BoundaryLabelledPairing.reindexEquiv (r := r) (m := d.2.1.1 + 1)
    (baseDartEquiv d)).symm (baseComponent d).1.raw

/-- Undo the uniform dart reindexing on the component away from the base. -/
def otherRestrictedPairing (d : Coproduct n h₀ h r m b) :
    BoundaryLabelledPairing
      (RestrictedDart (facets := rootedFacets h₀ h) (otherCellSet d)) r
      (m - d.2.1.1 + 1) :=
  (BoundaryLabelledPairing.reindexEquiv (r := r)
    (m := m - d.2.1.1 + 1) (otherDartEquiv d)).symm
      (otherComponent d).1.raw

/-- Interpret the base component's numerical labels as the allocated
ambient cut-boundary labels themselves. -/
def baseAllocatedLabel (d : Coproduct n h₀ h r m b) :
    (baseRestrictedPairing d).pairing.Boundary ≃
      {i : Fin (m + 2) // i ∈ (labels d).1} :=
  (baseRestrictedPairing d).label.trans <|
    (finCongr (labels d).2.2.2.symm).trans
      (finsetSubtypeEquivFin (labels d).1).symm

/-- Interpret the other component's numerical labels as the complementary
ambient cut-boundary labels. -/
def otherAllocatedLabel (d : Coproduct n h₀ h r m b) :
    (otherRestrictedPairing d).pairing.Boundary ≃
      {i : Fin (m + 2) // i ∉ (labels d).1} :=
  (otherRestrictedPairing d).label.trans <|
    (finCongr (by
      have hs : d.2.1.1 ≤ m := by omega
      rw [Fintype.card_fin, (labels d).2.2.2]
      omega)).trans (complementEquivFin (labels d).1).symm

/-- Exact coloured disjoint union of the two independently indexed
components on the original rooted ambient cell set. -/
def reconstructedCutPairing (d : Coproduct n h₀ h r m b) :
    ColoredMatching (RootedDart n h₀ h) r :=
  reassembleColored (baseCellSet d) (otherCellSet d)
    (cellSets_disjoint d)
    (baseRestrictedPairing d).pairing
    (otherRestrictedPairing d).pairing

/-- Allocation-enriched boundary labelling on the reconstructed cut. -/
def reconstructedCutLabel (d : Coproduct n h₀ h r m b) :
    (reconstructedCutPairing d).Boundary ≃ Fin (m + 2) :=
  (boundaryReassembleEquiv (baseCellSet d) (otherCellSet d)
    (cellSets_cover d) (cellSets_disjoint d)
    (baseRestrictedPairing d).pairing
    (otherRestrictedPairing d).pairing).trans <|
      (Equiv.sumCongr (baseAllocatedLabel d) (otherAllocatedLabel d)).trans
        (finsetSumComplementEquiv (labels d).1)

/-- The complete reconstructed, star-labelled rooted cut object. -/
def reconstructedCutRaw (d : Coproduct n h₀ h r m b) :
    BoundaryLabelledPairing (RootedDart n h₀ h) r (m + 2) where
  pairing := reconstructedCutPairing d
  label := reconstructedCutLabel d

/-- Local base-side boundary dart carrying the compulsory first star. -/
def baseStarBoundary (d : Coproduct n h₀ h r m b) :
    (baseRestrictedPairing d).pairing.Boundary :=
  (baseAllocatedLabel d).symm ⟨firstStar m, (labels d).2.1⟩

/-- Local other-side boundary dart carrying the compulsory second star. -/
def otherStarBoundary (d : Coproduct n h₀ h r m b) :
    (otherRestrictedPairing d).pairing.Boundary :=
  (otherAllocatedLabel d).symm ⟨secondStar m, (labels d).2.2.1⟩

theorem reconstructedCutLabel_baseStar (d : Coproduct n h₀ h r m b) :
    (reconstructedCutRaw d).label
      (includeLeftBoundary (baseCellSet d) (otherCellSet d)
        (cellSets_disjoint d)
        (baseRestrictedPairing d).pairing
        (otherRestrictedPairing d).pairing (baseStarBoundary d)) =
      firstStar m := by
  simp only [reconstructedCutRaw, reconstructedCutLabel,
    reconstructedCutPairing, Equiv.trans_apply,
    boundaryReassembleEquiv_includeLeft, Equiv.sumCongr_apply,
    Sum.map_inl, baseStarBoundary, Equiv.apply_symm_apply,
    finsetSumComplementEquiv]
  rfl

theorem reconstructedCutLabel_otherStar (d : Coproduct n h₀ h r m b) :
    (reconstructedCutRaw d).label
      (includeRightBoundary (baseCellSet d) (otherCellSet d)
        (cellSets_disjoint d)
        (baseRestrictedPairing d).pairing
        (otherRestrictedPairing d).pairing (otherStarBoundary d)) =
      secondStar m := by
  simp only [reconstructedCutRaw, reconstructedCutLabel,
    reconstructedCutPairing, Equiv.trans_apply,
    boundaryReassembleEquiv_includeRight, Equiv.sumCongr_apply,
    Sum.map_inr, otherStarBoundary, Equiv.apply_symm_apply,
    finsetSumComplementEquiv]
  rfl

/-- The first star lies on the intrinsic base component. -/
theorem firstStarDart_mem_baseCellSet (d : Coproduct n h₀ h r m b) :
    (firstStarDart (reconstructedCutRaw d)).1.1 ∈ baseCellSet d := by
  let x := includeLeftBoundary (baseCellSet d) (otherCellSet d)
    (cellSets_disjoint d)
    (baseRestrictedPairing d).pairing
    (otherRestrictedPairing d).pairing (baseStarBoundary d)
  have hx : x = firstStarDart (reconstructedCutRaw d) := by
    apply (reconstructedCutRaw d).label.injective
    rw [reconstructedCutLabel_baseStar]
    simp [firstStarDart]
  rw [← hx]
  exact (baseStarBoundary d).1.1.2

/-- The second star lies on the component away from the base. -/
theorem secondStarDart_mem_otherCellSet (d : Coproduct n h₀ h r m b) :
    (secondStarDart (reconstructedCutRaw d)).1.1 ∈ otherCellSet d := by
  let x := includeRightBoundary (baseCellSet d) (otherCellSet d)
    (cellSets_disjoint d)
    (baseRestrictedPairing d).pairing
    (otherRestrictedPairing d).pairing (otherStarBoundary d)
  have hx : x = secondStarDart (reconstructedCutRaw d) := by
    apply (reconstructedCutRaw d).label.injective
    rw [reconstructedCutLabel_otherStar]
    simp [secondStarDart]
  rw [← hx]
  exact (otherStarBoundary d).1.1.2

/-! ## Reindexing preserves component connectivity -/

universe uC uE

/-- A cell equivalence together with a fibrewise facet equivalence induces
the expected equivalence of dependent dart types. -/
def cellDartEquiv
    {C : Type uC} {E : Type uE}
    {f : C → ℕ} {g : E → ℕ}
    (e : C ≃ E) (q : ∀ c, Fin (f c) ≃ Fin (g (e c))) :
    CellDart C f ≃ CellDart E g :=
  Equiv.sigmaCongr e q

@[simp]
theorem cellDartEquiv_apply
    {C : Type uC} {E : Type uE}
    {f : C → ℕ} {g : E → ℕ}
    (e : C ≃ E) (q : ∀ c, Fin (f c) ≃ Fin (g (e c)))
    (c : C) (i : Fin (f c)) :
    cellDartEquiv e q ⟨c, i⟩ = ⟨e c, q c i⟩ := rfl

/-- Exact adjacency reflection and preservation under dependent cell/dart
reindexing. -/
theorem adjacent_reindex_cellDart_iff
    {C : Type uC} {E : Type uE}
    [DecidableEq C] [DecidableEq E]
    {f : C → ℕ} {g : E → ℕ}
    (e : C ≃ E) (q : ∀ c, Fin (f c) ≃ Fin (g (e c)))
    (P : ColoredMatching (CellDart C f) r) (u v : C) :
    (P.reindex (cellDartEquiv e q)).Adjacent g (e u) (e v) ↔
      P.Adjacent f u v := by
  constructor
  · rintro ⟨i, j, hij⟩
    change s(⟨e u, i⟩, ⟨e v, j⟩) ∈
      (P.matching.reindex (cellDartEquiv e q)).seams at hij
    rw [PartialMatching.seams_reindex] at hij
    obtain ⟨old, hold, hmap⟩ := Finset.mem_map.mp hij
    let wanted : Sym2 (CellDart C f) :=
      s(⟨u, (q u).symm i⟩, ⟨v, (q v).symm j⟩)
    have hwanted :
        Sym2.map (cellDartEquiv e q) wanted =
          s(⟨e u, i⟩, ⟨e v, j⟩) := by
      change Sym2.map (cellDartEquiv e q)
        s(⟨u, (q u).symm i⟩, ⟨v, (q v).symm j⟩) = _
      rw [Sym2.map_mk]
      have hu : cellDartEquiv e q ⟨u, (q u).symm i⟩ =
          (⟨e u, i⟩ : CellDart E g) := by
        apply Sigma.ext
        · rfl
        · simp
      have hv : cellDartEquiv e q ⟨v, (q v).symm j⟩ =
          (⟨e v, j⟩ : CellDart E g) := by
        apply Sigma.ext
        · rfl
        · simp
      rw [hu, hv]
    have holdEq : old = wanted := by
      apply (Sym2.map.injective (cellDartEquiv e q).injective)
      exact hmap.trans hwanted.symm
    refine ⟨(q u).symm i, (q v).symm j, ?_⟩
    simpa only [holdEq] using hold
  · rintro ⟨i, j, hij⟩
    refine ⟨q u i, q v j, ?_⟩
    change s(⟨e u, q u i⟩, ⟨e v, q v j⟩) ∈
      (P.matching.reindex (cellDartEquiv e q)).seams
    rw [PartialMatching.seams_reindex]
    apply Finset.mem_map.mpr
    refine ⟨s(⟨u, i⟩, ⟨v, j⟩), hij, ?_⟩
    change Sym2.map (cellDartEquiv e q) s(⟨u, i⟩, ⟨v, j⟩) = _
    rw [Sym2.map_mk]
    rfl

/-- Connectivity is invariant under a dependent cell/dart reindexing. -/
theorem connected_reindex_cellDart_iff
    {C : Type uC} {E : Type uE}
    [DecidableEq C] [DecidableEq E]
    {f : C → ℕ} {g : E → ℕ}
    (e : C ≃ E) (q : ∀ c, Fin (f c) ≃ Fin (g (e c)))
    (P : ColoredMatching (CellDart C f) r) :
    (P.reindex (cellDartEquiv e q)).IsConnected g ↔
      P.IsConnected f := by
  constructor
  · intro h x y
    have hp := h (e x) (e y)
    have hlift := Relation.ReflTransGen.lift e.symm
      (fun u v huv ↦ by
        have h' := (adjacent_reindex_cellDart_iff e q P
          (e.symm u) (e.symm v)).mp (by simpa using huv)
        simpa using h') _ _ hp
    simpa [Function.onFun] using hlift
  · intro h x y
    have hp := h (e.symm x) (e.symm y)
    have hlift := Relation.ReflTransGen.lift e
      (fun u v huv ↦
        (adjacent_reindex_cellDart_iff e q P u v).mpr huv) _ _ hp
    simpa [Function.onFun] using hlift

/-- Connectivity of the reconstructed base restriction follows from the
rooted canonical component stratum. -/
theorem baseRestrictedPairing_connected (d : Coproduct n h₀ h r m b) :
    (baseRestrictedPairing d).pairing.IsConnected
      (fun c : baseCellSet d ↦ rootedFacets h₀ h c.1) := by
  apply (connected_reindex_cellDart_iff (baseCellEquiv d) (baseFacetEquiv d)
    (baseRestrictedPairing d).pairing).mp
  have hp := BoundaryLabelledPairing.reindexEquiv_apply_symm_apply
    (r := r) (m := d.2.1.1 + 1) (baseDartEquiv d)
    (baseComponent d).1.raw
  have hpair :
      (baseRestrictedPairing d).pairing.reindex (baseDartEquiv d) =
        (baseComponent d).1.raw.pairing :=
    congrArg BoundaryLabelledPairing.pairing hp
  change ((baseRestrictedPairing d).pairing.reindex
    (cellDartEquiv (baseCellEquiv d) (baseFacetEquiv d))).IsConnected
      (rootedFacets h₀ h)
  rw [show cellDartEquiv (baseCellEquiv d) (baseFacetEquiv d) =
      baseDartEquiv d from rfl,
    hpair]
  exact (baseComponent d).1.connected

set_option maxHeartbeats 800000 in
/-- Connectivity of the reconstructed away restriction follows from its
canonical unrooted component stratum. -/
theorem otherRestrictedPairing_connected (d : Coproduct n h₀ h r m b) :
    (otherRestrictedPairing d).pairing.IsConnected
      (fun c : otherCellSet d ↦ rootedFacets h₀ h c.1) := by
  apply (connected_reindex_cellDart_iff (g := fun _ ↦ h)
    (otherCellEquiv d) (otherFacetEquiv d)
    (otherRestrictedPairing d).pairing).mp
  have hp := BoundaryLabelledPairing.reindexEquiv_apply_symm_apply
    (r := r) (m := m - d.2.1.1 + 1) (otherDartEquiv d)
    (otherComponent d).1.raw
  have hpair :
      (otherRestrictedPairing d).pairing.reindex (otherDartEquiv d) =
        (otherComponent d).1.raw.pairing :=
    congrArg BoundaryLabelledPairing.pairing hp
  rw [show cellDartEquiv (otherCellEquiv d) (otherFacetEquiv d) =
      otherDartEquiv d from rfl,
    hpair]
  exact (otherComponent d).1.connected

/-! ## Literal rooted bridge reconstruction -/

/-- Join the two allocation-selected stars with the stored colour. -/
def reconstructedJoinMarked (d : Coproduct n h₀ h r m b) :
    ColoredMatching.MarkedColoredMatching (RootedDart n h₀ h) r :=
  joinStarsMarked (reconstructedCutRaw d, bridgeColor d)

/-- Boundary-labelled rooted pairing after consuming the two star labels. -/
def reconstructedJoinedRaw (d : Coproduct n h₀ h r m b) :
    RootedPairing n h₀ h r m where
  pairing := (reconstructedJoinMarked d).1
  label := NonbridgeEquiv.joinedBoundaryLabel
    (reconstructedCutRaw d) (bridgeColor d)

/-- Erasing the distinguished reconstructed seam returns the complete
allocated cut coloured matching exactly. -/
theorem erase_reconstructedJoinMarked (d : Coproduct n h₀ h r m b) :
    (reconstructedJoinMarked d).1.erase (reconstructedJoinMarked d).2 =
      reconstructedCutPairing d := by
  exact cut_joinStars_pairing (reconstructedCutRaw d, bridgeColor d)

/-- The reassembly matching used by `JoinComponentsBridge` is precisely our
reconstructed cut matching. -/
theorem reconstructedCutPairing_eq_cutMatching
    (d : Coproduct n h₀ h r m b) :
    reconstructedCutPairing d =
      JoinComponentsBridge.cutMatching
        (baseCellSet d) (otherCellSet d) (cellSets_disjoint d)
        (baseRestrictedPairing d).pairing
        (otherRestrictedPairing d).pairing := rfl

/-- The first star dart is exactly the ambient inclusion of the selected
base-component boundary. -/
theorem firstStarDart_eq_include_base (d : Coproduct n h₀ h r m b) :
    firstStarDart (reconstructedCutRaw d) =
      includeLeftBoundary (baseCellSet d) (otherCellSet d)
        (cellSets_disjoint d)
        (baseRestrictedPairing d).pairing
        (otherRestrictedPairing d).pairing (baseStarBoundary d) := by
  apply (reconstructedCutRaw d).label.injective
  simp [firstStarDart, reconstructedCutLabel_baseStar]

/-- The second star dart is exactly the ambient inclusion of the selected
away-component boundary. -/
theorem secondStarDart_eq_include_other (d : Coproduct n h₀ h r m b) :
    secondStarDart (reconstructedCutRaw d) =
      includeRightBoundary (baseCellSet d) (otherCellSet d)
        (cellSets_disjoint d)
        (baseRestrictedPairing d).pairing
        (otherRestrictedPairing d).pairing (otherStarBoundary d) := by
  apply (reconstructedCutRaw d).label.injective
  simp [secondStarDart, reconstructedCutLabel_otherStar]

/-- The free-pair selected by the two stars is the same cross-component
pair used by the generic bridge-join construction. -/
theorem reconstructed_starFreePair_eq_crossPair
    (d : Coproduct n h₀ h r m b) :
    (starFreePair (reconstructedCutRaw d)).pair =
      s((JoinComponentsBridge.leftBoundary
          (baseCellSet d) (otherCellSet d) (cellSets_disjoint d)
          (baseRestrictedPairing d).pairing
          (otherRestrictedPairing d).pairing (baseStarBoundary d)).1,
        (JoinComponentsBridge.rightBoundary
          (baseCellSet d) (otherCellSet d) (cellSets_disjoint d)
          (baseRestrictedPairing d).pairing
          (otherRestrictedPairing d).pairing (otherStarBoundary d)).1) := by
  rw [starFreePair_pair, firstStarDart_eq_include_base,
    secondStarDart_eq_include_other]

/-- Joining the two connected allocated components produces a connected
rooted matching. -/
theorem reconstructedJoined_connected (d : Coproduct n h₀ h r m b) :
    (reconstructedJoinMarked d).1.IsConnected (rootedFacets h₀ h) := by
  intro u v
  let a := (firstStarDart (reconstructedCutRaw d)).1.1
  let c := (secondStarDart (reconstructedCutRaw d)).1.1
  have ha : a ∈ baseCellSet d := firstStarDart_mem_baseCellSet d
  have hc : c ∈ otherCellSet d := secondStarDart_mem_otherCellSet d
  have oldMono {x y : RootedCell n}
      (p : Relation.ReflTransGen
        ((reconstructedCutPairing d).Adjacent (rootedFacets h₀ h)) x y) :
      Relation.ReflTransGen
        ((reconstructedJoinMarked d).1.Adjacent (rootedFacets h₀ h)) x y :=
    p.mapRelation (fun x y hxy ↦ by
      obtain ⟨i, j, hij⟩ := hxy
      exact ⟨i, j, Finset.mem_insert_of_mem hij⟩)
  have hbase (x y : baseCellSet d) :
      Relation.ReflTransGen
        ((reconstructedCutPairing d).Adjacent (rootedFacets h₀ h)) x.1 y.1 := by
    exact ((baseRestrictedPairing_connected d) x y).lift Subtype.val
      (fun z w hzw ↦ by
        have hr := (reconstructedCutPairing d).adjacent_restrict_iff
          (baseCellSet d) z w
        have hres : (reconstructedCutPairing d).restrict (baseCellSet d) =
            (baseRestrictedPairing d).pairing :=
          ColoredMatching.restrict_reassembleColored_left
            (baseCellSet d) (otherCellSet d) (cellSets_disjoint d)
            (baseRestrictedPairing d).pairing
            (otherRestrictedPairing d).pairing
        rw [hres] at hr
        exact hr.mp hzw)
  have hother (x y : otherCellSet d) :
      Relation.ReflTransGen
        ((reconstructedCutPairing d).Adjacent (rootedFacets h₀ h)) x.1 y.1 := by
    exact ((otherRestrictedPairing_connected d) x y).lift Subtype.val
      (fun z w hzw ↦ by
        have hr := (reconstructedCutPairing d).adjacent_restrict_iff
          (otherCellSet d) z w
        have hres : (reconstructedCutPairing d).restrict (otherCellSet d) =
            (otherRestrictedPairing d).pairing :=
          ColoredMatching.restrict_reassembleColored_right
            (baseCellSet d) (otherCellSet d) (cellSets_disjoint d)
            (baseRestrictedPairing d).pairing
            (otherRestrictedPairing d).pairing
        rw [hres] at hr
        exact hr.mp hzw)
  have hcross : (reconstructedJoinMarked d).1.Adjacent (rootedFacets h₀ h) a c := by
    refine ⟨(firstStarDart (reconstructedCutRaw d)).1.2,
      (secondStarDart (reconstructedCutRaw d)).1.2, ?_⟩
    change s((firstStarDart (reconstructedCutRaw d)).1,
      (secondStarDart (reconstructedCutRaw d)).1) ∈
        (reconstructedJoinMarked d).1.matching.seams
    change (starFreePair (reconstructedCutRaw d)).pair ∈
      ((reconstructedCutPairing d).joinFreePair
        (starFreePairDatum (reconstructedCutRaw d)
          (bridgeColor d))).matching.seams
    rw [show (starFreePair (reconstructedCutRaw d)).pair =
      (starFreePairDatum (reconstructedCutRaw d)
        (bridgeColor d)).selected.pair from rfl]
    change _ ∈ insert _ _
    simp only [PartialMatching.FreePair.joinPair_left_right,
      Finset.mem_insert, true_or]
  have side (z : RootedCell n) : z ∈ baseCellSet d ∨ z ∈ otherCellSet d := by
    have hz : z ∈ baseCellSet d ∪ otherCellSet d := by
      rw [cellSets_cover d]
      exact Set.mem_univ z
    simpa only [Set.mem_union] using hz
  rcases side u with huB | huO
  · rcases side v with hvB | hvO
    · exact oldMono (hbase ⟨u, huB⟩ ⟨v, hvB⟩)
    · exact (oldMono (hbase ⟨u, huB⟩ ⟨a, ha⟩)).trans <|
        (Relation.ReflTransGen.single hcross).trans <|
          oldMono (hother ⟨c, hc⟩ ⟨v, hvO⟩)
  · rcases side v with hvB | hvO
    · exact (oldMono (hother ⟨u, huO⟩ ⟨c, hc⟩)).trans <|
        (Relation.ReflTransGen.single
          ((reconstructedJoinMarked d).1.adjacent_symm _ hcross)).trans <|
            oldMono (hbase ⟨a, ha⟩ ⟨v, hvB⟩)
    · exact oldMono (hother ⟨u, huO⟩ ⟨v, hvO⟩)

/-! ## Separation, seam counts, rank, and the inverse map -/

/-- No cut seam crosses between the two allocated cell blocks. -/
theorem reconstructedCut_noCrossing (d : Coproduct n h₀ h r m b) :
    NoCrossing (reconstructedCutPairing d)
      (baseCellSet d) (otherCellSet d) := by
  intro u hu v hv huv
  obtain ⟨i, j, hij⟩ := huv
  have hinternal := seamInternal_reassembleMatching
    (baseCellSet d) (otherCellSet d) (cellSets_disjoint d)
    (baseRestrictedPairing d).pairing.matching
    (otherRestrictedPairing d).pairing.matching
    s(⟨u, i⟩, ⟨v, j⟩) hij
  rcases hinternal with hbase | hother
  · exact Set.disjoint_left.mp (cellSets_disjoint d)
      (hbase ⟨v, j⟩ (by simp)) hv
  · exact Set.disjoint_left.mp (cellSets_disjoint d)
      hu (hother ⟨u, i⟩ (by simp))

/-- A cut path starting in the base allocation stays there. -/
theorem reconstructedCut_path_stays_base (d : Coproduct n h₀ h r m b)
    {x y : RootedCell n} (hx : x ∈ baseCellSet d)
    (p : Relation.ReflTransGen
      ((reconstructedCutPairing d).Adjacent (rootedFacets h₀ h)) x y) :
    y ∈ baseCellSet d := by
  induction p with
  | refl => exact hx
  | @tail u v huv huv' ih =>
      have hvSide : v ∈ baseCellSet d ∨ v ∈ otherCellSet d := by
        have : v ∈ baseCellSet d ∪ otherCellSet d := by
          rw [cellSets_cover d]
          exact Set.mem_univ v
        simpa only [Set.mem_union] using this
      exact hvSide.resolve_right (fun hv ↦
        reconstructedCut_noCrossing d ih hv huv')

/-- The allocated cut has two nonempty separated components. -/
theorem reconstructedCut_not_connected (d : Coproduct n h₀ h r m b) :
    ¬ (reconstructedCutPairing d).IsConnected (rootedFacets h₀ h) := by
  intro hconn
  let a := (firstStarDart (reconstructedCutRaw d)).1.1
  let c := (secondStarDart (reconstructedCutRaw d)).1.1
  have ha : a ∈ baseCellSet d := firstStarDart_mem_baseCellSet d
  have hc : c ∈ otherCellSet d := secondStarDart_mem_otherCellSet d
  have hcBase := reconstructedCut_path_stays_base d ha (hconn a c)
  exact Set.disjoint_left.mp (cellSets_disjoint d) hcBase hc

/-- Reindexing a coloured matching does not change its number of seams. -/
theorem seam_card_reindex
    {D E : Type*} [DecidableEq D] [DecidableEq E]
    (e : D ≃ E) (P : ColoredMatching D r) :
    (P.reindex e).matching.seams.card = P.matching.seams.card := by
  change (P.matching.reindex e).seams.card = P.matching.seams.card
  rw [PartialMatching.seams_reindex, Finset.card_map]

theorem baseRestrictedPairing_seam_card (d : Coproduct n h₀ h r m b) :
    (baseRestrictedPairing d).pairing.matching.seams.card + 1 =
      (d.1.1 + 1) + d.2.2.1.1 := by
  have hp := (baseComponent d).2
  simp only [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
    BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount,
    card_rootedCell] at hp
  have hpair :
      (baseRestrictedPairing d).pairing.reindex (baseDartEquiv d) =
        (baseComponent d).1.raw.pairing := by
    exact congrArg BoundaryLabelledPairing.pairing
      (BoundaryLabelledPairing.reindexEquiv_apply_symm_apply
        (r := r) (m := d.2.1.1 + 1) (baseDartEquiv d)
        (baseComponent d).1.raw)
  have hcard := seam_card_reindex (baseDartEquiv d)
    (baseRestrictedPairing d).pairing
  rw [hpair] at hcard
  omega

theorem otherRestrictedPairing_seam_card (d : Coproduct n h₀ h r m b) :
    (otherRestrictedPairing d).pairing.matching.seams.card + 1 =
      (n - d.1.1) + (b - d.2.2.1.1) := by
  have hp := (otherComponent d).2
  simp only [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
    BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount,
    card_unrootedCell] at hp
  have hpair :
      (otherRestrictedPairing d).pairing.reindex (otherDartEquiv d) =
        (otherComponent d).1.raw.pairing := by
    exact congrArg BoundaryLabelledPairing.pairing
      (BoundaryLabelledPairing.reindexEquiv_apply_symm_apply
        (r := r) (m := m - d.2.1.1 + 1) (otherDartEquiv d)
        (otherComponent d).1.raw)
  have hcard := seam_card_reindex (otherDartEquiv d)
    (otherRestrictedPairing d).pairing
  rw [hpair] at hcard
  omega

theorem reconstructedCut_seam_card_add (d : Coproduct n h₀ h r m b) :
    (reconstructedCutPairing d).matching.seams.card =
      (baseRestrictedPairing d).pairing.matching.seams.card +
        (otherRestrictedPairing d).pairing.matching.seams.card := by
  change (reassembleMatching (baseCellSet d) (otherCellSet d)
    (cellSets_disjoint d)
    (baseRestrictedPairing d).pairing.matching
    (otherRestrictedPairing d).pairing.matching).seams.card = _
  rw [seams_reassembleMatching, Finset.card_union_of_disjoint]
  · simp
  · rw [Finset.disjoint_left]
    intro e heB heO
    obtain ⟨eB, heBM, heBe⟩ := Finset.mem_map.mp heB
    obtain ⟨eO, heOM, heOe⟩ := Finset.mem_map.mp heO
    exact includeSeam_ne_of_disjoint (baseCellSet d) (otherCellSet d)
      (cellSets_disjoint d) eB eO (heBe.trans heOe.symm)

theorem reconstructedCut_rank (d : Coproduct n h₀ h r m b) :
    (reconstructedCutPairing d).matching.seams.card + 2 = n + 1 + b := by
  have hℓ := d.1.2
  have hp : d.2.2.1.1 ≤ b := by omega
  have hB := baseRestrictedPairing_seam_card d
  have hO := otherRestrictedPairing_seam_card d
  rw [reconstructedCut_seam_card_add]
  omega

/-- Rejoining the bridge yields the exact rooted rank equation. -/
theorem reconstructedJoined_rank (d : Coproduct n h₀ h r m b) :
    (reconstructedJoinedRaw d).pairing.matching.seams.card + 1 =
      n + 1 + b := by
  change (reconstructedJoinMarked d).1.matching.seams.card + 1 = _
  have hj : (reconstructedJoinMarked d).1.matching.seams.card =
      (reconstructedCutPairing d).matching.seams.card + 1 := by
    change ((reconstructedCutPairing d).joinFreePair
      (starFreePairDatum (reconstructedCutRaw d)
        (bridgeColor d))).matching.seams.card = _
    exact PartialMatching.card_seams_join _ _ _
      ((starFreePairDatum (reconstructedCutRaw d)
        (bridgeColor d)).selected.left_ne_right _)
  rw [hj]
  have := reconstructedCut_rank d
  omega

/-- The newly inserted seam is a genuine bridge. -/
theorem reconstructedJoin_bridge (d : Coproduct n h₀ h r m b) :
    (reconstructedJoinMarked d).1.IsBridge (reconstructedJoinMarked d).2 := by
  intro hconnected
  rw [erase_reconstructedJoinMarked] at hconnected
  exact reconstructedCut_not_connected d hconnected

/-- Actual connected rooted rank-`b` stratum reconstructed from fully
independent canonical components and their two allocations. -/
def reconstructedStratum (d : Coproduct n h₀ h r m b) :
    RootedStratum n h₀ h r m b :=
  ⟨⟨reconstructedJoinedRaw d, reconstructedJoined_connected d⟩,
    by simpa [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
      BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount,
      card_rootedCell, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        reconstructedJoined_rank d⟩

/-- Distinguished reconstructed bridge seam. -/
def reconstructedNewSeam (d : Coproduct n h₀ h r m b) :
    (reconstructedStratum d).1.raw.pairing.Seam :=
  (reconstructedJoinMarked d).2

/-- Concrete inverse candidate from the enriched numerical coproduct into
the literal rooted bridge-pointed stratum. -/
def fromCoproduct (d : Coproduct n h₀ h r m b) :
    RootedBridgePointed n h₀ h r m b :=
  ⟨⟨reconstructedStratum d, reconstructedNewSeam d⟩,
    reconstructedJoin_bridge d⟩

/-! ## Intrinsic base-oriented forward cut -/

theorem cutBridge_core_eq_cutLabelled
    (z : RootedBridgePointed n h₀ h r m b) :
    (cutBridge z).core = cutLabelled (domainEncoding z) := by
  calc
    (cutBridge z).core =
        cutLabelled (joinLabelled (cutBridge z).core) :=
      (cutLabelled_joinLabelled (cutBridge z).core).symm
    _ = cutLabelled (domainEncoding z) := by
      rw [show joinLabelled (cutBridge z).core = domainEncoding z from
        recoverMarked_cutBridge z]

/-- The carrier cut matching is the literal erasure in the source. -/
theorem cutBridge_core_pairing
    (z : RootedBridgePointed n h₀ h r m b) :
    (cutBridge z).core.1.1 =
      z.1.1.1.raw.pairing.erase z.1.2 := by
  rw [cutBridge_core_eq_cutLabelled]
  exact cutLabelled_pairing (domainEncoding z)

/-- The selected free pair in the rooted carrier is the cut seam itself. -/
theorem cutBridge_selectedPair
    (z : RootedBridgePointed n h₀ h r m b) :
    (cutBridge z).core.1.2.selected.pair = z.1.2.1 := by
  rw [cutBridge_core_eq_cutLabelled]
  exact cutLabelled_selectedPair (domainEncoding z)

/-- Ambient endpoint on the component containing the distinguished base. -/
def baseSelectedEndpoint
    (z : RootedBridgePointed n h₀ h r m b) :
    {d : RootedDart n h₀ h // d ∈ z.1.2.1} := by
  let C := cutBridge z
  let x := includeDart (facets := rootedFacets h₀ h)
    C.baseCells C.baseStar.1
  refine ⟨x, ?_⟩
  have hx : x ∈
      s(includeDart (facets := rootedFacets h₀ h)
          C.baseCells C.baseStar.1,
        includeDart (facets := rootedFacets h₀ h)
          C.otherCells C.otherStar.1) := by
    rw [Sym2.mem_iff]
    exact Or.inl rfl
  rw [C.exposedPair, cutBridge_selectedPair z] at hx
  exact hx

/-- Flat oriented marked object whose first endpoint is chosen intrinsically
by the distinguished base component. -/
def baseOrientedMarked
    (z : RootedBridgePointed n h₀ h r m b) :
    OrientedMarkedColored (RootedDart n h₀ h) r where
  pairing := z.1.1.1.raw.pairing
  seam := z.1.2.1
  seam_mem := z.1.2.2
  first := (baseSelectedEndpoint z).1
  first_mem := (baseSelectedEndpoint z).2

def baseOrientedSeam
    (z : RootedBridgePointed n h₀ h r m b) :
    (baseOrientedMarked z).pairing.matching.OrientedSeam :=
  ⟨(baseOrientedMarked z).seamSubtype,
    ⟨(baseOrientedMarked z).first, (baseOrientedMarked z).first_mem⟩⟩

def baseOrientedCutLabel
    (z : RootedBridgePointed n h₀ h r m b) :
    ((baseOrientedMarked z).pairing.erase
      (baseOrientedMarked z).seamSubtype).Boundary ≃ Fin (m + 2) :=
  (baseOrientedMarked z).pairing.matching.orientedCutBoundaryLabel
    (baseOrientedSeam z) z.1.1.1.raw.label

/-- Replace only the carrier's boundary label by the intrinsic base-first
oriented cut label. No component-exchange bit is introduced. -/
def baseOrientedCarrier
    (z : RootedBridgePointed n h₀ h r m b) :
    RootedBridgeCutCarrier n h₀ h r m b := by
  let C := cutBridge z
  have hcut : C.core.1.1 =
      (baseOrientedMarked z).pairing.erase
        (baseOrientedMarked z).seamSubtype := cutBridge_core_pairing z
  exact { C with
    componentBoundaryLabel :=
      (boundaryReassembleEquiv C.baseCells C.otherCells C.cover C.disjoint
        (C.core.1.1.restrict C.baseCells)
        (C.core.1.1.restrict C.otherCells)).symm |>.trans <|
        (boundaryEquivOfEq C.reassemble_exact).trans <|
          (boundaryEquivOfEq hcut).trans (baseOrientedCutLabel z) }

theorem orientedCutBoundaryLabel_first
    {D : Type*} [DecidableEq D]
    (M : PartialMatching D) (o : M.OrientedSeam)
    (label : M.Boundary ≃ Fin m) :
    M.orientedCutBoundaryLabel o label
      (M.endpointBoundaryAfterErase o.1 o.2.1 o.2.2) = firstStar m := by
  have hocc : o.2.1 ∈ M.occupied :=
    (M.mem_occupied_iff _).mpr ⟨o.1.1, o.1.2, o.2.2⟩
  have hnot : ¬ o.2.1 ∉ M.occupied := not_not.mpr hocc
  simp only [PartialMatching.orientedCutBoundaryLabel,
    PartialMatching.orientedBoundaryEraseEquiv,
    PartialMatching.endpointBoundaryAfterErase,
    Equiv.trans_apply, Equiv.sumCongr_apply, subtypeOrEquiv,
    Equiv.coe_fn_mk, Set.equivOfEq_apply]
  rw [subtypeOrLeftEmbedding_apply_right _ hnot]
  change Fin.natAdd m (finTwoEquiv.symm
    (if o.2.1 = o.2.1 then false else true)) = firstStar m
  rw [if_pos rfl]
  rfl

theorem orientedCutBoundaryLabel_second
    {D : Type*} [DecidableEq D]
    (M : PartialMatching D) (o : M.OrientedSeam)
    (label : M.Boundary ≃ Fin m) :
    M.orientedCutBoundaryLabel o label
      (M.endpointBoundaryAfterErase o.1 (M.otherEndpoint o)
        (M.otherEndpoint_mem o)) = secondStar m := by
  have hocc : M.otherEndpoint o ∈ M.occupied :=
    (M.mem_occupied_iff _).mpr
      ⟨o.1.1, o.1.2, M.otherEndpoint_mem o⟩
  have hnot : ¬ M.otherEndpoint o ∉ M.occupied := not_not.mpr hocc
  simp only [PartialMatching.orientedCutBoundaryLabel,
    PartialMatching.orientedBoundaryEraseEquiv,
    PartialMatching.endpointBoundaryAfterErase,
    Equiv.trans_apply, Equiv.sumCongr_apply, subtypeOrEquiv,
    Equiv.coe_fn_mk, Set.equivOfEq_apply]
  rw [subtypeOrLeftEmbedding_apply_right _ hnot]
  change Fin.natAdd m (finTwoEquiv.symm
    (if M.otherEndpoint o = o.2.1 then false else true)) = secondStar m
  rw [if_neg (M.oriented_endpoints_ne o).symm]
  rfl

@[simp]
theorem boundaryEquivOfEq_val
    {D : Type*} [DecidableEq D] {P Q : ColoredMatching D r}
    (h : P = Q) (x : P.Boundary) :
    (boundaryEquivOfEq h x).1 = x.1 := by
  subst Q
  rfl

theorem baseOrientedCarrier_baseStar_val
    (z : RootedBridgePointed n h₀ h r m b) :
    includeDart (facets := rootedFacets h₀ h)
      (baseOrientedCarrier z).baseCells
      (baseOrientedCarrier z).baseStar.1 =
        (baseSelectedEndpoint z).1 := rfl

theorem baseOrientedCarrier_otherStar_val
    (z : RootedBridgePointed n h₀ h r m b) :
    includeDart (facets := rootedFacets h₀ h)
      (baseOrientedCarrier z).otherCells
      (baseOrientedCarrier z).otherStar.1 =
        (baseOrientedMarked z).pairing.matching.otherEndpoint
          (baseOrientedSeam z) := by
  apply Sym2.congr_right.mp
  calc
    s((baseSelectedEndpoint z).1,
        includeDart (facets := rootedFacets h₀ h)
          (baseOrientedCarrier z).otherCells
          (baseOrientedCarrier z).otherStar.1) = z.1.2.1 := by
      exact (cutBridge z).exposedPair.trans (cutBridge_selectedPair z)
    _ = s((baseSelectedEndpoint z).1,
        (baseOrientedMarked z).pairing.matching.otherEndpoint
          (baseOrientedSeam z)) := by
      symm
      exact Sym2.other_spec' (baseOrientedSeam z).2.2

/-- The intrinsically selected base endpoint always receives the first star
label. -/
theorem baseOrientedCarrier_baseStar_label
    (z : RootedBridgePointed n h₀ h r m b) :
    (baseOrientedCarrier z).componentBoundaryLabel
      (Sum.inl (baseOrientedCarrier z).baseStar) = firstStar m := by
  let C := baseOrientedCarrier z
  let B := boundaryReassembleEquiv C.baseCells C.otherCells C.cover C.disjoint
    (C.core.1.1.restrict C.baseCells)
    (C.core.1.1.restrict C.otherCells)
  have hcut : C.core.1.1 =
      (baseOrientedMarked z).pairing.erase
        (baseOrientedMarked z).seamSubtype := cutBridge_core_pairing z
  have harg :
      boundaryEquivOfEq hcut
        (boundaryEquivOfEq C.reassemble_exact
          (B.symm (Sum.inl C.baseStar))) =
        (baseOrientedMarked z).pairing.matching.endpointBoundaryAfterErase
          (baseOrientedSeam z).1 (baseOrientedSeam z).2.1
          (baseOrientedSeam z).2.2 := by
    apply Subtype.ext
    rw [boundaryEquivOfEq_val, boundaryEquivOfEq_val,
      boundaryReassembleEquiv_symm_inl, includeLeftBoundary_val]
    exact baseOrientedCarrier_baseStar_val z
  change baseOrientedCutLabel z
    (boundaryEquivOfEq hcut
      (boundaryEquivOfEq C.reassemble_exact
        (B.symm (Sum.inl C.baseStar)))) = firstStar m
  rw [harg]
  exact orientedCutBoundaryLabel_first
    (baseOrientedMarked z).pairing.matching (baseOrientedSeam z)
      z.1.1.1.raw.label

/-- The opposite component's exposed endpoint always receives the second
star label. -/
theorem baseOrientedCarrier_otherStar_label
    (z : RootedBridgePointed n h₀ h r m b) :
    (baseOrientedCarrier z).componentBoundaryLabel
      (Sum.inr (baseOrientedCarrier z).otherStar) = secondStar m := by
  let C := baseOrientedCarrier z
  let B := boundaryReassembleEquiv C.baseCells C.otherCells C.cover C.disjoint
    (C.core.1.1.restrict C.baseCells)
    (C.core.1.1.restrict C.otherCells)
  have hcut : C.core.1.1 =
      (baseOrientedMarked z).pairing.erase
        (baseOrientedMarked z).seamSubtype := cutBridge_core_pairing z
  have harg :
      boundaryEquivOfEq hcut
        (boundaryEquivOfEq C.reassemble_exact
          (B.symm (Sum.inr C.otherStar))) =
        (baseOrientedMarked z).pairing.matching.endpointBoundaryAfterErase
          (baseOrientedSeam z).1
          ((baseOrientedMarked z).pairing.matching.otherEndpoint
            (baseOrientedSeam z))
          ((baseOrientedMarked z).pairing.matching.otherEndpoint_mem
            (baseOrientedSeam z)) := by
    apply Subtype.ext
    rw [boundaryEquivOfEq_val, boundaryEquivOfEq_val,
      boundaryReassembleEquiv_symm_inr, includeRightBoundary_val]
    exact baseOrientedCarrier_otherStar_val z
  change baseOrientedCutLabel z
    (boundaryEquivOfEq hcut
      (boundaryEquivOfEq C.reassemble_exact
        (B.symm (Sum.inr C.otherStar)))) = secondStar m
  rw [harg]
  exact orientedCutBoundaryLabel_second
    (baseOrientedMarked z).pairing.matching (baseOrientedSeam z)
      z.1.1.1.raw.label

/-! ## Literal forward allocations -/

def forwardCellFinset (z : RootedBridgePointed n h₀ h r m b) :
    Finset (Fin n) := by
  letI : Fintype (baseOrdinaryCells (baseOrientedCarrier z)) :=
    Fintype.ofFinite _
  exact (baseOrdinaryCells (baseOrientedCarrier z)).toFinset

theorem forwardCellFinset_card
    (z : RootedBridgePointed n h₀ h r m b) :
    (forwardCellFinset z).card =
      (baseOrientedCarrier z).baseOrdinaryCount := by
  classical
  letI : Fintype (baseOrdinaryCells (baseOrientedCarrier z)) :=
    Fintype.ofFinite _
  rw [forwardCellFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card]
  exact card_baseOrdinaryCells (baseOrientedCarrier z)

def forwardCellIndex (z : RootedBridgePointed n h₀ h r m b) : Fin n :=
  ⟨(baseOrientedCarrier z).baseOrdinaryCount,
    baseOrdinaryCount_lt (baseOrientedCarrier z)⟩

def forwardCellAllocation (z : RootedBridgePointed n h₀ h r m b) :
    CellAllocation n (forwardCellIndex z).1 :=
  ⟨forwardCellFinset z, forwardCellFinset_card z⟩

def forwardBaseBoundaryMap (z : RootedBridgePointed n h₀ h r m b) :
    ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).baseCells).Boundary → Fin (m + 2) :=
  fun x ↦ (baseOrientedCarrier z).componentBoundaryLabel (Sum.inl x)

def forwardOtherBoundaryMap (z : RootedBridgePointed n h₀ h r m b) :
    ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).otherCells).Boundary → Fin (m + 2) :=
  fun x ↦ (baseOrientedCarrier z).componentBoundaryLabel (Sum.inr x)

theorem forwardBaseBoundaryMap_injective
    (z : RootedBridgePointed n h₀ h r m b) :
    Function.Injective (forwardBaseBoundaryMap z) := by
  intro x y hxy
  apply Sum.inl.inj
  exact (baseOrientedCarrier z).componentBoundaryLabel.injective hxy

theorem forwardOtherBoundaryMap_injective
    (z : RootedBridgePointed n h₀ h r m b) :
    Function.Injective (forwardOtherBoundaryMap z) := by
  intro x y hxy
  apply Sum.inr.inj
  exact (baseOrientedCarrier z).componentBoundaryLabel.injective hxy

def forwardBaseBoundaryLabels (z : RootedBridgePointed n h₀ h r m b) :
    Finset (Fin (m + 2)) :=
  @Finset.image _ _ (Classical.decEq _) (forwardBaseBoundaryMap z)
    (@Finset.univ _ (Fintype.ofFinite _))

def forwardOtherBoundaryLabels (z : RootedBridgePointed n h₀ h r m b) :
    Finset (Fin (m + 2)) :=
  @Finset.image _ _ (Classical.decEq _) (forwardOtherBoundaryMap z)
    (@Finset.univ _ (Fintype.ofFinite _))

theorem mem_forwardBaseBoundaryLabels_iff
    (z : RootedBridgePointed n h₀ h r m b) (i : Fin (m + 2)) :
    i ∈ forwardBaseBoundaryLabels z ↔
      ∃ x, forwardBaseBoundaryMap z x = i := by
  classical
  simp [forwardBaseBoundaryLabels]

theorem mem_forwardOtherBoundaryLabels_iff
    (z : RootedBridgePointed n h₀ h r m b) (i : Fin (m + 2)) :
    i ∈ forwardOtherBoundaryLabels z ↔
      ∃ x, forwardOtherBoundaryMap z x = i := by
  classical
  simp [forwardOtherBoundaryLabels]

theorem forwardBoundaryLabels_disjoint
    (z : RootedBridgePointed n h₀ h r m b) :
    Disjoint (forwardBaseBoundaryLabels z) (forwardOtherBoundaryLabels z) := by
  rw [Finset.disjoint_left]
  intro i hiB hiO
  obtain ⟨x, hx⟩ := (mem_forwardBaseBoundaryLabels_iff z i).mp hiB
  obtain ⟨y, hy⟩ := (mem_forwardOtherBoundaryLabels_iff z i).mp hiO
  have hsum : (Sum.inl x :
      ((baseOrientedCarrier z).core.1.1.restrict
          (baseOrientedCarrier z).baseCells).Boundary ⊕
        ((baseOrientedCarrier z).core.1.1.restrict
          (baseOrientedCarrier z).otherCells).Boundary) = Sum.inr y := by
    apply (baseOrientedCarrier z).componentBoundaryLabel.injective
    exact hx.trans hy.symm
  cases hsum

theorem forwardBoundaryLabels_cover
    (z : RootedBridgePointed n h₀ h r m b) :
    forwardBaseBoundaryLabels z ∪ forwardOtherBoundaryLabels z =
      Finset.univ := by
  ext i
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  let q := (baseOrientedCarrier z).componentBoundaryLabel.symm i
  rcases hq : q with x | y
  · left
    apply (mem_forwardBaseBoundaryLabels_iff z i).mpr
    refine ⟨x, ?_⟩
    change (baseOrientedCarrier z).componentBoundaryLabel (Sum.inl x) = i
    rw [← hq]
    exact (baseOrientedCarrier z).componentBoundaryLabel.apply_symm_apply i
  · right
    apply (mem_forwardOtherBoundaryLabels_iff z i).mpr
    refine ⟨y, ?_⟩
    change (baseOrientedCarrier z).componentBoundaryLabel (Sum.inr y) = i
    rw [← hq]
    exact (baseOrientedCarrier z).componentBoundaryLabel.apply_symm_apply i

theorem forwardBoundaryLabel_cards_add
    (z : RootedBridgePointed n h₀ h r m b) :
    (forwardBaseBoundaryLabels z).card +
      (forwardOtherBoundaryLabels z).card = m + 2 := by
  rw [← Finset.card_union_of_disjoint (forwardBoundaryLabels_disjoint z),
    forwardBoundaryLabels_cover]
  simp

theorem firstStar_mem_forwardBaseBoundaryLabels
    (z : RootedBridgePointed n h₀ h r m b) :
    firstStar m ∈ forwardBaseBoundaryLabels z := by
  apply (mem_forwardBaseBoundaryLabels_iff z _).mpr
  exact ⟨(baseOrientedCarrier z).baseStar,
    baseOrientedCarrier_baseStar_label z⟩

theorem secondStar_mem_forwardOtherBoundaryLabels
    (z : RootedBridgePointed n h₀ h r m b) :
    secondStar m ∈ forwardOtherBoundaryLabels z := by
  apply (mem_forwardOtherBoundaryLabels_iff z _).mpr
  exact ⟨(baseOrientedCarrier z).otherStar,
    baseOrientedCarrier_otherStar_label z⟩

theorem secondStar_not_mem_forwardBaseBoundaryLabels
    (z : RootedBridgePointed n h₀ h r m b) :
    secondStar m ∉ forwardBaseBoundaryLabels z := by
  intro h
  exact Finset.disjoint_left.mp (forwardBoundaryLabels_disjoint z)
    h (secondStar_mem_forwardOtherBoundaryLabels z)

theorem forwardBaseBoundaryLabels_card_pos
    (z : RootedBridgePointed n h₀ h r m b) :
    0 < (forwardBaseBoundaryLabels z).card :=
  Finset.card_pos.mpr ⟨firstStar m,
    firstStar_mem_forwardBaseBoundaryLabels z⟩

theorem forwardBaseBoundaryLabels_card_lt
    (z : RootedBridgePointed n h₀ h r m b) :
    (forwardBaseBoundaryLabels z).card < m + 2 := by
  have hsum := forwardBoundaryLabel_cards_add z
  have hpos : 0 < (forwardOtherBoundaryLabels z).card :=
    Finset.card_pos.mpr ⟨secondStar m,
      secondStar_mem_forwardOtherBoundaryLabels z⟩
  omega

def forwardBoundaryIndex (z : RootedBridgePointed n h₀ h r m b) :
    Fin (m + 1) :=
  ⟨(forwardBaseBoundaryLabels z).card - 1, by
    have := forwardBaseBoundaryLabels_card_lt z
    omega⟩

theorem forwardBaseBoundaryCard_eq
    (z : RootedBridgePointed n h₀ h r m b) :
    (forwardBaseBoundaryLabels z).card =
      (forwardBoundaryIndex z).1 + 1 := by
  have := forwardBaseBoundaryLabels_card_pos z
  change (forwardBaseBoundaryLabels z).card =
    ((forwardBaseBoundaryLabels z).card - 1) + 1
  omega

def forwardBoundaryAllocation
    (z : RootedBridgePointed n h₀ h r m b) :
    BoundaryAllocation m (forwardBoundaryIndex z).1 :=
  ⟨forwardBaseBoundaryLabels z,
    firstStar_mem_forwardBaseBoundaryLabels z,
    secondStar_not_mem_forwardBaseBoundaryLabels z,
    forwardBaseBoundaryCard_eq z⟩

def forwardRankIndex (z : RootedBridgePointed n h₀ h r m b) :
    Fin (b + 1) :=
  ⟨(baseOrientedCarrier z).baseRank, by
    have := (baseOrientedCarrier z).ranks_add
    omega⟩

/-! ## Canonical forward component strata -/

def forwardBaseCellEquiv
    (z : RootedBridgePointed n h₀ h r m b) :
    (baseOrientedCarrier z).baseCells ≃ RootedCell (forwardCellIndex z).1 := by
  letI : Fintype (baseOrdinaryCells (baseOrientedCarrier z)) :=
    Fintype.ofFinite _
  exact (baseCellsEquiv (baseOrientedCarrier z)).trans <|
    Equiv.sumCongr (Equiv.refl Unit) <|
      (Fintype.equivFin _).trans (finCongr (by
        rw [← Nat.card_eq_fintype_card]
        exact card_baseOrdinaryCells (baseOrientedCarrier z)))

def forwardOtherCellEquiv
    (z : RootedBridgePointed n h₀ h r m b) :
    (baseOrientedCarrier z).otherCells ≃
      Fin (n - (forwardCellIndex z).1) := by
  letI : Fintype (otherOrdinaryCells (baseOrientedCarrier z)) :=
    Fintype.ofFinite _
  exact (otherCellsEquiv (baseOrientedCarrier z)).trans <|
    (Fintype.equivFin _).trans (finCongr (by
      have hc := card_otherOrdinaryCells (baseOrientedCarrier z)
      have ha := (baseOrientedCarrier z).ordinaryCounts_add
      change Fintype.card (otherOrdinaryCells (baseOrientedCarrier z)) =
        n - (baseOrientedCarrier z).baseOrdinaryCount
      rw [← Nat.card_eq_fintype_card]
      omega))

def forwardBaseFacetEquiv
    (z : RootedBridgePointed n h₀ h r m b)
    (c : (baseOrientedCarrier z).baseCells) :
    Fin (rootedFacets h₀ h c.1) ≃
      Fin (rootedFacets h₀ h (forwardBaseCellEquiv z c)) := by
  rcases c with ⟨c, hc⟩
  rcases c with u | i
  · exact Equiv.refl _
  · exact Equiv.refl _

def forwardOtherFacetEquiv
    (z : RootedBridgePointed n h₀ h r m b)
    (c : (baseOrientedCarrier z).otherCells) :
    Fin (rootedFacets h₀ h c.1) ≃ Fin h := by
  rcases c with ⟨c, hc⟩
  rcases c with u | i
  · cases u
    exact False.elim ((baseOrientedCarrier z).base_not_mem_other hc)
  · exact Equiv.refl _

def forwardBaseDartEquiv
    (z : RootedBridgePointed n h₀ h r m b) :
    RestrictedDart (facets := rootedFacets h₀ h)
        (baseOrientedCarrier z).baseCells ≃
      RootedDart (forwardCellIndex z).1 h₀ h :=
  Equiv.sigmaCongr (forwardBaseCellEquiv z) (forwardBaseFacetEquiv z)

def forwardOtherDartEquiv
    (z : RootedBridgePointed n h₀ h r m b) :
    RestrictedDart (facets := rootedFacets h₀ h)
        (baseOrientedCarrier z).otherCells ≃
      Dart (n - (forwardCellIndex z).1) h :=
  Equiv.sigmaCongr (forwardOtherCellEquiv z) (forwardOtherFacetEquiv z)

def forwardBaseBoundaryAllocationEquiv
    (z : RootedBridgePointed n h₀ h r m b) :
    ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).baseCells).Boundary ≃
      {i : Fin (m + 2) // i ∈ forwardBaseBoundaryLabels z} := by
  classical
  letI : Fintype ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).baseCells).Boundary := Fintype.ofFinite _
  refine
    { toFun := fun x ↦ ⟨forwardBaseBoundaryMap z x, by
        apply (mem_forwardBaseBoundaryLabels_iff z _).mpr
        exact ⟨x, rfl⟩⟩
      invFun := fun y ↦ Classical.choose
        ((mem_forwardBaseBoundaryLabels_iff z y.1).mp y.2)
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    exact forwardBaseBoundaryMap_injective z
      (Classical.choose_spec
        ((mem_forwardBaseBoundaryLabels_iff z
          (forwardBaseBoundaryMap z x)).mp
            (by apply (mem_forwardBaseBoundaryLabels_iff z _).mpr
                exact ⟨x, rfl⟩)))
  · intro y
    apply Subtype.ext
    exact Classical.choose_spec
      ((mem_forwardBaseBoundaryLabels_iff z y.1).mp y.2)

def forwardOtherBoundaryAllocationEquiv
    (z : RootedBridgePointed n h₀ h r m b) :
    ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).otherCells).Boundary ≃
      {i : Fin (m + 2) // i ∈ forwardOtherBoundaryLabels z} := by
  classical
  letI : Fintype ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).otherCells).Boundary := Fintype.ofFinite _
  refine
    { toFun := fun x ↦ ⟨forwardOtherBoundaryMap z x, by
        apply (mem_forwardOtherBoundaryLabels_iff z _).mpr
        exact ⟨x, rfl⟩⟩
      invFun := fun y ↦ Classical.choose
        ((mem_forwardOtherBoundaryLabels_iff z y.1).mp y.2)
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    exact forwardOtherBoundaryMap_injective z
      (Classical.choose_spec
        ((mem_forwardOtherBoundaryLabels_iff z
          (forwardOtherBoundaryMap z x)).mp
            (by apply (mem_forwardOtherBoundaryLabels_iff z _).mpr
                exact ⟨x, rfl⟩)))
  · intro y
    apply Subtype.ext
    exact Classical.choose_spec
      ((mem_forwardOtherBoundaryLabels_iff z y.1).mp y.2)

def forwardBaseNumericalPairing
    (z : RootedBridgePointed n h₀ h r m b) :
    BoundaryLabelledPairing
      (RootedDart (forwardCellIndex z).1 h₀ h) r
      ((forwardBoundaryIndex z).1 + 1) := by
  let C := baseOrientedCarrier z
  let P := C.core.1.1.restrict C.baseCells
  let e := forwardBaseDartEquiv z
  exact
    { pairing := P.reindex e
      label := (P.matching.boundaryReindexEquiv e).symm |>.trans <|
        (forwardBaseBoundaryAllocationEquiv z).trans <|
          (finsetSubtypeEquivFin (forwardBaseBoundaryLabels z)).trans
            (finCongr (forwardBaseBoundaryCard_eq z)) }

def forwardOtherNumericalPairing
    (z : RootedBridgePointed n h₀ h r m b) :
    BoundaryLabelledPairing
      (Dart (n - (forwardCellIndex z).1) h) r
      (m - (forwardBoundaryIndex z).1 + 1) := by
  let C := baseOrientedCarrier z
  let P := C.core.1.1.restrict C.otherCells
  let e := forwardOtherDartEquiv z
  exact
    { pairing := P.reindex e
      label := (P.matching.boundaryReindexEquiv e).symm |>.trans <|
        (forwardOtherBoundaryAllocationEquiv z).trans <|
          (finsetSubtypeEquivFin (forwardOtherBoundaryLabels z)).trans
            (finCongr (by
              have hsum := forwardBoundaryLabel_cards_add z
              have hbase := forwardBaseBoundaryCard_eq z
              omega)) }

theorem forwardBaseNumericalPairing_connected
    (z : RootedBridgePointed n h₀ h r m b) :
    (forwardBaseNumericalPairing z).pairing.IsConnected
      (rootedFacets h₀ h) := by
  change (((baseOrientedCarrier z).core.1.1.restrict
    (baseOrientedCarrier z).baseCells).reindex
      (forwardBaseDartEquiv z)).IsConnected (rootedFacets h₀ h)
  exact (connected_reindex_cellDart_iff
    (forwardBaseCellEquiv z) (forwardBaseFacetEquiv z)
    ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).baseCells)).mpr
        (baseOrientedCarrier z).baseConnected

theorem forwardOtherNumericalPairing_connected
    (z : RootedBridgePointed n h₀ h r m b) :
    (forwardOtherNumericalPairing z).pairing.IsConnected (fun _ ↦ h) := by
  change (((baseOrientedCarrier z).core.1.1.restrict
    (baseOrientedCarrier z).otherCells).reindex
      (forwardOtherDartEquiv z)).IsConnected (fun _ ↦ h)
  exact (connected_reindex_cellDart_iff (g := fun _ ↦ h)
    (forwardOtherCellEquiv z) (forwardOtherFacetEquiv z)
    ((baseOrientedCarrier z).core.1.1.restrict
      (baseOrientedCarrier z).otherCells)).mpr
        (baseOrientedCarrier z).otherConnected

def forwardBaseNumericalStratum
    (z : RootedBridgePointed n h₀ h r m b) :
    RootedStratum (forwardCellIndex z).1 h₀ h r
      ((forwardBoundaryIndex z).1 + 1) (forwardRankIndex z).1 :=
  ⟨⟨forwardBaseNumericalPairing z,
      forwardBaseNumericalPairing_connected z⟩,
    by
      have hs := (baseOrientedCarrier z).baseRank_spec
      have he := seam_card_reindex (forwardBaseDartEquiv z)
        ((baseOrientedCarrier z).core.1.1.restrict
          (baseOrientedCarrier z).baseCells)
      have hcard := (baseOrientedCarrier z).baseOrdinaryCount_spec
      have hrank :
          (forwardBaseNumericalPairing z).pairing.matching.seams.card + 1 =
            (forwardCellIndex z).1 + 1 + (forwardRankIndex z).1 := by
        change (((baseOrientedCarrier z).core.1.1.restrict
          (baseOrientedCarrier z).baseCells).reindex
            (forwardBaseDartEquiv z)).matching.seams.card + 1 = _
        change _ = (baseOrientedCarrier z).baseOrdinaryCount + 1 +
          (baseOrientedCarrier z).baseRank
        rw [he]
        omega
      simpa [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
        BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount,
        card_rootedCell, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hrank⟩

def forwardOtherNumericalStratum
    (z : RootedBridgePointed n h₀ h r m b) :
    UnrootedStratum (n - (forwardCellIndex z).1) h r
      (m - (forwardBoundaryIndex z).1 + 1)
      (b - (forwardRankIndex z).1) :=
  ⟨⟨forwardOtherNumericalPairing z,
      forwardOtherNumericalPairing_connected z⟩,
    by
      have hs := (baseOrientedCarrier z).otherRank_spec
      have hr := (baseOrientedCarrier z).ranks_add
      have ha := (baseOrientedCarrier z).ordinaryCounts_add
      have he := seam_card_reindex (forwardOtherDartEquiv z)
        ((baseOrientedCarrier z).core.1.1.restrict
          (baseOrientedCarrier z).otherCells)
      have hcard := (baseOrientedCarrier z).otherOrdinaryCount_spec
      have hrank :
          (forwardOtherNumericalPairing z).pairing.matching.seams.card + 1 =
            (n - (forwardCellIndex z).1) +
              (b - (forwardRankIndex z).1) := by
        change (((baseOrientedCarrier z).core.1.1.restrict
          (baseOrientedCarrier z).otherCells).reindex
            (forwardOtherDartEquiv z)).matching.seams.card + 1 = _
        change _ = (n - (baseOrientedCarrier z).baseOrdinaryCount) +
          (b - (baseOrientedCarrier z).baseRank)
        rw [he]
        omega
      simpa [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
        BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount,
        card_unrootedCell] using hrank⟩

/-- Concrete forward normalization to the genuine allocation-enriched
dependent coproduct. -/
def toCoproduct (z : RootedBridgePointed n h₀ h r m b) :
    Coproduct n h₀ h r m b :=
  ⟨forwardCellIndex z, forwardBoundaryIndex z, forwardRankIndex z,
    forwardCellAllocation z, forwardBoundaryAllocation z,
    forwardBaseNumericalStratum z, forwardOtherNumericalStratum z,
    (baseOrientedCarrier z).deletedColor⟩


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

