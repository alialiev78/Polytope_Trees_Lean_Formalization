module

public import Proofs.FiniteBoundaryConvolution
public import Proofs.RootedNumericalBridgeCoproductExtension

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical cell sizes for the root-component decomposition

The arbitrary complement is allowed to be empty or disconnected. The cell
subset allocation is retained by an actual equivalence, rather than being
inserted as an assumed binomial cardinality.
-/

namespace PolytopeCounting.FacetPairing.ComponentConvolution

noncomputable section

open scoped BigOperators
open CoreComponents
open RootedNumericalBridgeCoproduct (cellDartEquiv connected_reindex_cellDart_iff)
attribute [local instance] Classical.propDecidable

/-- Cell subsets containing the distinguished core. -/
abbrev CoreSubset (n : ℕ) :=
  {S : Set (RootedCell n) // baseCell n ∈ S}

def ordinaryCells (S : CoreSubset n) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ (Sum.inr i : RootedCell n) ∈ S.1)

@[simp] theorem mem_ordinaryCells (S : CoreSubset n) (i : Fin n) :
    i ∈ ordinaryCells S ↔ (Sum.inr i : RootedCell n) ∈ S.1 := by
  simp [ordinaryCells]

/-- Restore a cell subset from its allocated ordinary cells. -/
def subsetFromOrdinary (A : Finset (Fin n)) : CoreSubset n :=
  ⟨(fun c ↦ match c with
      | Sum.inl _ => True
      | Sum.inr i => i ∈ A), by trivial⟩

/-- A root-containing subset is determined by its ordinary-cell allocation. -/
def coreSubsetEquiv (n : ℕ) : CoreSubset n ≃ Finset (Fin n) where
  toFun := ordinaryCells
  invFun := subsetFromOrdinary
  left_inv S := by
    apply Subtype.ext
    ext c
    rcases c with u | i
    · cases u
      change True ↔ baseCell n ∈ S.1
      exact iff_of_true trivial S.2
    · exact mem_ordinaryCells S i
  right_inv A := by
    ext i
    rw [mem_ordinaryCells]
    rfl

/-- Moving a proof that the core belongs to a subset into the outer index. -/
def piecesLocatedEquiv (n h₀ h r : ℕ) :
    Pieces (facets := rootedFacets h₀ h) (r := r) (baseCell n) ≃
      (Σ S : CoreSubset n,
        ConnectedRaw S.1 (fun c ↦ rootedFacets h₀ h c.1) r ×
          ColoredMatching
            (RestrictedDart (facets := rootedFacets h₀ h) S.1ᶜ) r) where
  toFun X := ⟨⟨X.1, X.2.2.1⟩, ⟨X.2.1.1, X.2.2.2⟩, X.2.1.2⟩
  invFun X := ⟨X.1.1, ⟨(X.2.1.1, X.2.2), X.1.2, X.2.1.2⟩⟩
  left_inv X := by rcases X with ⟨S, ⟨⟨P, Q⟩, ha, hc⟩⟩; rfl
  right_inv X := by rcases X with ⟨⟨S, ha⟩, ⟨P, hc⟩, Q⟩; rfl

def ordinaryCellEquiv (S : CoreSubset n) :
    {i : Fin n // i ∈ ordinaryCells S} ≃ Fin (ordinaryCells S).card :=
  Fintype.equivFinOfCardEq (Fintype.card_coe _)

def complementCellEquiv (S : CoreSubset n) :
    {i : Fin n // i ∈ (ordinaryCells S)ᶜ} ≃
      Fin (n - (ordinaryCells S).card) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin])

/-- Root-preserving reindexing by the number of ordinary cells. -/
def rootCellEquiv (S : CoreSubset n) :
    S.1 ≃ RootedCell (ordinaryCells S).card where
  toFun c := match hc : c.1 with
    | Sum.inl u => Sum.inl u
    | Sum.inr i => Sum.inr (ordinaryCellEquiv S
        ⟨i, (mem_ordinaryCells S i).mpr (by simpa only [hc] using c.2)⟩)
  invFun c := match c with
    | Sum.inl u => ⟨Sum.inl u, by cases u; exact S.2⟩
    | Sum.inr i => ⟨Sum.inr ((ordinaryCellEquiv S).symm i).1,
        (mem_ordinaryCells S _).mp ((ordinaryCellEquiv S).symm i).2⟩
  left_inv c := by
    rcases c with ⟨u | i, hc⟩
    · cases u; rfl
    · apply Subtype.ext
      simp
  right_inv c := by
    rcases c with u | i
    · cases u; rfl
    · simp

def rootFacetEquiv (S : CoreSubset n) (h₀ h : ℕ) (c : S.1) :
    Fin (rootedFacets h₀ h c.1) ≃
      Fin (rootedFacets h₀ h (rootCellEquiv S c)) :=
  finCongr (by rcases c with ⟨u | i, hc⟩ <;> rfl)

def rootDartEquiv (S : CoreSubset n) (h₀ h : ℕ) :
    RestrictedDart (facets := rootedFacets h₀ h) S.1 ≃
      RootedDart (ordinaryCells S).card h₀ h :=
  cellDartEquiv (rootCellEquiv S) (rootFacetEquiv S h₀ h)

/-- The complement has no core cell and has exactly `n-k` ordinary cells. -/
def awayCellEquiv (S : CoreSubset n) :
    ↥(S.1ᶜ) ≃ Fin (n - (ordinaryCells S).card) where
  toFun c := match hc : c.1 with
    | Sum.inl u => False.elim (by
        cases u
        exact c.2 (by simpa only [hc, baseCell] using S.2))
    | Sum.inr i => complementCellEquiv S ⟨i, by
        rw [Finset.mem_compl]
        intro hi
        exact c.2 (by simpa only [hc] using (mem_ordinaryCells S i).mp hi)⟩
  invFun i := ⟨Sum.inr ((complementCellEquiv S).symm i).1, by
    intro hi
    have hnot := ((complementCellEquiv S).symm i).2
    rw [Finset.mem_compl] at hnot
    exact hnot ((mem_ordinaryCells S _).mpr hi)⟩
  left_inv c := by
    rcases c with ⟨u | i, hc⟩
    · cases u
      exact False.elim (hc S.2)
    · apply Subtype.ext
      simp
  right_inv i := by simp

def awayFacetEquiv (S : CoreSubset n) (h₀ h : ℕ) (c : ↥(S.1ᶜ)) :
    Fin (rootedFacets h₀ h c.1) ≃ Fin h := by
  rcases c with ⟨u | i, hc⟩
  · cases u
    exact False.elim (hc S.2)
  · exact Equiv.refl _

def awayDartEquiv (S : CoreSubset n) (h₀ h : ℕ) :
    RestrictedDart (facets := rootedFacets h₀ h) S.1ᶜ ≃
      Dart (n - (ordinaryCells S).card) h :=
  cellDartEquiv (awayCellEquiv S) (awayFacetEquiv S h₀ h)

universe uC uE

/-- Lift the existing connectivity-preserving dart transport to connected
raw matchings. -/
def connectedRawEquiv {C : Type uC} {E : Type uE}
    [DecidableEq C] [DecidableEq E] {f : C → ℕ} {g : E → ℕ}
    (e : C ≃ E) (q : ∀ c, Fin (f c) ≃ Fin (g (e c))) (r : ℕ) :
    ConnectedRaw C f r ≃ ConnectedRaw E g r where
  toFun P := ⟨P.1.reindex (cellDartEquiv e q),
    (connected_reindex_cellDart_iff e q P.1).mpr P.2⟩
  invFun Q := ⟨Q.1.reindex (cellDartEquiv e q).symm, by
    apply (connected_reindex_cellDart_iff e q _).mp
    simpa using Q.2⟩
  left_inv P := by
    apply Subtype.ext
    exact ColoredMatching.reindex_symm_reindex _ _
  right_inv Q := by
    apply Subtype.ext
    exact ColoredMatching.reindex_reindex_symm _ _

/-- The fibre over a literal cell allocation, including all seam colours. -/
def componentFibreEquiv (S : CoreSubset n) (h₀ h r : ℕ) :
    (ConnectedRaw S.1 (fun c ↦ rootedFacets h₀ h c.1) r ×
      ColoredMatching (RestrictedDart (facets := rootedFacets h₀ h) S.1ᶜ) r) ≃
    (ConnectedRaw (RootedCell (ordinaryCells S).card) (rootedFacets h₀ h) r ×
      ColoredMatching (Dart (n - (ordinaryCells S).card) h) r) :=
  Equiv.prodCongr
    (connectedRawEquiv (rootCellEquiv S) (rootFacetEquiv S h₀ h) r)
    (ColoredMatching.reindexEquiv (awayDartEquiv S h₀ h))

/-- The fully canonical numerical component carrier. -/
abbrev CanonicalPieces (n h₀ h r : ℕ) :=
  Σ A : Finset (Fin n),
    ConnectedRaw (RootedCell A.card) (rootedFacets h₀ h) r ×
      ColoredMatching (Dart (n - A.card) h) r

/-- A constructed equivalence, not an assumed counting certificate. -/
def canonicalPiecesEquiv (n h₀ h r : ℕ) :
    Pieces (facets := rootedFacets h₀ h) (r := r) (baseCell n) ≃
      CanonicalPieces n h₀ h r :=
  (piecesLocatedEquiv n h₀ h r).trans
    (Equiv.sigmaCongr (coreSubsetEquiv n)
      (fun S ↦ componentFibreEquiv S h₀ h r))

/-- Dart transport does not change the number of free slots. -/
theorem card_boundary_reindex {D : Type uC} {E : Type uE}
    [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E]
    (e : D ≃ E) (P : ColoredMatching D r) :
    Fintype.card (P.reindex e).Boundary = Fintype.card P.Boundary :=
  (Fintype.card_congr (P.matching.boundaryReindexEquiv e)).symm

/-- Numerical reindexing preserves both boundary summands. -/
theorem canonicalPieces_boundary (n h₀ h r : ℕ)
    (X : Pieces (facets := rootedFacets h₀ h) (r := r) (baseCell n)) :
    Fintype.card (canonicalPiecesEquiv n h₀ h r X).2.1.1.Boundary +
        Fintype.card (canonicalPiecesEquiv n h₀ h r X).2.2.Boundary =
      Fintype.card X.2.1.1.Boundary + Fintype.card X.2.1.2.Boundary := by
  change Fintype.card
      (X.2.1.1.reindex (rootDartEquiv ⟨X.1, X.2.2.1⟩ h₀ h)).Boundary +
      Fintype.card
      (X.2.1.2.reindex (awayDartEquiv ⟨X.1, X.2.2.1⟩ h₀ h)).Boundary = _
  rw [card_boundary_reindex, card_boundary_reindex]

/-- The boundary-normalized root decomposition, indexed by all ordinary
cell allocations. -/
theorem root_component_allocation_sum (n h₀ h r m : ℕ) :
    (∑ X : Pieces (facets := rootedFacets h₀ h) (r := r) (baseCell n),
      if Fintype.card X.2.1.1.Boundary + Fintype.card X.2.1.2.Boundary = m
        then (1 : ℚ) else 0) =
      ∑ A : Finset (Fin n), ∑ j ∈ Finset.range (m + 1),
        coreCount A.card h₀ h r j * allCount (n - A.card) h r (m - j) := by
  calc
    _ = ∑ X : CanonicalPieces n h₀ h r,
        if Fintype.card X.2.1.1.Boundary + Fintype.card X.2.2.Boundary = m
          then (1 : ℚ) else 0 := by
      apply Fintype.sum_equiv (canonicalPiecesEquiv n h₀ h r)
      intro X
      rw [canonicalPieces_boundary]
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro A _
      exact sizeCount_prod
        (fun P : ConnectedRaw (RootedCell A.card) (rootedFacets h₀ h) r ↦
          Fintype.card P.1.Boundary)
        (fun P : ColoredMatching (Dart (n - A.card) h) r ↦
          Fintype.card P.Boundary) m

/-- The raw binomial Cauchy product, before `n! tau^n` normalization. -/
theorem root_component_binomial_sum (n h₀ h r m : ℕ) :
    (∑ X : Pieces (facets := rootedFacets h₀ h) (r := r) (baseCell n),
      if Fintype.card X.2.1.1.Boundary + Fintype.card X.2.1.2.Boundary = m
        then (1 : ℚ) else 0) =
      ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (Nat.choose n k : ℚ) * coreCount k h₀ h r j *
          allCount (n - k) h r (m - j) := by
  rw [root_component_allocation_sum,
    sum_subsets_by_card n (fun k ↦ ∑ j ∈ Finset.range (m + 1),
      coreCount k h₀ h r j * allCount (n - k) h r (m - j))]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end PolytopeCounting.FacetPairing.ComponentConvolution
