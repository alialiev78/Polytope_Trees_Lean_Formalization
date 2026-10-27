module

public import Proofs.CoreComponentCoefficients
public import Proofs.Normalization
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite size distributions and boundary-normalized connected counts

All coefficients in this file are finite sums. In particular, neither a
Cauchy-product identity nor a freeness hypothesis is used as an input.
-/

namespace PolytopeCounting.FacetPairing.ComponentConvolution

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u v

/-- The counting distribution of a natural-valued size statistic. -/
def sizeCount (X : Type u) [Fintype X] (s : X → ℕ) (m : ℕ) : ℚ :=
  ∑ x : X, if s x = m then 1 else 0

theorem sizeCount_equiv {X : Type u} {Y : Type v}
    [Fintype X] [Fintype Y] (e : X ≃ Y)
    (s : X → ℕ) (t : Y → ℕ) (hs : ∀ x, t (e x) = s x) (m : ℕ) :
    sizeCount X s m = sizeCount Y t m := by
  unfold sizeCount
  apply Fintype.sum_equiv e
  intro x
  rw [hs]

/-- There is exactly one possible first size when two sizes add to `m`. -/
theorem boundary_indicator_convolution (a b m : ℕ) :
    (if a + b = m then (1 : ℚ) else 0) =
      ∑ j ∈ Finset.range (m + 1),
        (if a = j then (1 : ℚ) else 0) *
          (if b = m - j then (1 : ℚ) else 0) := by
  by_cases ha : a ≤ m
  · rw [Finset.sum_eq_single a]
    · have he : a + b = m ↔ b = m - a := by omega
      simp [he]
    · intro j _ hja
      simp [Ne.symm hja]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · have hab : a + b ≠ m := by omega
    rw [if_neg hab]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    have hne : a ≠ j := by omega
    simp [hne]

/-- Finite convolution, with no boundary-label allocations left over. -/
theorem sizeCount_prod {X : Type u} {Y : Type v}
    [Fintype X] [Fintype Y] (s : X → ℕ) (t : Y → ℕ) (m : ℕ) :
    sizeCount (X × Y) (fun z ↦ s z.1 + t z.2) m =
      ∑ j ∈ Finset.range (m + 1),
        sizeCount X s j * sizeCount Y t (m - j) := by
  unfold sizeCount
  rw [Fintype.sum_prod_type]
  simp_rw [boundary_indicator_convolution]
  calc
    _ = ∑ x : X, ∑ j ∈ Finset.range (m + 1), ∑ y : Y,
        (if s x = j then (1 : ℚ) else 0) *
          (if t y = m - j then (1 : ℚ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (m + 1), ∑ x : X, ∑ y : Y,
        (if s x = j then (1 : ℚ) else 0) *
          (if t y = m - j then (1 : ℚ) else 0) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- Raw connected matchings. No boundary labels are retained. -/
abbrev ConnectedRaw (Cell : Type u) [DecidableEq Cell]
    (facets : Cell → ℕ) (r : ℕ) :=
  {P : ColoredMatching (CellDart Cell facets) r // P.IsConnected facets}

/-- Rewrite the labelled connected record as a dependent labelling fibre. -/
def connectedDataEquiv (Cell : Type u) [Fintype Cell] [DecidableEq Cell]
    (facets : Cell → ℕ) (r m : ℕ) :
    ConnectedDiagram Cell facets r m ≃
      (Σ P : ConnectedRaw Cell facets r, P.1.Boundary ≃ Fin m) where
  toFun P := ⟨⟨P.raw.pairing, P.connected⟩, P.raw.label⟩
  invFun P := ⟨⟨P.1.1, P.2⟩, P.1.2⟩
  left_inv P := by cases P; rfl
  right_inv P := by rcases P with ⟨⟨P, hc⟩, lab⟩; rfl

/-- Boundary-normalized connected counts, obtained from the actual label
fibres. This does not assume a free cell-renaming action. -/
theorem normalized_connected_card (Cell : Type u)
    [Fintype Cell] [DecidableEq Cell]
    (facets : Cell → ℕ) (r m : ℕ) :
    (Fintype.card (ConnectedDiagram Cell facets r m) : ℚ) /
        (m.factorial : ℚ) =
      sizeCount (ConnectedRaw Cell facets r)
        (fun P ↦ Fintype.card P.1.Boundary) m := by
  have hfac : (m.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  rw [Fintype.card_congr (connectedDataEquiv Cell facets r m),
    Fintype.card_sigma]
  simp only [Nat.cast_sum, Finset.sum_div, sizeCount]
  apply Finset.sum_congr rfl
  intro P _
  rw [CoreComponents.card_labels]
  split_ifs <;> simp [hfac]

/-- Raw unrestricted size distribution. -/
def allCount (n h r m : ℕ) : ℚ :=
  sizeCount (ColoredMatching (Dart n h) r)
    (fun P ↦ Fintype.card P.Boundary) m

/-- Raw size distribution of the connected component of a fixed core. -/
def coreCount (n h₀ h r m : ℕ) : ℚ :=
  sizeCount (ConnectedRaw (RootedCell n) (rootedFacets h₀ h) r)
    (fun P ↦ Fintype.card P.1.Boundary) m

/-- The original public `W`, not a newly defined factorial surrogate. -/
theorem W_eq_allCount (L : Type u) [Fintype L] (n h r m : ℕ) :
    PolytopeTrees.W L n h r m =
      allCount n h r m /
        ((n.factorial * Fintype.card L ^ n : ℕ) : ℚ) := by
  unfold PolytopeTrees.W allCount
  rw [Nat.card_eq_fintype_card]
  rw [div_right_comm]
  rw [CoreComponents.normalized_labelled_card]
  rfl

/-- The original concrete connected rooted coefficient. -/
theorem PsiHat_eq_coreCount (L : Type u) [Fintype L] (n h₀ h r m : ℕ) :
    PolytopeTrees.PsiHat L h₀ h r n m =
      coreCount n h₀ h r m /
        ((n.factorial * Fintype.card L ^ n : ℕ) : ℚ) := by
  unfold PolytopeTrees.PsiHat coreCount
  rw [Nat.card_eq_fintype_card, div_right_comm,
    normalized_connected_card]

/-- Reindex all subsets by cardinality, including the empty and full sets. -/
def subsetsByCardEquiv (n : ℕ) :
    Finset (Fin n) ≃
      (Σ k : Fin (n + 1), {A : Finset (Fin n) // A.card = k.1}) where
  toFun A := ⟨⟨A.card, by
    have hA : A.card ≤ n := by simpa using Finset.card_le_univ A
    omega⟩, ⟨A, rfl⟩⟩
  invFun X := X.2.1
  left_inv _ := rfl
  right_inv X := by
    rcases X with ⟨⟨k, hk⟩, A, hA⟩
    cases hA
    rfl

theorem sum_subsets_by_card (n : ℕ) (f : ℕ → ℚ) :
    (∑ A : Finset (Fin n), f A.card) =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℚ) * f k := by
  calc
    _ = ∑ X : (Σ k : Fin (n + 1),
        {A : Finset (Fin n) // A.card = k.1}), f X.1.1 := by
      apply Fintype.sum_equiv (subsetsByCardEquiv n)
      intro A
      rfl
    _ = ∑ k : Fin (n + 1), (Nat.choose n k.1 : ℚ) * f k.1 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        FiniteCounting.card_labelPartitions]
    _ = _ := Fin.sum_univ_eq_sum_range (fun k ↦ (Nat.choose n k : ℚ) * f k) (n + 1)

end
end PolytopeCounting.FacetPairing.ComponentConvolution
