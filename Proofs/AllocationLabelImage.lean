module

public import Proofs.NumericalBridgeCut

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Images of allocation-reassembled boundary labels

The inverse global bridge construction labels the two component boundaries
by a chosen finite block and its literal complement, then reassembles them.
This file proves once and for all that the two resulting label images are
exactly those two blocks.  The statements are independent of connectivity,
rank, and the later star join.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace AllocationLabelImage

noncomputable section

universe uCell

variable {Cell : Type uCell} [Fintype Cell] [DecidableEq Cell]
  {facets : Cell → ℕ} {r N : ℕ}

@[simp]
theorem equivFinsetImage_val
    {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (x : A) :
    (NumericalBridgeCut.equivFinsetImage f hf x).1 = f x := by
  rfl

/-- A finite set and its literal complement as a disjoint-sum equivalence. -/
def sumComplementEquiv (A : Finset (Fin N)) :
    {i : Fin N // i ∈ A} ⊕ {i : Fin N // i ∉ A} ≃ Fin N where
  toFun z := z.elim Subtype.val Subtype.val
  invFun i := if hi : i ∈ A then Sum.inl ⟨i, hi⟩ else Sum.inr ⟨i, hi⟩
  left_inv z := by
    rcases z with i | i
    · simp [i.2]
    · simp [i.2]
  right_inv i := by
    by_cases hi : i ∈ A <;> simp [hi]

/-- Reassemble component boundary labels whose codomains are a block and
its complement. -/
def reassembledAllocationLabel
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (A : Finset (Fin N))
    (leftLabel : P.Boundary ≃ {i : Fin N // i ∈ A})
    (rightLabel : Q.Boundary ≃ {i : Fin N // i ∉ A}) :
    (reassembleColored S T hdisj P Q).Boundary ≃ Fin N :=
  (boundaryReassembleEquiv S T hcover hdisj P Q).trans <|
    (Equiv.sumCongr leftLabel rightLabel).trans (sumComplementEquiv A)

@[simp]
theorem reassembledAllocationLabel_includeLeft
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (A : Finset (Fin N))
    (leftLabel : P.Boundary ≃ {i : Fin N // i ∈ A})
    (rightLabel : Q.Boundary ≃ {i : Fin N // i ∉ A})
    (x : P.Boundary) :
    reassembledAllocationLabel S T hcover hdisj P Q A leftLabel rightLabel
        (includeLeftBoundary S T hdisj P Q x) =
      (leftLabel x).1 := by
  simp only [reassembledAllocationLabel, Equiv.trans_apply,
    boundaryReassembleEquiv_includeLeft, Equiv.sumCongr_apply, Sum.map_inl]
  rfl

@[simp]
theorem reassembledAllocationLabel_includeRight
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (A : Finset (Fin N))
    (leftLabel : P.Boundary ≃ {i : Fin N // i ∈ A})
    (rightLabel : Q.Boundary ≃ {i : Fin N // i ∉ A})
    (x : Q.Boundary) :
    reassembledAllocationLabel S T hcover hdisj P Q A leftLabel rightLabel
        (includeRightBoundary S T hdisj P Q x) =
      (rightLabel x).1 := by
  simp only [reassembledAllocationLabel, Equiv.trans_apply,
    boundaryReassembleEquiv_includeRight, Equiv.sumCongr_apply, Sum.map_inr]
  rfl

/-- The image of the reassembled left-component boundary labels is exactly
the chosen block. -/
theorem image_left_eq
    (S T : Set Cell) [Fintype S] [Fintype T]
    (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (A : Finset (Fin N))
    (leftLabel : P.Boundary ≃ {i : Fin N // i ∈ A})
    (rightLabel : Q.Boundary ≃ {i : Fin N // i ∉ A}) :
    Finset.univ.image (fun x : P.Boundary ↦
      reassembledAllocationLabel S T hcover hdisj P Q A leftLabel rightLabel
        (includeLeftBoundary S T hdisj P Q x)) = A := by
  ext i
  constructor
  · intro hi
    obtain ⟨x, _hx, hxi⟩ := Finset.mem_image.mp hi
    rw [reassembledAllocationLabel_includeLeft] at hxi
    simpa [← hxi] using (leftLabel x).2
  · intro hi
    let x := leftLabel.symm ⟨i, hi⟩
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ x, ?_⟩
    rw [reassembledAllocationLabel_includeLeft]
    exact congrArg Subtype.val (leftLabel.apply_symm_apply ⟨i, hi⟩)

/-- The image of the reassembled right-component boundary labels is exactly
the complement of the chosen block. -/
theorem image_right_eq
    (S T : Set Cell) [Fintype S] [Fintype T]
    (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (A : Finset (Fin N))
    (leftLabel : P.Boundary ≃ {i : Fin N // i ∈ A})
    (rightLabel : Q.Boundary ≃ {i : Fin N // i ∉ A}) :
    Finset.univ.image (fun x : Q.Boundary ↦
      reassembledAllocationLabel S T hcover hdisj P Q A leftLabel rightLabel
        (includeRightBoundary S T hdisj P Q x)) = Aᶜ := by
  ext i
  constructor
  · intro hi
    obtain ⟨x, _hx, hxi⟩ := Finset.mem_image.mp hi
    rw [reassembledAllocationLabel_includeRight] at hxi
    have hnot : i ∉ A := by
      intro hiA
      exact (rightLabel x).2 (hxi.symm ▸ hiA)
    simpa using hnot
  · intro hi
    have hnot : i ∉ A := by simpa using hi
    let x := rightLabel.symm ⟨i, hnot⟩
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ x, ?_⟩
    rw [reassembledAllocationLabel_includeRight]
    exact congrArg Subtype.val (rightLabel.apply_symm_apply ⟨i, hnot⟩)

/-! ## Recovery through a transported but value-preserving global label -/

/-- If a global cut label has the same value at every boundary dart as an
allocation-reassembled label, then the image of its left-component label map
is still exactly the allocated block.  This is the form used after cutting a
reconstructed star join, where the boundary subtype is transported across an
erasure equality. -/
theorem image_left_eq_of_pointwise
    (S T : Set Cell) [Fintype S] [Fintype T]
    (hcover : S ∪ T = Set.univ) (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (A : Finset (Fin N))
    (leftLabel : P.Boundary ≃ {i : Fin N // i ∈ A})
    (rightLabel : Q.Boundary ≃ {i : Fin N // i ∉ A})
    (global : (reassembleColored S T hdisj P Q).Boundary ≃ Fin N)
    (hglobal : ∀ z,
      global z = reassembledAllocationLabel S T hcover hdisj P Q A
        leftLabel rightLabel z) :
    Finset.univ.image (fun x : P.Boundary ↦
      global (includeLeftBoundary S T hdisj P Q x)) = A := by
  rw [← image_left_eq S T hcover hdisj P Q A leftLabel rightLabel]
  apply Finset.image_congr
  intro x _
  exact hglobal _

/-- Right-component counterpart of `image_left_eq_of_pointwise`. -/
theorem image_right_eq_of_pointwise
    (S T : Set Cell) [Fintype S] [Fintype T]
    (hcover : S ∪ T = Set.univ) (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (A : Finset (Fin N))
    (leftLabel : P.Boundary ≃ {i : Fin N // i ∈ A})
    (rightLabel : Q.Boundary ≃ {i : Fin N // i ∉ A})
    (global : (reassembleColored S T hdisj P Q).Boundary ≃ Fin N)
    (hglobal : ∀ z,
      global z = reassembledAllocationLabel S T hcover hdisj P Q A
        leftLabel rightLabel z) :
    Finset.univ.image (fun x : Q.Boundary ↦
      global (includeRightBoundary S T hdisj P Q x)) = Aᶜ := by
  rw [← image_right_eq S T hcover hdisj P Q A leftLabel rightLabel]
  apply Finset.image_congr
  intro x _
  exact hglobal _


end
end AllocationLabelImage
end FacetPairing
end PolytopeCounting
