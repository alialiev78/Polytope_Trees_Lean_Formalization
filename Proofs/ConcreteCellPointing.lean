module

public import Proofs.ConcreteXiConvolution

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Pointing one ordinary cell and the exponential differential equation

A core with `h` slots is an ordinary cell distinguished from the other `n`
cells. Reindexing its slots with the canonical `(n+1)`-cell carrier gives
`Xi_n = tau*(n+1)*W_(n+1)` and `Psi_n = tau*(n+1)*V_(n+1)`.
The already proved concrete Xi convolution therefore supplies `W' = V'*W`.
This is an identity for the actual finite coefficients, not a supplied
logarithmic-derivative hypothesis.
-/

namespace PolytopeCounting.FacetPairing.ComponentConvolution

noncomputable section
attribute [local instance] Classical.propDecidable

open RootedNumericalBridgeCoproduct (cellDartEquiv)

/-- The distinguished cell is placed at index zero. -/
def pointedCellEquiv (n : ℕ) : RootedCell n ≃ Fin (n + 1) where
  toFun c := match c with
    | Sum.inl _ => 0
    | Sum.inr i => i.succ
  invFun j := Fin.cases (Sum.inl ()) (fun i ↦ Sum.inr i) j
  left_inv c := by
    rcases c with u | i
    · cases u; rfl
    · rfl
  right_inv j := by
    refine Fin.cases ?_ (fun i ↦ ?_) j <;> rfl

def pointedFacetEquiv (n h : ℕ) (c : RootedCell n) :
    Fin (rootedFacets h h c) ≃ Fin h := by
  cases c <;> exact Equiv.refl _

def pointedDartEquiv (n h : ℕ) : RootedDart n h h ≃ Dart (n + 1) h :=
  cellDartEquiv (pointedCellEquiv n) (pointedFacetEquiv n h)

def pointedPairingEquiv (n h r m : ℕ) :
    RootedPairing n h h r m ≃ UnrootedPairing (n + 1) h r m :=
  BoundaryLabelledPairing.reindexEquiv (pointedDartEquiv n h)

/-- Preserve connectedness, seam colours, and all boundary labels. -/
def pointedDiagramEquiv (n h r m : ℕ) :
    RootedDiagram n h h r m ≃ UnrootedDiagram (n + 1) h r m :=
  (connectedDataEquiv (RootedCell n) (rootedFacets h h) r m).trans
    ((Equiv.sigmaCongr
      (connectedRawEquiv (pointedCellEquiv n) (pointedFacetEquiv n h) r)
      (fun P ↦ BoundaryLabelledPairing.labelTransportEquiv
        (P.1.matching.boundaryReindexEquiv (pointedDartEquiv n h)))).trans
      (connectedDataEquiv (Fin (n + 1)) (fun _ ↦ h) r m).symm)

/-- Exact arithmetic of the additional pointed ordinary cell. -/
theorem pointed_normalization (tau n m : ℕ) (htau : 0 < tau) (A : ℚ) :
    A / ((n.factorial * tau ^ n : ℕ) : ℚ) / (m.factorial : ℚ) =
      (tau : ℚ) * ((n + 1 : ℕ) : ℚ) *
        (A / (((n + 1).factorial * tau ^ (n + 1) : ℕ) : ℚ) /
          (m.factorial : ℚ)) := by
  have ht : (tau : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt htau
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  have htp : (tau : ℚ) ^ n ≠ 0 := pow_ne_zero n ht
  simp only [Nat.factorial_succ, pow_succ, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one]
  field_simp [ht, hf, hm, hn, htp]
  <;> ring

end
end PolytopeCounting.FacetPairing.ComponentConvolution

namespace PolytopeTrees

noncomputable section

open scoped BigOperators
open PolytopeCounting
open PolytopeCounting.FacetPairing
open PolytopeCounting.FacetPairing.ComponentConvolution
open PolytopeCounting.BivariateCoefficients

universe uL

/-- Pointing in the actual unrestricted carrier. -/
theorem Xi_equal_cell_pointing
    (L : Type uL) [Group L] [Fintype L] (n h r m : ℕ) :
    ConcreteXi.XiHatCount h h r (Fintype.card L) 1 n m =
      (Fintype.card L : ℚ) * ((n + 1 : ℕ) : ℚ) * W L (n + 1) h r m := by
  have hc := Fintype.card_congr (pointedPairingEquiv n h r m)
  unfold ConcreteXi.XiHatCount W
  rw [Nat.card_eq_fintype_card, hc]
  simpa only [Nat.cast_mul, Nat.cast_pow, one_div, one_mul, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using
    pointed_normalization (Fintype.card L) n m Fintype.card_pos
      (Fintype.card (UnrootedPairing (n + 1) h r m) : ℚ)

/-- Pointing in the actual nonempty connected carrier. -/
theorem Psi_equal_cell_pointing
    (L : Type uL) [Group L] [Fintype L] (n h r m : ℕ) :
    PsiHat L h h r n m =
      (Fintype.card L : ℚ) * ((n + 1 : ℕ) : ℚ) *
        VHat L h r (n + 1) m := by
  have hc := Fintype.card_congr (pointedDiagramEquiv n h r m)
  unfold PsiHat VHat
  rw [if_neg (by omega : n + 1 ≠ 0)]
  simp only [Nat.card_eq_fintype_card, hc]
  exact pointed_normalization (Fintype.card L) n m Fintype.card_pos _

/-- The empty unrestricted configuration contributes one. There are no
positive-boundary configurations on zero ordinary cells. -/
theorem W_zero_row (L : Type uL) [Fintype L] (h r m : ℕ) :
    W L 0 h r m = if m = 0 then 1 else 0 := by
  classical
  by_cases hm : m = 0
  · subst m
    have hc : Fintype.card (UnrootedPairing 0 h r 0) = 1 := by
      simpa using DisconnectedTop.card_unrootedPairing_top 0 h r
    simp [W, Nat.card_eq_fintype_card, hc]
  · letI : IsEmpty (UnrootedPairing 0 h r m) := ⟨fun P ↦ by
      have hb := P.boundary_balance
      rw [card_dart] at hb
      omega⟩
    simp [W, Nat.card_eq_fintype_card, Fintype.card_eq_zero, hm]

/-- Exact coefficient equation `dW/dt0 = (dV/dt0) W`. It follows from
one-cell pointing and the concrete Xi convolution. -/
theorem W_cell_derivative_convolution
    (L : Type uL) [Group L] [Fintype L] (h r n m : ℕ) :
    ((n + 1 : ℕ) : ℚ) * W L (n + 1) h r m =
      ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        ((k + 1 : ℕ) : ℚ) * VHat L h r (k + 1) j *
          W L (n - k) h r (m - j) := by
  have hx := XiHatCount_convolution L h h r 1 n m
  rw [Xi_equal_cell_pointing, one_mul] at hx
  simp only [convolution, Psi_equal_cell_pointing] at hx
  have ht : (Fintype.card L : ℚ) ≠ 0 := by
    have htN : 0 < Fintype.card L := Fintype.card_pos
    exact_mod_cast (Nat.ne_of_gt htN)
  apply mul_left_cancel₀ ht
  calc
    (Fintype.card L : ℚ) * (((n + 1 : ℕ) : ℚ) * W L (n + 1) h r m) =
        (Fintype.card L : ℚ) * ((n + 1 : ℕ) : ℚ) * W L (n + 1) h r m := by ring
    _ = _ := hx
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring

end
end PolytopeTrees
