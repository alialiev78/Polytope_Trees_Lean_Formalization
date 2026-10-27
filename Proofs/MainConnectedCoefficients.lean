module

public import Proofs.ConcreteCoreInitial
public import Proofs.CircuitRankComponents

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Concrete bivariate connected coefficients

The existing public `U` and `Psi` retain the circuit rank as an argument.
This module defines the rank-forgotten connected coefficients directly
from `UnrootedDiagram` and `RootedDiagram`, and proves their relation to
those rank strata. The rank is forced by the dart-balance equation.

The empty unrooted matching is NOT included in `VHat`: the definition of
`IsConnected` in the finite model is universal reachability and is vacuous
on an empty cell type. The explicit `n=0` clause below is therefore
necessary before forming an exponential generating series. No earlier
definition or proof is changed.
-/

namespace PolytopeTrees

open PolytopeCounting.FacetPairing
open PolytopeCounting.FacetPairing.ConcreteXi

noncomputable section

universe uL

local instance seriesUnrootedStratumFintype (n h r m b : ℕ) :
    Fintype (UnrootedStratum n h r m b) := Fintype.ofFinite _

local instance seriesRootedStratumFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedStratum n h₀ h r m b) := Fintype.ofFinite _

/-- `VHat` counts nonempty connected diagrams, not an abstract solution of
the connected PDE. -/
def VHat (L : Type uL) [Fintype L] (h r n m : ℕ) : ℚ :=
  if n = 0 then 0 else
    (Nat.card (UnrootedDiagram n h r m) : ℚ) /
      ((n.factorial * Fintype.card L ^ n : ℕ) : ℚ) / (m.factorial : ℚ)

/-- The root component is nonempty even at ordinary-cell degree zero. -/
def PsiHat (L : Type uL) [Fintype L] (h₀ h r n m : ℕ) : ℚ :=
  (Nat.card (RootedDiagram n h₀ h r m) : ℚ) /
    ((n.factorial * Fintype.card L ^ n : ℕ) : ℚ) / (m.factorial : ℚ)

@[simp] theorem VHat_zero (L : Type uL) [Fintype L] (h r m : ℕ) :
    VHat L h r 0 m = 0 := by simp [VHat]

/-- On a supported rank, the rank proof is completely determined by the
boundary and number of cells. -/
def unrootedStratumEquivDiagram (n h r m b : ℕ)
    (hs : m + 2 * (n + b) = n * h + 2) :
    UnrootedStratum n h r m b ≃ UnrootedDiagram n h r m where
  toFun P := P.1
  invFun P := ⟨P, by
    have hbal := unrooted_balance P
    change P.edgeCount + 1 = Fintype.card (UnrootedCell n) + b
    rw [card_unrootedCell]
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rootedStratumEquivDiagram (n h₀ h r m b : ℕ)
    (hs : m + 2 * (n + b) = h₀ + n * h) :
    RootedStratum n h₀ h r m b ≃ RootedDiagram n h₀ h r m where
  toFun P := P.1
  invFun P := ⟨P, by
    have hbal := rooted_balance P
    change P.edgeCount + 1 = Fintype.card (RootedCell n) + b
    rw [card_rootedCell]
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem VHat_eq_U (L : Type uL) [Fintype L] (h r n m b : ℕ)
    (hn : 0 < n) (hs : m + 2 * (n + b) = n * h + 2) :
    VHat L h r n m = U L n h r m b / (m.factorial : ℚ) := by
  have hc := Nat.card_congr (unrootedStratumEquivDiagram n h r m b hs)
  simp only [VHat, U, if_neg (Nat.ne_of_gt hn), hc]

theorem PsiHat_eq_Psi (L : Type uL) [Fintype L] (h₀ h r n m b : ℕ)
    (hs : m + 2 * (n + b) = h₀ + n * h) :
    PsiHat L h₀ h r n m = Psi L n h₀ h r m b / (m.factorial : ℚ) := by
  have hc := Nat.card_congr (rootedStratumEquivDiagram n h₀ h r m b hs)
  simp only [PsiHat, Psi, hc]

/-- Rank forgetting at `n=0` needs no support restriction: every raw core
pairing is already connected. -/
def rootedZeroDiagramEquiv (h₀ h r m : ℕ) :
    RootedDiagram 0 h₀ h r m ≃ RootedPairing 0 h₀ h r m where
  toFun P := P.raw
  invFun P := ⟨P, rootedPairing_zero_connected h₀ h r m P⟩
  left_inv P := by apply ConnectedDiagram.raw_injective; rfl
  right_inv _ := rfl

/-- Full degree-zero row, including all core self-pairings, for the actual
connected coefficient family. -/
theorem PsiHat_zero_eq_Xi (L : Type uL) [Fintype L] (h₀ h r m : ℕ) :
    PsiHat L h₀ h r 0 m = XiHatCount h h₀ r (Fintype.card L) 1 0 m := by
  have hc := Fintype.card_congr (rootedZeroDiagramEquiv h₀ h r m)
  simp [PsiHat, XiHatCount, Nat.card_eq_fintype_card, hc]

/-- Connectivity supplies a rank witness; the bivariate coefficients do
not introduce a larger class than the union of the concrete rank strata. -/
theorem unrootedDiagram_exists_rank (P : UnrootedDiagram n h r m) :
    ∃ b : ℕ, P.HasCircuitRank b := by
  refine ⟨circuitRank P.raw.pairing, ?_⟩
  exact circuitRank_spec P.raw.pairing P.connected

theorem rootedDiagram_exists_rank (P : RootedDiagram n h₀ h r m) :
    ∃ b : ℕ, P.HasCircuitRank b := by
  refine ⟨circuitRank P.raw.pairing, ?_⟩
  exact circuitRank_spec P.raw.pairing P.connected

end
end PolytopeTrees
