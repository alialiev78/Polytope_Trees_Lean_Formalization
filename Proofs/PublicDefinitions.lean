module

public import Proofs.FacetPairingModel
public import Mathlib.Tactic

@[expose] public section

namespace PolytopeTrees
open scoped BigOperators
open PolytopeCounting.FacetPairing
noncomputable section
universe u

/-- Labelled stratum cardinality divided by the cell-renaming group order. -/
def U (L : Type u) [Fintype L] (n h r m b : ℕ) : ℚ :=
  (Nat.card (UnrootedStratum n h r m b) : ℚ) /
    ((n.factorial * Fintype.card L ^ n : ℕ) : ℚ)

def Psi (L : Type u) [Fintype L] (n h₀ h r m b : ℕ) : ℚ :=
  (Nat.card (RootedStratum n h₀ h r m b) : ℚ) /
    ((n.factorial * Fintype.card L ^ n : ℕ) : ℚ)

def R (L : Type u) [Fintype L] (n h r : ℕ) : ℚ :=
  U L n h r ((h - 2) * n + 2) 0

def T (L : Type u) [Fintype L] (n h₀ h r : ℕ) : ℚ :=
  Psi L n h₀ h r (h₀ + (h - 2) * n) 0

/-- Also divide by the number of free-boundary labellings. -/
def W (L : Type u) [Fintype L] (n h r m : ℕ) : ℚ :=
  (Nat.card (UnrootedPairing n h r m) : ℚ) /
    ((n.factorial * Fintype.card L ^ n : ℕ) : ℚ) / (m.factorial : ℚ)

def Uprev (L : Type u) [Fintype L] (n h r m : ℕ) : ℕ → ℚ
  | 0 => 0
  | b + 1 => U L n h r (m + 2) b

def Psiprev (L : Type u) [Fintype L] (n h₀ h r m : ℕ) : ℕ → ℚ
  | 0 => 0
  | b + 1 => Psi L n h₀ h r (m + 2) b

abbrev ProperSize (n : ℕ) := {k : Fin (n + 1) // 0 < k.val ∧ k.val < n}

def Uconv (L : Type u) [Fintype L] (n h r m b : ℕ) : ℚ :=
  ∑ k : ProperSize n, ∑ s : Fin (m + 1), ∑ p : Fin (b + 1),
    (Nat.choose m s.val : ℚ) * U L k.val h r (s.val + 1) p.val *
      U L (n - k.val) h r (m - s.val + 1) (b - p.val)

def Psiconv (L : Type u) [Fintype L] (n h₀ h r m b : ℕ) : ℚ :=
  ∑ k : Fin n, ∑ s : Fin (m + 1), ∑ p : Fin (b + 1),
    (Nat.choose m s.val : ℚ) * Psi L k.val h₀ h r (s.val + 1) p.val *
      U L (n - k.val) h r (m - s.val + 1) (b - p.val)
end
end PolytopeTrees
