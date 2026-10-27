module

public import Mathlib.Tactic
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Finset.Sym
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

/-!
# Enumerating coloured facet-pairing diagrams

Finite cells carry distinguishable facet slots. Seams form an off-diagonal
partial matching of slots, each with one of `r` colours. Every unused slot is
labelled. Connectivity and circuit rank refer to the dual multigraph.
`U` and `Psi` are cardinalities divided by `n! |L|^n`; `W` also divides by `m!`.
They are symmetry-weighted counts, not unweighted geometric isomorphism counts.
The root cell and its slots are fixed. No manifold or realization hypothesis is
encoded. Theorems below give the paper's cut--join recurrences and factorial
solutions in this finite model. `sorry` occurs here only to state the challenge;
Article supplies independent proofs. See README.md for mathematical scope.
-/
namespace PolytopeCounting.FacetPairing
universe uD uC
/-- A cell together with one of its distinguishable facet slots. -/
abbrev CellDart (Cell : Type uC) (facets : Cell → ℕ) :=
  Σ c : Cell, Fin (facets c)
/-- The n globally labelled ordinary cells. -/
abbrev UnrootedCell (n : ℕ) := Fin n
/-- All ordinary facet slots. -/
abbrev Dart (n h : ℕ) := CellDart (UnrootedCell n) (fun _ ↦ h)
/-- One distinguished base cell and n ordinary cells. -/
abbrev RootedCell (n : ℕ) := Sum Unit (Fin n)
/-- The distinguished base cell. -/
def baseCell (n : ℕ) : RootedCell n := Sum.inl ()
/-- The base has h₀ slots; every ordinary cell has h slots. -/
def rootedFacets (h₀ h : ℕ) : RootedCell n → ℕ
  | Sum.inl _ => h₀
  | Sum.inr _ => h
/-- Facet slots including those of the fixed base. -/
abbrev RootedDart (n h₀ h : ℕ) := CellDart (RootedCell n) (rootedFacets h₀ h)
/-- Unordered, off-diagonal seams; no slot belongs to two seams. -/
structure PartialMatching (D : Type uD) [DecidableEq D] where
  seams : Finset (Sym2 D)
  offDiagonal : ∀ e ∈ seams, ¬e.IsDiag
  unique_incidence :
    ∀ d e, e ∈ seams → d ∈ e →
      ∀ f, f ∈ seams → d ∈ f → e = f
namespace PartialMatching
variable {D : Type uD} [DecidableEq D]
/-- The actual seams of a matching. -/
abbrev Seam (M : PartialMatching D) := {e : Sym2 D // e ∈ M.seams}
/-- The slots incident to some seam. -/
def occupied (M : PartialMatching D) : Finset D :=
  M.seams.biUnion Sym2.toFinset
/-- The slots unused by any seam. -/
abbrev Boundary (M : PartialMatching D) := {d : D // d ∉ M.occupied}
end PartialMatching
/-- A partial matching with one of r colours on every seam. -/
structure ColoredMatching (D : Type uD) [DecidableEq D] (r : ℕ) where
  matching : PartialMatching D
  color : matching.Seam → Fin r
namespace ColoredMatching
variable {D : Type uD} [DecidableEq D] {r : ℕ}
/-- The seam type of the underlying matching. -/
abbrev Seam (P : ColoredMatching D r) := P.matching.Seam
/-- The unused slots of the underlying matching. -/
abbrev Boundary (P : ColoredMatching D r) := P.matching.Boundary
/-- Number of seams. -/
def edgeCount (P : ColoredMatching D r) : ℕ := P.matching.seams.card

/-- Dual adjacency: some seam joins slots of the two cells. -/
def Adjacent {Cell : Type uC} [DecidableEq Cell] (facets : Cell → ℕ)
    (P : ColoredMatching (CellDart Cell facets) r) (u v : Cell) : Prop :=
  ∃ i : Fin (facets u), ∃ j : Fin (facets v),
    s(⟨u, i⟩, ⟨v, j⟩) ∈ P.matching.seams

/-- Dual-graph connectivity via finite edge paths. -/
def IsConnected {Cell : Type uC} [DecidableEq Cell] (facets : Cell → ℕ)
    (P : ColoredMatching (CellDart Cell facets) r) : Prop :=
  ∀ u v : Cell, Relation.ReflTransGen (P.Adjacent facets) u v
end ColoredMatching

/-- A coloured matching with a bijective labelling of all unused slots. -/
structure BoundaryLabelledPairing (D : Type uD) [DecidableEq D] (r m : ℕ) where
  pairing : ColoredMatching D r
  label : pairing.Boundary ≃ Fin m
namespace BoundaryLabelledPairing
variable {D : Type uD} [DecidableEq D] {r m : ℕ}

/-- Number of seams, independent of boundary labels. -/
def edgeCount (P : BoundaryLabelledPairing D r m) : ℕ :=
  P.pairing.edgeCount
end BoundaryLabelledPairing

/-- A boundary-labelled pairing with connected dual graph. -/
structure ConnectedDiagram (Cell : Type uC) [DecidableEq Cell]
    (facets : Cell → ℕ) (r m : ℕ) where
  raw : BoundaryLabelledPairing (CellDart Cell facets) r m
  connected : raw.pairing.IsConnected facets
namespace ConnectedDiagram
variable {Cell : Type uC} [DecidableEq Cell] {facets : Cell → ℕ} {r m : ℕ}

/-- Number of seams in the connected record. -/
def edgeCount (P : ConnectedDiagram Cell facets r m) : ℕ :=
  P.raw.edgeCount

/-- Circuit rank b, encoded by e + 1 = v + b. -/
def HasCircuitRank [Fintype Cell]
    (P : ConnectedDiagram Cell facets r m) (b : ℕ) : Prop :=
  P.edgeCount + 1 = Fintype.card Cell + b
end ConnectedDiagram

/-- Unrestricted pairing on ordinary cells. -/
abbrev UnrootedPairing (n h r m : ℕ) :=
  BoundaryLabelledPairing (Dart n h) r m

/-- Unrestricted pairing with one fixed base cell. -/
abbrev RootedPairing (n h₀ h r m : ℕ) :=
  BoundaryLabelledPairing (RootedDart n h₀ h) r m

/-- Connected ordinary-cell diagram. -/
abbrev UnrootedDiagram (n h r m : ℕ) :=
  ConnectedDiagram (UnrootedCell n) (fun _ ↦ h) r m

/-- Connected diagram containing the fixed base. -/
abbrev RootedDiagram (n h₀ h r m : ℕ) :=
  ConnectedDiagram (RootedCell n) (rootedFacets h₀ h) r m

/-- Connected ordinary-cell diagrams of specified circuit rank. -/
abbrev UnrootedStratum (n h r m b : ℕ) :=
  {P : UnrootedDiagram n h r m // P.HasCircuitRank b}

/-- Connected rooted diagrams of specified circuit rank. -/
abbrev RootedStratum (n h₀ h r m b : ℕ) :=
  {P : RootedDiagram n h₀ h r m // P.HasCircuitRank b}
end PolytopeCounting.FacetPairing
namespace PolytopeTrees
open scoped BigOperators
open PolytopeCounting.FacetPairing
noncomputable section
universe u

/-- Labelled stratum cardinality divided by the cell-renaming group order. -/
def U (L : Type u) [Fintype L] (n h r m b : ℕ) : ℚ :=
  (Nat.card (UnrootedStratum n h r m b) : ℚ) /
    ((n.factorial * Fintype.card L ^ n : ℕ) : ℚ)

/-- Rooted stratum cardinality divided by ordinary-cell renamings. -/
def Psi (L : Type u) [Fintype L] (n h₀ h r m b : ℕ) : ℚ :=
  (Nat.card (RootedStratum n h₀ h r m b) : ℚ) /
    ((n.factorial * Fintype.card L ^ n : ℕ) : ℚ)

/-- Rank-zero ordinary-cell mass at its forced boundary size. -/
def R (L : Type u) [Fintype L] (n h r : ℕ) : ℚ :=
  U L n h r ((h - 2) * n + 2) 0

/-- Rank-zero rooted mass at its forced boundary size. -/
def T (L : Type u) [Fintype L] (n h₀ h r : ℕ) : ℚ :=
  Psi L n h₀ h r (h₀ + (h - 2) * n) 0

/-- Also divide by the number of free-boundary labellings. -/
def W (L : Type u) [Fintype L] (n h r m : ℕ) : ℚ :=
  (Nat.card (UnrootedPairing n h r m) : ℚ) /
    ((n.factorial * Fintype.card L ^ n : ℕ) : ℚ) / (m.factorial : ℚ)

/-- Nonbridge deletion lowers circuit rank and exposes two slots. -/
def Uprev (L : Type u) [Fintype L] (n h r m : ℕ) : ℕ → ℚ
  | 0 => 0
  | b + 1 => U L n h r (m + 2) b

/-- The corresponding rooted nonbridge contribution. -/
def Psiprev (L : Type u) [Fintype L] (n h₀ h r m : ℕ) : ℕ → ℚ
  | 0 => 0
  | b + 1 => Psi L n h₀ h r (m + 2) b

/-- A nonempty proper ordinary-cell component size. -/
abbrev ProperSize (n : ℕ) := {k : Fin (n + 1) // 0 < k.val ∧ k.val < n}

/-- Two nonempty components, with every boundary-label and rank split. -/
def Uconv (L : Type u) [Fintype L] (n h r m b : ℕ) : ℚ :=
  ∑ k : ProperSize n, ∑ s : Fin (m + 1), ∑ p : Fin (b + 1),
    (Nat.choose m s.val : ℚ) * U L k.val h r (s.val + 1) p.val *
      U L (n - k.val) h r (m - s.val + 1) (b - p.val)

/-- Root-side and away-side components; the root side may have zero ordinary cells. -/
def Psiconv (L : Type u) [Fintype L] (n h₀ h r m b : ℕ) : ℚ :=
  ∑ k : Fin n, ∑ s : Fin (m + 1), ∑ p : Fin (b + 1),
    (Nat.choose m s.val : ℚ) * Psi L k.val h₀ h r (s.val + 1) p.val *
      U L (n - k.val) h r (m - s.val + 1) (b - p.val)
end
end PolytopeTrees
namespace PolytopeTrees
open scoped BigOperators
noncomputable section
universe u
variable (L : Type u) [Group L] [Fintype L]

/-- Connected cut--join, including closed boundaries and nontrivial stabilizers. -/
theorem U_recurrence (n h r m b : ℕ) [MulAction L (Fin h)] :
    ((n + b - 1 : ℕ) : ℚ) * U L n h r m b =
      (r : ℚ) / 2 * Uprev L n h r m b + (r : ℚ) / 2 * Uconv L n h r m b := by
  sorry

/-- Rooted cut--join; the root component may have zero ordinary cells. -/
theorem Psi_recurrence (n h₀ h r m b : ℕ) [MulAction L (Fin h)] :
    ((n + b : ℕ) : ℚ) * Psi L n h₀ h r m b =
      (r : ℚ) / 2 * Psiprev L n h₀ h r m b + (r : ℚ) * Psiconv L n h₀ h r m b := by
  sorry

/-- Statement 5.1, for the concrete rank-zero counts. -/
theorem R_recurrence (n h r : ℕ) [MulAction L (Fin h)] (hh : 2 ≤ h) (hn : 2 ≤ n) :
    ((n - 1 : ℕ) : ℚ) * R L n h r = (r : ℚ) / 2 *
      ∑ k ∈ Finset.Icc 1 (n - 1),
        (Nat.choose ((h - 2) * n + 2) ((h - 2) * k + 1) : ℚ) *
          R L k h r * R L (n - k) h r := by
  sorry

/-- Statement 5.2, with a fixed distinguished root cell. -/
theorem T_recurrence (n h₀ h r : ℕ) [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hroot : 1 ≤ h₀) (hn : 0 < n) :
    (n : ℚ) * T L n h₀ h r = (r : ℚ) *
      ∑ k ∈ Finset.range n,
        (Nat.choose ((h - 2) * n + h₀) ((h - 2) * (n - k) + 1) : ℚ) *
          T L k h₀ h r * R L (n - k) h r := by
  sorry

/-- Formula (20), including the proved one-cell initial condition. -/
theorem R_formula (n h r : ℕ) [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hr : 0 < r) (hn : 0 < n) :
    R L n h r = 1 / (r : ℚ) *
      ((h : ℚ) * (r : ℚ) / (Fintype.card L : ℚ)) ^ n *
      ((n * (h - 1)).factorial : ℚ) / (n.factorial : ℚ) := by
  sorry

/-- Formula (27), with the actual root count as initial value. -/
theorem T_formula (n h₀ h r : ℕ) [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hroot : 1 ≤ h₀) (hr : 0 < r) :
    T L n h₀ h r = T L 0 h₀ h r *
      ((h : ℚ) * (r : ℚ) / (Fintype.card L : ℚ)) ^ n *
      ((n * (h - 1) + h₀ - 1).factorial : ℚ) /
      (((h₀ - 1).factorial : ℚ) * (n.factorial : ℚ)) := by
  sorry

/-- Formula (46), with explicit parity and support. -/
theorem W_formula (n h r m e : ℕ) [MulAction L (Fin h)]
    (hs : h * n = m + 2 * e) :
    W L n h r m = 1 / ((n.factorial : ℚ) * (Fintype.card L : ℚ) ^ n) *
      ((r : ℚ) / 2) ^ e * ((h * n).factorial : ℚ) /
      ((m.factorial : ℚ) * (e.factorial : ℚ)) := by
  sorry

/-- Recurrence (43), expressed without truncated subtraction. -/
theorem W_recurrence (n h r m e : ℕ) [MulAction L (Fin h)]
    (hs : h * n = m + 2 * (e + 1)) :
    (2 * (e + 1) : ℚ) * W L n h r m =
      (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) * W L n h r (m + 2) := by
  sorry
end
end PolytopeTrees

open Filter PowerSeries
open scoped Topology BigOperators
noncomputable section
namespace PolytopeCounting.PublicNumerals
theorem two : (2 : ℕ).AtLeastTwo := Nat.instAtLeastTwoHAddOfNat 1
theorem three : (3 : ℕ).AtLeastTwo := Nat.instAtLeastTwoHAddOfNat 2
theorem four : (4 : ℕ).AtLeastTwo := Nat.instAtLeastTwoHAddOfNat 3
theorem five : (5 : ℕ).AtLeastTwo := Nat.instAtLeastTwoHAddOfNat 4
theorem six : (6 : ℕ).AtLeastTwo := Nat.instAtLeastTwoHAddOfNat 5
end PolytopeCounting.PublicNumerals
namespace PolytopeCounting.ExplicitFormulas

def normalizedTreeCoefficient
    (h : ℕ) (r : ℚ) (R : ℕ → ℚ) (n : ℕ) : ℚ :=
  r * R n / ((((h - 2) * n + 1).factorial : ℕ) : ℚ)

/-- The series with constant term zero and coefficient a_n at every positive degree. -/
def positiveSeries (a : ℕ → ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else a n)

/-- The normalized series 1 + sum_{n>0} a_n X^n. -/
def auxiliarySeries (a : ℕ → ℚ) : PowerSeries ℚ :=
  1 + positiveSeries a
end PolytopeCounting.ExplicitFormulas
namespace PolytopeCounting.ScalarAnalyticSeries

attribute [local instance 2000] NormedField.toNormedSpace
/-- F is the convergent complex Taylor expansion of f in a neighbourhood of zero. -/
def HasSeries (f : ℂ → ℂ) (F : PowerSeries ℂ) : Prop :=
  HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n F)) 0
end PolytopeCounting.ScalarAnalyticSeries
namespace PolytopeCounting.AppendixA
open ExplicitFormulas ScalarAnalyticSeries
universe u

/-- Principal complex n-th root, evaluated near one for analytic branch selection. -/
def root (n : ℕ) (z : ℂ) : ℂ := z ^ ((n : ℂ)⁻¹)

/-- The prescribed cubic summand at the origin: -i/sqrt(3). -/
def cubicBase : ℂ := -Complex.I / root 2 3

/-- Square root of t^2/4-1/27 with the prescribed imaginary value at zero. -/
def cubicDiscriminant (t : ℂ) : ℂ :=
  cubicBase ^ 3 * root 2 (1 - 27 * t ^ 2 / 4)

/-- First radicand in Cardano's formula. -/
def cubicA (t : ℂ) : ℂ := -t / 2 + cubicDiscriminant t

/-- Cube root of cubicA with value cubicBase at zero. -/
def cubicU (t : ℂ) : ℂ := cubicBase * root 3 (cubicA t / cubicBase ^ 3)

/-- Coupled second cube root, characterized by cubicU*cubicV=1/3. -/
def cubicV (t : ℂ) : ℂ := 1 / (3 * cubicU t)

/-- The sum of the coupled Cardano roots; its value at zero is zero. -/
def cubicY (t : ℂ) : ℂ := cubicU t + cubicV t

/-- Square root of 1/4-64t^3/27 with value 1/2 at zero. -/
def quarticDiscriminant (t : ℂ) : ℂ := root 2 (1 - 256 * t ^ 3 / 27) / 2

/-- First resolvent cube root, with value one at zero. -/
def quarticA (t : ℂ) : ℂ := root 3 (1 / 2 + quarticDiscriminant t)

/-- Companion resolvent cube root, selected by a*b=4t/3. -/
def quarticB (t : ℂ) : ℂ := 4 * t / (3 * quarticA t)

/-- The cubic resolvent u=a+b, satisfying u^3-4tu-1=0 near zero. -/
def quarticU (t : ℂ) : ℂ := quarticA t + quarticB t

/-- Square root of u with value one at zero. -/
def quarticK (t : ℂ) : ℂ := root 2 (quarticU t)

/-- Coefficient (k^2-1/k)/2 in the quadratic factor of the quartic. -/
def quarticL (t : ℂ) : ℂ := (quarticK t ^ 2 - 1 / quarticK t) / 2

/-- Ferrari root selected by y(0)=0. -/
def quarticY (t : ℂ) : ℂ :=
  (quarticK t - root 2 (quarticK t ^ 2 - 4 * quarticL t)) / 2

/-- The triangular branch (1-sqrt(1-4t))/2, normalized at zero. -/
def quadraticY (t : ℂ) : ℂ := (1 - root 2 (1 - 4 * t)) / 2

/-- Normalized auxiliary series constructed from the concrete finite tree counts. -/
def countingA (L : Type u) [Fintype L] (q r : ℕ) : PowerSeries ℚ :=
  auxiliarySeries (normalizedTreeCoefficient (q + 2) r
    (fun n => PolytopeTrees.R L n (q + 2) r))

/-- The lacunary counting series X*A(X^q), where q=h-2. -/
def countingY (L : Type u) [Fintype L] (q r : ℕ) (hq : q ≠ 0) : PowerSeries ℚ :=
  X * expand q hq (countingA L q r)

/-- The same rational counting series with coefficients embedded in the complex numbers. -/
def complexCountingY (L : Type u) [Fintype L] (q r : ℕ) (hq : q ≠ 0) : PowerSeries ℂ :=
  map (algebraMap ℚ ℂ) (countingY L q r hq)

/-- The formal primitive Y^(q+2)/((q+2)r)-Y^(2q+2)/(2r). -/
def formalPrimitive (q : ℕ) (r : ℚ) (Y : PowerSeries ℚ) : PowerSeries ℚ :=
  C (1 / ((q + 2 : ℚ) * r)) * Y ^ (q + 2) -
    C (1 / (2 * r)) * Y ^ (2 * q + 2)

section
attribute [local instance 2000] PolytopeCounting.PublicNumerals.two PolytopeCounting.PublicNumerals.three PolytopeCounting.PublicNumerals.four PolytopeCounting.PublicNumerals.five PolytopeCounting.PublicNumerals.six
/-- The corresponding complex function of the selected analytic branch. -/
def analyticPrimitive (q : ℕ) (r : ℚ) (f : ℂ → ℂ) (t : ℂ) : ℂ :=
  f t ^ (q + 2) / (((q : ℂ) + 2) * r) - f t ^ (2 * q + 2) / (2 * r)
end

/-- Fixed-core series T_0*Y^h0/h0!, built from the concrete initial count. -/
def countingCore (L : Type u) [Fintype L] (q r h₀ : ℕ) (hq : q ≠ 0) : PowerSeries ℚ :=
  C (PolytopeTrees.T L 0 h₀ (q + 2) r / (h₀.factorial : ℚ)) * countingY L q r hq ^ h₀

theorem cubicY_hasSeries (L : Type u) [Group L] [Fintype L]
    (r : ℕ) [MulAction L (Fin 4)] (hr : 0 < r) (hcard : Fintype.card L = 4 * r) :
    HasSeries cubicY (complexCountingY L 2 r (by decide)) := by
  sorry

theorem quarticY_hasSeries (L : Type u) [Group L] [Fintype L]
    (r : ℕ) [MulAction L (Fin 5)] (hr : 0 < r) (hcard : Fintype.card L = 5 * r) :
    HasSeries quarticY (complexCountingY L 3 r (by decide)) := by
  sorry

theorem quadraticY_hasSeries (L : Type u) [Group L] [Fintype L]
    (r : ℕ) [MulAction L (Fin 3)] (hr : 0 < r) (hcard : Fintype.card L = 3 * r) :
    HasSeries quadraticY (complexCountingY L 1 r (by decide)) := by
  sorry

theorem triangleR_hasSeries (L : Type u) [Group L] [Fintype L]
    [MulAction L (Fin 3)] (hcard : Fintype.card L = 3) :
    HasSeries (analyticPrimitive 1 1 quadraticY)
      (PowerSeries.map (algebraMap ℚ ℂ) (formalPrimitive 1 1 (countingY L 1 1 (by decide)))) := by
  sorry

theorem cubicR_hasSeries (L : Type u) [Group L] [Fintype L]
    (r : ℕ) [MulAction L (Fin 4)] (hr : 0 < r) (hcard : Fintype.card L = 4 * r) :
    HasSeries (analyticPrimitive 2 r cubicY)
      (PowerSeries.map (algebraMap ℚ ℂ) (formalPrimitive 2 r (countingY L 2 r (by decide)))) := by
  sorry

theorem quarticR_hasSeries (L : Type u) [Group L] [Fintype L]
    (r : ℕ) [MulAction L (Fin 5)] (hr : 0 < r) (hcard : Fintype.card L = 5 * r) :
    HasSeries (analyticPrimitive 3 r quarticY)
      (PowerSeries.map (algebraMap ℚ ℂ) (formalPrimitive 3 r (countingY L 3 r (by decide)))) := by
  sorry

theorem countingY_coeff (L : Type u) [Fintype L] (q r n : ℕ) (hq : q ≠ 0)
    (hn : 0 < n) :
    coeff (q * n + 1) (countingY L q r hq) =
      r * PolytopeTrees.R L n (q + 2) r / ((q * n + 1).factorial : ℚ) := by
  sorry

theorem formalPrimitive_coeff (L : Type u) [Group L] [Fintype L]
    (q r n : ℕ) (hq : q ≠ 0) [MulAction L (Fin (q + 2))]
    (hr : 0 < r) (hcard : Fintype.card L = (q + 2) * r) (hn : 0 < n) :
    coeff (q * n + 2) (formalPrimitive q r (countingY L q r hq)) =
      PolytopeTrees.R L n (q + 2) r / ((q * n + 2).factorial : ℚ) := by
  sorry

theorem formalPrimitive_coeff_zero (L : Type u) [Group L] [Fintype L]
    (q r m : ℕ) (hq : q ≠ 0) [MulAction L (Fin (q + 2))]
    (hr : 0 < r) (hcard : Fintype.card L = (q + 2) * r)
    (hm : ¬ ∃ n, 0 < n ∧ m = q * n + 2) :
    coeff m (formalPrimitive q r (countingY L q r hq)) = 0 := by
  sorry

theorem countingCore_coeff (L : Type u) [Group L] [Fintype L]
    (q r h₀ n : ℕ) (hq : q ≠ 0) [MulAction L (Fin (q + 2))]
    (hr : 0 < r) (hcard : Fintype.card L = (q + 2) * r) (hbase : 1 ≤ h₀) :
    coeff (q * n + h₀) (countingCore L q r h₀ hq) =
      PolytopeTrees.T L n h₀ (q + 2) r / ((q * n + h₀).factorial : ℚ) := by
  sorry

theorem core_hasSeries (L : Type u) [Fintype L] (q r h₀ : ℕ) (hq : q ≠ 0)
    (f : ℂ → ℂ) (hf : HasSeries f (complexCountingY L q r hq)) :
    HasSeries (fun t => ((PolytopeTrees.T L 0 h₀ (q + 2) r : ℚ) : ℂ) /
      (h₀.factorial : ℂ) * f t ^ h₀)
      (PowerSeries.map (algebraMap ℚ ℂ) (countingCore L q r h₀ hq)) := by
  sorry

theorem cubicR_derivative (r : ℚ) (hr : r ≠ 0) :
    ∀ᶠ t in 𝓝 0, HasDerivAt (analyticPrimitive 2 r cubicY) ((cubicY t - t) / r) t := by
  sorry

theorem quarticR_derivative (r : ℚ) (hr : r ≠ 0) :
    ∀ᶠ t in 𝓝 0, HasDerivAt (analyticPrimitive 3 r quarticY) ((quarticY t - t) / r) t := by
  sorry

theorem cubicY_equation (t : ℂ) : cubicY t ^ 3 = cubicY t - t := by
  sorry

theorem quarticY_eventually_equation :
    ∀ᶠ t in 𝓝 0, quarticY t ^ 4 = quarticY t - t := by
  sorry
end PolytopeCounting.AppendixA
namespace PolytopeTrees
universe u

section
attribute [local instance 2000] PolytopeCounting.PublicNumerals.two PolytopeCounting.PublicNumerals.three PolytopeCounting.PublicNumerals.four PolytopeCounting.PublicNumerals.five PolytopeCounting.PublicNumerals.six
/-- The smaller maximizing free-boundary index, rounded to the parity of N. -/
def closedMode (N r : ℕ) : ℕ :=
  N % 2 + 2 * Nat.ceil (((Real.sqrt ((r : ℝ) ^ 2 + 6 * r + 1 + 4 * r * N) -
    (3 * r + 1)) / (2 * r) - (N % 2 : ℕ)) / 2)
end

theorem W_maximum_explicit (L : Type u) [Group L] [Fintype L]
    (n h r m : ℕ) [MulAction L (Fin h)] (hr : 0 < r) :
    W L n h r m ≤ W L n h r (closedMode (h * n) r) := by
  sorry

theorem W_maximizers_explicit (L : Type u) [Group L] [Fintype L]
    (n h r m : ℕ) [MulAction L (Fin h)] (hr : 0 < r) :
    W L n h r m = W L n h r (closedMode (h * n) r) ↔
      m = closedMode (h * n) r ∨
        (m = closedMode (h * n) r + 2 ∧ h * n =
          closedMode (h * n) r + r * (closedMode (h * n) r + 1) *
            (closedMode (h * n) r + 2)) := by
  sorry
end PolytopeTrees
namespace PolytopeCounting.BinomialIdentities

/-- Literal binomial identity (29) for ordinary polytope trees. -/
def Identity29 (h n : ℕ) : Prop :=
  (2 * (n - 1) : ℚ) =
    ∑ k ∈ Finset.Icc 1 (n - 1),
      (Nat.choose ((h - 2) * n + 2) ((h - 2) * k + 1) : ℚ) *
      (Nat.choose n k : ℚ) /
      (Nat.choose (n * (h - 1)) (k * (h - 1)) : ℚ)

/-- Literal binomial identity (30) for a distinguished initial complex. -/
def Identity30 (h h₀ n : ℕ) : Prop :=
  (Nat.choose (n * (h - 1) + h₀ - 1) (h₀ - 1) : ℚ) =
    (1 / (n : ℚ)) *
      ∑ k ∈ Finset.range n,
        (Nat.choose ((h - 2) * n + h₀)
          ((h - 2) * (n - k) + 1) : ℚ) *
        (Nat.choose (k * (h - 1) + h₀ - 1) (h₀ - 1) : ℚ) *
        (Nat.choose n k : ℚ) /
        (Nat.choose (n * (h - 1)) (k * (h - 1)) : ℚ)

/-- Tetrahedral specialization of identity (29). -/
def Identity13 (n : ℕ) : Prop := Identity29 4 n

/-- Tetrahedral fixed-core specialization with h0=2*n0. -/
def Identity17 (n₀ n : ℕ) : Prop := Identity30 4 (2 * n₀) n

theorem identity29 (h n : ℕ) (hh : 2 ≤ h) (hn : 2 ≤ n) :
    Identity29 h n := by
  sorry

theorem identity30 (h h₀ n : ℕ) (hh : 2 ≤ h) (hbase : 1 ≤ h₀) (hn : 0 < n) :
    Identity30 h h₀ n := by
  sorry

theorem identity13 (n : ℕ) (hn : 2 ≤ n) : Identity13 n := by
  sorry

theorem identity17 (n₀ n : ℕ) (hn₀ : 1 ≤ n₀) (hn : 0 < n) :
    Identity17 n₀ n := by
  sorry

theorem identity29_of_identity30_one (h n : ℕ) (_hh : 2 ≤ h) (hn : 2 ≤ n)
    (h30 : Identity30 h 1 n) : Identity29 h n := by
  sorry
end PolytopeCounting.BinomialIdentities
end
namespace PolytopeCounting.AppendixA
open ExplicitFormulas ScalarAnalyticSeries
universe u
noncomputable section

theorem primitive_iteratedDeriv (L : Type u) [Group L] [Fintype L]
    (q r n : ℕ) (hq : q ≠ 0) [MulAction L (Fin (q + 2))]
    (hr : 0 < r) (hcard : Fintype.card L = (q + 2) * r) (hn : 0 < n)
    (f : ℂ → ℂ) (hf : HasSeries f (complexCountingY L q r hq)) :
    iteratedDeriv (q * n + 2) (analyticPrimitive q r f) 0 =
      (PolytopeTrees.R L n (q + 2) r : ℂ) := by
  sorry
end
end PolytopeCounting.AppendixA

/-! ## Formal exponential formula for the finite counting carriers -/
namespace PolytopeCounting.BivariateCoefficients
/-- Boundary and cell variables, respectively. -/
abbrev Series (R : Type*) := ℕ → ℕ → R
abbrev BoundarySeries := PowerSeries ℚ
abbrev CountingSeries := PowerSeries BoundarySeries
/-- Package a coefficient array without imposing an equation. -/
noncomputable def toPowerSeries (F : Series ℚ) : CountingSeries :=
  PowerSeries.mk (fun n ↦ PowerSeries.mk (F n))
end PolytopeCounting.BivariateCoefficients
namespace PolytopeTrees
noncomputable section
open PolytopeCounting.FacetPairing PolytopeCounting.BivariateCoefficients
universe uL
/-- Connected diagrams with free boundary labels forgotten; no empty component. -/
def VHat (L : Type uL) [Fintype L] (h r n m : ℕ) : ℚ :=
  if n = 0 then 0 else
    (Nat.card (UnrootedDiagram n h r m) : ℚ) /
      ((n.factorial * Fintype.card L ^ n : ℕ) : ℚ) / (m.factorial : ℚ)

/-- Generating series of all and connected finite diagrams. -/
def WSeries (L : Type uL) [Fintype L] (h r : ℕ) : CountingSeries :=
  toPowerSeries (fun n m ↦ W L n h r m)

def VSeries (L : Type uL) [Fintype L] (h r : ℕ) : CountingSeries :=
  toPowerSeries (VHat L h r)

/-- Cell pointing gives the formal differential identity. -/
theorem WSeries_derivative
    (L : Type uL) [Group L] [Fintype L] (h r : ℕ) :
    PowerSeries.derivative (WSeries L h r) =
      PowerSeries.derivative (VSeries L h r) * WSeries L h r := by
  sorry

/-- The standard formal exponential, derived from connected components. -/
theorem WSeries_eq_exp_subst_VSeries
    (L : Type uL) [Group L] [Fintype L] (h r : ℕ) :
    WSeries L h r = PowerSeries.subst (VSeries L h r)
      (PowerSeries.exp (PowerSeries ℚ)) := by
  sorry
end
end PolytopeTrees

/-! ## Corollaries 5.1 and 5.2: precise asymptotic equivalents -/
namespace PolytopeCounting.HermiteAsymptotic
/-- Ratio convergence to one. -/
def SequenceEquivalent (u v : ℕ → ℝ) : Prop :=
  Filter.Tendsto (fun n ↦ u n / v n) Filter.atTop (nhds 1)
end PolytopeCounting.HermiteAsymptotic
namespace PolytopeCounting.GeneralAsymptotics
noncomputable section
section
attribute [local instance 2000] PolytopeCounting.PublicNumerals.two PolytopeCounting.PublicNumerals.three PolytopeCounting.PublicNumerals.four PolytopeCounting.PublicNumerals.five PolytopeCounting.PublicNumerals.six
/-- Tree leading term, with boundary labels forgotten. -/
def treeUnlabelledLeading (h r tau n : ℕ) : ℝ :=
  Real.sqrt (h - 1 : ℝ) /
      ((r : ℝ) * Real.sqrt (2 * Real.pi) *
        Real.rpow (h - 2 : ℝ) (5 / 2 : ℝ)) *
    Real.rpow (n : ℝ) (-5 / 2 : ℝ) *
    ((((h * r : ℕ) : ℝ) / (tau : ℝ)) *
      Real.rpow (h - 1 : ℝ) (h - 1 : ℝ) /
      Real.rpow (h - 2 : ℝ) (h - 2 : ℝ)) ^ n
end

section
attribute [local instance 2000] PolytopeCounting.PublicNumerals.two PolytopeCounting.PublicNumerals.three PolytopeCounting.PublicNumerals.four PolytopeCounting.PublicNumerals.five PolytopeCounting.PublicNumerals.six
/-- Fixed-core leading term with its actual initial mass. -/
def fixedCoreUnlabelledLeading
    (T₀ : ℝ) (h₀ h r tau n : ℕ) : ℝ :=
  T₀ *
    Real.rpow (h - 1 : ℝ) (h₀ - (1 / 2 : ℝ)) /
      (((h₀ - 1).factorial : ℝ) * Real.sqrt (2 * Real.pi) *
        Real.rpow (h - 2 : ℝ) (h₀ + (1 / 2 : ℝ))) *
    Real.rpow (n : ℝ) (-3 / 2 : ℝ) *
    ((((h * r : ℕ) : ℝ) / (tau : ℝ)) *
      Real.rpow (h - 1 : ℝ) (h - 1 : ℝ) /
      Real.rpow (h - 2 : ℝ) (h - 2 : ℝ)) ^ n
end
end
end PolytopeCounting.GeneralAsymptotics
namespace PolytopeTrees
noncomputable section
open PolytopeCounting.GeneralAsymptotics PolytopeCounting.HermiteAsymptotic
universe u
/-- The finite tree and fixed-core masses divided by boundary factorials. -/
def RBoundaryReal (L : Type u) [Fintype L] (h r n : ℕ) : ℝ :=
  (R L n h r : ℝ) / (((h - 2) * n + 2).factorial : ℝ)

def TBoundaryReal (L : Type u) [Fintype L] (h₀ h r n : ℕ) : ℝ :=
  (T L n h₀ h r : ℝ) / (((h - 2) * n + h₀).factorial : ℝ)

theorem RBoundaryReal_asymptotic (L : Type u) [Group L] [Fintype L]
    (h r : ℕ) [MulAction L (Fin h)] (hh : 3 ≤ h) (hr : 0 < r) :
    SequenceEquivalent (RBoundaryReal L h r)
      (treeUnlabelledLeading h r (Fintype.card L)) := by
  sorry

theorem TBoundaryReal_asymptotic (L : Type u) [Group L] [Fintype L]
    (h₀ h r : ℕ) [MulAction L (Fin h)]
    (hh₀ : 1 ≤ h₀) (hh : 3 ≤ h) (hr : 0 < r) :
    SequenceEquivalent (TBoundaryReal L h₀ h r)
      (fixedCoreUnlabelledLeading (T L 0 h₀ h r : ℝ)
        h₀ h r (Fintype.card L)) := by
  sorry
end
end PolytopeTrees

/-! ## Ordinary triangulation classes: Corollary 5.3 -/
namespace PolytopeCounting.FinitePermutationExtension

/-- Extend a permutation of the actual N vertices by the identity outside
that finite vertex set. This is not a restriction on allowed graph isomorphisms. -/
def extendedMap {N : ℕ} (e : Equiv.Perm (Fin N)) (x : ℕ) : ℕ :=
  if h : x < N then (e ⟨x, h⟩).val else x

@[simp] theorem extendedMap_of_lt {N : ℕ} (e : Equiv.Perm (Fin N))
    (x : ℕ) (hx : x < N) : extendedMap e x = (e ⟨x, hx⟩).val := by
  simp [extendedMap, hx]

@[simp] theorem extendedMap_of_ge {N : ℕ} (e : Equiv.Perm (Fin N))
    (x : ℕ) (hx : N ≤ x) : extendedMap e x = x := by
  simp [extendedMap, show ¬x < N from Nat.not_lt.mpr hx]

theorem extendedMap_inverse {N : ℕ} (e : Equiv.Perm (Fin N)) (x : ℕ) :
    extendedMap e.symm (extendedMap e x) = x := by
  by_cases hx : x < N
  · have he : (e ⟨x, hx⟩).val < N := (e ⟨x, hx⟩).isLt
    simp only [extendedMap_of_lt e x hx, extendedMap_of_lt e.symm _ he]
    simp
  · have hg : N ≤ x := Nat.le_of_not_gt hx
    simp [extendedMap_of_ge e x hg, extendedMap_of_ge e.symm x hg]

def extend {N : ℕ} (e : Equiv.Perm (Fin N)) : Equiv.Perm ℕ where
  toFun := extendedMap e
  invFun := extendedMap e.symm
  left_inv := extendedMap_inverse e
  right_inv := extendedMap_inverse e.symm

@[simp] theorem extend_apply_lt {N : ℕ} (e : Equiv.Perm (Fin N))
    (x : ℕ) (hx : x < N) : extend e x = (e ⟨x, hx⟩).val := extendedMap_of_lt e x hx

@[simp] theorem extend_apply_ge {N : ℕ} (e : Equiv.Perm (Fin N))
    (x : ℕ) (hx : N ≤ x) : extend e x = x := extendedMap_of_ge e x hx

@[simp] theorem extend_refl (N : ℕ) : extend (Equiv.refl (Fin N)) = Equiv.refl ℕ := by
  ext x
  by_cases hx : x < N <;> simp [extend, extendedMap, hx]

@[simp] theorem extend_symm {N : ℕ} (e : Equiv.Perm (Fin N)) :
    extend e.symm = (extend e).symm := rfl

@[simp] theorem extend_trans {N : ℕ} (e f : Equiv.Perm (Fin N)) :
    extend (e.trans f) = (extend e).trans (extend f) := by
  ext x
  by_cases hx : x < N
  · have he := (e ⟨x, hx⟩).isLt
    simp [Equiv.trans_apply, extend_apply_lt e x hx, extend_apply_lt f _ he,
      extend_apply_lt (e.trans f) x hx]
  · have hg : N ≤ x := Nat.le_of_not_gt hx
    simp [Equiv.trans_apply, extend_apply_ge e x hg, extend_apply_ge f x hg,
      extend_apply_ge (e.trans f) x hg]
end PolytopeCounting.FinitePermutationExtension
namespace PolytopeCounting.RelabellingCardinality
noncomputable section
variable {W V O : Type*} [Fintype W] [Fintype V] [Fintype O]

/-- A concrete isomorphism witness is a permutation of the vertex set. -/
structure Isomorphisms (W V : Type*) where
  IsoAt : W → W → Equiv.Perm V → Prop
  identity : ∀ w, IsoAt w w (Equiv.refl V)
  inverse : ∀ {w u e}, IsoAt w u e → IsoAt u w e.symm
  compose : ∀ {w u z e f}, IsoAt w u e → IsoAt u z f → IsoAt w z (e.trans f)

def isoSetoid (I : Isomorphisms W V) : Setoid W where
  r w u := ∃ e, I.IsoAt w u e
  iseqv := ⟨fun w => ⟨Equiv.refl V, I.identity w⟩,
    by rintro w u ⟨e, he⟩; exact ⟨e.symm, I.inverse he⟩,
    by rintro w u z ⟨e, he⟩ ⟨f, hf⟩; exact ⟨e.trans f, I.compose he hf⟩⟩

abbrev Classes (I : Isomorphisms W V) := Quotient (isoSetoid I)

instance classesFinite (I : Isomorphisms W V) : Fintype (Classes I) := Fintype.ofFinite _
end
end PolytopeCounting.RelabellingCardinality
namespace PolytopeCounting.IntrinsicStellar
noncomputable section
open PolytopeCounting.RelabellingCardinality PolytopeCounting.FinitePermutationExtension
/-- Maximal simplices of a finite abstract simplicial complex. -/
abbrev Facets := Finset (Finset ℕ)
/-- Its vertex set, pure simplex size and a bound on its vertex labels. -/
def support (K : Facets) : Finset ℕ := K.biUnion id

def Pure (K : Facets) (q : ℕ) : Prop := ∀ T ∈ K, T.card = q

def Bounded (K : Facets) (p : ℕ) : Prop := ∀ T ∈ K, ∀ x ∈ T, x < p

/-- The usual barycentric realization, with the induced product topology. -/
abbrev Coordinates := ℕ → ℝ

def InSimplex (S : Finset ℕ) (x : Coordinates) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∑ i ∈ S, x i) = 1 ∧ ∀ i ∉ S, x i = 0

def InCarrier (K : Facets) (x : Coordinates) : Prop :=
  ∃ S ∈ K, InSimplex S x

abbrev Realization (K : Facets) := {x : Coordinates // InCarrier K x}

def rename (e : Equiv.Perm ℕ) (K : Facets) : Facets :=
  K.image (fun S => S.image e)

@[simp] theorem rename_refl (K : Facets) : rename (Equiv.refl ℕ) K = K := by
  simp [rename]

theorem rename_trans (e f : Equiv.Perm ℕ) (K : Facets) :
    rename f (rename e K) = rename (e.trans f) K := by
  simp [rename, Finset.image_image, Function.comp_def]

@[simp] theorem rename_inverse (e : Equiv.Perm ℕ) (K : Facets) :
    rename e.symm (rename e K) = K := by
  simp [rename, Finset.image_image, Function.comp_def]

/-- All facet families on the specified labelled vertex set. -/
def allFacetFamilies (N : ℕ) : Finset Facets := ((Finset.range N).powerset).powerset

abbrev BoundedFamilies (N : ℕ) := {K : Facets // K ∈ allFacetFamilies N}

/-- These are presentations of ordinary abstract simplicial triangulations,
not quotient spaces of arbitrary facet pairings. -/
def Triangulation (M : Type*) [TopologicalSpace M] (N q : ℕ) :=
  {K : BoundedFamilies N // Pure K.1 q ∧ support K.1 = Finset.range N ∧
    Nonempty (Realization K.1 ≃ₜ M)}

instance triangulationFintype (M : Type*) [TopologicalSpace M] (N q : ℕ) :
    Fintype (Triangulation M N q) := by
  classical
  unfold Triangulation
  exact Fintype.ofFinite _

def triangulationIsomorphisms (M : Type*) [TopologicalSpace M] (N q : ℕ) :
    Isomorphisms (Triangulation M N q) (Fin N) where
  IsoAt K L e := rename (extend e) K.1.1 = L.1.1
  identity K := by simp
  inverse := by
    intro K L e he
    have hh := congrArg (rename (extend e).symm) he
    simpa using hh.symm
  compose := by
    intro K L J e f he hf
    rw [extend_trans, ← rename_trans, he, hf]

/-- Ordinary number of simplicial isomorphism classes. No symmetry weights. -/
def triangulationCount (M : Type*) [TopologicalSpace M] (N q : ℕ) : ℕ :=
  Fintype.card (Classes (triangulationIsomorphisms M N q))

/-- Exact lower bound for ordinary isomorphism classes, in dimension >= 2. -/
theorem corollary53_from_initial_triangulation {M : Type*} [TopologicalSpace M]
    (K : Facets) (S : Finset ℕ) (v : ℕ)
    (hS : S ∈ K) (hcard : 3 ≤ S.card) (hpure : Pure K S.card)
    (hb : Bounded K v) (hsupp : support K = Finset.range v)
    (hM : Realization K ≃ₜ M) (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ (n - 1) / (v + n : ℝ) ^ v ≤
      (triangulationCount M (v + n) S.card : ℝ) := by
  sorry

/-- Every base strictly between one and two is an eventual lower bound. -/
theorem corollary53_eventually {M : Type*} [TopologicalSpace M]
    (K : Facets) (S : Finset ℕ) (v : ℕ)
    (hS : S ∈ K) (hcard : 3 ≤ S.card) (hpure : Pure K S.card)
    (hb : Bounded K v) (hsupp : support K = Finset.range v)
    (hM : Realization K ≃ₜ M) (c : ℝ) (hc : 1 < c) (hc2 : c < 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      c ^ n ≤ (triangulationCount M (v + n) S.card : ℝ) := by
  sorry
end
end PolytopeCounting.IntrinsicStellar

/-! ## Geometric meaning: unique extension of all intrinsic facet maps -/
namespace PolytopeCounting.FacetPairing.EuclideanGeometry
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
section
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]
/-- All ambient Euclidean isometries preserving the vertex set. -/
def symmetryGroup (s : Finset E) : Subgroup (E ≃ᵃⁱ[ℝ] E) where
  carrier := {g | ∀ x, g x ∈ s ↔ x ∈ s}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro g k hg hk x
    exact (hg (k x)).trans (hk x)
  inv_mem' := by
    intro g hg x
    exact (hg (g.symm x)).symm.trans (by rw [g.apply_symm_apply])

/-- Vertices regarded as points in their intrinsic affine span. -/
def spanVertices (t : Finset E) : Finset (affineSpan ℝ (t : Set E)) :=
  t.attach.map ⟨fun x ↦ ⟨x.1, subset_affineSpan ℝ (t : Set E) x.2⟩, by
    intro x y he
    exact Subtype.ext (congrArg (fun z : affineSpan ℝ (t : Set E) ↦ (z : E)) he)⟩
namespace GeometricFlags
/-- Nonempty proper face exposed by an affine functional. The maximum has been
normalized to zero; this entails no restriction on supporting hyperplanes. -/
def Supported (s t : Finset E) : Prop :=
  t.Nonempty ∧ ∃ f : E →ᵃ[ℝ] ℝ,
    (∀ x ∈ s, f x ≤ 0) ∧
    (∀ x, x ∈ t ↔ x ∈ s ∧ f x = 0) ∧
    ∃ x ∈ s, f x < 0

/-- The usual relative facet: a maximal proper supporting face. -/
def Facet (s t : Finset E) : Prop :=
  Supported s t ∧ ∀ u, Supported s u → t ⊆ u → u = t

theorem Supported.subset {s t : Finset E} (H : Supported s t) : t ⊆ s := by
  rcases H with ⟨_, f, _, hv, _⟩
  intro x hx
  exact ((hv x).mp hx).1

/-- Complete flags consist of actual facets down to a singleton. -/
inductive CompleteChain : List (Finset E) → Prop
  | point (x : E) : CompleteChain [{x}]
  | step {s t : Finset E} {l : List (Finset E)}
      (facet : Facet s t) (tail : CompleteChain (t :: l)) :
      CompleteChain (s :: t :: l)

def FullFlag (s : Finset E) := {l : List (Finset E) // CompleteChain (s :: l)}

theorem Facet.span_nonempty {s t : Finset E} (H : Facet s t) : Nonempty (affineSpan ℝ (t : Set E)) := by
  obtain ⟨p, hp⟩ := H.1.1
  exact ⟨⟨p, subset_affineSpan ℝ _ hp⟩⟩
end GeometricFlags
end
section
variable {V E W E' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MetricSpace E'] [NormedAddTorsor W E']
namespace GeometricFlags
/-- Ordinary image of a list of face vertex sets. -/
def mapChain (f : E → E') (l : List (Finset E)) : List (Finset E') :=
  l.map (fun s ↦ s.image f)

/-- Transitivity on all complete face flags of the actual vertex configuration. -/
def IsFlagRegular (s : Finset E) : Prop :=
  ∀ A B : FullFlag s, ∃ g : symmetryGroup s,
    mapChain g.1 (s :: A.1) = s :: B.1
end GeometricFlags
end
universe u
variable {V P : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]
namespace GeometricFlags
/-- The finite set of actual facets, with a canonical finite indexing. -/
def facetSets (s : Finset P) : Finset (Finset P) := s.powerset.filter (Facet s)
abbrev Facets (s : Finset P) := {t : Finset P // t ∈ facetSets s}

@[simp] theorem mem_facetSets {s t : Finset P} : t ∈ facetSets s ↔ Facet s t := by
  exact ⟨fun h ↦ (Finset.mem_filter.mp h).2,
    fun h ↦ Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1.subset, h⟩⟩

def Facets.ofFacet {s t : Finset P} (H : Facet s t) : Facets s :=
  ⟨t, mem_facetSets.mpr H⟩

theorem Facets.isFacet {s : Finset P} (t : Facets s) : Facet s t.1 :=
  mem_facetSets.mp t.2

/-- Indexing is of the actual finite facet set, not an input list of slots. -/
abbrev facetCount (s : Finset P) : ℕ := Fintype.card (Facets s)
def facetIndex (s : Finset P) : Facets s ≃ Fin (facetCount s) := Fintype.equivFin _
end GeometricFlags
/-- The geometric input includes only finite spanning vertices, flag transitivity,
and dimension at least two. A palette or extension certificate is not an input. -/
structure RegularCell (V P : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V] where
  vertices : Finset P
  nonempty : vertices.Nonempty
  full_span : affineSpan ℝ (vertices : Set P) = ⊤
  regular : GeometricFlags.IsFlagRegular vertices
  dimension : 2 ≤ Module.finrank ℝ V
namespace RegularCell
variable [FiniteDimensional ℝ V] (K : RegularCell V P)
open GeometricFlags
abbrev Group := symmetryGroup K.vertices
abbrev h := GeometricFlags.facetCount K.vertices
/-- The vertices and intrinsic space of each actual facet. -/
def facetVertices (i : Fin K.h) : Finset P := ((facetIndex K.vertices).symm i).1

theorem facet_property (i : Fin K.h) : Facet K.vertices (K.facetVertices i) :=
  ((facetIndex K.vertices).symm i).isFacet

abbrev FacetSpace (i : Fin K.h) := affineSpan ℝ (K.facetVertices i : Set P)

instance facetSpaceNonempty (i : Fin K.h) : Nonempty (K.FacetSpace i) :=
  (K.facet_property i).span_nonempty

/-- All affine isometries preserving the vertex sets of the two intrinsic
facets. There is no assumed ambient extension in this definition. -/
abbrev IntrinsicMap (i j : Fin K.h) :=
  {f : K.FacetSpace i ≃ᵃⁱ[ℝ] K.FacetSpace j //
    ∀ x, f x ∈ spanVertices (K.facetVertices j) ↔
      x ∈ spanVertices (K.facetVertices i)}

/-- Exactly one ambient symmetry extends each such intrinsic isometry. -/
theorem facet_isometry_extends_uniquely 
    (i j : Fin K.h) (f : K.IntrinsicMap i j) :
    ∃! g : K.Group, ∀ x : K.FacetSpace i, (f.1 x : P) = g.1 x := by
  sorry
end RegularCell
end
end PolytopeCounting.FacetPairing.EuclideanGeometry
namespace PolytopeCounting.HermiteAsymptotic
noncomputable section
section
attribute [local instance 2000] PolytopeCounting.PublicNumerals.two PolytopeCounting.PublicNumerals.three PolytopeCounting.PublicNumerals.four PolytopeCounting.PublicNumerals.five PolytopeCounting.PublicNumerals.six
/-- The explicit leading term of Statement 6.4. -/
def statement64LeadingTerm
    (h n : ℕ) (r tau : ℝ) : ℝ :=
  1 / (2 * Real.sqrt (Real.pi * (n : ℝ))) *
    Real.exp (-1 / (4 * r)) *
    (Real.rpow (r * (h : ℝ)) ((h : ℝ) / 2) *
        Real.exp (1 - (h : ℝ) / 2) / tau) ^ n *
    Real.rpow (n : ℝ) ((n : ℝ) * ((h : ℝ) / 2 - 1)) *
    Real.exp (Real.sqrt (((h * n : ℕ) : ℝ) / r))
end
end
end PolytopeCounting.HermiteAsymptotic
namespace PolytopeTrees
noncomputable section
open PolytopeCounting
universe u
/-- Unconditional disconnected asymptotic for the finite counts. -/
theorem W_total_asymptotic (L : Type u) [Group L] [Fintype L]
    (h r : ℕ) [MulAction L (Fin h)] (hh : 0 < h) (hr : 0 < r) :
    HermiteAsymptotic.SequenceEquivalent
      (fun n ↦ ((∑ e ∈ Finset.range (h * n / 2 + 1),
        W L n h r (h * n - 2 * e) : ℚ) : ℝ))
      (fun n ↦ HermiteAsymptotic.statement64LeadingTerm
        h n (r : ℝ) (Fintype.card L : ℝ)) := by
  sorry
end
end PolytopeTrees
