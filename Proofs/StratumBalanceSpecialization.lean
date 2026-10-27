module

public import Proofs.FacetPairingModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-!
# Boundary support and tree specializations of the rank strata

The raw bridge coproduct is naturally indexed by a cell split, an old
boundary-label split, and a circuit-rank split.  Most numerical index tuples
have empty component strata.  This file makes that support condition exact.

For `h ≥ 2`, an unrooted component with `k` cells, `s+1` boundary darts and
rank `p` can exist only when

`s + 2*p = k*(h-2) + 1`.

For a rooted component with `k` ordinary cells it can exist only when

`s + 1 + 2*p = h₀ + k*(h-2)`.

The corresponding away-component equations are obtained by replacing
`k,s,p` with their complements.  We prove `IsEmpty` and exact cardinal-zero
statements for every impossible index, then use them to filter the finite
boundary convolution.  At rank zero the filter is a singleton, so the
traditional tree recurrences really do have only one boundary split for
each cell split.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace StratumBalanceSpecialization

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

local instance unrootedStratumFintype (n h r m b : ℕ) :
    Fintype (UnrootedStratum n h r m b) := Fintype.ofFinite _

local instance rootedStratumFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedStratum n h₀ h r m b) := Fintype.ofFinite _

/-! ## Subtraction-free support equations -/

/-- Conventional unrooted boundary support, valid when every ordinary cell
has at least two facet slots. -/
theorem unrooted_rank_boundary_support
    (P : UnrootedStratum n h r m b) (hh : 2 ≤ h) :
    m + 2 * b = n * (h - 2) + 2 := by
  have hbal := unrooted_rank_balance P
  have hsplit : h = (h - 2) + 2 := (Nat.sub_add_cancel hh).symm
  have hmul : n * h = n * (h - 2) + 2 * n := by
    calc
      n * h = n * ((h - 2) + 2) :=
        congrArg (fun x : ℕ ↦ n * x) hsplit
      _ = n * (h - 2) + n * 2 := Nat.mul_add _ _ _
      _ = n * (h - 2) + 2 * n := by omega
  rw [hmul] at hbal
  omega

/-- Conventional rooted boundary support.  The base contributes `h₀`
instead of the unrooted constant `2`. -/
theorem rooted_rank_boundary_support
    (P : RootedStratum n h₀ h r m b) (hh : 2 ≤ h) :
    m + 2 * b = h₀ + n * (h - 2) := by
  have hbal := rooted_rank_balance P
  have hsplit : h = (h - 2) + 2 := (Nat.sub_add_cancel hh).symm
  have hmul : n * h = n * (h - 2) + 2 * n := by
    calc
      n * h = n * ((h - 2) + 2) :=
        congrArg (fun x : ℕ ↦ n * x) hsplit
      _ = n * (h - 2) + n * 2 := Nat.mul_add _ _ _
      _ = n * (h - 2) + 2 * n := by omega
  rw [hmul] at hbal
  omega

/-! ## Empty impossible strata and exact cardinal zero -/

theorem unrootedStratum_isEmpty_of_rank_balance_ne
    (hbad : m + 2 * (n + b) ≠ n * h + 2) :
    IsEmpty (UnrootedStratum n h r m b) where
  false P := hbad (unrooted_rank_balance P)

theorem rootedStratum_isEmpty_of_rank_balance_ne
    (hbad : m + 2 * (n + b) ≠ h₀ + n * h) :
    IsEmpty (RootedStratum n h₀ h r m b) where
  false P := hbad (rooted_rank_balance P)

theorem unrootedStratum_isEmpty_of_support_ne
    (hh : 2 ≤ h)
    (hbad : m + 2 * b ≠ n * (h - 2) + 2) :
    IsEmpty (UnrootedStratum n h r m b) where
  false P := hbad (unrooted_rank_boundary_support P hh)

theorem rootedStratum_isEmpty_of_support_ne
    (hh : 2 ≤ h)
    (hbad : m + 2 * b ≠ h₀ + n * (h - 2)) :
    IsEmpty (RootedStratum n h₀ h r m b) where
  false P := hbad (rooted_rank_boundary_support P hh)

theorem card_unrootedStratum_eq_zero_of_rank_balance_ne
    (hbad : m + 2 * (n + b) ≠ n * h + 2) :
    Fintype.card (UnrootedStratum n h r m b) = 0 := by
  letI := unrootedStratum_isEmpty_of_rank_balance_ne
    (n := n) (h := h) (r := r) (m := m) (b := b) hbad
  exact Fintype.card_eq_zero

theorem card_rootedStratum_eq_zero_of_rank_balance_ne
    (hbad : m + 2 * (n + b) ≠ h₀ + n * h) :
    Fintype.card (RootedStratum n h₀ h r m b) = 0 := by
  letI := rootedStratum_isEmpty_of_rank_balance_ne
    (n := n) (h₀ := h₀) (h := h) (r := r) (m := m) (b := b) hbad
  exact Fintype.card_eq_zero

theorem card_unrootedStratum_eq_zero_of_support_ne
    (hh : 2 ≤ h)
    (hbad : m + 2 * b ≠ n * (h - 2) + 2) :
    Fintype.card (UnrootedStratum n h r m b) = 0 := by
  letI := unrootedStratum_isEmpty_of_support_ne
    (n := n) (h := h) (r := r) (m := m) (b := b) hh hbad
  exact Fintype.card_eq_zero

theorem card_rootedStratum_eq_zero_of_support_ne
    (hh : 2 ≤ h)
    (hbad : m + 2 * b ≠ h₀ + n * (h - 2)) :
    Fintype.card (RootedStratum n h₀ h r m b) = 0 := by
  letI := rootedStratum_isEmpty_of_support_ne
    (n := n) (h₀ := h₀) (h := h) (r := r) (m := m) (b := b) hh hbad
  exact Fintype.card_eq_zero

/-! ## The support equations in bridge coordinates -/

/-- An unrooted component carrying `s` old boundary labels plus one exposed
bridge endpoint has the displayed unique numerical support. -/
theorem unrooted_bridge_component_support
    (P : UnrootedStratum k h r (s + 1) p) (hh : 2 ≤ h) :
    s + 2 * p = k * (h - 2) + 1 := by
  have hsupport := unrooted_rank_boundary_support P hh
  omega

/-- The component containing the fixed base has the rooted support equation.
The `+1` on the left is its exposed bridge endpoint. -/
theorem rooted_bridge_component_support
    (P : RootedStratum k h₀ h r (s + 1) p) (hh : 2 ≤ h) :
    s + 1 + 2 * p = h₀ + k * (h - 2) := by
  exact rooted_rank_boundary_support P hh

theorem unrootedBridgeComponent_isEmpty_of_support_ne
    (hh : 2 ≤ h)
    (hbad : s + 2 * p ≠ k * (h - 2) + 1) :
    IsEmpty (UnrootedStratum k h r (s + 1) p) where
  false P := hbad (unrooted_bridge_component_support P hh)

theorem rootedBridgeComponent_isEmpty_of_support_ne
    (hh : 2 ≤ h)
    (hbad : s + 1 + 2 * p ≠ h₀ + k * (h - 2)) :
    IsEmpty (RootedStratum k h₀ h r (s + 1) p) where
  false P := hbad (rooted_bridge_component_support P hh)

theorem card_unrootedBridgeComponent_eq_zero_of_support_ne
    (hh : 2 ≤ h)
    (hbad : s + 2 * p ≠ k * (h - 2) + 1) :
    Fintype.card (UnrootedStratum k h r (s + 1) p) = 0 := by
  letI := unrootedBridgeComponent_isEmpty_of_support_ne
    (k := k) (h := h) (r := r) (s := s) (p := p) hh hbad
  exact Fintype.card_eq_zero

theorem card_rootedBridgeComponent_eq_zero_of_support_ne
    (hh : 2 ≤ h)
    (hbad : s + 1 + 2 * p ≠ h₀ + k * (h - 2)) :
    Fintype.card (RootedStratum k h₀ h r (s + 1) p) = 0 := by
  letI := rootedBridgeComponent_isEmpty_of_support_ne
    (k := k) (h₀ := h₀) (h := h) (r := r) (s := s) (p := p) hh hbad
  exact Fintype.card_eq_zero

/-! ## Tree boundary functions -/

/-- Total boundary size of an unrooted rank-zero component.  The factor
ordering agrees definitionally with the manuscript's `treeBoundary`. -/
def unrootedTreeBoundary (h k : ℕ) : ℕ := (h - 2) * k + 2

/-- Old boundary labels on an unrooted tree component after reserving its
single exposed bridge endpoint. -/
def unrootedTreeOldBoundary (h k : ℕ) : ℕ := (h - 2) * k + 1

/-- Total boundary size of the base-containing rank-zero component. -/
def rootedTreeBoundary (h₀ h k : ℕ) : ℕ := h₀ + (h - 2) * k

/-- Boundary count in unrooted circuit rank `b`, with the manuscript's
truncated-natural convention. -/
def cyclicBoundary (h n b : ℕ) : ℕ :=
  (h - 2) * n + 2 - 2 * b

/-- Rooted boundary count at circuit rank `b`. -/
def rootedCyclicBoundary (h₀ h n b : ℕ) : ℕ :=
  h₀ + (h - 2) * n - 2 * b

/-- The old-boundary index forced on an unrooted bridge component of rank
`p`.  This is exactly the lower index occurring in the legacy `U` binomial. -/
def cyclicComponentOldBoundary (h k p : ℕ) : ℕ :=
  (h - 2) * k + 1 - 2 * p

/-- Rooted analogue: old boundary names on the base component at rank `p`. -/
def rootedCyclicComponentOldBoundary (h₀ h k p : ℕ) : ℕ :=
  h₀ + (h - 2) * k - 1 - 2 * p

/-- Old boundary labels on the base-containing tree component.  Truncated
subtraction is harmless: existence of the exposed endpoint forces the total
boundary to be positive. -/
def rootedTreeOldBoundary (h₀ h k : ℕ) : ℕ :=
  rootedTreeBoundary h₀ h k - 1

/-- Short manuscript-compatible alias. -/
abbrev treeBoundary := unrootedTreeBoundary

@[simp]
theorem treeBoundary_sub_one (h k : ℕ) :
    treeBoundary h k - 1 = unrootedTreeOldBoundary h k := by
  unfold treeBoundary unrootedTreeBoundary unrootedTreeOldBoundary
  omega

@[simp]
theorem cyclicComponentOldBoundary_zero (h k : ℕ) :
    cyclicComponentOldBoundary h k 0 = unrootedTreeOldBoundary h k := by
  simp [cyclicComponentOldBoundary, unrootedTreeOldBoundary]

@[simp]
theorem rootedCyclicComponentOldBoundary_zero (h₀ h k : ℕ) :
    rootedCyclicComponentOldBoundary h₀ h k 0 =
      rootedTreeOldBoundary h₀ h k := by
  simp [rootedCyclicComponentOldBoundary, rootedTreeOldBoundary,
    rootedTreeBoundary]

/-- Removing the left old-boundary block from a tree boundary leaves exactly
the right component's old-boundary block. -/
theorem treeBoundary_sub_oldBoundary
    (h n k : ℕ) (hk : k ≤ n) :
    treeBoundary h n - unrootedTreeOldBoundary h k =
      unrootedTreeOldBoundary h (n - k) := by
  have hn : n = k + (n - k) := by omega
  have hsub : k + (n - k) - k = n - k := by omega
  unfold treeBoundary unrootedTreeBoundary unrootedTreeOldBoundary
  rw [hn, Nat.mul_add]
  rw [hsub]
  omega

/-- The right component's total boundary after a tree cut. -/
theorem treeBoundary_sub_oldBoundary_add_one
    (h n k : ℕ) (hk : k ≤ n) :
    treeBoundary h n - unrootedTreeOldBoundary h k + 1 =
      treeBoundary h (n - k) := by
  rw [treeBoundary_sub_oldBoundary h n k hk]
  unfold treeBoundary unrootedTreeBoundary unrootedTreeOldBoundary
  omega

/-- The base-side old-boundary block and away-side old-boundary block are
complements in the ambient rooted-tree boundary. -/
theorem rootedTreeBoundary_sub_baseOldBoundary
    (h₀ h n k : ℕ) (hk : k ≤ n) (hbase : 1 ≤ h₀) :
    rootedTreeBoundary h₀ h n - rootedTreeOldBoundary h₀ h k =
      unrootedTreeOldBoundary h (n - k) := by
  have hn : n = k + (n - k) := by omega
  have hsub : k + (n - k) - k = n - k := by omega
  unfold rootedTreeOldBoundary rootedTreeBoundary unrootedTreeOldBoundary
  rw [hn, Nat.mul_add]
  rw [hsub]
  omega

theorem rootedTreeOldBoundary_add_one
    (h₀ h k : ℕ) (hbase : 1 ≤ h₀) :
    rootedTreeOldBoundary h₀ h k + 1 = rootedTreeBoundary h₀ h k := by
  unfold rootedTreeOldBoundary rootedTreeBoundary
  omega

theorem rootedTreeOldBoundary_le_ambient
    (h₀ h n k : ℕ) (hk : k ≤ n) (hbase : 1 ≤ h₀) :
    rootedTreeOldBoundary h₀ h k ≤ rootedTreeBoundary h₀ h n := by
  have hmul : (h - 2) * k ≤ (h - 2) * n :=
    Nat.mul_le_mul_left (h - 2) hk
  unfold rootedTreeOldBoundary rootedTreeBoundary
  omega

theorem unrooted_tree_boundary_eq
    (P : UnrootedStratum k h r m 0) (hh : 2 ≤ h) :
    m = unrootedTreeBoundary h k := by
  simpa [unrootedTreeBoundary, Nat.mul_comm] using
    (unrooted_rank_boundary_support P hh)

theorem rooted_tree_boundary_eq
    (P : RootedStratum k h₀ h r m 0) (hh : 2 ≤ h) :
    m = rootedTreeBoundary h₀ h k := by
  simpa [rootedTreeBoundary, Nat.mul_comm] using
    (rooted_rank_boundary_support P hh)

theorem unrooted_tree_old_boundary_eq
    (P : UnrootedStratum k h r (s + 1) 0) (hh : 2 ≤ h) :
    s = unrootedTreeOldBoundary h k := by
  simpa [unrootedTreeOldBoundary, Nat.mul_comm] using
    (unrooted_bridge_component_support P hh)

theorem rooted_tree_old_boundary_eq
    (P : RootedStratum k h₀ h r (s + 1) 0) (hh : 2 ≤ h) :
    s = rootedTreeOldBoundary h₀ h k := by
  have hs := rooted_bridge_component_support P hh
  simp only [Nat.mul_zero, add_zero] at hs
  unfold rootedTreeOldBoundary rootedTreeBoundary
  rw [Nat.mul_comm (h - 2) k]
  omega

/-- A nonempty concrete unrooted stratum has exactly the manuscript's
`cyclicBoundary`; admissibility of the truncated subtraction follows from
the existence of the object rather than being postulated separately. -/
theorem unrooted_boundary_eq_cyclicBoundary
    (P : UnrootedStratum n h r m b) (hh : 2 ≤ h) :
    m = cyclicBoundary h n b := by
  have hs := unrooted_rank_boundary_support P hh
  unfold cyclicBoundary
  rw [Nat.mul_comm (h - 2) n]
  omega

/-- Rooted counterpart of `unrooted_boundary_eq_cyclicBoundary`. -/
theorem rooted_boundary_eq_rootedCyclicBoundary
    (P : RootedStratum n h₀ h r m b) (hh : 2 ≤ h) :
    m = rootedCyclicBoundary h₀ h n b := by
  have hs := rooted_rank_boundary_support P hh
  unfold rootedCyclicBoundary
  rw [Nat.mul_comm (h - 2) n]
  omega

/-- The boundary index of any actual unrooted bridge component is the exact
truncated expression used in the legacy all-rank `U` recurrence. -/
theorem unrooted_bridge_old_boundary_eq_cyclicComponent
    (P : UnrootedStratum k h r (s + 1) p) (hh : 2 ≤ h) :
    s = cyclicComponentOldBoundary h k p := by
  have hs := unrooted_bridge_component_support P hh
  unfold cyclicComponentOldBoundary
  rw [Nat.mul_comm (h - 2) k]
  omega

theorem card_unrootedBridgeComponent_eq_zero_of_cyclicBoundary_ne
    (hh : 2 ≤ h)
    (hbad : s ≠ cyclicComponentOldBoundary h k p) :
    Fintype.card (UnrootedStratum k h r (s + 1) p) = 0 := by
  letI : IsEmpty (UnrootedStratum k h r (s + 1) p) :=
    ⟨fun P ↦ hbad (unrooted_bridge_old_boundary_eq_cyclicComponent P hh)⟩
  exact Fintype.card_eq_zero

theorem rooted_bridge_old_boundary_eq_cyclicComponent
    (P : RootedStratum k h₀ h r (s + 1) p) (hh : 2 ≤ h) :
    s = rootedCyclicComponentOldBoundary h₀ h k p := by
  have hs := rooted_bridge_component_support P hh
  unfold rootedCyclicComponentOldBoundary
  rw [Nat.mul_comm (h - 2) k]
  omega

theorem card_rootedBridgeComponent_eq_zero_of_cyclicBoundary_ne
    (hh : 2 ≤ h)
    (hbad : s ≠ rootedCyclicComponentOldBoundary h₀ h k p) :
    Fintype.card (RootedStratum k h₀ h r (s + 1) p) = 0 := by
  letI : IsEmpty (RootedStratum k h₀ h r (s + 1) p) :=
    ⟨fun P ↦ hbad (rooted_bridge_old_boundary_eq_cyclicComponent P hh)⟩
  exact Fintype.card_eq_zero

theorem card_unrootedTreeStratum_eq_zero_of_boundary_ne
    (hh : 2 ≤ h) (hbad : m ≠ unrootedTreeBoundary h k) :
    Fintype.card (UnrootedStratum k h r m 0) = 0 := by
  letI : IsEmpty (UnrootedStratum k h r m 0) :=
    ⟨fun P ↦ hbad (unrooted_tree_boundary_eq P hh)⟩
  exact Fintype.card_eq_zero

theorem card_rootedTreeStratum_eq_zero_of_boundary_ne
    (hh : 2 ≤ h) (hbad : m ≠ rootedTreeBoundary h₀ h k) :
    Fintype.card (RootedStratum k h₀ h r m 0) = 0 := by
  letI : IsEmpty (RootedStratum k h₀ h r m 0) :=
    ⟨fun P ↦ hbad (rooted_tree_boundary_eq P hh)⟩
  exact Fintype.card_eq_zero

theorem card_unrootedTreeBridgeComponent_eq_zero_of_old_boundary_ne
    (hh : 2 ≤ h) (hbad : s ≠ unrootedTreeOldBoundary h k) :
    Fintype.card (UnrootedStratum k h r (s + 1) 0) = 0 := by
  letI : IsEmpty (UnrootedStratum k h r (s + 1) 0) :=
    ⟨fun P ↦ hbad (unrooted_tree_old_boundary_eq P hh)⟩
  exact Fintype.card_eq_zero

theorem card_rootedTreeBridgeComponent_eq_zero_of_old_boundary_ne
    (hh : 2 ≤ h) (hbad : s ≠ rootedTreeOldBoundary h₀ h k) :
    Fintype.card (RootedStratum k h₀ h r (s + 1) 0) = 0 := by
  letI : IsEmpty (RootedStratum k h₀ h r (s + 1) 0) :=
    ⟨fun P ↦ hbad (rooted_tree_old_boundary_eq P hh)⟩
  exact Fintype.card_eq_zero

/-! ## Filtering the all-rank boundary convolution -/

/-- Numerical support of an unrooted bridge split. -/
def UnrootedBridgeBoundarySupported
    (n h m b k p s : ℕ) : Prop :=
  s + 2 * p = k * (h - 2) + 1 ∧
    (m - s) + 2 * (b - p) = (n - k) * (h - 2) + 1

/-- Numerical support of a rooted bridge split; the first component contains
the fixed base. -/
def RootedBridgeBoundarySupported
    (n h₀ h m b k p s : ℕ) : Prop :=
  s + 1 + 2 * p = h₀ + k * (h - 2) ∧
    (m - s) + 2 * (b - p) = (n - k) * (h - 2) + 1

/-- Every nonzero unrooted component product lies on the exact two-equation
boundary support.  Thus the full finite boundary sum equals its supported
filter, without any positivity or realizability assumption. -/
theorem sum_unrooted_bridge_components_eq_supported_filter
    (n h r m b k : ℕ) (p : Fin (b + 1)) (hh : 2 ≤ h) :
    (∑ s : Fin (m + 1),
        Nat.choose m s.1 *
          Fintype.card (UnrootedStratum k h r (s.1 + 1) p.1) *
          Fintype.card
            (UnrootedStratum (n - k) h r (m - s.1 + 1) (b - p.1))) =
      ∑ s ∈ (Finset.univ : Finset (Fin (m + 1))).filter
          (fun s ↦ UnrootedBridgeBoundarySupported
            n h m b k p.1 s.1),
        Nat.choose m s.1 *
          Fintype.card (UnrootedStratum k h r (s.1 + 1) p.1) *
          Fintype.card
            (UnrootedStratum (n - k) h r (m - s.1 + 1) (b - p.1)) := by
  classical
  symm
  apply Finset.sum_filter_of_ne
  intro s _ hterm
  constructor
  · by_contra hbad
    have hz := card_unrootedBridgeComponent_eq_zero_of_support_ne
      (k := k) (h := h) (r := r) (s := s.1) (p := p.1) hh hbad
    simp [hz] at hterm
  · by_contra hbad
    have hz := card_unrootedBridgeComponent_eq_zero_of_support_ne
      (k := n - k) (h := h) (r := r) (s := m - s.1)
      (p := b - p.1) hh hbad
    simp [hz] at hterm

/-- Rooted analogue of the all-rank boundary-support filter. -/
theorem sum_rooted_bridge_components_eq_supported_filter
    (n h₀ h r m b k : ℕ) (p : Fin (b + 1)) (hh : 2 ≤ h) :
    (∑ s : Fin (m + 1),
        Nat.choose m s.1 *
          Fintype.card (RootedStratum k h₀ h r (s.1 + 1) p.1) *
          Fintype.card
            (UnrootedStratum (n - k) h r (m - s.1 + 1) (b - p.1))) =
      ∑ s ∈ (Finset.univ : Finset (Fin (m + 1))).filter
          (fun s ↦ RootedBridgeBoundarySupported
            n h₀ h m b k p.1 s.1),
        Nat.choose m s.1 *
          Fintype.card (RootedStratum k h₀ h r (s.1 + 1) p.1) *
          Fintype.card
            (UnrootedStratum (n - k) h r (m - s.1 + 1) (b - p.1)) := by
  classical
  symm
  apply Finset.sum_filter_of_ne
  intro s _ hterm
  constructor
  · by_contra hbad
    have hz := card_rootedBridgeComponent_eq_zero_of_support_ne
      (k := k) (h₀ := h₀) (h := h) (r := r) (s := s.1) (p := p.1)
      hh hbad
    simp [hz] at hterm
  · by_contra hbad
    have hz := card_unrootedBridgeComponent_eq_zero_of_support_ne
      (k := n - k) (h := h) (r := r) (s := m - s.1)
      (p := b - p.1) hh hbad
    simp [hz] at hterm

/-! ## Eliminating the boundary index exactly -/

/-- At fixed cell and rank splits, the unrooted boundary sum has at most one
nonzero term.  The right side uses the manuscript's truncated lower index.
If that index lies outside `0,…,m`, `Nat.choose` makes the displayed term zero;
the proof separately shows that every term in the finite sum is then zero. -/
theorem sum_unrooted_bridge_components_eq_single_boundary
    (n h r m b k p : ℕ) (hh : 2 ≤ h) :
    (∑ s : Fin (m + 1),
        Nat.choose m s.1 *
          Fintype.card (UnrootedStratum k h r (s.1 + 1) p) *
          Fintype.card
            (UnrootedStratum (n - k) h r (m - s.1 + 1) (b - p))) =
      Nat.choose m (cyclicComponentOldBoundary h k p) *
        Fintype.card
          (UnrootedStratum k h r
            (cyclicComponentOldBoundary h k p + 1) p) *
        Fintype.card
          (UnrootedStratum (n - k) h r
            (m - cyclicComponentOldBoundary h k p + 1) (b - p)) := by
  classical
  let s₀ := cyclicComponentOldBoundary h k p
  by_cases hs₀ : s₀ ≤ m
  · let i₀ : Fin (m + 1) := ⟨s₀, by omega⟩
    rw [Finset.sum_eq_single i₀]
    · intro s _ hne
      have hsne : s.1 ≠ s₀ := by
        intro hs
        apply hne
        exact Fin.ext hs
      have hz :=
        card_unrootedBridgeComponent_eq_zero_of_cyclicBoundary_ne
          (k := k) (h := h) (r := r) (s := s.1) (p := p) hh (by
            simpa [s₀] using hsne)
      simp [hz]
    · simp
  · have hlt : m < s₀ := Nat.lt_of_not_ge hs₀
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp only [Nat.zero_mul]
    apply Finset.sum_eq_zero
    intro s _
    have hsne : s.1 ≠ s₀ := by
      intro hs
      have hslt := s.2
      omega
    have hz :=
      card_unrootedBridgeComponent_eq_zero_of_cyclicBoundary_ne
        (k := k) (h := h) (r := r) (s := s.1) (p := p) hh (by
          simpa [s₀] using hsne)
    simp [hz]

/-- Rooted analogue of exact boundary-index elimination. -/
theorem sum_rooted_bridge_components_eq_single_boundary
    (n h₀ h r m b k p : ℕ) (hh : 2 ≤ h) :
    (∑ s : Fin (m + 1),
        Nat.choose m s.1 *
          Fintype.card (RootedStratum k h₀ h r (s.1 + 1) p) *
          Fintype.card
            (UnrootedStratum (n - k) h r (m - s.1 + 1) (b - p))) =
      Nat.choose m (rootedCyclicComponentOldBoundary h₀ h k p) *
        Fintype.card
          (RootedStratum k h₀ h r
            (rootedCyclicComponentOldBoundary h₀ h k p + 1) p) *
        Fintype.card
          (UnrootedStratum (n - k) h r
            (m - rootedCyclicComponentOldBoundary h₀ h k p + 1)
              (b - p)) := by
  classical
  let s₀ := rootedCyclicComponentOldBoundary h₀ h k p
  by_cases hs₀ : s₀ ≤ m
  · let i₀ : Fin (m + 1) := ⟨s₀, by omega⟩
    rw [Finset.sum_eq_single i₀]
    · intro s _ hne
      have hsne : s.1 ≠ s₀ := by
        intro hs
        apply hne
        exact Fin.ext hs
      have hz :=
        card_rootedBridgeComponent_eq_zero_of_cyclicBoundary_ne
          (k := k) (h₀ := h₀) (h := h) (r := r) (s := s.1) (p := p) hh (by
            simpa [s₀] using hsne)
      simp [hz]
    · simp
  · have hlt : m < s₀ := Nat.lt_of_not_ge hs₀
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp only [Nat.zero_mul]
    apply Finset.sum_eq_zero
    intro s _
    have hsne : s.1 ≠ s₀ := by
      intro hs
      have hslt := s.2
      omega
    have hz :=
      card_rootedBridgeComponent_eq_zero_of_cyclicBoundary_ne
        (k := k) (h₀ := h₀) (h := h) (r := r) (s := s.1) (p := p) hh (by
          simpa [s₀] using hsne)
    simp [hz]

/-! ## The raw `R` and `T` convolution summands -/

/-- With the ambient boundary specialized to `treeBoundary h n`, eliminating
the boundary split gives exactly the raw summand of the legacy `R`
recurrence.  Both component boundary parameters have disappeared. -/
theorem sum_unrooted_tree_components_legacy
    (n h r k : ℕ) (hh : 2 ≤ h) (hk : k ≤ n) :
    (∑ s : Fin (treeBoundary h n + 1),
        Nat.choose (treeBoundary h n) s.1 *
          Fintype.card (UnrootedStratum k h r (s.1 + 1) 0) *
          Fintype.card
            (UnrootedStratum (n - k) h r
              (treeBoundary h n - s.1 + 1) 0)) =
      Nat.choose (treeBoundary h n) (treeBoundary h k - 1) *
        Fintype.card (UnrootedStratum k h r (treeBoundary h k) 0) *
        Fintype.card
          (UnrootedStratum (n - k) h r (treeBoundary h (n - k)) 0) := by
  have hsingle := sum_unrooted_bridge_components_eq_single_boundary
    n h r (treeBoundary h n) 0 k 0 hh
  have hleft : unrootedTreeOldBoundary h k + 1 = treeBoundary h k := by
    unfold treeBoundary unrootedTreeBoundary unrootedTreeOldBoundary
    omega
  rw [cyclicComponentOldBoundary_zero] at hsingle
  rw [hleft, treeBoundary_sub_oldBoundary_add_one h n k hk] at hsingle
  simpa [treeBoundary_sub_one, unrootedTreeOldBoundary, treeBoundary, unrootedTreeBoundary, Nat.add_assoc] using hsingle

/-- Fixed-base tree analogue.  Our oriented cut allocates old labels to the
base side; binomial symmetry changes this to the away-side lower index used
in the manuscript's `T` recurrence.  The hypothesis `h₀ ≥ 1` is the
geometric nondegeneracy ensuring that the base component can carry its
exposed bridge endpoint. -/
theorem sum_rooted_tree_components_legacy
    (n h₀ h r k : ℕ) (hh : 2 ≤ h) (hk : k ≤ n)
    (hbase : 1 ≤ h₀) :
    (∑ s : Fin (rootedTreeBoundary h₀ h n + 1),
        Nat.choose (rootedTreeBoundary h₀ h n) s.1 *
          Fintype.card (RootedStratum k h₀ h r (s.1 + 1) 0) *
          Fintype.card
            (UnrootedStratum (n - k) h r
              (rootedTreeBoundary h₀ h n - s.1 + 1) 0)) =
      Nat.choose (rootedTreeBoundary h₀ h n)
          (treeBoundary h (n - k) - 1) *
        Fintype.card
          (RootedStratum k h₀ h r (rootedTreeBoundary h₀ h k) 0) *
        Fintype.card
          (UnrootedStratum (n - k) h r (treeBoundary h (n - k)) 0) := by
  have hsingle := sum_rooted_bridge_components_eq_single_boundary
    n h₀ h r (rootedTreeBoundary h₀ h n) 0 k 0 hh
  have hle := rootedTreeOldBoundary_le_ambient h₀ h n k hk hbase
  have hchoose :
      Nat.choose (rootedTreeBoundary h₀ h n)
          (rootedTreeOldBoundary h₀ h k) =
        Nat.choose (rootedTreeBoundary h₀ h n)
          (unrootedTreeOldBoundary h (n - k)) := by
    rw [← rootedTreeBoundary_sub_baseOldBoundary h₀ h n k hk hbase]
    exact (Nat.choose_symm hle).symm
  rw [rootedCyclicComponentOldBoundary_zero] at hsingle
  rw [hchoose] at hsingle
  rw [rootedTreeOldBoundary_add_one h₀ h k hbase,
    rootedTreeBoundary_sub_baseOldBoundary h₀ h n k hk hbase] at hsingle
  simpa [treeBoundary_sub_one, unrootedTreeOldBoundary, treeBoundary, unrootedTreeBoundary, Nat.add_assoc] using hsingle

/-! ## Rank-zero filters -/

theorem sum_unrooted_tree_components_eq_supported_filter
    (n h r m k : ℕ) (hh : 2 ≤ h) :
    (∑ s : Fin (m + 1),
        Nat.choose m s.1 *
          Fintype.card (UnrootedStratum k h r (s.1 + 1) 0) *
          Fintype.card
            (UnrootedStratum (n - k) h r (m - s.1 + 1) 0)) =
      ∑ s ∈ (Finset.univ : Finset (Fin (m + 1))).filter
          (fun s ↦
            s.1 = unrootedTreeOldBoundary h k ∧
            m - s.1 = unrootedTreeOldBoundary h (n - k)),
        Nat.choose m s.1 *
          Fintype.card (UnrootedStratum k h r (s.1 + 1) 0) *
          Fintype.card
            (UnrootedStratum (n - k) h r (m - s.1 + 1) 0) := by
  classical
  simpa [UnrootedBridgeBoundarySupported, unrootedTreeOldBoundary,
    Nat.mul_comm] using
    (sum_unrooted_bridge_components_eq_supported_filter
      n h r m 0 k (0 : Fin 1) hh)

theorem sum_rooted_tree_components_eq_supported_filter
    (n h₀ h r m k : ℕ) (hh : 2 ≤ h) :
    (∑ s : Fin (m + 1),
        Nat.choose m s.1 *
          Fintype.card (RootedStratum k h₀ h r (s.1 + 1) 0) *
          Fintype.card
            (UnrootedStratum (n - k) h r (m - s.1 + 1) 0)) =
      ∑ s ∈ (Finset.univ : Finset (Fin (m + 1))).filter
          (fun s ↦
            s.1 = rootedTreeOldBoundary h₀ h k ∧
            m - s.1 = unrootedTreeOldBoundary h (n - k)),
        Nat.choose m s.1 *
          Fintype.card (RootedStratum k h₀ h r (s.1 + 1) 0) *
          Fintype.card
            (UnrootedStratum (n - k) h r (m - s.1 + 1) 0) := by
  classical
  symm
  apply Finset.sum_filter_of_ne
  intro s _ hterm
  constructor
  · by_contra hbad
    have hz := card_rootedTreeBridgeComponent_eq_zero_of_old_boundary_ne
      (k := k) (h₀ := h₀) (h := h) (r := r) (s := s.1) hh hbad
    simp [hz] at hterm
  · by_contra hbad
    have hz := card_unrootedTreeBridgeComponent_eq_zero_of_old_boundary_ne
      (k := n - k) (h := h) (r := r) (s := m - s.1) hh hbad
    simp [hz] at hterm


end
end StratumBalanceSpecialization
end FacetPairing
end PolytopeCounting
