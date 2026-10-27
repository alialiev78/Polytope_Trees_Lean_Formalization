module

public import Proofs.MarkedSeamBridge

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Literal seam pointing and the bridge/nonbridge decomposition

This module proves seam-pointing and the bridge/nonbridge decomposition.

* A pointed object is the literal dependent pair of a diagram and one of
  its seams.
* The rank equation proves the number of possible seam points.
* Every point lies in exactly one of the nonbridge and bridge subtypes.

No freeness of a symmetry action is used here.  In particular, these are
cardinality statements about concrete globally indexed objects, before any
groupoid normalization.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace PointedDecomposition

noncomputable section

/-- A literal seam-pointed unrooted diagram in a fixed circuit-rank
stratum. -/
abbrev UnrootedPointed (n h r m b : ℕ) :=
  Σ P : UnrootedStratum n h r m b, P.1.raw.pairing.Seam

/-- A literal seam-pointed rooted diagram in a fixed circuit-rank
stratum. -/
abbrev RootedPointed (n h₀ h r m b : ℕ) :=
  Σ P : RootedStratum n h₀ h r m b, P.1.raw.pairing.Seam

/-- The nonbridge part of the pointed unrooted stratum. -/
abbrev UnrootedNonbridgePointed (n h r m b : ℕ) :=
  {z : UnrootedPointed n h r m b //
    z.1.1.raw.pairing.IsNonbridge z.2}

/-- The bridge part of the pointed unrooted stratum. -/
abbrev UnrootedBridgePointed (n h r m b : ℕ) :=
  {z : UnrootedPointed n h r m b //
    z.1.1.raw.pairing.IsBridge z.2}

/-- The nonbridge part of the pointed rooted stratum. -/
abbrev RootedNonbridgePointed (n h₀ h r m b : ℕ) :=
  {z : RootedPointed n h₀ h r m b //
    z.1.1.raw.pairing.IsNonbridge z.2}

/-- The bridge part of the pointed rooted stratum. -/
abbrev RootedBridgePointed (n h₀ h r m b : ℕ) :=
  {z : RootedPointed n h₀ h r m b //
    z.1.1.raw.pairing.IsBridge z.2}

/- The stratum predicates and the bridge predicates are not computationally
decidable.  We therefore obtain their finite enumerations noncomputably from
the already proved `Finite` instances.  This changes no cardinality and does
not assert decidability of connectivity as mathematical data. -/
noncomputable local instance unrootedStratumFintype
    (n h r m b : ℕ) : Fintype (UnrootedStratum n h r m b) :=
  Fintype.ofFinite _

noncomputable local instance rootedStratumFintype
    (n h₀ h r m b : ℕ) : Fintype (RootedStratum n h₀ h r m b) :=
  Fintype.ofFinite _

noncomputable local instance unrootedNonbridgePointedFintype
    (n h r m b : ℕ) : Fintype (UnrootedNonbridgePointed n h r m b) :=
  Fintype.ofFinite _

noncomputable local instance unrootedBridgePointedFintype
    (n h r m b : ℕ) : Fintype (UnrootedBridgePointed n h r m b) :=
  Fintype.ofFinite _

noncomputable local instance rootedNonbridgePointedFintype
    (n h₀ h r m b : ℕ) : Fintype (RootedNonbridgePointed n h₀ h r m b) :=
  Fintype.ofFinite _

noncomputable local instance rootedBridgePointedFintype
    (n h₀ h r m b : ℕ) : Fintype (RootedBridgePointed n h₀ h r m b) :=
  Fintype.ofFinite _

/-- A finite-set dichotomy does not need a decidable predicate in its
statement: classical decidability is used only to construct the displayed
equivalence. -/
def subtypeOrNotEquiv (X : Type*) (p : X → Prop) :
    X ≃ {x : X // p x} ⊕ {x : X // ¬ p x} := by
  classical
  exact
    { toFun := fun x ↦ if hx : p x then Sum.inl ⟨x, hx⟩
        else Sum.inr ⟨x, hx⟩
      invFun := fun z ↦ z.elim Subtype.val Subtype.val
      left_inv := by
        intro x
        by_cases hx : p x <;> simp [hx]
      right_inv := by
        intro z
        rcases z with ⟨x, hx⟩ | ⟨x, hx⟩
        · simp [hx]
        · simp [hx] }

/-- The literal dichotomy map for unrooted pointed diagrams. -/
def unrootedPointedEquivDichotomy (n h r m b : ℕ) :
    UnrootedPointed n h r m b ≃
      UnrootedNonbridgePointed n h r m b ⊕
        UnrootedBridgePointed n h r m b := by
  simpa only [ColoredMatching.IsBridge, ColoredMatching.IsNonbridge, UnrootedNonbridgePointed, UnrootedBridgePointed,
    RootedNonbridgePointed, RootedBridgePointed] using
    subtypeOrNotEquiv (UnrootedPointed n h r m b)
      (fun z ↦ z.1.1.raw.pairing.IsNonbridge z.2)

/-- The literal dichotomy map for rooted pointed diagrams. -/
def rootedPointedEquivDichotomy (n h₀ h r m b : ℕ) :
    RootedPointed n h₀ h r m b ≃
      RootedNonbridgePointed n h₀ h r m b ⊕
        RootedBridgePointed n h₀ h r m b := by
  simpa only [ColoredMatching.IsBridge, ColoredMatching.IsNonbridge, UnrootedNonbridgePointed, UnrootedBridgePointed,
    RootedNonbridgePointed, RootedBridgePointed] using
    subtypeOrNotEquiv (RootedPointed n h₀ h r m b)
      (fun z ↦ z.1.1.raw.pairing.IsNonbridge z.2)

/-- The rank equation gives exactly `n+b-1` seams in an unrooted rank-`b`
stratum.  The subtraction is harmless here because it is a consequence of
the subtraction-free rank equation stored in the stratum. -/
theorem unrooted_seam_card (P : UnrootedStratum n h r m b) :
    Fintype.card P.1.raw.pairing.Seam = n + b - 1 := by
  have hrank := P.2
  simp only [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
    BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount,
    card_unrootedCell] at hrank
  rw [Fintype.card_coe]
  omega

/-- The rank equation gives exactly `n+b` seams in a rooted rank-`b`
stratum, since the fixed base contributes one additional dual vertex. -/
theorem rooted_seam_card (P : RootedStratum n h₀ h r m b) :
    Fintype.card P.1.raw.pairing.Seam = n + b := by
  have hrank := P.2
  simp only [ConnectedDiagram.HasCircuitRank, ConnectedDiagram.edgeCount,
    BoundaryLabelledPairing.edgeCount, ColoredMatching.edgeCount,
    card_rootedCell] at hrank
  rw [Fintype.card_coe]
  omega

/-- Literal seam pointing multiplies the unrooted stratum cardinality by
the exact seam count. -/
theorem card_unrootedPointed (n h r m b : ℕ) :
    Fintype.card (UnrootedPointed n h r m b) =
      (n + b - 1) * Fintype.card (UnrootedStratum n h r m b) := by
  calc
    Fintype.card (UnrootedPointed n h r m b) =
        ∑ P : UnrootedStratum n h r m b,
          Fintype.card P.1.raw.pairing.Seam := by
      change Fintype.card
          (Σ P : UnrootedStratum n h r m b, P.1.raw.pairing.Seam) = _
      exact Fintype.card_sigma
        (ι := UnrootedStratum n h r m b)
        (α := fun P ↦ P.1.raw.pairing.Seam)
    _ = (n + b - 1) * Fintype.card (UnrootedStratum n h r m b) := by
      simp_rw [unrooted_seam_card]
      simp [Nat.mul_comm]

/-- Literal seam pointing multiplies the rooted stratum cardinality by the
exact seam count. -/
theorem card_rootedPointed (n h₀ h r m b : ℕ) :
    Fintype.card (RootedPointed n h₀ h r m b) =
      (n + b) * Fintype.card (RootedStratum n h₀ h r m b) := by
  calc
    Fintype.card (RootedPointed n h₀ h r m b) =
        ∑ P : RootedStratum n h₀ h r m b,
          Fintype.card P.1.raw.pairing.Seam := by
      change Fintype.card
          (Σ P : RootedStratum n h₀ h r m b, P.1.raw.pairing.Seam) = _
      exact Fintype.card_sigma
        (ι := RootedStratum n h₀ h r m b)
        (α := fun P ↦ P.1.raw.pairing.Seam)
    _ = (n + b) * Fintype.card (RootedStratum n h₀ h r m b) := by
      simp_rw [rooted_seam_card]
      simp [Nat.mul_comm]

/-- Unrooted seam points are the disjoint union of the nonbridge and bridge
parts. -/
theorem card_unrooted_nonbridge_add_bridge (n h r m b : ℕ) :
    Fintype.card (UnrootedNonbridgePointed n h r m b) +
        Fintype.card (UnrootedBridgePointed n h r m b) =
      Fintype.card (UnrootedPointed n h r m b) := by
  rw [← Fintype.card_sum]
  exact Fintype.card_congr (unrootedPointedEquivDichotomy n h r m b).symm

/-- Rooted seam points are the disjoint union of the nonbridge and bridge
parts. -/
theorem card_rooted_nonbridge_add_bridge (n h₀ h r m b : ℕ) :
    Fintype.card (RootedNonbridgePointed n h₀ h r m b) +
        Fintype.card (RootedBridgePointed n h₀ h r m b) =
      Fintype.card (RootedPointed n h₀ h r m b) := by
  rw [← Fintype.card_sum]
  exact Fintype.card_congr (rootedPointedEquivDichotomy n h₀ h r m b).symm

/-- Combining pointing and the dichotomy gives the exact raw unrooted
left-hand side used by the `R` and `U` recurrences. -/
theorem unrooted_pointed_master_identity (n h r m b : ℕ) :
    Fintype.card (UnrootedNonbridgePointed n h r m b) +
        Fintype.card (UnrootedBridgePointed n h r m b) =
      (n + b - 1) * Fintype.card (UnrootedStratum n h r m b) := by
  rw [card_unrooted_nonbridge_add_bridge, card_unrootedPointed]

/-- Combining pointing and the dichotomy gives the exact raw rooted
left-hand side used by the fixed-base recurrences. -/
theorem rooted_pointed_master_identity (n h₀ h r m b : ℕ) :
    Fintype.card (RootedNonbridgePointed n h₀ h r m b) +
        Fintype.card (RootedBridgePointed n h₀ h r m b) =
      (n + b) * Fintype.card (RootedStratum n h₀ h r m b) := by
  rw [card_rooted_nonbridge_add_bridge, card_rootedPointed]

/-! Multiplication by `Bool` is the literal orientation choice responsible
for the factor two in unrooted cut data. -/

abbrev OrientedUnrootedPointed (n h r m b : ℕ) :=
  UnrootedPointed n h r m b × Bool

theorem card_orientedUnrootedPointed (n h r m b : ℕ) :
    Fintype.card (OrientedUnrootedPointed n h r m b) =
      2 * (n + b - 1) * Fintype.card (UnrootedStratum n h r m b) := by
  rw [Fintype.card_prod, card_unrootedPointed]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]


end
end PointedDecomposition
end FacetPairing
end PolytopeCounting
