module

public import Proofs.NonbridgeEquiv
public import Proofs.RootedNonbridgeEquiv

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# An unconditional concrete recurrence step

This module combines literal seam pointing, the bridge/nonbridge dichotomy,
and the exact unrooted nonbridge cut--join equivalence.  The result is the
`U` recurrence before expanding the bridge remainder into its component
convolution.  Unlike the older certificate interface, every term below is
the cardinality of a concrete subtype from `FacetPairingModel`.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace ConcreteRecurrenceStep

open PointedDecomposition NonbridgeEquiv RootedNonbridgeEquiv

noncomputable section

local instance unrootedStratumFintype (n h r m b : ℕ) :
    Fintype (UnrootedStratum n h r m b) := Fintype.ofFinite _

local instance unrootedNonbridgePointedFintype (n h r m b : ℕ) :
    Fintype (UnrootedNonbridgePointed n h r m b) := Fintype.ofFinite _

local instance unrootedBridgePointedFintype (n h r m b : ℕ) :
    Fintype (UnrootedBridgePointed n h r m b) := Fintype.ofFinite _

local instance rootedStratumFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedStratum n h₀ h r m b) := Fintype.ofFinite _

local instance rootedNonbridgePointedFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedNonbridgePointed n h₀ h r m b) := Fintype.ofFinite _

local instance rootedBridgePointedFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedBridgePointed n h₀ h r m b) := Fintype.ofFinite _

/-- For rank `b+1`, the oriented nonbridge part is exactly `r` copies of the
rank-`b` stratum with two new boundary labels.  Adding the oriented bridge
remainder gives twice the literal seam-pointed count. -/
theorem unrooted_successor_cut_decomposition
    (n h r m b : ℕ) :
    2 * ((n + b) * Fintype.card
          (UnrootedStratum n h r m (b + 1))) =
      r * Fintype.card (UnrootedStratum n h r (m + 2) b) +
        2 * Fintype.card
          (UnrootedBridgePointed n h r m (b + 1)) := by
  have hmaster := unrooted_pointed_master_identity n h r m (b + 1)
  have hseams : n + (b + 1) - 1 = n + b := by omega
  rw [hseams] at hmaster
  have hnonbridge := card_unrootedNonbridge_mul_two n h r m b
  calc
    2 * ((n + b) * Fintype.card
          (UnrootedStratum n h r m (b + 1))) =
        2 * (Fintype.card
            (UnrootedNonbridgePointed n h r m (b + 1)) +
          Fintype.card
            (UnrootedBridgePointed n h r m (b + 1))) := by rw [hmaster]
    _ = 2 * Fintype.card
            (UnrootedNonbridgePointed n h r m (b + 1)) +
          2 * Fintype.card
            (UnrootedBridgePointed n h r m (b + 1)) := by
        rw [Nat.mul_add]
    _ = r * Fintype.card (UnrootedStratum n h r (m + 2) b) +
          2 * Fintype.card
            (UnrootedBridgePointed n h r m (b + 1)) := by
        rw [hnonbridge]

/-- The same theorem with the seam-pointing factor associated to the left,
matching the usual displayed recurrence convention. -/
theorem unrooted_successor_cut_decomposition'
    (n h r m b : ℕ) :
    2 * (n + b) * Fintype.card
          (UnrootedStratum n h r m (b + 1)) =
      r * Fintype.card (UnrootedStratum n h r (m + 2) b) +
        2 * Fintype.card
          (UnrootedBridgePointed n h r m (b + 1)) := by
  simpa only [Nat.mul_assoc] using
    unrooted_successor_cut_decomposition n h r m b

/-- Rooted analogue of the unconditional nonbridge step.  It supplies the
`r/2` term in the rooted cyclic recurrence; the remaining rooted bridge
carrier is deliberately left visible until the global bridge coproduct is
constructed. -/
theorem rooted_successor_cut_decomposition
    (n h₀ h r m b : ℕ) :
    2 * ((n + b + 1) * Fintype.card
          (RootedStratum n h₀ h r m (b + 1))) =
      r * Fintype.card (RootedStratum n h₀ h r (m + 2) b) +
        2 * Fintype.card
          (RootedBridgePointed n h₀ h r m (b + 1)) := by
  have hmaster := rooted_pointed_master_identity n h₀ h r m (b + 1)
  have hnonbridge := card_rootedNonbridge_mul_two n h₀ h r m b
  calc
    2 * ((n + b + 1) * Fintype.card
          (RootedStratum n h₀ h r m (b + 1))) =
        2 * (Fintype.card
            (RootedNonbridgePointed n h₀ h r m (b + 1)) +
          Fintype.card
            (RootedBridgePointed n h₀ h r m (b + 1))) := by
        rw [hmaster]
        congr 2
    _ = 2 * Fintype.card
            (RootedNonbridgePointed n h₀ h r m (b + 1)) +
          2 * Fintype.card
            (RootedBridgePointed n h₀ h r m (b + 1)) := by
        rw [Nat.mul_add]
    _ = r * Fintype.card (RootedStratum n h₀ h r (m + 2) b) +
          2 * Fintype.card
            (RootedBridgePointed n h₀ h r m (b + 1)) := by
        rw [hnonbridge]


end
end ConcreteRecurrenceStep
end FacetPairing
end PolytopeCounting
