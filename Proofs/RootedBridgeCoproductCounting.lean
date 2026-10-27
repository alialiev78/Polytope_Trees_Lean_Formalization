module

public import Proofs.RootedNumericalBridgeCoproduct
public import Proofs.NumericalRecurrenceAssembly

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Counting the exact rooted bridge coproduct

The base-containing component is intrinsically distinguished.  Hence the
allocation-enriched rooted coproduct has no endpoint-orientation factor two:
its cardinality is exactly `r` times the raw numerical component sum.

The first theorem identifies the existing literal coproduct count with the
precise `rootedRawBridgeSum` consumed by `NumericalRecurrenceAssembly`.  The
second theorem shows that any exact rooted cut--join equivalence immediately
discharges the raw bridge-cardinality hypothesis of the final `Psi` and `T`
recurrences.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace RootedBridgeCoproductCounting

open scoped BigOperators

open PointedDecomposition
open NumericalRecurrenceAssembly

noncomputable section

local instance rootedStratumFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedStratum n h₀ h r m b) := Fintype.ofFinite _

local instance unrootedStratumFintype (n h r m b : ℕ) :
    Fintype (UnrootedStratum n h r m b) := Fintype.ofFinite _

local instance rootedBridgePointedFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedBridgePointed n h₀ h r m b) := Fintype.ofFinite _

/-- The literal allocation-enriched rooted coproduct has exactly the raw
triple-sum cardinality used by the normalized recurrence. -/
theorem card_coproduct (n h₀ h r m b : ℕ) :
    Fintype.card
        (RootedNumericalBridgeCoproduct.Coproduct n h₀ h r m b) =
      r * rootedRawBridgeSum n h₀ h r m b := by
  classical
  rw [RootedNumericalBridgeCoproduct.card_coproduct]
  have hraw :
      rootedRawBridgeSum n h₀ h r m b =
        ∑ k : Fin n, ∑ s : Fin (m + 1), ∑ p : Fin (b + 1),
          Nat.choose n k.1 * Nat.choose m s.1 *
            Fintype.card
              (RootedStratum k.1 h₀ h r (s.1 + 1) p.1) *
            Fintype.card
              (UnrootedStratum (n - k.1) h r
                (m - s.1 + 1) (b - p.1)) := by
    unfold rootedRawBridgeSum RootedIndex
    rw [Fintype.sum_prod_type]
    apply Fintype.sum_congr
    intro k
    rw [Fintype.sum_prod_type]
    rfl
  rw [hraw]
  simp only [Finset.mul_sum]
  apply Fintype.sum_congr
  intro k
  apply Fintype.sum_congr
  intro s
  apply Fintype.sum_congr
  intro p
  ac_rfl

/-- Taking cardinalities of an exact rooted bridge equivalence yields the
literal raw identity required by the final rooted recurrence.  There is no
factor two because the base side canonically orients the bridge. -/
theorem raw_bridge_cardinality_of_equiv
    (e : RootedBridgePointed n h₀ h r m b ≃
      RootedNumericalBridgeCoproduct.Coproduct n h₀ h r m b) :
    Fintype.card (RootedBridgePointed n h₀ h r m b) =
      r * rootedRawBridgeSum n h₀ h r m b := by
  calc
    Fintype.card (RootedBridgePointed n h₀ h r m b) =
        Fintype.card
          (RootedNumericalBridgeCoproduct.Coproduct n h₀ h r m b) :=
      Fintype.card_congr e
    _ = r * rootedRawBridgeSum n h₀ h r m b :=
      card_coproduct n h₀ h r m b


end
end RootedBridgeCoproductCounting
end FacetPairing
end PolytopeCounting
