module

public import Proofs.GlobalBridgeCut

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Cardinal consequences of the lossless global bridge cut

The global bridge cut is injective and records an orientation of the marked
seam.  This file extracts the exact finite-cardinality statement that follows
before the realized range is replaced by a numerical coproduct of two
standard `Fin k` components.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace GlobalBridgeCut

noncomputable section

open PointedDecomposition

local instance bridgePointedFintype (n h r m b : ℕ) :
    Fintype (UnrootedBridgePointed n h r m b) := Fintype.ofFinite _

local instance bridgeCutRangeFintype (n h r m b : ℕ) :
    Fintype (Set.range
      (cutBridge : UnrootedBridgePointed n h r m b × Bool →
        UnrootedBridgeCutCarrier n h r m b)) := Fintype.ofFinite _

/-- The realized global bridge-cut range has exactly twice the number of
unoriented bridge-pointed diagrams.  No freeness assumption is involved:
the factor two is the literal Boolean endpoint orientation in the source. -/
theorem card_cutBridge_range (n h r m b : ℕ) :
    Fintype.card (Set.range
        (cutBridge : UnrootedBridgePointed n h r m b × Bool →
          UnrootedBridgeCutCarrier n h r m b)) =
      2 * Fintype.card (UnrootedBridgePointed n h r m b) := by
  calc
    Fintype.card (Set.range
        (cutBridge : UnrootedBridgePointed n h r m b × Bool →
          UnrootedBridgeCutCarrier n h r m b)) =
        Fintype.card (UnrootedBridgePointed n h r m b × Bool) :=
      Fintype.card_congr (cutBridgeEquivRange :
        (UnrootedBridgePointed n h r m b × Bool) ≃ _).symm
    _ = 2 * Fintype.card (UnrootedBridgePointed n h r m b) := by
      simp [Fintype.card_prod, Nat.mul_comm]


end
end GlobalBridgeCut
end FacetPairing
end PolytopeCounting
