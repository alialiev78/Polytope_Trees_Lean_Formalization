module

public import Proofs.NonbridgeEquiv
public import Proofs.RootedNonbridgeEquiv
public import Proofs.TreeBridgeIdentity
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Global cut--join equivalences from the two bridge equivalences

This module combines the literal seam-pointing dichotomy with the exact
nonbridge cut--join equivalences.  It is generic in the bridge target, so it
contains no counting hypothesis and no recurrence certificate.  Supplying
the allocation-enriched bridge equivalences yields the global `R`, `T`, `U`
and `Psi` stratum equivalences directly.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace GlobalCutJoinAssembly

noncomputable section

open PointedDecomposition NonbridgeEquiv RootedNonbridgeEquiv

/-! ## Distributing endpoint orientation across the bridge dichotomy -/

/-- An oriented unrooted seam point is either an oriented nonbridge point
or an oriented bridge point. -/
def unrootedOrientedPointedEquivDichotomy (n h r m b : ℕ) :
    UnrootedPointed n h r m b × Bool ≃
      (UnrootedNonbridgePointed n h r m b × Bool) ⊕
        (UnrootedBridgePointed n h r m b × Bool) :=
  ((unrootedPointedEquivDichotomy n h r m b).prodCongr
      (Equiv.refl Bool)).trans
    (Equiv.sumProdDistrib _ _ Bool)

/-- Rooted nonbridge cutting still has two endpoint orientations.  The
bridge component itself is intrinsically based; the Boolean remains as a
separate factor on that branch. -/
def rootedOrientedPointedEquivDichotomy (n h₀ h r m b : ℕ) :
    RootedPointed n h₀ h r m b × Bool ≃
      (RootedNonbridgePointed n h₀ h r m b × Bool) ⊕
        (RootedBridgePointed n h₀ h r m b × Bool) :=
  ((rootedPointedEquivDichotomy n h₀ h r m b).prodCongr
      (Equiv.refl Bool)).trans
    (Equiv.sumProdDistrib _ _ Bool)

/-! ## Successor-rank `U` and `Psi` equivalences -/

/-- Global unrooted successor-rank cut--join equivalence.  Its first branch
is the concrete nonbridge cut, and its second branch is any supplied exact
bridge equivalence. -/
def unrootedSuccessorEquiv
    (X : Type*)
    (bridgeEquiv :
      (UnrootedBridgePointed n h r m (b + 1) × Bool) ≃ X) :
    (UnrootedPointed n h r m (b + 1) × Bool) ≃
      (UnrootedStratum n h r (m + 2) b × Fin r) ⊕ X :=
  (unrootedOrientedPointedEquivDichotomy n h r m (b + 1)).trans <|
    Equiv.sumCongr
      (unrootedNonbridgeEquiv
        (n := n) (h := h) (r := r) (m := m) (b := b))
      bridgeEquiv

/-- Global rooted successor-rank cut--join equivalence.  The bridge branch
has an explicit residual Boolean because the whole pointed stratum was
oriented for the nonbridge cut; this is exactly why its cardinal recurrence
has bridge coefficient `r`, rather than `r/2`. -/
def rootedSuccessorEquiv
    (X : Type*)
    (bridgeEquiv : RootedBridgePointed n h₀ h r m (b + 1) ≃ X) :
    (RootedPointed n h₀ h r m (b + 1) × Bool) ≃
      (RootedStratum n h₀ h r (m + 2) b × Fin r) ⊕
        (X × Bool) :=
  (rootedOrientedPointedEquivDichotomy n h₀ h r m (b + 1)).trans <|
    Equiv.sumCongr
      (rootedNonbridgeEquiv
        (n := n) (h₀ := h₀) (h := h) (r := r) (m := m) (b := b))
      (bridgeEquiv.prodCongr (Equiv.refl Bool))

/-! ## Rank-zero `R` and `T` equivalences -/

/-- At rank zero every unrooted seam is a bridge, so the global tree cut is
just the bridge equivalence after the exact all-bridges identification. -/
def unrootedTreeEquiv
    (X : Type*)
    (bridgeEquiv :
      (UnrootedBridgePointed n h r m 0 × Bool) ≃ X) :
    (UnrootedPointed n h r m 0 × Bool) ≃ X :=
  ((TreeBridgeIdentity.unrootedTreePointedEquivBridge n h r m).prodCongr
      (Equiv.refl Bool)).trans bridgeEquiv

/-- Rooted rank-zero global cut.  No endpoint-exchange Boolean is introduced
because the component containing the fixed base is canonical. -/
def rootedTreeEquiv
    (X : Type*)
    (bridgeEquiv : RootedBridgePointed n h₀ h r m 0 ≃ X) :
    RootedPointed n h₀ h r m 0 ≃ X :=
  (TreeBridgeIdentity.rootedTreePointedEquivBridge n h₀ h r m).trans
    bridgeEquiv


end
end GlobalCutJoinAssembly
end FacetPairing
end PolytopeCounting
