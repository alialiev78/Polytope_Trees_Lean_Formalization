module

public import Proofs.GlobalCutJoinAssembly
public import Proofs.UnrootedBridgeCoproductEquiv
public import Proofs.RootedNumericalBridgeCoproductEquivalence
public import Proofs.StratumBalanceSpecialization

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Concrete global `R`, `T`, `U`, and `Psi` cut--join equivalences

The generic global dichotomy is instantiated here with the realized
allocation-enriched bridge coproducts.  These are exact equivalences of
finite types, before taking cardinalities or groupoid masses.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace ConcreteGlobalCutJoin

noncomputable section

open PointedDecomposition
open StratumBalanceSpecialization

/-! ## Successor-rank cyclic strata -/

def U_equiv (n h r m b : ℕ) :
    (UnrootedPointed n h r m (b + 1) × Bool) ≃
      (UnrootedStratum n h r (m + 2) b × Fin r) ⊕
        UnrootedBridgeCoproduct.Coproduct n h r m (b + 1) :=
  GlobalCutJoinAssembly.unrootedSuccessorEquiv
    (UnrootedBridgeCoproduct.Coproduct n h r m (b + 1))
    (UnrootedBridgeCoproduct.bridgeEquiv n h r m (b + 1))

def Psi_equiv (n h₀ h r m b : ℕ) :
    (RootedPointed n h₀ h r m (b + 1) × Bool) ≃
      (RootedStratum n h₀ h r (m + 2) b × Fin r) ⊕
        (RootedNumericalBridgeCoproduct.Coproduct
          n h₀ h r m (b + 1) × Bool) :=
  GlobalCutJoinAssembly.rootedSuccessorEquiv
    (RootedNumericalBridgeCoproduct.Coproduct n h₀ h r m (b + 1))
    (RootedNumericalBridgeCoproduct.bridgeEquiv n h₀ h r m (b + 1))

/-! ## Rank-zero strata -/

/-- Exact rank-zero unrooted cut for an arbitrary boundary index. -/
def unrootedRankZeroEquiv (n h r m : ℕ) :
    (UnrootedPointed n h r m 0 × Bool) ≃
      UnrootedBridgeCoproduct.Coproduct n h r m 0 :=
  GlobalCutJoinAssembly.unrootedTreeEquiv
    (UnrootedBridgeCoproduct.Coproduct n h r m 0)
    (UnrootedBridgeCoproduct.bridgeEquiv n h r m 0)

/-- Exact rank-zero rooted cut for an arbitrary boundary index. -/
def rootedRankZeroEquiv (n h₀ h r m : ℕ) :
    RootedPointed n h₀ h r m 0 ≃
      RootedNumericalBridgeCoproduct.Coproduct n h₀ h r m 0 :=
  GlobalCutJoinAssembly.rootedTreeEquiv
    (RootedNumericalBridgeCoproduct.Coproduct n h₀ h r m 0)
    (RootedNumericalBridgeCoproduct.bridgeEquiv n h₀ h r m 0)

/-- Manuscript `R` equivalence at the forced tree boundary. -/
def R_equiv (n h r : ℕ) :
    (UnrootedPointed n h r (treeBoundary h n) 0 × Bool) ≃
      UnrootedBridgeCoproduct.Coproduct n h r (treeBoundary h n) 0 :=
  unrootedRankZeroEquiv n h r (treeBoundary h n)

/-- Manuscript fixed-base `T` equivalence at its forced tree boundary. -/
def T_equiv (n h₀ h r : ℕ) :
    RootedPointed n h₀ h r (rootedTreeBoundary h₀ h n) 0 ≃
      RootedNumericalBridgeCoproduct.Coproduct
        n h₀ h r (rootedTreeBoundary h₀ h n) 0 :=
  rootedRankZeroEquiv n h₀ h r (rootedTreeBoundary h₀ h n)


end
end ConcreteGlobalCutJoin
end FacetPairing
end PolytopeCounting
