module

public import Proofs.RootedNumericalBridgeCoproductCoproductExt
public import Proofs.RootedNumericalBridgeCoproductSourceSemantic
public import Proofs.RootedNumericalBridgeCoproductSourceRaw

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

open PointedDecomposition

/-- Assemble the concrete numerical maps into an equivalence once the
source-side raw cut normalization has been identified. -/
def bridgeEquivOfRaw
    (n h₀ h r m b : ℕ)
    (hraw : ∀ z : RootedBridgePointed n h₀ h r m b,
      reconstructedCutRaw (toCoproduct z) =
        OrientedCutJoinCoherence.orientedCutRaw
          z.1.1.1.raw (baseOrientedSeam z)) :
    RootedBridgePointed n h₀ h r m b ≃ Coproduct n h₀ h r m b where
  toFun := toCoproduct
  invFun := fromCoproduct
  left_inv z := fromCoproduct_toCoproduct_of_raw z (hraw z)
  right_inv := toCoproduct_fromCoproduct

@[simp]
theorem fromCoproduct_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    fromCoproduct (toCoproduct z) = z :=
  fromCoproduct_toCoproduct_of_raw z
    (reconstructedCutRaw_toCoproduct z)

/-- Exact lossless equivalence between rooted bridge-pointed strata and the
allocation-enriched numerical coproduct.  The component containing the
distinguished base is intrinsic, hence there is no component-exchange bit. -/
def bridgeEquiv (n h₀ h r m b : ℕ) :
    RootedBridgePointed n h₀ h r m b ≃ Coproduct n h₀ h r m b where
  toFun := toCoproduct
  invFun := fromCoproduct
  left_inv := fromCoproduct_toCoproduct
  right_inv := toCoproduct_fromCoproduct


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

