module

public import Proofs.RootedNumericalBridgeCoproductSourceReassembly
public import Proofs.OrientedCutJoinCoherence

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

open RootedGlobalBridgeCut PointedDecomposition LabelledCutJoin

@[simp]
theorem domainEncoding_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    RootedGlobalBridgeCut.domainEncoding (fromCoproduct d) =
      starJoinMarkedLabelled (reconstructedCutRaw d) (bridgeColor d) := by
  rfl

theorem baseOrientedCarrier_deletedColor_source
    (z : RootedBridgePointed n h₀ h r m b) :
    (baseOrientedCarrier z).deletedColor =
      z.1.1.1.raw.pairing.color z.1.2 := by
  rw [(baseOrientedCarrier z).deletedColor_eq]
  change (cutBridge z).core.1.2.color = _
  rw [cutBridge_core_eq_cutLabelled]
  rfl

theorem fromCoproduct_toCoproduct_of_raw
    (z : RootedBridgePointed n h₀ h r m b)
    (hraw : reconstructedCutRaw (toCoproduct z) =
      OrientedCutJoinCoherence.orientedCutRaw
        z.1.1.1.raw (baseOrientedSeam z)) :
    fromCoproduct (toCoproduct z) = z := by
  apply RootedGlobalBridgeCut.domainEncoding_injective
  rw [domainEncoding_fromCoproduct, hraw]
  change starJoinMarkedLabelled
      (OrientedCutJoinCoherence.orientedCutRaw
        z.1.1.1.raw (baseOrientedSeam z))
      (baseOrientedCarrier z).deletedColor =
    RootedGlobalBridgeCut.domainEncoding z
  rw [baseOrientedCarrier_deletedColor_source]
  exact OrientedCutJoinCoherence.starJoinMarkedLabelled_orientedCutRaw
    z.1.1.1.raw (baseOrientedSeam z)


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

