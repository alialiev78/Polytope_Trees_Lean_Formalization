module

public import Proofs.RootedNumericalBridgeCoproductSourceBase

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

open RootedGlobalBridgeCut PointedDecomposition NumericalBridgeCut

universe u

abbrev LocalPairingPackage
    (n h₀ h r k : ℕ) :=
  Σ S : Set (RootedCell n),
    BoundaryLabelledPairing
      (RestrictedDart (facets := rootedFacets h₀ h) S) r k

def baseDenormalizedAllocation
    (A : Finset (Fin (m + 2))) (hA : A.card = k)
    (x : LocalPairingPackage n h₀ h r k) :
    x.2.pairing.Boundary ≃ {i : Fin (m + 2) // i ∈ A} :=
  x.2.label.trans <|
    (finCongr hA.symm).trans (finsetSubtypeEquivFin A).symm

theorem allocation_denormalizes
    {X I : Type u} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : A.card = k)
    (e : X ≃ {i : I // i ∈ A}) :
    (((e.trans (finsetSubtypeEquivFin A)).trans (finCongr hA)).trans
      ((finCongr hA.symm).trans
        (finsetSubtypeEquivFin A).symm)) = e := by
  apply Equiv.ext
  intro x
  simp

theorem baseLocalPackage_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    (⟨baseCellSet (toCoproduct z),
        baseRestrictedPairing (toCoproduct z)⟩ :
      LocalPairingPackage n h₀ h r
        ((forwardBoundaryIndex z).1 + 1)) =
      ⟨(baseOrientedCarrier z).baseCells,
        carrierBaseLocalPairing z⟩ := by
  apply Sigma.ext
  · exact baseCellSet_toCoproduct z
  · exact baseRestrictedPairing_toCoproduct z

set_option maxHeartbeats 1000000 in
theorem baseAllocatedLabel_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    HEq (baseAllocatedLabel (toCoproduct z))
      (forwardBaseBoundaryAllocationEquiv z) := by
  let A := forwardBaseBoundaryLabels z
  let hA := forwardBaseBoundaryCard_eq z
  let xD : LocalPairingPackage n h₀ h r ((forwardBoundaryIndex z).1 + 1) :=
    ⟨baseCellSet (toCoproduct z),
      baseRestrictedPairing (toCoproduct z)⟩
  let xC : LocalPairingPackage n h₀ h r ((forwardBoundaryIndex z).1 + 1) :=
    ⟨(baseOrientedCarrier z).baseCells, carrierBaseLocalPairing z⟩
  have hx : xD = xC := baseLocalPackage_toCoproduct z
  have hd : HEq (baseDenormalizedAllocation A hA xD)
      (baseDenormalizedAllocation A hA xC) :=
    congr_arg_heq (baseDenormalizedAllocation A hA) hx
  have hleft : baseDenormalizedAllocation A hA xD =
      baseAllocatedLabel (toCoproduct z) := by
    rfl
  have hright : baseDenormalizedAllocation A hA xC =
      forwardBaseBoundaryAllocationEquiv z := by
    change ((((forwardBaseBoundaryAllocationEquiv z).trans
      (finsetSubtypeEquivFin A)).trans (finCongr hA)).trans
        ((finCongr hA.symm).trans
          (finsetSubtypeEquivFin A).symm)) = _
    exact allocation_denormalizes A hA
      (forwardBaseBoundaryAllocationEquiv z)
  exact (heq_of_eq hleft.symm).trans <| hd.trans (heq_of_eq hright)


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

