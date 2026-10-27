module

public import Proofs.RootedNumericalBridgeCoproductSourceOther

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

open RootedGlobalBridgeCut PointedDecomposition NumericalBridgeCut

theorem baseRestrictedPairing_pairing_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    HEq (baseRestrictedPairing (toCoproduct z)).pairing
      ((baseOrientedCarrier z).core.1.1.restrict
        (baseOrientedCarrier z).baseCells) := by
  exact congr_arg_heq
    (fun x : LocalPairingPackage n h₀ h r
      ((forwardBoundaryIndex z).1 + 1) ↦ x.2.pairing)
    (baseLocalPackage_toCoproduct z)

theorem otherLocalPackage_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    (⟨otherCellSet (toCoproduct z),
        otherRestrictedPairing (toCoproduct z)⟩ :
      LocalPairingPackage n h₀ h r
        (m - (forwardBoundaryIndex z).1 + 1)) =
      ⟨(baseOrientedCarrier z).otherCells,
        carrierOtherLocalPairing z⟩ := by
  apply Sigma.ext
  · exact otherCellSet_toCoproduct z
  · exact otherRestrictedPairing_toCoproduct z

theorem otherRestrictedPairing_pairing_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    HEq (otherRestrictedPairing (toCoproduct z)).pairing
      ((baseOrientedCarrier z).core.1.1.restrict
        (baseOrientedCarrier z).otherCells) := by
  exact congr_arg_heq
    (fun x : LocalPairingPackage n h₀ h r
      (m - (forwardBoundaryIndex z).1 + 1) ↦ x.2.pairing)
    (otherLocalPackage_toCoproduct z)

structure ReassemblyInput (n h₀ h r : ℕ) where
  baseCells : Set (RootedCell n)
  otherCells : Set (RootedCell n)
  disjoint : Disjoint baseCells otherCells
  basePairing : ColoredMatching
    (RestrictedDart (facets := rootedFacets h₀ h) baseCells) r
  otherPairing : ColoredMatching
    (RestrictedDart (facets := rootedFacets h₀ h) otherCells) r

theorem ReassemblyInput.ext
    {x y : ReassemblyInput n h₀ h r}
    (hbase : x.baseCells = y.baseCells)
    (hother : x.otherCells = y.otherCells)
    (hbasePairing : HEq x.basePairing y.basePairing)
    (hotherPairing : HEq x.otherPairing y.otherPairing) : x = y := by
  cases x with
  | mk S T hST P Q =>
    cases y with
    | mk S' T' hST' P' Q' =>
      dsimp only at hbase hother hbasePairing hotherPairing
      subst S'
      subst T'
      have hP : P = P' := eq_of_heq hbasePairing
      subst P'
      have hQ : Q = Q' := eq_of_heq hotherPairing
      subst Q'
      rfl

def reassemblyInputPairing (x : ReassemblyInput n h₀ h r) :
    ColoredMatching (RootedDart n h₀ h) r :=
  reassembleColored x.baseCells x.otherCells x.disjoint
    x.basePairing x.otherPairing

set_option maxHeartbeats 1000000 in
theorem reconstructedCutPairing_toCoproduct
    (z : RootedBridgePointed n h₀ h r m b) :
    reconstructedCutPairing (toCoproduct z) =
      (baseOrientedCarrier z).core.1.1 := by
  let C := baseOrientedCarrier z
  let d := toCoproduct z
  let xD : ReassemblyInput n h₀ h r :=
    ⟨baseCellSet d, otherCellSet d, cellSets_disjoint d,
      (baseRestrictedPairing d).pairing,
      (otherRestrictedPairing d).pairing⟩
  let xC : ReassemblyInput n h₀ h r :=
    ⟨C.baseCells, C.otherCells, C.disjoint,
      C.core.1.1.restrict C.baseCells,
      C.core.1.1.restrict C.otherCells⟩
  have hx : xD = xC := ReassemblyInput.ext
    (baseCellSet_toCoproduct z) (otherCellSet_toCoproduct z)
    (baseRestrictedPairing_pairing_toCoproduct z)
    (otherRestrictedPairing_pairing_toCoproduct z)
  have hr := congrArg reassemblyInputPairing hx
  change reconstructedCutPairing d = C.core.1.1
  calc
    reconstructedCutPairing d = reassemblyInputPairing xD := rfl
    _ = reassemblyInputPairing xC := hr
    _ = C.core.1.1 := C.reassemble_exact


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

