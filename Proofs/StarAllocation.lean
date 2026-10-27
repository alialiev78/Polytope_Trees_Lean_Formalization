module

public import Proofs.NumericalBridgeCut

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

namespace PolytopeCounting
namespace FacetPairing
namespace NumericalBridgeCut

noncomputable section

open PointedDecomposition LabelledCutJoin GlobalBridgeCut

variable {n h r m b : ℕ}

theorem boundaryEquivOfEq_apply_val
    {D : Type*} [DecidableEq D] {P Q : ColoredMatching D r}
    (hPQ : P = Q) (x : P.Boundary) :
    (boundaryEquivOfEq hPQ x).1 = x.1 := by
  subst Q
  rfl

theorem bridgeCutComponentBoundaryLabel_leftEndpoint
    (P : BoundaryLabelledPairing (Dart n h) r m)
    (e : P.pairing.Seam)
    (hconnected : P.pairing.IsConnected (fun _ : Fin n ↦ h))
    (hbridge : P.pairing.IsBridge e) :
    let Q := P.pairing.erase e
    let S := BridgePartition.LeftClass
      (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.leftCell e)
    let hstar := (bridge_exposed_endpoints_on_opposite_sides
      P.pairing e hconnected hbridge).1
    bridgeCutComponentBoundaryLabel P e hconnected hbridge
      (Sum.inl (restrictBoundary Q S
        (P.pairing.matching.leftBoundaryAfterErase e) hstar)) = firstStar m := by
  dsimp only
  let Q := P.pairing.erase e
  let C := P.pairing.bridge_partition e hconnected hbridge
  let S := BridgePartition.LeftClass
    (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.leftCell e)
  let T := BridgePartition.RightClass
    (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.rightCell e)
  let x := P.pairing.matching.leftBoundaryAfterErase e
  let hx := (bridge_exposed_endpoints_on_opposite_sides
    P.pairing e hconnected hbridge).1
  let hreassemble :
      reassembleColored S T C.disjoint (Q.restrict S) (Q.restrict T) = Q :=
    erase_bridge_reassemble_exact P.pairing e hconnected hbridge
  change P.pairing.matching.cutBoundaryLabel e P.label
    ((boundaryEquivOfEq hreassemble)
      ((boundaryReassembleEquiv S T C.cover C.disjoint
        (Q.restrict S) (Q.restrict T)).symm
          (Sum.inl (restrictBoundary Q S x hx)))) = firstStar m
  have hrecover :
      (boundaryEquivOfEq hreassemble)
          ((boundaryReassembleEquiv S T C.cover C.disjoint
            (Q.restrict S) (Q.restrict T)).symm
              (Sum.inl (restrictBoundary Q S x hx))) = x := by
    apply Subtype.ext
    rw [boundaryEquivOfEq_apply_val,
      boundaryReassembleEquiv_symm_inl, includeLeftBoundary_val,
      includeDart_restrictBoundary]
  rw [hrecover]
  exact cutBoundaryLabel_leftEndpoint P.pairing.matching e P.label

theorem bridgeCutComponentBoundaryLabel_rightEndpoint
    (P : BoundaryLabelledPairing (Dart n h) r m)
    (e : P.pairing.Seam)
    (hconnected : P.pairing.IsConnected (fun _ : Fin n ↦ h))
    (hbridge : P.pairing.IsBridge e) :
    let Q := P.pairing.erase e
    let T := BridgePartition.RightClass
      (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.rightCell e)
    let hstar := (bridge_exposed_endpoints_on_opposite_sides
      P.pairing e hconnected hbridge).2
    bridgeCutComponentBoundaryLabel P e hconnected hbridge
      (Sum.inr (restrictBoundary Q T
        (P.pairing.matching.rightBoundaryAfterErase e) hstar)) = secondStar m := by
  dsimp only
  let Q := P.pairing.erase e
  let C := P.pairing.bridge_partition e hconnected hbridge
  let S := BridgePartition.LeftClass
    (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.leftCell e)
  let T := BridgePartition.RightClass
    (Q.Adjacent (fun _ : Fin n ↦ h)) (P.pairing.rightCell e)
  let x := P.pairing.matching.rightBoundaryAfterErase e
  let hx := (bridge_exposed_endpoints_on_opposite_sides
    P.pairing e hconnected hbridge).2
  let hreassemble :
      reassembleColored S T C.disjoint (Q.restrict S) (Q.restrict T) = Q :=
    erase_bridge_reassemble_exact P.pairing e hconnected hbridge
  change P.pairing.matching.cutBoundaryLabel e P.label
    ((boundaryEquivOfEq hreassemble)
      ((boundaryReassembleEquiv S T C.cover C.disjoint
        (Q.restrict S) (Q.restrict T)).symm
          (Sum.inr (restrictBoundary Q T x hx)))) = secondStar m
  have hrecover :
      (boundaryEquivOfEq hreassemble)
          ((boundaryReassembleEquiv S T C.cover C.disjoint
            (Q.restrict S) (Q.restrict T)).symm
              (Sum.inr (restrictBoundary Q T x hx))) = x := by
    apply Subtype.ext
    rw [boundaryEquivOfEq_apply_val,
      boundaryReassembleEquiv_symm_inr, includeRightBoundary_val,
      includeDart_restrictBoundary]
  rw [hrecover]
  exact cutBoundaryLabel_rightEndpoint P.pairing.matching e P.label

theorem cutBridge_leftStar_label
    (z : UnrootedBridgePointed n h r m b × Bool) :
    leftBoundaryLabelMap (cutBridge z) (cutBridge z).leftStar =
      if z.2 then secondStar m else firstStar m := by
  rcases z with ⟨⟨⟨P, e⟩, hbridge⟩, orientation⟩
  cases orientation with
  | false =>
      exact bridgeCutComponentBoundaryLabel_leftEndpoint
        P.1.raw e P.1.connected hbridge
  | true =>
      exact bridgeCutComponentBoundaryLabel_rightEndpoint
        P.1.raw e P.1.connected hbridge

theorem cutBridge_rightStar_label
    (z : UnrootedBridgePointed n h r m b × Bool) :
    rightBoundaryLabelMap (cutBridge z) (cutBridge z).rightStar =
      if z.2 then firstStar m else secondStar m := by
  rcases z with ⟨⟨⟨P, e⟩, hbridge⟩, orientation⟩
  cases orientation with
  | false =>
      exact bridgeCutComponentBoundaryLabel_rightEndpoint
        P.1.raw e P.1.connected hbridge
  | true =>
      exact bridgeCutComponentBoundaryLabel_leftEndpoint
        P.1.raw e P.1.connected hbridge

theorem cutBridge_star_allocation_split
    (z : UnrootedBridgePointed n h r m b × Bool) :
    ((firstStar m ∈ leftBoundaryLabels (cutBridge z) ∧
        secondStar m ∉ leftBoundaryLabels (cutBridge z)) ∨
      (secondStar m ∈ leftBoundaryLabels (cutBridge z) ∧
        firstStar m ∉ leftBoundaryLabels (cutBridge z))) := by
  cases hz : z.2 with
  | false =>
      left
      constructor
      · apply (mem_leftBoundaryLabels_iff (cutBridge z) _).mpr
        exact ⟨(cutBridge z).leftStar, by
          simpa [hz] using cutBridge_leftStar_label z⟩
      · intro hleft
        have hright : secondStar m ∈ rightBoundaryLabels (cutBridge z) := by
          apply (mem_rightBoundaryLabels_iff (cutBridge z) _).mpr
          exact ⟨(cutBridge z).rightStar, by
            simpa [hz] using cutBridge_rightStar_label z⟩
        exact Finset.disjoint_left.mp
          (boundaryLabelAllocations_disjoint (cutBridge z)) hleft hright
  | true =>
      right
      constructor
      · apply (mem_leftBoundaryLabels_iff (cutBridge z) _).mpr
        exact ⟨(cutBridge z).leftStar, by
          simpa [hz] using cutBridge_leftStar_label z⟩
      · intro hleft
        have hright : firstStar m ∈ rightBoundaryLabels (cutBridge z) := by
          apply (mem_rightBoundaryLabels_iff (cutBridge z) _).mpr
          exact ⟨(cutBridge z).rightStar, by
            simpa [hz] using cutBridge_rightStar_label z⟩
        exact Finset.disjoint_left.mp
          (boundaryLabelAllocations_disjoint (cutBridge z)) hleft hright


end
end NumericalBridgeCut
end FacetPairing
end PolytopeCounting
