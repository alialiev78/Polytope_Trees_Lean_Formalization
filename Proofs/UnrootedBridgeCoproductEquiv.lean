module

public import Proofs.UnrootedBridgeCoproductReassembly

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

namespace PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct
noncomputable section

open PointedDecomposition LabelledCutJoin GlobalBridgeCut NumericalBridgeCut

variable {n h r m b : ℕ}

abbrev MarkedEndpoint (D : Type*) [DecidableEq D] (r m : ℕ) :=
  Σ w : MarkedBoundaryLabelledPairing D r m,
    {x : D // x ∈ w.2.1}

def markedEndpointBool {D : Type*} [DecidableEq D]
    {r m : ℕ}
    (u : MarkedEndpoint D r m) : Bool :=
  u.1.1.pairing.matching.seamEndpointEquivBool u.1.2 u.2

theorem markedEndpointBool_selected
    (z : UnrootedBridgePointed n h r m b × Bool) :
    markedEndpointBool
        (⟨(GlobalBridgeCut.domainEncoding z).1, selectedEndpoint z⟩ :
          MarkedEndpoint (Dart n h) r m) = z.2 := by
  exact z.1.1.1.1.raw.pairing.matching.seamEndpointEquivBool
    z.1.1.2 |>.apply_symm_apply z.2

@[simp] theorem domainEncoding_fromCoproduct_fst
    (d : Coproduct n h r m b) :
    (GlobalBridgeCut.domainEncoding (fromCoproduct d)).1 =
      LabelledCutJoin.starJoinMarkedLabelled (reconstructedCutRaw d)
        d.2.2.2.2.2 := by
  rfl

theorem fromCoproduct_toCoproduct_of_raw
    (z : UnrootedBridgePointed n h r m b × Bool)
    (hraw : reconstructedCutRaw (toCoproduct z) =
      OrientedCutJoinCoherence.orientedCutRaw
        z.1.1.1.1.raw (orientedSeam z)) :
    fromCoproduct (toCoproduct z) = z := by
  apply GlobalBridgeCut.domainEncoding_injective
  have hmarked :
      (GlobalBridgeCut.domainEncoding (fromCoproduct (toCoproduct z))).1 =
        (GlobalBridgeCut.domainEncoding z).1 := by
    rw [domainEncoding_fromCoproduct_fst, hraw]
    change LabelledCutJoin.starJoinMarkedLabelled
        (OrientedCutJoinCoherence.orientedCutRaw
          z.1.1.1.1.raw (orientedSeam z))
        ((orientedCarrier z).deletedColor) =
      (⟨z.1.1.1.1.raw, z.1.1.2⟩ :
        MarkedBoundaryLabelledPairing (Dart n h) r m)
    rw [(orientedCarrier z).deletedColor_eq,
      orientedCarrier_core_color]
    exact OrientedCutJoinCoherence.starJoinMarkedLabelled_orientedCutRaw
      z.1.1.1.1.raw (orientedSeam z)
  have hfirst :
      (reconstructedOrientation (toCoproduct z)).1 =
        (selectedEndpoint z).1 := by
    change (firstStarDart (reconstructedCutRaw (toCoproduct z))).1 = _
    rw [hraw]
    simpa [orientedSeam, orientedMarked] using
      (OrientedCutJoinCoherence.firstStarDart_orientedCutRaw
        z.1.1.1.1.raw (orientedSeam z))
  have horiented :
      (⟨(GlobalBridgeCut.domainEncoding
            (fromCoproduct (toCoproduct z))).1,
          selectedEndpoint (fromCoproduct (toCoproduct z))⟩ :
        MarkedEndpoint (Dart n h) r m) =
      ⟨(GlobalBridgeCut.domainEncoding z).1, selectedEndpoint z⟩ := by
    have hpair :
        (GlobalBridgeCut.domainEncoding
            (fromCoproduct (toCoproduct z))).1.2.1 =
          (GlobalBridgeCut.domainEncoding z).1.2.1 :=
      congrArg (fun w : MarkedBoundaryLabelledPairing (Dart n h) r m ↦
        w.2.1) hmarked
    apply Sigma.ext hmarked
    rw [selectedEndpoint_fromCoproduct]
    exact (Subtype.heq_iff_coe_eq (by
      intro x
      rw [hpair])).2 hfirst
  apply Prod.ext
  · exact hmarked
  · calc
      (fromCoproduct (toCoproduct z)).2 =
          markedEndpointBool
            (⟨(GlobalBridgeCut.domainEncoding
                (fromCoproduct (toCoproduct z))).1,
              selectedEndpoint (fromCoproduct (toCoproduct z))⟩ :
              MarkedEndpoint (Dart n h) r m) :=
        (markedEndpointBool_selected
          (fromCoproduct (toCoproduct z))).symm
      _ = markedEndpointBool
            (⟨(GlobalBridgeCut.domainEncoding z).1, selectedEndpoint z⟩ :
              MarkedEndpoint (Dart n h) r m) := congrArg _ horiented
      _ = z.2 := markedEndpointBool_selected z

end
end PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct

/-!
# Exact unrooted bridge coproduct equivalence

This module closes both inverse laws after component restriction,
reindexing, allocation normalization, exact reassembly, and oriented
cut--join coherence.
-/

namespace PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct
noncomputable section

open PointedDecomposition GlobalBridgeCut

variable {n h r m b : ℕ}

/-- Reconstructing after cutting an arbitrary oriented marked bridge is
literally the identity, including the endpoint-exchange Boolean. -/
theorem fromCoproduct_toCoproduct
    (z : UnrootedBridgePointed n h r m b × Bool) :
    fromCoproduct (toCoproduct z) = z :=
  fromCoproduct_toCoproduct_of_raw z
    (reconstructedCutRaw_toCoproduct z)

/-- The unconditional finite equivalence between oriented marked bridges
and the allocation-enriched dependent coproduct of two connected numerical
component strata. -/
def bridgeEquiv (n h r m b : ℕ) :
    (UnrootedBridgePointed n h r m b × Bool) ≃ Coproduct n h r m b where
  toFun := toCoproduct
  invFun := fromCoproduct
  left_inv := fromCoproduct_toCoproduct
  right_inv := toCoproduct_fromCoproduct

@[simp] theorem bridgeEquiv_apply
    (z : UnrootedBridgePointed n h r m b × Bool) :
    bridgeEquiv n h r m b z = toCoproduct z := rfl

@[simp] theorem bridgeEquiv_symm_apply
    (d : Coproduct n h r m b) :
    (bridgeEquiv n h r m b).symm d = fromCoproduct d := rfl


end
end PolytopeCounting.FacetPairing.UnrootedBridgeCoproduct
