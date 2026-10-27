module

public import Proofs.StarJoinMarkedLabelled
public import Proofs.StarJoinLabelCoherence
public import Proofs.BoundaryLabelledHEq
public import Proofs.StarAllocation

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Exact coherence of an oriented cut followed by the canonical star join

The chosen endpoint receives the first reserved boundary label.  Therefore
the two star preimages recover the erased seam itself, and the label obtained
after rejoining is exactly the original old-boundary label.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace OrientedCutJoinCoherence

noncomputable section

open LabelledCutJoin NonbridgeEquiv

universe u
variable {D : Type u} [DecidableEq D]
variable {r m : ℕ}

/-- Full boundary-labelled cut with an explicitly chosen first endpoint. -/
def orientedCutRaw
    (P : BoundaryLabelledPairing D r m)
    (o : P.pairing.matching.OrientedSeam) :
    BoundaryLabelledPairing D r (m + 2) where
  pairing := P.pairing.erase o.1
  label := P.pairing.matching.orientedCutBoundaryLabel o P.label

def firstCutBoundary
    (P : BoundaryLabelledPairing D r m)
    (o : P.pairing.matching.OrientedSeam) :
    (orientedCutRaw P o).pairing.Boundary :=
  P.pairing.matching.endpointBoundaryAfterErase o.1 o.2.1 o.2.2

def secondCutBoundary
    (P : BoundaryLabelledPairing D r m)
    (o : P.pairing.matching.OrientedSeam) :
    (orientedCutRaw P o).pairing.Boundary :=
  P.pairing.matching.endpointBoundaryAfterErase o.1
    (P.pairing.matching.otherEndpoint o)
    (P.pairing.matching.otherEndpoint_mem o)

theorem orientedCutRaw_first
    (P : BoundaryLabelledPairing D r m)
    (o : P.pairing.matching.OrientedSeam) :
    (orientedCutRaw P o).label (firstCutBoundary P o) = firstStar m := by
  have hocc : (firstCutBoundary P o).1 ∈ P.pairing.matching.occupied :=
    (P.pairing.matching.mem_occupied_iff _).mpr
      ⟨o.1.1, o.1.2, o.2.2⟩
  have hb : P.pairing.matching.orientedBoundaryEraseEquiv o
      (firstCutBoundary P o) = Sum.inr false := by
    rw [StarJoinLabelCoherence.orientedBoundaryEraseEquiv_endpoint
      P.pairing.matching o (firstCutBoundary P o) (not_not.mpr hocc)]
    have hval : (firstCutBoundary P o).1 = o.2.1 := rfl
    rw [hval, if_pos rfl]
  change PartialMatching.finSumEquiv
      ((P.label.sumCongr finTwoEquiv.symm)
        (P.pairing.matching.orientedBoundaryEraseEquiv o
          (firstCutBoundary P o))) = firstStar m
  rw [hb]
  rfl

theorem orientedCutRaw_second
    (P : BoundaryLabelledPairing D r m)
    (o : P.pairing.matching.OrientedSeam) :
    (orientedCutRaw P o).label (secondCutBoundary P o) = secondStar m := by
  have hmem := P.pairing.matching.otherEndpoint_mem o
  have hocc : (secondCutBoundary P o).1 ∈ P.pairing.matching.occupied :=
    (P.pairing.matching.mem_occupied_iff _).mpr
      ⟨o.1.1, o.1.2, hmem⟩
  have hne : P.pairing.matching.otherEndpoint o ≠ o.2.1 :=
    (P.pairing.matching.oriented_endpoints_ne o).symm
  have hb : P.pairing.matching.orientedBoundaryEraseEquiv o
      (secondCutBoundary P o) = Sum.inr true := by
    rw [StarJoinLabelCoherence.orientedBoundaryEraseEquiv_endpoint
      P.pairing.matching o (secondCutBoundary P o) (not_not.mpr hocc)]
    have hval : (secondCutBoundary P o).1 =
        P.pairing.matching.otherEndpoint o := rfl
    rw [hval, if_neg hne]
  change PartialMatching.finSumEquiv
      ((P.label.sumCongr finTwoEquiv.symm)
        (P.pairing.matching.orientedBoundaryEraseEquiv o
          (secondCutBoundary P o))) = secondStar m
  rw [hb]
  rfl

theorem firstStarDart_orientedCutRaw
    (P : BoundaryLabelledPairing D r m)
    (o : P.pairing.matching.OrientedSeam) :
    (firstStarDart (orientedCutRaw P o)).1 = o.2.1 := by
  have hstar : (orientedCutRaw P o).label
      (firstStarDart (orientedCutRaw P o)) = firstStar m :=
    (orientedCutRaw P o).label.apply_symm_apply (firstStar m)
  have h := (orientedCutRaw P o).label.injective
    ((orientedCutRaw_first P o).trans hstar.symm)
  exact congrArg Subtype.val h.symm

theorem secondStarDart_orientedCutRaw
    (P : BoundaryLabelledPairing D r m)
    (o : P.pairing.matching.OrientedSeam) :
    (secondStarDart (orientedCutRaw P o)).1 =
      P.pairing.matching.otherEndpoint o := by
  have hstar : (orientedCutRaw P o).label
      (secondStarDart (orientedCutRaw P o)) = secondStar m :=
    (orientedCutRaw P o).label.apply_symm_apply (secondStar m)
  have h := (orientedCutRaw P o).label.injective
    ((orientedCutRaw_second P o).trans hstar.symm)
  exact congrArg Subtype.val h.symm

theorem starFreePair_orientedCutRaw
    (P : BoundaryLabelledPairing D r m)
    (o : P.pairing.matching.OrientedSeam) :
    (starFreePair (orientedCutRaw P o)).pair = o.1.1 := by
  rw [starFreePair_pair, firstStarDart_orientedCutRaw,
    secondStarDart_orientedCutRaw]
  exact Sym2.other_spec' o.2.2

/-- The free-pair carrier extracted from the two star labels is exactly the
carrier obtained by cutting the original marked coloured matching. -/
theorem boundaryLabelledToFreePair_orientedCutRaw
    (P : BoundaryLabelledPairing D r m)
    (o : P.pairing.matching.OrientedSeam) :
    boundaryLabelledToFreePair
        (orientedCutRaw P o, P.pairing.color o.1) =
      ColoredMatching.cutMarked ⟨P.pairing, o.1⟩ := by
  apply Sigma.ext
  · rfl
  · apply ColoredMatching.FreePairDatum.heq_of_pairing_eq rfl
    · exact starFreePair_orientedCutRaw P o
    · rfl

/-- The canonical star join reconstructs the original marked coloured
matching, including the exact distinguished seam. -/
theorem joinStarsMarked_orientedCutRaw
    (P : BoundaryLabelledPairing D r m)
    (o : P.pairing.matching.OrientedSeam) :
    joinStarsMarked (orientedCutRaw P o, P.pairing.color o.1) =
      (⟨P.pairing, o.1⟩ : ColoredMatching.MarkedColoredMatching D r) := by
  change ColoredMatching.joinSelected
      (boundaryLabelledToFreePair
        (orientedCutRaw P o, P.pairing.color o.1)) = _
  rw [boundaryLabelledToFreePair_orientedCutRaw]
  exact ColoredMatching.joinSelected_cutMarked ⟨P.pairing, o.1⟩

/-- After transporting along the reconstructed matching equality, removing
the two reserved star labels recovers the original boundary labelling. -/
theorem joinedBoundaryLabel_orientedCutRaw
    (P : BoundaryLabelledPairing D r m)
    (o : P.pairing.matching.OrientedSeam) :
    let Q := orientedCutRaw P o
    let c := P.pairing.color o.1
    let hjoin : (joinStarsMarked (Q, c)).1 = P.pairing :=
      congrArg Sigma.fst (joinStarsMarked_orientedCutRaw P o)
    joinedBoundaryLabel Q c = (boundaryEquivOfEq hjoin).trans P.label := by
  classical
  dsimp only
  let Q := orientedCutRaw P o
  let c := P.pairing.color o.1
  let hjoin : (joinStarsMarked (Q, c)).1 = P.pairing :=
    congrArg Sigma.fst (joinStarsMarked_orientedCutRaw P o)
  apply Equiv.ext
  intro x
  apply Fin.eq_of_val_eq
  let q := joinedBoundaryAsOld Q c x
  let px : P.pairing.Boundary := boundaryEquivOfEq hjoin x
  have hqval : q.1 = x.1 := rfl
  have hpxval : px.1 = x.1 := by
    exact NumericalBridgeCut.boundaryEquivOfEq_apply_val hjoin x
  have hfree : q.1 ∉ P.pairing.matching.occupied := by
    rw [hqval, ← hpxval]
    exact px.2
  change (Q.label q).val = (P.label px).val
  have hb : P.pairing.matching.orientedBoundaryEraseEquiv o q =
      Sum.inl ⟨q.1, hfree⟩ :=
    StarJoinLabelCoherence.orientedBoundaryEraseEquiv_old
      P.pairing.matching o q hfree
  change (PartialMatching.finSumEquiv
      ((P.label.sumCongr finTwoEquiv.symm)
        (P.pairing.matching.orientedBoundaryEraseEquiv o q))).val =
      (P.label px).val
  rw [hb]
  have hboundary : (⟨q.1, hfree⟩ : P.pairing.Boundary) = px := by
    apply Subtype.ext
    exact hqval.trans hpxval.symm
  rw [hboundary]
  rfl

/-- Full labelled reconstruction: an oriented cut followed by the canonical
star join is the identity on the original marked pairing. -/
theorem starJoinMarkedLabelled_orientedCutRaw
    (P : BoundaryLabelledPairing D r m)
    (o : P.pairing.matching.OrientedSeam) :
    LabelledCutJoin.starJoinMarkedLabelled (orientedCutRaw P o)
        (P.pairing.color o.1) =
      (⟨P, o.1⟩ : MarkedBoundaryLabelledPairing D r m) := by
  let hmarked := joinStarsMarked_orientedCutRaw P o
  let hpair :
      (joinStarsMarked
        (orientedCutRaw P o, P.pairing.color o.1)).1 = P.pairing :=
    congrArg Sigma.fst hmarked
  have boundaryLabel_transport_heq
      {R S : ColoredMatching D r} (hRS : R = S)
      (label : S.Boundary ≃ Fin m) :
      HEq ((boundaryEquivOfEq hRS).trans label) label := by
    cases hRS
    rfl
  have hlabel : HEq
      (joinedBoundaryLabel (orientedCutRaw P o) (P.pairing.color o.1))
      P.label := by
    have h := joinedBoundaryLabel_orientedCutRaw P o
    exact (heq_of_eq h).trans (boundaryLabel_transport_heq hpair P.label)
  have hBL :
      (⟨(joinStarsMarked
          (orientedCutRaw P o, P.pairing.color o.1)).1,
        joinedBoundaryLabel (orientedCutRaw P o)
          (P.pairing.color o.1)⟩ : BoundaryLabelledPairing D r m) = P := by
    exact eq_of_heq
      (BoundaryLabelledPairing.heq_ext rfl (heq_of_eq hpair) hlabel)
  apply Sigma.ext hBL
  exact (Sigma.ext_iff.mp hmarked).2

/-- Carrier form used by both global bridge inverses. -/
theorem starJoinCore_orientedCutRaw
    (P : BoundaryLabelledPairing D r m)
    (o : P.pairing.matching.OrientedSeam) :
    LabelledCutJoin.starJoinCore (orientedCutRaw P o)
        (P.pairing.color o.1) = cutLabelled ⟨P, o.1⟩ := by
  rw [← LabelledCutJoin.cutLabelled_starJoinMarkedLabelled,
    starJoinMarkedLabelled_orientedCutRaw]


end
end OrientedCutJoinCoherence
end FacetPairing
end PolytopeCounting
