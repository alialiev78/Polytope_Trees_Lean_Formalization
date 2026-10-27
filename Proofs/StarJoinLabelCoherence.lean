module

public import Proofs.NonbridgeExact
public import Proofs.NonbridgeEquiv
public import Proofs.BridgeLabelledRestriction

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Boundary-label coherence for the canonical star join

`NonbridgeExact.joinStarBoundaryLabel` labels the boundary remaining after
the two canonical star darts are joined.  Cutting the newly inserted seam
with the first star as its chosen orientation must recover the entire
original `Fin (m+2)` labelling, not only the coloured matching.  This file
records that extensional equality explicitly.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace StarJoinLabelCoherence

noncomputable section

open LabelledCutJoin NonbridgeExact NonbridgeEquiv

universe uD

variable {D : Type uD} [DecidableEq D] {r m : ℕ}

theorem boundaryEquivOfEq_symm_val
    {P Q : ColoredMatching D r} (h : P = Q) (x : Q.Boundary) :
    ((_root_.PolytopeCounting.FacetPairing.boundaryEquivOfEq h).symm x).1 =
      x.1 := by
  subst Q
  rfl

theorem orientedBoundaryEraseEquiv_old
    (M : PartialMatching D) (o : M.OrientedSeam)
    (z : (M.erase o.1).Boundary) (hfree : z.1 ∉ M.occupied) :
    M.orientedBoundaryEraseEquiv o z = Sum.inl ⟨z.1, hfree⟩ := by
  classical
  simp only [PartialMatching.orientedBoundaryEraseEquiv, Equiv.trans_apply,
    Equiv.sumCongr_apply, subtypeOrEquiv, Equiv.coe_fn_mk]
  rw [subtypeOrLeftEmbedding_apply_left _ hfree]
  rfl

theorem orientedBoundaryEraseEquiv_endpoint
    (M : PartialMatching D) (o : M.OrientedSeam)
    (z : (M.erase o.1).Boundary) (hnotfree : ¬ z.1 ∉ M.occupied) :
    M.orientedBoundaryEraseEquiv o z =
      Sum.inr (if z.1 = o.2.1 then false else true) := by
  classical
  simp only [PartialMatching.orientedBoundaryEraseEquiv, Equiv.trans_apply,
    Equiv.sumCongr_apply, subtypeOrEquiv, Equiv.coe_fn_mk]
  rw [subtypeOrLeftEmbedding_apply_right _ hnotfree]
  rfl

/-- The oriented new seam of the canonical star join, with the first star
dart selected as its first endpoint. -/
def starJoinOrientation
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r) :
    (joinStarsMarked (Q, c)).1.matching.OrientedSeam := by
  let e := (joinStarsMarked (Q, c)).2
  refine ⟨e, ⟨(firstStarDart Q).1, ?_⟩⟩
  rw [show e.1 = (starFreePair Q).pair from
    ColoredMatching.freePairNewSeam_val Q.pairing
      (starFreePairDatum Q c)]
  rw [starFreePair_pair, Sym2.mem_iff]
  exact Or.inl rfl

@[simp]
theorem starJoinOrientation_first
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r) :
    (starJoinOrientation Q c).2.1 = (firstStarDart Q).1 := rfl

/-- Cutting the canonical star join recovers the original boundary label
pointwise.  The equality transports the cut boundary across the exact
`erase_join_newSeam` matching equality. -/
theorem orientedCut_starJoin_label
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r) :
    let P := (joinStarsMarked (Q, c)).1
    let o := starJoinOrientation Q c
    let hmatching : P.erase o.1 = Q.pairing := cut_joinStars_pairing (Q, c)
    (_root_.PolytopeCounting.FacetPairing.boundaryEquivOfEq hmatching).symm.trans
        (P.matching.orientedCutBoundaryLabel o (joinedBoundaryLabel Q c)) =
      Q.label := by
  classical
  dsimp only
  apply Equiv.ext
  intro q
  let P := (joinStarsMarked (Q, c)).1
  let o := starJoinOrientation Q c
  let hmatching : P.erase o.1 = Q.pairing := cut_joinStars_pairing (Q, c)
  let z : (P.erase o.1).Boundary :=
    (_root_.PolytopeCounting.FacetPairing.boundaryEquivOfEq hmatching).symm q
  have hzval : z.1 = q.1 := boundaryEquivOfEq_symm_val hmatching q
  change P.matching.orientedCutBoundaryLabel o
      (joinedBoundaryLabel Q c) z = Q.label q
  by_cases hfirst : q = firstStarDart Q
  · have hz : z.1 = (firstStarDart Q).1 :=
      hzval.trans (congrArg Subtype.val hfirst)
    have hendpoint : z.1 = o.2.1 := by
      exact hz
    have hocc : z.1 ∈ P.matching.occupied := by
      rw [PartialMatching.mem_occupied_iff]
      exact ⟨o.1.1, o.1.2, hendpoint ▸ o.2.2⟩
    simp only [PartialMatching.orientedCutBoundaryLabel, Equiv.trans_apply]
    rw [orientedBoundaryEraseEquiv_endpoint P.matching o z
      (not_not.mpr hocc)]
    simp only [Equiv.sumCongr_apply]
    change Fin.natAdd m (finTwoEquiv.symm
      (if z.1 = o.2.1 then false else true)) = Q.label q
    rw [if_pos hendpoint]
    rw [hfirst]
    simp [firstStarDart, firstStar, finTwoEquiv]
    apply Fin.ext
    rfl
  · by_cases hsecond : q = secondStarDart Q
    · have hz : z.1 = (secondStarDart Q).1 :=
        hzval.trans (congrArg Subtype.val hsecond)
      have hendpoint : z.1 ≠ o.2.1 := by
        intro heq
        apply firstStarDart_ne_secondStarDart Q
        exact (starJoinOrientation_first Q c).symm.trans
          (heq.symm.trans hz)
      have hocc : z.1 ∈ P.matching.occupied := by
        rw [PartialMatching.mem_occupied_iff]
        exact ⟨o.1.1, o.1.2, by
          rw [show o.1.1 = (starFreePair Q).pair from
            ColoredMatching.freePairNewSeam_val Q.pairing
              (starFreePairDatum Q c)]
          rw [starFreePair_pair, Sym2.mem_iff]
          exact Or.inr hz⟩
      simp only [PartialMatching.orientedCutBoundaryLabel, Equiv.trans_apply]
      rw [orientedBoundaryEraseEquiv_endpoint P.matching o z
        (not_not.mpr hocc)]
      simp only [Equiv.sumCongr_apply]
      change Fin.natAdd m (finTwoEquiv.symm
        (if z.1 = o.2.1 then false else true)) = Q.label _
      rw [if_neg hendpoint]
      rw [hsecond]
      simp [secondStarDart, secondStar, finTwoEquiv]
      apply Fin.ext
      rfl
    · have hfreeP : z.1 ∉ P.matching.occupied := by
        intro hocc
        obtain ⟨e, he, hze⟩ := (P.matching.mem_occupied_iff z.1).mp hocc
        have heq : e = o.1.1 := by
          have herased : e ∉ (P.erase o.1).matching.seams := by
            intro her
            exact z.2 ((P.erase o.1).matching.mem_occupied_iff z.1 |>.mpr
              ⟨e, her, hze⟩)
          have heq' : e = o.1.1 := by
            by_contra hne
            exact herased (Finset.mem_erase.mpr ⟨hne, he⟩)
          exact heq'
        subst e
        have hp : z.1 = (firstStarDart Q).1 ∨
            z.1 = (secondStarDart Q).1 := by
          rw [show o.1.1 = (starFreePair Q).pair from
            ColoredMatching.freePairNewSeam_val Q.pairing
              (starFreePairDatum Q c)] at hze
          simpa [starFreePair_pair] using Sym2.mem_iff.mp hze
        rcases hp with hp | hp
        · exact hfirst (Subtype.ext (hzval.symm.trans hp))
        · exact hsecond (Subtype.ext (hzval.symm.trans hp))
      simp only [PartialMatching.orientedCutBoundaryLabel, Equiv.trans_apply]
      rw [orientedBoundaryEraseEquiv_old P.matching o z hfreeP]
      simp only [Equiv.sumCongr_apply]
      change Fin.castAdd 2 (joinedBoundaryLabel Q c
        ⟨z.1, hfreeP⟩) = Q.label q
      apply Fin.eq_of_val_eq
      change (Q.label (joinedBoundaryAsOld Q c ⟨z.1, hfreeP⟩)).val =
        (Q.label q).val
      congr 2
      exact Subtype.ext hzval


end
end StarJoinLabelCoherence
end FacetPairing
end PolytopeCounting
