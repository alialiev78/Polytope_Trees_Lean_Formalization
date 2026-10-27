module

public import Proofs.RootedNumericalBridgeCoproductExtension
public import Proofs.AllocationNormalization

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Exact cancellation for the rooted numerical bridge coproduct

This file is deliberately separated from the kernel-green construction and
forward-normalization layers.  We first identify the intrinsic component of
the reconstructed cut, and only then eliminate the dependent `Sigma`
indices from the outside in.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

open RootedGlobalBridgeCut PointedDecomposition LabelledCutJoin
open NumericalBridgeCut

/-! ## Uniqueness of the intrinsic base component -/

/-- A path in a no-crossing carrier which starts on the base side never
leaves the base side. -/
theorem carrier_path_stays_base
    (C : RootedBridgeCutCarrier n h₀ h r m b)
    {x y : RootedCell n} (hx : x ∈ C.baseCells)
    (p : Relation.ReflTransGen
      (C.core.1.1.Adjacent (rootedFacets h₀ h)) x y) :
    y ∈ C.baseCells := by
  induction p with
  | refl => exact hx
  | @tail u v huv huv' ih =>
      have hvSide : v ∈ C.baseCells ∨ v ∈ C.otherCells := by
        have : v ∈ C.baseCells ∪ C.otherCells := by
          rw [C.cover]
          exact Set.mem_univ v
        simpa only [Set.mem_union] using this
      exact hvSide.resolve_right (fun hv ↦ C.noCrossing ih hv huv')

/-- The restriction of the reconstructed cut to its literal allocated base
block is the independently reconstructed rooted component. -/
theorem reconstructedCut_restrict_base (d : Coproduct n h₀ h r m b) :
    (reconstructedCutPairing d).restrict (baseCellSet d) =
      (baseRestrictedPairing d).pairing := by
  exact ColoredMatching.restrict_reassembleColored_left
    (baseCellSet d) (otherCellSet d) (cellSets_disjoint d)
    (baseRestrictedPairing d).pairing
    (otherRestrictedPairing d).pairing

/-- The analogous exact restriction on the component away from the base. -/
theorem reconstructedCut_restrict_other (d : Coproduct n h₀ h r m b) :
    (reconstructedCutPairing d).restrict (otherCellSet d) =
      (otherRestrictedPairing d).pairing := by
  exact ColoredMatching.restrict_reassembleColored_right
    (baseCellSet d) (otherCellSet d) (cellSets_disjoint d)
    (baseRestrictedPairing d).pairing
    (otherRestrictedPairing d).pairing

/-- Any two cells in the allocated base block are connected by an ambient
path of the reconstructed cut. -/
theorem reconstructedCut_base_connected (d : Coproduct n h₀ h r m b)
    (x y : baseCellSet d) :
    Relation.ReflTransGen
      ((reconstructedCutPairing d).Adjacent (rootedFacets h₀ h)) x.1 y.1 := by
  have hlocal :
      ((reconstructedCutPairing d).restrict (baseCellSet d)).IsConnected
        (fun c : baseCellSet d ↦ rootedFacets h₀ h c.1) := by
    rw [reconstructedCut_restrict_base]
    exact baseRestrictedPairing_connected d
  have hlift := Relation.ReflTransGen.lift Subtype.val
    (fun u v huv ↦ ((reconstructedCutPairing d).adjacent_restrict_iff
      (baseCellSet d) u v).mp huv) _ _ (hlocal x y)
  simpa [Function.onFun] using hlift

/-- Any two cells in the complementary allocated block are connected by an
ambient path of the reconstructed cut. -/
theorem reconstructedCut_other_connected (d : Coproduct n h₀ h r m b)
    (x y : otherCellSet d) :
    Relation.ReflTransGen
      ((reconstructedCutPairing d).Adjacent (rootedFacets h₀ h)) x.1 y.1 := by
  have hlocal :
      ((reconstructedCutPairing d).restrict (otherCellSet d)).IsConnected
        (fun c : otherCellSet d ↦ rootedFacets h₀ h c.1) := by
    rw [reconstructedCut_restrict_other]
    exact otherRestrictedPairing_connected d
  have hlift := Relation.ReflTransGen.lift Subtype.val
    (fun u v huv ↦ ((reconstructedCutPairing d).adjacent_restrict_iff
      (otherCellSet d) u v).mp huv) _ _ (hlocal x y)
  simpa [Function.onFun] using hlift

/-- The cut core obtained from the reconstructed bridge is literally the
allocation-reassembled cut matching. -/
theorem baseOrientedCarrier_from_core_pairing
    (d : Coproduct n h₀ h r m b) :
    (baseOrientedCarrier (fromCoproduct d)).core.1.1 =
      reconstructedCutPairing d := by
  change (cutBridge (fromCoproduct d)).core.1.1 = _
  rw [cutBridge_core_pairing]
  exact erase_reconstructedJoinMarked d

/-- The intrinsic component containing the distinguished base is exactly
the stored base-side cell allocation. -/
theorem baseOrientedCarrier_from_baseCells
    (d : Coproduct n h₀ h r m b) :
    (baseOrientedCarrier (fromCoproduct d)).baseCells = baseCellSet d := by
  let C := baseOrientedCarrier (fromCoproduct d)
  have hcore : C.core.1.1 = reconstructedCutPairing d :=
    baseOrientedCarrier_from_core_pairing d
  ext x
  constructor
  · intro hx
    have hpRestr := C.baseConnected
      ⟨baseCell n, C.base_mem⟩ ⟨x, hx⟩
    have hp : Relation.ReflTransGen
        (C.core.1.1.Adjacent (rootedFacets h₀ h)) (baseCell n) x :=
      hpRestr.lift Subtype.val (fun u v huv ↦
        (C.core.1.1.adjacent_restrict_iff C.baseCells u v).mp huv)
    rw [hcore] at hp
    exact reconstructedCut_path_stays_base d (by
      simp [baseCell, baseCellSet]) hp
  · intro hx
    have hp : Relation.ReflTransGen
        ((reconstructedCutPairing d).Adjacent (rootedFacets h₀ h))
          (baseCell n) x :=
      reconstructedCut_base_connected d
        ⟨baseCell n, by simp [baseCell, baseCellSet]⟩ ⟨x, hx⟩
    rw [← hcore] at hp
    exact carrier_path_stays_base C C.base_mem hp

/-- The complementary intrinsic component is likewise recovered exactly. -/
theorem baseOrientedCarrier_from_otherCells
    (d : Coproduct n h₀ h r m b) :
    (baseOrientedCarrier (fromCoproduct d)).otherCells = otherCellSet d := by
  let C := baseOrientedCarrier (fromCoproduct d)
  ext x
  constructor
  · intro hx
    have hcover : x ∈ baseCellSet d ∨ x ∈ otherCellSet d := by
      have : x ∈ baseCellSet d ∪ otherCellSet d := by
        rw [cellSets_cover d]
        exact Set.mem_univ x
      simpa only [Set.mem_union] using this
    exact hcover.resolve_left (fun hxB ↦
      Set.disjoint_left.mp C.disjoint
        ((Set.ext_iff.mp (baseOrientedCarrier_from_baseCells d) x).mpr hxB) hx)
  · intro hx
    have hcover : x ∈ C.baseCells ∨ x ∈ C.otherCells := by
      have : x ∈ C.baseCells ∪ C.otherCells := by
        rw [C.cover]
        exact Set.mem_univ x
      simpa only [Set.mem_union] using this
    exact hcover.resolve_left (fun hxB ↦
      Set.disjoint_left.mp (cellSets_disjoint d)
        ((Set.ext_iff.mp (baseOrientedCarrier_from_baseCells d) x).mp hxB) hx)

/-! ## Recovery of the outer numerical indices -/

@[simp]
theorem forwardCellFinset_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    forwardCellFinset (fromCoproduct d) = (cells d).1 := by
  classical
  ext i
  simp only [forwardCellFinset, Set.mem_toFinset, baseOrdinaryCells,
    Set.mem_setOf_eq]
  rw [baseOrientedCarrier_from_baseCells]
  rfl

theorem baseOrientedCarrier_from_baseOrdinaryCount
    (d : Coproduct n h₀ h r m b) :
    (baseOrientedCarrier (fromCoproduct d)).baseOrdinaryCount = d.1.1 := by
  have hcard := forwardCellFinset_card (fromCoproduct d)
  rw [forwardCellFinset_fromCoproduct, (cells d).2] at hcard
  exact hcard.symm

@[simp]
theorem forwardCellIndex_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    forwardCellIndex (fromCoproduct d) = d.1 := by
  apply Fin.ext
  exact baseOrientedCarrier_from_baseOrdinaryCount d

theorem baseOrientedCarrier_from_base_seam_card
    (d : Coproduct n h₀ h r m b) :
    ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).baseCells).matching.seams.card =
        (baseRestrictedPairing d).pairing.matching.seams.card := by
  rw [baseOrientedCarrier_from_baseCells,
    baseOrientedCarrier_from_core_pairing,
    reconstructedCut_restrict_base]

theorem baseOrientedCarrier_from_other_seam_card
    (d : Coproduct n h₀ h r m b) :
    ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).otherCells).matching.seams.card =
        (otherRestrictedPairing d).pairing.matching.seams.card := by
  rw [baseOrientedCarrier_from_otherCells,
    baseOrientedCarrier_from_core_pairing,
    reconstructedCut_restrict_other]

theorem baseOrientedCarrier_from_baseRank
    (d : Coproduct n h₀ h r m b) :
    (baseOrientedCarrier (fromCoproduct d)).baseRank = d.2.2.1.1 := by
  let C := baseOrientedCarrier (fromCoproduct d)
  have hspec := C.baseRank_spec
  have hseam := baseOrientedCarrier_from_base_seam_card d
  rw [hseam] at hspec
  have hcard : Nat.card (baseCellSet d) = d.1.1 + 1 := by
    calc
      Nat.card (baseCellSet d) = Nat.card (RootedCell d.1.1) :=
        Nat.card_congr (baseCellEquiv d)
      _ = d.1.1 + 1 := by
        rw [Nat.card_eq_fintype_card, card_rootedCell]
  have hcardC : Nat.card C.baseCells = d.1.1 + 1 := by
    rw [show C.baseCells = baseCellSet d from
      baseOrientedCarrier_from_baseCells d]
    exact hcard
  have hlocal := baseRestrictedPairing_seam_card d
  dsimp only [C] at hspec hcardC
  omega

@[simp]
theorem forwardRankIndex_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    forwardRankIndex (fromCoproduct d) = d.2.2.1 := by
  apply Fin.ext
  exact baseOrientedCarrier_from_baseRank d

theorem baseOrientedCarrier_from_deletedColor
    (d : Coproduct n h₀ h r m b) :
    (baseOrientedCarrier (fromCoproduct d)).deletedColor = bridgeColor d := by
  change (cutBridge (fromCoproduct d)).deletedColor = _
  rw [(cutBridge (fromCoproduct d)).deletedColor_eq,
    cutBridge_core_eq_cutLabelled]
  change (reconstructedJoinMarked d).1.color
      (reconstructedJoinMarked d).2 = bridgeColor d
  exact cut_joinStars_color (reconstructedCutRaw d, bridgeColor d)

/-! ## Recovery of the star orientation and global cut label -/

theorem baseSelectedEndpoint_fromCoproduct_val
    (d : Coproduct n h₀ h r m b) :
    (baseSelectedEndpoint (fromCoproduct d)).1 =
      (firstStarDart (reconstructedCutRaw d)).1 := by
  have hm := (baseSelectedEndpoint (fromCoproduct d)).2
  change (baseSelectedEndpoint (fromCoproduct d)).1 ∈
    (reconstructedJoinMarked d).2.1 at hm
  rw [show (reconstructedJoinMarked d).2.1 =
      (starFreePair (reconstructedCutRaw d)).pair from
        ColoredMatching.freePairNewSeam_val
          (reconstructedCutRaw d).pairing
          (starFreePairDatum (reconstructedCutRaw d) (bridgeColor d)),
    starFreePair_pair, Sym2.mem_iff] at hm
  rcases hm with hfirst | hsecond
  · exact hfirst
  · exfalso
    let C := baseOrientedCarrier (fromCoproduct d)
    have hbaseC : (baseSelectedEndpoint (fromCoproduct d)).1.1 ∈
        C.baseCells := by
      change C.baseStar.1.1.1 ∈ C.baseCells
      exact C.baseStar.1.1.2
    have hbase : (baseSelectedEndpoint (fromCoproduct d)).1.1 ∈
        baseCellSet d := by
      rw [← baseOrientedCarrier_from_baseCells d]
      exact hbaseC
    have hsecondCell :
        (baseSelectedEndpoint (fromCoproduct d)).1.1 =
          (secondStarDart (reconstructedCutRaw d)).1.1 :=
      congrArg Sigma.fst hsecond
    exact Set.disjoint_left.mp (cellSets_disjoint d)
      (hsecondCell ▸ hbase) (secondStarDart_mem_otherCellSet d)

theorem baseSelectedEndpoint_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    baseSelectedEndpoint (fromCoproduct d) =
      (StarJoinLabelCoherence.starJoinOrientation
        (reconstructedCutRaw d) (bridgeColor d)).2 := by
  apply Subtype.ext
  exact baseSelectedEndpoint_fromCoproduct_val d

theorem baseOrientedSeam_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    baseOrientedSeam (fromCoproduct d) =
      StarJoinLabelCoherence.starJoinOrientation
        (reconstructedCutRaw d) (bridgeColor d) := by
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (baseSelectedEndpoint_fromCoproduct d)

set_option maxHeartbeats 1000000 in
theorem baseOrientedCutLabel_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    (boundaryEquivOfEq (erase_reconstructedJoinMarked d)).symm.trans
        (baseOrientedCutLabel (fromCoproduct d)) =
      (reconstructedCutRaw d).label := by
  have hstar := StarJoinLabelCoherence.orientedCut_starJoin_label
    (reconstructedCutRaw d) (bridgeColor d)
  unfold baseOrientedCutLabel
  change (boundaryEquivOfEq (erase_reconstructedJoinMarked d)).symm.trans
      ((reconstructedJoinMarked d).1.matching.orientedCutBoundaryLabel
        (baseOrientedSeam (fromCoproduct d))
        (NonbridgeEquiv.joinedBoundaryLabel
          (reconstructedCutRaw d) (bridgeColor d))) =
    (reconstructedCutRaw d).label
  let M := (reconstructedJoinMarked d).1
  let e : M.Seam := (reconstructedJoinMarked d).2
  let lab := NonbridgeEquiv.joinedBoundaryLabel
    (reconstructedCutRaw d) (bridgeColor d)
  let cutAt : {x : RootedDart n h₀ h // x ∈ e.1} →
      ((M.erase e).Boundary ≃ Fin (m + 2)) := fun x ↦
    M.matching.orientedCutBoundaryLabel ⟨e, x⟩ lab
  have hcutAt := congrArg cutAt (baseSelectedEndpoint_fromCoproduct d)
  change (boundaryEquivOfEq (erase_reconstructedJoinMarked d)).symm.trans
      (cutAt (baseSelectedEndpoint (fromCoproduct d))) =
    (reconstructedCutRaw d).label
  rw [hcutAt]
  exact hstar

/-! ## Recovery of the boundary allocation -/

/-- The reconstructed global label belongs to the allocated base block
exactly on boundary darts whose cells belong to the base allocation. -/
theorem reconstructedCutLabel_mem_base_iff
    (d : Coproduct n h₀ h r m b)
    (x : (reconstructedCutPairing d).Boundary) :
    reconstructedCutLabel d x ∈ (labels d).1 ↔
      x.1.1 ∈ baseCellSet d := by
  classical
  rcases hxcell : x.1.1 with u | i
  · cases u
    simp [reconstructedCutLabel, boundaryReassembleEquiv,
      baseCellSet, otherCellSet, hxcell, finsetSumComplementEquiv]
  · by_cases hi : i ∈ (cells d).1
    · have hx : x.1.1 ∈ baseCellSet d := by
        simpa only [baseCellSet, Set.mem_setOf_eq, cells, hxcell] using hi
      simp [reconstructedCutLabel, boundaryReassembleEquiv,
        baseCellSet, otherCellSet, hxcell, hi, finsetSumComplementEquiv]
    · have hx : x.1.1 ∈ otherCellSet d := by
        simpa only [otherCellSet, Set.mem_setOf_eq, cells, hxcell] using hi
      have hnot (y : (otherRestrictedPairing d).pairing.Boundary) :
          ((otherAllocatedLabel d) y).1 ∉ (labels d).1 :=
        ((otherAllocatedLabel d) y).2
      simp [reconstructedCutLabel, boundaryReassembleEquiv,
        baseCellSet, otherCellSet, hxcell, hi, finsetSumComplementEquiv]
      exact hnot _

set_option maxHeartbeats 1000000 in
theorem baseOrientedCarrier_from_base_label_mem
    (d : Coproduct n h₀ h r m b)
    (x : ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).baseCells).Boundary) :
    forwardBaseBoundaryMap (fromCoproduct d) x ∈ (labels d).1 := by
  let z := fromCoproduct d
  let C := baseOrientedCarrier z
  change ((C.core.1.1.restrict C.baseCells).Boundary) at x
  let E := boundaryReassembleEquiv C.baseCells C.otherCells C.cover C.disjoint
    (C.core.1.1.restrict C.baseCells)
    (C.core.1.1.restrict C.otherCells)
  let y : C.core.1.1.Boundary :=
    boundaryEquivOfEq C.reassemble_exact (E.symm (Sum.inl x))
  have hcut : C.core.1.1 =
      (baseOrientedMarked z).pairing.erase
        (baseOrientedMarked z).seamSubtype := cutBridge_core_pairing z
  let u : ((baseOrientedMarked z).pairing.erase
      (baseOrientedMarked z).seamSubtype).Boundary :=
    boundaryEquivOfEq hcut y
  let q : (reconstructedCutPairing d).Boundary :=
    boundaryEquivOfEq (erase_reconstructedJoinMarked d) u
  have hcoh : baseOrientedCutLabel z u = reconstructedCutLabel d q := by
    calc
      baseOrientedCutLabel z u =
          ((boundaryEquivOfEq (erase_reconstructedJoinMarked d)).symm.trans
            (baseOrientedCutLabel z))
            (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u) := by
              simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
              rfl
      _ = reconstructedCutLabel d
          (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u) :=
            congrArg (fun L ↦ L
              (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u))
              (baseOrientedCutLabel_fromCoproduct d)
      _ = reconstructedCutLabel d q := rfl
  change baseOrientedCutLabel z u ∈ (labels d).1
  rw [hcoh]
  apply (reconstructedCutLabel_mem_base_iff d q).2
  have hxcell : x.1.1.1 ∈ baseCellSet d := by
    have hxmem := x.1.1.2
    exact (Set.ext_iff.mp (baseOrientedCarrier_from_baseCells d) _).mp hxmem
  have hqcell : q.1.1 = x.1.1.1 := by
    simp only [q, u, y, E, boundaryEquivOfEq_val,
      boundaryReassembleEquiv_symm_inl, includeLeftBoundary_val]
    rfl
  rwa [hqcell]

set_option maxHeartbeats 1000000 in
theorem baseOrientedCarrier_from_other_label_not_mem
    (d : Coproduct n h₀ h r m b)
    (x : ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).otherCells).Boundary) :
    forwardOtherBoundaryMap (fromCoproduct d) x ∉ (labels d).1 := by
  let z := fromCoproduct d
  let C := baseOrientedCarrier z
  change ((C.core.1.1.restrict C.otherCells).Boundary) at x
  let E := boundaryReassembleEquiv C.baseCells C.otherCells C.cover C.disjoint
    (C.core.1.1.restrict C.baseCells)
    (C.core.1.1.restrict C.otherCells)
  let y : C.core.1.1.Boundary :=
    boundaryEquivOfEq C.reassemble_exact (E.symm (Sum.inr x))
  have hcut : C.core.1.1 =
      (baseOrientedMarked z).pairing.erase
        (baseOrientedMarked z).seamSubtype := cutBridge_core_pairing z
  let u : ((baseOrientedMarked z).pairing.erase
      (baseOrientedMarked z).seamSubtype).Boundary :=
    boundaryEquivOfEq hcut y
  let q : (reconstructedCutPairing d).Boundary :=
    boundaryEquivOfEq (erase_reconstructedJoinMarked d) u
  have hcoh : baseOrientedCutLabel z u = reconstructedCutLabel d q := by
    calc
      baseOrientedCutLabel z u =
          ((boundaryEquivOfEq (erase_reconstructedJoinMarked d)).symm.trans
            (baseOrientedCutLabel z))
            (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u) := by
              simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
              rfl
      _ = reconstructedCutLabel d
          (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u) :=
            congrArg (fun L ↦ L
              (boundaryEquivOfEq (erase_reconstructedJoinMarked d) u))
              (baseOrientedCutLabel_fromCoproduct d)
      _ = reconstructedCutLabel d q := rfl
  change baseOrientedCutLabel z u ∉ (labels d).1
  rw [hcoh]
  intro hlabel
  have hqbase := (reconstructedCutLabel_mem_base_iff d q).1 hlabel
  have hxother : x.1.1.1 ∈ otherCellSet d := by
    have hxmem := x.1.1.2
    exact (Set.ext_iff.mp (baseOrientedCarrier_from_otherCells d) _).mp hxmem
  have hqcell : q.1.1 = x.1.1.1 := by
    simp only [q, u, y, E, boundaryEquivOfEq_val,
      boundaryReassembleEquiv_symm_inr, includeRightBoundary_val]
    rfl
  exact Set.disjoint_left.mp (cellSets_disjoint d)
    (hqcell ▸ hqbase) hxother

@[simp]
theorem forwardBaseBoundaryLabels_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    forwardBaseBoundaryLabels (fromCoproduct d) = (labels d).1 := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨x, rfl⟩ :=
      (mem_forwardBaseBoundaryLabels_iff (fromCoproduct d) i).mp hi
    exact baseOrientedCarrier_from_base_label_mem d x
  · intro hi
    have hcover := forwardBoundaryLabels_cover (fromCoproduct d)
    have hiUnion : i ∈ forwardBaseBoundaryLabels (fromCoproduct d) ∨
        i ∈ forwardOtherBoundaryLabels (fromCoproduct d) := by
      have : i ∈ forwardBaseBoundaryLabels (fromCoproduct d) ∪
          forwardOtherBoundaryLabels (fromCoproduct d) := by
        rw [hcover]
        exact Finset.mem_univ i
      simpa only [Finset.mem_union] using this
    rcases hiUnion with hiB | hiO
    · exact hiB
    · obtain ⟨x, hx⟩ :=
        (mem_forwardOtherBoundaryLabels_iff (fromCoproduct d) i).mp hiO
      exact False.elim (baseOrientedCarrier_from_other_label_not_mem d x
        (hx ▸ hi))

@[simp]
theorem forwardBoundaryIndex_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    forwardBoundaryIndex (fromCoproduct d) = d.2.1 := by
  apply Fin.ext
  have hcard := (labels d).2.2.2
  change (forwardBaseBoundaryLabels (fromCoproduct d)).card - 1 = d.2.1.1
  rw [forwardBaseBoundaryLabels_fromCoproduct, hcard]
  omega

/-- Heterogeneous equality is the natural exact statement for allocation
fibres before the enclosing dependent indices have been eliminated. -/
theorem forwardCellAllocation_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    HEq (forwardCellAllocation (fromCoproduct d)) (cells d) := by
  have hval : (forwardCellIndex (fromCoproduct d)).1 = d.1.1 :=
    congrArg Fin.val (forwardCellIndex_fromCoproduct d)
  apply (Subtype.heq_iff_coe_eq (fun A : Finset (Fin n) ↦ by
    rw [hval])).2
  exact forwardCellFinset_fromCoproduct d

theorem forwardBoundaryAllocation_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    HEq (forwardBoundaryAllocation (fromCoproduct d)) (labels d) := by
  have hval : (forwardBoundaryIndex (fromCoproduct d)).1 = d.2.1.1 :=
    congrArg Fin.val (forwardBoundaryIndex_fromCoproduct d)
  apply (Subtype.heq_iff_coe_eq
    (fun B : Finset (Fin (m + 2)) ↦ by rw [hval])).2
  exact forwardBaseBoundaryLabels_fromCoproduct d

/-! ## Exact source-restriction cancellation -/

theorem carrierBaseRestriction_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    HEq ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).baseCells)
      (baseRestrictedPairing d).pairing := by
  let C := baseOrientedCarrier (fromCoproduct d)
  have hS : C.baseCells = baseCellSet d :=
    baseOrientedCarrier_from_baseCells d
  have hQ : C.core.1.1 = reconstructedCutPairing d :=
    baseOrientedCarrier_from_core_pairing d
  have h1 : C.core.1.1.restrict C.baseCells =
      (reconstructedCutPairing d).restrict C.baseCells :=
    congrArg (fun Q : ColoredMatching (RootedDart n h₀ h) r ↦
      Q.restrict C.baseCells) hQ
  have h2 : HEq ((reconstructedCutPairing d).restrict C.baseCells)
      ((reconstructedCutPairing d).restrict (baseCellSet d)) :=
    congr_arg_heq (fun U : Set (RootedCell n) ↦
      (reconstructedCutPairing d).restrict U) hS
  exact (heq_of_eq h1).trans <|
    h2.trans (heq_of_eq (reconstructedCut_restrict_base d))

theorem carrierOtherRestriction_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    HEq ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).otherCells)
      (otherRestrictedPairing d).pairing := by
  let C := baseOrientedCarrier (fromCoproduct d)
  have hS : C.otherCells = otherCellSet d :=
    baseOrientedCarrier_from_otherCells d
  have hQ : C.core.1.1 = reconstructedCutPairing d :=
    baseOrientedCarrier_from_core_pairing d
  have h1 : C.core.1.1.restrict C.otherCells =
      (reconstructedCutPairing d).restrict C.otherCells :=
    congrArg (fun Q : ColoredMatching (RootedDart n h₀ h) r ↦
      Q.restrict C.otherCells) hQ
  have h2 : HEq ((reconstructedCutPairing d).restrict C.otherCells)
      ((reconstructedCutPairing d).restrict (otherCellSet d)) :=
    congr_arg_heq (fun U : Set (RootedCell n) ↦
      (reconstructedCutPairing d).restrict U) hS
  exact (heq_of_eq h1).trans <|
    h2.trans (heq_of_eq (reconstructedCut_restrict_other d))


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

