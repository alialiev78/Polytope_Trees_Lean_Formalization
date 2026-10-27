module

public import Proofs.RootedNumericalBridgeCoproductInverse

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Component normalization cancellation for the rooted bridge coproduct

The choice of `Fintype.equivFin` is packaged together with its source data.
This makes equality of the independently chosen finite instances explicit
and prevents proof transports from obscuring the inverse law.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

open RootedGlobalBridgeCut NumericalBridgeCut

structure RootedComponentInput (n h₀ h r : ℕ) where
  cellSet : Set (RootedCell n)
  ordinarySet : Set (Fin n)
  ordinaryFintype : Fintype ordinarySet
  size : ℕ
  card_eq : @Fintype.card ordinarySet ordinaryFintype = size
  base_mem : baseCell n ∈ cellSet
  ordinary_iff : ∀ i : Fin n,
    (Sum.inr i : RootedCell n) ∈ cellSet ↔ i ∈ ordinarySet
  pairing : ColoredMatching
    (RestrictedDart (facets := rootedFacets h₀ h) cellSet) r

theorem RootedComponentInput.ext
    {x y : RootedComponentInput n h₀ h r}
    (hcell : x.cellSet = y.cellSet)
    (hordinary : x.ordinarySet = y.ordinarySet)
    (hfintype : HEq x.ordinaryFintype y.ordinaryFintype)
    (hsize : x.size = y.size)
    (hpairing : HEq x.pairing y.pairing) : x = y := by
  cases x with
  | mk X O fO k hk hb hi P =>
    cases y with
    | mk Y U fU l hl hb' hi' Q =>
      dsimp only at hcell hordinary hfintype hsize hpairing
      subst Y
      subst U
      have hf : fO = fU := eq_of_heq hfintype
      subst fU
      subst l
      have hPQ : P = Q := eq_of_heq hpairing
      subst Q
      rfl

def rootedInputCellEquiv (x : RootedComponentInput n h₀ h r) :
    x.cellSet ≃ RootedCell x.size := by
  letI : Fintype x.ordinarySet := x.ordinaryFintype
  let eO : x.ordinarySet ≃ Fin x.size :=
    (Fintype.equivFin _).trans (finCongr x.card_eq)
  refine
    { toFun := fun c ↦ match hc : c.1 with
        | Sum.inl u => Sum.inl u
        | Sum.inr i => Sum.inr (eO ⟨i, (x.ordinary_iff i).mp (by
            simpa only [hc] using c.2)⟩)
      invFun := fun c ↦ match c with
        | Sum.inl u => ⟨Sum.inl u, by cases u; exact x.base_mem⟩
        | Sum.inr i => ⟨Sum.inr (eO.symm i).1,
            (x.ordinary_iff _).mpr (eO.symm i).2⟩
      left_inv := by
        rintro ⟨c, hc⟩
        rcases c with u | i
        · cases u; rfl
        · apply Subtype.ext
          simp
      right_inv := by
        intro c
        rcases c with u | i
        · cases u; rfl
        · simp }

def rootedInputFacetEquiv (x : RootedComponentInput n h₀ h r)
    (c : x.cellSet) :
    Fin (rootedFacets h₀ h c.1) ≃
      Fin (rootedFacets h₀ h (rootedInputCellEquiv x c)) :=
  finCongr (by
    rcases c with ⟨u | i, hc⟩
    · rfl
    · rfl)

def rootedInputDartEquiv (x : RootedComponentInput n h₀ h r) :
    RestrictedDart (facets := rootedFacets h₀ h) x.cellSet ≃
      RootedDart x.size h₀ h :=
  Equiv.sigmaCongr (rootedInputCellEquiv x) (rootedInputFacetEquiv x)

def rootedComponentNormalize (x : RootedComponentInput n h₀ h r) :
    Σ k : ℕ, ColoredMatching (RootedDart k h₀ h) r :=
  ⟨x.size, x.pairing.reindex (rootedInputDartEquiv x)⟩

def carrierRootedInput (d : Coproduct n h₀ h r m b) :
    RootedComponentInput n h₀ h r := by
  let C := baseOrientedCarrier (fromCoproduct d)
  let fO : Fintype (baseOrdinaryCells C) := Fintype.ofFinite _
  refine
    { cellSet := C.baseCells
      ordinarySet := baseOrdinaryCells C
      ordinaryFintype := fO
      size := C.baseOrdinaryCount
      card_eq := ?_
      base_mem := C.base_mem
      ordinary_iff := fun _ ↦ Iff.rfl
      pairing := C.core.1.1.restrict C.baseCells }
  rw [← Nat.card_eq_fintype_card]
  exact card_baseOrdinaryCells C

def literalRootedInput (d : Coproduct n h₀ h r m b) :
    RootedComponentInput n h₀ h r := by
  let O : Set (Fin n) := {i | i ∈ (cells d).1}
  let fO : Fintype O := inferInstance
  refine
    { cellSet := baseCellSet d
      ordinarySet := O
      ordinaryFintype := fO
      size := d.1.1
      card_eq := ?_
      base_mem := by simp [baseCell, baseCellSet]
      ordinary_iff := fun _ ↦ Iff.rfl
      pairing := (baseRestrictedPairing d).pairing }
  rw [← Nat.card_eq_fintype_card]
  change Nat.card {i : Fin n // i ∈ (cells d).1} = d.1.1
  rw [Nat.card_eq_fintype_card]
  simpa using (cells d).2

set_option maxHeartbeats 1000000 in
theorem carrierRootedInput_eq_literal
    (d : Coproduct n h₀ h r m b) :
    carrierRootedInput d = literalRootedInput d := by
  let C := baseOrientedCarrier (fromCoproduct d)
  let O : Set (Fin n) := {i | i ∈ (cells d).1}
  have hcell : C.baseCells = baseCellSet d :=
    baseOrientedCarrier_from_baseCells d
  have hordinary : baseOrdinaryCells C = O := by
    ext i
    change (Sum.inr i : RootedCell n) ∈ C.baseCells ↔ i ∈ (cells d).1
    rw [hcell]
    rfl
  let fC : Fintype (baseOrdinaryCells C) := Fintype.ofFinite _
  let fD : Fintype O := inferInstance
  have hf : HEq fC fD := by
    have hfun := congr_arg_heq
      (fun U : Set (Fin n) ↦ Fintype.ofFinite U) hordinary
    exact hfun.trans (heq_of_eq (Subsingleton.elim _ _))
  apply RootedComponentInput.ext hcell hordinary hf
    (baseOrientedCarrier_from_baseOrdinaryCount d)
    (carrierBaseRestriction_fromCoproduct d)

theorem rootedInputDartEquiv_carrier
    (d : Coproduct n h₀ h r m b) :
    rootedInputDartEquiv (carrierRootedInput d) =
      forwardBaseDartEquiv (fromCoproduct d) := by
  apply Equiv.ext
  rintro ⟨⟨u | i, hc⟩, j⟩
  · cases u
    rfl
  · apply Sigma.ext
    · rfl
    · rfl

theorem rootedInputDartEquiv_literal
    (d : Coproduct n h₀ h r m b) :
    rootedInputDartEquiv (literalRootedInput d) = baseDartEquiv d := by
  apply Equiv.ext
  rintro ⟨⟨u | i, hc⟩, j⟩
  · cases u
    rfl
  · apply Sigma.ext
    · rfl
    · rfl

set_option maxHeartbeats 1000000 in
theorem forwardBaseNumericalPairing_pairing_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    HEq (forwardBaseNumericalPairing (fromCoproduct d)).pairing
      (baseComponent d).1.raw.pairing := by
  have hx := congrArg rootedComponentNormalize
    (carrierRootedInput_eq_literal d)
  have hsnd : HEq
      (rootedComponentNormalize (carrierRootedInput d)).2
      (rootedComponentNormalize (literalRootedInput d)).2 :=
    (Sigma.ext_iff.mp hx).2
  have hleft : (rootedComponentNormalize (carrierRootedInput d)).2 =
      (forwardBaseNumericalPairing (fromCoproduct d)).pairing := by
    change ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).baseCells).reindex
        (rootedInputDartEquiv (carrierRootedInput d)) = _
    rw [rootedInputDartEquiv_carrier]
    rfl
  have hright : (rootedComponentNormalize (literalRootedInput d)).2 =
      (baseComponent d).1.raw.pairing := by
    change (baseRestrictedPairing d).pairing.reindex
      (rootedInputDartEquiv (literalRootedInput d)) = _
    rw [rootedInputDartEquiv_literal]
    have hraw := BoundaryLabelledPairing.reindexEquiv_apply_symm_apply
      (r := r) (m := d.2.1.1 + 1) (baseDartEquiv d)
      (baseComponent d).1.raw
    exact congrArg BoundaryLabelledPairing.pairing hraw
  exact (heq_of_eq hleft.symm).trans <|
    hsnd.trans (heq_of_eq hright)

/-! ## The uniform component away from the base -/

structure OtherComponentInput (n h₀ h r : ℕ) where
  cellSet : Set (RootedCell n)
  ordinarySet : Set (Fin n)
  ordinaryFintype : Fintype ordinarySet
  size : ℕ
  card_eq : @Fintype.card ordinarySet ordinaryFintype = size
  base_not_mem : baseCell n ∉ cellSet
  ordinary_iff : ∀ i : Fin n,
    (Sum.inr i : RootedCell n) ∈ cellSet ↔ i ∈ ordinarySet
  pairing : ColoredMatching
    (RestrictedDart (facets := rootedFacets h₀ h) cellSet) r

theorem OtherComponentInput.ext
    {x y : OtherComponentInput n h₀ h r}
    (hcell : x.cellSet = y.cellSet)
    (hordinary : x.ordinarySet = y.ordinarySet)
    (hfintype : HEq x.ordinaryFintype y.ordinaryFintype)
    (hsize : x.size = y.size)
    (hpairing : HEq x.pairing y.pairing) : x = y := by
  cases x with
  | mk X O fO k hk hb hi P =>
    cases y with
    | mk Y U fU l hl hb' hi' Q =>
      dsimp only at hcell hordinary hfintype hsize hpairing
      subst Y
      subst U
      have hf : fO = fU := eq_of_heq hfintype
      subst fU
      subst l
      have hPQ : P = Q := eq_of_heq hpairing
      subst Q
      rfl

def otherInputCellEquiv (x : OtherComponentInput n h₀ h r) :
    x.cellSet ≃ Fin x.size := by
  letI : Fintype x.ordinarySet := x.ordinaryFintype
  let eO : x.ordinarySet ≃ Fin x.size :=
    (Fintype.equivFin _).trans (finCongr x.card_eq)
  refine
    { toFun := fun c ↦ match hc : c.1 with
        | Sum.inl u => False.elim (by
            cases u
            exact x.base_not_mem (by simpa only [hc, baseCell] using c.2))
        | Sum.inr i => eO ⟨i, (x.ordinary_iff i).mp (by
            simpa only [hc] using c.2)⟩
      invFun := fun i ↦ ⟨Sum.inr (eO.symm i).1,
        (x.ordinary_iff _).mpr (eO.symm i).2⟩
      left_inv := by
        rintro ⟨u | i, hc⟩
        · cases u
          exact False.elim (x.base_not_mem hc)
        · apply Subtype.ext
          simp
      right_inv := by intro i; simp }

def otherInputFacetEquiv (x : OtherComponentInput n h₀ h r)
    (c : x.cellSet) : Fin (rootedFacets h₀ h c.1) ≃ Fin h := by
  rcases c with ⟨u | i, hc⟩
  · cases u
    exact False.elim (x.base_not_mem hc)
  · exact Equiv.refl _

def otherInputDartEquiv (x : OtherComponentInput n h₀ h r) :
    RestrictedDart (facets := rootedFacets h₀ h) x.cellSet ≃
      Dart x.size h :=
  Equiv.sigmaCongr (otherInputCellEquiv x) (otherInputFacetEquiv x)

def otherComponentNormalize (x : OtherComponentInput n h₀ h r) :
    Σ k : ℕ, ColoredMatching (Dart k h) r :=
  ⟨x.size, x.pairing.reindex (otherInputDartEquiv x)⟩

def carrierOtherInput (d : Coproduct n h₀ h r m b) :
    OtherComponentInput n h₀ h r := by
  let C := baseOrientedCarrier (fromCoproduct d)
  let fO : Fintype (otherOrdinaryCells C) := Fintype.ofFinite _
  refine
    { cellSet := C.otherCells
      ordinarySet := otherOrdinaryCells C
      ordinaryFintype := fO
      size := n - C.baseOrdinaryCount
      card_eq := ?_
      base_not_mem := C.base_not_mem_other
      ordinary_iff := fun _ ↦ Iff.rfl
      pairing := C.core.1.1.restrict C.otherCells }
  rw [← Nat.card_eq_fintype_card]
  rw [card_otherOrdinaryCells]
  have hadd := C.ordinaryCounts_add
  omega

def literalOtherInput (d : Coproduct n h₀ h r m b) :
    OtherComponentInput n h₀ h r := by
  let O : Set (Fin n) := {i | i ∉ (cells d).1}
  let fO : Fintype O := inferInstance
  refine
    { cellSet := otherCellSet d
      ordinarySet := O
      ordinaryFintype := fO
      size := n - d.1.1
      card_eq := ?_
      base_not_mem := by simp [baseCell, otherCellSet]
      ordinary_iff := fun _ ↦ Iff.rfl
      pairing := (otherRestrictedPairing d).pairing }
  rw [← Nat.card_eq_fintype_card]
  change Nat.card {i : Fin n // i ∉ (cells d).1} = n - d.1.1
  rw [Nat.card_eq_fintype_card]
  have hc := card_complement (cells d).1
  rw [Fintype.card_fin, (cells d).2] at hc
  exact hc

theorem baseOrientedCarrier_from_otherOrdinaryCount
    (d : Coproduct n h₀ h r m b) :
    (baseOrientedCarrier (fromCoproduct d)).otherOrdinaryCount = n - d.1.1 := by
  have hadd := (baseOrientedCarrier (fromCoproduct d)).ordinaryCounts_add
  rw [baseOrientedCarrier_from_baseOrdinaryCount] at hadd
  omega

set_option maxHeartbeats 1000000 in
theorem carrierOtherInput_eq_literal
    (d : Coproduct n h₀ h r m b) :
    carrierOtherInput d = literalOtherInput d := by
  let C := baseOrientedCarrier (fromCoproduct d)
  let O : Set (Fin n) := {i | i ∉ (cells d).1}
  have hcell : C.otherCells = otherCellSet d :=
    baseOrientedCarrier_from_otherCells d
  have hordinary : otherOrdinaryCells C = O := by
    ext i
    change (Sum.inr i : RootedCell n) ∈ C.otherCells ↔ i ∉ (cells d).1
    rw [hcell]
    rfl
  let fC : Fintype (otherOrdinaryCells C) := Fintype.ofFinite _
  let fD : Fintype O := inferInstance
  have hf : HEq fC fD := by
    have hfun := congr_arg_heq
      (fun U : Set (Fin n) ↦ Fintype.ofFinite U) hordinary
    exact hfun.trans (heq_of_eq (Subsingleton.elim _ _))
  apply OtherComponentInput.ext hcell hordinary hf
    (congrArg (fun k ↦ n - k)
      (baseOrientedCarrier_from_baseOrdinaryCount d))
    (carrierOtherRestriction_fromCoproduct d)

theorem otherInputDartEquiv_carrier
    (d : Coproduct n h₀ h r m b) :
    otherInputDartEquiv (carrierOtherInput d) =
      forwardOtherDartEquiv (fromCoproduct d) := by
  apply Equiv.ext
  rintro ⟨⟨u | i, hc⟩, j⟩
  · cases u
    exact False.elim ((baseOrientedCarrier (fromCoproduct d)).base_not_mem_other hc)
  · apply Sigma.ext <;> rfl

theorem otherInputDartEquiv_literal
    (d : Coproduct n h₀ h r m b) :
    otherInputDartEquiv (literalOtherInput d) = otherDartEquiv d := by
  apply Equiv.ext
  rintro ⟨⟨u | i, hc⟩, j⟩
  · cases u
    exact False.elim hc
  · apply Sigma.ext <;> rfl

set_option maxHeartbeats 1000000 in
theorem forwardOtherNumericalPairing_pairing_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    HEq (forwardOtherNumericalPairing (fromCoproduct d)).pairing
      (otherComponent d).1.raw.pairing := by
  have hx := congrArg otherComponentNormalize
    (carrierOtherInput_eq_literal d)
  have hsnd : HEq
      (otherComponentNormalize (carrierOtherInput d)).2
      (otherComponentNormalize (literalOtherInput d)).2 :=
    (Sigma.ext_iff.mp hx).2
  have hleft : (otherComponentNormalize (carrierOtherInput d)).2 =
      (forwardOtherNumericalPairing (fromCoproduct d)).pairing := by
    change ((baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
      (baseOrientedCarrier (fromCoproduct d)).otherCells).reindex
        (otherInputDartEquiv (carrierOtherInput d)) = _
    rw [otherInputDartEquiv_carrier]
    rfl
  have hright : (otherComponentNormalize (literalOtherInput d)).2 =
      (otherComponent d).1.raw.pairing := by
    change (otherRestrictedPairing d).pairing.reindex
      (otherInputDartEquiv (literalOtherInput d)) = _
    rw [otherInputDartEquiv_literal]
    have hraw := BoundaryLabelledPairing.reindexEquiv_apply_symm_apply
      (r := r) (m := m - d.2.1.1 + 1) (otherDartEquiv d)
      (otherComponent d).1.raw
    exact congrArg BoundaryLabelledPairing.pairing hraw
  exact (heq_of_eq hleft.symm).trans <|
    hsnd.trans (heq_of_eq hright)


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

