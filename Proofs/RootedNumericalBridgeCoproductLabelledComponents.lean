module

public import Proofs.RootedNumericalBridgeCoproductOtherLabels

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Labelled rooted-component normalization

This packages a restricted coloured matching together with its boundary count
and local boundary label before applying the canonical component reindexing.
Equality of packages therefore transports all finite choices and labels at
once, and yields exact recovery of the numerical rooted component.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

open RootedGlobalBridgeCut NumericalBridgeCut

structure RootedLabelInput (n h₀ h r : ℕ) where
  component : RootedComponentInput n h₀ h r
  boundaryCount : ℕ
  label : component.pairing.Boundary ≃ Fin boundaryCount

theorem RootedLabelInput.ext
    {x y : RootedLabelInput n h₀ h r}
    (hcomponent : x.component = y.component)
    (hboundary : x.boundaryCount = y.boundaryCount)
    (hlabel : HEq x.label y.label) : x = y := by
  cases x with
  | mk xc xm xl =>
    cases y with
    | mk yc ym yl =>
      dsimp only at hcomponent hboundary hlabel
      subst yc
      subst ym
      have hxy : xl = yl := eq_of_heq hlabel
      subst yl
      rfl

def rootedLabelNormalize (x : RootedLabelInput n h₀ h r) :
    Σ k : ℕ, Σ q : ℕ,
      BoundaryLabelledPairing (RootedDart k h₀ h) r q :=
  ⟨x.component.size, x.boundaryCount,
    BoundaryLabelledPairing.reindexEquiv
      (rootedInputDartEquiv x.component)
      ⟨x.component.pairing, x.label⟩⟩

def carrierRootedLabelInput (d : Coproduct n h₀ h r m b) :
    RootedLabelInput n h₀ h r :=
  { component := carrierRootedInput d
    boundaryCount := (forwardBoundaryIndex (fromCoproduct d)).1 + 1
    label := forwardBaseLocalLabel d }

def literalRootedLabelInput (d : Coproduct n h₀ h r m b) :
    RootedLabelInput n h₀ h r :=
  { component := literalRootedInput d
    boundaryCount := d.2.1.1 + 1
    label := (baseRestrictedPairing d).label }

theorem carrierRootedLabelInput_eq_literal
    (d : Coproduct n h₀ h r m b) :
    carrierRootedLabelInput d = literalRootedLabelInput d := by
  apply RootedLabelInput.ext
  · exact carrierRootedInput_eq_literal d
  · exact congrArg (fun s ↦ s + 1)
      (congrArg Fin.val (forwardBoundaryIndex_fromCoproduct d))
  · exact forwardBaseLocalLabel_fromCoproduct d

theorem rootedLabelNormalize_carrier
    (d : Coproduct n h₀ h r m b) :
    (rootedLabelNormalize (carrierRootedLabelInput d)).2.2 =
      forwardBaseNumericalPairing (fromCoproduct d) := by
  change BoundaryLabelledPairing.reindexEquiv
      (rootedInputDartEquiv (carrierRootedInput d))
      ⟨(baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
          (baseOrientedCarrier (fromCoproduct d)).baseCells,
        forwardBaseLocalLabel d⟩ = _
  rw [rootedInputDartEquiv_carrier]
  rfl

theorem rootedLabelNormalize_literal
    (d : Coproduct n h₀ h r m b) :
    (rootedLabelNormalize (literalRootedLabelInput d)).2.2 =
      (baseComponent d).1.raw := by
  change BoundaryLabelledPairing.reindexEquiv
      (rootedInputDartEquiv (literalRootedInput d))
      (baseRestrictedPairing d) = _
  rw [rootedInputDartEquiv_literal]
  exact BoundaryLabelledPairing.reindexEquiv_apply_symm_apply
    (r := r) (m := d.2.1.1 + 1) (baseDartEquiv d)
      (baseComponent d).1.raw

set_option maxHeartbeats 1000000 in
theorem forwardBaseNumericalPairing_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    HEq (forwardBaseNumericalPairing (fromCoproduct d))
      (baseComponent d).1.raw := by
  have hx := congrArg rootedLabelNormalize
    (carrierRootedLabelInput_eq_literal d)
  have hsnd : HEq
      (rootedLabelNormalize (carrierRootedLabelInput d)).2.2
      (rootedLabelNormalize (literalRootedLabelInput d)).2.2 :=
    congr_arg_heq (fun x : Σ k : ℕ, Σ q : ℕ,
      BoundaryLabelledPairing (RootedDart k h₀ h) r q ↦ x.2.2) hx
  exact (heq_of_eq (rootedLabelNormalize_carrier d).symm).trans <|
    hsnd.trans (heq_of_eq (rootedLabelNormalize_literal d))

theorem rootedStratum_heq_of_raw
    {n₁ n₂ m₁ m₂ b₁ b₂ : ℕ}
    (hn : n₁ = n₂) (hm : m₁ = m₂) (hb : b₁ = b₂)
    {P : RootedStratum n₁ h₀ h r m₁ b₁}
    {Q : RootedStratum n₂ h₀ h r m₂ b₂}
    (hraw : HEq P.1.raw Q.1.raw) : HEq P Q := by
  subst n₂
  subst m₂
  subst b₂
  rw [heq_iff_eq]
  apply Subtype.ext
  apply ConnectedDiagram.raw_injective
  exact eq_of_heq hraw

theorem forwardBaseNumericalStratum_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    HEq (forwardBaseNumericalStratum (fromCoproduct d))
      (baseComponent d) := by
  apply rootedStratum_heq_of_raw
  · exact congrArg Fin.val (forwardCellIndex_fromCoproduct d)
  · exact congrArg (fun s ↦ s + 1)
      (congrArg Fin.val (forwardBoundaryIndex_fromCoproduct d))
  · exact congrArg Fin.val (forwardRankIndex_fromCoproduct d)
  · exact forwardBaseNumericalPairing_fromCoproduct d

/-! ## The uniform component away from the distinguished base -/

structure OtherLabelInput (n h₀ h r : ℕ) where
  component : OtherComponentInput n h₀ h r
  boundaryCount : ℕ
  label : component.pairing.Boundary ≃ Fin boundaryCount

theorem OtherLabelInput.ext
    {x y : OtherLabelInput n h₀ h r}
    (hcomponent : x.component = y.component)
    (hboundary : x.boundaryCount = y.boundaryCount)
    (hlabel : HEq x.label y.label) : x = y := by
  cases x with
  | mk xc xm xl =>
    cases y with
    | mk yc ym yl =>
      dsimp only at hcomponent hboundary hlabel
      subst yc
      subst ym
      have hxy : xl = yl := eq_of_heq hlabel
      subst yl
      rfl

def otherLabelNormalize (x : OtherLabelInput n h₀ h r) :
    Σ k : ℕ, Σ q : ℕ,
      BoundaryLabelledPairing (Dart k h) r q :=
  ⟨x.component.size, x.boundaryCount,
    BoundaryLabelledPairing.reindexEquiv
      (otherInputDartEquiv x.component)
      ⟨x.component.pairing, x.label⟩⟩

def carrierOtherLabelInput (d : Coproduct n h₀ h r m b) :
    OtherLabelInput n h₀ h r :=
  { component := carrierOtherInput d
    boundaryCount := m - (forwardBoundaryIndex (fromCoproduct d)).1 + 1
    label := forwardOtherLocalLabel d }

def literalOtherLabelInput (d : Coproduct n h₀ h r m b) :
    OtherLabelInput n h₀ h r :=
  { component := literalOtherInput d
    boundaryCount := m - d.2.1.1 + 1
    label := (otherRestrictedPairing d).label }

theorem carrierOtherLabelInput_eq_literal
    (d : Coproduct n h₀ h r m b) :
    carrierOtherLabelInput d = literalOtherLabelInput d := by
  apply OtherLabelInput.ext
  · exact carrierOtherInput_eq_literal d
  · exact congrArg (fun s ↦ m - s + 1)
      (congrArg Fin.val (forwardBoundaryIndex_fromCoproduct d))
  · exact forwardOtherLocalLabel_fromCoproduct d

theorem otherLabelNormalize_carrier
    (d : Coproduct n h₀ h r m b) :
    (otherLabelNormalize (carrierOtherLabelInput d)).2.2 =
      forwardOtherNumericalPairing (fromCoproduct d) := by
  change BoundaryLabelledPairing.reindexEquiv
      (otherInputDartEquiv (carrierOtherInput d))
      ⟨(baseOrientedCarrier (fromCoproduct d)).core.1.1.restrict
          (baseOrientedCarrier (fromCoproduct d)).otherCells,
        forwardOtherLocalLabel d⟩ = _
  rw [otherInputDartEquiv_carrier]
  rfl

theorem otherLabelNormalize_literal
    (d : Coproduct n h₀ h r m b) :
    (otherLabelNormalize (literalOtherLabelInput d)).2.2 =
      (otherComponent d).1.raw := by
  change BoundaryLabelledPairing.reindexEquiv
      (otherInputDartEquiv (literalOtherInput d))
      (otherRestrictedPairing d) = _
  rw [otherInputDartEquiv_literal]
  exact BoundaryLabelledPairing.reindexEquiv_apply_symm_apply
    (r := r) (m := m - d.2.1.1 + 1) (otherDartEquiv d)
      (otherComponent d).1.raw

set_option maxHeartbeats 1000000 in
theorem forwardOtherNumericalPairing_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    HEq (forwardOtherNumericalPairing (fromCoproduct d))
      (otherComponent d).1.raw := by
  have hx := congrArg otherLabelNormalize
    (carrierOtherLabelInput_eq_literal d)
  have hsnd : HEq
      (otherLabelNormalize (carrierOtherLabelInput d)).2.2
      (otherLabelNormalize (literalOtherLabelInput d)).2.2 :=
    congr_arg_heq (fun x : Σ k : ℕ, Σ q : ℕ,
      BoundaryLabelledPairing (Dart k h) r q ↦ x.2.2) hx
  exact (heq_of_eq (otherLabelNormalize_carrier d).symm).trans <|
    hsnd.trans (heq_of_eq (otherLabelNormalize_literal d))

theorem unrootedStratum_heq_of_raw
    {n₁ n₂ m₁ m₂ b₁ b₂ : ℕ}
    (hn : n₁ = n₂) (hm : m₁ = m₂) (hb : b₁ = b₂)
    {P : UnrootedStratum n₁ h r m₁ b₁}
    {Q : UnrootedStratum n₂ h r m₂ b₂}
    (hraw : HEq P.1.raw Q.1.raw) : HEq P Q := by
  subst n₂
  subst m₂
  subst b₂
  rw [heq_iff_eq]
  apply Subtype.ext
  apply ConnectedDiagram.raw_injective
  exact eq_of_heq hraw

theorem forwardOtherNumericalStratum_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    HEq (forwardOtherNumericalStratum (fromCoproduct d))
      (otherComponent d) := by
  apply unrootedStratum_heq_of_raw
  · exact congrArg (fun ell ↦ n - ell)
      (congrArg Fin.val (forwardCellIndex_fromCoproduct d))
  · exact congrArg (fun s ↦ m - s + 1)
      (congrArg Fin.val (forwardBoundaryIndex_fromCoproduct d))
  · exact congrArg (fun p ↦ b - p)
      (congrArg Fin.val (forwardRankIndex_fromCoproduct d))
  · exact forwardOtherNumericalPairing_fromCoproduct d


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

