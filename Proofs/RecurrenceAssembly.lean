module

public import Proofs.AllRankMassRecurrence
public import Proofs.BridgeConvolutionNormalization

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-! # Assembly of the all-rank recurrence

This module combines the bridge-pointed count with factorial and local-group
normalization. The concrete coproduct cardinalities used by the public
recurrences are proved in the bridge-counting modules.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace RecurrenceAssembly

open scoped BigOperators

open PointedDecomposition MassRecurrence
open AllRankMassRecurrence BridgeConvolutionNormalization

noncomputable section

universe uI uL

variable {I : Type uI} {L : Type uL}

local instance unrootedStratumFintype (n h r m b : ℕ) :
    Fintype (UnrootedStratum n h r m b) := Fintype.ofFinite _

local instance unrootedBridgePointedFintype (n h r m b : ℕ) :
    Fintype (UnrootedBridgePointed n h r m b) := Fintype.ofFinite _

local instance rootedStratumFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedStratum n h₀ h r m b) := Fintype.ofFinite _

local instance rootedBridgePointedFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedBridgePointed n h₀ h r m b) := Fintype.ofFinite _

/-! ## Expanded recurrences over a finite index type -/

/-- Final unrooted mass recurrence conditional only on the raw cardinality
identity for the bridge coproduct.

The raw factor `2` records the orientation of the deleted bridge.  After
normalization, both the nonbridge cycle term and the bridge convolution
therefore carry the coefficient `r / 2`. -/
theorem unrooted_mass_recurrence_of_bridge_cardinality
    [Fintype I]
    (n h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (k s A B : I → ℕ)
    (hk : ∀ i, k i ≤ n)
    (hcard : Fintype.card L = tau)
    (hbridge :
      2 * Fintype.card (UnrootedBridgePointed n h r m b) =
        r * ∑ i : I,
          Nat.choose n (k i) * Nat.choose m (s i) * A i * B i) :
    ((n + b - 1 : ℕ) : ℚ) * UMass L n h r m b =
      ((r : ℚ) / 2) * unrootedCyclePrevious L n h r m b +
        ((r : ℚ) / 2) *
          ∑ i : I, normalizedSummand n m tau k s A B i := by
  classical
  have htau : 0 < tau := by
    rw [← hcard]
    exact Fintype.card_pos_iff.mpr ⟨(1 : L)⟩
  have hk' : ∀ i ∈ (Finset.univ : Finset I), k i ≤ n := by
    intro i _
    exact hk i
  have hnormalized :=
    unrooted_bridge_convolution_of_cardinality
      (Finset.univ : Finset I) n m tau r
      (Fintype.card (UnrootedBridgePointed n h r m b))
      k s A B hk' htau hbridge
  calc
    ((n + b - 1 : ℕ) : ℚ) * UMass L n h r m b =
        ((r : ℚ) / 2) * unrootedCyclePrevious L n h r m b +
          bridgeRemainder n h r m b tau :=
      unrooted_all_rank_mass_recurrence
        (L := L) n h r m b tau hcard
    _ = ((r : ℚ) / 2) * unrootedCyclePrevious L n h r m b +
          ((r : ℚ) / 2) *
            ∑ i : I, normalizedSummand n m tau k s A B i := by
      simpa only [bridgeRemainder] using
        congrArg
          (fun z : ℚ ↦
            ((r : ℚ) / 2) *
                unrootedCyclePrevious L n h r m b + z)
          hnormalized

/-- Final rooted mass recurrence conditional only on the raw cardinality
identity for the rooted bridge coproduct.

The nonbridge cut still has two endpoint orientations and contributes
`r / 2`.  The component containing the root is intrinsic, so the bridge
convolution has coefficient `r`, with no extra factor two. -/
theorem rooted_mass_recurrence_of_bridge_cardinality
    [Fintype I]
    (n h₀ h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (k s A B : I → ℕ)
    (hk : ∀ i, k i ≤ n)
    (hcard : Fintype.card L = tau)
    (hbridge :
      Fintype.card (RootedBridgePointed n h₀ h r m b) =
        r * ∑ i : I,
          Nat.choose n (k i) * Nat.choose m (s i) * A i * B i) :
    ((n + b : ℕ) : ℚ) * PsiMass L n h₀ h r m b =
      ((r : ℚ) / 2) * rootedCyclePrevious L n h₀ h r m b +
        (r : ℚ) *
          ∑ i : I, normalizedSummand n m tau k s A B i := by
  classical
  have htau : 0 < tau := by
    rw [← hcard]
    exact Fintype.card_pos_iff.mpr ⟨(1 : L)⟩
  have hk' : ∀ i ∈ (Finset.univ : Finset I), k i ≤ n := by
    intro i _
    exact hk i
  have hnormalized :=
    rooted_bridge_convolution_of_cardinality
      (Finset.univ : Finset I) n m tau r
      (Fintype.card (RootedBridgePointed n h₀ h r m b))
      k s A B hk' htau hbridge
  calc
    ((n + b : ℕ) : ℚ) * PsiMass L n h₀ h r m b =
        ((r : ℚ) / 2) * rootedCyclePrevious L n h₀ h r m b +
          rootedBridgeRemainder n h₀ h r m b tau :=
      rooted_all_rank_mass_recurrence
        (L := L) n h₀ h r m b tau hcard
    _ = ((r : ℚ) / 2) * rootedCyclePrevious L n h₀ h r m b +
          (r : ℚ) *
            ∑ i : I, normalizedSummand n m tau k s A B i := by
      simpa only [rootedBridgeRemainder] using
        congrArg
          (fun z : ℚ ↦
            ((r : ℚ) / 2) * rootedCyclePrevious L n h₀ h r m b + z)
          hnormalized


end
end RecurrenceAssembly
end FacetPairing
end PolytopeCounting
