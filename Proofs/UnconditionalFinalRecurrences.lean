module

public import Proofs.FinalRecurrencesFromEquivalences
public import Proofs.UnrootedBridgeCoproductEquiv
public import Proofs.RootedNumericalBridgeCoproductEquivalence

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Unconditional expanded facet-pairing recurrences

The exact global bridge equivalences are constructed internally, and the wreath parameter is specialized to the actual
cardinality of the local symmetry group.  Consequently the theorem
signatures contain neither bridge-cardinality certificates, equivalence
arguments, normalization constants, nor freeness hypotheses.

The two constants referenced below are the inverse cut--join constructions:

* `UnrootedBridgeCoproduct.bridgeEquiv`;
* `RootedNumericalBridgeCoproduct.bridgeEquiv`.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace UnconditionalFinalRecurrences

open scoped BigOperators

open PointedDecomposition MassRecurrence AllRankMassRecurrence
open StratumBalanceSpecialization NumericalRecurrenceAssembly

noncomputable section

universe uL

variable {L : Type uL}

/-! ## Realized global bridge equivalences -/

def unrootedBridgeEquiv (n h r m b : ℕ) :
    FinalRecurrencesFromEquivalences.UnrootedBridgeEquiv n h r m b :=
  UnrootedBridgeCoproduct.bridgeEquiv n h r m b

def rootedBridgeEquiv (n h₀ h r m b : ℕ) :
    FinalRecurrencesFromEquivalences.RootedBridgeEquiv n h₀ h r m b :=
  RootedNumericalBridgeCoproduct.bridgeEquiv n h₀ h r m b

/-! ## Fully expanded all-rank recurrences -/

theorem U_all_rank
    (n h r m b : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)] :
    ((n + b - 1 : ℕ) : ℚ) * UMass L n h r m b =
      ((r : ℚ) / 2) * unrootedCyclePrevious L n h r m b +
        ((r : ℚ) / 2) * unrootedMassConvolution L n h r m b :=
  FinalRecurrencesFromEquivalences.U_all_rank
    (L := L) n h r m b (Fintype.card L) rfl
      (unrootedBridgeEquiv n h r m b)

theorem Psi_all_rank
    (n h₀ h r m b : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)] :
    ((n + b : ℕ) : ℚ) * PsiMass L n h₀ h r m b =
      ((r : ℚ) / 2) * rootedCyclePrevious L n h₀ h r m b +
        (r : ℚ) * rootedMassConvolution L n h₀ h r m b :=
  FinalRecurrencesFromEquivalences.Psi_all_rank
    (L := L) n h₀ h r m b (Fintype.card L) rfl
      (rootedBridgeEquiv n h₀ h r m b)

/-! ## Boundary-collapsed manuscript forms -/

theorem U_all_rank_collapsed
    (n h r m b : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) :
    ((n + b - 1 : ℕ) : ℚ) * UMass L n h r m b =
      ((r : ℚ) / 2) * unrootedCyclePrevious L n h r m b +
        ((r : ℚ) / 2) *
          unrootedCollapsedMassConvolution L n h r m b :=
  FinalRecurrencesFromEquivalences.U_all_rank_collapsed
    (L := L) n h r m b (Fintype.card L) hh rfl
      (unrootedBridgeEquiv n h r m b)

theorem Psi_all_rank_collapsed
    (n h₀ h r m b : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) :
    ((n + b : ℕ) : ℚ) * PsiMass L n h₀ h r m b =
      ((r : ℚ) / 2) * rootedCyclePrevious L n h₀ h r m b +
        (r : ℚ) * rootedCollapsedMassConvolution L n h₀ h r m b :=
  FinalRecurrencesFromEquivalences.Psi_all_rank_collapsed
    (L := L) n h₀ h r m b (Fintype.card L) hh rfl
      (rootedBridgeEquiv n h₀ h r m b)

/-! ## Rank-zero tree recurrences -/

theorem R_tree
    (n h r : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) :
    ((n - 1 : ℕ) : ℚ) * RMass L n h r =
      ((r : ℚ) / 2) *
        ∑ k : BridgeAllocationCounting.ProperCellSize n,
          treeMassSummand L n h r k :=
  FinalRecurrencesFromEquivalences.R_tree
    (L := L) n h r (Fintype.card L) hh rfl
      (unrootedBridgeEquiv n h r (treeBoundary h n) 0)

theorem T_fixed_tree
    (n h₀ h r : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hbase : 1 ≤ h₀) :
    (n : ℚ) * TMass L n h₀ h r =
      (r : ℚ) * ∑ k : Fin n, fixedTreeMassSummand L n h₀ h r k :=
  FinalRecurrencesFromEquivalences.T_fixed_tree
    (L := L) n h₀ h r (Fintype.card L) hh hbase rfl
      (rootedBridgeEquiv n h₀ h r (rootedTreeBoundary h₀ h n) 0)


end
end UnconditionalFinalRecurrences
end FacetPairing
end PolytopeCounting
