module

public import Proofs.UnrootedBridgeCoproductCounting
public import Proofs.RootedBridgeCoproductCounting
public import Proofs.NumericalRecurrenceAssembly

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# The four recurrences from the two exact bridge equivalences

This is the final compositional API.  Its combinatorial inputs are actual
Lean equivalences:

* an oriented unrooted bridge point is equivalent to the literal unrooted
  allocation coproduct;
* a rooted bridge point is equivalent to the literal rooted allocation
  coproduct.

Taking cardinalities, regrouping allocation fibers, wreath normalization,
non-free action-groupoid mass, and boundary-support elimination are all
internal consequences.  No raw cardinality identity, cut--join certificate,
freeness hypothesis, or mass-preservation field remains in the signatures.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace FinalRecurrencesFromEquivalences

open scoped BigOperators

open PointedDecomposition MassRecurrence AllRankMassRecurrence
open StratumBalanceSpecialization
open NumericalRecurrenceAssembly

noncomputable section

universe uL

variable {L : Type uL}

local instance unrootedStratumFintype (n h r m b : ℕ) :
    Fintype (UnrootedStratum n h r m b) := Fintype.ofFinite _

local instance rootedStratumFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedStratum n h₀ h r m b) := Fintype.ofFinite _

local instance unrootedBridgePointedFintype (n h r m b : ℕ) :
    Fintype (UnrootedBridgePointed n h r m b) := Fintype.ofFinite _

local instance rootedBridgePointedFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedBridgePointed n h₀ h r m b) := Fintype.ofFinite _

/-! ## Exact equivalence types -/

abbrev UnrootedBridgeEquiv (n h r m b : ℕ) :=
  (UnrootedBridgePointed n h r m b × Bool) ≃
    UnrootedBridgeCoproduct.Coproduct n h r m b

abbrev RootedBridgeEquiv (n h₀ h r m b : ℕ) :=
  RootedBridgePointed n h₀ h r m b ≃
    RootedNumericalBridgeCoproduct.Coproduct n h₀ h r m b

/-! ## Raw identities are theorems, not hypotheses -/

theorem unrooted_raw_bridge_cardinality
    (e : UnrootedBridgeEquiv n h r m b) :
    2 * Fintype.card (UnrootedBridgePointed n h r m b) =
      r * unrootedRawBridgeSum n h r m b :=
  UnrootedBridgeCoproductCounting.raw_bridge_cardinality_of_equiv e

theorem rooted_raw_bridge_cardinality
    (e : RootedBridgeEquiv n h₀ h r m b) :
    Fintype.card (RootedBridgePointed n h₀ h r m b) =
      r * rootedRawBridgeSum n h₀ h r m b :=
  RootedBridgeCoproductCounting.raw_bridge_cardinality_of_equiv e

/-! ## Fully expanded all-rank `U` and `Psi` recurrences -/

theorem U_all_rank
    (n h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (e : UnrootedBridgeEquiv n h r m b) :
    ((n + b - 1 : ℕ) : ℚ) * UMass L n h r m b =
      ((r : ℚ) / 2) * unrootedCyclePrevious L n h r m b +
        ((r : ℚ) / 2) * unrootedMassConvolution L n h r m b :=
  unrooted_numerical_all_rank_recurrence
    (L := L) n h r m b tau hcard (unrooted_raw_bridge_cardinality e)

theorem Psi_all_rank
    (n h₀ h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (e : RootedBridgeEquiv n h₀ h r m b) :
    ((n + b : ℕ) : ℚ) * PsiMass L n h₀ h r m b =
      ((r : ℚ) / 2) * rootedCyclePrevious L n h₀ h r m b +
        (r : ℚ) * rootedMassConvolution L n h₀ h r m b :=
  rooted_numerical_all_rank_recurrence
    (L := L) n h₀ h r m b tau hcard (rooted_raw_bridge_cardinality e)

/-! ## Boundary-collapsed manuscript forms -/

/-- The bridge boundary sum is eliminated using the forced lower index
`(h-2)k+1-2p`. -/
theorem U_all_rank_collapsed
    (n h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hcard : Fintype.card L = tau)
    (e : UnrootedBridgeEquiv n h r m b) :
    ((n + b - 1 : ℕ) : ℚ) * UMass L n h r m b =
      ((r : ℚ) / 2) * unrootedCyclePrevious L n h r m b +
        ((r : ℚ) / 2) *
          unrootedCollapsedMassConvolution L n h r m b :=
  unrooted_numerical_collapsed_all_rank_recurrence
    (L := L) n h r m b tau hh hcard (unrooted_raw_bridge_cardinality e)

/-- Rooted collapsed form.  The outer cell sum is over `Fin n`, so the
essential `ell=0` direct-attachment term is present. -/
theorem Psi_all_rank_collapsed
    (n h₀ h r m b tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hcard : Fintype.card L = tau)
    (e : RootedBridgeEquiv n h₀ h r m b) :
    ((n + b : ℕ) : ℚ) * PsiMass L n h₀ h r m b =
      ((r : ℚ) / 2) * rootedCyclePrevious L n h₀ h r m b +
        (r : ℚ) * rootedCollapsedMassConvolution L n h₀ h r m b :=
  rooted_numerical_collapsed_all_rank_recurrence
    (L := L) n h₀ h r m b tau hh hcard (rooted_raw_bridge_cardinality e)

/-! ## Rank-zero `R` and `T` recurrences -/

theorem R_tree
    (n h r tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hcard : Fintype.card L = tau)
    (e : UnrootedBridgeEquiv n h r (treeBoundary h n) 0) :
    ((n - 1 : ℕ) : ℚ) * RMass L n h r =
      ((r : ℚ) / 2) *
        ∑ k : BridgeAllocationCounting.ProperCellSize n,
          treeMassSummand L n h r k :=
  tree_R_recurrence (L := L) n h r tau hh hcard
    (unrooted_raw_bridge_cardinality e)

/-- Fixed-base tree recurrence.  It has coefficient `r`, not `r/2`, and its
sum includes the base-only component (`ell=0`). -/
theorem T_fixed_tree
    (n h₀ h r tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hh : 2 ≤ h) (hbase : 1 ≤ h₀)
    (hcard : Fintype.card L = tau)
    (e : RootedBridgeEquiv n h₀ h r (rootedTreeBoundary h₀ h n) 0) :
    (n : ℚ) * TMass L n h₀ h r =
      (r : ℚ) * ∑ k : Fin n, fixedTreeMassSummand L n h₀ h r k :=
  fixed_tree_T_recurrence (L := L) n h₀ h r tau hh hbase hcard
    (rooted_raw_bridge_cardinality e)


end
end FinalRecurrencesFromEquivalences
end FacetPairing
end PolytopeCounting
