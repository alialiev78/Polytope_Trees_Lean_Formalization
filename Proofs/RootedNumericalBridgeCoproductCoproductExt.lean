module

public import Proofs.RootedNumericalBridgeCoproductLabelledComponents

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Extensionality for the allocation-enriched rooted coproduct

The target is a three-level dependent sigma followed by a nested product.
This module isolates the transport bookkeeping needed to reassemble equality
from heterogeneous equality of every stored allocation and component.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace RootedNumericalBridgeCoproduct

noncomputable section

theorem coproduct_ext
    {x y : Coproduct n h₀ h r m b}
    (hell : x.1 = y.1)
    (hs : x.2.1 = y.2.1)
    (hp : x.2.2.1 = y.2.2.1)
    (hcells : HEq x.2.2.2.1 y.2.2.2.1)
    (hlabels : HEq x.2.2.2.2.1 y.2.2.2.2.1)
    (hbase : HEq x.2.2.2.2.2.1 y.2.2.2.2.2.1)
    (hother : HEq x.2.2.2.2.2.2.1 y.2.2.2.2.2.2.1)
    (hcolor : HEq x.2.2.2.2.2.2.2 y.2.2.2.2.2.2.2) : x = y := by
  rcases x with ⟨xell, xt⟩
  rcases xt with ⟨xs, xt⟩
  rcases xt with ⟨xp, xt⟩
  rcases xt with ⟨xcells, xt⟩
  rcases xt with ⟨xlabels, xt⟩
  rcases xt with ⟨xbase, xt⟩
  rcases xt with ⟨xother, xcolor⟩
  rcases y with ⟨yell, yt⟩
  rcases yt with ⟨ys, yt⟩
  rcases yt with ⟨yp, yt⟩
  rcases yt with ⟨ycells, yt⟩
  rcases yt with ⟨ylabels, yt⟩
  rcases yt with ⟨ybase, yt⟩
  rcases yt with ⟨yother, ycolor⟩
  dsimp only at hell hs hp hcells hlabels hbase hother hcolor
  subst yell
  subst ys
  subst yp
  have hcells' : xcells = ycells := eq_of_heq hcells
  have hlabels' : xlabels = ylabels := eq_of_heq hlabels
  have hbase' : xbase = ybase := eq_of_heq hbase
  have hother' : xother = yother := eq_of_heq hother
  have hcolor' : xcolor = ycolor := eq_of_heq hcolor
  subst ycells
  subst ylabels
  subst ybase
  subst yother
  subst ycolor
  rfl

theorem toCoproduct_fromCoproduct_of_other
    (hother : ∀ d : Coproduct n h₀ h r m b,
      HEq (forwardOtherNumericalStratum (fromCoproduct d))
        (otherComponent d))
    (d : Coproduct n h₀ h r m b) :
    toCoproduct (fromCoproduct d) = d := by
  apply coproduct_ext
  · exact forwardCellIndex_fromCoproduct d
  · exact forwardBoundaryIndex_fromCoproduct d
  · exact forwardRankIndex_fromCoproduct d
  · exact forwardCellAllocation_fromCoproduct d
  · exact forwardBoundaryAllocation_fromCoproduct d
  · exact forwardBaseNumericalStratum_fromCoproduct d
  · exact hother d
  · exact heq_of_eq (baseOrientedCarrier_from_deletedColor d)

@[simp]
theorem toCoproduct_fromCoproduct
    (d : Coproduct n h₀ h r m b) :
    toCoproduct (fromCoproduct d) = d :=
  toCoproduct_fromCoproduct_of_other
    (fun q ↦ forwardOtherNumericalStratum_fromCoproduct q) d


end
end RootedNumericalBridgeCoproduct
end FacetPairing
end PolytopeCounting

