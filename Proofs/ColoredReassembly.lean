module

public import Proofs.BridgeRestriction

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Colour-preserving restriction/reassembly

This module proves the colour-preserving restriction/reassembly equivalence
using the induced matchings from `BridgeRestriction`.
-/

namespace PolytopeCounting
namespace FacetPairing

noncomputable section

universe uC

variable {Cell : Type uC} [Fintype Cell] [DecidableEq Cell]
  {facets : Cell → ℕ} {r : ℕ}

namespace ColoredMatching

/-- Ambient coloured matchings all of whose seams lie on one of the two
specified sides. -/
def ComponentInternal
    (S T : Set Cell)
    (P : ColoredMatching (CellDart Cell facets) r) : Prop :=
  ∀ e ∈ P.matching.seams, SeamInternal S e ∨ SeamInternal T e

/-- The exact colour-preserving restriction/reassembly equivalence for a
fixed disjoint pair of cell sets. -/
noncomputable def componentRestrictionEquiv
    (S T : Set Cell) (hdisj : Disjoint S T) :
    (ColoredMatching (RestrictedDart (facets := facets) S) r ×
        ColoredMatching (RestrictedDart (facets := facets) T) r) ≃
      {P : ColoredMatching (CellDart Cell facets) r //
        ComponentInternal S T P} where
  toFun X := ⟨reassembleColored S T hdisj X.1 X.2, by
    intro e he
    exact seamInternal_reassembleMatching S T hdisj
      X.1.matching X.2.matching e he⟩
  invFun P := ⟨P.1.restrict S, P.1.restrict T⟩
  left_inv X := by
    apply Prod.ext
    · exact restrict_reassembleColored_left S T hdisj X.1 X.2
    · exact restrict_reassembleColored_right S T hdisj X.1 X.2
  right_inv P := by
    apply Subtype.ext
    exact reassembleColored_restrict P.1 S T hdisj P.2

/-- If every seam is internal to one side of a disjoint partition, then no
dual adjacency crosses from the left side to the right side.  This is the
converse of `seam_internal_left_or_right` (under the covering hypothesis).
It closes the logical gap between the structural predicate used by the
reassembly equivalence and the graph-theoretic `NoCrossing` predicate. -/
theorem noCrossing_of_internal
    (P : ColoredMatching (CellDart Cell facets) r)
    (S T : Set Cell) (hdisj : Disjoint S T)
    (hint : ComponentInternal S T P) :
    NoCrossing P S T := by
  intro u hu v hv hadj
  obtain ⟨i, j, hij⟩ := hadj
  rcases hint s(⟨u, i⟩, ⟨v, j⟩) hij with hS | hT
  · have hvS : v ∈ S := hS ⟨v, j⟩ (by simp)
    exact Set.disjoint_left.mp hdisj hvS hv
  · have huT : u ∈ T := hT ⟨u, i⟩ (by simp)
    exact Set.disjoint_left.mp hdisj hu huT

/-- For a covering pair of cell sets, graph-theoretic noncrossing is exactly
the internal-seam predicate used by colour-preserving reassembly. -/
theorem internal_iff_noCrossing
    (P : ColoredMatching (CellDart Cell facets) r)
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T) :
    ComponentInternal S T P ↔ NoCrossing P S T := by
  constructor
  · exact noCrossing_of_internal P S T hdisj
  · intro hno e he
    exact seam_internal_left_or_right P S T hcover hno e he

/-- Identity-on-objects equivalence between the internal-seam subtype and
the graph-theoretic no-crossing subtype. -/
noncomputable def internalNoCrossingEquiv
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T) :
    {P : ColoredMatching (CellDart Cell facets) r //
        ComponentInternal S T P} ≃
      {P : ColoredMatching (CellDart Cell facets) r // NoCrossing P S T} where
  toFun P := ⟨P.1, (internal_iff_noCrossing P.1 S T hcover hdisj).mp P.2⟩
  invFun P := ⟨P.1, (internal_iff_noCrossing P.1 S T hcover hdisj).mpr P.2⟩
  left_inv P := by rfl
  right_inv P := by rfl

/-- Exact equivalence between pairs of coloured component matchings and
ambient coloured matchings having no crossing seam.  No freeness or orbit
division is used: this is an explicit pair of mutually inverse functions.

The hypotheses say that `S,T` are the two sides of a genuine set partition.
The component dart types remain the literal subtypes `RestrictedDart S` and
`RestrictedDart T`; reindexing them by standard finite types is a separate
normalization layer. -/
noncomputable def reassembleNoCrossingColoredEquiv
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T) :
    (ColoredMatching (RestrictedDart (facets := facets) S) r ×
        ColoredMatching (RestrictedDart (facets := facets) T) r) ≃
      {P : ColoredMatching (CellDart Cell facets) r // NoCrossing P S T} :=
  (componentRestrictionEquiv (facets := facets) (r := r) S T hdisj).trans
    (internalNoCrossingEquiv (facets := facets) (r := r)
      S T hcover hdisj)

@[simp]
theorem reassembleNoCrossingColoredEquiv_apply_val
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r) :
    (reassembleNoCrossingColoredEquiv (facets := facets) (r := r)
      S T hcover hdisj (P, Q)).1 = reassembleColored S T hdisj P Q := rfl

@[simp]
theorem reassembleNoCrossingColoredEquiv_symm_apply
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T)
    (P : {P : ColoredMatching (CellDart Cell facets) r //
      NoCrossing P S T}) :
    (reassembleNoCrossingColoredEquiv (facets := facets) (r := r)
      S T hcover hdisj).symm P = ⟨P.1.restrict S, P.1.restrict T⟩ := rfl


end ColoredMatching

end
end FacetPairing
end PolytopeCounting
