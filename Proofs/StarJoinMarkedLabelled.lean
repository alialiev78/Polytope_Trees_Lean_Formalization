module

public import Proofs.NonbridgeExact
public import Proofs.NonbridgeEquiv

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

namespace PolytopeCounting
namespace FacetPairing
namespace LabelledCutJoin

noncomputable section

universe u
variable {D : Type u} [DecidableEq D]

/-- The full marked boundary-labelled object canonically obtained by joining
the two star-labelled boundary darts. -/
def starJoinMarkedLabelled
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r) :
    MarkedBoundaryLabelledPairing D r m :=
  ⟨⟨(joinStarsMarked (Q, c)).1,
      _root_.PolytopeCounting.FacetPairing.NonbridgeEquiv.joinedBoundaryLabel Q c⟩,
    (joinStarsMarked (Q, c)).2⟩

/-- The same star join, expressed in the exact rejoined-free-pair carrier. -/
def starJoinCore
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r) :
    RejoinedBoundaryLabelledFreePair D r m :=
  ⟨boundaryLabelledToFreePair (Q, c),
    _root_.PolytopeCounting.FacetPairing.NonbridgeEquiv.joinedBoundaryLabel Q c⟩

/-- The direct star construction is definitionally the inverse labelled join
of its exact carrier. -/
theorem starJoinMarkedLabelled_eq_joinLabelled
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r) :
    starJoinMarkedLabelled Q c = joinLabelled (starJoinCore Q c) := by
  rfl

/-- Consequently cutting the newly joined marked object recovers its entire
free-pair carrier, including the old boundary label. -/
theorem cutLabelled_starJoinMarkedLabelled
    (Q : BoundaryLabelledPairing D r (m + 2)) (c : Fin r) :
    cutLabelled (starJoinMarkedLabelled Q c) = starJoinCore Q c := by
  rw [starJoinMarkedLabelled_eq_joinLabelled]
  exact cutLabelled_joinLabelled (starJoinCore Q c)


end
end LabelledCutJoin
end FacetPairing
end PolytopeCounting
