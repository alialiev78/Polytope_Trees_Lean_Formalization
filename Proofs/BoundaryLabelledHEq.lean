module

public import Proofs.FacetPairingModel

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Heterogeneous extensionality for boundary-labelled pairings

Bridge-component restriction changes the literal dart subtype and can also
select a propositionally different `DecidableEq` instance.  This small lemma
packages the otherwise repetitive dependent elimination needed to combine
an underlying coloured-matching `HEq` with an `HEq` of its boundary label.
-/

namespace PolytopeCounting
namespace FacetPairing

universe u

theorem BoundaryLabelledPairing.heq_ext
    {D E : Type u} [decD : DecidableEq D] [decE : DecidableEq E]
    {r m : ℕ}
    {P : BoundaryLabelledPairing D r m}
    {Q : BoundaryLabelledPairing E r m}
    (hDE : D = E)
    (hpair : HEq P.pairing Q.pairing)
    (hlabel : HEq P.label Q.label) : HEq P Q := by
  cases hDE
  have hdec : decD = decE := Subsingleton.elim _ _
  cases hdec
  cases P with
  | mk PP PL =>
    cases Q with
    | mk QP QL =>
      dsimp only at hpair hlabel
      have hp : PP = QP := eq_of_heq hpair
      subst QP
      have hl : PL = QL := eq_of_heq hlabel
      subst QL
      rfl

/-- Variant in which the number of boundary labels is itself only
propositionally equal. -/
theorem BoundaryLabelledPairing.heq_ext'
    {D E : Type u} [decD : DecidableEq D] [decE : DecidableEq E]
    {r m q : ℕ}
    {P : BoundaryLabelledPairing D r m}
    {Q : BoundaryLabelledPairing E r q}
    (hDE : D = E) (hmq : m = q)
    (hpair : HEq P.pairing Q.pairing)
    (hlabel : HEq P.label Q.label) : HEq P Q := by
  cases hmq
  exact BoundaryLabelledPairing.heq_ext hDE hpair hlabel


end FacetPairing
end PolytopeCounting
