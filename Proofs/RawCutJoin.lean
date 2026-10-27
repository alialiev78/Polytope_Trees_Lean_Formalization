module

public import Proofs.OrientedBoundaryCut

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# A literal cut--join bijection for partial matchings

This file proves the elementary set-theoretic core of every recurrence.  An
oriented marked seam is a matching, a seam, and one chosen endpoint.  Cutting
it produces a matching with two *ordered* free endpoints.  Conversely, two
ordered distinct free endpoints can be joined.  The constructions are proved
mutually inverse as an actual `Equiv`; no cardinality argument, quotient, or
freeness assumption is used.
-/

namespace PolytopeCounting
namespace FacetPairing

universe uD

variable (D : Type uD) [DecidableEq D]

/-- A partial matching with an oriented marked seam, written with flat fields
so equality does not hide transports between dependent subtype proofs. -/
structure OrientedMarkedMatching where
  matching : PartialMatching D
  seam : Sym2 D
  seam_mem : seam ∈ matching.seams
  first : D
  first_mem : first ∈ seam

/-- A partial matching with two ordered distinct boundary darts. -/
structure OrderedJoinDatum where
  matching : PartialMatching D
  first : D
  second : D
  first_free : first ∉ matching.occupied
  second_free : second ∉ matching.occupied
  distinct : first ≠ second

namespace OrientedMarkedMatching

variable {D}

@[ext]
theorem ext {P Q : OrientedMarkedMatching D}
    (hm : P.matching = Q.matching) (he : P.seam = Q.seam)
    (hf : P.first = Q.first) : P = Q := by
  cases P
  cases Q
  simp_all

/-- The underlying dependent oriented seam. -/
def orientedSeam (P : OrientedMarkedMatching D) :
    P.matching.OrientedSeam :=
  ⟨⟨P.seam, P.seam_mem⟩, ⟨P.first, P.first_mem⟩⟩

end OrientedMarkedMatching

namespace OrderedJoinDatum

variable {D}

@[ext]
theorem ext {P Q : OrderedJoinDatum D}
    (hm : P.matching = Q.matching)
    (hf : P.first = Q.first) (hs : P.second = Q.second) : P = Q := by
  cases P
  cases Q
  simp_all

/-- First boundary dart as the literal boundary subtype. -/
def firstBoundary (P : OrderedJoinDatum D) : P.matching.Boundary :=
  ⟨P.first, P.first_free⟩

/-- Second boundary dart as the literal boundary subtype. -/
def secondBoundary (P : OrderedJoinDatum D) : P.matching.Boundary :=
  ⟨P.second, P.second_free⟩

end OrderedJoinDatum

open OrientedMarkedMatching OrderedJoinDatum

variable {D}

/-- Cut an oriented marked seam, exposing its chosen endpoint first and its
other endpoint second. -/
def cutOriented (P : OrientedMarkedMatching D) : OrderedJoinDatum D := by
  let e : P.matching.Seam := ⟨P.seam, P.seam_mem⟩
  let other := Sym2.Mem.other' P.first_mem
  exact
    { matching := P.matching.erase e
      first := P.first
      second := other
      first_free := (P.matching.endpointBoundaryAfterErase e P.first
        P.first_mem).2
      second_free := (P.matching.endpointBoundaryAfterErase e other
        (Sym2.other_mem' P.first_mem)).2
      distinct := by
        intro h
        apply P.matching.offDiagonal P.seam P.seam_mem
        rw [← Sym2.other_spec' P.first_mem, Sym2.mk_isDiag_iff]
        exact h }

/-- Join the two ordered free endpoints and orient the new seam from the
first endpoint to the second. -/
def joinOrdered (Q : OrderedJoinDatum D) : OrientedMarkedMatching D :=
  { matching := Q.matching.join Q.firstBoundary Q.secondBoundary Q.distinct
    seam := Q.matching.joinPair Q.firstBoundary Q.secondBoundary
    seam_mem := Finset.mem_insert_self ..
    first := Q.first
    first_mem := by simp [PartialMatching.joinPair, firstBoundary,
      secondBoundary] }

private theorem other'_eq_second (Q : OrderedJoinDatum D) :
    Sym2.Mem.other'
        (show Q.first ∈ Q.matching.joinPair Q.firstBoundary Q.secondBoundary by
          simp [PartialMatching.joinPair, OrderedJoinDatum.firstBoundary,
            OrderedJoinDatum.secondBoundary]) = Q.second := by
  let hmem : Q.first ∈
      Q.matching.joinPair Q.firstBoundary Q.secondBoundary := by
    simp [PartialMatching.joinPair, OrderedJoinDatum.firstBoundary,
      OrderedJoinDatum.secondBoundary]
  have hotherMem : Sym2.Mem.other' hmem ∈
      Q.matching.joinPair Q.firstBoundary Q.secondBoundary :=
    Sym2.other_mem' hmem
  have hor : Sym2.Mem.other' hmem = Q.first ∨
      Sym2.Mem.other' hmem = Q.second := by
    simpa [PartialMatching.joinPair, OrderedJoinDatum.firstBoundary,
      OrderedJoinDatum.secondBoundary] using (Sym2.mem_iff.mp hotherMem)
  exact hor.resolve_left (by
    intro heq
    apply Q.distinct
    have hdiag : (Q.matching.joinPair Q.firstBoundary Q.secondBoundary).IsDiag := by
      rw [← Sym2.other_spec' hmem, Sym2.mk_isDiag_iff]
      exact heq.symm
    simpa [PartialMatching.joinPair, OrderedJoinDatum.firstBoundary,
      OrderedJoinDatum.secondBoundary, Sym2.mk_isDiag_iff] using hdiag)

/-- Joining immediately after cutting recovers the marked and oriented
matching exactly. -/
theorem joinOrdered_cutOriented (P : OrientedMarkedMatching D) :
    joinOrdered (cutOriented P) = P := by
  apply OrientedMarkedMatching.ext
  · apply PartialMatching.ext
    simp [joinOrdered, cutOriented, OrderedJoinDatum.firstBoundary,
      OrderedJoinDatum.secondBoundary, PartialMatching.join,
      PartialMatching.erase, PartialMatching.joinPair,
      Sym2.other_spec' P.first_mem, P.seam_mem]
  · simp [joinOrdered, cutOriented, PartialMatching.joinPair,
      OrderedJoinDatum.firstBoundary, OrderedJoinDatum.secondBoundary,
      Sym2.other_spec' P.first_mem]
  · rfl

/-- Cutting immediately after joining recovers the matching and both ordered
endpoints exactly. -/
theorem cutOriented_joinOrdered (Q : OrderedJoinDatum D) :
    cutOriented (joinOrdered Q) = Q := by
  apply OrderedJoinDatum.ext
  · exact Q.matching.erase_join_newSeam Q.firstBoundary Q.secondBoundary
      Q.distinct
  · rfl
  · exact other'_eq_second Q

/-- The raw oriented cut--join bijection. -/
def orientedCutJoinEquiv :
    OrientedMarkedMatching D ≃ OrderedJoinDatum D where
  toFun := cutOriented
  invFun := joinOrdered
  left_inv := joinOrdered_cutOriented
  right_inv := cutOriented_joinOrdered


end FacetPairing
end PolytopeCounting
