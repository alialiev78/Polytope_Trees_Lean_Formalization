module

public import Proofs.RawCutJoin

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# A literal colour-preserving oriented cut--join bijection

This module lifts the raw oriented matching equivalence to
coloured matchings.  Cutting retains the deleted seam colour; joining uses
that colour for the new seam.  Both inverse laws are literal structure
equalities.
-/

namespace PolytopeCounting
namespace FacetPairing

universe uD

variable (D : Type uD) [DecidableEq D] (r : ℕ)

/-- A coloured matching with one oriented marked seam. -/
structure OrientedMarkedColored where
  pairing : ColoredMatching D r
  seam : Sym2 D
  seam_mem : seam ∈ pairing.matching.seams
  first : D
  first_mem : first ∈ seam

/-- A coloured matching with two ordered free endpoints and the colour to
assign when they are rejoined. -/
structure OrderedColoredJoinDatum where
  pairing : ColoredMatching D r
  first : D
  second : D
  first_free : first ∉ pairing.matching.occupied
  second_free : second ∉ pairing.matching.occupied
  distinct : first ≠ second
  newColor : Fin r

namespace OrientedMarkedColored

variable {D r}

@[ext]
theorem ext {P Q : OrientedMarkedColored D r}
    (hp : P.pairing = Q.pairing) (he : P.seam = Q.seam)
    (hf : P.first = Q.first) : P = Q := by
  cases P
  cases Q
  simp_all

def seamSubtype (P : OrientedMarkedColored D r) : P.pairing.Seam :=
  ⟨P.seam, P.seam_mem⟩

end OrientedMarkedColored

namespace OrderedColoredJoinDatum

variable {D r}

@[ext]
theorem ext {P Q : OrderedColoredJoinDatum D r}
    (hp : P.pairing = Q.pairing)
    (hf : P.first = Q.first) (hs : P.second = Q.second)
    (hc : P.newColor = Q.newColor) : P = Q := by
  cases P
  cases Q
  simp_all

def firstBoundary (P : OrderedColoredJoinDatum D r) : P.pairing.Boundary :=
  ⟨P.first, P.first_free⟩

def secondBoundary (P : OrderedColoredJoinDatum D r) : P.pairing.Boundary :=
  ⟨P.second, P.second_free⟩

end OrderedColoredJoinDatum

open OrientedMarkedColored OrderedColoredJoinDatum

variable {D r}

/-- Cut a coloured oriented seam, retaining its colour as part of the join
datum. -/
def cutColored (P : OrientedMarkedColored D r) :
    OrderedColoredJoinDatum D r := by
  let e : P.pairing.Seam := P.seamSubtype
  let other := Sym2.Mem.other' P.first_mem
  exact
    { pairing := P.pairing.erase e
      first := P.first
      second := other
      first_free := (P.pairing.matching.endpointBoundaryAfterErase e
        P.first P.first_mem).2
      second_free := (P.pairing.matching.endpointBoundaryAfterErase e other
        (Sym2.other_mem' P.first_mem)).2
      distinct := by
        intro h
        apply P.pairing.matching.offDiagonal P.seam P.seam_mem
        rw [← Sym2.other_spec' P.first_mem, Sym2.mk_isDiag_iff]
        exact h
      newColor := P.pairing.color e }

/-- Rejoin ordered free endpoints with the retained colour. -/
def joinColored (Q : OrderedColoredJoinDatum D r) :
    OrientedMarkedColored D r :=
  { pairing := Q.pairing.join Q.firstBoundary Q.secondBoundary
      Q.distinct Q.newColor
    seam := Q.pairing.matching.joinPair Q.firstBoundary Q.secondBoundary
    seam_mem := Finset.mem_insert_self ..
    first := Q.first
    first_mem := by simp [PartialMatching.joinPair, firstBoundary,
      secondBoundary] }

private theorem other'_eq_second (Q : OrderedColoredJoinDatum D r) :
    Sym2.Mem.other'
        (show Q.first ∈ Q.pairing.matching.joinPair Q.firstBoundary
            Q.secondBoundary by
          simp [PartialMatching.joinPair, firstBoundary, secondBoundary]) =
      Q.second := by
  let hmem : Q.first ∈ Q.pairing.matching.joinPair Q.firstBoundary
      Q.secondBoundary := by
    simp [PartialMatching.joinPair, firstBoundary, secondBoundary]
  have hm := Sym2.other_mem' hmem
  have hor : Sym2.Mem.other' hmem = Q.first ∨
      Sym2.Mem.other' hmem = Q.second := by
    simpa [PartialMatching.joinPair, firstBoundary, secondBoundary] using
      (Sym2.mem_iff.mp hm)
  exact hor.resolve_left (by
    intro heq
    apply Q.distinct
    have hdiag :
        (Q.pairing.matching.joinPair Q.firstBoundary
          Q.secondBoundary).IsDiag := by
      rw [← Sym2.other_spec' hmem, Sym2.mk_isDiag_iff]
      exact heq.symm
    simpa [PartialMatching.joinPair, firstBoundary, secondBoundary,
      Sym2.mk_isDiag_iff] using hdiag)

/-- Joining immediately after cutting recovers the complete coloured
matching, the marked seam, and its chosen first endpoint. -/
theorem joinColored_cutColored (P : OrientedMarkedColored D r) :
    joinColored (cutColored P) = P := by
  apply OrientedMarkedColored.ext
  · let e : P.pairing.Seam := P.seamSubtype
    let other : D := Sym2.Mem.other' P.first_mem
    have hpair : s(P.first, other) = P.seam :=
      Sym2.other_spec' P.first_mem
    let hm : (joinColored (cutColored P)).pairing.matching =
        P.pairing.matching := by
      apply PartialMatching.ext
      change insert s(P.first, other)
          (P.pairing.matching.seams.erase P.seam) =
        P.pairing.matching.seams
      rw [hpair]
      exact Finset.insert_erase P.seam_mem
    refine ColoredMatching.ext hm ?_
    intro f
    let fP : P.pairing.Seam := ⟨f.1, hm ▸ f.2⟩
    change (joinColored (cutColored P)).pairing.color f =
      P.pairing.color fP
    rcases eq_or_ne f.1 P.seam with hnew | hold
    · have hfP : fP = e := by
        apply Subtype.ext
        exact hnew
      rw [hfP]
      simp [joinColored, cutColored, ColoredMatching.join,
        OrderedColoredJoinDatum.firstBoundary,
        OrderedColoredJoinDatum.secondBoundary, PartialMatching.joinPair,
        hnew]
      rfl
    · simp [joinColored, cutColored, ColoredMatching.join,
        ColoredMatching.erase, OrderedColoredJoinDatum.firstBoundary,
        OrderedColoredJoinDatum.secondBoundary, PartialMatching.joinPair,
        hold, fP]
  · change s(P.first, Sym2.Mem.other' P.first_mem) = P.seam
    exact Sym2.other_spec' P.first_mem
  · rfl

/-- Cutting immediately after joining recovers the coloured matching, both
ordered endpoints, and the retained colour. -/
theorem cutColored_joinColored (Q : OrderedColoredJoinDatum D r) :
    cutColored (joinColored Q) = Q := by
  apply OrderedColoredJoinDatum.ext
  · exact Q.pairing.erase_join_newSeam Q.firstBoundary Q.secondBoundary
      Q.distinct Q.newColor
  · rfl
  · exact other'_eq_second Q
  · exact Q.pairing.color_join_newSeam Q.firstBoundary Q.secondBoundary
      Q.distinct Q.newColor

/-- The exact colour-preserving oriented cut--join equivalence. -/
def coloredOrientedCutJoinEquiv :
    OrientedMarkedColored D r ≃ OrderedColoredJoinDatum D r where
  toFun := cutColored
  invFun := joinColored
  left_inv := joinColored_cutColored
  right_inv := cutColored_joinColored


end FacetPairing
end PolytopeCounting
