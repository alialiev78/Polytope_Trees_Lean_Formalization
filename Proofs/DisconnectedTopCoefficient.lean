module

public import Proofs.DisconnectedMassRecurrence
public import Proofs.FiniteCounting
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# The no-gluing coefficient of the disconnected series

When all `D` darts are boundary darts, the partial matching has no seams.
There is one coloured empty matching and `|D|!` bijective boundary
labellings.  This proves the top value

`\widehat W_{n,hn} = 1/(n! tau^n)`

for the actual action-groupoid mass, and removes the final hypothesis from
the closed-form identification.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace DisconnectedTop

noncomputable section

universe uD uL

variable {D : Type uD} [Fintype D] [DecidableEq D]
variable {L : Type uL}

/-- The empty partial matching. -/
def emptyPartialMatching (D : Type uD) [DecidableEq D] : PartialMatching D where
  seams := ∅
  offDiagonal e he := by simp at he
  unique_incidence d e he hde f hf hdf := by simp at he

@[simp]
theorem emptyPartialMatching_seams :
    (emptyPartialMatching D).seams = ∅ := rfl

/-- The unique coloured matching with no seams. -/
def emptyColoredMatching (D : Type uD) [DecidableEq D] (r : ℕ) :
    ColoredMatching D r where
  matching := emptyPartialMatching D
  color e := by
    have he : e.1 ∈ (∅ : Finset (Sym2 D)) := e.2
    exact (Finset.notMem_empty e.1 he).elim

@[simp]
theorem emptyColoredMatching_edgeCount (r : ℕ) :
    (emptyColoredMatching D r).edgeCount = 0 := by
  simp [emptyColoredMatching, ColoredMatching.edgeCount,
    emptyPartialMatching]

@[simp]
theorem emptyColoredMatching_boundary_card (r : ℕ) :
    Fintype.card (emptyColoredMatching D r).Boundary = Fintype.card D := by
  simp [emptyColoredMatching, emptyPartialMatching,
    PartialMatching.occupied]

/-- A coloured matching whose whole dart set is free is the empty matching. -/
theorem eq_emptyColoredMatching_of_boundary_card
    (Q : ColoredMatching D r)
    (hboundary : Fintype.card Q.Boundary = Fintype.card D) :
    Q = emptyColoredMatching D r := by
  have hbalance := Q.matching.card_boundary_add_twice_seams
  have hzero : Q.matching.seams.card = 0 := by
    rw [hboundary] at hbalance
    omega
  have hseams : Q.matching.seams = ∅ := Finset.card_eq_zero.mp hzero
  have hmatching : Q.matching = emptyPartialMatching D := by
    apply PartialMatching.ext
    simpa [emptyPartialMatching] using hseams
  apply ColoredMatching.ext hmatching
  intro e
  have he : e.1 ∈ (∅ : Finset (Sym2 D)) := by
    simpa only [hseams] using e.2
  exact (Finset.notMem_empty e.1 he).elim

/-- Boundary-labelled pairings are definitionally a sigma type of a coloured
matching and a boundary equivalence. -/
def boundaryLabelledDataEquiv (r m : ℕ) :
    BoundaryLabelledPairing D r m ≃
      Σ Q : ColoredMatching D r, Q.Boundary ≃ Fin m where
  toFun P := ⟨P.pairing, P.label⟩
  invFun z := ⟨z.1, z.2⟩
  left_inv P := by cases P; rfl
  right_inv z := by cases z; rfl

/-- Exact top-stratum cardinality: one empty coloured matching and `|D|!`
boundary labellings. -/
theorem card_top_boundaryLabelledPairing (r : ℕ) :
    Fintype.card
        (BoundaryLabelledPairing D r (Fintype.card D)) =
      (Fintype.card D).factorial := by
  classical
  rw [Fintype.card_congr (boundaryLabelledDataEquiv (D := D)
    r (Fintype.card D))]
  rw [Fintype.card_sigma]
  rw [Finset.sum_eq_single (emptyColoredMatching D r)]
  · exact FiniteCounting.card_boundaryLabellings
      (emptyColoredMatching D r).Boundary
      (emptyColoredMatching_boundary_card (D := D) r)
  · intro Q hQ hne
    letI : IsEmpty (Q.Boundary ≃ Fin (Fintype.card D)) := ⟨fun e => by
        apply hne
        apply eq_emptyColoredMatching_of_boundary_card Q
        simpa using Fintype.card_congr e
      ⟩
    exact Fintype.card_eq_zero
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- Top raw cardinality for `n` cells with `h` darts each. -/
theorem card_unrootedPairing_top (n h r : ℕ) :
    Fintype.card (UnrootedPairing n h r (n * h)) =
      (n * h).factorial := by
  simpa only [card_dart] using
    (card_top_boundaryLabelledPairing (D := Dart n h) r)

/-- The concrete normalized groupoid mass has the top value used in formula
(46). -/
theorem WHatMass_top
    (n h r tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (htau : 0 < tau) :
    DisconnectedMass.WHatMass L n h r (n * h) =
      1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n) := by
  have hfac : ((n * h).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n * h)
  have htauQ : (tau : ℚ) ≠ 0 := by exact_mod_cast htau.ne'
  unfold DisconnectedMass.WHatMass
  rw [DisconnectedMass.WLabelledMass_eq_card_div_of_card
      (L := L) n h r (n * h) tau hcard,
    card_unrootedPairing_top]
  field_simp [hfac, htauQ]
  norm_num only [Nat.cast_mul, Nat.cast_pow]

/-- Full identification of the concrete disconnected groupoid mass with
formula (46), without an extra top-value hypothesis. -/
theorem WHatMass_closed_form
    (n h r tau : ℕ)
    [Group L] [Fintype L] [MulAction L (Fin h)]
    (hcard : Fintype.card L = tau)
    (htau : 0 < tau) :
    ∀ m ell, n * h = m + 2 * ell →
      DisconnectedMass.WHatMass L n h r m =
        ExplicitFormulas.WHatClosedForm h r tau n m := by
  have hTop :
      DisconnectedMass.WHatMass L n h r (h * n) =
        1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n) := by
    simpa [Nat.mul_comm] using
      (WHatMass_top (L := L) n h r tau hcard htau)
  have hclosed := DisconnectedMass.WHatMass_eq_closedForm_of_top
    (L := L) n h r tau hcard htau hTop
  intro m ell hs
  apply hclosed m ell
  simpa [Nat.mul_comm] using hs


end
end DisconnectedTop
end FacetPairing
end PolytopeCounting
