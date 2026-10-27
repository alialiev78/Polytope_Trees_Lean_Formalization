module

public import Proofs.BoundaryJoin

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Boundary cutting with a chosen seam orientation

`BoundaryCut` used the arbitrary representative `Sym2.out`.  For a genuine
cut--join equivalence we instead retain one chosen endpoint of the marked
seam.  The chosen end receives `false`, the other end receives `true`.
This makes the inverse gluing operation canonical and is the literal source
of the later quotient by endpoint exchange.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace PartialMatching

universe uD

variable {D : Type uD} [DecidableEq D]

/-- The endpoint opposite to the distinguished orientation. -/
def otherEndpoint (M : PartialMatching D) (o : M.OrientedSeam) : D :=
  Sym2.Mem.other' o.2.2

theorem otherEndpoint_mem (M : PartialMatching D) (o : M.OrientedSeam) :
    M.otherEndpoint o ∈ o.1.1 :=
  Sym2.other_mem' o.2.2

theorem oriented_endpoints_ne (M : PartialMatching D) (o : M.OrientedSeam) :
    o.2.1 ≠ M.otherEndpoint o := by
  intro heq
  apply M.offDiagonal o.1.1 o.1.2
  rw [← Sym2.other_spec' o.2.2, Sym2.mk_isDiag_iff]
  exact heq

/-- The two endpoints, ordered by the chosen orientation, are `Bool`. -/
def orientedEndpointEquivBool (M : PartialMatching D) (o : M.OrientedSeam) :
    {d : D // d ∈ o.1.1} ≃ Bool where
  toFun d := if d.1 = o.2.1 then false else true
  invFun b := if b then ⟨M.otherEndpoint o, M.otherEndpoint_mem o⟩ else o.2
  left_inv d := by
    apply Subtype.ext
    by_cases hd : d.1 = o.2.1
    · simp [hd]
    · have hrepr : s(o.2.1, M.otherEndpoint o) = o.1.1 :=
        Sym2.other_spec' o.2.2
      have hor : d.1 = o.2.1 ∨ d.1 = M.otherEndpoint o := by
        have : d.1 ∈ s(o.2.1, M.otherEndpoint o) := by
          rw [hrepr]
          exact d.2
        exact Sym2.mem_iff.mp this
      have hother : M.otherEndpoint o ≠ o.2.1 :=
        (M.oriented_endpoints_ne o).symm
      simp [hd, hor.resolve_left hd, hother]
  right_inv b := by
    cases b <;> simp [M.oriented_endpoints_ne o,
      (M.oriented_endpoints_ne o).symm]

/-- Boundary after an oriented cut: old boundary plus two *ordered* exposed
endpoints. -/
noncomputable def orientedBoundaryEraseEquiv
    (M : PartialMatching D) (o : M.OrientedSeam) :
    (M.erase o.1).Boundary ≃ M.Boundary ⊕ Bool := by
  classical
  let p : D → Prop := fun d ↦ d ∉ M.occupied
  let q : D → Prop := fun d ↦ d ∈ o.1.1
  have hset : {d : D | d ∉ (M.erase o.1).occupied} =
      {d : D | p d ∨ q d} := by
    ext d
    exact M.boundary_erase_iff o.1 d
  have hd : Disjoint p q := by
    rw [disjoint_iff_inf_le]
    intro d hboth
    exact hboth.1 ((M.mem_occupied_iff d).mpr
      ⟨o.1.1, o.1.2, hboth.2⟩)
  exact (Set.equivOfEq hset).trans <|
    (subtypeOrEquiv p q hd).trans <|
      (Equiv.refl M.Boundary).sumCongr (M.orientedEndpointEquivBool o)

/-- Extend the old labels by two ordered star labels. -/
noncomputable def orientedCutBoundaryLabel
    (M : PartialMatching D) (o : M.OrientedSeam)
    (label : M.Boundary ≃ Fin m) :
    (M.erase o.1).Boundary ≃ Fin (m + 2) :=
  (M.orientedBoundaryEraseEquiv o).trans <|
    ((label.sumCongr finTwoEquiv.symm).trans finSumEquiv)


end PartialMatching
end FacetPairing
end PolytopeCounting
