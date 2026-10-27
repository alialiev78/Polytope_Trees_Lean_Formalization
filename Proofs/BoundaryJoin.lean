module

public import Proofs.OrientedSeam

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# The exact boundary after joining two distinguished free facets

This is the inverse boundary operation to `BoundaryCut`.  We first prove a
literal membership characterization, then package it as an equivalence.  A
boundary split `Boundary ≃ Fin m ⊕ Bool` designates the two facets to be
joined by the two `Bool` values; after the join, precisely the `Fin m` part
remains free.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace PartialMatching

universe uD

variable {D : Type uD} [DecidableEq D]

/-- A dart is free after a join iff it was free before and is neither of the
two joined darts. -/
theorem boundary_join_iff (M : PartialMatching D) (x y : M.Boundary)
    (hxy : x.1 ≠ y.1) (d : D) :
    d ∉ (M.join x y hxy).occupied ↔
      d ∉ M.occupied ∧ d ≠ x.1 ∧ d ≠ y.1 := by
  constructor
  · intro hfree
    refine ⟨?_, ?_, ?_⟩
    · intro hocc
      obtain ⟨e, he, hde⟩ := (M.mem_occupied_iff d).mp hocc
      apply hfree
      exact ((M.join x y hxy).mem_occupied_iff d).mpr
        ⟨e, Finset.mem_insert_of_mem he, hde⟩
    · intro hdx
      apply hfree
      exact ((M.join x y hxy).mem_occupied_iff d).mpr
        ⟨M.joinPair x y, Finset.mem_insert_self .., by
          simpa [PartialMatching.joinPair, hdx] using
            (Sym2.mem_mk_left x.1 y.1)⟩
    · intro hdy
      apply hfree
      exact ((M.join x y hxy).mem_occupied_iff d).mpr
        ⟨M.joinPair x y, Finset.mem_insert_self .., by
          simpa [PartialMatching.joinPair, hdy] using
            (Sym2.mem_mk_right x.1 y.1)⟩
  · rintro ⟨hfree, hdx, hdy⟩ hocc
    obtain ⟨e, he, hde⟩ := ((M.join x y hxy).mem_occupied_iff d).mp hocc
    rcases Finset.mem_insert.mp he with hnew | hold
    · subst e
      have : d = x.1 ∨ d = y.1 := by
        simpa [PartialMatching.joinPair] using (Sym2.mem_iff.mp hde)
      exact this.elim hdx hdy
    · exact hfree ((M.mem_occupied_iff d).mpr ⟨e, hold, hde⟩)

/-- The boundary point selected by the right summand of a split. -/
noncomputable def splitEndpoint (M : PartialMatching D)
    (split : M.Boundary ≃ Fin m ⊕ Bool) (b : Bool) : M.Boundary :=
  split.symm (Sum.inr b)

theorem splitEndpoint_ne (M : PartialMatching D)
    (split : M.Boundary ≃ Fin m ⊕ Bool) :
    (M.splitEndpoint split false).1 ≠ (M.splitEndpoint split true).1 := by
  intro h
  have hs : M.splitEndpoint split false = M.splitEndpoint split true :=
    Subtype.ext h
  have := congrArg split hs
  simp [splitEndpoint] at this

/-- Joining the two `Bool`-designated boundary darts leaves a boundary
canonically equivalent to the `Fin m` summand. -/
noncomputable def boundaryJoinEquiv (M : PartialMatching D)
    (split : M.Boundary ≃ Fin m ⊕ Bool) :
    (M.join (M.splitEndpoint split false) (M.splitEndpoint split true)
      (M.splitEndpoint_ne split)).Boundary ≃ Fin m := by
  let x := M.splitEndpoint split false
  let y := M.splitEndpoint split true
  let hxy := M.splitEndpoint_ne split
  let oldBoundaryEquiv :
      (M.join x y hxy).Boundary ≃
        {z : M.Boundary // (split z).isLeft} := by
    let carrier : (M.join x y hxy).Boundary → M.Boundary :=
      fun z ↦ ⟨z.1, ((M.boundary_join_iff x y hxy z.1).mp z.2).1⟩
    refine Equiv.ofBijective
      (fun z ↦ ⟨carrier z, ?_⟩) ⟨?_, ?_⟩
    · have hz := ((M.boundary_join_iff x y hxy z.1).mp z.2)
      cases hs : split (carrier z) with
      | inl i => simp
      | inr b =>
          exfalso
          cases b with
          | false =>
              apply hz.2.1
              have heq : carrier z = x := by
                apply split.injective
                simpa [x, splitEndpoint] using hs
              exact congrArg Subtype.val heq
          | true =>
              apply hz.2.2
              have heq : carrier z = y := by
                apply split.injective
                simpa [y, splitEndpoint] using hs
              exact congrArg Subtype.val heq
    · intro z w heq
      apply Subtype.ext
      exact congrArg (fun a ↦ a.1.1) heq
    · rintro ⟨z, hzleft⟩
      refine ⟨⟨z.1, (M.boundary_join_iff x y hxy z.1).mpr
        ⟨z.2, ?_, ?_⟩⟩, ?_⟩
      · intro hzx
        have heq : z = x := Subtype.ext hzx
        subst z
        simp [x, splitEndpoint] at hzleft
      · intro hzy
        have heq : z = y := Subtype.ext hzy
        subst z
        simp [y, splitEndpoint] at hzleft
      · apply Subtype.ext
        rfl
  exact oldBoundaryEquiv.trans <|
    (split.subtypeEquiv fun z ↦ Iff.rfl).trans Equiv.sumIsLeft


end PartialMatching
end FacetPairing
end PolytopeCounting
