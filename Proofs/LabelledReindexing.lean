module

public import Proofs.ComponentReindexing

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Reindexing boundary-labelled bridge components

`ComponentReindexing` transports the matching and its dependent seam-colour
function from a literal bridge-component subtype to the canonical dart type
`Dart k h`.  This file transports the boundary subtype and its bijective
labels as well.  The construction is an actual equivalence, including when
the boundary is empty (`m = 0`).
-/

namespace PolytopeCounting
namespace FacetPairing

noncomputable section

universe uD uE

namespace PartialMatching

variable {D : Type uD} {E : Type uE}
  [DecidableEq D] [DecidableEq E]

/-- Reindexing darts induces a bijection of the unused (boundary) darts. -/
def boundaryReindexEquiv (e : D ≃ E) (M : PartialMatching D) :
    M.Boundary ≃ (M.reindex e).Boundary where
  toFun x := ⟨e x.1, by
    intro hocc
    rcases ((M.reindex e).mem_occupied_iff (e x.1)).mp hocc with
      ⟨s, hs, hxs⟩
    rcases Finset.mem_map.mp hs with ⟨old, hold, rfl⟩
    rcases Sym2.mem_map.mp hxs with ⟨d, hd, hed⟩
    have hdx : d = x.1 := e.injective hed
    subst d
    exact x.2 ((M.mem_occupied_iff x.1).mpr ⟨old, hold, hd⟩)⟩
  invFun y := ⟨e.symm y.1, by
    intro hocc
    rcases (M.mem_occupied_iff (e.symm y.1)).mp hocc with
      ⟨s, hs, hys⟩
    apply y.2
    apply ((M.reindex e).mem_occupied_iff y.1).mpr
    refine ⟨Sym2.map e s, Finset.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
    exact Sym2.mem_map.mpr
      ⟨e.symm y.1, hys, e.apply_symm_apply y.1⟩⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

@[simp]
theorem boundaryReindexEquiv_apply_val (e : D ≃ E)
    (M : PartialMatching D) (x : M.Boundary) :
    (M.boundaryReindexEquiv e x).1 = e x.1 := rfl

@[simp]
theorem boundaryReindexEquiv_symm_apply_val (e : D ≃ E)
    (M : PartialMatching D) (x : (M.reindex e).Boundary) :
    ((M.boundaryReindexEquiv e).symm x).1 = e.symm x.1 := rfl

end PartialMatching

namespace BoundaryLabelledPairing

variable {D : Type uD} {E : Type uE}
  [DecidableEq D] [DecidableEq E] {r m : ℕ}

/-- Structure-as-dependent-pair equivalence used to avoid hidden transports
in the label field. -/
def dataEquiv : BoundaryLabelledPairing D r m ≃
    (Σ P : ColoredMatching D r, P.Boundary ≃ Fin m) where
  toFun P := ⟨P.pairing, P.label⟩
  invFun P := ⟨P.1, P.2⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

/-- Precomposition with a boundary equivalence transports bijective labels.
This remains a singleton-to-singleton equivalence in the closed case. -/
def labelTransportEquiv {A : Type uD} {B : Type uE}
    (b : A ≃ B) : (A ≃ Fin m) ≃ (B ≃ Fin m) where
  toFun label := b.symm.trans label
  invFun label := b.trans label
  left_inv label := by
    ext x
    simp
  right_inv label := by
    ext x
    simp

/-- Reindexing is an equivalence of boundary-labelled coloured pairings,
not just of their underlying matchings. -/
def reindexEquiv (e : D ≃ E) :
    BoundaryLabelledPairing D r m ≃ BoundaryLabelledPairing E r m :=
  dataEquiv.trans <|
    (Equiv.sigmaCongr (ColoredMatching.reindexEquiv (r := r) e)
      (fun P ↦ labelTransportEquiv
        (P.matching.boundaryReindexEquiv e))).trans dataEquiv.symm

@[simp]
theorem pairing_reindexEquiv (e : D ≃ E)
    (P : BoundaryLabelledPairing D r m) :
    (reindexEquiv (r := r) (m := m) e P).pairing =
      P.pairing.reindex e := rfl

@[simp]
theorem reindexEquiv_symm_apply_apply (e : D ≃ E)
    (P : BoundaryLabelledPairing D r m) :
    (reindexEquiv (r := r) (m := m) e).symm
        (reindexEquiv (r := r) (m := m) e P) = P :=
  (reindexEquiv (r := r) (m := m) e).left_inv P

@[simp]
theorem reindexEquiv_apply_symm_apply (e : D ≃ E)
    (P : BoundaryLabelledPairing E r m) :
    reindexEquiv (r := r) (m := m) e
        ((reindexEquiv (r := r) (m := m) e).symm P) = P :=
  (reindexEquiv (r := r) (m := m) e).right_inv P

end BoundaryLabelledPairing

/-! ## Canonical labels on a `k`-cell bridge component -/

variable {n h k r m : ℕ}

/-- The full coloured, boundary-labelled component is canonically equivalent
to a pairing on `k` standard cells. -/
def componentBoundaryLabelledEquiv
    (S : Set (Fin n)) [Fintype S]
    (hcard : Fintype.card S = k) :
    BoundaryLabelledPairing
        (RestrictedDart (facets := fun _ : Fin n ↦ h) S) r m ≃
      BoundaryLabelledPairing (Dart k h) r m :=
  BoundaryLabelledPairing.reindexEquiv (componentDartEquiv S hcard)

@[simp]
theorem componentBoundaryLabelledEquiv_symm_apply_apply
    (S : Set (Fin n)) [Fintype S]
    (hcard : Fintype.card S = k)
    (P : BoundaryLabelledPairing
      (RestrictedDart (facets := fun _ : Fin n ↦ h) S) r m) :
    (componentBoundaryLabelledEquiv (r := r) (m := m) S hcard).symm
        (componentBoundaryLabelledEquiv (r := r) (m := m) S hcard P) = P :=
  (componentBoundaryLabelledEquiv (r := r) (m := m) S hcard).left_inv P

@[simp]
theorem componentBoundaryLabelledEquiv_apply_symm_apply
    (S : Set (Fin n)) [Fintype S]
    (hcard : Fintype.card S = k)
    (P : BoundaryLabelledPairing (Dart k h) r m) :
    componentBoundaryLabelledEquiv (r := r) (m := m) S hcard
        ((componentBoundaryLabelledEquiv (r := r) (m := m)
          S hcard).symm P) = P :=
  (componentBoundaryLabelledEquiv (r := r) (m := m) S hcard).right_inv P


end
end FacetPairing
end PolytopeCounting
