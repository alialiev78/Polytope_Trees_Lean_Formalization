module

public import Proofs.ColoredReassembly

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Reindexing finite bridge components

This module transports partial and coloured matchings along explicit dart
equivalences.  It then specializes the construction to a component
`S : Set (Fin n)` of cardinality `k`, identifying its restricted dart type
with the canonical `Dart k h`.
-/

namespace PolytopeCounting
namespace FacetPairing

noncomputable section

universe uD uE

namespace PartialMatching

variable {D : Type uD} {E : Type uE}
  [DecidableEq D] [DecidableEq E]

/-- Transport a partial matching along an equivalence of dart types. -/
def reindex (e : D ≃ E) (M : PartialMatching D) : PartialMatching E :=
  M.map e e.injective

@[simp]
theorem seams_reindex (e : D ≃ E) (M : PartialMatching D) :
    (M.reindex e).seams =
      M.seams.map ⟨Sym2.map e, Sym2.map.injective e.injective⟩ :=
  rfl

/-- Reindexing by an equivalence and then by its inverse is the identity. -/
@[simp]
theorem reindex_symm_reindex (e : D ≃ E) (M : PartialMatching D) :
    (M.reindex e).reindex e.symm = M := by
  apply PartialMatching.ext
  ext s
  simp [reindex, Sym2.map_map]

/-- The reverse inverse law for reindexing partial matchings. -/
@[simp]
theorem reindex_reindex_symm (e : D ≃ E) (M : PartialMatching E) :
    (M.reindex e.symm).reindex e = M := by
  simpa using reindex_symm_reindex e.symm M

/-- Reindexing is an equivalence of the finite types of partial matchings. -/
def reindexEquiv (e : D ≃ E) : PartialMatching D ≃ PartialMatching E where
  toFun := reindex e
  invFun := reindex e.symm
  left_inv := reindex_symm_reindex e
  right_inv := reindex_reindex_symm e

/-- Reindexing darts induces an equivalence between the seam types of a
matching and of its transported matching. -/
def seamReindexEquiv (e : D ≃ E) (M : PartialMatching D) :
    M.Seam ≃ (M.reindex e).Seam where
  toFun s := ⟨Sym2.map e s.1, Finset.mem_map.mpr ⟨s.1, s.2, rfl⟩⟩
  invFun t := ⟨Sym2.map e.symm t.1, by
    obtain ⟨s, hs, hst⟩ := Finset.mem_map.mp t.2
    have hback : Sym2.map e.symm t.1 = s := by
      rw [← hst]
      simp [Sym2.map_map]
    simpa only [hback] using hs⟩
  left_inv s := by
    apply Subtype.ext
    simp [Sym2.map_map]
  right_inv t := by
    apply Subtype.ext
    simp [Sym2.map_map]

end PartialMatching

namespace ColoredMatching

variable {D : Type uD} {E : Type uE}
  [DecidableEq D] [DecidableEq E] {r : ℕ}

/-- Transport a coloured matching along an equivalence of dart types.
The colour of a transported seam is the colour of its unique inverse image. -/
def reindex (e : D ≃ E) (P : ColoredMatching D r) : ColoredMatching E r where
  matching := P.matching.reindex e
  color s := P.color ((P.matching.seamReindexEquiv e).symm s)

@[simp]
theorem matching_reindex (e : D ≃ E) (P : ColoredMatching D r) :
    (P.reindex e).matching = P.matching.reindex e := rfl

@[simp]
theorem color_reindex (e : D ≃ E) (P : ColoredMatching D r)
    (s : (P.reindex e).Seam) :
    (P.reindex e).color s =
      P.color ((P.matching.seamReindexEquiv e).symm s) := rfl

/-- Reindexing a coloured matching and then using the inverse dart
equivalence recovers every seam and every colour. -/
@[simp]
theorem reindex_symm_reindex (e : D ≃ E) (P : ColoredMatching D r) :
    (P.reindex e).reindex e.symm = P := by
  refine ColoredMatching.ext (PartialMatching.reindex_symm_reindex e P.matching) ?_
  intro s
  change P.color _ = P.color _
  apply congrArg P.color
  apply Subtype.ext
  simp [reindex, PartialMatching.seamReindexEquiv,
    PartialMatching.reindex, Sym2.map_map]

/-- The reverse inverse law for coloured matching reindexing. -/
@[simp]
theorem reindex_reindex_symm (e : D ≃ E) (P : ColoredMatching E r) :
    (P.reindex e.symm).reindex e = P := by
  simpa using reindex_symm_reindex e.symm P

/-- Reindexing is an equivalence of coloured matching types. -/
def reindexEquiv (e : D ≃ E) : ColoredMatching D r ≃ ColoredMatching E r where
  toFun := reindex e
  invFun := reindex e.symm
  left_inv := reindex_symm_reindex e
  right_inv := reindex_reindex_symm e

end ColoredMatching

/-! ## Reindexing a finite component by its cardinality -/

variable {n h k r : ℕ}

/-- A component of `Fin n` having `k` cells is explicitly equivalent to
`Fin k`.  The construction is noncomputable because it chooses an ordering
of the cells of the component; no order is used by the matching theory. -/
def componentCellEquiv (S : Set (Fin n)) [Fintype S]
    (hcard : Fintype.card S = k) :
    S ≃ Fin k := by
  exact Fintype.equivFinOfCardEq hcard

/-- Reindexing the cell coordinate and leaving the local facet coordinate
unchanged identifies the restricted dart type with the canonical dart type
on `k` cells. -/
def componentDartEquiv (S : Set (Fin n)) [Fintype S]
    (hcard : Fintype.card S = k) :
    RestrictedDart (facets := fun _ : Fin n ↦ h) S ≃ Dart k h :=
  Equiv.sigmaCongr (componentCellEquiv S hcard) (fun _ ↦ Equiv.refl (Fin h))

@[simp]
theorem componentDartEquiv_cell (S : Set (Fin n)) [Fintype S]
    (hcard : Fintype.card S = k)
    (d : RestrictedDart (facets := fun _ : Fin n ↦ h) S) :
    (componentDartEquiv S hcard d).1 = componentCellEquiv S hcard d.1 :=
  rfl

@[simp]
theorem componentDartEquiv_facet (S : Set (Fin n)) [Fintype S]
    (hcard : Fintype.card S = k)
    (d : RestrictedDart (facets := fun _ : Fin n ↦ h) S) :
    (componentDartEquiv S hcard d).2 = d.2 :=
  rfl

/-- Canonical reindexing equivalence for partial matchings on a component. -/
def componentPartialMatchingEquiv (S : Set (Fin n)) [Fintype S]
    (hcard : Fintype.card S = k) :
    PartialMatching (RestrictedDart (facets := fun _ : Fin n ↦ h) S) ≃
      PartialMatching (Dart k h) :=
  PartialMatching.reindexEquiv (componentDartEquiv S hcard)

/-- Canonical reindexing equivalence for coloured matchings on a component. -/
def componentColoredMatchingEquiv (S : Set (Fin n)) [Fintype S]
    (hcard : Fintype.card S = k) :
    ColoredMatching (RestrictedDart (facets := fun _ : Fin n ↦ h) S) r ≃
      ColoredMatching (Dart k h) r :=
  ColoredMatching.reindexEquiv (componentDartEquiv S hcard)

@[simp]
theorem componentPartialMatchingEquiv_symm_apply_apply
    (S : Set (Fin n)) [Fintype S] (hcard : Fintype.card S = k)
    (M : PartialMatching (RestrictedDart (facets := fun _ : Fin n ↦ h) S)) :
    (componentPartialMatchingEquiv S hcard).symm
        (componentPartialMatchingEquiv S hcard M) = M :=
  (componentPartialMatchingEquiv S hcard).left_inv M

@[simp]
theorem componentPartialMatchingEquiv_apply_symm_apply
    (S : Set (Fin n)) [Fintype S] (hcard : Fintype.card S = k)
    (M : PartialMatching (Dart k h)) :
    componentPartialMatchingEquiv S hcard
        ((componentPartialMatchingEquiv S hcard).symm M) = M :=
  (componentPartialMatchingEquiv S hcard).right_inv M

@[simp]
theorem componentColoredMatchingEquiv_symm_apply_apply
    (S : Set (Fin n)) [Fintype S] (hcard : Fintype.card S = k)
    (P : ColoredMatching
      (RestrictedDart (facets := fun _ : Fin n ↦ h) S) r) :
    (componentColoredMatchingEquiv S hcard).symm
        (componentColoredMatchingEquiv S hcard P) = P :=
  (componentColoredMatchingEquiv S hcard).left_inv P

@[simp]
theorem componentColoredMatchingEquiv_apply_symm_apply
    (S : Set (Fin n)) [Fintype S] (hcard : Fintype.card S = k)
    (P : ColoredMatching (Dart k h) r) :
    componentColoredMatchingEquiv S hcard
        ((componentColoredMatchingEquiv S hcard).symm P) = P :=
  (componentColoredMatchingEquiv S hcard).right_inv P

end

end FacetPairing
end PolytopeCounting
