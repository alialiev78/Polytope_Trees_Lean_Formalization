module

public import Mathlib.Tactic

@[expose] public section
noncomputable section

/-! # Counting isomorphism classes after forgetting old-vertex names -/

namespace PolytopeCounting.RelabellingCardinality

variable {W V O : Type*} [Fintype W] [Fintype V] [Fintype O]

/-- A concrete isomorphism witness is a permutation of the vertex set. -/
structure Isomorphisms (W V : Type*) where
  IsoAt : W → W → Equiv.Perm V → Prop
  identity : ∀ w, IsoAt w w (Equiv.refl V)
  inverse : ∀ {w u e}, IsoAt w u e → IsoAt u w e.symm
  compose : ∀ {w u z e f}, IsoAt w u e → IsoAt u z f → IsoAt w z (e.trans f)

def isoSetoid (I : Isomorphisms W V) : Setoid W where
  r w u := ∃ e, I.IsoAt w u e
  iseqv := ⟨fun w => ⟨Equiv.refl V, I.identity w⟩,
    by rintro w u ⟨e, he⟩; exact ⟨e.symm, I.inverse he⟩,
    by rintro w u z ⟨e, he⟩ ⟨f, hf⟩; exact ⟨e.trans f, I.compose he hf⟩⟩

abbrev Classes (I : Isomorphisms W V) := Quotient (isoSetoid I)

instance classesFinite (I : Isomorphisms W V) : Fintype (Classes I) := Fintype.ofFinite _

def representative (I : Isomorphisms W V) (q : Classes I) : W :=
  Classical.choose (Quotient.exists_rep q)

omit [Fintype W] [Fintype V] in
theorem representative_spec (I : Isomorphisms W V) (q : Classes I) :
    Quotient.mk (isoSetoid I) (representative I q) = q :=
  Classical.choose_spec (Quotient.exists_rep q)

def toRepresentative (I : Isomorphisms W V) (w : W) : Equiv.Perm V :=
  Classical.choose (show ∃ e, I.IsoAt w
      (representative I (Quotient.mk (isoSetoid I) w)) e from
    Quotient.exact (representative_spec I (Quotient.mk (isoSetoid I) w)).symm)

omit [Fintype W] [Fintype V] in
theorem toRepresentative_spec (I : Isomorphisms W V) (w : W) :
    I.IsoAt w (representative I (Quotient.mk (isoSetoid I) w)) (toRepresentative I w) :=
  Classical.choose_spec (show ∃ e, I.IsoAt w
      (representative I (Quotient.mk (isoSetoid I) w)) e from
    Quotient.exact (representative_spec I (Quotient.mk (isoSetoid I) w)).symm)

def marked (I : Isomorphisms W V) (old : O → V) (w : W) : Classes I × (O → V) :=
  (Quotient.mk (isoSetoid I) w, fun i => toRepresentative I w (old i))

omit [Fintype W] [Fintype V] [Fintype O] in
/-- Rigidity here is explicitly about isomorphisms fixing the original
vertices, not about histories or an already-assumed joint injection. -/
theorem marked_injective (I : Isomorphisms W V) (old : O → V)
    (rigid : ∀ w u e, I.IsoAt w u e → (∀ i, e (old i) = old i) → w = u) :
    Function.Injective (marked I old) := by
  intro w u h
  have hc := congrArg Prod.fst h
  have hm := congrArg Prod.snd h
  have hr : representative I (Quotient.mk (isoSetoid I) w) =
      representative I (Quotient.mk (isoSetoid I) u) := congrArg (representative I) hc
  have hw := toRepresentative_spec I w
  rw [hr] at hw
  have hu := I.inverse (toRepresentative_spec I u)
  apply rigid w u ((toRepresentative I w).trans (toRepresentative I u).symm)
    (I.compose hw hu)
  intro i
  change (toRepresentative I u).symm (toRepresentative I w (old i)) = old i
  have hi : toRepresentative I w (old i) = toRepresentative I u (old i) := congrFun hm i
  rw [hi, Equiv.symm_apply_apply]

theorem classes_bound (I : Isomorphisms W V) (old : O → V)
    (rigid : ∀ w u e, I.IsoAt w u e → (∀ i, e (old i) = old i) → w = u) :
    Fintype.card W ≤ Fintype.card (Classes I) * Fintype.card V ^ Fintype.card O := by
  classical
  have h := Fintype.card_le_of_injective (marked I old) (marked_injective I old rigid)
  simpa using h

end PolytopeCounting.RelabellingCardinality
