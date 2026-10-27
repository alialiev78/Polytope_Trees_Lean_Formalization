module

public import Mathlib.Logic.Equiv.Defs

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Heterogeneous extensionality for equivalences

When both the domain and codomain of a boundary label have been transported,
ordinary `Equiv.ext` is inconvenient to apply.  This lemma eliminates the two
type equalities first and accepts a pointwise heterogeneous equality.
-/

universe u v

theorem Equiv.heq_ext_of_forall
    {A B : Type u} {C D : Type v}
    (hAB : A = B) (hCD : C = D)
    (f : A ≃ C) (g : B ≃ D)
    (hfg : ∀ x : A, HEq (f x) (g (cast hAB x))) :
    HEq f g := by
  cases hAB
  cases hCD
  rw [heq_iff_eq]
  ext x
  exact eq_of_heq (hfg x)

