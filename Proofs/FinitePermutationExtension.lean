module

public import Mathlib.Tactic

@[expose] public section

namespace PolytopeCounting.FinitePermutationExtension

/-- Extend a permutation of the actual N vertices by the identity outside
that finite vertex set. This is not a restriction on allowed graph isomorphisms. -/
def extendedMap {N : ℕ} (e : Equiv.Perm (Fin N)) (x : ℕ) : ℕ :=
  if h : x < N then (e ⟨x, h⟩).val else x

@[simp] theorem extendedMap_of_lt {N : ℕ} (e : Equiv.Perm (Fin N))
    (x : ℕ) (hx : x < N) : extendedMap e x = (e ⟨x, hx⟩).val := by
  simp [extendedMap, hx]

@[simp] theorem extendedMap_of_ge {N : ℕ} (e : Equiv.Perm (Fin N))
    (x : ℕ) (hx : N ≤ x) : extendedMap e x = x := by
  simp [extendedMap, show ¬x < N from Nat.not_lt.mpr hx]

theorem extendedMap_inverse {N : ℕ} (e : Equiv.Perm (Fin N)) (x : ℕ) :
    extendedMap e.symm (extendedMap e x) = x := by
  by_cases hx : x < N
  · have he : (e ⟨x, hx⟩).val < N := (e ⟨x, hx⟩).isLt
    simp only [extendedMap_of_lt e x hx, extendedMap_of_lt e.symm _ he]
    simp
  · have hg : N ≤ x := Nat.le_of_not_gt hx
    simp [extendedMap_of_ge e x hg, extendedMap_of_ge e.symm x hg]

def extend {N : ℕ} (e : Equiv.Perm (Fin N)) : Equiv.Perm ℕ where
  toFun := extendedMap e
  invFun := extendedMap e.symm
  left_inv := extendedMap_inverse e
  right_inv := extendedMap_inverse e.symm

@[simp] theorem extend_apply_lt {N : ℕ} (e : Equiv.Perm (Fin N))
    (x : ℕ) (hx : x < N) : extend e x = (e ⟨x, hx⟩).val := extendedMap_of_lt e x hx

@[simp] theorem extend_apply_ge {N : ℕ} (e : Equiv.Perm (Fin N))
    (x : ℕ) (hx : N ≤ x) : extend e x = x := extendedMap_of_ge e x hx

@[simp] theorem extend_refl (N : ℕ) : extend (Equiv.refl (Fin N)) = Equiv.refl ℕ := by
  ext x
  by_cases hx : x < N <;> simp [extend, extendedMap, hx]

@[simp] theorem extend_symm {N : ℕ} (e : Equiv.Perm (Fin N)) :
    extend e.symm = (extend e).symm := rfl

@[simp] theorem extend_trans {N : ℕ} (e f : Equiv.Perm (Fin N)) :
    extend (e.trans f) = (extend e).trans (extend f) := by
  ext x
  by_cases hx : x < N
  · have he := (e ⟨x, hx⟩).isLt
    simp [Equiv.trans_apply, extend_apply_lt e x hx, extend_apply_lt f _ he,
      extend_apply_lt (e.trans f) x hx]
  · have hg : N ≤ x := Nat.le_of_not_gt hx
    simp [Equiv.trans_apply, extend_apply_ge e x hg, extend_apply_ge f x hg,
      extend_apply_ge (e.trans f) x hg]

end PolytopeCounting.FinitePermutationExtension
