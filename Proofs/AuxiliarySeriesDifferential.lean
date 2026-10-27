module

public import Proofs.ClosedFormArithmetic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Differential identities for the auxiliary Raney series

Let `A` be the unique formal solution of

`A = 1 + c X A^(q+1)`.

The coefficient extraction in `ScaledRaneyApplication` gives its closed
form.  This file supplies the complementary algebraic identity used in
Appendix B of the manuscript.  No analytic convergence and no radical
formula is involved.
-/

namespace PolytopeCounting
namespace ExplicitFormulas

noncomputable section

open PowerSeries

/-- Differentiating the scaled Raney equation. -/
theorem derivative_scaled_raney_equation
    (A : PowerSeries ℚ) (c : ℚ) (p : ℕ)
    (hA : A = 1 + PowerSeries.C c * PowerSeries.X * A ^ p) :
    PowerSeries.derivative (R := ℚ) A =
      PowerSeries.C c * A ^ p +
        PowerSeries.C c * PowerSeries.X *
          (PowerSeries.C (p : ℚ) * A ^ (p - 1) *
            PowerSeries.derivative (R := ℚ) A) := by
  have hd := congrArg (PowerSeries.derivative (R := ℚ)) hA
  rw [map_add, (PowerSeries.derivative (R := ℚ)).map_one_eq_zero,
    Derivation.leibniz, Derivation.leibniz,
    PowerSeries.derivative_C, PowerSeries.derivative_X,
    (PowerSeries.derivative (R := ℚ)).leibniz_pow] at hd
  simp [smul_eq_mul] at hd
  have hpC : (p : PowerSeries ℚ) = PowerSeries.C (p : ℚ) := by
    norm_num
  rw [hpC] at hd
  ring_nf at hd ⊢
  exact hd

/-- The algebraic differential identity behind the tree recurrence.

Writing `p=q+1`, the identity is

`p X A' - q X A A' = A^2 - A`.

It is obtained by multiplying the differentiated functional equation by
`X A` and replacing `c X A^(q+1)` with `A-1`.
-/
theorem scaled_raney_tree_differential
    (A : PowerSeries ℚ) (c : ℚ) (q : ℕ)
    (hA : A =
      1 + PowerSeries.C c * PowerSeries.X * A ^ (q + 1)) :
    PowerSeries.C ((q + 1 : ℕ) : ℚ) * PowerSeries.X *
          PowerSeries.derivative (R := ℚ) A -
        PowerSeries.C (q : ℚ) * PowerSeries.X * A *
          PowerSeries.derivative (R := ℚ) A =
      A ^ 2 - A := by
  have hderiv := derivative_scaled_raney_equation A c (q + 1) hA
  have hshift :
      PowerSeries.C c * PowerSeries.X * A ^ (q + 1) = A - 1 := by
    calc
      PowerSeries.C c * PowerSeries.X * A ^ (q + 1) =
          (1 + PowerSeries.C c * PowerSeries.X * A ^ (q + 1)) - 1 := by
        ring
      _ = A - 1 := congrArg (fun Z : PowerSeries ℚ => Z - 1) hA.symm
  have hm := congrArg
    (fun Z : PowerSeries ℚ => PowerSeries.X * A * Z) hderiv
  have hpow : A * A ^ q = A ^ (q + 1) := by
    rw [pow_succ']
  rw [Nat.add_sub_cancel] at hm
  have hm' :
      PowerSeries.X * A * PowerSeries.derivative (R := ℚ) A =
        A * (A - 1) +
          PowerSeries.C ((q + 1 : ℕ) : ℚ) * PowerSeries.X *
            (A - 1) * PowerSeries.derivative (R := ℚ) A := by
    calc
      PowerSeries.X * A * PowerSeries.derivative (R := ℚ) A =
          PowerSeries.X * A *
            (PowerSeries.C c * A ^ (q + 1) +
              PowerSeries.C c * PowerSeries.X *
                (PowerSeries.C ((q + 1 : ℕ) : ℚ) * A ^ q *
                  PowerSeries.derivative (R := ℚ) A)) := hm
      _ = A * (PowerSeries.C c * PowerSeries.X * A ^ (q + 1)) +
          PowerSeries.C ((q + 1 : ℕ) : ℚ) * PowerSeries.X *
            (PowerSeries.C c * PowerSeries.X * (A * A ^ q)) *
              PowerSeries.derivative (R := ℚ) A := by ring
      _ = A * (PowerSeries.C c * PowerSeries.X * A ^ (q + 1)) +
          PowerSeries.C ((q + 1 : ℕ) : ℚ) * PowerSeries.X *
            (PowerSeries.C c * PowerSeries.X * A ^ (q + 1)) *
              PowerSeries.derivative (R := ℚ) A := by rw [hpow]
      _ = A * (A - 1) +
          PowerSeries.C ((q + 1 : ℕ) : ℚ) * PowerSeries.X *
            (A - 1) * PowerSeries.derivative (R := ℚ) A := by
        simp only [hshift]
  have hcoeff : PowerSeries.C (((q + 1 : ℕ) : ℚ)) =
      PowerSeries.C (q : ℚ) + 1 := by
    norm_num
  rw [hcoeff] at hm'
  calc
    PowerSeries.C ((q + 1 : ℕ) : ℚ) * PowerSeries.X *
          PowerSeries.derivative (R := ℚ) A -
        PowerSeries.C (q : ℚ) * PowerSeries.X * A *
          PowerSeries.derivative (R := ℚ) A =
        A * (PowerSeries.C c * PowerSeries.X * A ^ (q + 1)) := by
      rw [hcoeff]
      rw [hshift]
      linear_combination hm'
    _ = A * (A - 1) := by rw [hshift]
    _ = A ^ 2 - A := by ring

/-- The same identity in the manuscript's variables `q=h-2` and
`q+1=h-1`. -/
theorem manuscript_auxiliary_differential
    (A : PowerSeries ℚ) (c : ℚ) (h : ℕ) (hh : 2 ≤ h)
    (hA : A =
      1 + PowerSeries.C c * PowerSeries.X * A ^ (h - 1)) :
    PowerSeries.C ((h - 1 : ℕ) : ℚ) * PowerSeries.X *
          PowerSeries.derivative (R := ℚ) A -
        PowerSeries.C ((h - 2 : ℕ) : ℚ) * PowerSeries.X * A *
          PowerSeries.derivative (R := ℚ) A =
      A ^ 2 - A := by
  have hp : h - 1 = (h - 2) + 1 := by omega
  rw [hp] at hA ⊢
  exact scaled_raney_tree_differential A c (h - 2) hA


end
end ExplicitFormulas
end PolytopeCounting
