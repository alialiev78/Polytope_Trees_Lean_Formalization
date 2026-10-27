module

public import Proofs.ConcreteExponentialFormula
public import Proofs.DisconnectedGeneratingPDE
public import Proofs.FormalExpLogLinearization

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Boundary and cell derivations on the actual counting-series ring

The coefficient ring is `Q[[t1]]`, the outer variable is `t0`.
The boundary derivation acts coefficientwise.  In particular it is NOT
`PowerSeries.derivative` on the outer series, which differentiates in `t0`.
All sums in the coefficient proofs are finite.
-/

namespace PolytopeCounting.CountingDifferential

noncomputable section
open scoped BigOperators
open BivariateCoefficients

/-- Cell differentiation, with scalars restricted from `Q[[t1]]` to `Q`. -/
def cellD : Derivation ℚ CountingSeries CountingSeries :=
  Derivation.mk'
    { toFun := PowerSeries.derivative
      map_add' := by intro F G; exact map_add PowerSeries.derivative F G
      map_smul' := by
        intro a F
        apply PowerSeries.ext
        intro n
        apply PowerSeries.ext
        intro m
        simp [PowerSeries.coeff_derivative, smul_mul_assoc] }
    (by
      intro F G
      letI : Algebra BoundarySeries CountingSeries := MvPowerSeries.instAlgebra
      exact PowerSeries.derivative.leibniz F G)

@[simp] theorem cellD_apply (F : CountingSeries) :
    cellD F = PowerSeries.derivative F := rfl

/-- Differentiate each outer coefficient in the boundary variable. -/
def boundaryFun (F : CountingSeries) : CountingSeries :=
  PowerSeries.mk (fun n ↦ PowerSeries.derivative (PowerSeries.coeff n F))

@[simp] theorem coeff_boundaryFun (F : CountingSeries) (n : ℕ) :
    PowerSeries.coeff n (boundaryFun F) =
      PowerSeries.derivative (PowerSeries.coeff n F) := by
  simp [boundaryFun]

/-- A genuine rational-linear map, not only a coefficient-level operation. -/
def boundaryLinear : CountingSeries →ₗ[ℚ] CountingSeries where
  toFun := boundaryFun
  map_add' F G := by
    apply PowerSeries.ext
    intro n
    simp [boundaryFun]
  map_smul' a F := by
    apply PowerSeries.ext
    intro n
    simp [boundaryFun]

/-- Leibniz follows from the finite coefficient formula for multiplication. -/
theorem boundaryFun_mul (F G : CountingSeries) :
    boundaryFun (F * G) = F * boundaryFun G + G * boundaryFun F := by
  rw [show F * boundaryFun G + G * boundaryFun F =
      F * boundaryFun G + boundaryFun F * G by ring]
  apply PowerSeries.ext
  intro n
  simp only [coeff_boundaryFun, PowerSeries.coeff_mul, map_sum,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib, map_add]
  congr 1
  all_goals
    apply Finset.sum_congr rfl
    intro ij hij
    ring

/-- Boundary differentiation `d/dt1`. -/
def boundaryD : Derivation ℚ CountingSeries CountingSeries :=
  Derivation.mk' boundaryLinear (by
    intro F G
    change boundaryFun (F * G) = F * boundaryFun G + G * boundaryFun F
    exact boundaryFun_mul F G)

@[simp] theorem boundaryD_apply (F : CountingSeries) :
    boundaryD F = boundaryFun F := rfl

@[simp] theorem coeff_boundaryD (F : CountingSeries) (n : ℕ) :
    PowerSeries.coeff n (boundaryD F) =
      PowerSeries.derivative (PowerSeries.coeff n F) := by
  simp

@[simp] theorem boundaryD_constantCoeff (F : CountingSeries) :
    PowerSeries.constantCoeff (boundaryD F) =
      PowerSeries.derivative (PowerSeries.constantCoeff F) := by
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
    coeff_boundaryD F 0

/-- The two formal partial derivatives commute. -/
theorem cellD_boundaryD (F : CountingSeries) :
    cellD (boundaryD F) = boundaryD (cellD F) := by
  apply PowerSeries.ext
  intro n
  simp only [cellD_apply, PowerSeries.coeff_derivative, coeff_boundaryD,
    Derivation.leibniz, smul_eq_mul, map_add, Derivation.map_natCast,
    Derivation.map_one_eq_zero, mul_zero, add_zero]
  ring

/-- The two independent variables in `Q[[t1]][[t0]]`. -/
def cellVariable : CountingSeries := PowerSeries.X

def boundaryVariable : CountingSeries := PowerSeries.C PowerSeries.X

/-- Rational constants embedded through both coefficient rings. -/
def scalar (q : ℚ) : CountingSeries :=
  PowerSeries.C (PowerSeries.C q)

/-- The manuscript Euler derivation `h t0 d/dt0 - t1 d/dt1`. -/
def eulerD (h : ℕ) : Derivation ℚ CountingSeries CountingSeries :=
  (scalar (h : ℚ) * cellVariable) • cellD - boundaryVariable • boundaryD

@[simp] theorem eulerD_apply (h : ℕ) (F : CountingSeries) :
    eulerD h F = scalar (h : ℚ) * cellVariable * cellD F -
      boundaryVariable * boundaryD F := by
  simp [eulerD, smul_eq_mul]

@[simp] theorem coeff_coeff_boundaryD (F : CountingSeries) (n m : ℕ) :
    PowerSeries.coeff m (PowerSeries.coeff n (boundaryD F)) =
      PowerSeries.coeff (m + 1) (PowerSeries.coeff n F) * ((m : ℚ) + 1) := by
  simp [PowerSeries.coeff_derivative]

/-- Direct coefficient identification of the boundary Euler operator. -/
theorem coeff_boundary_euler (F : CountingSeries) (n m : ℕ) :
    PowerSeries.coeff m
        (PowerSeries.coeff n (boundaryVariable * boundaryD F)) =
      (m : ℚ) * PowerSeries.coeff m (PowerSeries.coeff n F) := by
  simp only [boundaryVariable, PowerSeries.coeff_C_mul, coeff_boundaryD]
  cases m with
  | zero => simp
  | succ m =>
      simp [PowerSeries.coeff_derivative, mul_comm]

/-- Direct coefficient identification of the cell Euler operator. -/
theorem coeff_cell_euler (h : ℕ) (F : CountingSeries) (n m : ℕ) :
    PowerSeries.coeff m
        (PowerSeries.coeff n (scalar (h : ℚ) * cellVariable * cellD F)) =
      ((h * n : ℕ) : ℚ) * PowerSeries.coeff m (PowerSeries.coeff n F) := by
  rw [mul_assoc]
  simp only [scalar, cellVariable, cellD_apply, PowerSeries.coeff_C_mul]
  cases n with
  | zero => simp
  | succ n =>
      simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
        PowerSeries.coeff_C_mul]
      rw [show (n : BoundarySeries) + 1 = PowerSeries.C ((n : ℚ) + 1) by simp,
        PowerSeries.coeff_mul_C]
      push_cast
      ring

/-- Full coefficient formula for the Euler derivation. -/
theorem coeff_eulerD (h : ℕ) (F : CountingSeries) (n m : ℕ) :
    PowerSeries.coeff m (PowerSeries.coeff n (eulerD h F)) =
      (((h * n : ℕ) : ℚ) - (m : ℚ)) *
        PowerSeries.coeff m (PowerSeries.coeff n F) := by
  simp only [eulerD_apply, map_sub, coeff_cell_euler, coeff_boundary_euler]
  ring

/-- The old coefficientwise heat equation is the literal derivation equation. -/
theorem disconnectedPDE_to_derivation
    (h r : ℕ) (F : Series ℚ) (hF : SatisfiesDisconnectedPDE h r F) :
    FormalExpLog.SatisfiesDisconnectedEquation (eulerD h) boundaryD
      (scalar (r : ℚ)) (toPowerSeries F) := by
  unfold FormalExpLog.SatisfiesDisconnectedEquation
  apply PowerSeries.ext
  intro n
  apply PowerSeries.ext
  intro m
  have hp := (satisfiesDisconnectedPDE_iff h r F).mp hF n m
  simp only [coeff_eulerD, coeff_coeff_toPowerSeries, scalar,
    PowerSeries.coeff_C_mul, coeff_boundaryD, PowerSeries.coeff_derivative]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul] at hp ⊢
  linear_combination hp

end
end PolytopeCounting.CountingDifferential
