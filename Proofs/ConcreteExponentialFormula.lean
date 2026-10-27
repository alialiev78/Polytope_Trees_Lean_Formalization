module

public import Proofs.ConcreteCellPointing
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Derivative

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# Actual generating functions: Xi = W Psi and W = exp V

The outer variable counts ordinary cells; the coefficient ring is a formal
power-series ring in the boundary variable. No analytic convergence is
asserted or required. The functions below package the pre-existing finite
counts, rather than defining an unknown count by the desired identity.

The exponential formula is obtained from the actual root-component
bijection with a one-cell core, followed by formal ODE uniqueness.
-/

namespace PolytopeCounting.BivariateCoefficients

noncomputable section
open scoped BigOperators

/-- The inner variable records free boundary facets. -/
abbrev BoundarySeries := PowerSeries ℚ

instance : CharZero BoundarySeries where
  cast_injective n m h := by
    have he : (n : ℚ) = (m : ℚ) := by
      simpa using congrArg (PowerSeries.constantCoeff (R := ℚ)) h
    exact_mod_cast he

/-- `Q[[t1]][[t0]]`; no radius of convergence is assumed. -/
abbrev CountingSeries := PowerSeries BoundarySeries

/-- Package an existing coefficient array as a genuine formal series. -/
def toPowerSeries (F : Series ℚ) : CountingSeries :=
  PowerSeries.mk (fun n ↦ PowerSeries.mk (F n))

@[simp] theorem coeff_toPowerSeries (F : Series ℚ) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeries F) = PowerSeries.mk (F n) := by
  simp [toPowerSeries]

@[simp] theorem coeff_coeff_toPowerSeries (F : Series ℚ) (n m : ℕ) :
    PowerSeries.coeff m (PowerSeries.coeff n (toPowerSeries F)) = F n m := by
  simp [toPowerSeries]

theorem toPowerSeries_injective : Function.Injective toPowerSeries := by
  intro F G h
  funext n m
  simpa using congrArg
    (fun P : CountingSeries ↦ PowerSeries.coeff m (PowerSeries.coeff n P)) h

/-- Finite coefficient convolution agrees with multiplication in the
iterated formal power-series ring. -/
theorem toPowerSeries_convolution (F G : Series ℚ) :
    toPowerSeries (convolution F G) = toPowerSeries F * toPowerSeries G := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_toPowerSeries]
  apply PowerSeries.ext
  intro m
  simp only [map_sum, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, PowerSeries.coeff_mk]
  rfl

/-- Coefficients of differentiation in the cell variable. -/
def cellDerivative (F : Series ℚ) : Series ℚ :=
  fun n m ↦ ((n + 1 : ℕ) : ℚ) * F (n + 1) m

private theorem mk_mul_constant (a : ℚ) (f : ℕ → ℚ) :
    PowerSeries.mk (fun m ↦ a * f m) =
      PowerSeries.mk f * PowerSeries.C a := by
  apply PowerSeries.ext
  intro m
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul_C]
  exact mul_comm _ _

/-- Derivative transport for the actual coefficient embedding. -/
theorem toPowerSeries_cellDerivative (F : Series ℚ) :
    toPowerSeries (cellDerivative F) = PowerSeries.derivative (toPowerSeries F) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_toPowerSeries, PowerSeries.coeff_derivative, coeff_toPowerSeries]
  change PowerSeries.mk (fun m ↦ ((n + 1 : ℕ) : ℚ) * F (n + 1) m) = _
  rw [mk_mul_constant]
  simp

end
end PolytopeCounting.BivariateCoefficients

namespace PolytopeCounting.FormalCounting

noncomputable section
open scoped BigOperators

/-- Uniqueness of a formal linear initial-value problem, proved by
coefficient induction; the coefficient ring need not be a field. -/
theorem linear_ode_unique {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {A F G : PowerSeries R}
    (h0 : PowerSeries.constantCoeff F = PowerSeries.constantCoeff G)
    (hF : PowerSeries.derivative F = A * F)
    (hG : PowerSeries.derivative G = A * G) : F = G := by
  apply PowerSeries.ext
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    cases N with
    | zero =>
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
    | succ n =>
      have hp : PowerSeries.coeff n (A * F) = PowerSeries.coeff n (A * G) := by
        rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
        apply Finset.sum_congr rfl
        intro ij hij
        have hs := Finset.mem_antidiagonal.mp hij
        rw [ih ij.2 (by omega)]
      have hd : PowerSeries.coeff n (PowerSeries.derivative F) =
          PowerSeries.coeff n (PowerSeries.derivative G) := by
        rw [hF, hG]
        exact hp
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at hd
      have hn : (n : R) + 1 ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero n)
      exact mul_right_cancel₀ hn hd

/-- The standard formal exponential composed with a series. All uses
below explicitly prove that its inner series has zero constant term. -/
def formalExp {R : Type*} [CommRing R] [Algebra ℚ R]
    (V : PowerSeries R) : PowerSeries R :=
  PowerSeries.subst V (PowerSeries.exp R)

theorem formalExp_constantCoeff {R : Type*} [CommRing R] [Algebra ℚ R]
    {V : PowerSeries R} (hV : PowerSeries.constantCoeff V = 0) :
    PowerSeries.constantCoeff (formalExp V) = 1 := by
  have hv : MvPowerSeries.constantCoeff V = 0 := hV
  change MvPowerSeries.constantCoeff (formalExp V) = 1
  simpa only [formalExp, PowerSeries.constantCoeff_exp, map_one] using
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero hv (PowerSeries.exp R)

theorem formalExp_derivative {R : Type*} [CommRing R] [Algebra ℚ R]
    {V : PowerSeries R} (hV : PowerSeries.constantCoeff V = 0) :
    PowerSeries.derivative (formalExp V) =
      PowerSeries.derivative V * formalExp V := by
  have hs : PowerSeries.HasSubst V :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hV
  unfold formalExp
  rw [PowerSeries.derivative_subst hs, PowerSeries.derivative_exp]
  exact mul_comm _ _

end
end PolytopeCounting.FormalCounting

namespace PolytopeTrees

noncomputable section

open PolytopeCounting
open PolytopeCounting.BivariateCoefficients
open PolytopeCounting.FormalCounting
open PolytopeCounting.FacetPairing

universe uL

def WSeries (L : Type uL) [Fintype L] (h r : ℕ) : CountingSeries :=
  toPowerSeries (fun n m ↦ W L n h r m)

def VSeries (L : Type uL) [Fintype L] (h r : ℕ) : CountingSeries :=
  toPowerSeries (VHat L h r)

def PsiSeries (L : Type uL) [Fintype L] (h h₀ r : ℕ) : CountingSeries :=
  toPowerSeries (PsiHat L h₀ h r)

def XiSeries (L : Type uL) [Fintype L] (h h₀ r : ℕ) : CountingSeries :=
  toPowerSeries (ConcreteXi.XiHatCount h h₀ r (Fintype.card L) 1)

/-- The literal product, now in a standard formal power-series ring. -/
theorem XiSeries_eq_WSeries_mul_PsiSeries
    (L : Type uL) [Group L] [Fintype L] (h h₀ r : ℕ) :
    XiSeries L h h₀ r = WSeries L h r * PsiSeries L h h₀ r := by
  unfold XiSeries WSeries PsiSeries
  rw [← toPowerSeries_convolution]
  exact congrArg toPowerSeries (Xi_equals_W_mul_Psi L h h₀ r)

@[simp] theorem WSeries_constantCoeff
    (L : Type uL) [Fintype L] (h r : ℕ) :
    PowerSeries.constantCoeff (WSeries L h r) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  apply PowerSeries.ext
  intro m
  simp [WSeries, W_zero_row]

@[simp] theorem VSeries_constantCoeff
    (L : Type uL) [Fintype L] (h r : ℕ) :
    PowerSeries.constantCoeff (VSeries L h r) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  apply PowerSeries.ext
  intro m
  simp [VSeries, VHat]

/-- This differential identity is derived from finite cell pointing;
it is not an assumption about the two generating functions. -/
theorem WSeries_derivative
    (L : Type uL) [Group L] [Fintype L] (h r : ℕ) :
    PowerSeries.derivative (WSeries L h r) =
      PowerSeries.derivative (VSeries L h r) * WSeries L h r := by
  unfold WSeries VSeries
  rw [← toPowerSeries_cellDerivative, ← toPowerSeries_cellDerivative,
    ← toPowerSeries_convolution]
  apply congrArg toPowerSeries
  funext n m
  exact W_cell_derivative_convolution L h r n m

/-- The exponential formula for the original concrete finite enumeration.
There is no `IsFormalExpPair` or coefficient identity among the hypotheses. -/
theorem WSeries_eq_formalExp_VSeries
    (L : Type uL) [Group L] [Fintype L] (h r : ℕ) :
    WSeries L h r = formalExp (VSeries L h r) := by
  apply linear_ode_unique (A := PowerSeries.derivative (VSeries L h r))
  · rw [WSeries_constantCoeff, formalExp_constantCoeff (VSeries_constantCoeff L h r)]
  · exact WSeries_derivative L h r
  · exact formalExp_derivative (VSeries_constantCoeff L h r)

/-- Expanded notation for users who prefer not to use the local abbreviation
`formalExp`. The right-hand side is Mathlib's standard formal exponential. -/
theorem WSeries_eq_exp_subst_VSeries
    (L : Type uL) [Group L] [Fintype L] (h r : ℕ) :
    WSeries L h r = PowerSeries.subst (VSeries L h r)
      (PowerSeries.exp (PowerSeries ℚ)) :=
  WSeries_eq_formalExp_VSeries L h r

end
end PolytopeTrees
