module

public import Proofs.ScaledRaneyApplication
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Factorial forms of the Raney coefficients and the manuscript formulas

This file converts the binomial form produced by Lagrange--Bürmann into the
factorial expressions printed in Theorems 3.3, 5.1, and 5.2 of the
manuscript.  Cardano/radical expressions are deliberately not used.
-/

namespace PolytopeCounting
namespace ExplicitFormulas

open PolytopeCounting.LagrangeBurmann
open LagrangeBurmann.RaneyApplication
open LagrangeBurmann.ScaledRaneyApplication

noncomputable section

/-- Factorial form of the rational Raney number. -/
theorem raneyNumber_eq_factorial
    (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    raneyNumber p q n =
      (q : ℚ) * ((p * n + q - 1).factorial : ℚ) /
        ((n.factorial : ℚ) * (((p - 1) * n + q).factorial : ℚ)) := by
  let M : ℕ := p * n + q
  have hMpos : 0 < M := by
    dsimp [M]
    omega
  have hpn : n ≤ p * n := by
    calc
      n = 1 * n := by simp
      _ ≤ p * n := Nat.mul_le_mul_right n hp
  have hnM : n ≤ M := by
    dsimp [M]
    exact le_trans hpn (Nat.le_add_right _ _)
  have hsub : M - n = (p - 1) * n + q := by
    have hp' : p = (p - 1) + 1 := by omega
    dsimp [M]
    nth_rewrite 1 [hp']
    rw [Nat.add_mul]
    simp only [one_mul]
    omega
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hnM
  have hchooseQ :
      (Nat.choose M n : ℚ) * (n.factorial : ℚ) *
          ((M - n).factorial : ℚ) = (M.factorial : ℚ) := by
    exact_mod_cast hchooseNat
  have hfacNat : M * (M - 1).factorial = M.factorial :=
    Nat.mul_factorial_pred hMpos.ne'
  have hfacQ :
      (M : ℚ) * ((M - 1).factorial : ℚ) = (M.factorial : ℚ) := by
    exact_mod_cast hfacNat
  have hcore :
      (Nat.choose M n : ℚ) * (n.factorial : ℚ) *
          ((M - n).factorial : ℚ) =
        (M : ℚ) * ((M - 1).factorial : ℚ) := by
    rw [hchooseQ, hfacQ]
  have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hnfac : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hsubfac : ((M - n).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (M - n)
  unfold raneyNumber
  change
    (q : ℚ) / (M : ℚ) * (Nat.choose M n : ℚ) =
      (q : ℚ) * ((M - 1).factorial : ℚ) /
        ((n.factorial : ℚ) * (((p - 1) * n + q).factorial : ℚ))
  rw [← hsub]
  field_simp [hMQ, hnfac, hsubfac]
  rw [← hcore]

/-- Factorial form in the manuscript's parameters `p=h-1`, `q=h₀`. -/
theorem manuscriptRaneyNumber_eq_factorial
    (h h₀ n : ℕ) (hh : 2 ≤ h) (hbase : 1 ≤ h₀) :
    manuscriptRaneyNumber h h₀ n =
      (h₀ : ℚ) * ((n * (h - 1) + h₀ - 1).factorial : ℚ) /
        ((n.factorial : ℚ) *
          (((h - 2) * n + h₀).factorial : ℚ)) := by
  unfold manuscriptRaneyNumber
  rw [raneyNumber_eq_factorial (h - 1) h₀ n (by omega) hbase]
  have hnum : (h - 1) * n + h₀ - 1 = n * (h - 1) + h₀ - 1 := by
    rw [Nat.mul_comm]
  have hpred : h - 1 - 1 = h - 2 := by omega
  have hden : (h - 1 - 1) * n + h₀ = (h - 2) * n + h₀ := by
    rw [hpred]
  rw [hnum, hden]

/-- The labeled polytope-tree formula of Theorem 5.1. -/
def treeClosedForm (h : ℕ) (r c : ℚ) (n : ℕ) : ℚ :=
  (1 / r) * c ^ n *
    ((n * (h - 1)).factorial : ℚ) / (n.factorial : ℚ)

/-- The labeled fixed-core formula of Theorem 5.2. -/
def fixedCoreClosedForm
    (T₀ : ℚ) (h₀ h : ℕ) (c : ℚ) (n : ℕ) : ℚ :=
  T₀ * c ^ n *
    ((n * (h - 1) + h₀ - 1).factorial : ℚ) /
      (((h₀ - 1).factorial : ℚ) * (n.factorial : ℚ))

/-- Extraction of the tree count from the auxiliary rooted-tree series.
The boundary factorial is exactly `((h-2)n+1)!`. -/
def treeCountFromAux
    (A : PowerSeries ℚ) (h : ℕ) (r : ℚ) (n : ℕ) : ℚ :=
  (((h - 2) * n + 1).factorial : ℚ) / r *
    PowerSeries.coeff n A

/-- Extraction of the fixed-core count from `A^h₀`. -/
def fixedCoreCountFromAux
    (A : PowerSeries ℚ) (T₀ : ℚ) (h₀ h n : ℕ) : ℚ :=
  T₀ / (h₀.factorial : ℚ) *
    (((h - 2) * n + h₀).factorial : ℚ) *
      PowerSeries.coeff n (A ^ h₀)

/-- Lagrange--Bürmann gives the complete labeled tree formula. -/
theorem treeCountFromAux_eq_closedForm
    (A : PowerSeries ℚ) (h n : ℕ) (r c : ℚ)
    (hh : 2 ≤ h) (hr : r ≠ 0) (hc : c ≠ 0)
    (hA : A = 1 + PowerSeries.C c * PowerSeries.X * A ^ (h - 1)) :
    treeCountFromAux A h r n = treeClosedForm h r c n := by
  have hcoeff := coeff_scaled_manuscript_solution
    A c h 1 n hc hA (by omega)
  rw [manuscriptRaneyNumber_eq_factorial h 1 n hh (by omega)] at hcoeff
  simp only [pow_one] at hcoeff
  have hnf : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hbf : ((((h - 2) * n + 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero ((h - 2) * n + 1)
  unfold treeCountFromAux treeClosedForm
  rw [hcoeff]
  have htop : n * (h - 1) + 1 - 1 = n * (h - 1) := by omega
  rw [htop]
  field_simp [hr, hnf, hbf]
  ring

/-- Lagrange--Bürmann gives the complete fixed-core formula. -/
theorem fixedCoreCountFromAux_eq_closedForm
    (A : PowerSeries ℚ) (T₀ c : ℚ) (h₀ h n : ℕ)
    (hh : 2 ≤ h) (hbase : 1 ≤ h₀) (hc : c ≠ 0)
    (hA : A = 1 + PowerSeries.C c * PowerSeries.X * A ^ (h - 1)) :
    fixedCoreCountFromAux A T₀ h₀ h n =
      fixedCoreClosedForm T₀ h₀ h c n := by
  have hcoeff := coeff_scaled_manuscript_solution
    A c h h₀ n hc hA hbase
  rw [manuscriptRaneyNumber_eq_factorial h h₀ n hh hbase] at hcoeff
  have hnfac : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hbf : ((((h - 2) * n + h₀).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero ((h - 2) * n + h₀)
  have hbasefac : (h₀.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero h₀
  have hpredfac : (((h₀ - 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (h₀ - 1)
  have hfacNat : h₀ * (h₀ - 1).factorial = h₀.factorial :=
    Nat.mul_factorial_pred (by omega)
  have hfacQ :
      (h₀ : ℚ) * ((h₀ - 1).factorial : ℚ) =
        (h₀.factorial : ℚ) := by
    exact_mod_cast hfacNat
  unfold fixedCoreCountFromAux fixedCoreClosedForm
  rw [hcoeff]
  field_simp [hnfac, hbf, hbasefac, hpredfac]
  rw [← hfacQ]
  ring

/-- The manuscript parameter `c = hr/τ`. -/
def geometricScale (h r tau : ℕ) : ℚ :=
  ((h * r : ℕ) : ℚ) / (tau : ℚ)

/-- Formula (20), written exactly with the manuscript parameters. -/
def manuscriptTreeClosedForm (h r tau n : ℕ) : ℚ :=
  treeClosedForm h (r : ℚ) (geometricScale h r tau) n

/-- Formula (27), written exactly with the manuscript parameters. -/
def manuscriptFixedCoreClosedForm
    (T₀ : ℚ) (h₀ h r tau n : ℕ) : ℚ :=
  fixedCoreClosedForm T₀ h₀ h (geometricScale h r tau) n

/-- The tetrahedral specialization of formula (20). -/
theorem tetrahedron_closed_form (n : ℕ) :
    manuscriptTreeClosedForm 4 3 12 n =
      ((3 * n).factorial : ℚ) / (3 * (n.factorial : ℚ)) := by
  unfold manuscriptTreeClosedForm treeClosedForm geometricScale
  norm_num
  have hmul : n * 3 = 3 * n := Nat.mul_comm n 3
  rw [hmul]
  ring


end
end ExplicitFormulas
end PolytopeCounting
