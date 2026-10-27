module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Convergent scalar expansions

The relation below connects algebraic power series to analytic functions near
the origin. Products are justified by absolute convergence and the Cauchy
product theorem; equality is equality of convergent Taylor expansions.
-/

@[expose] public section
noncomputable section
open Filter PowerSeries
open scoped Topology

namespace PolytopeCounting.ScalarAnalyticSeries

def HasSeries (f : ℂ → ℂ) (F : PowerSeries ℂ) : Prop :=
  HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n F)) 0

theorem hasSeries_iff (f : ℂ → ℂ) (F : PowerSeries ℂ) :
    HasSeries f F ↔ ∀ᶠ z in 𝓝 0, HasSum (fun n => coeff n F * z ^ n) (f z) := by
  simp [HasSeries, hasFPowerSeriesAt_iff, smul_eq_mul, mul_comm]

theorem HasSeries.unique {f g : ℂ → ℂ} {F G : PowerSeries ℂ}
    (hf : HasSeries f F) (hg : HasSeries g G) (he : f =ᶠ[𝓝 0] g) : F = G := by
  have h := hf.eq_formalMultilinearSeries_of_eventually hg he
  ext n
  exact congrFun ((FormalMultilinearSeries.ofScalars_series_eq_iff ℂ _ _).mp h) n

theorem HasSeries.congr {f g : ℂ → ℂ} {F : PowerSeries ℂ}
    (hf : HasSeries f F) (he : f =ᶠ[𝓝 0] g) : HasSeries g F :=
  HasFPowerSeriesAt.congr hf he

theorem HasSeries.constantCoeff {f : ℂ → ℂ} {F : PowerSeries ℂ}
    (hf : HasSeries f F) : constantCoeff F = f 0 := by
  have h := (hasSeries_iff f F).mp hf
  have hz := Filter.Eventually.self_of_nhds h
  simpa [zero_pow_eq, coeff_zero_eq_constantCoeff] using hz.tsum_eq

theorem exists_series {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ F : PowerSeries ℂ, HasSeries f F := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨PowerSeries.mk p.coeff, (hasSeries_iff _ _).mpr ?_⟩
  filter_upwards [(hasFPowerSeriesAt_iff.mp hp)] with z hz
  simpa [smul_eq_mul, mul_comm] using hz

theorem hasSeries_const (a : ℂ) : HasSeries (fun _ => a) (C a) := by
  apply (hasSeries_iff _ _).mpr
  exact Filter.Eventually.of_forall fun z => by
    simpa +contextual [coeff_C, ite_mul] using (hasSum_ite_eq (0 : ℕ) a)

theorem hasSeries_id : HasSeries (fun z => z) (X : PowerSeries ℂ) := by
  apply (hasSeries_iff _ _).mpr
  exact Filter.Eventually.of_forall fun z => by
    simpa +contextual [coeff_X, ite_mul] using (hasSum_ite_eq (1 : ℕ) z)

theorem HasSeries.add {f g : ℂ → ℂ} {F G : PowerSeries ℂ}
    (hf : HasSeries f F) (hg : HasSeries g G) :
    HasSeries (fun z => f z + g z) (F + G) := by
  apply (hasSeries_iff _ _).mpr
  filter_upwards [(hasSeries_iff _ _).mp hf, (hasSeries_iff _ _).mp hg] with z hz hw
  simpa [add_mul] using hz.add hw

theorem HasSeries.sub {f g : ℂ → ℂ} {F G : PowerSeries ℂ}
    (hf : HasSeries f F) (hg : HasSeries g G) :
    HasSeries (fun z => f z - g z) (F - G) := by
  apply (hasSeries_iff _ _).mpr
  filter_upwards [(hasSeries_iff _ _).mp hf, (hasSeries_iff _ _).mp hg] with z hz hw
  simpa [sub_mul] using hz.sub hw

theorem HasSeries.mul {f g : ℂ → ℂ} {F G : PowerSeries ℂ}
    (hf : HasSeries f F) (hg : HasSeries g G) :
    HasSeries (fun z => f z * g z) (F * G) := by
  apply (hasSeries_iff _ _).mpr
  filter_upwards [(hasSeries_iff _ _).mp hf, (hasSeries_iff _ _).mp hg] with z hz hw
  have hz' := summable_norm_iff.mpr hz.summable
  have hw' := summable_norm_iff.mpr hw.summable
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hz' hw').of_norm
  have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hz' hw'
  rw [hz.tsum_eq, hw.tsum_eq] at he
  rw [he]
  convert hsum.hasSum using 1
  funext n
  rw [coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hn := Finset.mem_antidiagonal.mp hij
  rw [← hn, pow_add]
  ring

theorem HasSeries.pow {f : ℂ → ℂ} {F : PowerSeries ℂ}
    (hf : HasSeries f F) (n : ℕ) : HasSeries (fun z => f z ^ n) (F ^ n) := by
  induction n with
  | zero => simpa using hasSeries_const 1
  | succ n ih => simpa [pow_succ] using ih.mul hf

/-- The branch with zero constant coefficient is unique for every degree
at least two. -/
theorem formal_branch_unique (p : ℕ) (hp : 2 ≤ p) (F G : PowerSeries ℂ)
    (hF0 : constantCoeff F = 0) (hG0 : constantCoeff G = 0)
    (hF : F = X + F ^ p) (hG : G = X + G ^ p) : F = G := by
  let S := ∑ i ∈ Finset.range p, F ^ i * G ^ (p - 1 - i)
  have hS : S * (F - G) = F ^ p - G ^ p := geom_sum₂_mul F G p
  have hS0 : constantCoeff S = 0 := by
    simp only [S, map_sum, map_mul, map_pow, hF0, hG0]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i = 0
    · simp [hi, show p - 1 ≠ 0 by omega]
    · simp [hi]
  have hprod : (1 - S) * (F - G) = 0 := by
    linear_combination hF - hG - hS
  have hn : (1 - S : PowerSeries ℂ) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp [hS0] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hn)

/-- Analytic identification: no convergence assumption on the algebraic
series is needed. Analyticity of the selected branch and uniqueness supply it. -/
theorem hasSeries_of_branch (p : ℕ) (hp : 2 ≤ p) (F : PowerSeries ℂ)
    (hF0 : constantCoeff F = 0) (hF : F = X + F ^ p)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (he : ∀ᶠ z in 𝓝 0, f z ^ p = f z - z) : HasSeries f F := by
  obtain ⟨G, hg⟩ := exists_series hf
  have hG0 : constantCoeff G = 0 := hg.constantCoeff.trans hf0
  have hG : G = X + G ^ p := by
    apply hg.unique (hasSeries_id.add (hg.pow p))
    filter_upwards [he] with z hz
    linear_combination -hz
  exact formal_branch_unique p hp G F hG0 hF0 hG hF ▸ hg

end PolytopeCounting.ScalarAnalyticSeries
