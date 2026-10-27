module

public import Proofs.MatchingSaddleExpansion
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Filter.AtTopBot.Floor
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# A local Poisson estimate derived from Stirling's formula

The input is a positive rate and an integer near its mean. The rate and the
integer may vary along any filter. No local limit theorem is assumed.

The entropy bound is deliberately global (not a formal Taylor series):
  0 <= lambda-k+k*log(k/lambda) <= (k-lambda)^2/lambda.
It will apply uniformly to the large Poisson factor in the matching problem.
-/

namespace PolytopeCounting.MatchingSaddle

noncomputable section
open Filter
open scoped Topology

def poissonRate (a : ℝ) (k : ℕ) : ℝ :=
  a - (k : ℝ) + (k : ℝ)*Real.log ((k : ℝ)/a)

def scaledPoisson (a : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (2*Real.pi*a) * poissonWeight a k

theorem poissonWeight_nonneg (a : ℝ) (k : ℕ) (ha : 0 ≤ a) :
    0 ≤ poissonWeight a k := by
  unfold poissonWeight
  positivity

theorem poissonWeight_pos (a : ℝ) (k : ℕ) (ha : 0 < a) :
    0 < poissonWeight a k := by
  unfold poissonWeight
  positivity

theorem poissonRate_nonneg (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k) :
    0 ≤ poissonRate a k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hkR ha)
  have hm := mul_le_mul_of_nonneg_left hlog hkR.le
  have he : (k : ℝ)*(1-((k : ℝ)/a)⁻¹) = (k : ℝ)-a := by
    field_simp [ha.ne', hkR.ne']
  rw [he] at hm
  unfold poissonRate
  linarith

theorem poissonRate_le_quadratic (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k) :
    poissonRate a k ≤ ((k : ℝ)-a)^2/a := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlog := Real.log_le_sub_one_of_pos (div_pos hkR ha)
  have hm := mul_le_mul_of_nonneg_left hlog hkR.le
  have he : a-(k : ℝ)+(k : ℝ)*((k : ℝ)/a-1) = ((k : ℝ)-a)^2/a := by
    field_simp [ha.ne']; ring
  unfold poissonRate
  linarith

/-- Exact identity, retaining the actual factorial/Stirling ratio. -/
theorem scaledPoisson_eq (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k) :
    scaledPoisson a k =
      Real.sqrt (a/(k : ℝ)) * Real.exp (-poissonRate a k) /
        saddleStirlingRatio k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hfac : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hl : 0 < scaledPoisson a k := by
    unfold scaledPoisson
    exact mul_pos (Real.sqrt_pos.2 (by positivity)) (poissonWeight_pos a k ha)
  have hr : 0 < Real.sqrt (a/(k : ℝ))*Real.exp (-poissonRate a k) /
      saddleStirlingRatio k := by
    unfold saddleStirlingRatio
    positivity
  have he : Real.log (scaledPoisson a k) =
      Real.log (Real.sqrt (a/(k : ℝ))*Real.exp (-poissonRate a k) /
        saddleStirlingRatio k) := by
    simp (disch := positivity) only [scaledPoisson, poissonWeight, poissonRate,
      saddleStirlingRatio, Real.log_mul, Real.log_div, Real.log_sqrt,
      Real.log_pow, Real.log_exp]
    ring
  calc
    _ = Real.exp (Real.log (scaledPoisson a k)) := (Real.exp_log hl).symm
    _ = _ := by rw [he, Real.exp_log hr]

/-- A genuine near-mean local estimate for an arbitrary varying integer.
The quadratic deviation is the checkable scale condition, not a Poisson
or matching asymptotic supplied as an extra input. -/
theorem scaledPoisson_tendsto_of_near_mean {I : Type*} {l : Filter I}
    (a : I → ℝ) (k : I → ℕ)
    (ha : ∀ᶠ i in l, 0 < a i)
    (hk : Tendsto k l atTop)
    (hratio : Tendsto (fun i ↦ (k i : ℝ)/a i) l (𝓝 1))
    (hdev : Tendsto (fun i ↦ ((k i : ℝ)-a i)^2/a i) l (𝓝 0)) :
    Tendsto (fun i ↦ scaledPoisson (a i) (k i)) l (𝓝 1) := by
  have hkpos : ∀ᶠ i in l, 0 < k i := hk.eventually (eventually_ge_atTop 1)
  have hrate : Tendsto (fun i ↦ poissonRate (a i) (k i)) l (𝓝 0) := by
    apply squeeze_zero' _ _ hdev
    · filter_upwards [ha, hkpos] with i hai hki
      exact poissonRate_nonneg _ _ hai hki
    · filter_upwards [ha, hkpos] with i hai hki
      exact poissonRate_le_quadratic _ _ hai hki
  have hroot : Tendsto (fun i ↦ Real.sqrt (a i/(k i : ℝ))) l (𝓝 1) := by
    simpa only [inv_div, inv_one, Real.sqrt_one] using
      (hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).sqrt
  have hst := saddleStirlingRatio_tendsto.comp hk
  have he := hrate.neg.rexp
  have ht := (hroot.mul he).div hst (by norm_num : (1 : ℝ) ≠ 0)
  apply (show Tendsto (fun i ↦ Real.sqrt (a i/(k i : ℝ)) *
      Real.exp (-poissonRate (a i) (k i)) / saddleStirlingRatio (k i))
      l (𝓝 1) by
        convert ht using 1 <;> first | rfl | simp).congr'
  filter_upwards [ha, hkpos] with i hai hki
  exact (scaledPoisson_eq _ _ hai hki).symm

/-- The elementary recurrence is also valid at zero rate. -/
theorem poissonWeight_succ (a : ℝ) (k : ℕ) :
    ((k : ℝ)+1)*poissonWeight a (k+1) = a*poissonWeight a k := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hf]

/-- A mode is floor(a); this supplies a bound valid for every k, not just
inside the central window. -/
theorem poissonWeight_le_mode (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    poissonWeight a k ≤ poissonWeight a ⌊a⌋₊ := by
  let m : ℕ := ⌊a⌋₊
  have hml : (m : ℝ) ≤ a := Nat.floor_le ha
  have hmu : a < (m : ℝ)+1 := Nat.lt_floor_add_one a
  have hup : ∀ j : ℕ, j < m → poissonWeight a j ≤ poissonWeight a (j+1) := by
    intro j hj
    have hja : (j : ℝ)+1 ≤ a := by
      have : (j+1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hj)
      linarith
    have hp := poissonWeight_nonneg a j ha
    have hrec := poissonWeight_succ a j
    have hmul := mul_le_mul_of_nonneg_right hja hp
    nlinarith
  have hdown : ∀ j : ℕ, m ≤ j → poissonWeight a (j+1) ≤ poissonWeight a j := by
    intro j hj
    have hja : a ≤ (j : ℝ)+1 := by
      have : (m : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      linarith
    have hp := poissonWeight_nonneg a j ha
    have hrec := poissonWeight_succ a j
    have hmul := mul_le_mul_of_nonneg_right hja hp
    nlinarith
  by_cases hkm : k ≤ m
  · have hchain : ∀ t : ℕ, ∀ j, j+t ≤ m →
        poissonWeight a j ≤ poissonWeight a (j+t) := by
      intro t
      induction t with
      | zero => intro j _; simp
      | succ t ih =>
        intro j hj
        exact (ih j (by omega)).trans (by
          simpa [Nat.add_assoc] using hup (j+t) (by omega))
    simpa [Nat.add_sub_of_le hkm] using hchain (m-k) k (by omega)
  · have hmk : m ≤ k := by omega
    clear hkm
    induction k, hmk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hmk ih => exact (hdown k hmk).trans ih

/-- The maximum of the rescaled Poisson weights tends to one. -/
theorem scaledPoisson_mode_tendsto :
    Tendsto (fun a : ℝ ↦ scaledPoisson a ⌊a⌋₊) atTop (𝓝 1) := by
  have hk : Tendsto (fun a : ℝ ↦ ⌊a⌋₊) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    filter_upwards [eventually_ge_atTop (M : ℝ)] with a ha
    exact Nat.le_floor ha
  have hi : Tendsto (fun a : ℝ ↦ a⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hrat : Tendsto (fun a : ℝ ↦ (⌊a⌋₊ : ℝ)/a) atTop (𝓝 1) := by
    have hsmall : Tendsto (fun a : ℝ ↦ (⌊a⌋₊ : ℝ)/a-1) atTop (𝓝 0) := by
      apply squeeze_zero_norm' (a := fun a : ℝ ↦ a⁻¹) _ hi
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
      have hp : 0 < a := by linarith
      have hfl := Nat.floor_le hp.le
      have hfu := Nat.lt_floor_add_one a
      have he : (⌊a⌋₊ : ℝ)/a-1 = ((⌊a⌋₊ : ℝ)-a)/a := by
        field_simp [hp.ne']
      rw [Real.norm_eq_abs, he, abs_div, abs_of_pos hp]
      rw [← one_div]
      apply (div_le_div_iff_of_pos_right hp).2
      rw [abs_le]
      constructor <;> linarith
    simpa using hsmall.add_const 1
  have hd : Tendsto (fun a : ℝ ↦ ((⌊a⌋₊ : ℝ)-a)^2/a) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hi
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
      have hp : 0 < a := by linarith
      have hfl := Nat.floor_le hp.le
      have hfu := Nat.lt_floor_add_one a
      rw [← one_div]
      apply (div_le_div_iff_of_pos_right hp).2
      nlinarith
  exact scaledPoisson_tendsto_of_near_mean id (fun a ↦ ⌊a⌋₊)
    (eventually_gt_atTop 0) hk hrat hd

/-- Eventual global bound for the large Poisson factor. -/
theorem scaledPoisson_eventually_le_two :
    ∀ᶠ a : ℝ in atTop, ∀ k : ℕ, scaledPoisson a k ≤ 2 := by
  have hm := scaledPoisson_mode_tendsto.eventually
    (eventually_le_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hm, eventually_ge_atTop (0 : ℝ)] with a ha ha0 k
  exact (mul_le_mul_of_nonneg_left (poissonWeight_le_mode a ha0 k)
    (Real.sqrt_nonneg _)).trans ha

end
end PolytopeCounting.MatchingSaddle
