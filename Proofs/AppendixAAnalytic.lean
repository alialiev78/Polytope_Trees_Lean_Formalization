module

public import Proofs.PublicNumerals

public import Proofs.ScalarAnalyticSeries
public import Proofs.AppendixARadicals
public import Proofs.AppendixAClosedForms
public import Proofs.ManuscriptFixedCoreExplicit
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! # Analytic generating functions from the finite tree counts

The formal branch is constructed from the already proved finite enumeration
recurrence, rather than defined by the desired radical. Uniqueness then
identifies it with the convergent expansions of the normalized radicals.
-/

@[expose] public section
noncomputable section
open Filter PowerSeries
open scoped Topology

namespace PolytopeCounting.AppendixA
open ExplicitFormulas ScalarAnalyticSeries
universe u

/-- The normalized counting series before its lacunary substitution. -/
def countingA (L : Type u) [Fintype L] (q r : ℕ) : PowerSeries ℚ :=
  auxiliarySeries (normalizedTreeCoefficient (q + 2) r
    (fun n => PolytopeTrees.R L n (q + 2) r))

theorem countingA_equation (L : Type u) [Group L] [Fintype L]
    (q r : ℕ) [MulAction L (Fin (q + 2))] (hr : 0 < r)
    (hcard : Fintype.card L = (q + 2) * r) :
    countingA L q r = 1 + X * countingA L q r ^ (q + 1) := by
  let a := normalizedTreeCoefficient (q + 2) (r : ℚ)
    (fun n => PolytopeTrees.R L n (q + 2) r)
  have hrec : SatisfiesPaperTreeRecurrence (q + 2) r
      (fun n => PolytopeTrees.R L n (q + 2) r) := by
    intro n hn
    exact PolytopeTrees.R_recurrence L n (q + 2) r (by omega) hn
  have ha1 : a 1 = 1 := by
    dsimp [a, normalizedTreeCoefficient]
    rw [PolytopeTrees.R_one L (q + 2) r (by omega), hcard]
    simp only [Nat.add_sub_cancel, mul_one, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_ofNat]
    have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp [hr']
    norm_num
    ring
  have h := functional_equation_of_auxiliary_recurrence q a
    (by simpa [a] using normalized_recurrence_of_paper_recurrence (q + 2) r _ hrec)
  simpa [countingA, a, ha1] using h

/-- `Y(t)=t A(t^q)`; the exponent `q=h-2` is positive in Appendix A. -/
def countingY (L : Type u) [Fintype L] (q r : ℕ) (hq : q ≠ 0) : PowerSeries ℚ :=
  X * expand q hq (countingA L q r)

@[simp] theorem countingY_constantCoeff (L : Type u) [Fintype L]
    (q r : ℕ) (hq : q ≠ 0) : constantCoeff (countingY L q r hq) = 0 := by
  simp [countingY]

theorem countingY_equation (L : Type u) [Group L] [Fintype L]
    (q r : ℕ) (hq : q ≠ 0) [MulAction L (Fin (q + 2))] (hr : 0 < r)
    (hcard : Fintype.card L = (q + 2) * r) :
    countingY L q r hq = X + countingY L q r hq ^ (q + 1) := by
  have h := congrArg (fun A : PowerSeries ℚ => X * expand q hq A)
    (countingA_equation L q r hr hcard)
  simp only [map_add, map_one, map_mul, map_pow, expand_X] at h
  simpa [countingY, mul_add, mul_pow, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

theorem countingY_coeff (L : Type u) [Fintype L] (q r n : ℕ) (hq : q ≠ 0)
    (hn : 0 < n) :
    coeff (q * n + 1) (countingY L q r hq) =
      r * PolytopeTrees.R L n (q + 2) r / ((q * n + 1).factorial : ℚ) := by
  unfold countingY
  rw [← pow_one (X : PowerSeries ℚ), coeff_X_pow_mul, coeff_expand_mul]
  simp [countingA, coeff_auxiliarySeries_of_pos _ hn, normalizedTreeCoefficient]

def complexCountingY (L : Type u) [Fintype L] (q r : ℕ) (hq : q ≠ 0) : PowerSeries ℂ :=
  map (algebraMap ℚ ℂ) (countingY L q r hq)

theorem counting_branch_hasSeries (L : Type u) [Group L] [Fintype L]
    (q r : ℕ) (hq : q ≠ 0) [MulAction L (Fin (q + 2))] (hr : 0 < r)
    (hcard : Fintype.card L = (q + 2) * r)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (he : ∀ᶠ t in 𝓝 0, f t ^ (q + 1) = f t - t) :
    HasSeries f (complexCountingY L q r hq) := by
  apply hasSeries_of_branch (q + 1) (by omega)
  · simp only [complexCountingY, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
    rw [coeff_zero_eq_constantCoeff_apply, countingY_constantCoeff]
    simp
  · have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ))
      (countingY_equation L q r hq hr hcard)
    simpa [complexCountingY] using h
  · exact hf
  · exact hf0
  · exact he

/-- The cubic radical is the convergent Taylor series of the actual tree
counts, for the square (`r=1`) and tetrahedron (`r=3`). -/
theorem cubicY_hasSeries (L : Type u) [Group L] [Fintype L]
    (r : ℕ) [MulAction L (Fin 4)] (hr : 0 < r) (hcard : Fintype.card L = 4 * r) :
    HasSeries cubicY (complexCountingY L 2 r (by decide)) := by
  exact counting_branch_hasSeries L 2 r (by decide) hr hcard cubicY cubicY_analyticAt
    cubicY_zero (Filter.Eventually.of_forall cubicY_equation)

/-- The quartic radical is the convergent Taylor series of the actual tree
counts, for the pentagon (`r=1`) and four-simplex (`r=12`). -/
theorem quarticY_hasSeries (L : Type u) [Group L] [Fintype L]
    (r : ℕ) [MulAction L (Fin 5)] (hr : 0 < r) (hcard : Fintype.card L = 5 * r) :
    HasSeries quarticY (complexCountingY L 3 r (by decide)) := by
  exact counting_branch_hasSeries L 3 r (by decide) hr hcard quarticY quarticY_analyticAt
    quarticY_zero quarticY_eventually_equation

/-- Polynomial primitive from the change of variable `t=y-y^(q+1)`. -/
def formalPrimitive (q : ℕ) (r : ℚ) (Y : PowerSeries ℚ) : PowerSeries ℚ :=
  C (1 / ((q + 2 : ℚ) * r)) * Y ^ (q + 2) -
    C (1 / (2 * r)) * Y ^ (2 * q + 2)

private theorem derivative_C_pow (c : ℚ) (Y : PowerSeries ℚ) (n : ℕ) :
    derivative (R := ℚ) (C c * Y ^ n) = C (c * n) * Y ^ (n - 1) * derivative Y := by
  simp only [Derivation.leibniz, derivative_C, derivative_pow, smul_eq_mul,
    mul_zero, add_zero]
  have hn : (n : PowerSeries ℚ) = C (n : ℚ) := by simp
  rw [hn]
  simp only [← mul_assoc, ← map_mul]

theorem formalPrimitive_derivative (q : ℕ) (r : ℚ) (hr : r ≠ 0)
    (Y : PowerSeries ℚ) (hY : Y = X + Y ^ (q + 1)) :
    derivative (R := ℚ) (formalPrimitive q r Y) = C (1 / r) * (Y - X) := by
  have hd := congrArg (derivative (R := ℚ)) hY
  simp only [map_add, derivative_X, derivative_pow, Nat.add_sub_cancel] at hd
  have hn : ((q + 1 : ℕ) : PowerSeries ℚ) = C (q + 1 : ℚ) := by simp
  rw [hn] at hd
  have h1 : (1 / ((q + 2 : ℚ) * r)) * (q + 2 : ℕ) = 1 / r := by
    push_cast
    field_simp
  have h2 : (1 / (2 * r)) * (2 * q + 2 : ℕ) = (q + 1 : ℚ) / r := by
    push_cast
    ring
  unfold formalPrimitive
  rw [map_sub, derivative_C_pow, derivative_C_pow, h1, h2]
  have hpow : 2 * q + 2 - 1 = (q + 1) + q := by omega
  simp only [show q + 2 - 1 = q + 1 by omega, hpow, pow_add]
  have hc : C ((q + 1 : ℚ) / r) = C (1 / r) * C (q + 1 : ℚ) := by
    rw [← map_mul]
    congr 1
    ring
  rw [hc]
  linear_combination C (1 / r) * (Y ^ (q + 1) * hd - hY)

theorem formalPrimitive_coeff (L : Type u) [Group L] [Fintype L]
    (q r n : ℕ) (hq : q ≠ 0) [MulAction L (Fin (q + 2))]
    (hr : 0 < r) (hcard : Fintype.card L = (q + 2) * r) (hn : 0 < n) :
    coeff (q * n + 2) (formalPrimitive q r (countingY L q r hq)) =
      PolytopeTrees.R L n (q + 2) r / ((q * n + 2).factorial : ℚ) := by
  have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have hd := congrArg (coeff (q * n + 1))
    (formalPrimitive_derivative q r hr' _ (countingY_equation L q r hq hr hcard))
  rw [coeff_derivative, coeff_C_mul, map_sub, countingY_coeff L q r n hq hn] at hd
  have hidx : q * n + 1 ≠ 1 := by have := Nat.mul_pos (Nat.pos_of_ne_zero hq) hn; omega
  simp only [coeff_X, ite_eq_right hidx, sub_zero] at hd
  have hn2 : (q * n + 2 : ℚ) ≠ 0 := by positivity
  have hf : ((q * n + 2).factorial : ℚ) =
      (q * n + 2 : ℚ) * ((q * n + 1).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ (q * n + 1)
  rw [hf]
  apply (eq_div_iff (mul_ne_zero hn2 (by positivity))).mpr
  push_cast at hd
  field_simp [hr'] at hd
  nlinarith [hd]

section
attribute [local instance 2000] PolytopeCounting.PublicNumerals.two PolytopeCounting.PublicNumerals.three PolytopeCounting.PublicNumerals.four PolytopeCounting.PublicNumerals.five PolytopeCounting.PublicNumerals.six
/-- Complex analytic primitive, including `r=3` for tetrahedra and `r=12`
for four-dimensional simplices. -/
def analyticPrimitive (q : ℕ) (r : ℚ) (f : ℂ → ℂ) (t : ℂ) : ℂ :=
  f t ^ (q + 2) / (((q : ℂ) + 2) * r) - f t ^ (2 * q + 2) / (2 * r)
end

theorem primitive_hasSeries (q : ℕ) (r : ℚ) (F : PowerSeries ℚ) (f : ℂ → ℂ)
    (hf : HasSeries f (PowerSeries.map (algebraMap ℚ ℂ) F)) :
    HasSeries (analyticPrimitive q r f)
      (PowerSeries.map (algebraMap ℚ ℂ) (formalPrimitive q r F)) := by
  have h := ((hasSeries_const (((1 / ((q + 2 : ℚ) * r)) : ℚ) : ℂ)).mul
      (hf.pow (q + 2))).sub
    ((hasSeries_const (((1 / (2 * r)) : ℚ) : ℂ)).mul (hf.pow (2 * q + 2)))
  convert h using 1
  · funext t
    simp only [analyticPrimitive, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
      Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat]
    ring
  · simp [formalPrimitive]

theorem quadraticY_hasSeries (L : Type u) [Group L] [Fintype L]
    (r : ℕ) [MulAction L (Fin 3)] (hr : 0 < r) (hcard : Fintype.card L = 3 * r) :
    HasSeries quadraticY (complexCountingY L 1 r (by decide)) := by
  exact counting_branch_hasSeries L 1 r (by decide) hr hcard quadraticY quadraticY_analyticAt
    quadraticY_zero (Filter.Eventually.of_forall quadraticY_equation)

theorem triangleR_hasSeries (L : Type u) [Group L] [Fintype L]
    [MulAction L (Fin 3)] (hcard : Fintype.card L = 3) :
    HasSeries (analyticPrimitive 1 1 quadraticY)
      (PowerSeries.map (algebraMap ℚ ℂ) (formalPrimitive 1 1 (countingY L 1 1 (by decide)))) := by
  exact primitive_hasSeries 1 1 _ _ (quadraticY_hasSeries L 1 (by decide) (by simpa using hcard))

theorem cubicR_hasSeries (L : Type u) [Group L] [Fintype L]
    (r : ℕ) [MulAction L (Fin 4)] (hr : 0 < r) (hcard : Fintype.card L = 4 * r) :
    HasSeries (analyticPrimitive 2 r cubicY)
      (PowerSeries.map (algebraMap ℚ ℂ) (formalPrimitive 2 r (countingY L 2 r (by decide)))) := by
  exact primitive_hasSeries 2 r _ _ (cubicY_hasSeries L r hr hcard)

theorem quarticR_hasSeries (L : Type u) [Group L] [Fintype L]
    (r : ℕ) [MulAction L (Fin 5)] (hr : 0 < r) (hcard : Fintype.card L = 5 * r) :
    HasSeries (analyticPrimitive 3 r quarticY)
      (PowerSeries.map (algebraMap ℚ ℂ) (formalPrimitive 3 r (countingY L 3 r (by decide)))) := by
  exact primitive_hasSeries 3 r _ _ (quarticY_hasSeries L r hr hcard)

/-- On the real interval in Appendix A.3 this is exactly formula (64). -/
theorem triangleR_analyticPrimitive (t : ℝ) (ht : t ≤ 1 / 4) :
    analyticPrimitive 1 1 quadraticY t = (triangleR t : ℂ) := by
  rw [analyticPrimitive, quadraticY_ofReal t ht]
  have h := congrArg (fun x : ℝ => (x : ℂ)) (triangleR_polynomial t ht)
  norm_num [triangleY] at h ⊢
  exact h

/-- There are no additional Taylor coefficients between the displayed
boundary degrees. Together with `formalPrimitive_coeff` this specifies the
entire generating series, not just a subsequence of its coefficients. -/
theorem formalPrimitive_coeff_zero (L : Type u) [Group L] [Fintype L]
    (q r m : ℕ) (hq : q ≠ 0) [MulAction L (Fin (q + 2))]
    (hr : 0 < r) (hcard : Fintype.card L = (q + 2) * r)
    (hm : ¬ ∃ n, 0 < n ∧ m = q * n + 2) :
    coeff m (formalPrimitive q r (countingY L q r hq)) = 0 := by
  have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  cases m with
  | zero => simp [coeff_zero_eq_constantCoeff_apply, formalPrimitive]
  | succ m =>
    have hd := congrArg (coeff m)
      (formalPrimitive_derivative q r hr' _ (countingY_equation L q r hq hr hcard))
    rw [coeff_derivative, coeff_C_mul] at hd
    have hz : coeff m (countingY L q r hq - X) = 0 := by
      cases m with
      | zero => simp [coeff_zero_eq_constantCoeff_apply]
      | succ k =>
        rw [map_sub]
        change coeff (k + 1) (X * expand q hq (countingA L q r)) - coeff (k + 1) X = 0
        rw [coeff_succ_X_mul]
        by_cases hk : k = 0
        · subst k
          simp [coeff_zero_eq_constantCoeff_apply, countingA]
        · have hn : ¬ q ∣ k := by
            rintro ⟨n, hn⟩
            apply hm
            refine ⟨n, ?_, ?_⟩
            · by_contra h
              have : n = 0 := by omega
              simp [this] at hn
              exact hk hn
            · omega
          rw [coeff_expand_of_not_dvd q hq _ hn]
          simp [coeff_X, hk]
    rw [hz, mul_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_right (by exact_mod_cast Nat.succ_ne_zero m)

def countingCore (L : Type u) [Fintype L] (q r h₀ : ℕ) (hq : q ≠ 0) : PowerSeries ℚ :=
  C (PolytopeTrees.T L 0 h₀ (q + 2) r / (h₀.factorial : ℚ)) * countingY L q r hq ^ h₀

/-- The fixed-core polynomial has exactly the manuscript's normalized
finite counts as coefficients. -/
theorem countingCore_coeff (L : Type u) [Group L] [Fintype L]
    (q r h₀ n : ℕ) (hq : q ≠ 0) [MulAction L (Fin (q + 2))]
    (hr : 0 < r) (hcard : Fintype.card L = (q + 2) * r) (hbase : 1 ≤ h₀) :
    coeff (q * n + h₀) (countingCore L q r h₀ hq) =
      PolytopeTrees.T L n h₀ (q + 2) r / ((q * n + h₀).factorial : ℚ) := by
  let a := normalizedTreeCoefficient (q + 2) (r : ℚ)
    (fun n => PolytopeTrees.R L n (q + 2) r)
  let u := normalizedFixedCoreCoefficient (q + 2) h₀
    (fun n => PolytopeTrees.T L n h₀ (q + 2) r)
  let A := countingA L q r
  have ht : SatisfiesPaperFixedCoreRecurrence (q + 2) h₀ r
      (fun n => PolytopeTrees.R L n (q + 2) r)
      (fun n => PolytopeTrees.T L n h₀ (q + 2) r) := by
    intro m hm
    exact PolytopeTrees.T_recurrence L m h₀ (q + 2) r (by omega) hbase hm
  have hu : SatisfiesAuxiliaryFixedRecurrence q h₀ a u := by
    simpa [a, u] using normalized_fixed_recurrence_of_paper (q + 2) h₀ r _ _
      (by omega) hbase ht
  have huA : SatisfiesAuxiliaryFixedRecurrence q h₀ (fun k => coeff k A) u := by
    intro m hm
    rw [hu m hm]
    apply Finset.sum_congr rfl
    intro k hk
    have hmk : 0 < m - k := by have := Finset.mem_range.mp hk; omega
    change _ * a (m - k) = _ * coeff (m - k) (auxiliarySeries a)
    rw [coeff_auxiliarySeries_of_pos a hmk]
  have hv := fixedAuxiliaryCoefficient_recurrence A 1 (u 0) q h₀ hbase
    (by simpa [A] using countingA_equation L q r hr hcard)
  have hzero : u 0 = fixedAuxiliaryCoefficient A (u 0) h₀ 0 := by
    simp [fixedAuxiliaryCoefficient, coeff_zero_eq_constantCoeff_apply, A, countingA]
  have he := auxiliary_fixed_recurrence_unique q h₀ _ u _ huA hv hzero n
  unfold countingCore countingY
  rw [coeff_C_mul, mul_pow, ← map_pow, coeff_X_pow_mul,
    coeff_expand_mul]
  simpa [fixedAuxiliaryCoefficient, A, u, normalizedFixedCoreCoefficient] using he.symm

theorem core_hasSeries (L : Type u) [Fintype L] (q r h₀ : ℕ) (hq : q ≠ 0)
    (f : ℂ → ℂ) (hf : HasSeries f (complexCountingY L q r hq)) :
    HasSeries (fun t => ((PolytopeTrees.T L 0 h₀ (q + 2) r : ℚ) : ℂ) /
      (h₀.factorial : ℂ) * f t ^ h₀)
      (PowerSeries.map (algebraMap ℚ ℂ) (countingCore L q r h₀ hq)) := by
  simpa [countingCore, complexCountingY] using
    (hasSeries_const (((PolytopeTrees.T L 0 h₀ (q + 2) r / (h₀.factorial : ℚ) : ℚ) : ℂ))).mul
      (hf.pow h₀)

/-- Differentiating the selected branch gives the manuscript's analytic
equation `R'=(y-t)/r`, as an identity on a neighbourhood of the origin. -/
theorem analyticPrimitive_hasDerivAt (q : ℕ) (r : ℚ) (hr : r ≠ 0)
    (f : ℂ → ℂ) (t : ℂ) (hf : DifferentiableAt ℂ f t)
    (he : ∀ᶠ z in 𝓝 t, f z ^ (q + 1) = f z - z) :
    HasDerivAt (analyticPrimitive q r f) ((f t - t) / r) t := by
  have hy := hf.hasDerivAt
  have hd : (q + 1 : ℂ) * f t ^ q * deriv f t = deriv f t - 1 := by
    have h := (hy.pow (q + 1)).unique
      ((hy.sub (hasDerivAt_id t)).congr_of_eventuallyEq he)
    simpa using h
  have he0 := he.self_of_nhds
  have hh := ((hy.pow (q + 2)).div_const (((q : ℂ) + 2) * r)).sub
    ((hy.pow (2 * q + 2)).div_const (2 * r))
  convert hh using 1
  · rfl
  · have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    have hq' : (q : ℂ) + 2 ≠ 0 := by exact_mod_cast (show q + 2 ≠ 0 by omega)
    simp only [show q + 2 - 1 = q + 1 by omega,
      show 2 * q + 2 - 1 = (q + 1) + q by omega, pow_add,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hr', hq']
    linear_combination f t ^ (q + 1) * hd - he0

theorem analyticPrimitive_eventually_hasDerivAt (q : ℕ) (r : ℚ) (hr : r ≠ 0)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (he : ∀ᶠ z in 𝓝 0, f z ^ (q + 1) = f z - z) :
    ∀ᶠ t in 𝓝 0, HasDerivAt (analyticPrimitive q r f) ((f t - t) / r) t := by
  filter_upwards [hf.eventually_analyticAt, he.eventually_nhds] with t ht he'
  exact analyticPrimitive_hasDerivAt q r hr f t ht.differentiableAt he'

theorem cubicR_derivative (r : ℚ) (hr : r ≠ 0) :
    ∀ᶠ t in 𝓝 0, HasDerivAt (analyticPrimitive 2 r cubicY) ((cubicY t - t) / r) t :=
  analyticPrimitive_eventually_hasDerivAt 2 r hr cubicY cubicY_analyticAt
    (Filter.Eventually.of_forall cubicY_equation)

theorem quarticR_derivative (r : ℚ) (hr : r ≠ 0) :
    ∀ᶠ t in 𝓝 0, HasDerivAt (analyticPrimitive 3 r quarticY) ((quarticY t - t) / r) t :=
  analyticPrimitive_eventually_hasDerivAt 3 r hr quarticY quarticY_analyticAt
    quarticY_eventually_equation

def inversePolynomial (q : ℕ) (z : ℂ) : ℂ := z - z ^ (q + 1)

theorem inversePolynomial_analyticAt (q : ℕ) : AnalyticAt ℂ (inversePolynomial q) 0 :=
  analyticAt_id.sub (analyticAt_id.pow (q + 1))

theorem inversePolynomial_deriv (q : ℕ) (hq : q ≠ 0) :
    deriv (inversePolynomial q) 0 = 1 := by
  have h := (hasDerivAt_id (0 : ℂ)).sub ((hasDerivAt_id (0 : ℂ)).pow (q + 1))
  have h' : HasDerivAt (inversePolynomial q) 1 0 := by
    convert h using 1 <;> first | rfl | simp [hq]
  exact h'.deriv

/-- For every `h=q+2>=3`, the analytic branch exists independently of a
radical expression, by the analytic inverse function theorem. -/
def analyticTreeBranch (q : ℕ) (hq : q ≠ 0) : ℂ → ℂ :=
  (inversePolynomial_analyticAt q).hasStrictDerivAt.localInverse _ _ _
    (by rw [inversePolynomial_deriv q hq]; exact one_ne_zero)

theorem analyticTreeBranch_analyticAt (q : ℕ) (hq : q ≠ 0) :
    AnalyticAt ℂ (analyticTreeBranch q hq) 0 := by
  have h := (inversePolynomial_analyticAt q).analyticAt_localInverse
    (by rw [inversePolynomial_deriv q hq]; exact one_ne_zero)
  simpa [analyticTreeBranch, inversePolynomial] using h

theorem analyticTreeBranch_zero (q : ℕ) (hq : q ≠ 0) : analyticTreeBranch q hq 0 = 0 := by
  have h := HasStrictDerivAt.eventually_left_inverse
    (inversePolynomial_analyticAt q).hasStrictDerivAt
    (by rw [inversePolynomial_deriv q hq]; exact one_ne_zero)
  simpa [inversePolynomial, analyticTreeBranch] using h.self_of_nhds

theorem analyticTreeBranch_equation (q : ℕ) (hq : q ≠ 0) :
    ∀ᶠ t in 𝓝 0, analyticTreeBranch q hq t ^ (q + 1) = analyticTreeBranch q hq t - t := by
  have h := HasStrictDerivAt.eventually_right_inverse
    (inversePolynomial_analyticAt q).hasStrictDerivAt
    (by rw [inversePolynomial_deriv q hq]; exact one_ne_zero)
  simp only [inversePolynomial, zero_pow (by omega : q + 1 ≠ 0), sub_zero] at h
  filter_upwards [h] with t ht
  change analyticTreeBranch q hq t - analyticTreeBranch q hq t ^ (q + 1) = t at ht
  linear_combination -ht

theorem analyticTreeBranch_hasSeries (L : Type u) [Group L] [Fintype L]
    (q r : ℕ) (hq : q ≠ 0) [MulAction L (Fin (q + 2))]
    (hr : 0 < r) (hcard : Fintype.card L = (q + 2) * r) :
    HasSeries (analyticTreeBranch q hq) (complexCountingY L q r hq) :=
  counting_branch_hasSeries L q r hq hr hcard _ (analyticTreeBranch_analyticAt q hq)
    (analyticTreeBranch_zero q hq) (analyticTreeBranch_equation q hq)

/-- Corollary 3.1 and its general version: the boundary-order derivative
of the analytic primitive is the actual finite tree count. -/
theorem primitive_iteratedDeriv (L : Type u) [Group L] [Fintype L]
    (q r n : ℕ) (hq : q ≠ 0) [MulAction L (Fin (q + 2))]
    (hr : 0 < r) (hcard : Fintype.card L = (q + 2) * r) (hn : 0 < n)
    (f : ℂ → ℂ) (hf : HasSeries f (complexCountingY L q r hq)) :
    iteratedDeriv (q * n + 2) (analyticPrimitive q r f) 0 =
      (PolytopeTrees.R L n (q + 2) r : ℂ) := by
  have hs := primitive_hasSeries q r (countingY L q r hq) f hf
  have he := HasFPowerSeriesAt.eq_formalMultilinearSeries hs hs.analyticAt.hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff (q * n + 2)) he
  simp only [FormalMultilinearSeries.coeff_ofScalars, coeff_map,
    formalPrimitive_coeff L q r n hq hr hcard hn] at hc
  have hfac : ((q * n + 2).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (q * n + 2)
  norm_cast at hc
  field_simp [hfac] at hc
  simpa [map_div₀, map_natCast, hfac] using hc.symm

end PolytopeCounting.AppendixA
