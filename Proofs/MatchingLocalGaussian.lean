module

public import Proofs.MatchingPoissonWindow
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic

@[expose] public section

/-!
# Local Gaussian estimate without a complex-argument Hermite theorem

The large Poisson kernel is asymptotically constant on the small Poisson's
concentration window. Exact parity mass supplies the factor 1/2. Variance
bounds control both tails, including the moving upper cutoff j<=N.
No local limit or saddle-coefficient estimate is a hypothesis of the endpoint.
-/

namespace PolytopeCounting.MatchingSaddle
noncomputable section
open Filter
open scoped Topology BigOperators

def parityTrunc (N : ℕ) (a : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N+1), parityWeight a N j

def parityKernelSum (N : ℕ) (a : ℝ) (g : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N+1),
    if j%2=N%2 then poissonWeight a j*g j else 0

theorem parityWeight_nonneg (a : ℝ) (ha : 0 ≤ a) (p j : ℕ) :
    0 ≤ parityWeight a p j := by
  unfold parityWeight
  split_ifs
  · exact poissonWeight_nonneg a j ha
  · exact le_rfl

theorem parityTrunc_le_mass (N : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    parityTrunc N a ≤ parityMass a N := by
  exact (parityWeight_hasSum a ha N).summable.sum_le_tsum
    (Finset.range (N+1)) (fun j _ ↦ parityWeight_nonneg a ha N j)

/-- A finite second-moment estimate, with the actual weights. -/
theorem finite_variance_div_le (a w : ℝ) (ha : 0 ≤ a) (hw : 0 < w) (S : Finset ℕ) :
    ∑ j ∈ S, (((j : ℝ)-a)^2*poissonWeight a j)/w^2 ≤ a/w^2 := by
  have hs := (poissonWeight_hasSum_variance a ha).div_const (w^2)
  exact (hs.summable.sum_le_tsum S (fun j _ ↦ by
    exact div_nonneg (mul_nonneg (sq_nonneg _) (poissonWeight_nonneg a j ha))
      (sq_nonneg w))).trans_eq hs.tsum_eq

/-- The truncated parity mass loses at most the variance tail. -/
theorem parityTrunc_error (N : ℕ) (a w : ℝ) (ha : 0 ≤ a) (hw : 0 < w)
    (hcut : a+w ≤ (N : ℝ)) :
    |parityTrunc N a-parityMass a N| ≤ a/w^2 := by
  classical
  have hlow := parityTrunc_le_mass N a ha
  have hupper : parityMass a N ≤ parityTrunc N a+a/w^2 := by
    rw [parityMass_eq a ha N]
    apply hasSum_le_of_sum_le (parityWeight_hasSum a ha N)
    intro S
    have hpoint (j : ℕ) : parityWeight a N j ≤
        (if j ≤ N then parityWeight a N j else 0) +
          (((j : ℝ)-a)^2*poissonWeight a j)/w^2 := by
      by_cases hj : j ≤ N
      · rw [if_pos hj]
        have : 0 ≤ (((j : ℝ)-a)^2*poissonWeight a j)/w^2 := by
          exact div_nonneg (mul_nonneg (sq_nonneg _) (poissonWeight_nonneg a j ha))
            (sq_nonneg w)
        linarith
      · rw [if_neg hj, zero_add]
        have hjR : (N : ℝ) < (j : ℝ) := by exact_mod_cast (Nat.lt_of_not_ge hj)
        have hsq : w^2 ≤ ((j : ℝ)-a)^2 := by nlinarith
        have hp : parityWeight a N j ≤ poissonWeight a j := by
          unfold parityWeight
          split_ifs
          · exact le_rfl
          · exact poissonWeight_nonneg a j ha
        refine hp.trans ((le_div_iff₀ (sq_pos_of_pos hw)).2 ?_)
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_right hsq (poissonWeight_nonneg a j ha)
    calc
      ∑ j ∈ S, parityWeight a N j ≤
          ∑ j ∈ S, ((if j ≤ N then parityWeight a N j else 0) +
            (((j : ℝ)-a)^2*poissonWeight a j)/w^2) :=
        Finset.sum_le_sum (fun j _ ↦ hpoint j)
      _ = (∑ j ∈ S.filter (fun j ↦ j ≤ N), parityWeight a N j) +
          ∑ j ∈ S, (((j : ℝ)-a)^2*poissonWeight a j)/w^2 := by
        rw [Finset.sum_add_distrib, Finset.sum_filter]
      _ ≤ parityTrunc N a+a/w^2 := by
        apply add_le_add _ (finite_variance_div_le a w ha hw S)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hj).2; omega)
        · intro j _ _; exact parityWeight_nonneg a ha N j
  rw [abs_of_nonpos (sub_nonpos.mpr hlow)]
  linarith

/-- A finite kernel estimate. Only elementary bounds on g are inputs;
the next theorem derives those inputs for the concrete Poisson kernel. -/
theorem parityKernel_error (N : ℕ) (a w ε : ℝ) (ha : 0 ≤ a) (hw : 0 < w)
    (hε : 0 ≤ ε) (g : ℕ → ℝ)
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ 2)
    (hc : ∀ j, j ≤ N → j%2=N%2 → |(j : ℝ)-a| ≤ w → |g j-1| ≤ ε) :
    |parityKernelSum N a g-parityTrunc N a| ≤ ε+a/w^2 := by
  classical
  let f : ℕ → ℝ := fun j ↦ if j%2=N%2 then poissonWeight a j*(g j-1) else 0
  have he : parityKernelSum N a g-parityTrunc N a =
      ∑ j ∈ Finset.range (N+1), f j := by
    unfold parityKernelSum parityTrunc parityWeight
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f]
    split_ifs <;> ring
  have hp (j : ℕ) (hj : j ∈ Finset.range (N+1)) :
      |f j| ≤ ε*poissonWeight a j + (((j : ℝ)-a)^2*poissonWeight a j)/w^2 := by
    have hpj := poissonWeight_nonneg a j ha
    have hvj : 0 ≤ (((j : ℝ)-a)^2*poissonWeight a j)/w^2 :=
      div_nonneg (mul_nonneg (sq_nonneg _) hpj) (sq_nonneg w)
    by_cases hpar : j%2=N%2
    · dsimp [f]; rw [if_pos hpar, abs_mul, abs_of_nonneg hpj]
      by_cases hnear : |(j : ℝ)-a| ≤ w
      · have hgc := hc j (by have := Finset.mem_range.mp hj; omega) hpar hnear
        nlinarith [mul_le_mul_of_nonneg_left hgc hpj]
      · have hsq : w^2 ≤ ((j : ℝ)-a)^2 := by
          have hfar := lt_of_not_ge hnear
          nlinarith [sq_abs ((j : ℝ)-a)]
        have hunit : |g j-1| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [(hg j).1, (hg j).2]
        have htail : poissonWeight a j ≤ (((j : ℝ)-a)^2*poissonWeight a j)/w^2 := by
          apply (le_div_iff₀ (sq_pos_of_pos hw)).2
          simpa [mul_comm] using mul_le_mul_of_nonneg_right hsq hpj
        nlinarith [mul_le_mul_of_nonneg_left hunit hpj,
          mul_nonneg hε hpj]
    · dsimp [f]; rw [if_neg hpar, abs_zero]
      exact add_nonneg (mul_nonneg hε hpj) hvj
  rw [he]
  calc
    _ ≤ ∑ j ∈ Finset.range (N+1), |f j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (N+1),
        (ε*poissonWeight a j + (((j : ℝ)-a)^2*poissonWeight a j)/w^2) :=
      Finset.sum_le_sum hp
    _ = ε*(∑ j ∈ Finset.range (N+1), poissonWeight a j) +
        ∑ j ∈ Finset.range (N+1), (((j : ℝ)-a)^2*poissonWeight a j)/w^2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ε+a/w^2 := by
      apply add_le_add _ (finite_variance_div_le a w ha hw _)
      simpa using mul_le_mul_of_nonneg_left
        (poissonWeight_sum_le_one a ha (Finset.range (N+1))) hε

/-- Reindex the original finite sum; the parity condition is not discarded. -/
theorem latticeWeight_parity (N : ℕ) (r s : ℝ) :
    latticeWeight N r s =
      ∑ j ∈ Finset.range (N+1),
        if j%2=N%2 then poissonWeight s j*poissonWeight (r*s^2/2) ((N-j)/2)
        else 0 := by
  classical
  unfold latticeWeight
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun k _ ↦ N-2*k) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (by omega)
    · omega
  · intro k hk l hl he
    have hk' := Finset.mem_range.mp hk
    have hl' := Finset.mem_range.mp hl
    omega
  · intro j hj
    have hb := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hp := (Finset.mem_filter.mp hj).2
    refine ⟨(N-j)/2, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    have he : (N-(N-2*k))/2=k := by omega
    rw [he]

def scaledLattice (N : ℕ) (r : ℝ) : ℝ :=
  Real.sqrt (2*Real.pi*pairMean N r) * latticeWeight N r (saddle N r)

theorem scaledLattice_eq (N : ℕ) (r : ℝ) :
    scaledLattice N r = parityKernelSum N (saddle N r)
      (fun j ↦ scaledPoisson (pairMean N r) ((N-j)/2)) := by
  unfold scaledLattice parityKernelSum scaledPoisson pairMean
  rw [latticeWeight_parity, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

theorem parity_exponential_error_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ ↦ Real.exp (-2*saddle N r)/2) atTop (𝓝 0) := by
  have he := Real.tendsto_exp_atTop.comp (saddle_tendsto_atTop r hr)
  have hi := (tendsto_inv_atTop_zero.comp he).pow 2
  have hrewrite (N : ℕ) : (Real.exp (saddle N r))⁻¹ ^ 2 = Real.exp (-2*saddle N r) := by
    calc
      _ = Real.exp (-saddle N r)*Real.exp (-saddle N r) := by
        simp only [pow_two, Real.exp_neg]
      _ = _ := by
        rw [← Real.exp_add]
        congr 1; ring
  simpa only [Function.comp_def, hrewrite, zero_pow (by decide : 2 ≠ 0), zero_div]
    using hi.div_const 2

/-- The factor 1/2 is the asymptotically balanced parity of the small Poisson. -/
theorem scaledLattice_tendsto_half (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ ↦ scaledLattice N r) atTop (𝓝 (1/2)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have he4 : 0 < ε/4 := by positivity
  have he8 : 0 < ε/8 := by positivity
  have htail := (central_tail_scale_tendsto r hr).eventually
    (eventually_lt_nhds he8)
  have hpar := (parity_exponential_error_tendsto r hr).eventually
    (eventually_lt_nhds he4)
  have hglobal := (pairMean_tendsto_atTop r hr).eventually scaledPoisson_eventually_le_two
  filter_upwards [eventually_ge_atTop 1, central_window_below_index r hr,
    central_scaledPoisson_uniform r hr (ε/4) he4, htail, hpar, hglobal]
    with N hN hcut hcentral htail hpar hglobal
  have hs := saddle_pos N r hN hr
  have hw := centralWidth_pos N r hN hr
  have hq := pairMean_pos N r hN hr
  have hg (j : ℕ) : 0 ≤ scaledPoisson (pairMean N r) ((N-j)/2) ∧
      scaledPoisson (pairMean N r) ((N-j)/2) ≤ 2 := by
    constructor
    · exact mul_nonneg (Real.sqrt_nonneg _) (poissonWeight_nonneg _ _ hq.le)
    · exact hglobal _
  have hk := parityKernel_error N (saddle N r) (centralWidth N r) (ε/4)
    hs.le hw he4.le (fun j ↦ scaledPoisson (pairMean N r) ((N-j)/2)) hg
    (fun j hj hp hn ↦ (hcentral j hj hp hn).le)
  rw [← scaledLattice_eq] at hk
  have ht := parityTrunc_error N (saddle N r) (centralWidth N r) hs.le hw hcut
  have hp := parityMass_error (saddle N r) hs.le N
  have hab := abs_sub_le (scaledLattice N r) (parityTrunc N (saddle N r))
    (parityMass (saddle N r) N)
  have hab' := abs_sub_le (scaledLattice N r) (parityMass (saddle N r) N) (1/2)
  rw [Real.dist_eq]
  linarith

theorem curvature_pairMean_ratio_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ ↦ curvature N r/pairMean N r) atTop (𝓝 4) := by
  have hi := (inv_saddle_tendsto_zero r hr).const_mul (2/r)
  have he := hi.const_add 4
  apply (show Tendsto (fun N : ℕ ↦ 4+(2/r)*(saddle N r)⁻¹) atTop (𝓝 4)
    by simpa using he).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hs := saddle_pos N r hN hr
  unfold curvature pairMean
  field_simp [hr.ne', hs.ne']
  ring

/-- Full local Gaussian estimate for the exact finite lattice weight. -/
theorem matching_localGaussian (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ ↦ Real.sqrt (2*Real.pi*curvature N r) *
      latticeWeight N r (saddle N r)) atTop (𝓝 1) := by
  have hc : Tendsto (fun N : ℕ ↦ Real.sqrt (curvature N r/pairMean N r))
      atTop (𝓝 2) := by
    convert (curvature_pairMean_ratio_tendsto r hr).sqrt using 1 <;> norm_num
  have ht := hc.mul (scaledLattice_tendsto_half r hr)
  apply (show Tendsto (fun N : ℕ ↦ Real.sqrt (curvature N r/pairMean N r)*
      scaledLattice N r) atTop (𝓝 1) by simpa using ht).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hq := pairMean_pos N r hN hr
  have hb := curvature_pos N r hN hr
  unfold scaledLattice
  rw [← mul_assoc, ← Real.sqrt_mul (div_nonneg hb.le hq.le)]
  congr 2
  field_simp [hq.ne']

/-- The unconditional matching/Hermite asymptotic in the original notation. -/
theorem matching_hermite_asymptotic (r : ℝ) (hr : 0 < r) :
    HermiteAsymptotic.SequenceEquivalent
      (fun N ↦ HermiteAsymptotic.matchingFactorialSumReal N r)
      (fun N ↦ HermiteAsymptotic.matchingHermiteLeadingTerm N r) :=
  matchingEquivalent_of_localGaussian r hr (matching_localGaussian r hr)

end
end PolytopeCounting.MatchingSaddle
