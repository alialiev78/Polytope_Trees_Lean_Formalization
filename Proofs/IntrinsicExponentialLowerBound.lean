module

public import Proofs.IntrinsicCorollary53
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section
noncomputable section

/-! # Eventual exponential lower bound for ordinary triangulation classes -/

namespace PolytopeCounting.IntrinsicStellar

open Filter
open scoped Topology

/-- An exponential lower bound divided by a fixed polynomial still dominates
any exponential with a smaller base. -/
theorem eventually_exp_le_binary_bound (v : ℕ) (c : ℝ)
    (hc : 1 < c) (hc2 : c < 2) :
    ∀ᶠ n : ℕ in atTop,
      c ^ n ≤ (2 : ℝ) ^ (n - 1) / (v + n : ℝ) ^ v := by
  have hr0 : (0 : ℝ) ≤ c / 2 := by positivity
  have hr1 : c / 2 < 1 := by linarith
  have hlim : Tendsto
      (fun n : ℕ => 2 * (v + 1 : ℝ) ^ v * ((n : ℝ) ^ v * (c / 2) ^ n))
      atTop (nhds 0) := by
    simpa using
      (tendsto_pow_const_mul_const_pow_of_lt_one v hr0 hr1).const_mul
        (2 * (v + 1 : ℝ) ^ v)
  have hevent : ∀ᶠ n : ℕ in atTop,
      2 * (v + 1 : ℝ) ^ v * ((n : ℝ) ^ v * (c / 2) ^ n) < 1 :=
    hlim.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hevent, eventually_ge_atTop (1 : ℕ)] with n hsmall hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : (v + n : ℝ) ≤ (v + 1 : ℝ) * (n : ℝ) := by
    have hv : (0 : ℝ) ≤ v := Nat.cast_nonneg v
    nlinarith
  have hpow : (v + n : ℝ) ^ v ≤ ((v + 1 : ℝ) * (n : ℝ)) ^ v := by
    gcongr
  have hsmall' : 2 * (v + n : ℝ) ^ v * (c / 2) ^ n < 1 := by
    calc
      _ ≤ 2 * (((v + 1 : ℝ) * (n : ℝ)) ^ v) * (c / 2) ^ n := by
        gcongr
      _ = 2 * (v + 1 : ℝ) ^ v * ((n : ℝ) ^ v * (c / 2) ^ n) := by
        rw [mul_pow]; ring
      _ < 1 := hsmall
  have htwo : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
    ring
  have hratio : 2 * (v + n : ℝ) ^ v * (c / 2) ^ n =
      ((v + n : ℝ) ^ v * c ^ n) / (2 : ℝ) ^ (n - 1) := by
    rw [div_pow, htwo]
    field_simp
  rw [hratio] at hsmall'
  have hprod : (v + n : ℝ) ^ v * c ^ n < (2 : ℝ) ^ (n - 1) := by
    simpa only [one_mul] using
      (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (n - 1))).1 hsmall'
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (v + n : ℝ) ^ v)).2
  simpa [mul_comm] using le_of_lt hprod

/-- The final ordinary-class exponential statement, for the user's original
operation on any fixed initial triangulation. No graph or topology bridge is
an input: both are supplied by the concrete construction above. -/
theorem corollary53_eventually {M : Type*} [TopologicalSpace M]
    (K : Facets) (S : Finset ℕ) (v : ℕ)
    (hS : S ∈ K) (hcard : 3 ≤ S.card) (hpure : Pure K S.card)
    (hb : Bounded K v) (hsupp : support K = Finset.range v)
    (hM : Realization K ≃ₜ M) (c : ℝ) (hc : 1 < c) (hc2 : c < 2) :
    ∀ᶠ n : ℕ in atTop,
      c ^ n ≤ (triangulationCount M (v + n) S.card : ℝ) := by
  filter_upwards [eventually_exp_le_binary_bound v c hc hc2,
      eventually_ge_atTop (1 : ℕ)] with n hbound hn
  exact hbound.trans
    (corollary53_from_initial_triangulation K S v hS hcard hpure hb hsupp hM n hn)

end PolytopeCounting.IntrinsicStellar
