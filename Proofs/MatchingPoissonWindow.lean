module

public import Proofs.PoissonMomentsAndParity
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Tactic

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# The central Poisson window for the matching saddle

The smaller Poisson has mean s; the larger one has mean q=r*s^2/2.
The window sqrt(s*sqrt(s)) has vanishing Chebyshev tail, but is still
small compared with sqrt(q). All uniformity is proved on the pullback
filter of actual admissible pairs (N,j); it is not an assumed uniform LLT.
-/

namespace PolytopeCounting.MatchingSaddle
noncomputable section
open Filter
open scoped Topology

def pairMean (N : ℕ) (r : ℝ) : ℝ := r*(saddle N r)^2/2

def centralWidth (N : ℕ) (r : ℝ) : ℝ :=
  Real.sqrt (saddle N r * Real.sqrt (saddle N r))

theorem pairMean_pos (N : ℕ) (r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    0 < pairMean N r := by
  have hs := saddle_pos N r hN hr
  unfold pairMean; positivity

theorem index_eq_means (N : ℕ) (r : ℝ) (hr : 0 < r) :
    (N : ℝ) = saddle N r + 2*pairMean N r := by
  unfold pairMean
  nlinarith [saddle_equation N r hr]

theorem centralWidth_pos (N : ℕ) (r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    0 < centralWidth N r := by
  have hs := saddle_pos N r hN hr
  unfold centralWidth; positivity

theorem centralWidth_sq (N : ℕ) (r : ℝ) (hr : 0 < r) :
    (centralWidth N r)^2 = saddle N r * Real.sqrt (saddle N r) := by
  unfold centralWidth
  exact Real.sq_sqrt (mul_nonneg (saddle_nonneg N r hr) (Real.sqrt_nonneg _))

theorem centralWidth_le_saddle (N : ℕ) (r : ℝ) (hr : 0 < r)
    (hs : 1 ≤ saddle N r) : centralWidth N r ≤ saddle N r := by
  have hs0 : 0 ≤ saddle N r := by linarith
  have hroot : Real.sqrt (saddle N r) ≤ saddle N r := by
    have hsq := Real.sq_sqrt hs0
    have hn := Real.sqrt_nonneg (saddle N r)
    nlinarith
  have hw := Real.sqrt_nonneg (saddle N r * Real.sqrt (saddle N r))
  have hsq := centralWidth_sq N r hr
  have hmul := mul_le_mul_of_nonneg_left hroot hs0
  nlinarith

theorem pairMean_eventually_ge_saddle (r : ℝ) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, saddle N r ≤ pairMean N r := by
  filter_upwards [(saddle_tendsto_atTop r hr).eventually
    (eventually_ge_atTop (2/r))] with N hN
  have hs := saddle_nonneg N r hr
  have hm : 2 ≤ r*saddle N r := by
    have := (div_le_iff₀ hr).mp hN
    nlinarith
  unfold pairMean
  nlinarith [mul_le_mul_of_nonneg_right hm hs]

theorem pairMean_tendsto_atTop (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ ↦ pairMean N r) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [pairMean_eventually_ge_saddle r hr,
    (saddle_tendsto_atTop r hr).eventually (eventually_ge_atTop b)] with N hq hs
  exact hs.trans hq

theorem central_tail_scale (N : ℕ) (r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    saddle N r/(centralWidth N r)^2 = (Real.sqrt (saddle N r))⁻¹ := by
  rw [centralWidth_sq N r hr]
  have hs := saddle_pos N r hN hr
  field_simp [hs.ne', (Real.sqrt_pos.2 hs).ne']

theorem central_tail_scale_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ ↦ saddle N r/(centralWidth N r)^2) atTop (𝓝 0) := by
  have hi := (inv_saddle_tendsto_zero r hr).sqrt
  have ht : Tendsto (fun N : ℕ ↦ (Real.sqrt (saddle N r))⁻¹) atTop (𝓝 0) := by
    simpa [Real.sqrt_inv] using hi
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (central_tail_scale N r hN hr).symm

theorem central_window_below_index (r : ℝ) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, saddle N r+centralWidth N r ≤ (N : ℝ) := by
  filter_upwards [pairMean_eventually_ge_saddle r hr,
    (saddle_tendsto_atTop r hr).eventually (eventually_ge_atTop 1)] with N hq hs
  have hw := centralWidth_le_saddle N r hr hs
  have he := index_eq_means N r hr
  have hs0 := saddle_nonneg N r hr
  linarith

/-- An admissible value of the smaller Poisson factor in the central window. -/
structure CentralIndex (r : ℝ) where
  N : ℕ
  j : ℕ
  below : j ≤ N
  parity : j%2 = N%2
  near : |(j : ℝ)-saddle N r| ≤ centralWidth N r

def centralFilter (r : ℝ) : Filter (CentralIndex r) :=
  Filter.comap CentralIndex.N atTop

def complementaryIndex {r : ℝ} (z : CentralIndex r) : ℕ := (z.N-z.j)/2

theorem complementaryIndex_equation {r : ℝ} (z : CentralIndex r) :
    2*complementaryIndex z + z.j = z.N := by
  have hb := z.below
  have hp := z.parity
  unfold complementaryIndex
  omega

theorem complementaryIndex_deviation {r : ℝ} (hr : 0 < r) (z : CentralIndex r) :
    (complementaryIndex z : ℝ)-pairMean z.N r =
      (saddle z.N r-(z.j : ℝ))/2 := by
  have he : 2*(complementaryIndex z : ℝ)+(z.j : ℝ)=(z.N : ℝ) := by
    exact_mod_cast complementaryIndex_equation z
  linarith [index_eq_means z.N r hr]

theorem central_projection_tendsto (r : ℝ) :
    Tendsto (CentralIndex.N : CentralIndex r → ℕ) (centralFilter r) atTop := by
  exact Filter.tendsto_comap

theorem complementaryIndex_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (complementaryIndex : CentralIndex r → ℕ) (centralFilter r) atTop := by
  have hproj := central_projection_tendsto r
  refine tendsto_atTop.2 ?_
  intro M
  filter_upwards [hproj.eventually (pairMean_eventually_ge_saddle r hr),
    hproj.eventually ((saddle_tendsto_atTop r hr).eventually (eventually_ge_atTop 1)),
    hproj.eventually ((pairMean_tendsto_atTop r hr).eventually
      (eventually_ge_atTop (2*(M : ℝ))))] with z hq hs hM
  have hw := centralWidth_le_saddle z.N r hr hs
  have hn := (abs_le.mp z.near).2
  have he := complementaryIndex_deviation hr z
  have hk : (M : ℝ) ≤ (complementaryIndex z : ℝ) := by linarith
  exact_mod_cast hk

theorem central_index_ratio_bound (r : ℝ) (hr : 0 < r) (z : CentralIndex r)
    (hN : 0 < z.N) (hs : 1 ≤ saddle z.N r) :
    |(complementaryIndex z : ℝ)/pairMean z.N r-1| ≤
      1/(r*saddle z.N r) := by
  have hs0 := saddle_pos z.N r hN hr
  have hq := pairMean_pos z.N r hN hr
  have hw := centralWidth_le_saddle z.N r hr hs
  have he := complementaryIndex_deviation hr z
  have hb : |(complementaryIndex z : ℝ)-pairMean z.N r| ≤ saddle z.N r/2 := by
    rw [he, abs_div, abs_sub_comm]
    norm_num
    linarith [z.near]
  have hrat : (complementaryIndex z : ℝ)/pairMean z.N r-1 =
      ((complementaryIndex z : ℝ)-pairMean z.N r)/pairMean z.N r := by
    field_simp [hq.ne']
  rw [hrat, abs_div, abs_of_pos hq]
  calc
    _ ≤ (saddle z.N r/2)/pairMean z.N r := div_le_div_of_nonneg_right hb hq.le
    _ = _ := by unfold pairMean; field_simp [hr.ne', hs0.ne']

theorem central_index_deviation_bound (r : ℝ) (hr : 0 < r) (z : CentralIndex r)
    (hN : 0 < z.N) :
    ((complementaryIndex z : ℝ)-pairMean z.N r)^2/pairMean z.N r ≤
      1/(2*r*Real.sqrt (saddle z.N r)) := by
  have hs := saddle_pos z.N r hN hr
  have hq := pairMean_pos z.N r hN hr
  have hw0 : 0 ≤ centralWidth z.N r := by unfold centralWidth; positivity
  have hsq : ((z.j : ℝ)-saddle z.N r)^2 ≤ (centralWidth z.N r)^2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg ((z.j : ℝ)-saddle z.N r)) hw0).2 z.near
  rw [complementaryIndex_deviation hr z]
  calc
    _ ≤ (centralWidth z.N r)^2/(4*pairMean z.N r) := by
      apply (div_le_iff₀ hq).2
      have : 0 < 4*pairMean z.N r := by positivity
      field_simp [hq.ne']
      nlinarith
    _ = _ := by
      rw [centralWidth_sq z.N r hr]
      unfold pairMean
      have hh := Real.sq_sqrt hs.le
      field_simp [hr.ne', hs.ne', (Real.sqrt_pos.2 hs).ne']
      nlinarith

/-- The central estimate holds on the full filter of admissible pairs. -/
theorem central_scaledPoisson_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun z : CentralIndex r ↦
      scaledPoisson (pairMean z.N r) (complementaryIndex z))
      (centralFilter r) (𝓝 1) := by
  have hproj := central_projection_tendsto r
  have hs := (saddle_tendsto_atTop r hr).comp hproj
  have hi := (inv_saddle_tendsto_zero r hr).comp hproj
  have hpos := hproj.eventually (eventually_ge_atTop 1)
  have hr0 : Tendsto (fun z : CentralIndex r ↦
      (complementaryIndex z : ℝ)/pairMean z.N r-1) (centralFilter r) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun z ↦ 1/(r*saddle z.N r))
    · filter_upwards [hpos, hs.eventually (eventually_ge_atTop 1)] with z hN hs1
      simpa [Real.norm_eq_abs] using central_index_ratio_bound r hr z hN hs1
    · simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using hi.const_mul r⁻¹
  have hrat : Tendsto (fun z : CentralIndex r ↦
      (complementaryIndex z : ℝ)/pairMean z.N r) (centralFilter r) (𝓝 1) := by
    simpa using hr0.add_const 1
  have hdev : Tendsto (fun z : CentralIndex r ↦
      ((complementaryIndex z : ℝ)-pairMean z.N r)^2/pairMean z.N r)
      (centralFilter r) (𝓝 0) := by
    apply squeeze_zero' _ _
      (show Tendsto (fun z : CentralIndex r ↦ 1/(2*r*Real.sqrt (saddle z.N r)))
        (centralFilter r) (𝓝 0) from by
          simpa [div_eq_mul_inv, mul_inv_rev, Real.sqrt_inv, mul_comm, mul_assoc] using
            hi.sqrt.const_mul (2*r)⁻¹)
    · filter_upwards [hpos] with z hN
      exact div_nonneg (sq_nonneg _) (pairMean_pos _ _ hN hr).le
    · filter_upwards [hpos] with z hN
      exact central_index_deviation_bound r hr z hN
  apply scaledPoisson_tendsto_of_near_mean (I := CentralIndex r) (l := centralFilter r)
    (fun z : CentralIndex r ↦ pairMean z.N r)
    (fun z : CentralIndex r ↦ complementaryIndex z) ?_
    (complementaryIndex_tendsto r hr) hrat hdev
  filter_upwards [hpos] with z hN
  exact pairMean_pos z.N r hN hr

/-- Unpack the pullback filter: one threshold works for every central j. -/
theorem central_scaledPoisson_uniform (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ j : ℕ, j ≤ N → j%2 = N%2 →
      |(j : ℝ)-saddle N r| ≤ centralWidth N r →
      |scaledPoisson (pairMean N r) ((N-j)/2)-1| < ε := by
  have he := Metric.tendsto_nhds.mp (central_scaledPoisson_tendsto r hr) ε hε
  simp only [Real.dist_eq] at he
  rcases (Filter.mem_comap (m := (CentralIndex.N : CentralIndex r → ℕ))).mp he with
    ⟨S, hS, hsub⟩
  filter_upwards [hS] with N hN j hj hp hw
  exact hsub (a := (⟨N,j,hj,hp,hw⟩ : CentralIndex r)) hN

end
end PolytopeCounting.MatchingSaddle
