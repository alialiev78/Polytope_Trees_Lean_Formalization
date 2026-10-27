module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Tactic

/-! # The radical branches in Section 3 and Appendix A

All roots are normalized at the origin. In Cardano's formula the two cube
roots are coupled by their product; taking their principal values independently
would select the wrong root. Ferrari's resolvent uses a cube root nonzero at
zero and expresses its companion by division, avoiding an apparent singularity.
-/

@[expose] public section
noncomputable section
open Filter
open scoped Topology

namespace PolytopeCounting.AppendixA

/-- Principal root, used only with arguments near one for analyticity. -/
def root (n : ℕ) (z : ℂ) : ℂ := z ^ ((n : ℂ)⁻¹)

@[simp] theorem root_one (n : ℕ) : root n 1 = 1 := by simp [root]

theorem root_pow (n : ℕ) (hn : n ≠ 0) (z : ℂ) : root n z ^ n = z :=
  Complex.cpow_nat_inv_pow z hn

theorem analyticAt_root_comp (n : ℕ) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 1) :
    AnalyticAt ℂ (fun z => root n (f z)) 0 := by
  have h := (Complex.one_add_cpow_hasFPowerSeriesAt_zero
    (a := (n : ℂ)⁻¹)).analyticAt
  have hg : AnalyticAt ℂ (fun z => f z - 1) 0 := hf.sub analyticAt_const
  have h' : AnalyticAt ℂ (fun x : ℂ => (1 + x) ^ ((n : ℂ)⁻¹))
      ((fun z => f z - 1) 0) := by simpa [h0] using h
  have hh := AnalyticAt.comp (f := fun z => f z - 1) (x := 0) h' hg
  simpa [root, Function.comp_def] using hh

/-- The cubic summand at zero is `-i/sqrt(3)`. -/
def cubicBase : ℂ := -Complex.I / root 2 3

theorem cubicBase_sq : cubicBase ^ 2 = -(1 / 3 : ℂ) := by
  have hs := root_pow 2 (by decide) (3 : ℂ)
  dsimp [cubicBase]
  rw [div_pow, hs]
  norm_num

theorem cubicBase_ne_zero : cubicBase ≠ 0 := by
  intro h
  have := cubicBase_sq
  rw [h] at this
  norm_num at this

def cubicDiscriminant (t : ℂ) : ℂ :=
  cubicBase ^ 3 * root 2 (1 - 27 * t ^ 2 / 4)

def cubicA (t : ℂ) : ℂ := -t / 2 + cubicDiscriminant t
def cubicU (t : ℂ) : ℂ := cubicBase * root 3 (cubicA t / cubicBase ^ 3)
def cubicV (t : ℂ) : ℂ := 1 / (3 * cubicU t)
def cubicY (t : ℂ) : ℂ := cubicU t + cubicV t

@[simp] theorem cubicDiscriminant_zero : cubicDiscriminant 0 = cubicBase ^ 3 := by
  simp [cubicDiscriminant]
@[simp] theorem cubicA_zero : cubicA 0 = cubicBase ^ 3 := by simp [cubicA]
@[simp] theorem cubicU_zero : cubicU 0 = cubicBase := by
  simp [cubicU, cubicBase_ne_zero]
@[simp] theorem cubicV_zero : cubicV 0 = -cubicBase := by
  simp only [cubicV, cubicU_zero]
  apply (div_eq_iff (mul_ne_zero (by norm_num) cubicBase_ne_zero)).mpr
  linear_combination 3 * cubicBase_sq
@[simp] theorem cubicY_zero : cubicY 0 = 0 := by simp [cubicY]

theorem cubicDiscriminant_sq (t : ℂ) :
    cubicDiscriminant t ^ 2 = t ^ 2 / 4 - 1 / 27 := by
  dsimp [cubicDiscriminant]
  rw [mul_pow, root_pow 2 (by decide)]
  have h6 : (cubicBase ^ 3) ^ 2 = -(1 / 27 : ℂ) := by
    calc (cubicBase ^ 3) ^ 2 = (cubicBase ^ 2) ^ 3 := by ring
         _ = -(1 / 27 : ℂ) := by rw [cubicBase_sq]; norm_num
  rw [h6]
  ring

theorem cubicA_relation (t : ℂ) : cubicA t * (-t / 2 - cubicDiscriminant t) = 1 / 27 := by
  dsimp [cubicA]
  linear_combination -cubicDiscriminant_sq t

theorem cubicU_cube (t : ℂ) : cubicU t ^ 3 = cubicA t := by
  dsimp [cubicU]
  rw [mul_pow, root_pow 3 (by decide)]
  field_simp [cubicBase_ne_zero]

theorem cubicU_ne_zero (t : ℂ) : cubicU t ≠ 0 := by
  intro h
  have he := cubicU_cube t
  have hh := cubicA_relation t
  rw [h] at he
  norm_num at he
  rw [← he] at hh
  norm_num at hh

theorem cubicV_cube (t : ℂ) : cubicV t ^ 3 = -t / 2 - cubicDiscriminant t := by
  dsimp [cubicV]
  rw [div_pow, mul_pow, cubicU_cube]
  have hn : cubicA t ≠ 0 := by rw [← cubicU_cube]; exact pow_ne_zero _ (cubicU_ne_zero t)
  apply (div_eq_iff (mul_ne_zero (by norm_num) hn)).mpr
  linear_combination -27 * cubicA_relation t

theorem cubicUV (t : ℂ) : cubicU t * cubicV t = 1 / 3 := by
  dsimp [cubicV]
  field_simp [cubicU_ne_zero t]

/-- Cardano's formula with the branch that vanishes at the origin. -/
theorem cubicY_equation (t : ℂ) : cubicY t ^ 3 = cubicY t - t := by
  have hsum : cubicU t ^ 3 + cubicV t ^ 3 = -t := by
    rw [cubicU_cube, cubicV_cube, cubicA]
    ring
  dsimp [cubicY]
  linear_combination hsum + 3 * (cubicU t + cubicV t) * cubicUV t

theorem cubicY_analyticAt : AnalyticAt ℂ cubicY 0 := by
  have hd : AnalyticAt ℂ cubicDiscriminant 0 :=
    analyticAt_const.mul (analyticAt_root_comp 2
      (analyticAt_const.sub ((analyticAt_const.mul (analyticAt_id.pow 2)).div
        analyticAt_const (by norm_num))) (by norm_num))
  have ha : AnalyticAt ℂ cubicA 0 :=
    (analyticAt_id.neg.div analyticAt_const (by norm_num)).add hd
  have hu : AnalyticAt ℂ cubicU 0 :=
    analyticAt_const.mul (analyticAt_root_comp 3
      (ha.div analyticAt_const (pow_ne_zero _ cubicBase_ne_zero))
      (by simp [cubicBase_ne_zero]))
  exact hu.add (analyticAt_const.div (analyticAt_const.mul hu)
    (by simpa using mul_ne_zero (by norm_num : (3 : ℂ) ≠ 0) cubicBase_ne_zero))

/-- Normalized square root of Ferrari's discriminant. -/
def quarticDiscriminant (t : ℂ) : ℂ := root 2 (1 - 256 * t ^ 3 / 27) / 2
def quarticA (t : ℂ) : ℂ := root 3 (1 / 2 + quarticDiscriminant t)
def quarticB (t : ℂ) : ℂ := 4 * t / (3 * quarticA t)
def quarticU (t : ℂ) : ℂ := quarticA t + quarticB t
def quarticK (t : ℂ) : ℂ := root 2 (quarticU t)
def quarticL (t : ℂ) : ℂ := (quarticK t ^ 2 - 1 / quarticK t) / 2
def quarticY (t : ℂ) : ℂ :=
  (quarticK t - root 2 (quarticK t ^ 2 - 4 * quarticL t)) / 2

@[simp] theorem quarticDiscriminant_zero : quarticDiscriminant 0 = 1 / 2 := by
  norm_num [quarticDiscriminant]
@[simp] theorem quarticA_zero : quarticA 0 = 1 := by norm_num [quarticA]
@[simp] theorem quarticB_zero : quarticB 0 = 0 := by simp [quarticB]
@[simp] theorem quarticU_zero : quarticU 0 = 1 := by simp [quarticU]
@[simp] theorem quarticK_zero : quarticK 0 = 1 := by simp [quarticK]
@[simp] theorem quarticL_zero : quarticL 0 = 0 := by simp [quarticL]
@[simp] theorem quarticY_zero : quarticY 0 = 0 := by simp [quarticY]

theorem quarticDiscriminant_sq (t : ℂ) :
    quarticDiscriminant t ^ 2 = 1 / 4 - 64 * t ^ 3 / 27 := by
  dsimp [quarticDiscriminant]
  rw [div_pow, root_pow 2 (by decide)]
  ring

theorem quarticA_cube (t : ℂ) : quarticA t ^ 3 = 1 / 2 + quarticDiscriminant t :=
  root_pow 3 (by decide) _

/-- The companion cube root is selected by `a*b=4t/3`. This also specifies its
branch when its value at zero vanishes. -/
theorem quarticB_cube (t : ℂ) (ha : quarticA t ≠ 0) :
    quarticB t ^ 3 = 1 / 2 - quarticDiscriminant t := by
  dsimp [quarticB]
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero _ (mul_ne_zero (by norm_num) ha))).mpr
  simp only [mul_pow, quarticA_cube]
  linear_combination 27 * quarticDiscriminant_sq t

theorem quarticAB (t : ℂ) (ha : quarticA t ≠ 0) :
    quarticA t * quarticB t = 4 * t / 3 := by
  dsimp [quarticB]
  field_simp [ha]

theorem quarticU_equation (t : ℂ) (ha : quarticA t ≠ 0) :
    quarticU t ^ 3 = 1 + 4 * t * quarticU t := by
  have hs : quarticA t ^ 3 + quarticB t ^ 3 = 1 := by
    rw [quarticA_cube, quarticB_cube t ha]
    ring
  dsimp [quarticU]
  linear_combination hs + 3 * (quarticA t + quarticB t) * quarticAB t ha

theorem quarticK_sq (t : ℂ) : quarticK t ^ 2 = quarticU t := root_pow 2 (by decide) _

theorem quarticY_quadratic (t : ℂ) :
    quarticY t ^ 2 - quarticK t * quarticY t + quarticL t = 0 := by
  have hs := root_pow 2 (by decide) (quarticK t ^ 2 - 4 * quarticL t)
  dsimp [quarticY]
  linear_combination hs / 4

/-- Ferrari's selected root solves the quartic wherever its displayed
denominators are nonzero. Both are nonzero in a neighbourhood of zero. -/
theorem quarticY_equation (t : ℂ) (ha : quarticA t ≠ 0) (hk : quarticK t ≠ 0) :
    quarticY t ^ 4 = quarticY t - t := by
  have hu := quarticU_equation t ha
  rw [← quarticK_sq] at hu
  have hy := quarticY_quadratic t
  dsimp [quarticL] at hy
  have hfactor : (quarticY t ^ 2 + quarticK t * quarticY t +
      (quarticK t ^ 2 + 1 / quarticK t) / 2) *
      (quarticY t ^ 2 - quarticK t * quarticY t +
      (quarticK t ^ 2 - 1 / quarticK t) / 2) =
      quarticY t ^ 4 - quarticY t + t := by
    apply (mul_right_injective₀ (pow_ne_zero 2 hk))
    field_simp [hk]
    linear_combination hu
  rw [hy, mul_zero] at hfactor
  linear_combination -hfactor

theorem quarticA_analyticAt : AnalyticAt ℂ quarticA 0 := by
  have hd : AnalyticAt ℂ quarticDiscriminant 0 :=
    (analyticAt_root_comp 2
      (analyticAt_const.sub ((analyticAt_const.mul (analyticAt_id.pow 3)).div
        analyticAt_const (by norm_num))) (by norm_num)).div analyticAt_const (by norm_num)
  exact analyticAt_root_comp 3 (analyticAt_const.add hd) (by norm_num)

theorem quarticK_analyticAt : AnalyticAt ℂ quarticK 0 := by
  have hb : AnalyticAt ℂ quarticB 0 :=
    (analyticAt_const.mul analyticAt_id).div (analyticAt_const.mul quarticA_analyticAt)
      (by simp)
  exact analyticAt_root_comp 2 (quarticA_analyticAt.add hb) (by simp)

theorem quarticY_analyticAt : AnalyticAt ℂ quarticY 0 := by
  have hl : AnalyticAt ℂ quarticL 0 :=
    ((quarticK_analyticAt.pow 2).sub (analyticAt_const.div quarticK_analyticAt
      (by simp))).div analyticAt_const (by norm_num)
  exact (quarticK_analyticAt.sub (analyticAt_root_comp 2
    ((quarticK_analyticAt.pow 2).sub (analyticAt_const.mul hl)) (by simp))).div
    analyticAt_const (by norm_num)

theorem quarticY_eventually_equation :
    ∀ᶠ t in 𝓝 0, quarticY t ^ 4 = quarticY t - t := by
  have ha := quarticA_analyticAt.continuousAt.eventually_ne (by simp : quarticA 0 ≠ 0)
  have hk := quarticK_analyticAt.continuousAt.eventually_ne (by simp : quarticK 0 ≠ 0)
  filter_upwards [ha, hk] with t ht hu using quarticY_equation t ht hu

/-- The complex analytic version of the triangular branch. -/
def quadraticY (t : ℂ) : ℂ := (1 - root 2 (1 - 4 * t)) / 2

@[simp] theorem quadraticY_zero : quadraticY 0 = 0 := by simp [quadraticY]

theorem quadraticY_equation (t : ℂ) : quadraticY t ^ 2 = quadraticY t - t := by
  have h := root_pow 2 (by decide) (1 - 4 * t)
  dsimp [quadraticY]
  linear_combination h / 4

theorem quadraticY_analyticAt : AnalyticAt ℂ quadraticY 0 := by
  exact (analyticAt_const.sub (analyticAt_root_comp 2
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (by norm_num))).div
    analyticAt_const (by norm_num)

theorem root_two_ofReal (x : ℝ) (hx : 0 ≤ x) : root 2 (x : ℂ) = (Real.sqrt x : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx]
  simp [root]

theorem quadraticY_ofReal (t : ℝ) (ht : t ≤ 1 / 4) :
    quadraticY t = (((1 - Real.sqrt (1 - 4 * t)) / 2 : ℝ) : ℂ) := by
  have h : (1 - 4 * (t : ℂ)) = ((1 - 4 * t : ℝ) : ℂ) := by push_cast; rfl
  dsimp [quadraticY]
  rw [h, root_two_ofReal _ (by linarith)]
  push_cast
  rfl

end PolytopeCounting.AppendixA
