module

public import Proofs.IntrinsicStellarFaces
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-! # Global relative homeomorphisms and explicit linear pieces -/

namespace PolytopeCounting.IntrinsicStellar

open BinaryStellarSpine

abbrev Coordinates := ℕ → ℝ

def InSimplex (S : Finset ℕ) (x : Coordinates) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∑ i ∈ S, x i) = 1 ∧ ∀ i ∉ S, x i = 0

def InCarrier (K : Facets) (x : Coordinates) : Prop :=
  ∃ S ∈ K, InSimplex S x

abbrev Realization (K : Facets) := {x : Coordinates // InCarrier K x}

def minCoordinate (S : Finset ℕ) (hne : S.Nonempty) (x : Coordinates) : ℝ :=
  S.inf' hne x

def collapse (S : Finset ℕ) (p : ℕ) (y : Coordinates) : Coordinates :=
  fun i => if i = p then 0 else y i + if i ∈ S then y p / (S.card : ℝ) else 0

def expand (S : Finset ℕ) (hne : S.Nonempty) (p : ℕ)
    (x : Coordinates) : Coordinates :=
  fun i => if i = p then (S.card : ℝ) * minCoordinate S hne x
    else x i - if i ∈ S then minCoordinate S hne x else 0

def sectorLinear (S : Finset ℕ) (p a : ℕ) (x : Coordinates) : Coordinates :=
  fun i => if i = p then (S.card : ℝ) * x a else x i - if i ∈ S then x a else 0

private theorem card_real_pos {S : Finset ℕ} (hne : S.Nonempty) :
    (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hne

theorem minCoordinate_le {S : Finset ℕ} (hne : S.Nonempty) (x : Coordinates)
    {i : ℕ} (hi : i ∈ S) : minCoordinate S hne x ≤ x i :=
  Finset.inf'_le x hi

theorem le_minCoordinate {S : Finset ℕ} (hne : S.Nonempty) (x : Coordinates)
    {a : ℝ} (h : ∀ i ∈ S, a ≤ x i) : a ≤ minCoordinate S hne x :=
  Finset.le_inf' hne x h

theorem minimum_attained (S : Finset ℕ) (hne : S.Nonempty) (x : Coordinates) :
    ∃ a ∈ S, x a = minCoordinate S hne x := by
  obtain ⟨a, ha, hmin⟩ := S.exists_min_image x hne
  exact ⟨a, ha, le_antisymm (le_minCoordinate hne x hmin)
    (minCoordinate_le hne x ha)⟩

theorem minCoordinate_zero {S : Finset ℕ} (hne : S.Nonempty) (x : Coordinates)
    (hx : ∀ i, 0 ≤ x i) (hz : ∃ a ∈ S, x a = 0) :
    minCoordinate S hne x = 0 := by
  obtain ⟨a, ha, hzero⟩ := hz
  apply le_antisymm
  · simpa [hzero] using minCoordinate_le hne x ha
  · exact le_minCoordinate hne x (fun i _ => hx i)

theorem continuous_minCoordinate (S : Finset ℕ) (hne : S.Nonempty) :
    Continuous (minCoordinate S hne) := by
  exact Continuous.finset_inf'_apply hne (fun i _ => continuous_apply i)

theorem continuous_collapse (S : Finset ℕ) (p : ℕ) : Continuous (collapse S p) := by
  apply continuous_pi
  intro i
  by_cases hip : i = p
  · simpa [collapse, hip] using (continuous_const : Continuous (fun _ : Coordinates => (0 : ℝ)))
  · by_cases hi : i ∈ S
    · simp only [collapse, ite_eq_right hip, ite_eq_left hi]
      fun_prop
    · simpa [collapse, hip, hi] using continuous_apply i

theorem continuous_expand (S : Finset ℕ) (hne : S.Nonempty) (p : ℕ) :
    Continuous (expand S hne p) := by
  apply continuous_pi
  intro i
  by_cases hip : i = p
  · simpa [expand, hip] using (continuous_minCoordinate S hne).const_mul (S.card : ℝ)
  · by_cases hi : i ∈ S
    · simp only [expand, ite_eq_right hip, ite_eq_left hi]
      have hm := continuous_minCoordinate S hne
      fun_prop
    · simpa [expand, hip, hi] using continuous_apply i

theorem collapse_eq_self (S : Finset ℕ) (p : ℕ) (x : Coordinates)
    (hp : x p = 0) : collapse S p x = x := by
  funext i
  by_cases hi : i = p <;> simp [collapse, hi, hp]

theorem expand_eq_self (S : Finset ℕ) (hne : S.Nonempty) (p : ℕ)
    (x : Coordinates) (hp : x p = 0) (hm : minCoordinate S hne x = 0) :
    expand S hne p x = x := by
  funext i
  by_cases hi : i = p <;> simp [expand, hi, hp, hm]

/-- A maximal face different from S omits a vertex of S. -/
theorem omitted_in_exterior (K : Facets) (S : Finset ℕ)
    (hmax : ∀ T ∈ K, S ⊆ T → T = S)
    {T : Finset ℕ} (hT : T ∈ K) (hne : T ≠ S) :
    ∃ a ∈ S, a ∉ T := by
  apply Finset.not_subset.mp
  intro hsub
  exact hne (hmax T hT hsub)

theorem collapse_expand (S : Finset ℕ) (hne : S.Nonempty) (p : ℕ)
    (_hpS : p ∉ S) (x : Coordinates) (hxp : x p = 0) :
    collapse S p (expand S hne p x) = x := by
  have hq : (S.card : ℝ) ≠ 0 := ne_of_gt (card_real_pos hne)
  funext i
  by_cases hip : i = p
  · simp [collapse, hip, hxp]
  · by_cases hi : i ∈ S
    · simp [collapse, expand, hip, hi, hq]
    · simp [collapse, expand, hip, hi]

theorem min_collapse (S : Finset ℕ) (hne : S.Nonempty) (p : ℕ)
    (hpS : p ∉ S) (y : Coordinates) (hy : ∀ i, 0 ≤ y i)
    (hz : ∃ a ∈ S, y a = 0) :
    minCoordinate S hne (collapse S p y) = y p / (S.card : ℝ) := by
  obtain ⟨a, ha, hzero⟩ := hz
  have hap : a ≠ p := by intro h; exact hpS (h ▸ ha)
  apply le_antisymm
  · simpa [collapse, hap, ha, hzero] using
      minCoordinate_le hne (collapse S p y) ha
  · apply le_minCoordinate hne
    intro i hi
    have hip : i ≠ p := by intro h; exact hpS (h ▸ hi)
    simp only [collapse, ite_eq_right hip, ite_eq_left hi]
    linarith [hy i]

theorem expand_collapse (S : Finset ℕ) (hne : S.Nonempty) (p : ℕ)
    (hpS : p ∉ S) (y : Coordinates) (hy : ∀ i, 0 ≤ y i)
    (hz : ∃ a ∈ S, y a = 0) :
    expand S hne p (collapse S p y) = y := by
  have hq : (S.card : ℝ) ≠ 0 := ne_of_gt (card_real_pos hne)
  have hm := min_collapse S hne p hpS y hy hz
  funext i
  by_cases hip : i = p
  · simp [expand, hip, hm]
    field_simp [hq]
  · by_cases hi : i ∈ S
    · simp [expand, collapse, hip, hi, hm]
    · simp [expand, collapse, hip, hi]

theorem expand_inside_simplex (S : Finset ℕ) (hne : S.Nonempty) (p : ℕ)
    (hpS : p ∉ S) (x : Coordinates) (hx : InSimplex S x) :
    ∃ a ∈ S, InSimplex (insert p (S.erase a)) (expand S hne p x) := by
  obtain ⟨a, ha, ham⟩ := minimum_attained S hne x
  have hm0 : 0 ≤ minCoordinate S hne x := le_minCoordinate hne x (fun i _ => hx.1 i)
  have hq : (0 : ℝ) < S.card := card_real_pos hne
  have hpa : p ∉ S.erase a := by
    intro hp; exact hpS (Finset.mem_erase.mp hp).2
  have hca : ((S.erase a).card : ℝ) + 1 = (S.card : ℝ) := by
    exact_mod_cast Finset.card_erase_add_one ha
  have hsum : (∑ i ∈ S.erase a, x i) + x a = 1 := by
    rw [Finset.sum_erase_add _ _ ha, hx.2.1]
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · intro i
    by_cases hip : i = p
    · simp only [expand, ite_eq_left hip]
      exact mul_nonneg (le_of_lt hq) hm0
    · by_cases hi : i ∈ S
      · simpa [expand, hip, hi] using sub_nonneg.mpr (minCoordinate_le hne x hi)
      · simpa [expand, hip, hi] using hx.1 i
  · rw [Finset.sum_insert hpa]
    have he : (∑ i ∈ S.erase a, expand S hne p x i) =
        (∑ i ∈ S.erase a, x i) - ((S.erase a).card : ℝ) * minCoordinate S hne x := by
      calc
        _ = ∑ i ∈ S.erase a, (x i - minCoordinate S hne x) := by
          apply Finset.sum_congr rfl
          intro i hi
          have his := (Finset.mem_erase.mp hi).2
          have hip : i ≠ p := by intro h; exact hpS (h ▸ his)
          simp [expand, hip, his]
        _ = _ := by simp [Finset.sum_sub_distrib, nsmul_eq_mul]
    rw [he]
    simp only [expand, ↓reduceIte]
    rw [ham] at hsum
    nlinarith
  · intro i hi
    have hip : i ≠ p := by intro he; subst i; simp at hi
    by_cases his : i ∈ S
    · have hia : i = a := by
        by_contra hia
        exact hi (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hia, his⟩))
      subst i
      simp [expand, hip, ha, ham]
    · simp [expand, hip, his, hx.2.2 i his]

theorem collapse_child (S : Finset ℕ) (hne : S.Nonempty) (p a : ℕ)
    (hpS : p ∉ S) (ha : a ∈ S) (y : Coordinates)
    (hy : InSimplex (insert p (S.erase a)) y) : InSimplex S (collapse S p y) := by
  have hq : (0 : ℝ) < S.card := card_real_pos hne
  have hqn : (S.card : ℝ) ≠ 0 := ne_of_gt hq
  have hap : a ≠ p := by intro h; exact hpS (h ▸ ha)
  have hya : y a = 0 := hy.2.2 a (by simp [hap])
  have hpa : p ∉ S.erase a := by intro h; exact hpS (Finset.mem_erase.mp h).2
  have hs : (∑ i ∈ S, y i) + y p = 1 := by
    have hs' := hy.2.1
    rw [Finset.sum_insert hpa] at hs'
    have he := Finset.sum_erase_add S y ha
    rw [hya, add_zero] at he
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hip : i = p
    · simp [collapse, hip]
    · by_cases hi : i ∈ S
      · simpa [collapse, hip, hi] using
          add_nonneg (hy.1 i) (div_nonneg (hy.1 p) (le_of_lt hq))
      · simpa [collapse, hip, hi] using hy.1 i
  · have he : (∑ i ∈ S, collapse S p y i) =
        (∑ i ∈ S, y i) + (S.card : ℝ) * (y p / (S.card : ℝ)) := by
      calc
        _ = ∑ i ∈ S, (y i + y p / (S.card : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hip : i ≠ p := by intro h; exact hpS (h ▸ hi)
          simp [collapse, hip, hi]
        _ = _ := by simp [Finset.sum_add_distrib, nsmul_eq_mul]
    rw [he]
    have hcancel : (S.card : ℝ) * (y p / (S.card : ℝ)) = y p := by
      field_simp [hqn]
    rw [hcancel]
    exact hs
  · intro i hi
    by_cases hip : i = p
    · simp [collapse, hip]
    · have hnot : i ∉ insert p (S.erase a) := by simp [hip, hi]
      simp [collapse, hip, hi, hy.2.2 i hnot]

theorem carrier_old_coordinate_zero (K : Facets) (p : ℕ) (hb : Bounded K p)
    {x : Coordinates} (hx : InCarrier K x) : x p = 0 := by
  obtain ⟨T, hT, hx⟩ := hx
  exact hx.2.2 p (fresh_not_face K p hb hT)

theorem expand_inCarrier (K : Facets) (S : Finset ℕ) (hne : S.Nonempty) (p : ℕ)
    (hS : S ∈ K) (hb : Bounded K p)
    (hmax : ∀ T ∈ K, S ⊆ T → T = S)
    {x : Coordinates} (hx : InCarrier K x) :
    InCarrier (replace K S p) (expand S hne p x) := by
  obtain ⟨T, hT, hx⟩ := hx
  by_cases he : T = S
  · subst T
    obtain ⟨a, ha, hy⟩ := expand_inside_simplex S hne p
      (fresh_not_face K p hb hS) x hx
    exact ⟨insert p (S.erase a), child_mem_replace K S p a ha, hy⟩
  · obtain ⟨a, ha, han⟩ := omitted_in_exterior K S hmax hT he
    have hm := minCoordinate_zero hne x hx.1 ⟨a, ha, hx.2.2 a han⟩
    have hp := hx.2.2 p (fresh_not_face K p hb hT)
    rw [expand_eq_self S hne p x hp hm]
    exact ⟨T, old_mem_replace hT he, hx⟩

theorem collapse_inCarrier (K : Facets) (S : Finset ℕ) (hne : S.Nonempty) (p : ℕ)
    (hS : S ∈ K) (hb : Bounded K p)
    {y : Coordinates} (hy : InCarrier (replace K S p) y) :
    InCarrier K (collapse S p y) := by
  obtain ⟨T, hT, hy⟩ := hy
  rcases Finset.mem_union.mp hT with hold | hnew
  · have hTK := (Finset.mem_erase.mp hold).2
    have hp := hy.2.2 p (fresh_not_face K p hb hTK)
    rw [collapse_eq_self S p y hp]
    exact ⟨T, hTK, hy⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hnew
    exact ⟨S, hS, collapse_child S hne p a (fresh_not_face K p hb hS) ha y hy⟩

theorem newCarrier_has_zero (K : Facets) (S : Finset ℕ) (p : ℕ)
    (hS : S ∈ K) (hb : Bounded K p)
    (hmax : ∀ T ∈ K, S ⊆ T → T = S)
    {y : Coordinates} (hy : InCarrier (replace K S p) y) :
    (∀ i, 0 ≤ y i) ∧ ∃ a ∈ S, y a = 0 := by
  obtain ⟨T, hT, hy⟩ := hy
  refine ⟨hy.1, ?_⟩
  rcases Finset.mem_union.mp hT with hold | hnew
  · obtain ⟨a, ha, han⟩ := omitted_in_exterior K S hmax
      (Finset.mem_erase.mp hold).2 (Finset.mem_erase.mp hold).1
    exact ⟨a, ha, hy.2.2 a han⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hnew
    have hap : a ≠ p := by
      intro he; exact fresh_not_face K p hb hS (he ▸ ha)
    exact ⟨a, ha, hy.2.2 a (by simp [hap])⟩

/-- A genuine homeomorphism of the complete realizations. -/
def stellarHomeomorph (K : Facets) (S : Finset ℕ) (hne : S.Nonempty) (p : ℕ)
    (hS : S ∈ K) (hb : Bounded K p)
    (hmax : ∀ T ∈ K, S ⊆ T → T = S) :
    Realization (replace K S p) ≃ₜ Realization K where
  toFun y := ⟨collapse S p y.1, collapse_inCarrier K S hne p hS hb y.2⟩
  invFun x := ⟨expand S hne p x.1, expand_inCarrier K S hne p hS hb hmax x.2⟩
  left_inv y := by
    apply Subtype.ext
    have hz := newCarrier_has_zero K S p hS hb hmax y.2
    exact expand_collapse S hne p (fresh_not_face K p hb hS) y.1 hz.1 hz.2
  right_inv x := by
    apply Subtype.ext
    exact collapse_expand S hne p (fresh_not_face K p hb hS) x.1
      (carrier_old_coordinate_zero K p hb x.2)
  continuous_toFun := ((continuous_collapse S p).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_expand S hne p).comp continuous_subtype_val).subtype_mk _

/-- The exterior is fixed pointwise, including every old boundary face. -/
theorem stellar_relative_exterior (K : Facets) (S : Finset ℕ) (hne : S.Nonempty)
    (p : ℕ) (hb : Bounded K p) (hmax : ∀ T ∈ K, S ⊆ T → T = S)
    {T : Finset ℕ} (hT : T ∈ K) (hTS : T ≠ S)
    (x : Coordinates) (hx : InSimplex T x) : expand S hne p x = x := by
  obtain ⟨a, ha, han⟩ := omitted_in_exterior K S hmax hT hTS
  exact expand_eq_self S hne p x (hx.2.2 p (fresh_not_face K p hb hT))
    (minCoordinate_zero hne x hx.1 ⟨a, ha, hx.2.2 a han⟩)

/-- Explicit finite piecewise-linear inverse, on each minimum sector. -/
theorem expand_on_sector (S : Finset ℕ) (hne : S.Nonempty) (p a : ℕ)
    (ha : a ∈ S) (x : Coordinates) (hmin : ∀ i ∈ S, x a ≤ x i) :
    expand S hne p x = sectorLinear S p a x := by
  have hm : minCoordinate S hne x = x a :=
    le_antisymm (minCoordinate_le hne x ha) (le_minCoordinate hne x hmin)
  funext i
  simp only [expand, sectorLinear, hm]

theorem collapse_linear (S : Finset ℕ) (p : ℕ) (x y : Coordinates) (a b : ℝ) :
    collapse S p (fun i => a * x i + b * y i) =
      fun i => a * collapse S p x i + b * collapse S p y i := by
  funext i
  by_cases hip : i = p <;> by_cases hi : i ∈ S <;>
    simp [collapse, hip, hi]; ring

theorem sector_linear (S : Finset ℕ) (p i : ℕ) (x y : Coordinates) (a b : ℝ) :
    sectorLinear S p i (fun j => a * x j + b * y j) =
      fun j => a * sectorLinear S p i x j + b * sectorLinear S p i y j := by
  funext j
  by_cases hjp : j = p <;> by_cases hj : j ∈ S <;>
    simp [sectorLinear, hjp, hj] <;> ring

/-- Every point is in one of the finitely many pieces of the inverse. -/
theorem expand_has_linear_piece (S : Finset ℕ) (hne : S.Nonempty) (p : ℕ)
    (x : Coordinates) : ∃ a ∈ S, expand S hne p x = sectorLinear S p a x := by
  obtain ⟨a, ha, hmin⟩ := S.exists_min_image x hne
  exact ⟨a, ha, expand_on_sector S hne p a ha x hmin⟩

/-- Composition supplies the global homeomorphism for the actual sequence
used in the lower-bound construction, on any fixed initial pure complex. -/
def evolveHomeomorph (K : Facets) (s : State) (bs : List Bool) (h : Valid s K) :
    Realization (evolve K s bs) ≃ₜ Realization K := by
  have step (K : Facets) (s : State) (h : Valid s K) :
      Realization (replace K s.vertices s.nextFresh) ≃ₜ Realization K := by
    have hne : s.vertices.Nonempty :=
      Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 3) h.dimension)
    have hmax : ∀ T ∈ K, s.vertices ⊆ T → T = s.vertices := by
      intro T hT hsub
      exact (maximal_of_pure h.pure h.selected hT hsub).symm
    exact stellarHomeomorph K s.vertices hne s.nextFresh h.selected h.bounded hmax
  induction bs generalizing K s with
  | nil => exact step K s h
  | cons b bs ih =>
      exact (ih (replace K s.vertices s.nextFresh) (advance s b)
        (valid_advance h b)).trans (step K s h)

/-- Same underlying space, including a manifold when M is a manifold. -/
def evolveHomeomorphTo {M : Type*} [TopologicalSpace M]
    (K : Facets) (s : State) (bs : List Bool) (h : Valid s K)
    (hM : Realization K ≃ₜ M) : Realization (evolve K s bs) ≃ₜ M :=
  (evolveHomeomorph K s bs h).trans hM

end PolytopeCounting.IntrinsicStellar
