module

public import Proofs.EuclideanFacetRestriction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic

@[expose] public section

/-!
# Actual supporting faces and complete flags of a finite polytope

A facet is a maximal nonempty proper supporting face. In particular neither
codimension one, an affine frame, nor rigidity is included in the definition.
The centroid-span theorem below proves the needed codimension-one statement by
perturbing a supporting affine functional. Flags carry only vertex subsets;
choices of functionals are propositions, not extra geometric decorations.

-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry.GeometricFlags
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]

/-- Nonempty proper face exposed by an affine functional. The maximum has been
normalized to zero; this entails no restriction on supporting hyperplanes. -/
def Supported (s t : Finset E) : Prop :=
  t.Nonempty ∧ ∃ f : E →ᵃ[ℝ] ℝ,
    (∀ x ∈ s, f x ≤ 0) ∧
    (∀ x, x ∈ t ↔ x ∈ s ∧ f x = 0) ∧
    ∃ x ∈ s, f x < 0

/-- The usual relative facet: a maximal proper supporting face. -/
def Facet (s t : Finset E) : Prop :=
  Supported s t ∧ ∀ u, Supported s u → t ⊆ u → u = t

theorem Supported.subset {s t : Finset E} (H : Supported s t) : t ⊆ s := by
  rcases H with ⟨_, f, _, hv, _⟩
  intro x hx
  exact ((hv x).mp hx).1

theorem Supported.ssubset {s t : Finset E} (H : Supported s t) : t ⊂ s := by
  refine ⟨H.subset, ?_⟩
  rcases H with ⟨_, f, _, hv, x, hx, hlt⟩
  intro hst
  have hz := ((hv x).mp (hst hx)).2
  linarith

theorem Supported.parent_nonempty {s t : Finset E} (H : Supported s t) : s.Nonempty := by
  rcases H.1 with ⟨x, hx⟩
  exact ⟨x, H.subset hx⟩

/-- An affine functional evaluated at the arithmetic centroid. -/
theorem affine_centroid_value (s : Finset E) (hs : s.Nonempty)
    (f : E →ᵃ[ℝ] ℝ) :
    f (s.centroid ℝ id) = (s.card : ℝ)⁻¹ * ∑ x ∈ s, f x := by
  rw [Finset.centroid_def]
  rw [Finset.map_affineCombination _ _ _
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  rw [Finset.affineCombination_eq_linear_combination _ _ _
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp only [Finset.centroidWeights_apply, smul_eq_mul, Function.comp_apply, id_eq,
    ← Finset.mul_sum]

theorem centroid_mem_span (s : Finset E) (hs : s.Nonempty) :
    s.centroid ℝ id ∈ affineSpan ℝ (s : Set E) := by
  letI : Nonempty {x : E // x ∈ s} := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  have H := centroid_mem_affineSpan_of_nonempty ℝ
    (Subtype.val : {x : E // x ∈ s} → E)
    (Finset.univ_nonempty : (Finset.univ : Finset {x : E // x ∈ s}).Nonempty)
  have hr : Set.range (Subtype.val : {x : E // x ∈ s} → E) = (s : Set E) := by
    ext x
    simp
  simpa only [Finset.centroid_univ, hr] using H

theorem supporting_centroid_strict {s : Finset E}
    (hs : s.Nonempty) (f : E →ᵃ[ℝ] ℝ)
    (hbelow : ∀ x ∈ s, f x ≤ 0) (hproper : ∃ x ∈ s, f x < 0) :
    f (s.centroid ℝ id) < 0 := by
  have hp : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hsum : (∑ x ∈ s, f x) < 0 := by
    simpa using Finset.sum_lt_sum hbelow hproper
  rw [affine_centroid_value s hs f]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hp) hsum

/-- Algebraic affine separation: no finite-dimensional or continuity assumption
is needed, since only finitely generated affine spans will be used. -/
theorem separate_affine_subspace (A : AffineSubspace ℝ E) {p x : E}
    (hp : p ∈ A) (hx : x ∉ A) :
    ∃ f : E →ᵃ[ℝ] ℝ, (∀ y ∈ A, f y = 0) ∧ 0 < f x := by
  have hv : x -ᵥ p ∉ A.direction := by
    intro h
    exact hx ((A.vsub_right_mem_direction_iff_mem hp x).mp h)
  obtain ⟨l, hl, hzero⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv
    (inferInstance : Module.Projective ℝ (V ⧸ A.direction))
  let a : E →ᵃ[ℝ] ℝ := AffineMap.mk'
    (fun y ↦ l (y -ᵥ p)) l p (by
      intro y
      simp)
  have ha : ∀ y ∈ A, a y = 0 := by
    intro y hy
    have hz : l (y -ᵥ p) ∈ A.direction.map l :=
      ⟨y -ᵥ p, A.vsub_mem_direction hy hp, rfl⟩
    rw [hzero] at hz
    exact hz
  by_cases hpos : 0 < a x
  · exact ⟨a, ha, hpos⟩
  · refine ⟨-a, ?_, ?_⟩
    · intro y hy
      simp [ha y hy]
    · change 0 < -l (x -ᵥ p)
      have hn : l (x -ᵥ p) < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hl
      linarith

/-- Every nonsingleton finite point set has a nonempty proper exposed face. -/
theorem exists_supported {s : Finset E} (hs : 1 < s.card) :
    ∃ t, Supported s t := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hs
  have hpA : p ∈ affineSpan ℝ ({p} : Set E) := subset_affineSpan ℝ _ (by simp)
  have hqA : q ∉ affineSpan ℝ ({p} : Set E) := by simpa using hpq.symm
  obtain ⟨f, hf, hqpos⟩ := separate_affine_subspace _ hpA hqA
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image s f ⟨p, hp⟩
  let t := s.filter (fun x ↦ f x = f z)
  let a : E →ᵃ[ℝ] ℝ := f - AffineMap.const ℝ E (f z)
  have hpzero : f p = 0 := hf p hpA
  refine ⟨t, ⟨z, by simp [t, hz]⟩, a, ?_, ?_, p, hp, ?_⟩
  · intro x hx
    change f x - f z ≤ 0
    exact sub_nonpos.mpr (hmax x hx)
  · intro x
    simp only [t, Finset.mem_filter]
    change (x ∈ s ∧ f x = f z) ↔ (x ∈ s ∧ f x - f z = 0)
    simp [sub_eq_zero]
  · change f p - f z < 0
    have := hmax q hq
    linarith

/-- Facet existence is proved by maximization over a finite powerset. -/
theorem exists_facet {s : Finset E} (hs : 1 < s.card) :
    ∃ t, Facet s t := by
  obtain ⟨t, ht⟩ := exists_supported hs
  let B := s.powerset.filter (Supported s)
  have htB : t ∈ B := by simp [B, ht.subset, ht]
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image B Finset.card ⟨t, htB⟩
  have huS : Supported s u := (Finset.mem_filter.mp hu).2
  refine ⟨u, huS, ?_⟩
  intro w hw huw
  have hwB : w ∈ B := by simp [B, hw.subset, hw]
  exact Finset.eq_of_subset_of_card_le huw (hmax w hwB) |>.symm

/-- The missing geometric rigidity input is a theorem: a facet and the centroid
span the parent. Its proof perturbs an exposing affine functional; maximality
rules out a supporting face of larger codimension. -/
theorem Facet.span_with_centroid {s t : Finset E} (H : Facet s t) :
    affineSpan ℝ (insert (s.centroid ℝ id) (t : Set E)) =
      affineSpan ℝ (s : Set E) := by
  rcases H.1 with ⟨ht, f, hbelow, hvertices, hproper⟩
  have hs : s.Nonempty := H.1.parent_nonempty
  let c := s.centroid ℝ id
  let A := affineSpan ℝ (insert c (t : Set E))
  have hcA : c ∈ A := subset_affineSpan ℝ _ (Set.mem_insert _ _)
  have htA : ∀ x ∈ t, x ∈ A := by
    intro x hx
    exact subset_affineSpan ℝ _ (Set.mem_insert_of_mem _ hx)
  have hle : A ≤ affineSpan ℝ (s : Set E) := by
    apply affineSpan_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact centroid_mem_span s hs
    · exact subset_affineSpan ℝ _ (H.1.subset hx)
  apply le_antisymm hle
  apply affineSpan_le.mpr
  intro x hxs
  by_contra hxA
  obtain ⟨q, hqA, hqx⟩ := separate_affine_subspace A hcA hxA
  let B := s.filter (fun z ↦ 0 < q z)
  have hxB : x ∈ B := Finset.mem_filter.mpr ⟨hxs, hqx⟩
  have hfneg : ∀ z ∈ B, f z < 0 := by
    intro z hz
    obtain ⟨hzs, hzq⟩ := Finset.mem_filter.mp hz
    refine lt_of_le_of_ne (hbelow z hzs) ?_
    intro hfz
    have hzt : z ∈ t := (hvertices z).mpr ⟨hzs, hfz⟩
    have := hqA z (htA z hzt)
    linarith
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image B
    (fun z ↦ -f z / q z) ⟨x, hxB⟩
  let a := -f y / q y
  have hyq : 0 < q y := (Finset.mem_filter.mp hy).2
  have hapos : 0 < a := div_pos (neg_pos.mpr (hfneg y hy)) hyq
  let f' : E →ᵃ[ℝ] ℝ := f + a • q
  have hbelow' : ∀ z ∈ s, f' z ≤ 0 := by
    intro z hzs
    change f z + a * q z ≤ 0
    by_cases hzq : 0 < q z
    · have hzB : z ∈ B := by simp [B, hzs, hzq]
      have hl := (le_div_iff₀ hzq).mp (hmin z hzB)
      linarith
    · have hl := mul_nonpos_of_nonneg_of_nonpos hapos.le (le_of_not_gt hzq)
      linarith [hbelow z hzs]
  have hyzero : f' y = 0 := by
    change f y + (-f y / q y) * q y = 0
    field_simp [ne_of_gt hyq]
    ring
  have hcneg : f' c < 0 := by
    have hf := supporting_centroid_strict hs f hbelow hproper
    have hqc := hqA c hcA
    change f c + a * q c < 0
    simpa [hqc, c] using hf
  have hproper' : ∃ z ∈ s, f' z < 0 := by
    by_contra hh
    push Not at hh
    have hz : ∀ z ∈ s, f' z = 0 := by
      intro z hzs
      exact le_antisymm (hbelow' z hzs) (hh z hzs)
    have hcent := affine_centroid_value s hs f'
    have hsum : (∑ z ∈ s, f' z) = 0 := Finset.sum_eq_zero hz
    rw [hsum, mul_zero] at hcent
    have : f' c = 0 := hcent
    linarith
  let u := s.filter (fun z ↦ f' z = 0)
  have hyu : y ∈ u := by simp [u, (Finset.mem_filter.mp hy).1, hyzero]
  have htu : t ⊆ u := by
    intro z hzt
    have hz := (hvertices z).mp hzt
    have hqz := hqA z (htA z hzt)
    simp [u, hz.1, f', hz.2, hqz]
  have hu : Supported s u := by
    refine ⟨⟨y, hyu⟩, f', hbelow', ?_, hproper'⟩
    intro z
    simp [u]
  have hut := H.2 u hu htu
  have hyt : y ∈ t := hut ▸ hyu
  have := hqA y (htA y hyt)
  linarith

/-- For finite polytopes a supporting face of a supporting face is a face.
The affine functionals may be taken in the same ambient affine space. -/
theorem Supported.trans {s t u : Finset E}
    (H : Supported s t) (K : Supported t u) : Supported s u := by
  rcases H with ⟨ht, f, hf, htf, hp⟩
  rcases K with ⟨hu, g, hg, hug, _⟩
  let B := s \ t
  have hneg : ∀ x ∈ B, f x < 0 := by
    intro x hx
    obtain ⟨hxs, hxt⟩ := Finset.mem_sdiff.mp hx
    exact lt_of_le_of_ne (hf x hxs) (by
      intro he
      exact hxt ((htf x).mpr ⟨hxs, he⟩))
  let a := 1 + ∑ x ∈ B, |g x| / (-f x)
  have hterms : ∀ x ∈ B, 0 ≤ |g x| / (-f x) := by
    intro x hx
    exact div_nonneg (abs_nonneg _) (neg_nonneg.mpr (hneg x hx).le)
  have hapos : 0 < a := by
    have := Finset.sum_nonneg hterms
    dsimp [a]
    linarith
  have hout : ∀ x ∈ B, a * f x + g x < 0 := by
    intro x hx
    have hm := Finset.single_le_sum hterms hx
    have hb : |g x| / (-f x) < a := by dsimp [a]; linarith
    have hl := (div_lt_iff₀ (neg_pos.mpr (hneg x hx))).mp hb
    have habs := le_abs_self (g x)
    nlinarith
  let k : E →ᵃ[ℝ] ℝ := a • f + g
  have hbelow : ∀ x ∈ s, k x ≤ 0 := by
    intro x hx
    by_cases hxt : x ∈ t
    · have hfz := ((htf x).mp hxt).2
      simpa [k, hfz] using hg x hxt
    · exact (hout x (Finset.mem_sdiff.mpr ⟨hx, hxt⟩)).le
  refine ⟨hu, k, hbelow, ?_, ?_⟩
  · intro x
    constructor
    · intro hxu
      obtain ⟨hxt, hgz⟩ := (hug x).mp hxu
      obtain ⟨hxs, hfz⟩ := (htf x).mp hxt
      exact ⟨hxs, by simp [k, hfz, hgz]⟩
    · rintro ⟨hxs, hk⟩
      have hxt : x ∈ t := by
        by_contra hxt
        have := hout x (Finset.mem_sdiff.mpr ⟨hxs, hxt⟩)
        change a * f x + g x = 0 at hk
        linarith
      have hfz := ((htf x).mp hxt).2
      have hgz : g x = 0 := by simpa [k, hfz] using hk
      exact (hug x).mpr ⟨hxt, hgz⟩
  · obtain ⟨x, hxs, hfx⟩ := hp
    have hxt : x ∉ t := by
      intro ht'
      have := ((htf x).mp ht').2
      linarith
    exact ⟨x, hxs, hout x (Finset.mem_sdiff.mpr ⟨hxs, hxt⟩)⟩

/-- A concrete complete flag, written from top face down to its vertex.
This is a proposition about a list of vertex subsets, not an affine basis. -/
inductive CompleteChain : List (Finset E) → Prop
  | point (x : E) : CompleteChain [{x}]
  | step {s t : Finset E} {l : List (Finset E)}
      (facet : Facet s t) (tail : CompleteChain (t :: l)) :
      CompleteChain (s :: t :: l)

def FullFlag (s : Finset E) := {l : List (Finset E) // CompleteChain (s :: l)}

theorem CompleteChain.top_nonempty {s : Finset E} {l : List (Finset E)}
    (H : CompleteChain (s :: l)) : s.Nonempty := by
  cases H with
  | point x => simp
  | step h _ => exact h.1.parent_nonempty

/-- All faces in the tail really are supporting faces of the original top
polytope, not only faces in auxiliary coordinate systems. -/
theorem CompleteChain.tail_supported {s : Finset E} {l : List (Finset E)}
    (H : CompleteChain (s :: l)) : ∀ t ∈ l, Supported s t := by
  generalize he : s :: l = L at H
  induction H generalizing s l with
  | point x =>
    cases he
    simp
  | @step s₀ t l₀ h ht ih =>
    cases he
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h.1
    · exact h.1.trans (ih rfl u hu)

/-- There is no infinite-history information in a flag: the number of faces is
bounded by the number of original vertices. -/
theorem CompleteChain.length_le_card {s : Finset E} {l : List (Finset E)}
    (H : CompleteChain (s :: l)) : (s :: l).length ≤ s.card := by
  generalize he : s :: l = L at H
  induction H generalizing s l with
  | point x =>
    cases he
    simp
  | step h ht ih =>
    cases he
    have hi := ih rfl
    have hc := Finset.card_lt_card h.1.ssubset
    simp only [List.length_cons] at *
    omega

/-- Actual flags exist; flag nonemptiness is not postulated in regularity. -/
theorem fullFlag_nonempty (s : Finset E) (hs : s.Nonempty) : Nonempty (FullFlag s) := by
  suffices H : ∀ n (u : Finset E), u.card = n → u.Nonempty → Nonempty (FullFlag u) by
    exact H s.card s rfl hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u hn hu
    by_cases hsingle : u.card = 1
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hsingle
      exact ⟨⟨[], CompleteChain.point x⟩⟩
    · have hbig : 1 < u.card := by have := hu.card_pos; omega
      obtain ⟨t, ht⟩ := exists_facet hbig
      have hsmall : t.card < n := by
        rw [← hn]
        exact Finset.card_lt_card ht.1.ssubset
      obtain ⟨A⟩ := ih t.card hsmall t rfl ht.1.1
      exact ⟨⟨t :: A.1, CompleteChain.step ht A.2⟩⟩

end
end PolytopeCounting.FacetPairing.EuclideanGeometry.GeometricFlags
