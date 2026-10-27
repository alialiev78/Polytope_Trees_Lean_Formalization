module

public import Proofs.IntrinsicFacetRestriction
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

/-!
# Orientation reversal derived from Euclidean flag regularity

The negative symmetry needed by the old `System` is not assumed. Induct on
proper facet vertex sets. A singleton facet forces a one-dimensional parent;
a symmetry moving that endpoint is the reflection about the fixed centroid.
For a larger facet, extend its already constructed negative involution and
use determinant compatibility. Applying the result inside any facet of a
cell of dimension at least two yields a negative facet stabilizer.

-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry.GeometricFlags
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

section Elementary
variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]
variable {s t : Finset P}

/-- Maximization among faces containing an already exposed face. -/
theorem Supported.exists_superfacet (H : Supported s t) :
    ∃ u, Facet s u ∧ t ⊆ u := by
  let B := s.powerset.filter (fun u ↦ Supported s u ∧ t ⊆ u)
  have ht : t ∈ B := by simp [B, H.subset, H]
  obtain ⟨u, hu, hm⟩ := Finset.exists_max_image B Finset.card ⟨t, ht⟩
  have hu' := (Finset.mem_filter.mp hu).2
  refine ⟨u, ⟨hu'.1, ?_⟩, hu'.2⟩
  intro w hw huw
  have hwB : w ∈ B := by simp [B, hw.subset, hw, hu'.2.trans huw]
  exact (Finset.eq_of_subset_of_card_le huw (hm w hwB)).symm

/-- A bounded positive-dimensional polytope has a facet different from any
prescribed one. The opposite exposing functional produces the witness. -/
theorem Facet.exists_other (H : Facet s t) : ∃ u, Facet s u ∧ u ≠ t := by
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image s H.form H.1.parent_nonempty
  obtain ⟨z, hz, hzneg⟩ := H.form_proper
  have hxneg : H.form x < 0 := lt_of_le_of_lt (hmin z hz) hzneg
  let u := s.filter (fun y ↦ H.form y = H.form x)
  let f : P →ᵃ[ℝ] ℝ := AffineMap.const ℝ P (H.form x) - H.form
  have hxu : x ∈ u := by simp [u, hx]
  have hu : Supported s u := by
    refine ⟨⟨x, hxu⟩, f, ?_, ?_, ?_⟩
    · intro y hy
      change H.form x - H.form y ≤ 0
      exact sub_nonpos.mpr (hmin y hy)
    · intro y
      simp only [u, Finset.mem_filter]
      change (y ∈ s ∧ H.form y = H.form x) ↔
        (y ∈ s ∧ H.form x - H.form y = 0)
      rw [sub_eq_zero]
      exact and_congr_right (fun _ ↦ eq_comm)
    · obtain ⟨p, hp⟩ := H.1.1
      refine ⟨p, H.1.subset hp, ?_⟩
      change H.form x - H.form p < 0
      rw [((H.form_vertices p).mp hp).2, sub_zero]
      exact hxneg
  obtain ⟨w, hw, huw⟩ := hu.exists_superfacet
  refine ⟨w, hw, ?_⟩
  intro he
  have hxt : x ∈ t := he ▸ huw hxu
  have := ((H.form_vertices x).mp hxt).2
  linarith

theorem singleton_direction (p : P) :
    (affineSpan ℝ ({p} : Set P)).direction = ⊥ := by
  apply le_antisymm _ bot_le
  intro w hw
  have hp : p ∈ affineSpan ℝ ({p} : Set P) := subset_affineSpan ℝ _ (by simp)
  have hy := (affineSpan ℝ ({p} : Set P)).vadd_mem_of_mem_direction hw hp
  have he : w +ᵥ p = p := by simpa using hy
  change w = 0
  simpa using congrArg (fun x : P ↦ x -ᵥ p) he

theorem nontrivial_vertex_set [FiniteDimensional ℝ V]
    (hs : s.Nonempty) (span : affineSpan ℝ (s : Set P) = ⊤)
    (hd : 0 < Module.finrank ℝ V) : 1 < s.card := by
  by_contra h
  have hcard : s.card = 1 := by have := hs.card_pos; omega
  obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hcard
  rw [Finset.coe_singleton] at span
  have hp : ∀ x : P, x = p := by
    intro x
    have hx : x ∈ affineSpan ℝ ({p} : Set P) := by rw [span]; trivial
    simpa using hx
  have hv : ∀ w : V, w = 0 := by
    intro w
    simpa using congrArg (fun x : P ↦ x -ᵥ p) (hp (w +ᵥ p))
  letI : Subsingleton V := ⟨fun a b ↦ (hv a).trans (hv b).symm⟩
  have hz : Module.finrank ℝ V = 0 := Module.finrank_zero_of_subsingleton
  omega

/-- Facets in ambient dimension at least two are not zero-dimensional. -/
theorem Facet.card_gt_one [FiniteDimensional ℝ V] (H : Facet s t)
    (span : affineSpan ℝ (s : Set P) = ⊤)
    (hd : 2 ≤ Module.finrank ℝ V) : 1 < t.card := by
  by_contra h
  have hc : t.card = 1 := by have := H.1.1.card_pos; omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  have hdim := H.direction_finrank span
  have hz : Module.finrank ℝ (affineSpan ℝ (t : Set P)).direction = 0 :=
    Submodule.finrank_eq_zero.mpr (by rw [hp, Finset.coe_singleton, singleton_direction])
  rw [hz] at hdim
  omega

/-- In the rank-one base case an endpoint-moving symmetry is exactly the
negative linear map around the common fixed centroid. -/
theorem singleton_facet_reflection [FiniteDimensional ℝ V] {p : P}
    (H : Facet s {p}) (span : affineSpan ℝ (s : Set P) = ⊤)
    (g : symmetryGroup s) (hmove : g.1 p ≠ p) :
    euclideanOrientation s g = -1 ∧ g * g = 1 := by
  let c := s.centroid ℝ id
  let v : V := p -ᵥ c
  let f := H.form.linear
  have hcfix : g.1 c = c := centroid_fixed s H.1.parent_nonempty g
  have hpzero : H.form p = 0 := ((H.form_vertices p).mp (by simp)).2
  have hfv : f v ≠ 0 := by
    change H.form.linear (p -ᵥ c) ≠ 0
    rw [H.form.linearMap_vsub, hpzero, vsub_eq_sub, zero_sub]
    exact neg_ne_zero.mpr (ne_of_lt H.form_centroid_neg)
  have hv : v ≠ 0 := by intro hh; exact hfv (by simp [hh, f])
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    ext w
    change f w = 0 ↔ w = 0
    rw [← H.direction_iff span, Finset.coe_singleton, singleton_direction]
    rfl
  have coord : ∀ w : V, w = (f w / f v) • v := by
    intro w
    apply hf
    simp [map_smul, smul_eq_mul, hfv]
  let a := f (g.1.linear v) / f v
  have hLv : g.1.linear v = a • v := coord _
  have habs : |a| = 1 := by
    have hn : |a| * ‖v‖ = 1 * ‖v‖ := by
      calc
        |a| * ‖v‖ = ‖a • v‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = ‖g.1.linear v‖ := congrArg norm hLv.symm
        _ = 1 * ‖v‖ := by simp
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hv) hn
  have haone : a ≠ 1 := by
    intro ha
    have hfix : g.1.linear v = v := by simpa [ha] using hLv
    apply hmove
    calc
      g.1 p = g.1 (v +ᵥ c) := by simp [v]
      _ = g.1.linear v +ᵥ g.1 c := g.1.toAffineMap.map_vadd c v
      _ = p := by rw [hfix, hcfix]; simp [v]
  have ha : a = -1 := by
    by_cases hneg : a < 0
    · rw [abs_of_neg hneg] at habs
      linarith
    · rw [abs_of_nonneg (le_of_not_gt hneg)] at habs
      exact (haone habs).elim
  have hlinear : g.1.toAffineMap.linear = (-1 : ℝ) • LinearMap.id := by
    ext w
    rw [coord w, map_smul]
    change (f w / f v) • g.1.linear v = (-1 : ℝ) • ((f w / f v) • v)
    rw [hLv, ha]
    simp [smul_smul, mul_comm]
  have hdim : Module.finrank ℝ V = 1 := by
    have hh := H.direction_finrank span
    have hz : Module.finrank ℝ (affineSpan ℝ (({p} : Finset P) : Set P)).direction = 0 :=
      Submodule.finrank_eq_zero.mpr (by rw [Finset.coe_singleton, singleton_direction])
    omega
  have hdet : LinearMap.det g.1.toAffineMap.linear = -1 := by
    rw [hlinear, LinearMap.det_smul, LinearMap.det_id, hdim]
    simp
  refine ⟨?_, ?_⟩
  · change realUnitSign (LinearEquiv.det g.1.linear) = -1
    have hd' : (LinearEquiv.det g.1.linear : ℝ) = -1 := by
      rw [LinearEquiv.coe_det]
      convert hdet using 1 <;> rfl
    simp only [realUnitSign, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [hd']
    norm_num
  · have hx : ∀ x : P, g.1 x -ᵥ c = -(x -ᵥ c) := by
      intro x
      calc
        g.1 x -ᵥ c = g.1 x -ᵥ g.1 c := by rw [hcfix]
        _ = g.1.toAffineMap.linear (x -ᵥ c) :=
          (g.1.toAffineMap.linearMap_vsub x c).symm
        _ = -(x -ᵥ c) := by rw [hlinear]; simp
    apply Subtype.ext
    ext x
    have he : g.1 (g.1 x) -ᵥ c = x -ᵥ c := by rw [hx, hx, neg_neg]
    simpa using congrArg (fun w : V ↦ w +ᵥ c) he

end Elementary

universe u

/-- Every nontrivial geometrically flag-regular finite polytope has an actual
orientation-reversing involution. The recursion takes place in intrinsic face
spaces and terminates because each supporting facet has fewer vertices. -/
theorem exists_negative_involution
    {V P : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
    (s : Finset P) (span : affineSpan ℝ (s : Set P) = ⊤)
    (regular : IsFlagRegular s) (big : 1 < s.card) :
    ∃ g : symmetryGroup s, euclideanOrientation s g = -1 ∧ g * g = 1 := by
  have aux : ∀ n, ∀ (W Q : Type u) [NormedAddCommGroup W] [NormedSpace ℝ W]
      [MetricSpace Q] [NormedAddTorsor W Q] [FiniteDimensional ℝ W]
      (a : Finset Q), a.card = n → affineSpan ℝ (a : Set Q) = ⊤ →
      IsFlagRegular a → 1 < a.card →
      ∃ g : symmetryGroup a, euclideanOrientation a g = -1 ∧ g * g = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W Q _ _ _ _ _ a hn ha hreg hbig
      obtain ⟨t, H⟩ := exists_facet hbig
      by_cases ht : t.card = 1
      · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp ht
        obtain ⟨u, U, hune⟩ := H.exists_other
        obtain ⟨B⟩ := fullFlag_nonempty u U.1.1
        let A : FullFlag a := ⟨[{p}], CompleteChain.step H (CompleteChain.point p)⟩
        let B' : FullFlag a := ⟨u :: B.1, CompleteChain.step U B.2⟩
        obtain ⟨g, hg⟩ := hreg A B'
        have him : ({p} : Finset Q).image g.1 = u :=
          (List.cons.inj (List.cons.inj hg).2).1
        have hmove : g.1 p ≠ p := by
          intro hp
          have hu : u = {p} := by simpa [hp] using him.symm
          exact hune hu
        exact ⟨g, singleton_facet_reflection H ha g hmove⟩
      · letI := H.span_nonempty
        let T := affineSpan ℝ (t : Set Q)
        let W' := T.direction
        have hsmall : t.card < n := by rw [← hn]; exact Finset.card_lt_card H.1.ssubset
        have hcard : (spanVertices t).card = t.card := H.intrinsic_card
        have hbig' : 1 < (spanVertices t).card := by
          rw [hcard]
          have := H.1.1.card_pos
          omega
        obtain ⟨b, hb, hbb⟩ := ih t.card hsmall W' T (spanVertices t)
          hcard (spanVertices_span t) (H.intrinsic_regular hreg) hbig'
        let e := H.restrictionEquiv ha hreg
        let g : cellFacetStabilizer a t := e.symm b
        have hg : facetRestriction a t g = b := e.apply_symm_apply b
        have hsign : euclideanOrientation a g.1 = -1 := by
          rw [← H.restriction_orientation ha g, hg, hb]
        have hgg : g * g = 1 := by
          apply e.injective
          simp only [map_mul, map_one]
          change facetRestriction a t g * facetRestriction a t g = 1
          rw [hg, hbb]
        exact ⟨g.1, hsign, congrArg Subtype.val hgg⟩
  exact aux s.card V P s rfl span regular big

/-- The reflection required in a signed facet system is derived, for every
facet. Ambient dimension at least two is essential: a point facet has no
negative intrinsic symmetry. -/
theorem Facet.exists_negative_stabilizer
    {V P : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
    {s t : Finset P} (H : Facet s t)
    (span : affineSpan ℝ (s : Set P) = ⊤)
    (regular : IsFlagRegular s) (hd : 2 ≤ Module.finrank ℝ V) :
    ∃ g : cellFacetStabilizer s t,
      euclideanOrientation s g.1 = -1 ∧ g * g = 1 := by
  letI := H.span_nonempty
  have hbig : 1 < (spanVertices t).card := by
    rw [H.intrinsic_card]
    exact H.card_gt_one span hd
  obtain ⟨b, hb, hbb⟩ := exists_negative_involution (spanVertices t)
    (spanVertices_span t) (H.intrinsic_regular regular) hbig
  let e := H.restrictionEquiv span regular
  let g : cellFacetStabilizer s t := e.symm b
  have hg : facetRestriction s t g = b := e.apply_symm_apply b
  refine ⟨g, ?_, ?_⟩
  · rw [← H.restriction_orientation span g, hg, hb]
  · apply e.injective
    simp only [map_mul, map_one]
    change facetRestriction s t g * facetRestriction s t g = 1
    rw [hg, hbb]

end
end PolytopeCounting.FacetPairing.EuclideanGeometry.GeometricFlags
