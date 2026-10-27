module

public import Mathlib.Tactic

@[expose] public section

/-! # Barycentric sectors in every finite dimension -/

namespace PolytopeCounting.GeneralSimplexStellarSubdivision

/-- A point of the standard closed `d`-simplex in barycentric coordinates. -/
structure Point (d : ℕ) where
  coord : Fin (d + 1) → ℝ
  nonneg : ∀ i, 0 ≤ coord i
  total : (∑ i : Fin (d + 1), coord i) = 1

/-- The `i`-th cone: the barycentre and the original vertices other than `i`.
The coefficient of the omitted original vertex must vanish. -/
def Sector {d : ℕ} (p : Point d) (i : Fin (d + 1)) : Prop :=
  ∃ (t : ℝ) (u : Fin (d + 1) → ℝ),
    0 ≤ t ∧ (∀ j, 0 ≤ u j) ∧ u i = 0 ∧
    t + (∑ j : Fin (d + 1), u j) = 1 ∧
    ∀ j, p.coord j = t / (d + 1 : ℝ) + u j

/-- A cone is exactly a region of minimal `i`-th coordinate. -/
theorem sector_iff_min {d : ℕ} (p : Point d) (i : Fin (d + 1)) :
    Sector p i ↔ ∀ j, p.coord i ≤ p.coord j := by
  constructor
  · rintro ⟨t, u, ht, hu, hi, htotal, hcoord⟩ j
    rw [hcoord i, hcoord j, hi]
    linarith [hu j]
  · intro hmin
    refine ⟨(d + 1 : ℝ) * p.coord i,
      (fun j => p.coord j - p.coord i), ?_, ?_, ?_, ?_, ?_⟩
    · exact mul_nonneg (by positivity) (p.nonneg i)
    · intro j
      exact sub_nonneg.mpr (hmin j)
    · simp
    · have hsum : (∑ j : Fin (d + 1), (p.coord j - p.coord i)) =
          1 - (d + 1 : ℝ) * p.coord i := by
        rw [Finset.sum_sub_distrib, p.total]
        simp [Finset.sum_const, nsmul_eq_mul]
      rw [hsum]
      ring
    · intro j
      dsimp
      have hden : (d + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- Every point lies in at least one of the small simplices. -/
theorem cover {d : ℕ} (p : Point d) :
    ∃ i : Fin (d + 1), Sector p i := by
  classical
  have huniv : (Finset.univ : Finset (Fin (d + 1))).Nonempty := by
    simp
  obtain ⟨i, hi, hmin⟩ :=
    (Finset.univ : Finset (Fin (d + 1))).exists_min_image p.coord huniv
  exact ⟨i, (sector_iff_min p i).2 (fun j => hmin j (by simp))⟩

/-- Two closed sectors intersect precisely where the corresponding
coordinates tie for the minimum. -/
theorem overlap {d : ℕ} (p : Point d) (i j : Fin (d + 1)) :
    Sector p i ∧ Sector p j ↔
      p.coord i = p.coord j ∧ ∀ k, p.coord i ≤ p.coord k := by
  rw [sector_iff_min p i, sector_iff_min p j]
  constructor
  · rintro ⟨hi, hj⟩
    exact ⟨le_antisymm (hi j) (hj i), hi⟩
  · rintro ⟨hij, hi⟩
    exact ⟨hi, fun k => by simpa [← hij] using hi k⟩

/-- Every original facet `x_i=0` belongs to its corresponding cone.
This is the local relative-boundary compatibility statement. -/
theorem original_facet {d : ℕ} (p : Point d) (i : Fin (d + 1))
    (hi : p.coord i = 0) : Sector p i := by
  apply (sector_iff_min p i).2
  intro j
  simpa [hi] using p.nonneg j

end PolytopeCounting.GeneralSimplexStellarSubdivision
