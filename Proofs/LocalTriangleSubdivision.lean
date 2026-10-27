module

import Mathlib.Tactic

/-! # Barycentric subdivision of a triangle -/

namespace PolytopeCounting.LocalTriangleSubdivision

/-- Barycentric coordinates of a point in the standard closed triangle. -/
structure Point where
  a : ℝ
  b : ℝ
  c : ℝ
  a_nonneg : 0 ≤ a
  b_nonneg : 0 ≤ b
  c_nonneg : 0 ≤ c
  total : a + b + c = 1

/-- A point belongs to the small triangle opposite vertex `a` if it
admits barycentric coefficients relative to the barycentre and the other two
vertices. -/
def SectorA (p : Point) : Prop :=
  ∃ t u v : ℝ, 0 ≤ t ∧ 0 ≤ u ∧ 0 ≤ v ∧ t + u + v = 1 ∧
    p.a = t / 3 ∧ p.b = t / 3 + u ∧ p.c = t / 3 + v

def SectorB (p : Point) : Prop :=
  ∃ t u v : ℝ, 0 ≤ t ∧ 0 ≤ u ∧ 0 ≤ v ∧ t + u + v = 1 ∧
    p.a = t / 3 + u ∧ p.b = t / 3 ∧ p.c = t / 3 + v

def SectorC (p : Point) : Prop :=
  ∃ t u v : ℝ, 0 ≤ t ∧ 0 ≤ u ∧ 0 ≤ v ∧ t + u + v = 1 ∧
    p.a = t / 3 + u ∧ p.b = t / 3 + v ∧ p.c = t / 3

/-- Characterize the first closed subtriangle by a minimal coordinate. -/
theorem sectorA_iff (p : Point) :
    SectorA p ↔ p.a ≤ p.b ∧ p.a ≤ p.c := by
  constructor
  · rintro ⟨t, u, v, ht, hu, hv, hs, ha, hb, hc⟩
    constructor <;> linarith
  · rintro ⟨hab, hac⟩
    refine ⟨3 * p.a, p.b - p.a, p.c - p.a, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals linarith [p.a_nonneg, p.total]

theorem sectorB_iff (p : Point) :
    SectorB p ↔ p.b ≤ p.a ∧ p.b ≤ p.c := by
  constructor
  · rintro ⟨t, u, v, ht, hu, hv, hs, ha, hb, hc⟩
    constructor <;> linarith
  · rintro ⟨hba, hbc⟩
    refine ⟨3 * p.b, p.a - p.b, p.c - p.b, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals linarith [p.b_nonneg, p.total]

theorem sectorC_iff (p : Point) :
    SectorC p ↔ p.c ≤ p.a ∧ p.c ≤ p.b := by
  constructor
  · rintro ⟨t, u, v, ht, hu, hv, hs, ha, hb, hc⟩
    constructor <;> linarith
  · rintro ⟨hca, hcb⟩
    refine ⟨3 * p.c, p.a - p.c, p.b - p.c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals linarith [p.c_nonneg, p.total]

/-- The three explicitly parametrised triangles cover the original triangle. -/
theorem cover (p : Point) : SectorA p ∨ SectorB p ∨ SectorC p := by
  rcases le_total p.a p.b with hab | hba
  · rcases le_total p.a p.c with hac | hca
    · exact Or.inl ((sectorA_iff p).2 ⟨hab, hac⟩)
    · exact Or.inr (Or.inr ((sectorC_iff p).2 ⟨hca, le_trans hca hab⟩))
  · rcases le_total p.b p.c with hbc | hcb
    · exact Or.inr (Or.inl ((sectorB_iff p).2 ⟨hba, hbc⟩))
    · exact Or.inr (Or.inr ((sectorC_iff p).2 ⟨le_trans hcb hba, hcb⟩))

/-- The common edge of the first two closed sectors is exactly `a=b≤c`. -/
theorem overlapAB (p : Point) :
    SectorA p ∧ SectorB p ↔ p.a = p.b ∧ p.a ≤ p.c := by
  rw [sectorA_iff, sectorB_iff]
  constructor
  · rintro ⟨⟨hab, hac⟩, ⟨hba, hbc⟩⟩
    exact ⟨le_antisymm hab hba, hac⟩
  · rintro ⟨heq, hac⟩
    exact ⟨⟨le_of_eq heq, hac⟩, ⟨le_of_eq heq.symm, heq ▸ hac⟩⟩

theorem overlapAC (p : Point) :
    SectorA p ∧ SectorC p ↔ p.a = p.c ∧ p.a ≤ p.b := by
  rw [sectorA_iff, sectorC_iff]
  constructor
  · rintro ⟨⟨hab, hac⟩, ⟨hca, hcb⟩⟩
    exact ⟨le_antisymm hac hca, hab⟩
  · rintro ⟨heq, hab⟩
    exact ⟨⟨hab, le_of_eq heq⟩, ⟨le_of_eq heq.symm, heq ▸ hab⟩⟩

theorem overlapBC (p : Point) :
    SectorB p ∧ SectorC p ↔ p.b = p.c ∧ p.b ≤ p.a := by
  rw [sectorB_iff, sectorC_iff]
  constructor
  · rintro ⟨⟨hba, hbc⟩, ⟨hca, hcb⟩⟩
    exact ⟨le_antisymm hbc hcb, hba⟩
  · rintro ⟨heq, hba⟩
    exact ⟨⟨hba, le_of_eq heq⟩, ⟨heq ▸ hba, le_of_eq heq.symm⟩⟩

/-- Every point on an original boundary edge is retained in the local
subdivision.  No boundary point is collapsed or removed. -/
theorem originalEdgeA (p : Point) (ha : p.a = 0) : SectorA p := by
  apply (sectorA_iff p).2
  constructor <;> linarith [p.b_nonneg, p.c_nonneg]

theorem originalEdgeB (p : Point) (hb : p.b = 0) : SectorB p := by
  apply (sectorB_iff p).2
  constructor <;> linarith [p.a_nonneg, p.c_nonneg]

theorem originalEdgeC (p : Point) (hc : p.c = 0) : SectorC p := by
  apply (sectorC_iff p).2
  constructor <;> linarith [p.a_nonneg, p.b_nonneg]

end PolytopeCounting.LocalTriangleSubdivision
