module

public import Mathlib.Tactic

@[expose] public section

/-! # Finite cardinality bounds for forgetting marked vertices -/

namespace PolytopeCounting.UnmarkingBound

/-- There are at most `|New| ^ |Old|` injections from the vertices of a
fixed initial complex into the vertices of a resulting complex. -/
theorem embeddings_le_functions (Old New : Type*)
    [Fintype Old] [Fintype New] :
    Fintype.card (Old ↪ New) ≤ Fintype.card New ^ Fintype.card Old := by
  classical
  calc
    Fintype.card (Old ↪ New) ≤ Fintype.card (Old → New) := by
      apply Fintype.card_le_of_injective
        (fun e : Old ↪ New => (e : Old → New))
      intro e f hef
      ext x
      exact congrFun hef x
    _ = Fintype.card New ^ Fintype.card Old := by
      exact Fintype.card_fun

/-- A jointly injective assignment of an unmarked output and an embedding
of the old vertices yields the polynomial unmarking bound. Concrete rigidity
for stellar subdivisions is proved in `IntrinsicCorollary53`. -/
theorem binary_classes_bound
    (k : ℕ) (Output Original Vertex : Type*)
    [Fintype Output] [Fintype Original] [Fintype Vertex]
    (result : (Fin k → Bool) → Output)
    (mark : (Fin k → Bool) → (Original ↪ Vertex))
    (joint_injective : Function.Injective (fun w => (result w, mark w))) :
    2 ^ k ≤ Fintype.card Output *
      (Fintype.card Vertex ^ Fintype.card Original) := by
  classical
  have hcount : Fintype.card (Fin k → Bool) ≤
      Fintype.card (Output × (Original ↪ Vertex)) :=
    Fintype.card_le_of_injective
      (fun w : Fin k → Bool => (result w, mark w)) joint_injective
  calc
    2 ^ k = Fintype.card (Fin k → Bool) := by simp
    _ ≤ Fintype.card (Output × (Original ↪ Vertex)) := hcount
    _ = Fintype.card Output * Fintype.card (Original ↪ Vertex) := by simp
    _ ≤ Fintype.card Output *
        (Fintype.card Vertex ^ Fintype.card Original) :=
      Nat.mul_le_mul_left _ (embeddings_le_functions Original Vertex)

end PolytopeCounting.UnmarkingBound
