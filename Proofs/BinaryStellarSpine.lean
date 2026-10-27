module

public import Mathlib.Tactic

@[expose] public section

/-! # Binary stellar subdivisions and injective active-face traces -/

namespace PolytopeCounting.BinaryStellarSpine

structure State where
  vertices : Finset ℕ
  first : ℕ
  second : ℕ
  nextFresh : ℕ
  first_mem : first ∈ vertices
  second_mem : second ∈ vertices
  distinct : first ≠ second
  fresh : ∀ x ∈ vertices, x < nextFresh

lemma next_not_mem (s : State) : s.nextFresh ∉ s.vertices := by
  intro h
  exact Nat.lt_irrefl _ (s.fresh s.nextFresh h)

lemma next_ne_first (s : State) : s.nextFresh ≠ s.first := by
  intro h
  apply next_not_mem s
  rw [h]
  exact s.first_mem

lemma next_ne_second (s : State) : s.nextFresh ≠ s.second := by
  intro h
  apply next_not_mem s
  rw [h]
  exact s.second_mem

/-- `false`: replace the first vertex; `true`: replace the second. -/
def child (s : State) (b : Bool) : Finset ℕ :=
  insert s.nextFresh (s.vertices.erase (if b then s.second else s.first))

lemma first_not_mem_false (s : State) : s.first ∉ child s false := by
  have hfresh : s.first ≠ s.nextFresh := (next_ne_first s).symm
  simp [child, hfresh]

lemma first_mem_true (s : State) : s.first ∈ child s true := by
  simp [child, s.first_mem, s.distinct]

/-- The two choices really have different *unordered* child vertex sets. -/
theorem child_false_ne_true (s : State) : child s false ≠ child s true := by
  intro h
  have hx : s.first ∈ child s true := first_mem_true s
  rw [← h] at hx
  exact first_not_mem_false s hx

theorem fresh_after (s : State) (omitted : ℕ) :
    ∀ x ∈ insert s.nextFresh (s.vertices.erase omitted), x < s.nextFresh + 1 := by
  intro x hx
  rcases Finset.mem_insert.mp hx with hnew | hold
  · subst x
    exact Nat.lt_succ_self _
  · exact Nat.lt_trans (s.fresh x (Finset.mem_erase.mp hold).2)
      (Nat.lt_succ_self _)

/-- Update the active face and the two distinguished positions.
The fresh index increases, so all hypotheses remain true. -/
def advance (s : State) : Bool → State
  | false =>
      { vertices := insert s.nextFresh (s.vertices.erase s.first)
        first := s.nextFresh
        second := s.second
        nextFresh := s.nextFresh + 1
        first_mem := by simp
        second_mem := by simp [s.second_mem, s.distinct.symm]
        distinct := next_ne_second s
        fresh := fresh_after s s.first }
  | true =>
      { vertices := insert s.nextFresh (s.vertices.erase s.second)
        first := s.first
        second := s.nextFresh
        nextFresh := s.nextFresh + 1
        first_mem := by simp [s.first_mem, s.distinct]
        second_mem := by simp
        distinct := (next_ne_first s).symm
        fresh := fresh_after s s.second }

@[simp] theorem advance_nextFresh (s : State) (b : Bool) :
    (advance s b).nextFresh = s.nextFresh + 1 := by cases b <;> rfl

@[simp] theorem advance_vertices (s : State) (b : Bool) :
    (advance s b).vertices = child s b := by cases b <;> rfl

/-- Record every chosen active vertex set as an unordered finite set. -/
def trace (s : State) : List Bool → List (Finset ℕ)
  | [] => []
  | b :: bs => child s b :: trace (advance s b) bs

/-- This complete chronological neighbourhood trace determines the binary
word. No marked-graph reconstruction hypothesis is used. -/
theorem trace_injective (s : State) : Function.Injective (trace s) := by
  intro xs
  induction xs generalizing s with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons b bs => cases h
  | cons b bs ih =>
      intro ys h
      cases ys with
      | nil => cases h
      | cons c cs =>
          have hhead : child s b = child s c := (List.cons.inj h).1
          have hbc : b = c := by
            cases b <;> cases c
            · rfl
            · exact False.elim (child_false_ne_true s hhead)
            · exact False.elim (child_false_ne_true s hhead.symm)
            · rfl
          subst c
          have htail : trace (advance s b) bs = trace (advance s b) cs :=
            (List.cons.inj h).2
          have hrest : bs = cs := ih (advance s b) htail
          simp [hrest]

/-- Initially every vertex in the active simplex precedes the first new
vertex; positions 0 and 1 are available when `d ≥ 1`. -/
def initial (d : ℕ) (hd : 1 ≤ d) : State where
  vertices := Finset.range (d + 1)
  first := 0
  second := 1
  nextFresh := d + 1
  first_mem := Finset.mem_range.mpr (by omega)
  second_mem := Finset.mem_range.mpr (by omega)
  distinct := by decide
  fresh := by
    intro x hx
    exact Finset.mem_range.mp hx

/-- Binary words inject into active-facet traces. Recovery from the final
graph, without insertion-order labels, is proved in `IntrinsicGraphRecovery`. -/
theorem binary_trace_injective (d : ℕ) (hd : 1 ≤ d) :
    Function.Injective (trace (initial d hd)) :=
  trace_injective (initial d hd)

end PolytopeCounting.BinaryStellarSpine
