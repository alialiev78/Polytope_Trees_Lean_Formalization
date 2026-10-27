module

public import Proofs.BinaryStellarSpine

@[expose] public section

/-! # Persistence of omitted vertices under stellar subdivisions -/

namespace PolytopeCounting.BinaryStellarSpine

/-- The vertex that the chosen child omits. -/
def omitted (s : State) (b : Bool) : ℕ :=
  if b then s.second else s.first

lemma omitted_lt_fresh (s : State) (b : Bool) :
    omitted s b < s.nextFresh := by
  cases b with
  | false => exact s.fresh s.first s.first_mem
  | true => exact s.fresh s.second s.second_mem

lemma omitted_not_child (s : State) (b : Bool) :
    omitted s b ∉ child s b := by
  cases b with
  | false =>
      have h : s.first ≠ s.nextFresh := (next_ne_first s).symm
      simp [omitted, child, h]
  | true =>
      have h : s.second ≠ s.nextFresh := (next_ne_second s).symm
      simp [omitted, child, h]

lemma omitted_not_next_state (s : State) (b : Bool) :
    omitted s b ∉ (advance s b).vertices := by
  cases b with
  | false => exact omitted_not_child s false
  | true => exact omitted_not_child s true

/-- An already absent old vertex is not reintroduced by another insertion. -/
theorem absence_step (s : State) (x : ℕ) (b : Bool)
    (hnot : x ∉ s.vertices) (hbound : x < s.nextFresh) :
    x ∉ (advance s b).vertices := by
  have hfresh : x ≠ s.nextFresh := Nat.ne_of_lt hbound
  cases b with
  | false =>
      simp only [advance, Finset.mem_insert, Finset.mem_erase]
      rintro (heq | hrest)
      · exact hfresh heq
      · exact hnot hrest.2
  | true =>
      simp only [advance, Finset.mem_insert, Finset.mem_erase]
      rintro (heq | hrest)
      · exact hfresh heq
      · exact hnot hrest.2

/-- Absence is invariant under *any* further finite sequence of binary
insertions, because new vertex indices are strictly increasing. -/
theorem absence_all :
    ∀ (bits : List Bool) (s : State) (x : ℕ),
      x ∉ s.vertices → x < s.nextFresh →
      x ∉ (bits.foldl advance s).vertices
  | [], s, _, hnot, _ => hnot
  | b :: bs, s, x, hnot, hbound => by
      apply absence_all bs (advance s b) x
      · exact absence_step s x b hnot hbound
      · rw [advance_nextFresh]
        omega

/-- After a choice, its omitted vertex is absent from every later
active face, independently of all subsequent choices. -/
theorem omitted_forever (s : State) (b : Bool) (later : List Bool) :
    omitted s b ∉ (later.foldl advance (advance s b)).vertices := by
  apply absence_all later (advance s b) (omitted s b)
  · exact omitted_not_next_state s b
  · rw [advance_nextFresh]
    have h := omitted_lt_fresh s b
    omega

end PolytopeCounting.BinaryStellarSpine
