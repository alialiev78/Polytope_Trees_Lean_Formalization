module

public import Proofs.PermanentOmission

@[expose] public section

/-! # Recovery of stellar choices from the final graph -/

namespace PolytopeCounting.BinaryStellarSpine

theorem omitted_mem (s : State) (b : Bool) : omitted s b ∈ s.vertices := by
  cases b
  · exact s.first_mem
  · exact s.second_mem

def starEdge (s : State) (x y : ℕ) : Prop :=
  (x = s.nextFresh ∧ y ∈ s.vertices) ∨
  (y = s.nextFresh ∧ x ∈ s.vertices)

/-- A list of length k specifies k+1 insertions, including the last insertion
whose child is not subsequently chosen. -/
def newEdge (s : State) : List Bool → ℕ → ℕ → Prop
  | [], x, y => starEdge s x y
  | b :: bs, x, y => starEdge s x y ∨ newEdge (advance s b) bs x y

theorem root_adjacent (s : State) (bs : List Bool) {a : ℕ}
    (ha : a ∈ s.vertices) : newEdge s bs s.nextFresh a := by
  cases bs with
  | nil => exact Or.inl ⟨rfl, ha⟩
  | cons b bs => exact Or.inl (Or.inl ⟨rfl, ha⟩)

theorem newEdge_has_new (s : State) (bs : List Bool) {x y : ℕ}
    (h : newEdge s bs x y) : s.nextFresh ≤ x ∨ s.nextFresh ≤ y := by
  induction bs generalizing s with
  | nil => rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  | cons b bs ih =>
      rcases h with h | h
      · rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
      · have ht := ih (advance s b) h
        simp only [advance_nextFresh] at ht
        omega

/-- An old vertex absent from the active face receives no edge at any of the
remaining insertions. This statement is about the actual final edge relation. -/
theorem newEdge_absent_old (s : State) (bs : List Bool) {a : ℕ}
    (ha : a < s.nextFresh) (hnot : a ∉ s.vertices) (x : ℕ) :
    ¬newEdge s bs x a := by
  induction bs generalizing s with
  | nil =>
      rintro (⟨_, hm⟩ | ⟨he, _⟩)
      · exact hnot hm
      · omega
  | cons b bs ih =>
      rintro (h | h)
      · rcases h with ⟨_, hm⟩ | ⟨he, _⟩
        · exact hnot hm
        · omega
      · apply ih (advance s b) (by simpa using Nat.lt_succ_of_lt ha)
          (absence_step s a b hnot ha) h

/-- Characterization entirely in terms of adjacency and the original active
face. No insertion-time labels are supplied to the reconstructed vertex. -/
theorem root_characterization (s : State) (bs : List Bool) (x : ℕ)
    (hx : s.nextFresh ≤ x) :
    (∀ a ∈ s.vertices, newEdge s bs x a) ↔ x = s.nextFresh := by
  constructor
  · intro h
    cases bs with
    | nil =>
        have he := h s.first s.first_mem
        rcases he with ⟨he, _⟩ | ⟨he, _⟩
        · exact he
        · have hlt := s.fresh s.first s.first_mem
          omega
    | cons b bs =>
        have he := h (omitted s b) (omitted_mem s b)
        have hn : ¬newEdge (advance s b) bs x (omitted s b) :=
          newEdge_absent_old (advance s b) bs
            (by simpa using Nat.lt_succ_of_lt (omitted_lt_fresh s b))
            (omitted_not_next_state s b) x
        rcases he.resolve_right hn with ⟨he, _⟩ | ⟨he, _⟩
        · exact he
        · have hlt := omitted_lt_fresh s b
          omega
  · rintro rfl a ha
    exact root_adjacent s bs ha

/-- Remove the edges created at the first insertion by retaining edges with
an endpoint outside the now enlarged original-vertex set. -/
theorem tail_edge_iff (s : State) (b : Bool) (bs : List Bool) (x y : ℕ) :
    newEdge (advance s b) bs x y ↔
      newEdge s (b :: bs) x y ∧
        (s.nextFresh + 1 ≤ x ∨ s.nextFresh + 1 ≤ y) := by
  constructor
  · intro h
    exact ⟨Or.inr h, by simpa using newEdge_has_new (advance s b) bs h⟩
  · rintro ⟨hs | ht, hlarge⟩
    · rcases hs with ⟨rfl, hy⟩ | ⟨rfl, hx⟩
      · have hlt := s.fresh y hy
        omega
      · have hlt := s.fresh x hx
        omega
    · exact ht

/-- A permutation fixing a finite initial segment preserves its complement. -/
theorem fixed_prefix_threshold (e : Equiv.Perm ℕ) (p : ℕ)
    (hfix : ∀ x < p, e x = x) (x : ℕ) :
    p ≤ e x ↔ p ≤ x := by
  constructor
  · intro h
    by_contra hx
    have hxp : x < p := by omega
    rw [hfix x hxp] at h
    omega
  · intro h
    by_contra hx
    have hxp : e x < p := by omega
    have he : e x = x := e.injective (hfix (e x) hxp)
    omega

theorem omitted_other_mem (s : State) (b c : Bool) (hbc : b ≠ c) :
    omitted s c ∈ (advance s b).vertices := by
  cases b <;> cases c <;>
    simp_all [advance, omitted, s.first_mem, s.second_mem, s.distinct,
      s.distinct.symm, (next_ne_first s).symm, (next_ne_second s).symm]

theorem no_future_edge_to_omitted (s : State) (c : Bool) (cs : List Bool)
    (x : ℕ) (hx : s.nextFresh + 1 ≤ x) :
    ¬newEdge s (c :: cs) x (omitted s c) := by
  rintro (h | h)
  · rcases h with ⟨he, _⟩ | ⟨he, _⟩
    · omega
    · have ht := omitted_lt_fresh s c
      omega
  · exact newEdge_absent_old (advance s c) cs
      (by simpa using Nat.lt_succ_of_lt (omitted_lt_fresh s c))
      (omitted_not_next_state s c) x h

/-- The complete final graph determines the choices up to arbitrary
permutation of all inserted vertices, when the original vertices are named. -/
theorem word_eq_of_graph_iso (s : State) (xs ys : List Bool)
    (hlen : xs.length = ys.length) (e : Equiv.Perm ℕ)
    (hfix : ∀ x < s.nextFresh, e x = x)
    (hgraph : ∀ x y, newEdge s xs x y ↔ newEdge s ys (e x) (e y)) :
    xs = ys := by
  induction xs generalizing s ys with
  | nil =>
      cases ys <;> simp_all
  | cons b bs ih =>
      cases ys with
      | nil => simp at hlen
      | cons c cs =>
          have hroot : e s.nextFresh = s.nextFresh := by
            apply (root_characterization s (c :: cs) (e s.nextFresh)
              ((fixed_prefix_threshold e s.nextFresh hfix _).2 le_rfl)).1
            intro a ha
            have h := (hgraph s.nextFresh a).1 (root_adjacent s (b :: bs) ha)
            simpa [hfix a (s.fresh a ha)] using h
          have hfix' : ∀ x < s.nextFresh + 1, e x = x := by
            intro x hx
            by_cases h : x < s.nextFresh
            · exact hfix x h
            · have heq : x = s.nextFresh := by omega
              simpa [heq] using hroot
          have hbc : b = c := by
            by_contra hne
            have hm := omitted_other_mem s b c hne
            have hedge : newEdge s (b :: bs) (s.nextFresh + 1) (omitted s c) := by
              right
              simpa using root_adjacent (advance s b) bs hm
            have himage := (hgraph _ _).1 hedge
            rw [hfix _ (omitted_lt_fresh s c)] at himage
            exact no_future_edge_to_omitted s c cs _
              ((fixed_prefix_threshold e (s.nextFresh + 1) hfix' _).2 le_rfl)
              himage
          subst c
          have htail : ∀ x y,
              newEdge (advance s b) bs x y ↔
              newEdge (advance s b) cs (e x) (e y) := by
            intro x y
            rw [tail_edge_iff, tail_edge_iff]
            exact and_congr (hgraph x y)
              (or_congr (fixed_prefix_threshold e _ hfix' x).symm
                (fixed_prefix_threshold e _ hfix' y).symm)
          have hrest := ih (advance s b) cs (by simpa using hlen)
            (by simpa using hfix') htail
          simp [hrest]

/-- The same recovery theorem with any fixed exterior graph. -/
theorem word_eq_of_full_graph_iso (s : State) (xs ys : List Bool)
    (hlen : xs.length = ys.length) (base : ℕ → ℕ → Prop)
    (hbase : ∀ x y, base x y → x < s.nextFresh ∧ y < s.nextFresh)
    (e : Equiv.Perm ℕ) (hfix : ∀ x < s.nextFresh, e x = x)
    (hgraph : ∀ x y, (base x y ∨ newEdge s xs x y) ↔
      (base (e x) (e y) ∨ newEdge s ys (e x) (e y))) : xs = ys := by
  apply word_eq_of_graph_iso s xs ys hlen e hfix
  intro x y
  constructor
  · intro h
    rcases (hgraph x y).1 (Or.inr h) with hb | ht
    · have hxy := hbase _ _ hb
      have hnew := newEdge_has_new s xs h
      have htx := fixed_prefix_threshold e _ hfix x
      have hty := fixed_prefix_threshold e _ hfix y
      omega
    · exact ht
  · intro h
    rcases (hgraph x y).2 (Or.inr h) with hb | ht
    · have hxy := hbase _ _ hb
      have hnew := newEdge_has_new s ys h
      rw [hfix x hxy.1, hfix y hxy.2] at hnew
      omega
    · exact ht

end PolytopeCounting.BinaryStellarSpine
