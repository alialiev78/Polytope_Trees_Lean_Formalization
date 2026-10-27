module

public import Proofs.IntrinsicGraphRecovery

@[expose] public section

/-! # Finite simplicial complexes and their stellar subdivisions -/

namespace PolytopeCounting.IntrinsicStellar

open BinaryStellarSpine

abbrev Facets := Finset (Finset ℕ)

def support (K : Facets) : Finset ℕ := K.biUnion id

def IsFace (K : Facets) (s : Finset ℕ) : Prop := ∃ t ∈ K, s ⊆ t

def Adj (K : Facets) (x y : ℕ) : Prop :=
  x ≠ y ∧ ∃ t ∈ K, x ∈ t ∧ y ∈ t

def replace (K : Facets) (S : Finset ℕ) (p : ℕ) : Facets :=
  K.erase S ∪ S.image (fun a => insert p (S.erase a))

def Pure (K : Facets) (q : ℕ) : Prop := ∀ T ∈ K, T.card = q

def Bounded (K : Facets) (p : ℕ) : Prop := ∀ T ∈ K, ∀ x ∈ T, x < p

@[simp] theorem mem_support (K : Facets) (x : ℕ) :
    x ∈ support K ↔ ∃ T ∈ K, x ∈ T := by simp [support]

/-- The finite facet presentation really generates a downward-closed
abstract simplicial complex. -/
theorem isFace_downward {K : Facets} {S T : Finset ℕ}
    (hT : IsFace K T) (hst : S ⊆ T) : IsFace K S := by
  obtain ⟨U, hU, htu⟩ := hT
  exact ⟨U, hU, hst.trans htu⟩

@[simp] theorem singleton_isFace (K : Facets) (x : ℕ) :
    IsFace K {x} ↔ x ∈ support K := by
  simp [IsFace, mem_support]

theorem fresh_not_face (K : Facets) (p : ℕ) (hb : Bounded K p)
    {T : Finset ℕ} (hT : T ∈ K) : p ∉ T := by
  intro hp
  exact Nat.lt_irrefl p (hb T hT p hp)

theorem maximal_of_pure {K : Facets} {S : Finset ℕ} {q : ℕ}
    (hpure : Pure K q) (hS : S ∈ K) {T : Finset ℕ}
    (hT : T ∈ K) (hst : S ⊆ T) : S = T := by
  exact Finset.eq_of_subset_of_card_le hst (by rw [hpure S hS, hpure T hT])

theorem exists_third {S : Finset ℕ} (hcard : 3 ≤ S.card) (x y : ℕ) :
    ∃ a ∈ S, a ≠ x ∧ a ≠ y := by
  by_contra h
  have hsub : S ⊆ {x, y} := by
    intro a ha
    by_contra hxy
    have hx : a ≠ x := by intro he; subst a; simp at hxy
    have hy : a ≠ y := by intro he; subst a; simp at hxy
    exact h ⟨a, ha, hx, hy⟩
  have hc := Finset.card_le_card hsub
  have htwo : ({x, y} : Finset ℕ).card ≤ 2 := by
    by_cases hxy : x = y <;> simp [hxy]
  omega

theorem child_mem_replace (K : Facets) (S : Finset ℕ) (p a : ℕ)
    (ha : a ∈ S) : insert p (S.erase a) ∈ replace K S p := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

theorem old_mem_replace {K : Facets} {S T : Finset ℕ} {p : ℕ}
    (hT : T ∈ K) (hne : T ≠ S) : T ∈ replace K S p := by
  apply Finset.mem_union_left
  exact Finset.mem_erase.mpr ⟨hne, hT⟩

/-- The one-skeleton equality; the dimension hypothesis is used precisely
when an old edge of S must survive in a child not opposite either endpoint. -/
theorem adj_replace (K : Facets) (S : Finset ℕ) (p x y : ℕ)
    (hS : S ∈ K) (hcard : 3 ≤ S.card) (hb : Bounded K p) :
    Adj (replace K S p) x y ↔ Adj K x y ∨
      ((x = p ∧ y ∈ S) ∨ (y = p ∧ x ∈ S)) := by
  have hpS : p ∉ S := fresh_not_face K p hb hS
  constructor
  · rintro ⟨hne, T, hT, hx, hy⟩
    rcases Finset.mem_union.mp hT with hold | hnew
    · exact Or.inl ⟨hne, T, (Finset.mem_erase.mp hold).2, hx, hy⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hnew
      rcases Finset.mem_insert.mp hx with hxp | hxo
      · right; left
        refine ⟨hxp, ?_⟩
        have hyp : y ≠ p := by intro he; exact hne (hxp.trans he.symm)
        exact (Finset.mem_erase.mp ((Finset.mem_insert.mp hy).resolve_left hyp)).2
      · rcases Finset.mem_insert.mp hy with hyp | hyo
        · exact Or.inr (Or.inr ⟨hyp, (Finset.mem_erase.mp hxo).2⟩)
        · exact Or.inl ⟨hne, S, hS, (Finset.mem_erase.mp hxo).2,
            (Finset.mem_erase.mp hyo).2⟩
  · rintro (hold | hstar)
    · obtain ⟨hne, T, hT, hx, hy⟩ := hold
      by_cases he : T = S
      · subst T
        obtain ⟨a, ha, hax, hay⟩ := exists_third hcard x y
        exact ⟨hne, insert p (S.erase a), child_mem_replace K S p a ha,
          Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hax.symm, hx⟩),
          Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hay.symm, hy⟩)⟩
      · exact ⟨hne, T, old_mem_replace hT he, hx, hy⟩
    · rcases hstar with ⟨hxp, hy⟩ | ⟨hyp, hx⟩
      · subst x
        obtain ⟨a, ha, hay, _⟩ := exists_third hcard y y
        refine ⟨?_, insert p (S.erase a), child_mem_replace K S p a ha, by simp, ?_⟩
        · intro h; exact hpS (h.symm ▸ hy)
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hay.symm, hy⟩)
      · subst y
        obtain ⟨a, ha, hax, _⟩ := exists_third hcard x x
        refine ⟨?_, insert p (S.erase a), child_mem_replace K S p a ha, ?_, by simp⟩
        · intro h; exact hpS (h ▸ hx)
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hax.symm, hx⟩)

theorem bounded_replace (K : Facets) (S : Finset ℕ) (p : ℕ)
    (hS : S ∈ K) (hb : Bounded K p) : Bounded (replace K S p) (p + 1) := by
  intro T hT x hx
  rcases Finset.mem_union.mp hT with hold | hnew
  · exact Nat.lt_succ_of_lt (hb T (Finset.mem_erase.mp hold).2 x hx)
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hnew
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hb S hS x (Finset.mem_erase.mp hx).2)

theorem pure_replace (K : Facets) (S : Finset ℕ) (p q : ℕ)
    (hS : S ∈ K) (hpure : Pure K q) (hb : Bounded K p) :
    Pure (replace K S p) q := by
  intro T hT
  rcases Finset.mem_union.mp hT with hold | hnew
  · exact hpure T (Finset.mem_erase.mp hold).2
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hnew
    have hp : p ∉ S.erase a := by
      intro hm; exact fresh_not_face K p hb hS (Finset.mem_erase.mp hm).2
    rw [Finset.card_insert_of_notMem hp, Finset.card_erase_of_mem ha]
    have hc := hpure S hS
    have hpos := Finset.card_pos.mpr ⟨a, ha⟩
    omega

theorem child_face_injective {S : Finset ℕ} {p : ℕ} (hpS : p ∉ S) :
    Set.InjOn (fun a => insert p (S.erase a)) (S : Set ℕ) := by
  intro a ha b hb he
  by_contra hab
  have hap : a ≠ p := by intro h; exact hpS (h ▸ ha)
  have hm : a ∈ insert p (S.erase b) :=
    Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hab, ha⟩)
  dsimp only at he
  rw [← he] at hm
  simp [hap] at hm

/-- Exact size change: one old maximal simplex is replaced by q new ones. -/
theorem card_replace (K : Facets) (S : Finset ℕ) (p : ℕ)
    (hS : S ∈ K) (hb : Bounded K p) :
    (replace K S p).card + 1 = K.card + S.card := by
  have hpS := fresh_not_face K p hb hS
  have hd : Disjoint (K.erase S) (S.image (fun a => insert p (S.erase a))) := by
    apply Finset.disjoint_left.mpr
    intro T hT hnew
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hnew
    exact fresh_not_face K p hb (Finset.mem_erase.mp hT).2 (by simp)
  rw [replace, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injOn (child_face_injective hpS)]
  have he := Finset.card_erase_add_one hS
  omega

/-- Validity contains only properties of the actual initial finite complex
and of its selected face; it is not a reconstruction or topology assumption. -/
structure Valid (s : State) (K : Facets) : Prop where
  selected : s.vertices ∈ K
  dimension : 3 ≤ s.vertices.card
  pure : Pure K s.vertices.card
  bounded : Bounded K s.nextFresh

theorem valid_advance {s : State} {K : Facets} (h : Valid s K) (b : Bool) :
    Valid (advance s b) (replace K s.vertices s.nextFresh) := by
  have hm : (advance s b).vertices ∈ replace K s.vertices s.nextFresh := by
    rw [advance_vertices]
    exact child_mem_replace K s.vertices s.nextFresh (omitted s b) (omitted_mem s b)
  have hpure := pure_replace K s.vertices s.nextFresh s.vertices.card
    h.selected h.pure h.bounded
  have hc := hpure _ hm
  refine ⟨hm, hc ▸ h.dimension, ?_, ?_⟩
  · rw [hc]; exact hpure
  · simpa using bounded_replace K s.vertices s.nextFresh h.selected h.bounded

def evolve (K : Facets) (s : State) : List Bool → Facets
  | [] => replace K s.vertices s.nextFresh
  | b :: bs => evolve (replace K s.vertices s.nextFresh) (advance s b) bs

/-- Connect the graph used in the recovery theorem to the actual face
incidence of the constructed simplicial complex. -/
theorem adj_evolve (K : Facets) (s : State) (bs : List Bool) (h : Valid s K)
    (x y : ℕ) : Adj (evolve K s bs) x y ↔ Adj K x y ∨ newEdge s bs x y := by
  induction bs generalizing K s with
  | nil =>
      exact adj_replace K s.vertices s.nextFresh x y h.selected h.dimension h.bounded
  | cons b bs ih =>
      change Adj (evolve (replace K s.vertices s.nextFresh) (advance s b) bs) x y ↔ _
      rw [ih _ _ (valid_advance h b),
        adj_replace K s.vertices s.nextFresh x y h.selected h.dimension h.bounded]
      change ((Adj K x y ∨ starEdge s x y) ∨ newEdge (advance s b) bs x y) ↔ _
      exact or_assoc

theorem bounded_evolve (K : Facets) (s : State) (bs : List Bool) (h : Valid s K) :
    Bounded (evolve K s bs) (s.nextFresh + bs.length + 1) := by
  induction bs generalizing K s with
  | nil => simpa [evolve] using bounded_replace K s.vertices s.nextFresh h.selected h.bounded
  | cons b bs ih =>
      have hh := ih _ _ (valid_advance h b)
      simpa [evolve, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem pure_evolve (K : Facets) (s : State) (bs : List Bool) (h : Valid s K) :
    Pure (evolve K s bs) s.vertices.card := by
  induction bs generalizing K s with
  | nil => exact pure_replace K s.vertices s.nextFresh _ h.selected h.pure h.bounded
  | cons b bs ih =>
      have hm := (valid_advance h b).selected
      have hp := pure_replace K s.vertices s.nextFresh _ h.selected h.pure h.bounded
      have hc := hp _ hm
      have hh := ih _ _ (valid_advance h b)
      rw [hc] at hh
      exact hh

theorem support_replace (K : Facets) (S : Finset ℕ) (p : ℕ)
    (hS : S ∈ K) (hcard : 3 ≤ S.card) :
    support (replace K S p) = insert p (support K) := by
  ext x
  simp only [mem_support, Finset.mem_insert]
  constructor
  · rintro ⟨T, hT, hx⟩
    rcases Finset.mem_union.mp hT with hold | hnew
    · exact Or.inr ⟨T, (Finset.mem_erase.mp hold).2, hx⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hnew
      rcases Finset.mem_insert.mp hx with he | hm
      · exact Or.inl he
      · exact Or.inr ⟨S, hS, (Finset.mem_erase.mp hm).2⟩
  · rintro (hxp | ⟨T, hT, hx⟩)
    · subst x
      obtain ⟨a, ha, _, _⟩ := exists_third hcard p p
      exact ⟨insert p (S.erase a), child_mem_replace K S p a ha, by simp⟩
    · by_cases he : T = S
      · subst T
        obtain ⟨a, ha, hax, _⟩ := exists_third hcard x x
        exact ⟨insert p (S.erase a), child_mem_replace K S p a ha,
          Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hax.symm, hx⟩)⟩
      · exact ⟨T, old_mem_replace hT he, hx⟩

theorem support_evolve (K : Facets) (s : State) (bs : List Bool) (h : Valid s K)
    (hsupp : support K = Finset.range s.nextFresh) :
    support (evolve K s bs) = Finset.range (s.nextFresh + bs.length + 1) := by
  induction bs generalizing K s with
  | nil =>
      rw [evolve, support_replace K s.vertices s.nextFresh h.selected h.dimension, hsupp]
      simpa using (Finset.range_add_one (n := s.nextFresh)).symm
  | cons b bs ih =>
      have hsupp' : support (replace K s.vertices s.nextFresh) =
          Finset.range (advance s b).nextFresh := by
        rw [support_replace K s.vertices s.nextFresh h.selected h.dimension, hsupp]
        simpa using (Finset.range_add_one (n := s.nextFresh)).symm
      have hh := ih _ _ (valid_advance h b) hsupp'
      simpa [evolve, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

/-- Number of actual maximal simplices after all insertions. -/
theorem card_evolve (K : Facets) (s : State) (bs : List Bool) (h : Valid s K) :
    (evolve K s bs).card = K.card + (s.vertices.card - 1) * (bs.length + 1) := by
  induction bs generalizing K s with
  | nil =>
      have hc := card_replace K s.vertices s.nextFresh h.selected h.bounded
      have hd := h.dimension
      simp only [evolve, List.length_nil, zero_add, Nat.mul_one]
      omega
  | cons b bs ih =>
      have hv := valid_advance h b
      have hp := pure_replace K s.vertices s.nextFresh _ h.selected h.pure h.bounded
      have hq := hp _ hv.selected
      have hc := card_replace K s.vertices s.nextFresh h.selected h.bounded
      have hd := h.dimension
      change (evolve (replace K s.vertices s.nextFresh) (advance s b) bs).card = _
      rw [ih _ _ hv, hq]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- Reconstruction is a conclusion about
the actual final simplicial one-skeleta. -/
theorem word_eq_of_complex_graph_iso (K : Facets) (s : State) (xs ys : List Bool)
    (h : Valid s K) (hlen : xs.length = ys.length) (e : Equiv.Perm ℕ)
    (hfix : ∀ x < s.nextFresh, e x = x)
    (hgraph : ∀ x y, Adj (evolve K s xs) x y ↔ Adj (evolve K s ys) (e x) (e y)) :
    xs = ys := by
  refine word_eq_of_full_graph_iso s xs ys hlen (Adj K) ?_ e hfix ?_
  · intro x y he
    obtain ⟨_, T, hT, hx, hy⟩ := he
    exact ⟨h.bounded T hT x hx, h.bounded T hT y hy⟩
  · intro x y
    simpa [adj_evolve K s xs h x y, adj_evolve K s ys h (e x) (e y)] using hgraph x y

end PolytopeCounting.IntrinsicStellar
