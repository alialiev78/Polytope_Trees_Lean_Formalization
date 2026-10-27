module

public import Proofs.GlobalStellarHomeomorphism
public import Proofs.FinitePermutationExtension
public import Proofs.RelabellingCardinality
public import Mathlib.Data.List.OfFn

@[expose] public section
noncomputable section

/-! # Corollary 5.3 for finite pure triangulations of dimension at least two -/

namespace PolytopeCounting.IntrinsicStellar

open BinaryStellarSpine
open FinitePermutationExtension
open RelabellingCardinality

def rename (e : Equiv.Perm ℕ) (K : Facets) : Facets :=
  K.image (fun S => S.image e)

@[simp] theorem rename_refl (K : Facets) : rename (Equiv.refl ℕ) K = K := by
  simp [rename]

theorem rename_trans (e f : Equiv.Perm ℕ) (K : Facets) :
    rename f (rename e K) = rename (e.trans f) K := by
  simp [rename, Finset.image_image, Function.comp_def]

@[simp] theorem rename_inverse (e : Equiv.Perm ℕ) (K : Facets) :
    rename e.symm (rename e K) = K := by
  simp [rename, Finset.image_image, Function.comp_def]

theorem adj_rename (e : Equiv.Perm ℕ) (K : Facets) (x y : ℕ) :
    Adj (rename e K) (e x) (e y) ↔ Adj K x y := by
  constructor
  · rintro ⟨hne, T, hT, hx, hy⟩
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨u, hu, hex⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, hey⟩ := Finset.mem_image.mp hy
    have hux : u = x := e.injective hex
    have hvy : v = y := e.injective hey
    subst u; subst v
    exact ⟨fun h => hne (congrArg e h), S, hS, hu, hv⟩
  · rintro ⟨hne, S, hS, hx, hy⟩
    exact ⟨fun h => hne (e.injective h), S.image e,
      Finset.mem_image.mpr ⟨S, hS, rfl⟩,
      Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩

def allFacetFamilies (N : ℕ) : Finset Facets := ((Finset.range N).powerset).powerset

abbrev BoundedFamilies (N : ℕ) := {K : Facets // K ∈ allFacetFamilies N}

/-- These are presentations of ordinary abstract simplicial triangulations,
not quotient spaces of arbitrary facet pairings. -/
def Triangulation (M : Type*) [TopologicalSpace M] (N q : ℕ) :=
  {K : BoundedFamilies N // Pure K.1 q ∧ support K.1 = Finset.range N ∧
    Nonempty (Realization K.1 ≃ₜ M)}

instance triangulationFintype (M : Type*) [TopologicalSpace M] (N q : ℕ) :
    Fintype (Triangulation M N q) := by
  classical
  unfold Triangulation
  exact Fintype.ofFinite _

def triangulationIsomorphisms (M : Type*) [TopologicalSpace M] (N q : ℕ) :
    Isomorphisms (Triangulation M N q) (Fin N) where
  IsoAt K L e := rename (extend e) K.1.1 = L.1.1
  identity K := by simp
  inverse := by
    intro K L e he
    have hh := congrArg (rename (extend e).symm) he
    simpa using hh.symm
  compose := by
    intro K L J e f he hf
    rw [extend_trans, ← rename_trans, he, hf]

/-- Ordinary number of simplicial isomorphism classes. No symmetry weights. -/
def triangulationCount (M : Type*) [TopologicalSpace M] (N q : ℕ) : ℕ :=
  Fintype.card (Classes (triangulationIsomorphisms M N q))

theorem bounded_mem_all {K : Facets} {N : ℕ} (hb : Bounded K N) :
    K ∈ allFacetFamilies N := by
  simp only [allFacetFamilies, Finset.mem_powerset]
  intro S hS
  apply Finset.mem_powerset.mpr
  intro x hx
  exact Finset.mem_range.mpr (hb S hS x hx)

def binaryTriangulation {M : Type*} [TopologicalSpace M]
    (K : Facets) (s : State) (h : Valid s K)
    (hsupp : support K = Finset.range s.nextFresh)
    (hM : Realization K ≃ₜ M) (k : ℕ) (w : Fin k → Bool) :
    Triangulation M (s.nextFresh + k + 1) s.vertices.card := by
  let B := evolve K s (List.ofFn w)
  refine ⟨⟨B, bounded_mem_all ?_⟩, ?_, ?_, ?_⟩
  · simpa [B] using bounded_evolve K s (List.ofFn w) h
  · exact pure_evolve K s (List.ofFn w) h
  · simpa [B] using support_evolve K s (List.ofFn w) h hsupp
  · exact ⟨evolveHomeomorphTo K s (List.ofFn w) h hM⟩

@[simp] theorem binaryTriangulation_facets {M : Type*} [TopologicalSpace M]
    (K : Facets) (s : State) (h : Valid s K)
    (hsupp : support K = Finset.range s.nextFresh)
    (hM : Realization K ≃ₜ M) (k : ℕ) (w : Fin k → Bool) :
    (binaryTriangulation K s h hsupp hM k w).1.1 = evolve K s (List.ofFn w) := rfl

def binaryIsomorphisms {M : Type*} [TopologicalSpace M]
    (K : Facets) (s : State) (_h : Valid s K)
    (_hsupp : support K = Finset.range s.nextFresh)
    (_hM : Realization K ≃ₜ M) (k : ℕ) :
    Isomorphisms (Fin k → Bool) (Fin (s.nextFresh + k + 1)) where
  IsoAt w u e := rename (extend e) (evolve K s (List.ofFn w)) = evolve K s (List.ofFn u)
  identity w := by simp
  inverse := by
    intro w u e he
    have hh := congrArg (rename (extend e).symm) he
    simpa using hh.symm
  compose := by
    intro w u z e f he hf
    rw [extend_trans, ← rename_trans, he, hf]

def oldVertex (p k : ℕ) (i : Fin p) : Fin (p + k + 1) := ⟨i.val, by omega⟩

/-- Discharges the rigidity assumption of the generic unmarking lemma using
the actual graph of the constructed simplicial complexes. -/
theorem binary_rigidity {M : Type*} [TopologicalSpace M]
    (K : Facets) (s : State) (h : Valid s K)
    (hsupp : support K = Finset.range s.nextFresh)
    (hM : Realization K ≃ₜ M) (k : ℕ)
    (w u : Fin k → Bool) (e : Equiv.Perm (Fin (s.nextFresh + k + 1)))
    (he : (binaryIsomorphisms K s h hsupp hM k).IsoAt w u e)
    (hfix : ∀ i, e (oldVertex s.nextFresh k i) = oldVertex s.nextFresh k i) : w = u := by
  apply List.ofFn_injective
  apply word_eq_of_complex_graph_iso K s (List.ofFn w) (List.ofFn u) h
    (by simp) (extend e)
  · intro x hx
    have hf := congrArg Fin.val (hfix ⟨x, hx⟩)
    have hxN : x < s.nextFresh + k + 1 := by omega
    simpa [oldVertex, extend_apply_lt e x hxN] using hf
  · intro x y
    change rename (extend e) (evolve K s (List.ofFn w)) =
      evolve K s (List.ofFn u) at he
    rw [← he]
    exact (adj_rename (extend e) (evolve K s (List.ofFn w)) x y).symm

def familyClassMap {M : Type*} [TopologicalSpace M]
    (K : Facets) (s : State) (h : Valid s K)
    (hsupp : support K = Finset.range s.nextFresh)
    (hM : Realization K ≃ₜ M) (k : ℕ) :
    Classes (binaryIsomorphisms K s h hsupp hM k) →
      Classes (triangulationIsomorphisms M (s.nextFresh + k + 1) s.vertices.card) :=
  Quotient.lift
    (fun w => Quotient.mk _ (binaryTriangulation K s h hsupp hM k w))
    (by
      intro w u hrel
      apply Quotient.sound
      exact hrel)

theorem familyClassMap_injective {M : Type*} [TopologicalSpace M]
    (K : Facets) (s : State) (h : Valid s K)
    (hsupp : support K = Finset.range s.nextFresh)
    (hM : Realization K ≃ₜ M) (k : ℕ) :
    Function.Injective (familyClassMap K s h hsupp hM k) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro w u hrel
  apply Quotient.sound
  have hh := Quotient.exact hrel
  exact hh

/-- Exact ordinary-class lower bound after n=k+1 insertions. There is no
unproved reconstruction, topology-preservation, or mass-to-class hypothesis. -/
theorem corollary53_integer {M : Type*} [TopologicalSpace M]
    (K : Facets) (s : State) (h : Valid s K)
    (hsupp : support K = Finset.range s.nextFresh)
    (hM : Realization K ≃ₜ M) (k : ℕ) :
    2 ^ k ≤ triangulationCount M (s.nextFresh + k + 1) s.vertices.card *
      (s.nextFresh + k + 1) ^ s.nextFresh := by
  have hmark := classes_bound (binaryIsomorphisms K s h hsupp hM k)
    (oldVertex s.nextFresh k) (binary_rigidity K s h hsupp hM k)
  have hclasses := Fintype.card_le_of_injective
    (familyClassMap K s h hsupp hM k) (familyClassMap_injective K s h hsupp hM k)
  calc
    2 ^ k ≤ Fintype.card (Classes (binaryIsomorphisms K s h hsupp hM k)) *
        (s.nextFresh + k + 1) ^ s.nextFresh := by simpa using hmark
    _ ≤ _ := Nat.mul_le_mul_right _ hclasses

/-- The displayed real-valued version, with n inserted vertices. -/
theorem corollary53 {M : Type*} [TopologicalSpace M]
    (K : Facets) (s : State) (h : Valid s K)
    (hsupp : support K = Finset.range s.nextFresh)
    (hM : Realization K ≃ₜ M) (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ (n - 1) / (s.nextFresh + n : ℝ) ^ s.nextFresh ≤
      (triangulationCount M (s.nextFresh + n) s.vertices.card : ℝ) := by
  have hint := corollary53_integer K s h hsupp hM (n - 1)
  have hn' : s.nextFresh + (n - 1) + 1 = s.nextFresh + n := by omega
  rw [hn'] at hint
  have hpos : (0 : ℝ) < (s.nextFresh + n : ℝ) ^ s.nextFresh := by positivity
  apply (div_le_iff₀ hpos).2
  exact_mod_cast hint

/-- The state required above can be selected from any maximal simplex of
cardinality at least three; it is not additional combinatorial structure. -/
def stateFromFacet (K : Facets) (S : Finset ℕ) (v : ℕ)
    (hS : S ∈ K) (hcard : 3 ≤ S.card) (hb : Bounded K v) : State := by
  have hn : S.Nonempty := Finset.card_pos.mp (by omega)
  let a := Classical.choose hn
  have ha : a ∈ S := Classical.choose_spec hn
  let b := Classical.choose (exists_third hcard a a)
  have hbmem : b ∈ S := (Classical.choose_spec (exists_third hcard a a)).1
  have hba : b ≠ a := (Classical.choose_spec (exists_third hcard a a)).2.1
  exact {
    vertices := S
    first := a
    second := b
    nextFresh := v
    first_mem := ha
    second_mem := hbmem
    distinct := hba.symm
    fresh := fun x hx => hb S hS x hx }

/-- The same lower bound directly from an arbitrary fixed finite pure
triangulation, using only ordinary inductive simplex attachments. -/
theorem corollary53_from_initial_triangulation {M : Type*} [TopologicalSpace M]
    (K : Facets) (S : Finset ℕ) (v : ℕ)
    (hS : S ∈ K) (hcard : 3 ≤ S.card) (hpure : Pure K S.card)
    (hb : Bounded K v) (hsupp : support K = Finset.range v)
    (hM : Realization K ≃ₜ M) (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ (n - 1) / (v + n : ℝ) ^ v ≤
      (triangulationCount M (v + n) S.card : ℝ) := by
  let s := stateFromFacet K S v hS hcard hb
  have hv : Valid s K := ⟨hS, hcard, hpure, hb⟩
  exact corollary53 K s hv hsupp hM n hn

end PolytopeCounting.IntrinsicStellar
