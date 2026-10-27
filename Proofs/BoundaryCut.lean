module

public import Proofs.FacetPairingModel
public import Mathlib.Logic.Embedding.Set

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-!
# The exact boundary after cutting one seam

This file proves the set-theoretic statement used by every nonbridge and
bridge cut construction: after erasing one seam, the new boundary is the
disjoint union of the old boundary and the two exposed endpoints.  The
equivalence is explicit, so it remains meaningful when the old boundary is
empty (`m = 0`).
-/

namespace PolytopeCounting
namespace FacetPairing
namespace PartialMatching

universe uD

variable {D : Type uD} [DecidableEq D]

/-- Local, dependency-light equivalence `Fin m ⊕ Fin n ≃ Fin (m+n)`. -/
def finSumEquiv : Fin m ⊕ Fin n ≃ Fin (m + n) where
  toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
  invFun i := Fin.addCases Sum.inl Sum.inr i
  left_inv x := by rcases x with x | x <;> simp
  right_inv x := by refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) x <;> simp

/-- A dart is free after erasing `e` iff it was free before, or it is one of
the two endpoints of `e`. -/
theorem boundary_erase_iff (M : PartialMatching D) (e : M.Seam) (d : D) :
    d ∉ (M.erase e).occupied ↔ d ∉ M.occupied ∨ d ∈ e.1 := by
  constructor
  · intro hfree
    by_cases hold : d ∉ M.occupied
    · exact Or.inl hold
    · right
      have hocc : d ∈ M.occupied := not_not.mp hold
      obtain ⟨f, hf, hdf⟩ := (M.mem_occupied_iff d).mp hocc
      have hfe : f = e.1 := by
        by_contra hne
        apply hfree
        exact ((M.erase e).mem_occupied_iff d).mpr
          ⟨f, Finset.mem_erase.mpr ⟨hne, hf⟩, hdf⟩
      simpa [hfe] using hdf
  · rintro (hold | hend) herased
    · apply hold
      obtain ⟨f, hf, hdf⟩ := ((M.erase e).mem_occupied_iff d).mp herased
      exact (M.mem_occupied_iff d).mpr
        ⟨f, Finset.mem_of_mem_erase hf, hdf⟩
    · obtain ⟨f, hf, hdf⟩ := ((M.erase e).mem_occupied_iff d).mp herased
      have hfe : e.1 = f := M.unique_incidence d e.1 e.2 hend
        f (Finset.mem_of_mem_erase hf) hdf
      exact (Finset.mem_erase.mp hf).1 hfe.symm

/-- The two endpoints of an off-diagonal seam, in the order supplied by
`Sym2.out`, are equivalent to `Bool`. -/
noncomputable def seamEndpointEquivBool (M : PartialMatching D) (e : M.Seam) :
    {d : D // d ∈ e.1} ≃ Bool where
  toFun d := if d.1 = e.1.out.1 then false else true
  invFun b := if b then ⟨e.1.out.2, Sym2.out_snd_mem e.1⟩
    else ⟨e.1.out.1, Sym2.out_fst_mem e.1⟩
  left_inv d := by
    apply Subtype.ext
    by_cases hfirst : d.1 = e.1.out.1
    · simp [hfirst]
    · have hrepr : s(e.1.out.1, e.1.out.2) = e.1 := by
        rw [Sym2.mk, e.1.out_eq]
      have hor : d.1 = e.1.out.1 ∨ d.1 = e.1.out.2 := by
        have hd : d.1 ∈ s(e.1.out.1, e.1.out.2) := by
          rw [hrepr]
          exact d.2
        exact Sym2.mem_iff.mp hd
      have hsecond := hor.resolve_left hfirst
      have hne : e.1.out.2 ≠ e.1.out.1 := by
        have h := M.exposed_endpoints_ne e
        change e.1.out.1 ≠ e.1.out.2 at h
        exact h.symm
      simp [hsecond, hne]
  right_inv b := by
    have hne := M.exposed_endpoints_ne e
    change e.1.out.1 ≠ e.1.out.2 at hne
    cases b <;> simp [hne, hne.symm]

/-- The boundary after a cut is explicitly the old boundary plus two
distinguished endpoints. -/
noncomputable def boundaryEraseEquiv (M : PartialMatching D) (e : M.Seam) :
    (M.erase e).Boundary ≃ M.Boundary ⊕ Bool := by
  classical
  let p : D → Prop := fun d ↦ d ∉ M.occupied
  let q : D → Prop := fun d ↦ d ∈ e.1
  have hset : {d : D | d ∉ (M.erase e).occupied} =
      {d : D | p d ∨ q d} := by
    ext d
    exact M.boundary_erase_iff e d
  have hd : Disjoint p q := by
    rw [disjoint_iff_inf_le]
    intro d hboth
    exact hboth.1 ((M.mem_occupied_iff d).mpr ⟨e.1, e.2, hboth.2⟩)
  exact (Set.equivOfEq hset).trans <|
    (subtypeOrEquiv p q hd).trans <|
      (Equiv.refl M.Boundary).sumCongr (M.seamEndpointEquivBool e)

/-- Cutting creates exactly two new boundary darts. -/
theorem card_boundary_erase [Fintype D]
    (M : PartialMatching D) (e : M.Seam) :
    Fintype.card (M.erase e).Boundary = Fintype.card M.Boundary + 2 := by
  rw [Fintype.card_congr (M.boundaryEraseEquiv e), Fintype.card_sum]
  simp

/-- Extend any old `Fin m` boundary labelling by two canonical star labels.
No exceptional definition is needed for `m = 0`. -/
noncomputable def cutBoundaryLabel
    (M : PartialMatching D) (e : M.Seam) (label : M.Boundary ≃ Fin m) :
    (M.erase e).Boundary ≃ Fin (m + 2) :=
  (M.boundaryEraseEquiv e).trans <|
    ((label.sumCongr finTwoEquiv.symm).trans finSumEquiv)

/-! ## Cutting and joining as inverse operations

An unordered seam must be joined from an unordered pair of free darts.  Using
an ordered pair here would introduce an artificial two-to-one choice. -/

/-- An off-diagonal unordered pair all of whose darts are free in `M`. -/
structure FreePair (M : PartialMatching D) where
  pair : Sym2 D
  free : ∀ d, d ∈ pair → d ∉ M.occupied
  offDiagonal : ¬ pair.IsDiag

namespace FreePair

@[ext]
theorem ext {M : PartialMatching D} {p q : M.FreePair}
    (hpair : p.pair = q.pair) : p = q := by
  cases p
  cases q
  cases hpair
  rfl

/-- Heterogeneous extensionality for free pairs whose ambient matchings have
been identified.  Only the underlying unordered pair contains data; the
freeness and off-diagonal fields are propositions. -/
theorem heq_of_matching_eq {M N : PartialMatching D} (hMN : M = N)
    {p : M.FreePair} {q : N.FreePair} (hpair : p.pair = q.pair) :
    HEq p q := by
  subst N
  exact heq_of_eq (FreePair.ext hpair)

/-- A free unordered pair is exactly an off-diagonal unordered pair in the
boundary subtype.  This equivalence is later used to obtain the binomial
factor `choose m 2`. -/
noncomputable def equivBoundaryOffDiagonal (M : PartialMatching D) :
    M.FreePair ≃ {p : Sym2 M.Boundary // ¬ p.IsDiag} where
  toFun p := ⟨p.pair.pmap Subtype.mk p.free, by
    intro hdiag
    apply p.offDiagonal
    have hmapped := hdiag.map (f := Subtype.val)
    have hmap :
        (p.pair.pmap Subtype.mk p.free).map Subtype.val = p.pair :=
      Sym2.pmap_subtype_map_subtypeVal p.pair _
    rw [hmap] at hmapped
    exact hmapped⟩
  invFun q := ⟨q.1.map Subtype.val, by
    intro d hd
    obtain ⟨a, _ha, rfl⟩ := Sym2.mem_map.mp hd
    exact a.2, by
    rw [Sym2.isDiag_map Subtype.val_injective]
    exact q.2⟩
  left_inv p := by
    apply FreePair.ext
    exact Sym2.pmap_subtype_map_subtypeVal p.pair _
  right_inv q := by
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    exact Sym2.pmap_subtype_map_subtypeVal (q.1.map Subtype.val) _

noncomputable instance instFintype [Fintype D] (M : PartialMatching D) :
  Fintype M.FreePair :=
  Fintype.ofEquiv {p : Sym2 M.Boundary // ¬ p.IsDiag}
    (equivBoundaryOffDiagonal M).symm

/-- First free endpoint, using the representative supplied by `Sym2.out`. -/
noncomputable def left (M : PartialMatching D) (p : M.FreePair) : M.Boundary :=
  ⟨p.pair.out.1, p.free _ (Sym2.out_fst_mem p.pair)⟩

/-- Second free endpoint. -/
noncomputable def right (M : PartialMatching D) (p : M.FreePair) : M.Boundary :=
  ⟨p.pair.out.2, p.free _ (Sym2.out_snd_mem p.pair)⟩

theorem left_ne_right (M : PartialMatching D) (p : M.FreePair) :
    (p.left M).1 ≠ (p.right M).1 := by
  intro h
  apply p.offDiagonal
  have hrepr : s(p.pair.out.1, p.pair.out.2) = p.pair := by
    rw [Sym2.mk, p.pair.out_eq]
  rw [← hrepr, Sym2.mk_isDiag_iff]
  simpa only [left, right] using h

theorem joinPair_left_right (M : PartialMatching D) (p : M.FreePair) :
    M.joinPair (p.left M) (p.right M) = p.pair := by
  change s(p.pair.out.1, p.pair.out.2) = p.pair
  rw [Sym2.mk, p.pair.out_eq]

end FreePair

/-- Join the selected unordered pair of free darts. -/
noncomputable def joinFreePair (M : PartialMatching D) (p : M.FreePair) :
    PartialMatching D :=
  M.join (p.left M) (p.right M) (p.left_ne_right M)

/-- The selected pair becomes the distinguished new seam. -/
noncomputable def freePairNewSeam (M : PartialMatching D) (p : M.FreePair) :
    (M.joinFreePair p).Seam :=
  M.newSeam (p.left M) (p.right M) (p.left_ne_right M)

@[simp] theorem freePairNewSeam_val (M : PartialMatching D) (p : M.FreePair) :
    (M.freePairNewSeam p).1 = p.pair := by
  exact p.joinPair_left_right M

/-- Cutting a seam records precisely that seam as a free pair. -/
def freePairAfterErase (M : PartialMatching D) (e : M.Seam) :
    (M.erase e).FreePair where
  pair := e.1
  free d hd := (M.endpointBoundaryAfterErase e d hd).2
  offDiagonal := M.offDiagonal e.1 e.2

/-- Joining the free pair exposed by a cut recovers the original matching. -/
theorem joinFreePair_afterErase (M : PartialMatching D) (e : M.Seam) :
    (M.erase e).joinFreePair (M.freePairAfterErase e) = M := by
  apply PartialMatching.ext
  have hout : s(e.1.out.1, e.1.out.2) = e.1 := by
    rw [Sym2.mk, e.1.out_eq]
  simp [joinFreePair, FreePair.left, FreePair.right, join, erase,
    freePairAfterErase, joinPair, hout, e.2]

/-- Cutting the seam just inserted from a free pair recovers the old
matching. -/
theorem erase_joinFreePair (M : PartialMatching D) (p : M.FreePair) :
    (M.joinFreePair p).erase (M.freePairNewSeam p) = M := by
  exact M.erase_join_newSeam (p.left M) (p.right M) (p.left_ne_right M)

/-- The total type of matchings with one distinguished seam. -/
abbrev MarkedMatching (D : Type uD) [DecidableEq D] :=
  Σ M : PartialMatching D, M.Seam

/-- The total type of matchings with one selected off-diagonal free pair. -/
abbrev FreePairMatching (D : Type uD) [DecidableEq D] :=
  Σ M : PartialMatching D, M.FreePair

/-- Cut a distinguished seam and retain its two endpoints as an unordered
free pair. -/
def cutMarked : MarkedMatching D → FreePairMatching D
  | ⟨M, e⟩ => ⟨M.erase e, M.freePairAfterErase e⟩

/-- Join a selected unordered free pair and distinguish the inserted seam. -/
noncomputable def joinSelected : FreePairMatching D → MarkedMatching D
  | ⟨M, p⟩ => ⟨M.joinFreePair p, M.freePairNewSeam p⟩

/-- Joining immediately after cutting is the identity on marked matchings. -/
theorem joinSelected_cutMarked (z : MarkedMatching D) :
    joinSelected (cutMarked z) = z := by
  rcases z with ⟨M, e⟩
  let hM := M.joinFreePair_afterErase e
  apply Sigma.ext hM
  apply (Subtype.heq_iff_coe_eq (fun x ↦ by
    change x ∈ ((M.erase e).joinFreePair (M.freePairAfterErase e)).seams ↔
      x ∈ M.seams
    rw [hM])).2
  simp only [joinSelected, cutMarked, freePairNewSeam_val]
  rfl

/-- Cutting immediately after joining is the identity on matchings equipped
with a selected free pair. -/
theorem cutMarked_joinSelected (z : FreePairMatching D) :
    cutMarked (joinSelected z) = z := by
  rcases z with ⟨M, p⟩
  let hM := M.erase_joinFreePair p
  apply Sigma.ext hM
  apply FreePair.heq_of_matching_eq hM
  simp only [cutMarked, joinSelected, freePairAfterErase,
    freePairNewSeam_val]

/-- Exact cut--join equivalence for partial matchings.  It is formulated
with an unordered free pair, so it carries no spurious orientation factor. -/
noncomputable def markedMatchingEquivFreePair :
    MarkedMatching D ≃ FreePairMatching D where
  toFun := cutMarked
  invFun := joinSelected
  left_inv := joinSelected_cutMarked
  right_inv := cutMarked_joinSelected


end PartialMatching

namespace ColoredMatching

universe uD

variable {D : Type uD} [DecidableEq D] {r : ℕ}

/-- A selected unordered pair of free darts together with the colour assigned
to the seam that will join them. -/
structure FreePairDatum (P : ColoredMatching D r) where
  selected : P.matching.FreePair
  color : Fin r

namespace FreePairDatum

@[ext]
theorem ext {P : ColoredMatching D r} {p q : P.FreePairDatum}
    (hpair : p.selected.pair = q.selected.pair)
    (hcolor : p.color = q.color) : p = q := by
  cases p with
  | mk ps pc =>
      cases q with
      | mk qs qc =>
          have hs : ps = qs := PartialMatching.FreePair.ext hpair
          subst qs
          cases hcolor
          rfl

theorem heq_of_pairing_eq {P Q : ColoredMatching D r} (hPQ : P = Q)
    {p : P.FreePairDatum} {q : Q.FreePairDatum}
    (hpair : p.selected.pair = q.selected.pair)
    (hcolor : p.color = q.color) : HEq p q := by
  subst Q
  exact heq_of_eq (FreePairDatum.ext hpair hcolor)

def equivProd (P : ColoredMatching D r) :
    P.FreePairDatum ≃ P.matching.FreePair × Fin r where
  toFun d := ⟨d.selected, d.color⟩
  invFun d := ⟨d.1, d.2⟩
  left_inv := by rintro ⟨_, _⟩; rfl
  right_inv := by rintro ⟨_, _⟩; rfl

noncomputable instance instFintype [Fintype D]
    (P : ColoredMatching D r) : Fintype P.FreePairDatum :=
  Fintype.ofEquiv (P.matching.FreePair × Fin r) (equivProd P).symm

end FreePairDatum

/-- Join a selected free pair with its specified colour. -/
noncomputable def joinFreePair (P : ColoredMatching D r)
    (d : P.FreePairDatum) : ColoredMatching D r :=
  P.join (d.selected.left P.matching) (d.selected.right P.matching)
    (d.selected.left_ne_right P.matching) d.color

/-- Distinguished seam created by `joinFreePair`. -/
noncomputable def freePairNewSeam (P : ColoredMatching D r)
    (d : P.FreePairDatum) : (P.joinFreePair d).Seam :=
  P.matching.newSeam (d.selected.left P.matching)
    (d.selected.right P.matching) (d.selected.left_ne_right P.matching)

@[simp] theorem freePairNewSeam_val (P : ColoredMatching D r)
    (d : P.FreePairDatum) : (P.freePairNewSeam d).1 = d.selected.pair :=
  d.selected.joinPair_left_right P.matching

/-- Data obtained by cutting a coloured seam. -/
def freePairAfterErase (P : ColoredMatching D r) (e : P.Seam) :
    (P.erase e).FreePairDatum where
  selected := P.matching.freePairAfterErase e
  color := P.color e

/-- Rejoining a cut coloured seam, with its remembered colour, recovers the
original coloured matching. -/
theorem joinFreePair_afterErase (P : ColoredMatching D r) (e : P.Seam) :
    (P.erase e).joinFreePair (P.freePairAfterErase e) = P := by
  exact P.join_erase_endpoints e

/-- Erasing a seam just joined from a selected free pair recovers the old
coloured matching. -/
theorem erase_joinFreePair (P : ColoredMatching D r)
    (d : P.FreePairDatum) :
    (P.joinFreePair d).erase (P.freePairNewSeam d) = P := by
  exact P.erase_join_newSeam (d.selected.left P.matching)
    (d.selected.right P.matching) (d.selected.left_ne_right P.matching)
    d.color

/-- Coloured matchings with a distinguished seam. -/
abbrev MarkedColoredMatching (D : Type uD) [DecidableEq D] (r : ℕ) :=
  Σ P : ColoredMatching D r, P.Seam

/-- Coloured matchings with a selected free pair and a proposed seam colour. -/
abbrev FreePairColoredMatching (D : Type uD) [DecidableEq D] (r : ℕ) :=
  Σ P : ColoredMatching D r, P.FreePairDatum

def cutMarked : MarkedColoredMatching D r → FreePairColoredMatching D r
  | ⟨P, e⟩ => ⟨P.erase e, P.freePairAfterErase e⟩

noncomputable def joinSelected :
    FreePairColoredMatching D r → MarkedColoredMatching D r
  | ⟨P, d⟩ => ⟨P.joinFreePair d, P.freePairNewSeam d⟩

theorem joinSelected_cutMarked (z : MarkedColoredMatching D r) :
    joinSelected (cutMarked z) = z := by
  rcases z with ⟨P, e⟩
  let hP := P.joinFreePair_afterErase e
  apply Sigma.ext hP
  apply (Subtype.heq_iff_coe_eq (fun x ↦ by
    change x ∈ ((P.erase e).joinFreePair (P.freePairAfterErase e)).matching.seams ↔
      x ∈ P.matching.seams
    rw [hP])).2
  simp only [joinSelected, cutMarked, freePairNewSeam_val,
    freePairAfterErase]
  rfl

theorem cutMarked_joinSelected (z : FreePairColoredMatching D r) :
    cutMarked (joinSelected z) = z := by
  rcases z with ⟨P, d⟩
  let hP := P.erase_joinFreePair d
  apply Sigma.ext hP
  apply FreePairDatum.heq_of_pairing_eq hP
  · change (P.freePairNewSeam d).1 = d.selected.pair
    exact P.freePairNewSeam_val d
  · exact P.color_join_newSeam (d.selected.left P.matching)
      (d.selected.right P.matching) (d.selected.left_ne_right P.matching)
      d.color

/-- Exact colour-preserving cut--join equivalence. -/
noncomputable def markedColoredEquivFreePair :
    MarkedColoredMatching D r ≃ FreePairColoredMatching D r where
  toFun := cutMarked
  invFun := joinSelected
  left_inv := joinSelected_cutMarked
  right_inv := cutMarked_joinSelected


end ColoredMatching
end FacetPairing
end PolytopeCounting
