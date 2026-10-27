module

public import Proofs.MarkedSeamBridge

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Restricting a facet matching to a component

This module defines the induced
partial and coloured matching on a subtype of cells and proves that, when a
partition has no crossing seam, the two restrictions determine all seams of
the original matching.
-/

namespace PolytopeCounting
namespace FacetPairing

noncomputable section

universe uC uD uE

variable {Cell : Type uC} [Fintype Cell] [DecidableEq Cell]
  {facets : Cell → ℕ} {r : ℕ}

/-- Darts whose cell lies in `S`. -/
abbrev RestrictedDart (S : Set Cell) :=
  CellDart S (fun c ↦ facets c.1)

/-- Forget the proof that the cell of a restricted dart lies in `S`. -/
def includeDart (S : Set Cell) : RestrictedDart (facets := facets) S →
    CellDart Cell facets
  | ⟨c, i⟩ => ⟨c.1, i⟩

theorem includeDart_injective (S : Set Cell) :
    Function.Injective (includeDart (facets := facets) S) := by
  intro x y h
  apply Sigma.ext
  · exact Subtype.ext (Sigma.ext_iff.mp h).1
  · exact (Sigma.ext_iff.mp h).2

/-- Transport a local seam to the ambient dart type. -/
def includeSeam (S : Set Cell) :
    Sym2 (RestrictedDart (facets := facets) S) →
      Sym2 (CellDart Cell facets) :=
  Sym2.map (includeDart (facets := facets) S)

theorem includeSeam_injective (S : Set Cell) :
    Function.Injective (includeSeam (facets := facets) S) :=
  Sym2.map.injective (includeDart_injective (facets := facets) S)

/-- Every endpoint dart of a seam has its cell in `S`. -/
def SeamInternal (S : Set Cell) (e : Sym2 (CellDart Cell facets)) : Prop :=
  ∀ d ∈ e, d.1 ∈ S

/-- Regard an ambient dart known to lie over `S` as a restricted dart. -/
def restrictDart (S : Set Cell) (d : CellDart Cell facets) (hd : d.1 ∈ S) :
    RestrictedDart (facets := facets) S :=
  ⟨⟨d.1, hd⟩, d.2⟩

@[simp]
theorem includeDart_restrictDart (S : Set Cell) (d : CellDart Cell facets)
    (hd : d.1 ∈ S) :
    includeDart (facets := facets) S (restrictDart S d hd) = d := by
  cases d
  rfl

/-- Lift an ambient seam all of whose endpoints lie over `S` to a local
seam. -/
noncomputable def liftInternalSeam (S : Set Cell)
    (e : Sym2 (CellDart Cell facets)) (h : SeamInternal S e) :
    Sym2 (RestrictedDart (facets := facets) S) :=
  s(restrictDart S e.out.1 (h e.out.1 (Sym2.out_fst_mem e)),
    restrictDart S e.out.2 (h e.out.2 (Sym2.out_snd_mem e)))

@[simp]
theorem includeSeam_liftInternalSeam (S : Set Cell)
    (e : Sym2 (CellDart Cell facets)) (h : SeamInternal S e) :
    includeSeam (facets := facets) S (liftInternalSeam S e h) = e := by
  simp only [includeSeam, liftInternalSeam, Sym2.map_mk,
    includeDart_restrictDart]
  rw [Sym2.mk, e.out_eq]

/-! ## Generic transport and disjoint union of matchings -/

namespace PartialMatching

variable {D : Type uD} {E : Type uE} [DecidableEq D] [DecidableEq E]

/-- Push a partial matching forward along an injective map of darts. -/
def map (M : PartialMatching D) (f : D → E) (hf : Function.Injective f) :
    PartialMatching E where
  seams := M.seams.map ⟨Sym2.map f, Sym2.map.injective hf⟩
  offDiagonal e he := by
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_map.mp he
    intro hd
    exact M.offDiagonal e₀ he₀ ((Sym2.isDiag_map hf).mp hd)
  unique_incidence d e he hde g hg hdg := by
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨g₀, hg₀, rfl⟩ := Finset.mem_map.mp hg
    obtain ⟨d₁, hd₁, hfd₁⟩ := Sym2.mem_map.mp hde
    obtain ⟨d₂, hd₂, hfd₂⟩ := Sym2.mem_map.mp hdg
    have heg : e₀ = g₀ := by
      apply M.unique_incidence d₁ e₀ he₀ hd₁ g₀ hg₀
      simpa [hf (hfd₁.trans hfd₂.symm)] using hd₂
    exact congrArg (Sym2.map f) heg

@[simp]
theorem seams_map (M : PartialMatching D) (f : D → E)
    (hf : Function.Injective f) :
    (M.map f hf).seams = M.seams.map ⟨Sym2.map f, Sym2.map.injective hf⟩ :=
  rfl

/-- Union of two matchings whose occupied dart sets are disjoint. -/
def disjointUnion (M N : PartialMatching D)
    (hdisj : Disjoint M.occupied N.occupied) : PartialMatching D where
  seams := M.seams ∪ N.seams
  offDiagonal e he := by
    rcases Finset.mem_union.mp he with heM | heN
    · exact M.offDiagonal e heM
    · exact N.offDiagonal e heN
  unique_incidence d e he hde g hg hdg := by
    rcases Finset.mem_union.mp he with heM | heN
    · rcases Finset.mem_union.mp hg with hgM | hgN
      · exact M.unique_incidence d e heM hde g hgM hdg
      · exact False.elim (Finset.disjoint_left.mp hdisj
          ((M.mem_occupied_iff d).mpr ⟨e, heM, hde⟩)
          ((N.mem_occupied_iff d).mpr ⟨g, hgN, hdg⟩))
    · rcases Finset.mem_union.mp hg with hgM | hgN
      · exact False.elim (Finset.disjoint_left.mp hdisj
          ((M.mem_occupied_iff d).mpr ⟨g, hgM, hdg⟩)
          ((N.mem_occupied_iff d).mpr ⟨e, heN, hde⟩))
      · exact N.unique_incidence d e heN hde g hgN hdg

@[simp]
theorem seams_disjointUnion (M N : PartialMatching D)
    (hdisj : Disjoint M.occupied N.occupied) :
    (M.disjointUnion N hdisj).seams = M.seams ∪ N.seams := rfl

end PartialMatching

theorem includeSeam_ne_of_disjoint
    (S T : Set Cell) (hdisj : Disjoint S T)
    (eS : Sym2 (RestrictedDart (facets := facets) S))
    (eT : Sym2 (RestrictedDart (facets := facets) T)) :
    includeSeam (facets := facets) S eS ≠
      includeSeam (facets := facets) T eT := by
  intro hEq
  have hmemS : includeDart (facets := facets) S eS.out.1 ∈
      includeSeam (facets := facets) S eS :=
    Sym2.mem_map.mpr ⟨eS.out.1, Sym2.out_fst_mem eS, rfl⟩
  have hmemT : includeDart (facets := facets) S eS.out.1 ∈
      includeSeam (facets := facets) T eT := by simpa [hEq] using hmemS
  obtain ⟨dT, hdT, hTdS⟩ := Sym2.mem_map.mp hmemT
  have hcell : dT.1.1 = eS.out.1.1.1 :=
    congrArg Sigma.fst hTdS
  have hT : eS.out.1.1.1 ∈ T := hcell ▸ dT.1.2
  exact Set.disjoint_left.mp hdisj eS.out.1.1.2 hT

namespace PartialMatching

/-- The matching induced on a set of cells.  A local seam is retained exactly
when its image is an ambient seam. -/
noncomputable def restrict
    (M : PartialMatching (CellDart Cell facets)) (S : Set Cell) :
    PartialMatching (RestrictedDart (facets := facets) S) := by
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype (RestrictedDart (facets := facets) S) := Fintype.ofFinite _
  letI : Fintype (Sym2 (RestrictedDart (facets := facets) S)) :=
    Fintype.ofFinite _
  exact
    { seams := Finset.univ.filter fun e ↦
        includeSeam (facets := facets) S e ∈ M.seams
      offDiagonal := by
        intro e he
        have hamb : includeSeam (facets := facets) S e ∈ M.seams :=
          (Finset.mem_filter.mp he).2
        intro hdiag
        exact M.offDiagonal _ hamb hdiag.map
      unique_incidence := by
        intro d e he hde f hf hdf
        apply includeSeam_injective (facets := facets) S
        apply M.unique_incidence
          (includeDart (facets := facets) S d)
          (includeSeam (facets := facets) S e)
          ((Finset.mem_filter.mp he).2)
        · exact Sym2.mem_map.mpr ⟨d, hde, rfl⟩
        · exact (Finset.mem_filter.mp hf).2
        · exact Sym2.mem_map.mpr ⟨d, hdf, rfl⟩ }

@[simp]
theorem mem_restrict_seams
    (M : PartialMatching (CellDart Cell facets)) (S : Set Cell)
    (e : Sym2 (RestrictedDart (facets := facets) S)) :
    e ∈ (M.restrict S).seams ↔
      includeSeam (facets := facets) S e ∈ M.seams := by
  simp [restrict]

/-- Ambient images of all seams in the restriction. -/
noncomputable def restrictedSeams
    (M : PartialMatching (CellDart Cell facets)) (S : Set Cell) :
    Finset (Sym2 (CellDart Cell facets)) :=
  (M.restrict S).seams.map
    ⟨includeSeam (facets := facets) S,
      includeSeam_injective (facets := facets) S⟩

theorem mem_restrictedSeams_iff
    (M : PartialMatching (CellDart Cell facets)) (S : Set Cell)
    (e : Sym2 (CellDart Cell facets)) :
    e ∈ M.restrictedSeams S ↔
      ∃ eS : Sym2 (RestrictedDart (facets := facets) S),
        includeSeam (facets := facets) S eS = e ∧ e ∈ M.seams := by
  constructor
  · intro he
    obtain ⟨eS, heS, rfl⟩ := Finset.mem_map.mp he
    exact ⟨eS, rfl, (M.mem_restrict_seams S eS).mp heS⟩
  · rintro ⟨eS, rfl, he⟩
    apply Finset.mem_map.mpr
    exact ⟨eS, (M.mem_restrict_seams S eS).mpr he, rfl⟩

/-- Intrinsic characterization of the ambient seams recovered from a
restriction. -/
theorem mem_restrictedSeams_iff_internal
    (M : PartialMatching (CellDart Cell facets)) (S : Set Cell)
    (e : Sym2 (CellDart Cell facets)) :
    e ∈ M.restrictedSeams S ↔ e ∈ M.seams ∧ SeamInternal S e := by
  constructor
  · intro he
    obtain ⟨eS, hmap, heM⟩ := (M.mem_restrictedSeams_iff S e).mp he
    refine ⟨heM, ?_⟩
    intro d hd
    have hd' : d ∈ includeSeam (facets := facets) S eS := by
      simpa [hmap] using hd
    obtain ⟨dS, hdS, hinc⟩ := Sym2.mem_map.mp hd'
    rw [← hinc]
    exact dS.1.2
  · rintro ⟨heM, hint⟩
    apply (M.mem_restrictedSeams_iff S e).mpr
    exact ⟨liftInternalSeam S e hint,
      includeSeam_liftInternalSeam S e hint, heM⟩

end PartialMatching

/-! ## Reassembly of two component matchings -/

/-- The ambient images of matchings on disjoint cell sets occupy disjoint
darts. -/
theorem occupied_map_include_disjoint
    (S T : Set Cell) (hdisj : Disjoint S T)
    (M : PartialMatching (RestrictedDart (facets := facets) S))
    (N : PartialMatching (RestrictedDart (facets := facets) T)) :
    Disjoint
      (M.map (includeDart (facets := facets) S)
        (includeDart_injective (facets := facets) S)).occupied
      (N.map (includeDart (facets := facets) T)
        (includeDart_injective (facets := facets) T)).occupied := by
  rw [Finset.disjoint_left]
  intro d hdM hdN
  obtain ⟨e, he, hde⟩ :=
    ((M.map (includeDart (facets := facets) S)
      (includeDart_injective (facets := facets) S)).mem_occupied_iff d).mp hdM
  obtain ⟨f, hf, hdf⟩ :=
    ((N.map (includeDart (facets := facets) T)
      (includeDart_injective (facets := facets) T)).mem_occupied_iff d).mp hdN
  obtain ⟨eS, heS, heEq⟩ := Finset.mem_map.mp he
  obtain ⟨fT, hfT, hfEq⟩ := Finset.mem_map.mp hf
  have hde' : d ∈ Sym2.map (includeDart (facets := facets) S) eS := by
    rw [← heEq] at hde
    exact hde
  have hdf' : d ∈ Sym2.map (includeDart (facets := facets) T) fT := by
    rw [← hfEq] at hdf
    exact hdf
  obtain ⟨dS, hdSe, hSd⟩ := Sym2.mem_map.mp hde'
  obtain ⟨dT, hdTf, hTd⟩ := Sym2.mem_map.mp hdf'
  have hcell : dT.1.1 = dS.1.1 :=
    congrArg Sigma.fst (hTd.trans hSd.symm)
  exact Set.disjoint_left.mp hdisj dS.1.2 (hcell ▸ dT.1.2)

/-- Reassemble two local matchings on disjoint cell sets as an ambient
matching. -/
noncomputable def reassembleMatching
    (S T : Set Cell) (hdisj : Disjoint S T)
    (M : PartialMatching (RestrictedDart (facets := facets) S))
    (N : PartialMatching (RestrictedDart (facets := facets) T)) :
    PartialMatching (CellDart Cell facets) :=
  let MS := M.map (includeDart (facets := facets) S)
    (includeDart_injective (facets := facets) S)
  let NT := N.map (includeDart (facets := facets) T)
    (includeDart_injective (facets := facets) T)
  MS.disjointUnion NT (occupied_map_include_disjoint S T hdisj M N)

theorem seams_reassembleMatching
    (S T : Set Cell) (hdisj : Disjoint S T)
    (M : PartialMatching (RestrictedDart (facets := facets) S))
    (N : PartialMatching (RestrictedDart (facets := facets) T)) :
    (reassembleMatching S T hdisj M N).seams =
      M.seams.map
          ⟨includeSeam (facets := facets) S,
            includeSeam_injective (facets := facets) S⟩ ∪
        N.seams.map
          ⟨includeSeam (facets := facets) T,
            includeSeam_injective (facets := facets) T⟩ := rfl

/-- Every seam of a reassembled matching remains on one component. -/
theorem seamInternal_reassembleMatching
    (S T : Set Cell) (hdisj : Disjoint S T)
    (M : PartialMatching (RestrictedDart (facets := facets) S))
    (N : PartialMatching (RestrictedDart (facets := facets) T))
    (e : Sym2 (CellDart Cell facets))
    (he : e ∈ (reassembleMatching S T hdisj M N).seams) :
    SeamInternal S e ∨ SeamInternal T e := by
  rw [seams_reassembleMatching] at he
  rcases Finset.mem_union.mp he with heS | heT
  · obtain ⟨eS, heSM, rfl⟩ := Finset.mem_map.mp heS
    left
    intro d hd
    obtain ⟨dS, hdS, rfl⟩ := Sym2.mem_map.mp hd
    exact dS.1.2
  · obtain ⟨eT, heTN, rfl⟩ := Finset.mem_map.mp heT
    right
    intro d hd
    obtain ⟨dT, hdT, rfl⟩ := Sym2.mem_map.mp hd
    exact dT.1.2

/-- Restricting the reassembled matching back to the left component recovers
the left local matching. -/
theorem restrict_reassembleMatching_left
    (S T : Set Cell) (hdisj : Disjoint S T)
    (M : PartialMatching (RestrictedDart (facets := facets) S))
    (N : PartialMatching (RestrictedDart (facets := facets) T)) :
    (reassembleMatching S T hdisj M N).restrict S = M := by
  apply PartialMatching.ext
  ext eS
  rw [PartialMatching.mem_restrict_seams]
  rw [seams_reassembleMatching]
  constructor
  · intro he
    rcases Finset.mem_union.mp he with heM | heN
    · obtain ⟨eS', heSM, hEq⟩ := Finset.mem_map.mp heM
      have hlocal : eS' = eS :=
        includeSeam_injective (facets := facets) S hEq
      simpa only [hlocal] using heSM
    · obtain ⟨eT, heTN, hEq⟩ := Finset.mem_map.mp heN
      exact False.elim (includeSeam_ne_of_disjoint S T hdisj eS eT hEq.symm)
  · intro heM
    apply Finset.mem_union.mpr
    exact Or.inl (Finset.mem_map.mpr ⟨eS, heM, rfl⟩)

/-- Restricting the reassembled matching back to the right component recovers
the right local matching. -/
theorem restrict_reassembleMatching_right
    (S T : Set Cell) (hdisj : Disjoint S T)
    (M : PartialMatching (RestrictedDart (facets := facets) S))
    (N : PartialMatching (RestrictedDart (facets := facets) T)) :
    (reassembleMatching S T hdisj M N).restrict T = N := by
  apply PartialMatching.ext
  ext eT
  rw [PartialMatching.mem_restrict_seams]
  rw [seams_reassembleMatching]
  constructor
  · intro he
    rcases Finset.mem_union.mp he with heM | heN
    · obtain ⟨eS, heSM, hEq⟩ := Finset.mem_map.mp heM
      exact False.elim (includeSeam_ne_of_disjoint S T hdisj eS eT hEq)
    · obtain ⟨eT', heTN, hEq⟩ := Finset.mem_map.mp heN
      have hlocal : eT' = eT :=
        includeSeam_injective (facets := facets) T hEq
      simpa only [hlocal] using heTN
  · intro heN
    apply Finset.mem_union.mpr
    exact Or.inr (Finset.mem_map.mpr ⟨eT, heN, rfl⟩)

/-! ## No-crossing partitions -/

/-- No dual adjacency runs from `S` to `T`. -/
def NoCrossing (P : ColoredMatching (CellDart Cell facets) r)
    (S T : Set Cell) : Prop :=
  ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ T → ¬ P.Adjacent facets u v

theorem seamInternal_of_out_cells
    (S : Set Cell) (e : Sym2 (CellDart Cell facets))
    (h₁ : e.out.1.1 ∈ S) (h₂ : e.out.2.1 ∈ S) :
    SeamInternal S e := by
  intro d hd
  have hout : s(e.out.1, e.out.2) = e := by
    rw [Sym2.mk, e.out_eq]
  rw [← hout] at hd
  rcases (Sym2.mem_iff.mp hd) with rfl | rfl
  · exact h₁
  · exact h₂

/-- Under a covering two-set partition with no crossing adjacency, every
seam lies wholly on exactly one side (existence is all that decomposition
needs; disjointness supplies uniqueness separately). -/
theorem seam_internal_left_or_right
    (P : ColoredMatching (CellDart Cell facets) r)
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hno : NoCrossing P S T)
    (e : Sym2 (CellDart Cell facets)) (he : e ∈ P.matching.seams) :
    SeamInternal S e ∨ SeamInternal T e := by
  have hmem (c : Cell) : c ∈ S ∨ c ∈ T := by
    have hc : c ∈ S ∪ T := by rw [hcover]; exact Set.mem_univ c
    simpa only [Set.mem_union] using hc
  have hadj : P.Adjacent facets e.out.1.1 e.out.2.1 := by
    refine ⟨e.out.1.2, e.out.2.2, ?_⟩
    rw [Sym2.mk, e.out_eq]
    exact he
  rcases hmem e.out.1.1 with h1S | h1T
  · rcases hmem e.out.2.1 with h2S | h2T
    · exact Or.inl (seamInternal_of_out_cells S e h1S h2S)
    · exact False.elim ((hno h1S h2T) hadj)
  · rcases hmem e.out.2.1 with h2S | h2T
    · exact False.elim ((hno h2S h1T) (P.adjacent_symm facets hadj))
    · exact Or.inr (seamInternal_of_out_cells T e h1T h2T)

/-- Seam reassembly from an already established internal-side dichotomy. -/
theorem PartialMatching.restrictedSeams_union_eq_of_internal
    (M : PartialMatching (CellDart Cell facets)) (S T : Set Cell)
    (hint : ∀ e ∈ M.seams, SeamInternal S e ∨ SeamInternal T e) :
    M.restrictedSeams S ∪ M.restrictedSeams T = M.seams := by
  ext e
  simp only [Finset.mem_union, M.mem_restrictedSeams_iff_internal]
  constructor
  · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
  · intro he
    rcases hint e he with hS | hT
    · exact Or.inl ⟨he, hS⟩
    · exact Or.inr ⟨he, hT⟩

/-- Exact seam-level reassembly: if the two cell sets cover and no seam
crosses, the ambient seam finset is the union of the two induced seam
finsets. -/
theorem restrictedSeams_union_eq
    (P : ColoredMatching (CellDart Cell facets) r)
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hno : NoCrossing P S T) :
    P.matching.restrictedSeams S ∪ P.matching.restrictedSeams T =
      P.matching.seams := by
  apply P.matching.restrictedSeams_union_eq_of_internal
  exact seam_internal_left_or_right P S T hcover hno

/-- Restrictions to disjoint cell sets have disjoint ambient seam images. -/
theorem PartialMatching.restrictedSeams_disjoint
    (M : PartialMatching (CellDart Cell facets)) (S T : Set Cell)
    (hdisj : Disjoint S T) :
    Disjoint (M.restrictedSeams S) (M.restrictedSeams T) := by
  rw [Finset.disjoint_left]
  intro e heS heT
  have hiS := (M.mem_restrictedSeams_iff_internal S e).mp heS |>.2
  have hiT := (M.mem_restrictedSeams_iff_internal T e).mp heT |>.2
  exact Set.disjoint_left.mp hdisj
    (hiS e.out.1 (Sym2.out_fst_mem e))
    (hiT e.out.1 (Sym2.out_fst_mem e))

@[simp]
theorem PartialMatching.card_restrictedSeams
    (M : PartialMatching (CellDart Cell facets)) (S : Set Cell) :
    (M.restrictedSeams S).card = (M.restrict S).seams.card := by
  simp [PartialMatching.restrictedSeams]

/-- With a disjoint no-crossing partition, seam counts add exactly. -/
theorem restricted_seam_counts_add
    (P : ColoredMatching (CellDart Cell facets) r)
    (S T : Set Cell) (hcover : S ∪ T = Set.univ)
    (hdisj : Disjoint S T) (hno : NoCrossing P S T) :
    (P.matching.restrict S).seams.card +
        (P.matching.restrict T).seams.card = P.matching.seams.card := by
  rw [← P.matching.card_restrictedSeams S,
    ← P.matching.card_restrictedSeams T,
    ← Finset.card_union_of_disjoint
      (P.matching.restrictedSeams_disjoint S T hdisj),
    restrictedSeams_union_eq P S T hcover hno]

/-- Two partial matchings with internal seams are equal as soon as their two
component restrictions agree.  This is the uniqueness half of reassembly. -/
theorem PartialMatching.eq_of_restrict_eq_of_internal
    (M N : PartialMatching (CellDart Cell facets)) (S T : Set Cell)
    (hM : ∀ e ∈ M.seams, SeamInternal S e ∨ SeamInternal T e)
    (hN : ∀ e ∈ N.seams, SeamInternal S e ∨ SeamInternal T e)
    (hS : M.restrict S = N.restrict S)
    (hT : M.restrict T = N.restrict T) : M = N := by
  apply PartialMatching.ext
  have hSeamsS : M.restrictedSeams S = N.restrictedSeams S := by
    unfold PartialMatching.restrictedSeams
    rw [hS]
  have hSeamsT : M.restrictedSeams T = N.restrictedSeams T := by
    unfold PartialMatching.restrictedSeams
    rw [hT]
  calc
    M.seams = M.restrictedSeams S ∪ M.restrictedSeams T :=
      (M.restrictedSeams_union_eq_of_internal S T hM).symm
    _ = N.restrictedSeams S ∪ N.restrictedSeams T := by
      rw [hSeamsS, hSeamsT]
    _ = N.seams := N.restrictedSeams_union_eq_of_internal S T hN

/-- Reassembling the two restrictions of a matching with no crossing seam
recovers the original matching. -/
theorem reassembleMatching_restrict
    (S T : Set Cell) (hdisj : Disjoint S T)
    (M : PartialMatching (CellDart Cell facets))
    (hint : ∀ e ∈ M.seams, SeamInternal S e ∨ SeamInternal T e) :
    reassembleMatching S T hdisj (M.restrict S) (M.restrict T) = M := by
  apply PartialMatching.eq_of_restrict_eq_of_internal _ _ S T
  · exact seamInternal_reassembleMatching S T hdisj (M.restrict S) (M.restrict T)
  · exact hint
  · exact restrict_reassembleMatching_left S T hdisj (M.restrict S) (M.restrict T)
  · exact restrict_reassembleMatching_right S T hdisj (M.restrict S) (M.restrict T)

/-- Restriction and reassembly are mutually inverse at the level of partial
matchings with no crossing seam.  The domain remembers the internal-side
condition needed for the inverse law. -/
noncomputable def matchingRestrictionEquiv
    (S T : Set Cell) (hdisj : Disjoint S T) :
    {M : PartialMatching (CellDart Cell facets) //
        ∀ e ∈ M.seams, SeamInternal S e ∨ SeamInternal T e} ≃
      PartialMatching (RestrictedDart (facets := facets) S) ×
        PartialMatching (RestrictedDart (facets := facets) T) where
  toFun M := (M.1.restrict S, M.1.restrict T)
  invFun MN := ⟨reassembleMatching S T hdisj MN.1 MN.2,
    seamInternal_reassembleMatching S T hdisj MN.1 MN.2⟩
  left_inv M := by
    apply Subtype.ext
    exact reassembleMatching_restrict S T hdisj M.1 M.2
  right_inv MN := by
    apply Prod.ext
    · exact restrict_reassembleMatching_left S T hdisj MN.1 MN.2
    · exact restrict_reassembleMatching_right S T hdisj MN.1 MN.2

/-- A bridge certificate supplies exactly the covering and no-crossing
hypotheses required by `restrictedSeams_union_eq`. -/
theorem bridge_restrictedSeams_union_eq
    (P : ColoredMatching (CellDart Cell facets) r) (a b : Cell)
    (C : BridgePartition.Certificate (P.Adjacent facets) a b) :
    P.matching.restrictedSeams (BridgePartition.LeftClass (P.Adjacent facets) a) ∪
        P.matching.restrictedSeams
          (BridgePartition.RightClass (P.Adjacent facets) b) =
      P.matching.seams := by
  apply restrictedSeams_union_eq P _ _ C.cover
  intro u hu v hv
  exact C.no_left_right ⟨u, hu⟩ ⟨v, hv⟩

/-- A bridge certificate also gives the exact additive seam-count split. -/
theorem bridge_restricted_seam_counts_add
    (P : ColoredMatching (CellDart Cell facets) r) (a b : Cell)
    (C : BridgePartition.Certificate (P.Adjacent facets) a b) :
    (P.matching.restrict
        (BridgePartition.LeftClass (P.Adjacent facets) a)).seams.card +
      (P.matching.restrict
        (BridgePartition.RightClass (P.Adjacent facets) b)).seams.card =
      P.matching.seams.card := by
  apply restricted_seam_counts_add P _ _ C.cover C.disjoint
  intro u hu v hv
  exact C.no_left_right ⟨u, hu⟩ ⟨v, hv⟩

/-! ## Coloured restrictions -/

namespace ColoredMatching

/-- Restrict both the matching and its seam colours to `S`. -/
noncomputable def restrict
    (P : ColoredMatching (CellDart Cell facets) r) (S : Set Cell) :
    ColoredMatching (RestrictedDart (facets := facets) S) r where
  matching := P.matching.restrict S
  color e := P.color
    ⟨includeSeam (facets := facets) S e.1,
      (P.matching.mem_restrict_seams S e.1).mp e.2⟩

/-- A local seam, viewed as an ambient seam of `P`. -/
def includeRestrictedSeam
    (P : ColoredMatching (CellDart Cell facets) r) (S : Set Cell)
    (e : (P.restrict S).Seam) : P.Seam :=
  ⟨includeSeam (facets := facets) S e.1,
    (P.matching.mem_restrict_seams S e.1).mp e.2⟩

@[simp]
theorem color_restrict
    (P : ColoredMatching (CellDart Cell facets) r) (S : Set Cell)
    (e : (P.restrict S).Seam) :
    (P.restrict S).color e = P.color (P.includeRestrictedSeam S e) := rfl

/-- An ambient seam internal to `S`, as a seam of the restricted matching. -/
def liftRestrictedSeam
    (P : ColoredMatching (CellDart Cell facets) r) (S : Set Cell)
    (e : P.Seam) (hint : SeamInternal S e.1) : (P.restrict S).Seam :=
  ⟨liftInternalSeam S e.1 hint,
    (P.matching.mem_restrict_seams S _).mpr (by
      simpa using e.2)⟩

/-- Restriction and lifting preserve the colour of every internal seam. -/
theorem color_liftRestrictedSeam
    (P : ColoredMatching (CellDart Cell facets) r) (S : Set Cell)
    (e : P.Seam) (hint : SeamInternal S e.1) :
    (P.restrict S).color (P.liftRestrictedSeam S e hint) = P.color e := by
  change P.color
      ⟨includeSeam (facets := facets) S (liftInternalSeam S e.1 hint), _⟩ =
    P.color e
  congr 1
  exact Subtype.ext (includeSeam_liftInternalSeam S e.1 hint)

/-- Dual adjacency of a restriction is exactly the relation induced from the
ambient dual adjacency.  This is the key fact needed to transport the
connectedness part of a bridge certificate to the two concrete restricted
matchings. -/
theorem adjacent_restrict_iff
    (P : ColoredMatching (CellDart Cell facets) r) (S : Set Cell)
    (u v : S) :
    (P.restrict S).Adjacent (fun c : S ↦ facets c.1) u v ↔
      P.Adjacent facets u.1 v.1 := by
  constructor
  · rintro ⟨i, j, hij⟩
    refine ⟨i, j, ?_⟩
    have himage :
        includeSeam (facets := facets) S
            s(⟨u, i⟩, ⟨v, j⟩) =
          s(⟨u.1, i⟩, ⟨v.1, j⟩) := by
      simp [includeSeam, includeDart]
    have hamb := (P.matching.mem_restrict_seams S
      s(⟨u, i⟩, ⟨v, j⟩)).mp hij
    simpa only [himage] using hamb
  · rintro ⟨i, j, hij⟩
    refine ⟨i, j, ?_⟩
    apply (P.matching.mem_restrict_seams S
      s(⟨u, i⟩, ⟨v, j⟩)).mpr
    simpa [includeSeam, includeDart] using hij

/-- Any proof that the ambient induced relation on `S` is connected yields
connectedness of the concrete coloured restriction. -/
theorem restrict_isConnected_of_induced
    (P : ColoredMatching (CellDart Cell facets) r) (S : Set Cell)
    (hconn : ∀ u v : S,
      Relation.ReflTransGen (fun x y : S ↦ P.Adjacent facets x.1 y.1) u v) :
    (P.restrict S).IsConnected (fun c : S ↦ facets c.1) := by
  intro u v
  exact (hconn u v).mapRelation fun x y hxy ↦
    (P.adjacent_restrict_iff S x y).mpr hxy

end ColoredMatching

/-! ## Concrete bridge components -/

/-- The left restriction supplied by a bridge certificate is connected. -/
theorem bridge_left_restriction_connected
    (P : ColoredMatching (CellDart Cell facets) r) (a b : Cell)
    (C : BridgePartition.Certificate (P.Adjacent facets) a b) :
    (P.restrict (BridgePartition.LeftClass (P.Adjacent facets) a)).IsConnected
      (fun c : BridgePartition.LeftClass (P.Adjacent facets) a ↦
        facets c.1) := by
  apply P.restrict_isConnected_of_induced
  exact C.left_induced_connected

/-- The right restriction supplied by a bridge certificate is connected. -/
theorem bridge_right_restriction_connected
    (P : ColoredMatching (CellDart Cell facets) r) (a b : Cell)
    (C : BridgePartition.Certificate (P.Adjacent facets) a b) :
    (P.restrict (BridgePartition.RightClass (P.Adjacent facets) b)).IsConnected
      (fun c : BridgePartition.RightClass (P.Adjacent facets) b ↦
        facets c.1) := by
  apply P.restrict_isConnected_of_induced
  exact C.right_induced_connected

/-- After erasing a genuine bridge from a connected pairing, the two
reachability classes are realized by concrete connected coloured matchings.
Their seam counts add to the erased seam count. -/
theorem erase_bridge_gives_two_connected_restrictions
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam)
    (hconnected : P.IsConnected facets) (hbridge : P.IsBridge e) :
    let Q := P.erase e
    let C := P.bridge_partition e hconnected hbridge
    (Q.restrict (BridgePartition.LeftClass (Q.Adjacent facets) (P.leftCell e))).IsConnected
        (fun c : BridgePartition.LeftClass (Q.Adjacent facets) (P.leftCell e) ↦
          facets c.1) ∧
      (Q.restrict (BridgePartition.RightClass (Q.Adjacent facets) (P.rightCell e))).IsConnected
        (fun c : BridgePartition.RightClass (Q.Adjacent facets) (P.rightCell e) ↦
          facets c.1) ∧
      (Q.matching.restrict
          (BridgePartition.LeftClass (Q.Adjacent facets) (P.leftCell e))).seams.card +
        (Q.matching.restrict
          (BridgePartition.RightClass (Q.Adjacent facets) (P.rightCell e))).seams.card =
        Q.matching.seams.card := by
  dsimp only
  let C := P.bridge_partition e hconnected hbridge
  exact ⟨bridge_left_restriction_connected (P.erase e) _ _ C,
    bridge_right_restriction_connected (P.erase e) _ _ C,
    bridge_restricted_seam_counts_add (P.erase e) _ _ C⟩

end
end FacetPairing
end PolytopeCounting

/-! ## Colour-preserving generic reassembly

The seam-finset reconstruction above is enough for the uncoloured model, but
the recurrence strata carry a gluing colour on every seam.  The following
definitions reconstruct that dependent colour function as well.  They use
the injectivity of `includeSeam`, so the apparently chosen inverse image is
in fact unique.
-/

namespace PolytopeCounting
namespace FacetPairing

noncomputable section

universe uC

variable {Cell : Type uC} [Fintype Cell] [DecidableEq Cell]
  {facets : Cell → ℕ} {r : ℕ}

/-- Recover the unique local seam represented by a member of the ambient
image of a local matching. -/
noncomputable def localSeamOfImage
    (S : Set Cell)
    (M : PartialMatching (RestrictedDart (facets := facets) S))
    (e : Sym2 (CellDart Cell facets))
    (he : e ∈ M.seams.map
      ⟨includeSeam (facets := facets) S,
        includeSeam_injective (facets := facets) S⟩) : M.Seam :=
  ⟨Classical.choose (Finset.mem_map.mp he),
    (Classical.choose_spec (Finset.mem_map.mp he)).1⟩

@[simp]
theorem includeSeam_localSeamOfImage
    (S : Set Cell)
    (M : PartialMatching (RestrictedDart (facets := facets) S))
    (e : Sym2 (CellDart Cell facets))
    (he : e ∈ M.seams.map
      ⟨includeSeam (facets := facets) S,
        includeSeam_injective (facets := facets) S⟩) :
    includeSeam (facets := facets) S (localSeamOfImage S M e he).1 = e :=
  (Classical.choose_spec (Finset.mem_map.mp he)).2

theorem localSeamOfImage_includeSeam
    (S : Set Cell)
    (M : PartialMatching (RestrictedDart (facets := facets) S))
    (e : M.Seam)
    (he : includeSeam (facets := facets) S e.1 ∈ M.seams.map
      ⟨includeSeam (facets := facets) S,
        includeSeam_injective (facets := facets) S⟩) :
    localSeamOfImage S M (includeSeam (facets := facets) S e.1) he = e := by
  apply Subtype.ext
  apply includeSeam_injective (facets := facets) S
  exact includeSeam_localSeamOfImage S M _ he

/-- Reassemble two coloured local matchings.  The disjointness hypothesis
ensures that every ambient seam has exactly one source side, and therefore a
well-defined inherited colour. -/
noncomputable def reassembleColored
    (S T : Set Cell) (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r) :
    ColoredMatching (CellDart Cell facets) r where
  matching := reassembleMatching S T hdisj P.matching Q.matching
  color e :=
    if hS : e.1 ∈ P.matching.seams.map
        ⟨includeSeam (facets := facets) S,
          includeSeam_injective (facets := facets) S⟩ then
      P.color (localSeamOfImage S P.matching e.1 hS)
    else
      Q.color (localSeamOfImage T Q.matching e.1 (by
        have he : e.1 ∈
            P.matching.seams.map
                ⟨includeSeam (facets := facets) S,
                  includeSeam_injective (facets := facets) S⟩ ∪
              Q.matching.seams.map
                ⟨includeSeam (facets := facets) T,
                  includeSeam_injective (facets := facets) T⟩ := by
          simpa only [seams_reassembleMatching] using e.2
        exact (Finset.mem_union.mp he).resolve_left hS))

/-- A left local seam, regarded as a seam of the coloured reassembly. -/
def reassembleColoredLeftSeam
    (S T : Set Cell) (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (e : P.Seam) : (reassembleColored S T hdisj P Q).Seam :=
  ⟨includeSeam (facets := facets) S e.1, by
    rw [show (reassembleColored S T hdisj P Q).matching.seams =
        (reassembleMatching S T hdisj P.matching Q.matching).seams from rfl,
      seams_reassembleMatching]
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_map.mpr ⟨e.1, e.2, rfl⟩))⟩

/-- A right local seam, regarded as a seam of the coloured reassembly. -/
def reassembleColoredRightSeam
    (S T : Set Cell) (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (e : Q.Seam) : (reassembleColored S T hdisj P Q).Seam :=
  ⟨includeSeam (facets := facets) T e.1, by
    rw [show (reassembleColored S T hdisj P Q).matching.seams =
        (reassembleMatching S T hdisj P.matching Q.matching).seams from rfl,
      seams_reassembleMatching]
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_map.mpr ⟨e.1, e.2, rfl⟩))⟩

/-- Reassembly preserves every colour on the left. -/
@[simp]
theorem color_reassembleColored_left
    (S T : Set Cell) (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (e : P.Seam) :
    (reassembleColored S T hdisj P Q).color
        (reassembleColoredLeftSeam S T hdisj P Q e) = P.color e := by
  have hmem : includeSeam (facets := facets) S e.1 ∈
      P.matching.seams.map
        ⟨includeSeam (facets := facets) S,
          includeSeam_injective (facets := facets) S⟩ :=
    Finset.mem_map.mpr ⟨e.1, e.2, rfl⟩
  change (if hS : includeSeam (facets := facets) S e.1 ∈
      P.matching.seams.map
        ⟨includeSeam (facets := facets) S,
          includeSeam_injective (facets := facets) S⟩ then
        P.color (localSeamOfImage S P.matching _ hS)
      else _) = P.color e
  rw [dif_pos hmem]
  congr 1
  exact localSeamOfImage_includeSeam S P.matching e hmem

/-- Reassembly preserves every colour on the right. -/
@[simp]
theorem color_reassembleColored_right
    (S T : Set Cell) (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r)
    (e : Q.Seam) :
    (reassembleColored S T hdisj P Q).color
        (reassembleColoredRightSeam S T hdisj P Q e) = Q.color e := by
  have hnot : includeSeam (facets := facets) T e.1 ∉
      P.matching.seams.map
        ⟨includeSeam (facets := facets) S,
          includeSeam_injective (facets := facets) S⟩ := by
    intro hmem
    obtain ⟨eS, heS, hEq⟩ := Finset.mem_map.mp hmem
    exact includeSeam_ne_of_disjoint S T hdisj eS e.1 hEq
  change (if hS : includeSeam (facets := facets) T e.1 ∈
      P.matching.seams.map
        ⟨includeSeam (facets := facets) S,
          includeSeam_injective (facets := facets) S⟩ then _
      else Q.color (localSeamOfImage T Q.matching _ _)) = Q.color e
  rw [dif_neg hnot]
  congr 1
  apply Subtype.ext
  apply includeSeam_injective (facets := facets) T
  exact includeSeam_localSeamOfImage T Q.matching _ _

/-- Equality of coloured matchings transports the colour of a seam along
the induced equality of underlying seam finsets. -/
theorem ColoredMatching.color_eq_of_eq
    {D : Type*} [DecidableEq D]
    {P Q : ColoredMatching D r} (h : P = Q) (e : P.Seam) :
    P.color e = Q.color ⟨e.1, congrArg ColoredMatching.matching h ▸ e.2⟩ := by
  subst Q
  rfl

/-- Restriction is a left inverse to coloured reassembly on the left
component, including the dependent seam-colour function. -/
theorem ColoredMatching.restrict_reassembleColored_left
    (S T : Set Cell) (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r) :
    (reassembleColored S T hdisj P Q).restrict S = P := by
  let hmatching :
      ((reassembleColored S T hdisj P Q).restrict S).matching = P.matching :=
    restrict_reassembleMatching_left S T hdisj P.matching Q.matching
  refine ColoredMatching.ext hmatching ?_
  intro e
  let eP : P.Seam := ⟨e.1, hmatching ▸ e.2⟩
  have hseam :
      (reassembleColored S T hdisj P Q).includeRestrictedSeam S e =
        reassembleColoredLeftSeam S T hdisj P Q eP := by
    apply Subtype.ext
    rfl
  change (reassembleColored S T hdisj P Q).color
      ((reassembleColored S T hdisj P Q).includeRestrictedSeam S e) =
    P.color eP
  rw [hseam]
  exact color_reassembleColored_left S T hdisj P Q eP

/-- Restriction is a left inverse to coloured reassembly on the right
component. -/
theorem ColoredMatching.restrict_reassembleColored_right
    (S T : Set Cell) (hdisj : Disjoint S T)
    (P : ColoredMatching (RestrictedDart (facets := facets) S) r)
    (Q : ColoredMatching (RestrictedDart (facets := facets) T) r) :
    (reassembleColored S T hdisj P Q).restrict T = Q := by
  let hmatching :
      ((reassembleColored S T hdisj P Q).restrict T).matching = Q.matching :=
    restrict_reassembleMatching_right S T hdisj P.matching Q.matching
  refine ColoredMatching.ext hmatching ?_
  intro e
  let eQ : Q.Seam := ⟨e.1, hmatching ▸ e.2⟩
  have hseam :
      (reassembleColored S T hdisj P Q).includeRestrictedSeam T e =
        reassembleColoredRightSeam S T hdisj P Q eQ := by
    apply Subtype.ext
    rfl
  change (reassembleColored S T hdisj P Q).color
      ((reassembleColored S T hdisj P Q).includeRestrictedSeam T e) =
    Q.color eQ
  rw [hseam]
  exact color_reassembleColored_right S T hdisj P Q eQ

/-- The two restrictions of a coloured matching determine it uniquely once
all seams of both candidates are internal to one side of the partition. -/
theorem ColoredMatching.eq_of_restrict_eq_of_internal
    (P Q : ColoredMatching (CellDart Cell facets) r)
    (S T : Set Cell)
    (hP : ∀ e ∈ P.matching.seams,
      SeamInternal S e ∨ SeamInternal T e)
    (hQ : ∀ e ∈ Q.matching.seams,
      SeamInternal S e ∨ SeamInternal T e)
    (hS : P.restrict S = Q.restrict S)
    (hT : P.restrict T = Q.restrict T) : P = Q := by
  have hmS : (P.restrict S).matching = (Q.restrict S).matching :=
    congrArg ColoredMatching.matching hS
  have hmT : (P.restrict T).matching = (Q.restrict T).matching :=
    congrArg ColoredMatching.matching hT
  have hm : P.matching = Q.matching :=
    PartialMatching.eq_of_restrict_eq_of_internal
      P.matching Q.matching S T hP hQ hmS hmT
  refine ColoredMatching.ext hm ?_
  intro e
  let eQ : Q.Seam := ⟨e.1, hm ▸ e.2⟩
  rcases hP e.1 e.2 with heS | heT
  · let ePS : (P.restrict S).Seam := P.liftRestrictedSeam S e heS
    let eQS : (Q.restrict S).Seam := Q.liftRestrictedSeam S eQ heS
    have hlocal :
        ⟨ePS.1, congrArg ColoredMatching.matching hS ▸ ePS.2⟩ = eQS := by
      apply Subtype.ext
      rfl
    calc
      P.color e = (P.restrict S).color ePS :=
        (P.color_liftRestrictedSeam S e heS).symm
      _ = (Q.restrict S).color
          ⟨ePS.1, congrArg ColoredMatching.matching hS ▸ ePS.2⟩ :=
        ColoredMatching.color_eq_of_eq hS ePS
      _ = (Q.restrict S).color eQS := by rw [hlocal]
      _ = Q.color eQ := Q.color_liftRestrictedSeam S eQ heS
  · let ePT : (P.restrict T).Seam := P.liftRestrictedSeam T e heT
    let eQT : (Q.restrict T).Seam := Q.liftRestrictedSeam T eQ heT
    have hlocal :
        ⟨ePT.1, congrArg ColoredMatching.matching hT ▸ ePT.2⟩ = eQT := by
      apply Subtype.ext
      rfl
    calc
      P.color e = (P.restrict T).color ePT :=
        (P.color_liftRestrictedSeam T e heT).symm
      _ = (Q.restrict T).color
          ⟨ePT.1, congrArg ColoredMatching.matching hT ▸ ePT.2⟩ :=
        ColoredMatching.color_eq_of_eq hT ePT
      _ = (Q.restrict T).color eQT := by rw [hlocal]
      _ = Q.color eQ := Q.color_liftRestrictedSeam T eQ heT

/-- Reassembling both restrictions recovers the complete coloured matching,
not only its seam finset. -/
theorem ColoredMatching.reassembleColored_restrict
    (P : ColoredMatching (CellDart Cell facets) r)
    (S T : Set Cell) (hdisj : Disjoint S T)
    (hint : ∀ e ∈ P.matching.seams,
      SeamInternal S e ∨ SeamInternal T e) :
    reassembleColored S T hdisj (P.restrict S) (P.restrict T) = P := by
  apply ColoredMatching.eq_of_restrict_eq_of_internal _ _ S T
  · exact seamInternal_reassembleMatching S T hdisj
      (P.restrict S).matching (P.restrict T).matching
  · exact hint
  · exact ColoredMatching.restrict_reassembleColored_left S T hdisj
      (P.restrict S) (P.restrict T)
  · exact ColoredMatching.restrict_reassembleColored_right S T hdisj
      (P.restrict S) (P.restrict T)

/-- Ambient coloured matchings all of whose seams lie on one of the two
specified sides. -/
def IsInternalToPartition
    (S T : Set Cell)
    (P : ColoredMatching (CellDart Cell facets) r) : Prop :=
  ∀ e ∈ P.matching.seams, SeamInternal S e ∨ SeamInternal T e

/-- The exact cut--reassemble equivalence for a fixed disjoint pair of cell
sets.  This is a genuine equivalence of finite object types, not merely an
equality of seam counts.  It remembers every seam and every colour. -/
noncomputable def reassembleColoredEquiv
    (S T : Set Cell) (hdisj : Disjoint S T) :
    (ColoredMatching (RestrictedDart (facets := facets) S) r ×
        ColoredMatching (RestrictedDart (facets := facets) T) r) ≃
      {P : ColoredMatching (CellDart Cell facets) r //
        IsInternalToPartition S T P} where
  toFun X := ⟨reassembleColored S T hdisj X.1 X.2, by
    intro e he
    exact seamInternal_reassembleMatching S T hdisj
      X.1.matching X.2.matching e he⟩
  invFun P := ⟨P.1.restrict S, P.1.restrict T⟩
  left_inv X := by
    apply Prod.ext
    · exact ColoredMatching.restrict_reassembleColored_left
        S T hdisj X.1 X.2
    · exact ColoredMatching.restrict_reassembleColored_right
        S T hdisj X.1 X.2
  right_inv P := by
    apply Subtype.ext
    exact P.1.reassembleColored_restrict S T hdisj P.2

/-- The inverse of `reassembleColoredEquiv` is literally the ordered pair of
the two induced coloured restrictions. -/
@[simp]
theorem reassembleColoredEquiv_symm_apply
    (S T : Set Cell) (hdisj : Disjoint S T)
    (P : {P : ColoredMatching (CellDart Cell facets) r //
      IsInternalToPartition S T P}) :
    (reassembleColoredEquiv (facets := facets) (r := r) S T hdisj).symm P =
      ⟨P.1.restrict S, P.1.restrict T⟩ := rfl

/-- Cutting an actual marked bridge and reassembling its two induced
coloured components recovers the complete erased diagram exactly. -/
theorem erase_bridge_reassemble_exact
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam)
    (hconnected : P.IsConnected facets) (hbridge : P.IsBridge e) :
    let Q := P.erase e
    let C := P.bridge_partition e hconnected hbridge
    let S := BridgePartition.LeftClass
      (Q.Adjacent facets) (P.leftCell e)
    let T := BridgePartition.RightClass
      (Q.Adjacent facets) (P.rightCell e)
    reassembleColored S T C.disjoint (Q.restrict S) (Q.restrict T) = Q := by
  dsimp only
  let Q := P.erase e
  let C := P.bridge_partition e hconnected hbridge
  let S := BridgePartition.LeftClass
    (Q.Adjacent facets) (P.leftCell e)
  let T := BridgePartition.RightClass
    (Q.Adjacent facets) (P.rightCell e)
  apply Q.reassembleColored_restrict S T C.disjoint
  intro f hf
  apply seam_internal_left_or_right Q S T C.cover
  · intro u hu v hv
    exact C.no_left_right ⟨u, hu⟩ ⟨v, hv⟩
  · exact hf

/-- Both restrictions are connected,
their seams partition all remaining seams, and their colour-preserving
reassembly is exactly the erased diagram. -/
theorem erase_bridge_full_restriction_reassembly
    (P : ColoredMatching (CellDart Cell facets) r) (e : P.Seam)
    (hconnected : P.IsConnected facets) (hbridge : P.IsBridge e) :
    let Q := P.erase e
    let C := P.bridge_partition e hconnected hbridge
    let S := BridgePartition.LeftClass
      (Q.Adjacent facets) (P.leftCell e)
    let T := BridgePartition.RightClass
      (Q.Adjacent facets) (P.rightCell e)
    (Q.restrict S).IsConnected (fun c : S ↦ facets c.1) ∧
      (Q.restrict T).IsConnected (fun c : T ↦ facets c.1) ∧
      (Q.matching.restrict S).seams.card +
          (Q.matching.restrict T).seams.card = Q.matching.seams.card ∧
      reassembleColored S T C.disjoint (Q.restrict S) (Q.restrict T) = Q := by
  dsimp only
  let Q := P.erase e
  let C := P.bridge_partition e hconnected hbridge
  refine ⟨bridge_left_restriction_connected Q _ _ C,
    bridge_right_restriction_connected Q _ _ C,
    bridge_restricted_seam_counts_add Q _ _ C, ?_⟩
  exact erase_bridge_reassemble_exact P e hconnected hbridge

end
end FacetPairing
end PolytopeCounting
