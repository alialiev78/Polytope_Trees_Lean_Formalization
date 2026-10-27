module

public import Proofs.SupportingFaceFlags

@[expose] public section

/-!
# Transport and rigidity of the concrete flags

Injective affine maps preserve supporting faces and their maximality, including
inclusions of intrinsic facet spaces. Rigidity is proved from the centroids of
the actual faces: no equivariant affine basis is supplied as an assumption.

-/

namespace PolytopeCounting.FacetPairing.EuclideanGeometry.GeometricFlags
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

variable {V E W E' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MetricSpace E'] [NormedAddTorsor W E']

/-- An affine left inverse of an injective affine map, constructed by splitting
its linear part. It is used only on the embedded finite polytope. -/
def affineLeftInverse (f : E →ᵃ[ℝ] E') : E' →ᵃ[ℝ] E :=
  let p : E := Classical.choice (inferInstance : Nonempty E)
  AffineMap.mk' (fun y ↦ f.linear.leftInverse (y -ᵥ f p) +ᵥ p)
    f.linear.leftInverse (f p) (by intro y; simp)

@[simp] theorem affineLeftInverse_apply (f : E →ᵃ[ℝ] E')
    (hf : Function.Injective f) (x : E) : affineLeftInverse f (f x) = x := by
  let p : E := Classical.choice (inferInstance : Nonempty E)
  have hk : LinearMap.ker f.linear = ⊥ :=
    LinearMap.ker_eq_bot.mpr ((AffineMap.linear_injective_iff f).mpr hf)
  change f.linear.leftInverse (f x -ᵥ f p) +ᵥ p = x
  rw [← f.linearMap_vsub x p,
    LinearMap.leftInverse_apply_of_inj hk, vsub_vadd]

/-- Affine centroid transport. The target centroid is taken over the image set,
not over a potentially different list of multiplicities. -/
theorem map_centroid (f : E →ᵃ[ℝ] E') (hf : Function.Injective f)
    (s : Finset E) (hs : s.Nonempty) :
    f (s.centroid ℝ id) = (s.image f).centroid ℝ id := by
  change f (s.affineCombination ℝ id (s.centroidWeights ℝ)) = _
  rw [Finset.map_affineCombination _ _ _
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  change s.centroid ℝ (fun x ↦ f x) = (s.image f).centroid ℝ id
  apply Finset.centroid_eq_of_inj_on_of_image_eq
  · intro x _ y _ h
    exact hf h
  · intro x _ y _ h
    exact h
  · ext y
    simp

/-- Supporting faces are preserved by affine embeddings into a larger ambient
space; an affine left inverse extends the exposing functional. -/
theorem Supported.map {s t : Finset E} (H : Supported s t)
    (f : E →ᵃ[ℝ] E') (hf : Function.Injective f) :
    Supported (s.image f) (t.image f) := by
  rcases H with ⟨ht, a, ha, hv, x, hx, hlt⟩
  refine ⟨ht.image f, a.comp (affineLeftInverse f), ?_, ?_, f x,
    Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    simpa [affineLeftInverse_apply f hf] using ha z hz
  · intro y
    constructor
    · rintro hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hzs, hza⟩ := (hv z).mp hz
      exact ⟨Finset.mem_image.mpr ⟨z, hzs, rfl⟩, by simpa [affineLeftInverse_apply f hf] using hza⟩
    · rintro ⟨hy, hya⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have hza : a z = 0 := by simpa [affineLeftInverse_apply f hf] using hya
      exact Finset.mem_image.mpr ⟨z, (hv z).mpr ⟨hz, hza⟩, rfl⟩
  · simpa [affineLeftInverse_apply f hf] using hlt

/-- Pull a supporting face back from an embedded polytope. -/
theorem Supported.pullback {s : Finset E} {u : Finset E'}
    (f : E →ᵃ[ℝ] E') (H : Supported (s.image f) u) :
    Supported s (s.filter (fun x ↦ f x ∈ u)) := by
  rcases H with ⟨hu, a, ha, hv, y, hy, hlt⟩
  obtain ⟨z, hz⟩ := hu
  obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp (((hv z).mp hz).1)
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  refine ⟨⟨x, by simp [hx, hfx, hz]⟩, a.comp f, ?_, ?_, w, hw, hlt⟩
  · intro v hv'
    exact ha (f v) (Finset.mem_image.mpr ⟨v, hv', rfl⟩)
  · intro v
    simp only [Finset.mem_filter, AffineMap.comp_apply]
    constructor
    · rintro ⟨hvs, hvu⟩
      exact ⟨hvs, ((hv (f v)).mp hvu).2⟩
    · rintro ⟨hvs, hav⟩
      exact ⟨hvs, (hv (f v)).mpr
        ⟨Finset.mem_image.mpr ⟨v, hvs, rfl⟩, hav⟩⟩

theorem image_pullback {s : Finset E} {u : Finset E'}
    (f : E →ᵃ[ℝ] E') (hu : u ⊆ s.image f) :
    (s.filter (fun x ↦ f x ∈ u)).image f = u := by
  ext y
  constructor
  · rintro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hx).2
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hu hy)
    exact Finset.mem_image.mpr ⟨x, by simp [hx, hy], rfl⟩

/-- Maximality is transported rather than assumed. -/
theorem Facet.map {s t : Finset E} (H : Facet s t)
    (f : E →ᵃ[ℝ] E') (hf : Function.Injective f) :
    Facet (s.image f) (t.image f) := by
  refine ⟨H.1.map f hf, ?_⟩
  intro u hu htu
  let v := s.filter (fun x ↦ f x ∈ u)
  have hv : Supported s v := hu.pullback f
  have htv : t ⊆ v := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨H.1.subset hx,
      htu (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
  have hvt := H.2 v hv htv
  have him := image_pullback f hu.subset
  change v.image f = u at him
  rw [hvt] at him
  exact him.symm

/-- Ordinary image of a list of face vertex sets. -/
def mapChain (f : E → E') (l : List (Finset E)) : List (Finset E') :=
  l.map (fun s ↦ s.image f)

@[simp] theorem mapChain_cons (f : E → E') (s : Finset E) (l : List (Finset E)) :
    mapChain f (s :: l) = s.image f :: mapChain f l := rfl

@[simp] theorem mapChain_comp {E'' : Type*}
    (g : E' → E'') (f : E → E') (l : List (Finset E)) :
    mapChain g (mapChain f l) = mapChain (g ∘ f) l := by
  simp [mapChain, List.map_map, Function.comp_def, Finset.image_image]

/-- Including intrinsic face sets into ambient space loses no flag data. -/
theorem mapChain_injective (f : E → E') (hf : Function.Injective f) :
    Function.Injective (mapChain f) := by
  have himage : Function.Injective (fun u : Finset E ↦ u.image f) := by
    intro u v he
    change u.image f = v.image f at he
    apply Finset.Subset.antisymm
    · intro x hx
      have hx' : f x ∈ v.image f := he ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hfy⟩ := Finset.mem_image.mp hx'
      exact hf hfy ▸ hy
    · intro x hx
      have hx' : f x ∈ u.image f := he.symm ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hfy⟩ := Finset.mem_image.mp hx'
      exact hf hfy ▸ hy
  intro a
  induction a with
  | nil =>
    intro b he
    cases b with
    | nil => rfl
    | cons u b => simp [mapChain] at he
  | cons u a ih =>
    intro b he
    cases b with
    | nil => simp [mapChain] at he
    | cons v b =>
      have hh := List.cons.inj he
      have huv := himage hh.1
      subst v
      exact congrArg (List.cons u) (ih hh.2)

theorem CompleteChain.map {l : List (Finset E)} (H : CompleteChain l)
    (f : E →ᵃ[ℝ] E') (hf : Function.Injective f) :
    CompleteChain (mapChain f l) := by
  induction H with
  | point x => simpa [mapChain] using CompleteChain.point (f x)
  | step h ht ih => exact CompleteChain.step (h.map f hf) ih

/-- The centroids along an actual full flag form a determining set for affine
maps. This theorem derives rigidity from maximal supporting faces. -/
theorem CompleteChain.maps_agree {l : List (Finset E)} (H : CompleteChain l)
    (f g : E →ᵃ[ℝ] E') (hf : Function.Injective f) (hg : Function.Injective g)
    (he : mapChain f l = mapChain g l) :
    ∀ s ∈ l, Set.EqOn f g (affineSpan ℝ (s : Set E)) := by
  revert he
  induction H with
  | point x =>
    intro he
    have he' : f x = g x := by simpa [mapChain] using he
    intro s hs
    have hs' : s = {x} := by simpa using hs
    subst s
    apply AffineMap.eqOn_affineSpan
    intro y hy
    have : y = x := by simpa using hy
    simpa [this] using he'
  | @step s t l h ht ih =>
    intro he
    have hcons := List.cons.inj he
    have htail := ih hcons.2
    have hcent : f (s.centroid ℝ id) = g (s.centroid ℝ id) := by
      rw [map_centroid f hf s h.1.parent_nonempty,
        map_centroid g hg s h.1.parent_nonempty]
      exact congrArg (fun u : Finset E' ↦ u.centroid ℝ id) hcons.1
    have hon : Set.EqOn f g (affineSpan ℝ (s : Set E)) := by
      rw [← h.span_with_centroid]
      apply AffineMap.eqOn_affineSpan
      intro x hx
      rcases hx with rfl | hx
      · exact hcent
      · exact htail t (List.mem_cons_self) (subset_affineSpan ℝ _ hx)
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hon
    · exact htail u hu

/-- Equality of the image flags forces equality on the parent affine span. -/
theorem FullFlag.maps_agree {s : Finset E} (A : FullFlag s)
    (f g : E →ᵃ[ℝ] E') (hf : Function.Injective f) (hg : Function.Injective g)
    (he : mapChain f (s :: A.1) = mapChain g (s :: A.1)) :
    Set.EqOn f g (affineSpan ℝ (s : Set E)) :=
  A.2.maps_agree f g hf hg he s (List.mem_cons_self)

/-- Transport a flag when the image of its top face has been identified. -/
def FullFlag.map {s : Finset E} {t : Finset E'} (A : FullFlag s)
    (f : E →ᵃ[ℝ] E') (hf : Function.Injective f) (he : s.image f = t) :
    FullFlag t :=
  ⟨mapChain f A.1, by
    simpa only [mapChain_cons, he] using A.2.map f hf⟩

/-- Geometric regularity in the ordinary flag-transitivity sense. No
restriction-surjectivity, facet rigidity, frames or orientation data is input. -/
def IsFlagRegular (s : Finset E) : Prop :=
  ∀ A B : FullFlag s, ∃ g : symmetryGroup s,
    mapChain g.1 (s :: A.1) = s :: B.1

/-- A useful setwise-preservation test for an injective map. -/
theorem preserves_finset_of_image (f : E → E') (hf : Function.Injective f)
    {t : Finset E} {u : Finset E'} (he : t.image f = u) (x : E) :
    f x ∈ u ↔ x ∈ t := by
  rw [← he]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    exact hf heq ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end
end PolytopeCounting.FacetPairing.EuclideanGeometry.GeometricFlags
