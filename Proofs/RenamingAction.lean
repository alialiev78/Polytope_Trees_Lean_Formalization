module

public import Proofs.FacetPairingModel
public import Mathlib.Algebra.Group.Action.End

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-!
# The wreath-style renaming group

For a finite type `I` of cells and a local symmetry group `L`, a renaming
consists of a permutation of the cells and one local symmetry at every cell.
The multiplication below is the (imprimitive) wreath-product multiplication.
It is chosen so that the displayed action on cell--facet darts is a left
action.

This file deliberately constructs the group and its action rather than using
an abstract cardinality certificate.  It therefore fixes the precise
renaming group which is to be divided out in the later groupoid-mass
calculation.
-/

namespace PolytopeCounting
namespace Renaming

universe uI uL uF

/-- Wreath-style renamings: a permutation of the cells and a local symmetry
at each cell. -/
@[ext]
structure WreathRenaming (I : Type uI) (L : Type uL) where
  cell : Equiv.Perm I
  slot : I → L

namespace WreathRenaming

variable {I : Type uI} {L : Type uL}

instance [Group L] : Mul (WreathRenaming I L) where
  mul a b :=
    ⟨a.cell * b.cell, fun i ↦ a.slot (b.cell i) * b.slot i⟩

instance [Group L] : One (WreathRenaming I L) where
  one := ⟨1, fun _ ↦ 1⟩

instance [Group L] : Inv (WreathRenaming I L) where
  inv a :=
    ⟨a.cell⁻¹, fun i ↦ (a.slot (a.cell⁻¹ i))⁻¹⟩

@[simp]
theorem cell_mul [Group L] (a b : WreathRenaming I L) :
    (a * b).cell = a.cell * b.cell := rfl

@[simp]
theorem slot_mul [Group L] (a b : WreathRenaming I L) (i : I) :
    (a * b).slot i = a.slot (b.cell i) * b.slot i := rfl

@[simp]
theorem cell_one [Group L] : (1 : WreathRenaming I L).cell = 1 := rfl

@[simp]
theorem slot_one [Group L] (i : I) :
    (1 : WreathRenaming I L).slot i = 1 := rfl

@[simp]
theorem cell_inv [Group L] (a : WreathRenaming I L) :
    a⁻¹.cell = a.cell⁻¹ := rfl

@[simp]
theorem slot_inv [Group L] (a : WreathRenaming I L) (i : I) :
    a⁻¹.slot i = (a.slot (a.cell⁻¹ i))⁻¹ := rfl

/-- The wreath multiplication really defines a group. -/
instance [Group L] : Group (WreathRenaming I L) where
  mul_assoc a b c := by
    ext i
    · simp
    · simp [mul_assoc]
  one_mul a := by
    ext i
    · simp
    · simp
  mul_one a := by
    ext i
    · simp
    · simp
  inv_mul_cancel a := by
    ext i
    · simp
    · simp

/-- Forgetting multiplication identifies the renaming group with the product
of the cell permutation type and the family of local symmetries. -/
def dataEquiv :
    WreathRenaming I L ≃ Equiv.Perm I × (I → L) where
  toFun a := (a.cell, a.slot)
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instFintype [Fintype I] [Fintype L] :
    Fintype (WreathRenaming I L) := by
  classical
  exact Fintype.ofEquiv (Equiv.Perm I × (I → L)) dataEquiv.symm

/-- Order of the wreath-style renaming group. -/
theorem card [Fintype I] [Fintype L] :
    Fintype.card (WreathRenaming I L) =
      (Fintype.card I).factorial *
        (Fintype.card L) ^ Fintype.card I := by
  classical
  rw [Fintype.card_congr dataEquiv]
  simp [Fintype.card_perm]

variable (F : Type uF) [Group L] [MulAction L F]

/-- The actual permutation of cell--facet darts associated with a wreath
renaming. -/
def dartPerm (a : WreathRenaming I L) : Equiv.Perm (Σ _ : I, F) where
  toFun x := ⟨a.cell x.1, a.slot x.1 • x.2⟩
  invFun x :=
    ⟨a.cell⁻¹ x.1, (a.slot (a.cell⁻¹ x.1))⁻¹ • x.2⟩
  left_inv x := by
    cases x with
    | mk i f => simp
  right_inv x := by
    cases x with
    | mk i f => simp

@[simp]
theorem dartPerm_apply (a : WreathRenaming I L) (i : I) (f : F) :
    dartPerm F a ⟨i, f⟩ = ⟨a.cell i, a.slot i • f⟩ := rfl

@[simp]
theorem dartPerm_one :
    dartPerm F (1 : WreathRenaming I L) = 1 := by
  apply Equiv.ext
  rintro ⟨i, f⟩
  simp [dartPerm]

@[simp]
theorem dartPerm_mul (a b : WreathRenaming I L) :
    dartPerm F (a * b) = dartPerm F a * dartPerm F b := by
  apply Equiv.ext
  rintro ⟨i, f⟩
  simp [dartPerm, mul_smul]

/-- The dart permutation is a homomorphism, not merely a pointwise formula. -/
def dartPermHom :
    WreathRenaming I L →* Equiv.Perm (Σ _ : I, F) where
  toFun := dartPerm F
  map_one' := dartPerm_one F
  map_mul' := dartPerm_mul F

instance : SMul (WreathRenaming I L) (Σ _ : I, F) where
  smul a x := dartPerm F a x

/-- The wreath group acts on darts. -/
instance : MulAction (WreathRenaming I L) (Σ _ : I, F) where
  one_smul x := by
    change dartPerm F 1 x = x
    rw [dartPerm_one]
    rfl
  mul_smul a b x := by
    change dartPerm F (a * b) x = dartPerm F a (dartPerm F b x)
    rw [dartPerm_mul]
    rfl

end WreathRenaming

/-! ## Transport of concrete partial pairings -/

namespace MatchingTransport

open FacetPairing

universe uD

variable {D : Type uD} [DecidableEq D]

/-- Relabel every dart in a partial matching by a permutation.  This is the
first, structure-preserving lift of the wreath action from darts to pairing
objects: off-diagonality and disjoint incidence are proved rather than
postulated. -/
def renamePartial (sigma : Equiv.Perm D) (M : PartialMatching D) :
    PartialMatching D where
  seams := M.seams.map sigma.toEmbedding.sym2Map
  offDiagonal e he := by
    rcases Finset.mem_map.mp he with ⟨f, hf, rfl⟩
    exact fun hdiag ↦ M.offDiagonal f hf
      ((Sym2.isDiag_map sigma.injective).mp hdiag)
  unique_incidence d e he hde f hf hdf := by
    rcases Finset.mem_map.mp he with ⟨e0, he0, rfl⟩
    rcases Finset.mem_map.mp hf with ⟨f0, hf0, rfl⟩
    rcases Sym2.mem_map.mp hde with ⟨a, ha, had⟩
    rcases Sym2.mem_map.mp hdf with ⟨b, hb, hbd⟩
    have hab : a = b := sigma.injective (had.trans hbd.symm)
    subst b
    exact congrArg (Sym2.map sigma)
      (M.unique_incidence a e0 he0 ha f0 hf0 hb)

@[simp]
theorem seams_renamePartial (sigma : Equiv.Perm D) (M : PartialMatching D) :
    (renamePartial sigma M).seams =
      M.seams.map sigma.toEmbedding.sym2Map := rfl

/-- Relabelling by the identity permutation changes no pairing. -/
@[simp]
theorem renamePartial_one (M : PartialMatching D) :
    renamePartial 1 M = M := by
  apply PartialMatching.ext
  ext e
  simp [renamePartial]

/-- Successive dart relabellings compose in the same order as permutation
multiplication. -/
@[simp]
theorem renamePartial_mul (sigma tau : Equiv.Perm D)
    (M : PartialMatching D) :
    renamePartial (sigma * tau) M =
      renamePartial sigma (renamePartial tau M) := by
  apply PartialMatching.ext
  ext e
  constructor
  · intro he
    rcases Finset.mem_map.mp he with ⟨old, hold, heq⟩
    apply Finset.mem_map.mpr
    refine ⟨Sym2.map tau old, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨old, hold, rfl⟩
    · rw [← heq]
      exact Sym2.map_map old
  · intro he
    rcases Finset.mem_map.mp he with ⟨afterTau, hafter, heq⟩
    rcases Finset.mem_map.mp hafter with ⟨old, hold, htau⟩
    apply Finset.mem_map.mpr
    refine ⟨old, hold, ?_⟩
    rw [← heq, ← htau]
    change Sym2.map (sigma * tau) old =
      Sym2.map sigma (Sym2.map tau old)
    rw [Sym2.map_map]
    apply Sym2.map_congr
    intro x _
    rfl

@[simp]
theorem sym2_map_inv_map (sigma : Equiv.Perm D) (e : Sym2 D) :
    Sym2.map sigma.symm (Sym2.map sigma e) = e := by
  induction e using Sym2.ind
  simp

@[simp]
theorem sym2_map_map_inv (sigma : Equiv.Perm D) (e : Sym2 D) :
    Sym2.map sigma (Sym2.map sigma.symm e) = e := by
  induction e using Sym2.ind
  simp

/-- Relabelling induces an explicit equivalence of old and new seam types. -/
def seamEquiv (sigma : Equiv.Perm D) (M : PartialMatching D) :
    M.Seam ≃ (renamePartial sigma M).Seam where
  toFun e := ⟨Sym2.map sigma e.1,
    Finset.mem_map.mpr ⟨e.1, e.2, rfl⟩⟩
  invFun e := ⟨Sym2.map sigma.symm e.1, by
    rcases Finset.mem_map.mp e.2 with ⟨old, hold, heq⟩
    rw [← heq]
    change Sym2.map sigma.symm (Sym2.map sigma old) ∈ M.seams
    rw [sym2_map_inv_map]
    exact hold⟩
  left_inv e := by
    apply Subtype.ext
    exact sym2_map_inv_map sigma e.1
  right_inv e := by
    apply Subtype.ext
    exact sym2_map_map_inv sigma e.1

@[simp]
theorem seamEquiv_apply_val (sigma : Equiv.Perm D)
    (M : PartialMatching D) (e : M.Seam) :
    (seamEquiv sigma M e).1 = Sym2.map sigma e.1 := rfl

@[simp]
theorem seamEquiv_symm_apply_val (sigma : Equiv.Perm D)
    (M : PartialMatching D) (e : (renamePartial sigma M).Seam) :
    ((seamEquiv sigma M).symm e).1 = Sym2.map sigma.symm e.1 := rfl

/-- Boundary darts are transported bijectively by every dart relabelling. -/
def boundaryEquiv (sigma : Equiv.Perm D) (M : PartialMatching D) :
    M.Boundary ≃ (renamePartial sigma M).Boundary where
  toFun x := ⟨sigma x.1, by
    intro hocc
    rcases ((renamePartial sigma M).mem_occupied_iff (sigma x.1)).mp hocc with
      ⟨e, he, hxe⟩
    rcases Finset.mem_map.mp he with ⟨old, hold, heq⟩
    rw [← heq] at hxe
    rcases Sym2.mem_map.mp hxe with ⟨oldDart, hOldDart, hImage⟩
    have hdx : oldDart = x.1 := sigma.injective hImage
    subst oldDart
    exact x.2 ((M.mem_occupied_iff x.1).mpr ⟨old, hold, hOldDart⟩)⟩
  invFun y := ⟨sigma.symm y.1, by
    intro hocc
    rcases (M.mem_occupied_iff (sigma.symm y.1)).mp hocc with
      ⟨old, hold, hOld⟩
    apply y.2
    apply ((renamePartial sigma M).mem_occupied_iff y.1).mpr
    refine ⟨Sym2.map sigma old, Finset.mem_map.mpr ⟨old, hold, rfl⟩, ?_⟩
    apply Sym2.mem_map.mpr
    exact ⟨sigma.symm y.1, hOld, sigma.apply_symm_apply y.1⟩⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

@[simp]
theorem boundaryEquiv_apply_val (sigma : Equiv.Perm D)
    (M : PartialMatching D) (x : M.Boundary) :
    (boundaryEquiv sigma M x).1 = sigma x.1 := rfl

@[simp]
theorem boundaryEquiv_symm_apply_val (sigma : Equiv.Perm D)
    (M : PartialMatching D) (x : (renamePartial sigma M).Boundary) :
    ((boundaryEquiv sigma M).symm x).1 = sigma.symm x.1 := rfl

/-- Transport a coloured partial matching.  The colour of a transported seam
is, by definition, the colour of its unique inverse image. -/
def renameColored {r : ℕ} (sigma : Equiv.Perm D)
    (P : ColoredMatching D r) : ColoredMatching D r where
  matching := renamePartial sigma P.matching
  color e := P.color ((seamEquiv sigma P.matching).symm e)

@[simp]
theorem matching_renameColored {r : ℕ} (sigma : Equiv.Perm D)
    (P : ColoredMatching D r) :
    (renameColored sigma P).matching = renamePartial sigma P.matching := rfl

@[simp]
theorem color_renameColored {r : ℕ} (sigma : Equiv.Perm D)
    (P : ColoredMatching D r) (e : (renameColored sigma P).Seam) :
    (renameColored sigma P).color e =
      P.color ((seamEquiv sigma P.matching).symm e) := rfl

@[simp]
theorem renameColored_one {r : ℕ} (P : ColoredMatching D r) :
    renameColored 1 P = P := by
  refine ColoredMatching.ext (renamePartial_one P.matching) ?_
  intro e
  simp [renameColored, seamEquiv]
  apply congrArg P.color
  apply Subtype.ext
  change Sym2.map (1 : Equiv.Perm D).symm e.1 = e.1
  exact congrFun Sym2.map_id e.1

@[simp]
theorem renameColored_mul {r : ℕ} (sigma tau : Equiv.Perm D)
    (P : ColoredMatching D r) :
    renameColored (sigma * tau) P =
      renameColored sigma (renameColored tau P) := by
  refine ColoredMatching.ext (renamePartial_mul sigma tau P.matching) ?_
  intro e
  simp [renameColored, seamEquiv]
  apply congrArg P.color
  apply Subtype.ext
  change Sym2.map (sigma * tau).symm e.1 =
    Sym2.map tau.symm (Sym2.map sigma.symm e.1)
  rw [Sym2.map_map]
  apply Sym2.map_congr
  intro x _
  rfl

/-- Transport a boundary-labelled coloured pairing.  The pairing moves
covariantly, while the label of a new boundary dart is read at its unique
inverse image. -/
def renameLabelled {r m : ℕ} (sigma : Equiv.Perm D)
    (P : BoundaryLabelledPairing D r m) :
    BoundaryLabelledPairing D r m where
  pairing := renameColored sigma P.pairing
  label := (boundaryEquiv sigma P.pairing.matching).symm.trans P.label

@[simp]
theorem pairing_renameLabelled {r m : ℕ} (sigma : Equiv.Perm D)
    (P : BoundaryLabelledPairing D r m) :
    (renameLabelled sigma P).pairing = renameColored sigma P.pairing := rfl

@[simp]
theorem label_renameLabelled {r m : ℕ} (sigma : Equiv.Perm D)
    (P : BoundaryLabelledPairing D r m)
    (x : (renameLabelled sigma P).pairing.Boundary) :
    (renameLabelled sigma P).label x =
      P.label ((boundaryEquiv sigma P.pairing.matching).symm x) := rfl

universe uA uB

/-- Extensionality across propositionally equal source and target types. -/
theorem equiv_heq_of_apply {A A' : Type uA} {B B' : Type uB}
    (hA : A = A') (hB : B = B') (e : A ≃ B) (f : A' ≃ B')
    (happly : ∀ (x : A) (y : A'), x ≍ y → e x ≍ f y) : e ≍ f := by
  subst A'
  subst B'
  rw [heq_iff_eq]
  apply Equiv.ext
  intro x
  exact eq_of_heq (happly x x (HEq.refl x))

/-- Extensionality for the dependent label field. -/
theorem labelled_ext {r m : ℕ} {P Q : BoundaryLabelledPairing D r m}
    (hp : P.pairing = Q.pairing) (hl : P.label ≍ Q.label) : P = Q := by
  apply BoundaryLabelledPairing.toData_injective
  exact Sigma.ext hp hl

@[simp]
theorem renameLabelled_one {r m : ℕ}
    (P : BoundaryLabelledPairing D r m) :
    renameLabelled 1 P = P := by
  let hp : (renameLabelled 1 P).pairing = P.pairing :=
    renameColored_one P.pairing
  apply labelled_ext hp
  apply equiv_heq_of_apply
    (congrArg (fun Q : ColoredMatching D r ↦ Q.Boundary) hp)
    rfl
  intro x y hxy
  apply heq_of_eq
  change P.label ((boundaryEquiv 1 P.pairing.matching).symm x) = P.label y
  apply congrArg P.label
  apply Subtype.ext
  change (1 : Equiv.Perm D).symm x.1 = y.1
  have hval : x.1 = y.1 :=
    (Subtype.heq_iff_coe_heq rfl
      (heq_of_eq (congrArg
        (fun Q : ColoredMatching D r ↦
          fun d ↦ d ∉ Q.matching.occupied) hp))).mp hxy
      |> eq_of_heq
  change x.1 = y.1
  exact hval

@[simp]
theorem renameLabelled_mul {r m : ℕ} (sigma tau : Equiv.Perm D)
    (P : BoundaryLabelledPairing D r m) :
    renameLabelled (sigma * tau) P =
      renameLabelled sigma (renameLabelled tau P) := by
  let hp : (renameLabelled (sigma * tau) P).pairing =
      (renameLabelled sigma (renameLabelled tau P)).pairing :=
    renameColored_mul sigma tau P.pairing
  apply labelled_ext hp
  apply equiv_heq_of_apply
    (congrArg (fun Q : ColoredMatching D r ↦ Q.Boundary) hp)
    rfl
  intro x y hxy
  apply heq_of_eq
  change P.label ((boundaryEquiv (sigma * tau) P.pairing.matching).symm x) =
    P.label ((boundaryEquiv tau P.pairing.matching).symm
      ((boundaryEquiv sigma
        (renameColored tau P.pairing).matching).symm y))
  apply congrArg P.label
  apply Subtype.ext
  change (sigma * tau).symm x.1 =
    tau.symm (sigma.symm y.1)
  have hval : x.1 = y.1 :=
    (Subtype.heq_iff_coe_heq rfl
      (heq_of_eq (congrArg
        (fun Q : ColoredMatching D r ↦
          fun d ↦ d ∉ Q.matching.occupied) hp))).mp hxy
      |> eq_of_heq
  rw [hval]
  rfl

/-- The full wreath renaming group acts on concrete partial pairings through
its proved action on darts. -/
instance wreathSMulPartial {I : Type uI} {L : Type uL} {F : Type uF}
    [Group L] [MulAction L F] [DecidableEq I] [DecidableEq F] :
    SMul (WreathRenaming I L) (PartialMatching (Σ _ : I, F)) where
  smul a M := renamePartial (WreathRenaming.dartPerm F a) M

instance wreathMulActionPartial {I : Type uI} {L : Type uL} {F : Type uF}
    [Group L] [MulAction L F] [DecidableEq I] [DecidableEq F] :
    MulAction (WreathRenaming I L) (PartialMatching (Σ _ : I, F)) where
  one_smul M := by
    change renamePartial (WreathRenaming.dartPerm F 1) M = M
    rw [WreathRenaming.dartPerm_one]
    exact renamePartial_one M
  mul_smul a b M := by
    change renamePartial (WreathRenaming.dartPerm F (a * b)) M =
      renamePartial (WreathRenaming.dartPerm F a)
        (renamePartial (WreathRenaming.dartPerm F b) M)
    rw [WreathRenaming.dartPerm_mul]
    exact renamePartial_mul _ _ M

instance wreathSMulColored {I : Type uI} {L : Type uL} {F : Type uF}
    [Group L] [MulAction L F] [DecidableEq I] [DecidableEq F] (r : ℕ) :
    SMul (WreathRenaming I L) (ColoredMatching (Σ _ : I, F) r) where
  smul a P := renameColored (WreathRenaming.dartPerm F a) P

instance wreathMulActionColored {I : Type uI} {L : Type uL} {F : Type uF}
    [Group L] [MulAction L F] [DecidableEq I] [DecidableEq F] (r : ℕ) :
    MulAction (WreathRenaming I L) (ColoredMatching (Σ _ : I, F) r) where
  one_smul P := by
    change renameColored (WreathRenaming.dartPerm F 1) P = P
    rw [WreathRenaming.dartPerm_one]
    exact renameColored_one P
  mul_smul a b P := by
    change renameColored (WreathRenaming.dartPerm F (a * b)) P =
      renameColored (WreathRenaming.dartPerm F a)
        (renameColored (WreathRenaming.dartPerm F b) P)
    rw [WreathRenaming.dartPerm_mul]
    exact renameColored_mul _ _ P

instance wreathSMulLabelled {I : Type uI} {L : Type uL} {F : Type uF}
    [Group L] [MulAction L F] [DecidableEq I] [DecidableEq F]
    (r m : ℕ) :
    SMul (WreathRenaming I L)
      (BoundaryLabelledPairing (Σ _ : I, F) r m) where
  smul a P := renameLabelled (WreathRenaming.dartPerm F a) P

/-- Hence the genuine wreath renaming group acts on the fully coloured,
boundary-labelled pairing objects, with labels transported
contravariantly. -/
instance wreathMulActionLabelled {I : Type uI} {L : Type uL} {F : Type uF}
    [Group L] [MulAction L F] [DecidableEq I] [DecidableEq F]
    (r m : ℕ) :
    MulAction (WreathRenaming I L)
      (BoundaryLabelledPairing (Σ _ : I, F) r m) where
  one_smul P := by
    change renameLabelled (WreathRenaming.dartPerm F 1) P = P
    rw [WreathRenaming.dartPerm_one]
    exact renameLabelled_one P
  mul_smul a b P := by
    change renameLabelled (WreathRenaming.dartPerm F (a * b)) P =
      renameLabelled (WreathRenaming.dartPerm F a)
        (renameLabelled (WreathRenaming.dartPerm F b) P)
    rw [WreathRenaming.dartPerm_mul]
    exact renameLabelled_mul _ _ P

/-! ### Connectivity and rank strata for the unrooted concrete model -/

theorem adjacent_renameUnrooted {n h r : ℕ}
    (a : WreathRenaming (Fin n) (Equiv.Perm (Fin h)))
    (P : ColoredMatching (FacetPairing.Dart n h) r)
    {u v : Fin n}
    (huv : P.Adjacent (fun _ ↦ h) u v) :
    (renameColored (WreathRenaming.dartPerm (Fin h) a) P).Adjacent
      (fun _ ↦ h) (a.cell u) (a.cell v) := by
  rcases huv with ⟨i, j, hij⟩
  refine ⟨a.slot u i, a.slot v j, ?_⟩
  change s(⟨a.cell u, a.slot u i⟩, ⟨a.cell v, a.slot v j⟩) ∈
    (renamePartial (WreathRenaming.dartPerm (Fin h) a) P.matching).seams
  apply Finset.mem_map.mpr
  refine ⟨s(⟨u, i⟩, ⟨v, j⟩), hij, ?_⟩
  rfl

/-- Wreath renaming preserves dual connectivity. -/
theorem connected_renameUnrooted {n h r : ℕ}
    (a : WreathRenaming (Fin n) (Equiv.Perm (Fin h)))
    (P : ColoredMatching (FacetPairing.Dart n h) r)
    (hP : P.IsConnected (fun _ ↦ h)) :
    (renameColored (WreathRenaming.dartPerm (Fin h) a) P).IsConnected
      (fun _ ↦ h) := by
  intro u v
  have oldPath :=
    hP (a.cell.symm u) (a.cell.symm v)
  have newPath := oldPath.lift a.cell
    (fun _ _ hxy ↦ adjacent_renameUnrooted a P hxy)
  simpa [Function.onFun] using newPath

/-- Renaming an unrooted connected diagram. -/
def renameUnrootedDiagram {n h r m : ℕ}
    (a : WreathRenaming (Fin n) (Equiv.Perm (Fin h)))
    (P : FacetPairing.UnrootedDiagram n h r m) :
    FacetPairing.UnrootedDiagram n h r m where
  raw := renameLabelled (WreathRenaming.dartPerm (Fin h) a) P.raw
  connected := connected_renameUnrooted a P.raw.pairing P.connected

@[simp]
theorem raw_renameUnrootedDiagram {n h r m : ℕ}
    (a : WreathRenaming (Fin n) (Equiv.Perm (Fin h)))
    (P : FacetPairing.UnrootedDiagram n h r m) :
    (renameUnrootedDiagram a P).raw =
      renameLabelled (WreathRenaming.dartPerm (Fin h) a) P.raw := rfl

@[simp]
theorem renameUnrootedDiagram_one {n h r m : ℕ}
    (P : FacetPairing.UnrootedDiagram n h r m) :
    renameUnrootedDiagram 1 P = P := by
  apply FacetPairing.ConnectedDiagram.raw_injective
  change renameLabelled
    (WreathRenaming.dartPerm (Fin h)
      (1 : WreathRenaming (Fin n) (Equiv.Perm (Fin h)))) P.raw = P.raw
  rw [WreathRenaming.dartPerm_one]
  exact renameLabelled_one P.raw

@[simp]
theorem renameUnrootedDiagram_mul {n h r m : ℕ}
    (a b : WreathRenaming (Fin n) (Equiv.Perm (Fin h)))
    (P : FacetPairing.UnrootedDiagram n h r m) :
    renameUnrootedDiagram (a * b) P =
      renameUnrootedDiagram a (renameUnrootedDiagram b P) := by
  apply FacetPairing.ConnectedDiagram.raw_injective
  change renameLabelled (WreathRenaming.dartPerm (Fin h) (a * b)) P.raw =
    renameLabelled (WreathRenaming.dartPerm (Fin h) a)
      (renameLabelled (WreathRenaming.dartPerm (Fin h) b) P.raw)
  rw [WreathRenaming.dartPerm_mul]
  exact renameLabelled_mul _ _ P.raw

instance fullRenamingSMulUnrootedDiagram (n h r m : ℕ) :
    SMul (WreathRenaming (Fin n) (Equiv.Perm (Fin h)))
      (FacetPairing.UnrootedDiagram n h r m) where
  smul := renameUnrootedDiagram

instance fullRenamingMulActionUnrootedDiagram (n h r m : ℕ) :
    MulAction (WreathRenaming (Fin n) (Equiv.Perm (Fin h)))
      (FacetPairing.UnrootedDiagram n h r m) where
  one_smul := renameUnrootedDiagram_one
  mul_smul := renameUnrootedDiagram_mul

theorem card_seams_renamePartial (sigma : Equiv.Perm D)
    (M : PartialMatching D) :
    (renamePartial sigma M).seams.card = M.seams.card := by
  simp [renamePartial]

theorem edgeCount_renameUnrootedDiagram {n h r m : ℕ}
    (a : WreathRenaming (Fin n) (Equiv.Perm (Fin h)))
    (P : FacetPairing.UnrootedDiagram n h r m) :
    (renameUnrootedDiagram a P).edgeCount = P.edgeCount := by
  simp [FacetPairing.ConnectedDiagram.edgeCount,
    FacetPairing.BoundaryLabelledPairing.edgeCount,
    FacetPairing.ColoredMatching.edgeCount, renameUnrootedDiagram,
    renameLabelled, renameColored, card_seams_renamePartial]

/-- Renaming preserves each circuit-rank stratum, not merely the ambient
connected-diagram type. -/
def renameUnrootedStratum {n h r m b : ℕ}
    (a : WreathRenaming (Fin n) (Equiv.Perm (Fin h)))
    (P : FacetPairing.UnrootedStratum n h r m b) :
    FacetPairing.UnrootedStratum n h r m b :=
  ⟨renameUnrootedDiagram a P.1, by
    unfold FacetPairing.ConnectedDiagram.HasCircuitRank
    rw [edgeCount_renameUnrootedDiagram]
    exact P.2⟩

@[simp]
theorem renameUnrootedStratum_one {n h r m b : ℕ}
    (P : FacetPairing.UnrootedStratum n h r m b) :
    renameUnrootedStratum 1 P = P := by
  apply Subtype.ext
  exact renameUnrootedDiagram_one P.1

@[simp]
theorem renameUnrootedStratum_mul {n h r m b : ℕ}
    (a c : WreathRenaming (Fin n) (Equiv.Perm (Fin h)))
    (P : FacetPairing.UnrootedStratum n h r m b) :
    renameUnrootedStratum (a * c) P =
      renameUnrootedStratum a (renameUnrootedStratum c P) := by
  apply Subtype.ext
  exact renameUnrootedDiagram_mul a c P.1

instance fullRenamingSMulUnrootedStratum (n h r m b : ℕ) :
    SMul (WreathRenaming (Fin n) (Equiv.Perm (Fin h)))
      (FacetPairing.UnrootedStratum n h r m b) where
  smul := renameUnrootedStratum

instance fullRenamingMulActionUnrootedStratum (n h r m b : ℕ) :
    MulAction (WreathRenaming (Fin n) (Equiv.Perm (Fin h)))
      (FacetPairing.UnrootedStratum n h r m b) where
  one_smul := renameUnrootedStratum_one
  mul_smul := renameUnrootedStratum_mul


end MatchingTransport

/-! ## Full slot-renaming groups used by the concrete pairing model -/

/-- All independent facet-slot permutations, together with all cell
permutations, for `n` cells having `h` slots each. -/
abbrev FullDartRenaming (n h : ℕ) :=
  WreathRenaming (Fin n) (Equiv.Perm (Fin h))

/-- Its action on the concrete dart type is the action constructed above. -/
example (n h : ℕ) : MulAction (FullDartRenaming n h)
    (FacetPairing.Dart n h) := inferInstance

/-- The familiar wreath-product order `n! (h!)^n`. -/
theorem card_fullDartRenaming (n h : ℕ) :
    Fintype.card (FullDartRenaming n h) =
      n.factorial * h.factorial ^ n := by
  rw [WreathRenaming.card]
  simp only [Fintype.card_fin, Fintype.card_perm]


end Renaming
end PolytopeCounting
