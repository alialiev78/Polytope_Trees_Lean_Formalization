module

public import Proofs.RecursiveXiPairableCoreComplete
public import Proofs.DisconnectedTopCoefficient
public import Proofs.GenericRootedStratumAction

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Concrete finite-carrier meaning of the pairable-core Xi formula

Unlike a definition of Xi by its factorial expression, `XiHatCount` below
counts the already existing finite carrier `RootedPairing`. Its recurrence
comes from the generic two-sided cut--join equivalence, and its top value
comes from the unique empty matching. Uniqueness then identifies this
concrete count with formula (53), at every coefficient.

The base and its ports are fixed pointwise by the renaming action. The
scalar `c` is a separately specified weight for that distinguished core.
All core--core, core--ordinary and ordinary--ordinary seams are allowed.
This module does not prove the component decomposition Xi = W * Psi.
-/

namespace PolytopeCounting.FacetPairing.ConcreteXi

open ExplicitFormulas ExplicitFormulas.RecursiveXi
open Renaming Renaming.MatchingTransport

noncomputable section

universe uL

/-- Actual finite rooted-pairing count, normalized by ordinary-cell
renaming and boundary labelling. This definition contains no closed-form
factorial count of matchings. -/
def XiHatCount (h h₀ r tau : ℕ) (c : ℚ) (n m : ℕ) : ℚ :=
  c / ((n.factorial : ℚ) * (tau : ℚ) ^ n) *
    (Fintype.card (RootedPairing n h₀ h r m) : ℚ) /
      (m.factorial : ℚ)

/-- Concrete rooted pairings cannot inhabit an unsupported boundary
stratum. -/
theorem XiHatCount_eq_zero_of_not_supported
    (h h₀ r tau : ℕ) (c : ℚ) (n m : ℕ)
    (hs : ¬ PairableCoreSupported h h₀ n m) :
    XiHatCount h h₀ r tau c n m = 0 := by
  classical
  letI : IsEmpty (RootedPairing n h₀ h r m) := ⟨fun P ↦ by
    apply hs
    refine ⟨P.edgeCount, ?_⟩
    have hbal := P.boundary_balance
    simpa [card_rootedDart, rootedFacets, Nat.mul_comm, Nat.add_comm] using hbal.symm⟩
  simp [XiHatCount, Fintype.card_eq_zero]

/-- The top boundary stratum consists of one empty matching with all
bijective boundary labels. The top value is therefore proved from the
actual carrier, rather than supplied as an assumption. -/
theorem XiHatCount_top
    (h h₀ r tau : ℕ) (c : ℚ) (n : ℕ) :
    XiHatCount h h₀ r tau c n (h * n + h₀) =
      c * (1 / ((n.factorial : ℚ) * (tau : ℚ) ^ n)) := by
  have hcard :
      Fintype.card (RootedPairing n h₀ h r (h * n + h₀)) =
        (h * n + h₀).factorial := by
    simpa [card_rootedDart, rootedFacets, Nat.mul_comm, Nat.add_comm] using
      (DisconnectedTop.card_top_boundaryLabelledPairing
        (D := RootedDart n h₀ h) r)
  have hfac : ((h * n + h₀).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (h * n + h₀)
  unfold XiHatCount
  rw [hcard]
  simp [div_eq_mul_inv, mul_assoc, hfac]

/-- Concrete recurrence obtained by cutting any seam, including a seam
whose two endpoints belong to the distinguished core. -/
theorem XiHatCount_recurrence_by_pairs
    (h h₀ r tau : ℕ) (c : ℚ) (n m ell : ℕ)
    (hs : h * n + h₀ = m + 2 * (ell + 1)) :
    (2 * (ell + 1) : ℚ) * XiHatCount h h₀ r tau c n m =
      (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        XiHatCount h h₀ r tau c n (m + 2) := by
  have hraw := DisconnectedRawCutJoin.raw_card_recurrence
    (D := RootedDart n h₀ h) r m (ell + 1)
    (by simpa [card_rootedDart, rootedFacets, Nat.mul_comm, Nat.add_comm] using hs)
  have hrawQ :
      (2 * (ell + 1) : ℚ) *
          (Fintype.card (RootedPairing n h₀ h r m) : ℚ) =
        (r : ℚ) *
          (Fintype.card (RootedPairing n h₀ h r (m + 2)) : ℚ) := by
    exact_mod_cast hraw
  have hmfac : (m.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  unfold XiHatCount
  calc
    _ = (c / ((n.factorial : ℚ) * (tau : ℚ) ^ n)) *
        ((2 * (ell + 1) : ℚ) *
          (Fintype.card (RootedPairing n h₀ h r m) : ℚ)) /
        (m.factorial : ℚ) := by ring
    _ = (c / ((n.factorial : ℚ) * (tau : ℚ) ^ n)) *
        ((r : ℚ) *
          (Fintype.card (RootedPairing n h₀ h r (m + 2)) : ℚ)) /
        (m.factorial : ℚ) := by rw [hrawQ]
    _ = _ := by
      rw [DisconnectedMass.factorial_add_two_cast]
      by_cases hden : (n.factorial : ℚ) * (tau : ℚ) ^ n = 0
      · simp [hden]
      · field_simp [hden, hmfac]

/-- All-index recurrence for the actual rooted-pairing carrier. -/
theorem XiHatCount_recurrence_all
    (h h₀ r tau : ℕ) (c : ℚ) (n m : ℕ) :
    (((h * n + h₀ : ℕ) : ℚ) - (m : ℚ)) * XiHatCount h h₀ r tau c n m =
      (r : ℚ) * ((m + 1 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) *
        XiHatCount h h₀ r tau c n (m + 2) := by
  by_cases hs : PairableCoreSupported h h₀ n m
  · obtain ⟨ell, hell⟩ := hs
    cases ell with
    | zero =>
      have htop : h * n + h₀ = m := by omega
      have hnext : ¬ PairableCoreSupported h h₀ n (m + 2) := by
        rintro ⟨q, hq⟩
        omega
      rw [XiHatCount_eq_zero_of_not_supported h h₀ r tau c n (m + 2) hnext]
      simp [htop]
    | succ ell =>
      have hs' : h * n + h₀ = m + 2 * (ell + 1) := by omega
      have hsQ : ((h * n + h₀ : ℕ) : ℚ) =
          (m : ℚ) + (2 * (ell + 1) : ℚ) := by exact_mod_cast hs'
      have hdiff : (((h * n + h₀ : ℕ) : ℚ) - (m : ℚ)) =
          (2 * (ell + 1) : ℚ) := by linarith
      rw [hdiff]
      exact XiHatCount_recurrence_by_pairs h h₀ r tau c n m ell hs'
  · have hsnext : ¬ PairableCoreSupported h h₀ n (m + 2) :=
      fun hnext ↦ hs (supported_of_supported_add_two hnext)
    rw [XiHatCount_eq_zero_of_not_supported h h₀ r tau c n m hs,
      XiHatCount_eq_zero_of_not_supported h h₀ r tau c n (m + 2) hsnext]
    simp

/-- Formula (53) for the actual rooted finite carrier, with no supplied
top value, recurrence, cardinality equation or equivalence assumption. -/
theorem XiHatCount_eq_closedForm
    (h h₀ r tau : ℕ) (c : ℚ) (htau : 0 < tau) :
    XiHatCount h h₀ r tau c = pairableCoreXiClosedForm h h₀ r tau c := by
  apply pairableCoreXiClosedForm_unique h h₀ r tau c htau
  · exact XiHatCount_eq_zero_of_not_supported h h₀ r tau c
  · exact XiHatCount_top h h₀ r tau c
  · exact XiHatCount_recurrence_all h h₀ r tau c

/-- Base-preserving renaming acts on unrestricted rooted pairings, without
requiring connectedness. -/
instance rootedPairingMulAction
    (n h₀ h r m : ℕ) (L : Type uL)
    [Group L] [MulAction L (Fin h)] :
    MulAction (WreathRenaming (Fin n) L) (RootedPairing n h₀ h r m) where
  smul a P := renameLabelled (GenericRootedStratumAction.dartPerm a) P
  one_smul P := by
    change renameLabelled (GenericRootedStratumAction.dartPerm
      (h₀ := h₀) (h := h) (1 : WreathRenaming (Fin n) L)) P = P
    rw [GenericRootedStratumAction.dartPerm_one]
    exact renameLabelled_one P
  mul_smul a b P := by
    change renameLabelled (GenericRootedStratumAction.dartPerm
      (h₀ := h₀) (h := h) (a * b)) P =
        renameLabelled (GenericRootedStratumAction.dartPerm a)
          (renameLabelled (GenericRootedStratumAction.dartPerm b) P)
    rw [GenericRootedStratumAction.dartPerm_mul]
    exact renameLabelled_mul _ _ P

/-- The genuine action-groupoid mass with boundary labels normalized away.
The local action need not be free or faithful. -/
def XiHatMass
    (L : Type uL) [Group L] [Fintype L]
    (h h₀ r : ℕ) [MulAction L (Fin h)] (c : ℚ) (n m : ℕ) : ℚ :=
  c * ActionGroupoid.mass (WreathRenaming (Fin n) L)
    (RootedPairing n h₀ h r m) ℚ / (m.factorial : ℚ)

/-- Exact non-free groupoid normalization for the concrete Xi carrier. -/
theorem XiHatMass_eq_count
    (L : Type uL) [Group L] [Fintype L]
    (h h₀ r : ℕ) [MulAction L (Fin h)] (c : ℚ) (n m : ℕ) :
    XiHatMass L h h₀ r c n m =
      XiHatCount h h₀ r (Fintype.card L) c n m := by
  unfold XiHatMass XiHatCount
  rw [ActionGroupoid.mass_eq_card_div_card, WreathRenaming.card]
  simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
  ring

/-- The homogeneous Xi factorial formula counts the actual rooted action
groupoid, at every n,m, including closed and unsupported boundaries. -/
theorem XiHatMass_eq_closedForm
    (L : Type uL) [Group L] [Fintype L]
    (h h₀ r : ℕ) [MulAction L (Fin h)] (c : ℚ) (n m : ℕ) :
    XiHatMass L h h₀ r c n m =
      pairableCoreXiClosedForm h h₀ r (Fintype.card L) c n m := by
  rw [XiHatMass_eq_count,
    XiHatCount_eq_closedForm h h₀ r (Fintype.card L) c Fintype.card_pos]


end
end PolytopeCounting.FacetPairing.ConcreteXi
