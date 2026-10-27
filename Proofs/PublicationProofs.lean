module

public import Proofs.PublicDefinitions
public import Proofs.MassFixedCoreExplicit
public import Proofs.DisconnectedTopCoefficient

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-! # The paper's formulas for directly defined finite cardinalities -/
namespace PolytopeTrees
open scoped BigOperators
open PolytopeCounting PolytopeCounting.FacetPairing
open MassRecurrence NumericalRecurrenceAssembly StratumBalanceSpecialization
noncomputable section
universe u
variable (L : Type u) [Group L] [Fintype L]

theorem U_eq_mass (n h r m b : ℕ) [MulAction L (Fin h)] :
    U L n h r m b = UMass L n h r m b := by
  classical
  rw [UMass, Renaming.GenericStratumMass.mass_genericWreath_unrootedStratum]
  simp only [U, ← Nat.card_eq_fintype_card]

theorem Psi_eq_mass (n h₀ h r m b : ℕ) [MulAction L (Fin h)] :
    Psi L n h₀ h r m b = PsiMass L n h₀ h r m b := by
  classical
  rw [PsiMass, Renaming.GenericRootedStratumAction.mass_genericWreath_rootedStratum]
  simp only [Psi, ← Nat.card_eq_fintype_card]

theorem R_eq_mass (n h r : ℕ) [MulAction L (Fin h)] :
    R L n h r = RMass L n h r := by
  simpa only [R, RMass, treeBoundary, unrootedTreeBoundary] using U_eq_mass L n h r ((h - 2) * n + 2) 0

theorem T_eq_mass (n h₀ h r : ℕ) [MulAction L (Fin h)] :
    T L n h₀ h r = TMass L n h₀ h r := by
  simpa only [T, TMass, rootedTreeBoundary, Nat.add_comm] using Psi_eq_mass L n h₀ h r (h₀ + (h - 2) * n) 0

theorem W_eq_mass (n h r m : ℕ) [MulAction L (Fin h)] :
    W L n h r m = DisconnectedMass.WHatMass L n h r m := by
  rw [DisconnectedMass.WHatMass, DisconnectedMass.WLabelledMass_eq_card_div]
  simp only [W, Nat.card_eq_fintype_card]

theorem Uprev_eq_mass (n h r m b : ℕ) [MulAction L (Fin h)] :
    Uprev L n h r m b = AllRankMassRecurrence.unrootedCyclePrevious L n h r m b := by
  cases b with
  | zero => rfl
  | succ b => exact U_eq_mass L n h r (m + 2) b

theorem Psiprev_eq_mass (n h₀ h r m b : ℕ) [MulAction L (Fin h)] :
    Psiprev L n h₀ h r m b = AllRankMassRecurrence.rootedCyclePrevious L n h₀ h r m b := by
  cases b with
  | zero => rfl
  | succ b => exact Psi_eq_mass L n h₀ h r (m + 2) b

theorem Uconv_eq_mass (n h r m b : ℕ) [MulAction L (Fin h)] :
    Uconv L n h r m b = unrootedMassConvolution L n h r m b := by
  simp only [Uconv, unrootedMassConvolution, UnrootedIndex, Fintype.sum_prod_type,
    unrootedMassSummand, unrootedCellIndex, unrootedBoundaryIndex, unrootedRankIndex,
    U_eq_mass, ProperSize, BridgeAllocationCounting.ProperCellSize]

theorem Psiconv_eq_mass (n h₀ h r m b : ℕ) [MulAction L (Fin h)] :
    Psiconv L n h₀ h r m b = rootedMassConvolution L n h₀ h r m b := by
  simp only [Psiconv, rootedMassConvolution, RootedIndex, Fintype.sum_prod_type,
    rootedMassSummand, rootedCellIndex, rootedBoundaryIndex, rootedRankIndex,
    U_eq_mass, Psi_eq_mass]

/-- With one cell and every facet free, connectivity and rank impose no extra choices. -/
def singleCellEquiv (h r : ℕ) :
    UnrootedStratum 1 h r h 0 ≃ UnrootedPairing 1 h r h where
  toFun P := P.val.raw
  invFun P := by
    have hc : P.pairing.IsConnected (fun _ : Fin 1 => h) := by
      intro a b
      have hab : a = b := Subsingleton.elim _ _
      subst b
      exact .refl
    refine ⟨⟨P, hc⟩, ?_⟩
    have hb := P.boundary_balance
    simp only [card_dart, one_mul] at hb
    change P.edgeCount + 1 = Fintype.card (Fin 1) + 0
    simp only [Fintype.card_fin]
    omega
  left_inv P := by cases P; rfl
  right_inv P := rfl

theorem R_one (h r : ℕ) (hh : 2 ≤ h) :
    R L 1 h r = (h.factorial : ℚ) / (Fintype.card L : ℚ) := by
  have hb : (h - 2) * 1 + 2 = h := by omega
  have hc : Nat.card (UnrootedStratum 1 h r h 0) = h.factorial := by
    rw [Nat.card_congr (singleCellEquiv h r), Nat.card_eq_fintype_card]
    simpa only [one_mul] using DisconnectedTop.card_unrootedPairing_top 1 h r
  simp only [R, U, hb, hc, Nat.factorial_one, one_mul, pow_one]
end
end PolytopeTrees
