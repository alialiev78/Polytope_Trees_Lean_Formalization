module

public import Proofs.PublicDefinitions
public import Proofs.ConcreteXiPairableCore

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# The actual degree-zero row of the connected rooted family

There is one distinguished core cell when the number of ordinary cells is
zero. Thus every raw rooted pairing is connected, including a pairing of
two slots of the core. The circuit rank is the number of such pairings.

These equivalences connect the concrete public `Psi` and `T` to their
initial values. No initial coefficient, cardinality formula, or generating
function identity is supplied as an extra hypothesis.
-/

namespace PolytopeTrees

open PolytopeCounting.FacetPairing
open PolytopeCounting.FacetPairing.ConcreteXi

noncomputable section

universe uL

local instance initialRootedStratumFintype (n h₀ h r m b : ℕ) :
    Fintype (RootedStratum n h₀ h r m b) := Fintype.ofFinite _

/-- At ordinary-cell degree zero, the distinguished cell is the only cell. -/
theorem rootedCell_zero_eq (x y : RootedCell 0) : x = y := by
  rcases x with u | i
  · rcases y with v | j
    · cases u
      cases v
      rfl
    · exact Fin.elim0 j
  · exact Fin.elim0 i

/-- Internal core pairings do not affect connectedness of the one-cell
base. In particular, the degree-zero row is not concentrated at `m=h₀`. -/
theorem rootedPairing_zero_connected (h₀ h r m : ℕ)
    (P : RootedPairing 0 h₀ h r m) :
    P.pairing.IsConnected (rootedFacets h₀ h) := by
  intro x y
  have hxy := rootedCell_zero_eq x y
  subst y
  exact Relation.ReflTransGen.refl

/-- At `n=0`, the balance condition determines the rank. Forgetting the
rank and connectedness proofs is an equivalence with the raw pairing type. -/
def rootedZeroStratumEquiv (h₀ h r m b : ℕ)
    (hs : h₀ = m + 2 * b) :
    RootedStratum 0 h₀ h r m b ≃ RootedPairing 0 h₀ h r m where
  toFun P := P.1.raw
  invFun P := ⟨⟨P, rootedPairing_zero_connected h₀ h r m P⟩, by
    have hbal := P.boundary_balance
    simp only [card_rootedDart, Nat.zero_mul, Nat.add_zero] at hbal
    change P.edgeCount + 1 = Fintype.card (RootedCell 0) + b
    rw [card_rootedCell]
    omega⟩
  left_inv P := by
    apply Subtype.ext
    apply ConnectedDiagram.raw_injective
    rfl
  right_inv P := rfl

/-- Exact cardinality of the initial tree stratum: a core with all its
slots unpaired has `h₀!` boundary labellings. -/
theorem card_rooted_tree_zero (h₀ h r : ℕ) :
    Fintype.card (RootedStratum 0 h₀ h r h₀ 0) = h₀.factorial := by
  rw [Fintype.card_congr
    (rootedZeroStratumEquiv h₀ h r h₀ 0 (by omega))]
  simpa only [card_rootedDart, Nat.zero_mul, Nat.add_zero] using
    (DisconnectedTop.card_top_boundaryLabelledPairing
      (D := RootedDart 0 h₀ h) r)

/-- The initial value of the public fixed-core tree count is proved from
its carrier. The core slots are still fixed pointwise in this definition. -/
theorem T_zero (L : Type uL) [Fintype L] (h₀ h r : ℕ) :
    T L 0 h₀ h r = (h₀.factorial : ℚ) := by
  simp [T, Psi, Nat.card_eq_fintype_card, card_rooted_tree_zero]

theorem T_zero_ne_zero (L : Type uL) [Fintype L] (h₀ h r : ℕ) :
    T L 0 h₀ h r ≠ 0 := by
  rw [T_zero]
  exact_mod_cast Nat.factorial_ne_zero h₀

/-- The normalized initial connected coefficient is exactly the initial
coefficient of the concrete unrestricted pairable-core carrier. -/
theorem Psi_zero_normalized_eq_Xi
    (L : Type uL) [Fintype L] (h₀ h r m b : ℕ)
    (hs : h₀ = m + 2 * b) :
    Psi L 0 h₀ h r m b / (m.factorial : ℚ) =
      XiHatCount h h₀ r (Fintype.card L) 1 0 m := by
  have hc := Fintype.card_congr (rootedZeroStratumEquiv h₀ h r m b hs)
  simp [Psi, XiHatCount, Nat.card_eq_fintype_card, hc]

/-- Initial coefficients in formula (53) are genuine core self-pairings,
not hypothetical initial data. This includes the closed case `m=0`. -/
theorem Psi_zero_normalized_closedForm
    (L : Type uL) [Group L] [Fintype L] (h₀ h r m b : ℕ)
    (hs : h₀ = m + 2 * b) :
    Psi L 0 h₀ h r m b / (m.factorial : ℚ) =
      PolytopeCounting.ExplicitFormulas.RecursiveXi.pairableCoreXiClosedForm
        h h₀ r (Fintype.card L) 1 0 m := by
  rw [Psi_zero_normalized_eq_Xi L h₀ h r m b hs,
    XiHatCount_eq_closedForm h h₀ r (Fintype.card L) 1 Fintype.card_pos]

end
end PolytopeTrees
