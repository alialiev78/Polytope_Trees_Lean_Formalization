module

public import Proofs.CountingSeriesDerivations
public import Proofs.PublicationProofs

@[expose] public section

/-!
# Closing the old IsFormalExpPair interface for the concrete series

We do not assume a chain rule in the boundary variable.  Starting with the
proved cell-pointing identity, the defect `D W - W D V` satisfies a homogeneous
formal ODE with zero initial value.  Coefficientwise ODE uniqueness forces
it to vanish.  Thus both components of the old interface are conclusions.
-/

namespace PolytopeCounting.CountingDifferential

noncomputable section
open BivariateCoefficients FormalCounting FormalExpLog

/-- Boundary chain rule obtained by commuting the two derivations and
using formal initial-value uniqueness. -/
theorem boundary_chain_rule_of_cell_ode
    (V W : CountingSeries)
    (hV0 : PowerSeries.constantCoeff V = 0)
    (hW0 : PowerSeries.constantCoeff W = 1)
    (hcell : cellD W = cellD V * W) :
    boundaryD W = W * boundaryD V := by
  let H : CountingSeries := boundaryD W - W * boundaryD V
  have hH0 : PowerSeries.constantCoeff H = 0 := by
    simp only [H, map_sub, map_mul, boundaryD_constantCoeff, hV0, hW0,
      Derivation.map_one_eq_zero, map_zero, mul_zero, sub_zero]
  have hH : cellD H = cellD V * H := by
    dsimp only [H]
    rw [map_sub, cellD_boundaryD, hcell,
      boundaryD.leibniz, cellD.leibniz, hcell, cellD_boundaryD]
    simp only [smul_eq_mul]
    ring
  have hHzero : H = 0 := by
    apply linear_ode_unique (A := cellD V)
    · simpa using hH0
    · simpa only [cellD_apply] using hH
    · simp
  exact sub_eq_zero.mp hHzero

/-- Literal realization of the old two-derivation interface. -/
theorem expPair_of_cell_ode
    (h : ℕ) (V W : CountingSeries)
    (hV0 : PowerSeries.constantCoeff V = 0)
    (hW0 : PowerSeries.constantCoeff W = 1)
    (hcell : cellD W = cellD V * W) :
    IsFormalExpPair (eulerD h) boundaryD V W := by
  have hb := boundary_chain_rule_of_cell_ode V W hV0 hW0 hcell
  refine ⟨hb, ?_⟩
  simp only [eulerD_apply, hcell, hb]
  ring

/-- The reverse heat-equation implication needs only cancellation of W,
not a field structure or division by a formal series. -/
theorem connectedEquation_of_exp_disconnectedEquation
    {A : Type*} [CommRing A] [IsDomain A] [Algebra ℚ A]
    (E D : Derivation ℚ A A) (ρ V W : A)
    (hW : W ≠ 0) (hExp : IsFormalExpPair E D V W)
    (hHeat : SatisfiesDisconnectedEquation E D ρ W) :
    SatisfiesConnectedEquation E D ρ V := by
  have hD2 := secondDerivative_of_expPair E D V W hExp
  have hEW := hExp.2
  unfold SatisfiesDisconnectedEquation at hHeat
  unfold SatisfiesConnectedEquation
  apply mul_left_cancel₀ hW
  calc
    W * E V = E W := hEW.symm
    _ = ρ * D (D W) := hHeat
    _ = W * (ρ * (D (D V) + D V * D V)) := by rw [hD2]; ring

end
end PolytopeCounting.CountingDifferential

namespace PolytopeTrees

noncomputable section
open PolytopeCounting PolytopeCounting.FacetPairing
open BivariateCoefficients CountingDifferential FormalExpLog
universe uL

/-- The boundary identity for the previously defined finite counting series. -/
theorem WSeries_boundary_derivative
    (L : Type uL) [Group L] [Fintype L] (h r : ℕ) :
    boundaryD (WSeries L h r) =
      WSeries L h r * boundaryD (VSeries L h r) := by
  apply boundary_chain_rule_of_cell_ode
  · exact VSeries_constantCoeff L h r
  · exact WSeries_constantCoeff L h r
  · exact WSeries_derivative L h r

/-- Both differential identities in IsFormalExpPair, now as a theorem
about the concrete families, with no missing exponential hypothesis. -/
theorem concrete_IsFormalExpPair
    (L : Type uL) [Group L] [Fintype L] (h r : ℕ) :
    IsFormalExpPair (eulerD h) boundaryD (VSeries L h r) (WSeries L h r) := by
  exact expPair_of_cell_ode h _ _
    (VSeries_constantCoeff L h r) (WSeries_constantCoeff L h r)
    (WSeries_derivative L h r)

/-- Euler/logarithmic derivative form, extracted without rebuilding a
parallel coefficient model. -/
theorem WSeries_euler_derivative
    (L : Type uL) [Group L] [Fintype L] (h r : ℕ) :
    eulerD h (WSeries L h r) =
      WSeries L h r * eulerD h (VSeries L h r) :=
  (concrete_IsFormalExpPair L h r).2

/-- Formula (46), also at unsupported indices.  Unsupported carriers are
empty by the actual dart-balance theorem, not by a new count definition. -/
theorem W_eq_WCoefficient_all
    (L : Type uL) [Group L] [Fintype L]
    (h r n m : ℕ) [MulAction L (Fin h)] :
    W L n h r m = WCoefficient h r (Fintype.card L) n m := by
  classical
  by_cases hs : ExplicitFormulas.WSupported h n m
  · obtain ⟨ell, hell⟩ := hs
    rw [W_eq_mass]
    exact DisconnectedTop.WHatMass_closed_form n h r (Fintype.card L)
      rfl Fintype.card_pos m ell (by simpa [Nat.mul_comm] using hell)
  · letI : IsEmpty (UnrootedPairing n h r m) := ⟨fun P ↦ by
      apply hs
      refine ⟨P.edgeCount, ?_⟩
      simpa [Nat.mul_comm] using P.boundary_balance.symm⟩
    rw [show WCoefficient h r (Fintype.card L) n m = 0 from
      ExplicitFormulas.WHatClosedForm_eq_zero_of_not_supported
        h r (Fintype.card L) n m hs]
    simp [W]

/-- The heat equation for the actual disconnected series. -/
theorem WSeries_heat_equation
    (L : Type uL) [Group L] [Fintype L]
    (h r : ℕ) [MulAction L (Fin h)] :
    SatisfiesDisconnectedEquation (eulerD h) boundaryD (scalar (r : ℚ))
      (WSeries L h r) := by
  have hc : (fun n m ↦ W L n h r m) =
      WCoefficient h r (Fintype.card L) := by
    funext n m
    exact W_eq_WCoefficient_all L h r n m
  unfold WSeries
  rw [hc]
  exact disconnectedPDE_to_derivation h r _
    (WCoefficient_satisfiesDisconnectedPDE h r (Fintype.card L) Fintype.card_pos)

/-- The connected nonlinear PDE (37) for the concrete series.  The
exponential interface and linear heat equation are supplied by proofs. -/
theorem VSeries_connected_equation
    (L : Type uL) [Group L] [Fintype L]
    (h r : ℕ) [MulAction L (Fin h)] :
    SatisfiesConnectedEquation (eulerD h) boundaryD (scalar (r : ℚ))
      (VSeries L h r) := by
  apply connectedEquation_of_exp_disconnectedEquation
    (eulerD h) boundaryD (scalar (r : ℚ)) (VSeries L h r) (WSeries L h r)
  · intro hz
    have h0 := WSeries_constantCoeff L h r
    rw [hz, map_zero] at h0
    exact zero_ne_one h0
  · exact concrete_IsFormalExpPair L h r
  · exact WSeries_heat_equation L h r

end
end PolytopeTrees
