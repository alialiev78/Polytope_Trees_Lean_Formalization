module

public import Proofs.CoreComponentCanonical
public import Proofs.BivariateConvolution

@[expose] public section

set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

/-!
# The concrete identity Xi = W * Psi

The source coefficients are the existing finite-carrier definitions
`ConcreteXi.XiHatCount`, `PolytopeTrees.W`, and `PolytopeTrees.PsiHat`.
The proof uses the constructed root-component equivalence, canonical cell
reindexing, finite boundary-size convolution, and factorial cancellation.
No generating-function identity is supplied as a hypothesis.
-/

namespace PolytopeCounting.BivariateCoefficients

noncomputable section
open scoped BigOperators

private def reverseIndex (N : ℕ) : Fin (N + 1) ≃ Fin (N + 1) where
  toFun i := ⟨N - i.1, by omega⟩
  invFun i := ⟨N - i.1, by omega⟩
  left_inv i := by apply Fin.ext; have := i.2; dsimp; omega
  right_inv i := by apply Fin.ext; have := i.2; dsimp; omega

theorem convolution_eq_fin_sum {R : Type*} [Semiring R]
    (A B : Series R) (n m : ℕ) :
    convolution A B n m =
      ∑ i : Fin (n + 1), ∑ j : Fin (m + 1),
        A i.1 j.1 * B (n - i.1) (m - j.1) := by
  unfold convolution
  symm
  rw [Fin.sum_univ_eq_sum_range (fun i ↦
    ∑ j : Fin (m + 1), A i j.1 * B (n - i) (m - j.1)) (n + 1)]
  apply Finset.sum_congr rfl
  intro i _
  exact Fin.sum_univ_eq_sum_range (fun j ↦ A i j * B (n - i) (m - j)) (m + 1)

/-- Commutativity of the coefficientwise bivariate Cauchy product. -/
theorem convolution_comm {R : Type*} [CommSemiring R]
    (A B : Series R) : convolution A B = convolution B A := by
  funext n m
  rw [convolution_eq_fin_sum, convolution_eq_fin_sum]
  apply Fintype.sum_equiv (reverseIndex n)
  intro i
  apply Fintype.sum_equiv (reverseIndex m)
  intro j
  have hi : n - (n - i.1) = i.1 := by have := i.2; omega
  have hj : m - (m - j.1) = j.1 := by have := j.2; omega
  change A i.1 j.1 * B (n - i.1) (m - j.1) =
    B (n - i.1) (m - j.1) * A (n - (n - i.1)) (m - (m - j.1))
  rw [hi, hj, mul_comm]

end
end PolytopeCounting.BivariateCoefficients

namespace PolytopeTrees

noncomputable section

open scoped BigOperators
open PolytopeCounting
open PolytopeCounting.FacetPairing
open PolytopeCounting.FacetPairing.CoreComponents
open PolytopeCounting.FacetPairing.ComponentConvolution
open PolytopeCounting.BivariateCoefficients

universe uL

/-- Fully normalized finite convolution, including arbitrary scalar core
weight `c`. All subset allocations are counted and cancelled internally. -/
theorem XiHatCount_convolution
    (L : Type uL) [Group L] [Fintype L]
    (h h₀ r : ℕ) (c : ℚ) (n m : ℕ) :
    ConcreteXi.XiHatCount h h₀ r (Fintype.card L) c n m =
      c * convolution (PsiHat L h₀ h r) (fun n m ↦ W L n h r m) n m := by
  have htau : 0 < Fintype.card L := Fintype.card_pos
  calc
    _ = ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        c * ((Nat.choose n k : ℚ) * coreCount k h₀ h r j *
          allCount (n - k) h r (m - j) /
            ((n.factorial * Fintype.card L ^ n : ℕ) : ℚ)) := by
      rw [XiHatCount_component_sum, root_component_binomial_sum]
      simp only [Finset.mul_sum, Nat.cast_mul, Nat.cast_pow]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        c * (PsiHat L h₀ h r k j * W L (n - k) h r (m - j)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      apply Finset.sum_congr rfl
      intro j _
      rw [PsiHat_eq_coreCount, W_eq_allCount,
        Normalization.choose_mul_normalized_components hkn htau]
    _ = _ := by simp only [convolution, Finset.mul_sum]

/-- Literal bivariate product for the original fixed-slot core. -/
theorem Xi_equals_W_mul_Psi
    (L : Type uL) [Group L] [Fintype L] (h h₀ r : ℕ) :
    XiEqualsProduct (fun n m ↦ W L n h r m) (PsiHat L h₀ h r)
      (ConcreteXi.XiHatCount h h₀ r (Fintype.card L) 1) := by
  unfold XiEqualsProduct
  funext n m
  rw [XiHatCount_convolution, one_mul, convolution_comm]

/-- Same theorem for the actual action-groupoid mass. In particular, the
claim remains valid for closed boundaries and non-free actions. -/
theorem XiMass_equals_W_mul_Psi
    (L : Type uL) [Group L] [Fintype L]
    (h h₀ r : ℕ) [MulAction L (Fin h)] :
    XiEqualsProduct (fun n m ↦ W L n h r m) (PsiHat L h₀ h r)
      (ConcreteXi.XiHatMass L h h₀ r 1) := by
  unfold XiEqualsProduct
  funext n m
  rw [ConcreteXi.XiHatMass_eq_count]
  exact congrFun (congrFun (Xi_equals_W_mul_Psi L h h₀ r) n) m

/-- Expanded coefficient statement, convenient for comparison with the
manuscript. There is no omitted `n=0` or `m=0` case. -/
theorem Xi_coefficient_convolution
    (L : Type uL) [Group L] [Fintype L]
    (h h₀ r n m : ℕ) :
    ConcreteXi.XiHatCount h h₀ r (Fintype.card L) 1 n m =
      ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        W L k h r j * PsiHat L h₀ h r (n - k) (m - j) := by
  exact congrFun (congrFun (Xi_equals_W_mul_Psi L h h₀ r) n) m

end
end PolytopeTrees
