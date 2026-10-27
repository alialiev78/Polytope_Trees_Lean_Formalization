module

public import Proofs.Normalization

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Normalizing complete bridge convolutions

The local lemma in `MassRecurrence` normalizes one bridge summand.  This
module performs the same cancellation under an arbitrary finite sum.  It is
the arithmetic endpoint needed by the global bridge coproduct: once the
coproduct supplies the raw cardinal identity, these theorems turn it into the
product of the two component groupoid masses.

The unrooted theorem retains the literal endpoint-orientation factor two.
The rooted theorem has no such factor because the component containing the
base is intrinsic.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace BridgeConvolutionNormalization

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

noncomputable section

theorem cast_sum_nat_rat
    (I : Finset ι) (f : ι → ℕ) :
    ((∑ i ∈ I, f i : ℕ) : ℚ) = ∑ i ∈ I, (f i : ℚ) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.cast_add, ih]

/-- The normalized contribution of one ordered pair of components. -/
def normalizedSummand
    (n m tau : ℕ) (k s A B : ι → ℕ) (i : ι) : ℚ :=
  (Nat.choose m (s i) : ℚ) *
    ((A i : ℚ) / (((k i).factorial * tau ^ k i : ℕ) : ℚ)) *
    ((B i : ℚ) /
      ((((n - k i).factorial * tau ^ (n - k i) : ℕ)) : ℚ))

/-- A whole raw cell-labelled bridge sum normalizes term by term. -/
theorem normalize_raw_bridge_sum
    (I : Finset ι) (n m tau : ℕ) (k s A B : ι → ℕ)
    (hk : ∀ i ∈ I, k i ≤ n) (htau : 0 < tau) :
    (((∑ i ∈ I,
          Nat.choose n (k i) * Nat.choose m (s i) * A i * B i : ℕ) : ℚ) /
        ((n.factorial * tau ^ n : ℕ) : ℚ)) =
      ∑ i ∈ I, normalizedSummand n m tau k s A B i := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
      have hka : k a ≤ n := hk a (Finset.mem_insert_self a I)
      have hkI : ∀ i ∈ I, k i ≤ n := by
        intro i hi
        exact hk i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.cast_add]
      rw [div_eq_mul_inv, add_mul, ← div_eq_mul_inv, ← div_eq_mul_inv]
      rw [ih hkI]
      congr 1
      simpa only [Nat.cast_mul, normalizedSummand] using
        (Normalization.choose_cells_labels_normalized
          hka htau (A a : ℚ) (B a : ℚ))

/-- Unrooted bridge normalization.  The hypothesis is exactly the raw
cardinality identity delivered by an oriented bridge coproduct:

`2 * bridge = color * sum(raw component products)`.

No action is assumed free, and no division by a cardinality is performed
before its nonzeroness is proved. -/
theorem unrooted_bridge_convolution_of_cardinality
    (I : Finset ι) (n m tau color bridge : ℕ)
    (k s A B : ι → ℕ)
    (hk : ∀ i ∈ I, k i ≤ n) (htau : 0 < tau)
    (hraw :
      2 * bridge = color *
        ∑ i ∈ I,
          Nat.choose n (k i) * Nat.choose m (s i) * A i * B i) :
    (bridge : ℚ) / ((n.factorial * tau ^ n : ℕ) : ℚ) =
      ((color : ℚ) / 2) *
        ∑ i ∈ I, normalizedSummand n m tau k s A B i := by
  have htwo : (2 : ℚ) ≠ 0 := by decide
  have hrawQ :
      (2 : ℚ) * (bridge : ℚ) = (color : ℚ) *
        (((∑ i ∈ I,
          Nat.choose n (k i) * Nat.choose m (s i) * A i * B i : ℕ) : ℚ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun z : ℕ ↦ (z : ℚ)) hraw
  have hsum := normalize_raw_bridge_sum I n m tau k s A B hk htau
  apply mul_left_cancel₀ htwo
  calc
    (2 : ℚ) *
        ((bridge : ℚ) / ((n.factorial * tau ^ n : ℕ) : ℚ)) =
      ((2 : ℚ) * (bridge : ℚ)) /
        ((n.factorial * tau ^ n : ℕ) : ℚ) :=
          (mul_div_assoc (2 : ℚ) (bridge : ℚ)
            ((n.factorial * tau ^ n : ℕ) : ℚ)).symm
    _ = ((color : ℚ) *
          (((∑ i ∈ I,
            Nat.choose n (k i) * Nat.choose m (s i) * A i * B i : ℕ) : ℚ))) /
          ((n.factorial * tau ^ n : ℕ) : ℚ) := by rw [hrawQ]
    _ = (color : ℚ) *
          ((((∑ i ∈ I,
            Nat.choose n (k i) * Nat.choose m (s i) * A i * B i : ℕ) : ℚ) /
            ((n.factorial * tau ^ n : ℕ) : ℚ))) :=
              mul_div_assoc _ _ _
    _ = (color : ℚ) *
          ∑ i ∈ I, normalizedSummand n m tau k s A B i := by rw [hsum]
    _ = (2 : ℚ) *
          (((color : ℚ) / 2) *
            ∑ i ∈ I, normalizedSummand n m tau k s A B i) := by
              rw [← mul_assoc, mul_div_cancel₀ (color : ℚ) htwo]

/-- Rooted bridge normalization.  Since the base-containing component is
distinguished, the raw identity and the normalized convolution have no
orientation factor `2`. -/
theorem rooted_bridge_convolution_of_cardinality
    (I : Finset ι) (n m tau color bridge : ℕ)
    (k s A B : ι → ℕ)
    (hk : ∀ i ∈ I, k i ≤ n) (htau : 0 < tau)
    (hraw :
      bridge = color *
        ∑ i ∈ I,
          Nat.choose n (k i) * Nat.choose m (s i) * A i * B i) :
    (bridge : ℚ) / ((n.factorial * tau ^ n : ℕ) : ℚ) =
      (color : ℚ) *
        ∑ i ∈ I, normalizedSummand n m tau k s A B i := by
  have hrawQ :
      (bridge : ℚ) = (color : ℚ) *
        (((∑ i ∈ I,
          Nat.choose n (k i) * Nat.choose m (s i) * A i * B i : ℕ) : ℚ)) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun z : ℕ ↦ (z : ℚ)) hraw
  have hsum := normalize_raw_bridge_sum I n m tau k s A B hk htau
  rw [hrawQ, mul_div_assoc, hsum]


end
end BridgeConvolutionNormalization
end FacetPairing
end PolytopeCounting
