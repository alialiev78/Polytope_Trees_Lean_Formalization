module

public import Proofs.AllocationLabelImage

@[expose] public section

set_option backward.dsimp.instances true

set_option backward.isDefEq.respectTransparency false

/-!
# Cancellation of allocation normalization

After a bridge component has been reindexed to a canonical dart type, its
numerical boundary labels are converted to a chosen ambient label block.
The forward numerical cut later recovers the image of that block and labels
the image subtype canonically again.  This file proves that the composite is
exactly the original numerical label, including all dependent transports.
-/

namespace PolytopeCounting
namespace FacetPairing
namespace AllocationNormalization

noncomputable section

universe uX uI

variable {X : Type uX} {I : Type uI}
  [Fintype X] [Fintype I] [DecidableEq I]

/-- The literal image finset of a finite map. -/
def mapImage (f : X → I) : Finset I :=
  Finset.univ.image f

@[simp]
theorem mem_mapImage_iff (f : X → I) (i : I) :
    i ∈ mapImage f ↔ ∃ x, f x = i := by
  simp [mapImage]

/-- If a map is pointwise the value map of an equivalence onto `A`, its
image is exactly `A`. -/
theorem mapImage_eq_allocation
    (A : Finset I) (e : X ≃ {i : I // i ∈ A})
    (f : X → I) (hfe : ∀ x, f x = (e x).1) :
    mapImage f = A := by
  ext i
  constructor
  · intro hi
    obtain ⟨x, hx⟩ := (mem_mapImage_iff f i).mp hi
    rw [hfe x] at hx
    simpa [← hx] using (e x).2
  · intro hi
    let x := e.symm ⟨i, hi⟩
    apply (mem_mapImage_iff f i).mpr
    refine ⟨x, ?_⟩
    rw [hfe]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)

/-- Transport from the recovered image subtype back to the originally
chosen allocation subtype.  It changes no underlying value. -/
def imageToAllocation
    (A : Finset I) (e : X ≃ {i : I // i ∈ A})
    (f : X → I) (hfe : ∀ x, f x = (e x).1) :
    {i : I // i ∈ mapImage f} ≃ {i : I // i ∈ A} :=
  Set.equivOfEq (by
    ext i
    exact Finset.ext_iff.mp (mapImage_eq_allocation A e f hfe) i)

@[simp]
theorem imageToAllocation_val
    (A : Finset I) (e : X ≃ {i : I // i ∈ A})
    (f : X → I) (hfe : ∀ x, f x = (e x).1)
    (i : {i : I // i ∈ mapImage f}) :
    (imageToAllocation A e f hfe i).1 = i.1 := by
  rfl

/-- Recovering the image subtype and transporting it back to `A` is exactly
the original equivalence `e`. -/
theorem imageEquiv_roundTrip
    (A : Finset I) (e : X ≃ {i : I // i ∈ A})
    (f : X → I) (hf : Function.Injective f)
    (hfe : ∀ x, f x = (e x).1) :
    (NumericalBridgeCut.equivFinsetImage f hf).trans
        (imageToAllocation A e f hfe) = e := by
  ext x
  exact hfe x

/-- The complete label cancellation used by numerical bridge components.

Start with a numerical label `label : X ≃ Fin A.card`, reinterpret it as
an allocated ambient label, recover the image subtype by the forward cut,
and finally apply the canonical numerical labelling of `A`.  The result is
literally `label`. -/
theorem allocatedLabel_roundTrip
    (A : Finset I) (label : X ≃ Fin A.card)
    (f : X → I) (hf : Function.Injective f)
    (hfe : ∀ x,
      f x = ((label.trans
        (NumericalBridgeCut.finsetSubtypeEquivFin A).symm) x).1) :
    (NumericalBridgeCut.equivFinsetImage f hf).trans
        ((imageToAllocation A
          (label.trans
            (NumericalBridgeCut.finsetSubtypeEquivFin A).symm)
          f hfe).trans
            (NumericalBridgeCut.finsetSubtypeEquivFin A)) = label := by
  let e := label.trans
    (NumericalBridgeCut.finsetSubtypeEquivFin A).symm
  calc
    (NumericalBridgeCut.equivFinsetImage f hf).trans
          ((imageToAllocation A e f hfe).trans
            (NumericalBridgeCut.finsetSubtypeEquivFin A)) =
        ((NumericalBridgeCut.equivFinsetImage f hf).trans
          (imageToAllocation A e f hfe)).trans
            (NumericalBridgeCut.finsetSubtypeEquivFin A) := by
              rfl
    _ = e.trans (NumericalBridgeCut.finsetSubtypeEquivFin A) := by
      rw [imageEquiv_roundTrip]
    _ = label := by
      ext x
      simp [e]

/-- Cardinal equality between the recovered image and the stored block. -/
theorem card_mapImage_eq
    (A : Finset I) (e : X ≃ {i : I // i ∈ A})
    (f : X → I) (hfe : ∀ x, f x = (e x).1) :
    (mapImage f).card = A.card := by
  rw [mapImage_eq_allocation A e f hfe]


end
end AllocationNormalization
end FacetPairing
end PolytopeCounting
