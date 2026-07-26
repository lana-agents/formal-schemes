import FormalSchemes.GlueDataCarrier

set_option linter.style.header false

/-!
# Image intersection for a glued locally ringed space

For a `LocallyRingedSpace.GlueData` `D`, two pieces `U i`, `U j` of the glued space `D.glued` meet
exactly along the image of their overlap `V(i, j)`: the intersection of the ranges of the inclusions
`ι i`, `ι j` is contained in the range of the overlap inclusion `f i j ≫ ι i`. This is the
locally-ringed-space analogue of the containment half of `TopCat.GlueData.image_inter`, obtained by
transporting the topological statement across the carrier comparison isomorphism
`AlgebraicGeometry.LocallyRingedSpace.GlueData.isoCarrier` (`FormalSchemes.GlueDataCarrier`).

The complementary disjointness statement (empty overlap ⇒ disjoint ranges) is
`LocallyRingedSpace.GlueData.range_ι_disjoint_of_isEmpty_V`; this file records the *positive* form
for pieces that do meet. It is the geometric input used to rule out the neighbouring translate of a
properly-discontinuous action fixing a patch: if a piece equals its translate, the overlap inclusion
would have to be surjective.

## Main results

* `LocallyRingedSpace.GlueData.range_ι_inter_subset`: on underlying spaces,
  `range (ι i) ∩ range (ι j) ⊆ range (f i j ≫ ι i)`.

## References

* `TopCat.GlueData.image_inter` (Mathlib), the topological input.
* `AlgebraicGeometry.Scheme.GlueData` (Mathlib), the scheme analogue.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.GlueData

variable (D : LocallyRingedSpace.GlueData.{u})

local notation "𝖣" => D.toGlueData

/-- Transport of a glued inclusion through the carrier comparison isomorphism: applying
`isoCarrier.hom` to a point of the image of `ι k` recovers the corresponding point of the underlying
topological gluing. -/
private theorem hom_isoCarrier_ι_base (k : D.J) (a : (𝖣.U k).carrier) :
    D.isoCarrier.hom ((𝖣.ι k).base a) = D.topGlueData.ι k a := by
  have h := ConcreteCategory.congr_hom (D.ι_isoCarrier_inv k) a
  rw [ConcreteCategory.comp_apply] at h
  calc D.isoCarrier.hom ((𝖣.ι k).base a)
      = D.isoCarrier.hom (D.isoCarrier.inv (D.topGlueData.ι k a)) := congrArg _ h.symm
    _ = D.topGlueData.ι k a := Iso.inv_hom_id_apply _ _

/-- **Image intersection for a glued locally ringed space (containment half).** The intersection of
the ranges of the inclusions `ι i`, `ι j` into the glued space is contained in the range of the
overlap inclusion `f i j ≫ ι i`: two pieces meet only along the image of their overlap object
`V(i, j)`. This is the locally-ringed-space analogue of the containment half of
`TopCat.GlueData.image_inter`, transported across the carrier comparison isomorphism
`isoCarrier`. -/
theorem range_ι_inter_subset (i j : D.J) :
    Set.range (𝖣.ι i).base ∩ Set.range (𝖣.ι j).base ⊆
      Set.range (𝖣.f i j ≫ 𝖣.ι i).base := by
  rintro x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hinj : Function.Injective ⇑D.isoCarrier.hom := (TopCat.homeoOfIso D.isoCarrier).injective
  -- `isoCarrier.hom x` lies in both topological ranges, so `image_inter` gives a point of `V(i,j)`.
  have hmem : D.isoCarrier.hom x ∈
      Set.range ⇑(D.topGlueData.ι i) ∩ Set.range ⇑(D.topGlueData.ι j) :=
    ⟨⟨a, (hom_isoCarrier_ι_base D i a).symm.trans (congrArg _ ha)⟩,
      ⟨b, (hom_isoCarrier_ι_base D j b).symm.trans (congrArg _ hb)⟩⟩
  rw [D.topGlueData.image_inter i j] at hmem
  obtain ⟨v, hv⟩ := hmem
  rw [ConcreteCategory.comp_apply] at hv
  -- `v : V(i, j)`; the point `(f i j ≫ ι i) v` maps to `isoCarrier.hom x`, hence equals `x`.
  refine ⟨v, hinj ?_⟩
  calc D.isoCarrier.hom ((𝖣.f i j ≫ 𝖣.ι i).base v)
      = D.isoCarrier.hom ((𝖣.ι i).base ((𝖣.f i j).base v)) := rfl
    _ = D.topGlueData.ι i ((𝖣.f i j).base v) := hom_isoCarrier_ι_base D i _
    _ = D.isoCarrier.hom x := hv

end AlgebraicGeometry.LocallyRingedSpace.GlueData
