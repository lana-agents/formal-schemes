import FormalSchemes.GlueDataCarrier

set_option linter.style.header false

/-!
# How two pieces of a glued locally ringed space meet

For a `LocallyRingedSpace.GlueData` `D`, two pieces `U i`, `U j` of the glued space `D.glued` meet
exactly along the image of their overlap `V(i, j)`. This file records that in two forms, both
obtained by transporting a `TopCat.GlueData` statement across the carrier comparison isomorphism
`AlgebraicGeometry.LocallyRingedSpace.GlueData.isoCarrier` (`FormalSchemes.GlueDataCarrier`):

* the **containment** form, `range (ι i) ∩ range (ι j) ⊆ range (f i j ≫ ι i)`, from
  `TopCat.GlueData.image_inter`;
* the **preimage** form, `ι j ⁻¹' range (ι i) = range (f j i)`, from
  `TopCat.GlueData.preimage_range` — an equality, and the shape a chart-by-chart argument wants,
  since it says *which* part of the `j`-th piece lands in the `i`-th.

Both go through `isoCarrier_hom_ι_base`, which is `ι_isoCarrier_inv` read at a point.

The complementary disjointness statement (empty overlap ⇒ disjoint ranges) is
`LocallyRingedSpace.GlueData.range_ι_disjoint_of_isEmpty_V`; this file records the *positive* forms
for pieces that do meet. The containment form is the geometric input used to rule out the
neighbouring translate of a properly-discontinuous action fixing a patch: if a piece equals its
translate, the overlap inclusion would have to be surjective.

## Main results

* `LocallyRingedSpace.GlueData.isoCarrier_hom_ι_base`: the carrier comparison isomorphism carries
  `(ι k).base` to the topological gluing's `ι k`.
* `LocallyRingedSpace.GlueData.range_ι_inter_subset`: on underlying spaces,
  `range (ι i) ∩ range (ι j) ⊆ range (f i j ≫ ι i)`.
* `LocallyRingedSpace.GlueData.preimage_range_ι`: on underlying spaces,
  `ι j ⁻¹' range (ι i) = range (f j i)`.

## References

* `TopCat.GlueData.image_inter` and `TopCat.GlueData.preimage_range` (Mathlib), the topological
  inputs.
* `AlgebraicGeometry.Scheme.GlueData` (Mathlib), the scheme analogue.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.GlueData

variable (D : LocallyRingedSpace.GlueData.{u})

local notation "𝖣" => D.toGlueData

/-- **Transport of a glued inclusion through the carrier comparison isomorphism**: applying
`isoCarrier.hom` to a point of the image of `ι k` recovers the corresponding point of the underlying
topological gluing. This is `ι_isoCarrier_inv` read at a point, and it is what every transport of a
`TopCat.GlueData` statement down to a `LocallyRingedSpace.GlueData` goes through. -/
theorem isoCarrier_hom_ι_base (k : D.J) (a : (𝖣.U k).carrier) :
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
    ⟨⟨a, (isoCarrier_hom_ι_base D i a).symm.trans (congrArg _ ha)⟩,
      ⟨b, (isoCarrier_hom_ι_base D j b).symm.trans (congrArg _ hb)⟩⟩
  rw [D.topGlueData.image_inter i j] at hmem
  obtain ⟨v, hv⟩ := hmem
  rw [ConcreteCategory.comp_apply] at hv
  -- `v : V(i, j)`; the point `(f i j ≫ ι i) v` maps to `isoCarrier.hom x`, hence equals `x`.
  refine ⟨v, hinj ?_⟩
  calc D.isoCarrier.hom ((𝖣.f i j ≫ 𝖣.ι i).base v)
      = D.isoCarrier.hom ((𝖣.ι i).base ((𝖣.f i j).base v)) := rfl
    _ = D.topGlueData.ι i ((𝖣.f i j).base v) := isoCarrier_hom_ι_base D i _
    _ = D.isoCarrier.hom x := hv

/-- **The part of one piece that lands in another is the range of the overlap inclusion.** The
preimage under `ι j` of the range of `ι i` is exactly the range of `f j i`, the inclusion of the
overlap `V(j, i)` into the `j`-th piece. This is the locally-ringed-space analogue of
`TopCat.GlueData.preimage_range`, transported across `isoCarrier`, and it strengthens
`range_ι_inter_subset` from a containment to an equality by naming the *source* of the intersection
inside `U j` rather than its image in the glued space. -/
theorem preimage_range_ι (i j : D.J) :
    ⇑(𝖣.ι j).base ⁻¹' Set.range ⇑(𝖣.ι i).base = Set.range ⇑(𝖣.f j i).base := by
  have hinj : Function.Injective ⇑D.isoCarrier.hom := (TopCat.homeoOfIso D.isoCarrier).injective
  -- The topological statement, whose right-hand side is `(𝖣.f j i).base` on the nose.
  have key := Set.ext_iff.mp (D.topGlueData.preimage_range i j)
  ext x
  rw [Set.mem_preimage]
  refine (?_ : _ ↔ D.topGlueData.toGlueData.ι j x ∈
    Set.range ⇑(D.topGlueData.toGlueData.ι i)).trans (key _)
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [← isoCarrier_hom_ι_base, ← isoCarrier_hom_ι_base, ha]⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, hinj ?_⟩
    rw [isoCarrier_hom_ι_base, isoCarrier_hom_ι_base, ha]

end AlgebraicGeometry.LocallyRingedSpace.GlueData
