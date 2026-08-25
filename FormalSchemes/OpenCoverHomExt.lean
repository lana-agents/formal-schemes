import FormalSchemes.OpenCover

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Uniqueness of morphisms out of an open cover of a formal scheme

Given an open cover `𝒰 : FormalScheme.OpenCover X`, a morphism out of `X` (to any locally ringed
space `Y`) is determined by its restrictions to the pieces of the cover: two morphisms
`g₁ g₂ : X ⟶ Y` that agree after precomposition with every cover map `𝒰.map j` are equal. In
other words the family `{𝒰.map j}` is jointly epimorphic. This is the "local on the source"
half of descent for morphisms of formal schemes, and the load-bearing joint-epi statement behind
the uniqueness clause of the general fibre-product universal property (EGA I §10.7).

## Scope

This file delivers only `OpenCover.hom_ext` (the uniqueness / joint-epi statement); it independently
unblocks the uniqueness brick of the fibre-product universal property. The *construction* of a
morphism out of an open cover from compatible local data is the separate, heavier half, and it is
`FormalSchemes/OpenCoverGlueMorphisms.lean` — `OpenCover.glueMorphisms` together with its
computation rule `map_glueMorphisms`. That module imports this one, so the two together are descent
for morphisms of formal schemes: existence there, uniqueness here.

This paragraph used to say the construction was *not written*, which was a statement about this file
that read as a statement about the tree, and stayed on the page after
`OpenCoverGlueMorphisms.lean` landed. Do not restore that reading; if you are checking whether a
declaration exists, grep for it.

## Route

Equality of locally ringed space morphisms is local on the source and detected on base points and
on stalks. Since the cover maps are open immersions, their stalk maps are isomorphisms, so the
data of `g₁`/`g₂` on each stalk `𝒪_{X,x}` is pinned down by the corresponding stalk of the piece
covering `x`. Concretely we reduce to `SheafedSpace.hom_stalk_ext`: the base maps agree because the
ranges of the cover maps exhaust `X`, and the stalk maps agree after cancelling the (iso) stalk map
of the covering open immersion, using `LocallyRingedSpace.stalkMap_comp`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4, §10.7.
* Mathlib `AlgebraicGeometry.Scheme.Cover.hom_ext`, `SheafedSpace.hom_stalk_ext`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.FormalScheme.OpenCover

variable {X : FormalScheme.{u}} (𝒰 : OpenCover X)

/-- Joint surjectivity of the cover maps on points: every point of `X` is the image of a point of
some piece. -/
theorem exists_preimage (x : X.toLocallyRingedSpace) :
    ∃ (j : 𝒰.J) (y : (𝒰.obj j).toLocallyRingedSpace),
      (𝒰.map j).toLRSHom.base y = x :=
  ⟨𝒰.f x, (𝒰.covers x).choose, (𝒰.covers x).choose_spec⟩

/-- The stalk map of a cover map is an isomorphism (it is an open immersion of locally ringed
spaces). -/
instance isIso_map_stalkMap (j : 𝒰.J) (y : (𝒰.obj j).toLocallyRingedSpace) :
    IsIso ((𝒰.map j).toLRSHom.stalkMap y) :=
  inferInstanceAs (IsIso ((𝒰.map j).toLRSHom.toShHom.hom.stalkMap y))

/-- **Uniqueness of morphisms out of an open cover.** Two morphisms `g₁ g₂ : X ⟶ Y` out of a formal
scheme `X` that agree after restriction along every map of an open cover `𝒰` are equal; the cover
maps are jointly epimorphic. -/
theorem hom_ext {Y : LocallyRingedSpace.{u}}
    (g₁ g₂ : X.toLocallyRingedSpace ⟶ Y)
    (h : ∀ j, (𝒰.map j).toLRSHom ≫ g₁ = (𝒰.map j).toLRSHom ≫ g₂) :
    g₁ = g₂ := by
  -- Base maps agree, pointwise, because the cover exhausts `X`.
  have hbase_pt : ∀ x : X.toLocallyRingedSpace, g₁.base x = g₂.base x := by
    intro x
    obtain ⟨j, y, rfl⟩ := 𝒰.exists_preimage x
    have hj := congrArg (fun φ : (𝒰.obj j).toLocallyRingedSpace ⟶ Y => φ.base y) (h j)
    simpa only [LocallyRingedSpace.comp_base, TopCat.comp_app] using hj
  have hbase : g₁.base = g₂.base := by
    apply ConcreteCategory.hom_ext
    exact hbase_pt
  -- Reduce to `SheafedSpace.hom_stalk_ext`.
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  refine SheafedSpace.hom_stalk_ext _ _ hbase (fun x => ?_)
  -- Stalk maps agree, after cancelling the (iso) stalk map of the covering open immersion.
  obtain ⟨j, y, rfl⟩ := 𝒰.exists_preimage x
  -- The goal is stated with `PresheafedSpace` stalk maps of `forgetToSheafedSpace.map gᵢ`, which
  -- are definitionally the `LocallyRingedSpace` stalk maps of `gᵢ`. We therefore prove the
  -- equality in `LocallyRingedSpace` terms and transport it across the defeq with `exact`.
  have key : g₁.stalkMap ((𝒰.map j).toLRSHom.base y) =
      (Y.presheaf.stalkCongr (hbase ▸ rfl)).hom ≫ g₂.stalkMap ((𝒰.map j).toLRSHom.base y) := by
    -- Cancel the (iso) stalk map of the covering open immersion on the right, assemble both sides
    -- into stalk maps of `(𝒰.map j).toLRSHom ≫ gᵢ`, then compare using `stalkMap_congr_hom` and the
    -- hypothesis `h j`.
    rw [← cancel_mono ((𝒰.map j).toLRSHom.stalkMap y), Category.assoc,
      ← LocallyRingedSpace.stalkMap_comp, ← LocallyRingedSpace.stalkMap_comp,
      LocallyRingedSpace.stalkMap_congr_hom _ _ (h j) y, TopCat.Presheaf.stalkCongr_hom]
    -- The two `stalkSpecializes` factors record the same specialization (equal points), so agree by
    -- proof irrelevance.
    rfl
  exact key

end AlgebraicGeometry.FormalScheme.OpenCover

end
