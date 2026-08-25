import FormalSchemes.LocallyRingedSpaceHomExt
import FormalSchemes.OpenCover

set_option linter.style.header false

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

The mathematics of the uniqueness half is not here either. It is
`AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_jointly_surjective`
(`FormalSchemes/LocallyRingedSpaceHomExt.lean`), which says the same thing for a *bare* locally
ringed space covered by open immersions; what this file adds is the reading of it at a
`FormalScheme.OpenCover`, and `exists_preimage`, which is that reading's covering hypothesis.

## Route

Equality of locally ringed space morphisms is local on the source and detected on base points and
on stalks. Since the cover maps are open immersions, their stalk maps are isomorphisms, so the
data of `g₁`/`g₂` on each stalk `𝒪_{X,x}` is pinned down by the corresponding stalk of the piece
covering `x`. That argument — reduce to `SheafedSpace.hom_stalk_ext`, get the base maps from
joint surjectivity, cancel the (iso) stalk map of the covering open immersion — used to be written
out here. It is now written out once, in `LocallyRingedSpaceHomExt.lean`, and `hom_ext` is an
application of it.

Two things followed from the reroute and are worth knowing before editing this file. The local
`IsIso ((𝒰.map j).toLRSHom.stalkMap y)` instance is gone: it existed because the old proof needed
the stalk iso through the `FormalScheme.Hom` wrapper, and the general lemma gets it from Mathlib's
`LocallyRingedSpace.IsOpenImmersion.stalk_iso` instead. So are the file-scope
`maxHeartbeats 3200000` and `synthInstance.maxHeartbeats 1000000`, which the term proof does not
need. If you replace `hom_ext`'s proof with anything larger, expect to need them back.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4, §10.7.
* `FormalSchemes/LocallyRingedSpaceHomExt.lean` — the general statement this file specialises.
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

/-- **Uniqueness of morphisms out of an open cover.** Two morphisms `g₁ g₂ : X ⟶ Y` out of a formal
scheme `X` that agree after restriction along every map of an open cover `𝒰` are equal; the cover
maps are jointly epimorphic.

This is `LocallyRingedSpace.hom_ext_of_jointly_surjective` at a `FormalScheme.OpenCover`: the cover
maps are open immersions of locally ringed spaces and `exists_preimage` is exactly its joint
surjectivity hypothesis. Nothing about formal schemes enters the argument, which is why the general
form is stated on Mathlib alone. -/
theorem hom_ext {Y : LocallyRingedSpace.{u}}
    (g₁ g₂ : X.toLocallyRingedSpace ⟶ Y)
    (h : ∀ j, (𝒰.map j).toLRSHom ≫ g₁ = (𝒰.map j).toLRSHom ≫ g₂) :
    g₁ = g₂ :=
  LocallyRingedSpace.hom_ext_of_jointly_surjective (fun j => (𝒰.map j).toLRSHom)
    𝒰.exists_preimage h

end AlgebraicGeometry.FormalScheme.OpenCover

end
