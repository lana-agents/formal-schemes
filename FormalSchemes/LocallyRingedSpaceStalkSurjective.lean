import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

set_option linter.style.header false

/-!
# Surjectivity of stalk maps is stable under composition

Two pieces of bookkeeping, wanted whenever a closed-immersion-shaped predicate is checked on a
composite: surjectivity of the underlying ring homomorphism is preserved by composition in
`CommRingCat`, and — through `AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp`, which factors
the stalk map of a composite — so is surjectivity of the stalk maps of a morphism of locally
ringed spaces.

## Why this file exists, and why it is this low

Both statements were declared in `FormalSchemes/TateSeparated.lean`, as helpers of a fifty-line
stalk computation that PR #584 replaced by a three-line application of
`AlgebraicGeometry.surjective_stalkMap_of_retraction` (issue 1739). That left them with no
consumer anywhere on the tree, parked in a Tate file above every module that could have used
them (issue 1755).

Neither mentions a ring, an ideal, a spectrum, a formal scheme or a group action, so — following
`FormalSchemes/LocallyRingedSpaceHomExt.lean` and
`FormalSchemes/LocallyRingedSpaceBasisComponent.lean`, which make the same argument for the same
reason — they sit directly on Mathlib, in the import closure of everything that could want them.

That placement is forced rather than preferred here, and the measurement is the point:
`AlgebraicGeometry.FormalScheme.IsClosedImmersion.comp` (`FormalSchemes.ClosedImmersion`) had
re-proved both of them inline, and that module is **below** `FormalSchemes.TateSeparated`, where
they used to live, and below `FormalSchemes.ClosedImmersionSplitMono`, the file that owns the
general stalk-surjectivity statements. Either of those homes would have left the one consumer on
the tree unable to reach them.

## Main results

* `AlgebraicGeometry.surjective_hom_comp`: surjectivity of the underlying ring homomorphism is
  preserved by composition in `CommRingCat`.
* `AlgebraicGeometry.surjective_stalkMap_comp`: surjectivity of stalk maps is stable under
  composition.

## What is *not* here

**Nothing about the converse.** Extracting surjectivity of a factor from surjectivity of a
composite is `Function.Surjective.of_comp`, and the locally ringed space form of it that this
project uses is `AlgebraicGeometry.surjective_stalkMap_of_retraction`
(`FormalSchemes.ClosedImmersionSplitMono`), which is above this file and stays there.

**Nothing about open immersions.** A companion pair — that an open immersion has surjective stalk
maps, and that stalk-map surjectivity may be cancelled on the right along one — was declared
beside these two and is deleted rather than moved by issue 1755: neither had a consumer or an
inline re-proof anywhere, and the first is one line off the `IsIso` instance Mathlib supplies for
the stalk map of an open immersion.

## References

* [The Stacks Project, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ).
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

/-- Surjectivity of the underlying ring hom is preserved by composition in `CommRingCat`. -/
theorem surjective_hom_comp {X Y Z : CommRingCat} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Function.Surjective f.hom) (hg : Function.Surjective g.hom) :
    Function.Surjective (f ≫ g).hom := by
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact hg.comp hf

/-- Surjectivity of stalk maps is stable under composition: if the stalk map of `g` over the image
of `x` is surjective and the stalk map of `f` at `x` is surjective, then so is the stalk map of
`f ≫ g` at `x`.

`AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp` factors the composite's stalk map, and
`AlgebraicGeometry.surjective_hom_comp` composes the two surjections. -/
theorem surjective_stalkMap_comp {X Y Z : LocallyRingedSpace} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hg : Function.Surjective (g.stalkMap (f.base x)).hom)
    (hf : Function.Surjective (f.stalkMap x).hom) :
    Function.Surjective ((f ≫ g).stalkMap x).hom := by
  rw [LocallyRingedSpace.stalkMap_comp]
  exact surjective_hom_comp hg hf

end AlgebraicGeometry

end
