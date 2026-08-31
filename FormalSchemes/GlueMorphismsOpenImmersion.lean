import FormalSchemes.GlueMorphisms

set_option linter.style.header false

/-!
# When a morphism glued out of a formal scheme is an open immersion

`AlgebraicGeometry.FormalScheme.GlueData.glueMorphisms` (`FormalSchemes.GlueMorphisms`) assembles a
family `k i : U i ⟶ Y` of morphisms out of the pieces of a glue datum, agreeing on the double
overlaps, into a single morphism `glued ⟶ Y`. This file gives the criterion under which that glued
morphism is an **open immersion**, i.e. under which the glued object is an open subspace of `Y`:

> each `k i` is an open immersion, **and** the pieces meet in `Y` only where the glue datum says
> they do — `range (k i) ∩ range (k j) ⊆ range (f i j ≫ k i)`.

The second condition is the whole content. Without it the glued object can map onto the union of
the `range (k i)` while identifying too few points: the line with two origins is glued from two
copies of `𝔸¹` whose images in `𝔸¹` meet in all of `𝔸¹ ∖ {0}` *plus* the origin, which is more
than the overlap accounts for. The hypothesis is exactly what rules that out, and it is what makes
the proof of injectivity go through — everything else is formal.

It is asked for only at `i ≠ j`. On the diagonal the containment follows from injectivity of the
piece alone, so a caller never has to supply it; earlier versions of these statements quantified
over all `i j`, and the one consumer that supplied the diagonal case by hand
(`AlgebraicGeometry.AffineChartedFibreDatumX.isOpenImmersion_glueChartMorphisms`) no longer does.

**Everything here is a wrapper over `FormalSchemes.LocallyRingedSpaceGlueDesc`**, which proves all
seven statements for a bare `AlgebraicGeometry.LocallyRingedSpace.GlueData`; the formal-scheme
condition on the pieces is used nowhere in any of the arguments. The proofs — including the
injectivity argument the paragraph above describes — live there, once.

## Comparison with `FormalScheme.OpenCover.fromGlued`

`FormalSchemes.OpenCoverGlueMorphisms` proves the special case where the `k i` are the members of an
open cover *of `Y` itself*: there `fromGlued` is not merely an open immersion but an isomorphism,
because the cover is jointly surjective. The argument there routes injectivity through the pullback
`U i ×_Y U j` and openness through `GlueData.isOpen_iff`. Neither is needed here: the overlap
hypothesis above is weaker than "the overlap *is* the pullback" and is checked directly, and the
image of an open set is computed chartwise as `⋃ i, k i '' (ι i ⁻¹' U)`, which is open because each
`k i` is. The two files are therefore independent rather than one generalising the other.

## Main results

* `AlgebraicGeometry.FormalScheme.GlueData.range_glueMorphisms`: the range of the glued morphism is
  the union of the ranges of the `k i`.
* `AlgebraicGeometry.FormalScheme.GlueData.image_glueMorphisms`: the image of a set, computed
  chartwise.
* `AlgebraicGeometry.FormalScheme.GlueData.injective_glueMorphisms`: injectivity on points, from the
  overlap hypothesis.
* `AlgebraicGeometry.FormalScheme.GlueData.isOpenMap_glueMorphisms`,
  `isOpenEmbedding_glueMorphisms`, `isIso_stalkMap_glueMorphisms`.
* `AlgebraicGeometry.FormalScheme.GlueData.isOpenImmersion_glueMorphisms`: **the criterion.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6, §10.15.
* `AlgebraicGeometry.Scheme.GlueData` (Mathlib), the scheme analogue of the gluing bookkeeping.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

namespace FormalScheme.GlueData

variable (D : FormalScheme.GlueData.{u}) {Y : LocallyRingedSpace.{u}}
variable (k : ∀ i, D.toLocallyRingedSpaceGlueData.toGlueData.U i ⟶ Y)
variable (h : ∀ i j, D.toLocallyRingedSpaceGlueData.toGlueData.f i j ≫ k i =
  D.toLocallyRingedSpaceGlueData.toGlueData.t i j ≫
    D.toLocallyRingedSpaceGlueData.toGlueData.f j i ≫ k j)

/-- **The range of the glued morphism is the union of the ranges of the chart morphisms.** -/
theorem range_glueMorphisms :
    Set.range (D.glueMorphisms k h).base = ⋃ i, Set.range (k i).base :=
  D.toLocallyRingedSpaceGlueData.range_desc k h

/-- **The image of a set under the glued morphism, computed chartwise.** -/
theorem image_glueMorphisms (U : Set (D.gluedFormalScheme).toLocallyRingedSpace) :
    (D.glueMorphisms k h).base '' U = ⋃ i, (k i).base '' ((D.ι i).base ⁻¹' U) :=
  D.toLocallyRingedSpaceGlueData.image_desc k h U

/-- **The glued morphism is injective on points**, provided each chart morphism is and the charts
meet in `Y` only along their glue overlap.

The overlap hypothesis is asked for only at `i ≠ j`; on the diagonal it follows from injectivity of
the piece alone, so a caller never has to supply it. -/
theorem injective_glueMorphisms
    (hinj : ∀ i, Function.Injective (k i).base)
    (hmeet : ∀ i j, i ≠ j → Set.range (k i).base ∩ Set.range (k j).base ⊆
      Set.range (D.toLocallyRingedSpaceGlueData.toGlueData.f i j ≫ k i).base) :
    Function.Injective (D.glueMorphisms k h).base :=
  D.toLocallyRingedSpaceGlueData.injective_desc k h hinj hmeet

/-- **The glued morphism is an open map** as soon as every chart morphism is. -/
theorem isOpenMap_glueMorphisms (hopen : ∀ i, IsOpenMap (k i).base) :
    IsOpenMap (D.glueMorphisms k h).base :=
  D.toLocallyRingedSpaceGlueData.isOpenMap_desc k h hopen

/-- **The glued morphism is a topological open embedding.** -/
theorem isOpenEmbedding_glueMorphisms (hopen : ∀ i, IsOpenMap (k i).base)
    (hinj : ∀ i, Function.Injective (k i).base)
    (hmeet : ∀ i j, i ≠ j → Set.range (k i).base ∩ Set.range (k j).base ⊆
      Set.range (D.toLocallyRingedSpaceGlueData.toGlueData.f i j ≫ k i).base) :
    IsOpenEmbedding (D.glueMorphisms k h).base :=
  D.toLocallyRingedSpaceGlueData.isOpenEmbedding_desc k h hopen hinj hmeet

/-- **The glued morphism induces isomorphisms on stalks**, by two-out-of-three against the glue
inclusion `ι i` and the chart morphism `k i`. Mirrors
`FormalScheme.OpenCover.isIso_fromGlued_stalkMap`. -/
theorem isIso_stalkMap_glueMorphisms (hoi : ∀ i, LocallyRingedSpace.IsOpenImmersion (k i))
    (x : (D.gluedFormalScheme).toLocallyRingedSpace) :
    IsIso ((D.glueMorphisms k h).stalkMap x) :=
  D.toLocallyRingedSpaceGlueData.isIso_stalkMap_desc k h hoi x

/-- **The criterion: a morphism glued from open immersions that meet only along the glue overlaps is
an open immersion.** -/
theorem isOpenImmersion_glueMorphisms (hoi : ∀ i, LocallyRingedSpace.IsOpenImmersion (k i))
    (hmeet : ∀ i j, i ≠ j → Set.range (k i).base ∩ Set.range (k j).base ⊆
      Set.range (D.toLocallyRingedSpaceGlueData.toGlueData.f i j ≫ k i).base) :
    LocallyRingedSpace.IsOpenImmersion (D.glueMorphisms k h) :=
  D.toLocallyRingedSpaceGlueData.isOpenImmersion_desc k h hoi hmeet

end FormalScheme.GlueData

end AlgebraicGeometry

end
