import FormalSchemes.GlueDataTopFiniteType
import FormalSchemes.GeneralFibreProductExposeXStructMap

set_option linter.style.header false

/-!
# A charted datum with tf-type charts is of finite type over the base (EGA I §10.13)

`FormalScheme.GlueData.isRelativelyTopFiniteType_of_patches`
(`FormalSchemes.GlueDataTopFiniteType`, issue 808) is the general criterion: a formal scheme glued
from tf-type affine patches, along a structural morphism restricting to the patches' own, is
topologically of finite type over `Spf R`. It asks for four things — a tf-type presentation of each
patch algebra, an identification of each patch with `Spf` of it, the glued structural morphism, and
the chart law relating them.

An `AlgebraicGeometry.AffineChartedFibreDatumX` already carries all four, generically:

* its charts are `Spf (I·A_i)` **by construction** (`xGlueData'` takes
  `U i := locallyRingedSpaceObj (I.map (algebraMap R (A i)))`), so the identification is
  `Iso.refl _` — the same witness `xFormalGlueData` supplies for its own `isFormalScheme` field;
* `xStructMapChart i` is the chart's own structural morphism `Spf(A i) ⟶ Spf R`; and
* `ι_xStructMap` (`FormalSchemes.GeneralFibreProductExposeXStructMap`) is exactly the chart law,
  since `xStructMap` is *defined* by `glueMorphisms` from the `xStructMapChart i`.

So the criterion applies to every charted datum at once, with the tf-type hypothesis on the chart
algebras as the only input. That is what this file records.

## What this replaces

Nothing, yet — it is purely additive. The tf-type values on master
(`tateCurveModel_isRelativelyTopFiniteType`, `FormalSchemes.TateTopFiniteType`) are about
`tateCurveFormalGlueData`, which is a bare `FormalScheme.GlueData` and not a charted datum, so it
is not an instance of this theorem and is left alone. The first consumer is the three-chart open
cover (`FormalSchemes.ThreeChartCoverTopFiniteType`); any future charted datum gets its finite-type
half by supplying one hypothesis.

## The ideal-of-definition spelling

The hypothesis is stated at the **canonical** ideal `I·A_i = I.map (algebraMap R (A i))`, not at a
general `L i`, because that is the ideal the datum's own charts are built at: `xGlueData'.U i` is
`locallyRingedSpaceObj (I.map (algebraMap R (A i)))` and the datum's `isAdic` field is an instance
for that spelling. A consumer holding `IsTopologicallyFiniteType R I (A i) (L i)` converts with
`IsTopologicallyFiniteType.map_eq`.

## Main results

* `AlgebraicGeometry.AffineChartedFibreDatumX.xStructMap_isRelativelyTopFiniteType`: **a charted
  datum whose chart algebras are topologically of finite type over `(R, I)` has a structural
  morphism topologically of finite type.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
-/

noncomputable section

open CategoryTheory FormalSpectrum

universe u

namespace AlgebraicGeometry

namespace AffineChartedFibreDatumX

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG} [TopologicalSpace R] [IsAdicRing I]
variable {B : Type u} [CommRing B] [Algebra R B]
variable (D : AffineChartedFibreDatumX R I hI B)

/-- **A charted datum with tf-type charts is topologically of finite type over `Spf R`**
(EGA I §10.13): if every chart algebra `A i` is topologically of finite type over `(R, I)` at its
canonical ideal of definition `I·A_i`, then the glued structural morphism `xStructMap` is
relatively topologically of finite type.

The proof is `FormalScheme.GlueData.isRelativelyTopFiniteType_of_patches` applied once. The patch
identification is `Iso.refl _`, available because the datum's charts are *definitionally*
`Spf (I·A_i)`, and the chart law is `ι_xStructMap` up to `Category.id_comp`.

That last step is deliberately term-mode. In tactic mode `rw [Category.id_comp]` fails with
*"Did not find an occurrence of the pattern"* and a `Full error:` tail reporting that the goal is
not type-correct at `instances` transparency: the criterion's index is
`D.xFormalGlueData.toLocallyRingedSpaceGlueData.J`, which is `D.J` only by unfolding. Term-mode
application elaborates at default transparency and the mismatch never arises. -/
theorem xStructMap_isRelativelyTopFiniteType
    (h : letI := D.commRing; letI := D.algebra; letI := D.topology; letI := D.isAdic;
      ∀ i, IsTopologicallyFiniteType R I (D.A i) (I.map (algebraMap R (D.A i)))) :
    FormalScheme.IsRelativelyTopFiniteType R I (FormalScheme.Hom.mk D.xStructMap) := by
  letI := D.commRing
  letI := D.algebra
  letI := D.topology
  letI := D.isAdic
  exact FormalScheme.GlueData.isRelativelyTopFiniteType_of_patches D.xFormalGlueData h
    (fun _ => Iso.refl _) D.xStructMap
    (fun i => (Category.id_comp _).trans (D.ι_xStructMap i))

end AffineChartedFibreDatumX

end AlgebraicGeometry

end
