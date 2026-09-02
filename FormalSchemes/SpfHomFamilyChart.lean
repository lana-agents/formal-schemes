import FormalSchemes.ActionQuotientChartAt
import FormalSchemes.SpfHomColimitTarget

set_option linter.style.header false

/-!
# EGA I 10.6.10's target datum already charts the image of the morphism it produces

`FormalSpectrum.existsUnique_hom_thickeningMap` and its formal-affine variant
`FormalSpectrum.existsUnique_hom_thickeningMap_spfCover` build a morphism `Spf R ⟶ X` out of a
compatible family of morphisms from the infinitesimal thickenings. Both ask the target to be
**covered** by opens `U i` carrying identifications `X|_{U i} ≅ Spec (B i)`, respectively
`X|_{U i} ≅ Spf (L i)`. The construction underneath them,
`FormalSpectrum.ColimitTarget.spfHomOfFamily`, asks for **less**: the `U i` need only receive the
image of the source chart they are attached to (`hr`), and no covering hypothesis on the target
appears. That gap is what a consumer looking for a chart at a point of `X` would want to exploit —
it is the reason issue 1197 records the weaker input as "the sharpest open question here".

**This file measures the gap and finds it empty where it matters.** By
`FormalSpectrum.ColimitTarget.range_spfHomOfFamily_le` the image of the glued morphism lies in
`⋃ i, U i` regardless, so:

> every point the constructed morphism reaches lies in some `U i`, and there it is exactly as
> affine as the datum says the `U i` are.

At the two instantiations that make the `U i` affine the conclusion is a chart:

* `Spf`-shaped datum → `FormalSpectrum.hasAffineChartAt_of_spfChartFamily`;
* `Spec`-shaped datum → `FormalSpectrum.hasAffineChartAt_of_specChartFamily`.

So a construction of a chart of `X` at `y` that runs EGA I 10.6.10 with such a datum, and whose
morphism reaches `y`, must have been handed a chart at `y` as part of its input. **Dropping the
target-covering hypothesis does not weaken that.**

## What this does *not* close

The general `FormalSpectrum.ColimitTarget.spfHomOfFamily` does not ask the `U i` to be affine at
all: it asks for `e i : X|_{U i} ≅ Y i` with `FormalSpectrum.IsThickeningColimitTarget (Y i)`, a
property and not a shape. In that generality the argument here gives only

> every point in the image lies in some `U i` with `IsThickeningColimitTarget (X|_{U i})`,

which is **not** a chart. Whether an open with the colimit property but no known chart exists is a
genuinely different question, and the four producers of that property on this tree —
`FormalSpectrum.isThickeningColimitTarget_spec`, `…_spf`,
`FormalSpectrum.isThickeningColimitTarget_formalScheme` and
`FormalSpectrum.isThickeningColimitTarget_of_cover` — all hand back a formal scheme or a cover by
formal schemes. Nothing here proves they are the only ones.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.hasAffineChartAt_of_isoRestrict_spec`: the `Spec`-shaped
  companion of `LocallyRingedSpace.hasAffineChartAt_of_isoRestrict`, through
  `FormalSpectrum.specIsoSpfBot`.
* `AlgebraicGeometry.LocallyRingedSpace.formalSchemeOfSpfCover`: **the target hypothesis of
  `existsUnique_hom_thickeningMap_spfCover` already says the target is a formal scheme.** No new
  content — it is `formalSchemeOfHasAffineChartAt` fed by `hasAffineChartAt_of_isoRestrict` — and
  it is here so that the capstone's circularity is a named theorem rather than a remark.
* `FormalSpectrum.hasAffineChartAt_of_spfChartFamily` and
  `FormalSpectrum.hasAffineChartAt_of_specChartFamily`: the same conclusion from the *family*
  datum, with no covering hypothesis on the target, at every point of the image of the morphism.
  Stated for an arbitrary `g` with the right restrictions rather than for the term
  `spfHomOfFamily`, since `spfHomOfFamily_uniq` makes the two the same morphism.
* `FormalSpectrum.hasAffineChartAt_spfHomFormalLine` and
  `FormalSpectrum.formalSchemeFormalLineOfSpfCover`: non-vacuity, at the two witnesses this tree
  already carries — see the `Non-vacuity` section for what they do and do not exhibit.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **An open identified with an affine scheme is a chart at each of its points.** The
`Spec`-shaped companion of `LocallyRingedSpace.hasAffineChartAt_of_isoRestrict`: give `B` the
discrete topology, at which `FormalSpectrum.specIsoSpfBot` identifies `Spec B` with `Spf (B, ⊥)`,
and the `Spf`-shaped statement applies.

Separated from its companion because that one lives beside
`AlgebraicGeometry.LocallyRingedSpace.HasAffineChartAt` in `FormalSchemes.Gluing`, whose import
closure does not reach `FormalSchemes.SpfDiscrete` and should not be made to for one corollary —
less than ever, `FormalSchemes.Gluing` being upstream of 272 of this tree's 496 modules. -/
theorem hasAffineChartAt_of_isoRestrict_spec {X : LocallyRingedSpace.{u}} (U : Opens X.toTopCat)
    (B : Type u) [CommRing B]
    (e : X.restrict U.isOpenEmbedding ≅ Spec.locallyRingedSpaceObj (CommRingCat.of B))
    {y : X} (hy : y ∈ U) : HasAffineChartAt X y := by
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  exact hasAffineChartAt_of_isoRestrict U (⊥ : Ideal B) (e ≪≫ FormalSpectrum.specIsoSpfBot B) hy

section Cover

variable {X : LocallyRingedSpace.{u}} {ι : Type u} (U : ι → Opens X.toTopCat)
    (hU : ⨆ i, U i = ⊤) {C : ι → Type u} [∀ i, CommRing (C i)] [∀ i, TopologicalSpace (C i)]
    (L : ∀ i, Ideal (C i)) [∀ i, IsAdicRing (L i)]
    (e : ∀ i, X.restrict (U i).isOpenEmbedding ≅ FormalSpectrum.locallyRingedSpaceObj (L i))

include hU e in
/-- **A locally ringed space covered by opens identified with formal spectra has a chart
everywhere.** -/
theorem hasAffineChartAt_of_spfCover (y : X) : HasAffineChartAt X y := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hU ▸ Opens.mem_top y)
  exact hasAffineChartAt_of_isoRestrict (U i) (L i) (e i) hi

/-- **The target hypothesis of `FormalSpectrum.existsUnique_hom_thickeningMap_spfCover` already
makes the target a formal scheme.** The theorem takes a cover of `X` by opens `U i` *equipped* with
identifications `X|_{U i} ≅ Spf (L i)`, and that is character for character what
`AlgebraicGeometry.FormalScheme.local_affine` asks for.

There is no new content here: it is `LocallyRingedSpace.formalSchemeOfHasAffineChartAt` fed by
`hasAffineChartAt_of_spfCover`. It is named because "the mapping-out theorem is circular at a point
one is trying to chart" is a claim several rows of issue 1197 have made in prose, and a claim of
that kind should be a theorem. -/
def formalSchemeOfSpfCover : FormalScheme.{u} :=
  formalSchemeOfHasAffineChartAt X (hasAffineChartAt_of_spfCover U hU L e)

@[simp]
theorem formalSchemeOfSpfCover_toLocallyRingedSpace :
    (formalSchemeOfSpfCover U hU L e).toLocallyRingedSpace = X := rfl

end Cover

end AlgebraicGeometry.LocallyRingedSpace

namespace FormalSpectrum

open AlgebraicGeometry.LocallyRingedSpace

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : LocallyRingedSpace.{u}}
variable (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (hI : I.FG) {ι : Type u} (r : ι → R)
    [∀ i, IsAdicRing (awayCompletionIdeal I (r i))]
    (hcov : (⨆ i, basicOpen I (r i)) = ⊤)
    (U : ι → Opens X.toTopCat)
    (hr : ∀ i, basicOpen I (r i) ≤ (Opens.map (commonBase I f)).obj (U i))
    (g : locallyRingedSpaceObj I ⟶ X) (hg : ∀ n : ℕ, thickeningMap I n ≫ g = f n)

section SpfDatum

variable {C : ι → Type u} [∀ i, CommRing (C i)] [∀ i, TopologicalSpace (C i)]
    (L : ∀ i, Ideal (C i)) [∀ i, IsAdicRing (L i)] (hL : ∀ i, (L i).FG)
    (e : ∀ i, X.restrict (U i).isOpenEmbedding ≅ locallyRingedSpaceObj (L i))

include hf hI hcov hr hL e hg in
/-- **A formal-affine chart datum charts every point the morphism it produces reaches** — with no
covering hypothesis on the target.

The datum is the one `FormalSpectrum.ColimitTarget.spfHomOfFamily` takes: a covering family `r i`
of the *source*, and for each `i` an open `U i` of the target receiving the image of `D(r i)`,
identified with `Spf (L i)`. The morphism is any `g` restricting on the thickenings to the given
family, which by `ColimitTarget.spfHomOfFamily_uniq` is the glued one.

This is the sense in which `existsUnique_hom_thickeningMap_spfCover`'s missing `hU` buys nothing at
a point one is trying to chart: `ColimitTarget.range_spfHomOfFamily_le` puts `y` in some `U i`
anyway, and `U i` is formal-affine by hypothesis. -/
theorem hasAffineChartAt_of_spfChartFamily {y : X} (hy : y ∈ Set.range g.base) :
    HasAffineChartAt X y := by
  have hY : ∀ i, IsThickeningColimitTarget (locallyRingedSpaceObj (L i)) :=
    fun i => isThickeningColimitTarget_spf (L i) (hL i)
  have hgeq : g = ColimitTarget.spfHomOfFamily I f hf hI r hcov U hr _ e hY :=
    ColimitTarget.spfHomOfFamily_uniq I f hf hI r hcov U hr _ e hY g hg
  rw [hgeq] at hy
  obtain ⟨i, hi⟩ :=
    Set.mem_iUnion.1 (ColimitTarget.range_spfHomOfFamily_le I f hf hI r hcov U hr _ e hY hy)
  exact hasAffineChartAt_of_isoRestrict (U i) (L i) (e i) hi

end SpfDatum

section SpecDatum

variable (B : ι → Type u) [∀ i, CommRing (B i)]
    (e : ∀ i, X.restrict (U i).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (B i)))

include hf hI hcov hr e hg in
/-- **The `Spec`-shaped datum, which is the one `FormalSpectrum.existsUnique_hom_thickeningMap`
takes.** Same conclusion, same proof, with `isThickeningColimitTarget_spec` in place of
`isThickeningColimitTarget_spf` and `hasAffineChartAt_of_isoRestrict_spec` in place of its
companion. Note that the finite-generation hypothesis `hL` disappears: a `Spec`-shaped chart needs
nothing of the ring. -/
theorem hasAffineChartAt_of_specChartFamily {y : X} (hy : y ∈ Set.range g.base) :
    HasAffineChartAt X y := by
  have hY : ∀ i, IsThickeningColimitTarget
      (Spec.locallyRingedSpaceObj (CommRingCat.of (B i))) :=
    fun i => isThickeningColimitTarget_spec (B i)
  have hgeq : g = ColimitTarget.spfHomOfFamily I f hf hI r hcov U hr _ e hY :=
    ColimitTarget.spfHomOfFamily_uniq I f hf hI r hcov U hr _ e hY g hg
  rw [hgeq] at hy
  obtain ⟨i, hi⟩ :=
    Set.mem_iUnion.1 (ColimitTarget.range_spfHomOfFamily_le I f hf hI r hcov U hr _ e hY hy)
  exact hasAffineChartAt_of_isoRestrict_spec (U i) (B i) (e i) hi

end SpecDatum

/-!
### Non-vacuity

Both hypotheses are satisfiable, at the two witnesses umbrella 59 already carries. Neither witness
is a *surprising* formal scheme — `Spec ℤ` is a scheme and `Spf ℤ⟦X⟧` is a formal affine — and that
is the honest limit of what a witness for a statement of this shape can be: what they exhibit is
that the chart data these theorems consume is data one can actually produce, over a cover with two
distinct pieces, a nonempty overlap, and two different opens of the target.
-/

section Witness

open Polynomial

attribute [local instance] isAdicRing_formalLineIdeal
attribute [local instance] isAdicRing_awayCompletionIdeal_formalLineElem

/-- **The `Spec`-shaped family datum, at `Spf ℤ⟦X⟧ ⟶ Spec ℤ`.** `FormalSchemes.SpfHomOfFamily`'s
witness supplies every input: the covering family `2`, `3` of `ℤ⟦X⟧`, the target opens `D(2)`,
`D(3)` of `Spec ℤ` with `formalLine_hr`, their affine identifications, and the glued morphism with
its computation rule. So every point of `Spec ℤ` in the image of `spfHomFormalLine` gets a chart
out of the datum alone.

This is the general theorem run end to end on data that was assembled for a different purpose,
which is the point: the hypotheses are not a private shape invented here. -/
theorem hasAffineChartAt_spfHomFormalLine {y : witnessTarget}
    (hy : y ∈ Set.range spfHomFormalLine.base) : HasAffineChartAt witnessTarget y :=
  hasAffineChartAt_of_specChartFamily formalLineIdeal witnessFamily.1 witnessFamily.2
    (polyXIdeal_fg.map _) formalLineElem iSup_basicOpen_formalLineElem formalLineOpen
    formalLine_hr spfHomFormalLine thickeningMap_comp_spfHomFormalLine formalLineChartRing
    formalLineChartIso hy

/-- **The `Spf`-shaped cover datum, at `Spf ℤ⟦X⟧` covered by `D(2)` and `D(3)`.**
`FormalSchemes.SpfHomColimitTarget`'s witness supplies the two proper, overlapping formal-affine
pieces and their identifications, and `formalSchemeOfSpfCover` turns them into a formal scheme.

`Spf ℤ⟦X⟧` is of course already one — `isThickeningColimitTarget_formalLine` says so directly, and
that file records the same limitation about its own witness. What this exhibits is that the
*target hypothesis* of `existsUnique_hom_thickeningMap_spfCover` is satisfiable by a cover that is
genuinely formal and genuinely has more than one piece, so the circularity
`formalSchemeOfSpfCover` records is not a statement about a hypothesis nobody can meet. -/
def formalSchemeFormalLineOfSpfCover : FormalScheme.{0} :=
  formalSchemeOfSpfCover formalLineFormalOpen iSup_basicOpen_formalLineElem _
    formalLineFormalChartIso

@[simp]
theorem formalSchemeFormalLineOfSpfCover_toLocallyRingedSpace :
    formalSchemeFormalLineOfSpfCover.toLocallyRingedSpace =
      locallyRingedSpaceObj formalLineIdeal := rfl

end Witness

end FormalSpectrum
