import FormalSchemes.BasicOpenDisjointUnion
import FormalSchemes.OpenImmersionIsoOfRangeEq
import FormalSchemes.TateCurveModel

set_option linter.style.header false

/-!
# The Tate two-chart overlap is a single affine chart, as a morphism over `Spf A`

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`, and let
`A = R{x, y}/(x·y − q)` be the coordinate ring of the formal Tate annulus. The two-chart circular
model `𝔈_q = tateCurveModel` glues two copies of `Spf A` along the overlap object

```
Spf A{1/x} ⨿ Spf A{1/y}   --coprod.desc annulusOverlapChart annulusOverlapChartY-->   Spf A
```

whereas `AlgebraicGeometry.AffineChartedFibreDatum` demands that each overlap be a **single**
basic-open chart `Spf A{1/g} ⟶ Spf A`. `FormalSchemes.BasicOpenDisjointUnion` (601a) showed the
two presentations have the same underlying subspace, `D(x) ⊔ D(y) = D(x + y)`. This file upgrades
that set-level equality to the morphism-level statement the datum actually consumes:

```
basicOpenChart (I·A) (x + y)  =  (tateOverlapChartIso …).hom ≫
  coprod.desc (annulusOverlapChart …) (annulusOverlapChartY …)
```

## Why this is cheap

No ring-theoretic input is needed, and in particular one does **not** need "`Spf` of a product ring
is a coproduct". Both morphisms are open immersions into the *same* `Spf A` with the *same* range,
so the isomorphism and both factorisation laws come straight from the universal property of open
immersions, via `LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq`
(`FormalSchemes.OpenImmersionIsoOfRangeEq`). The algebraic counterpart — the ring isomorphism
`A{1/(x+y)}^ ≃ₐ[R] A{1/x}^ × A{1/y}^` — is `FormalSchemes.TateAwaySplit` and is independent of
this file.

## Main results

* `AlgebraicGeometry.range_tateCurveOverlapChart_eq`: the two presentations of the overlap have the
  same underlying-space range.
* `AlgebraicGeometry.tateOverlapChartIso`: hence `Spf A{1/(x+y)} ≅ Spf A{1/x} ⨿ Spf A{1/y}`.
* `AlgebraicGeometry.tateOverlapChartIso_hom_fac` and `tateOverlapChartIso_inv_fac`: the
  isomorphism is one *over* `Spf A`, in both directions.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- **The two presentations of the Tate two-chart overlap have the same range.** The single
basic-open chart at `x + y` and the coproduct of the two overlap charts at `x` and at `y` are both
morphisms into `Spf A` whose images are the open `D(x + y) = D(x) ⊔ D(y)`.

This is `range_annulusOverlapCharts_union` (601a) rewritten through
`LocallyRingedSpace.range_coprodDesc_base`, and it is the sole hypothesis of
`tateOverlapChartIso`. -/
theorem range_tateCurveOverlapChart_eq (hq : q ∈ I) (hI : I.FG) :
    Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
        (overlapX R I q + overlapY R I q)).base =
      Set.range (coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q)).base := by
  rw [LocallyRingedSpace.range_coprodDesc_base,
    range_annulusOverlapCharts_union R I q hq hI]

/-- **The Tate two-chart overlap object is affine**: the coproduct `Spf A{1/x} ⨿ Spf A{1/y}` of
the two `𝔾̂m`-overlap charts is isomorphic to the single affine formal spectrum `Spf A{1/(x+y)}`.

Both are open immersions into `Spf A` with the same range
(`range_tateCurveOverlapChart_eq`), so `LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq` produces
the isomorphism, and `tateOverlapChartIso_hom_fac`/`_inv_fac` say it is an isomorphism *over*
`Spf A`. Together with the ring-level splitting `awaySplitAlgEquiv`
(`FormalSchemes.TateAwaySplit`) this is what exhibits `𝔈_q`'s glue datum in the shape
`AffineChartedFibreDatum` requires. -/
def tateOverlapChartIso (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (overlapX R I q + overlapY R I q)) ≅
      (locallyRingedSpaceObj
          (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) ⨿
        locallyRingedSpaceObj
          (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))) :=
  haveI := isOpenImmersion_basicOpenChart (annulusIdealOfDefinition R I q)
    (overlapX R I q + overlapY R I q) (annulusIdealOfDefinition_fg R I q hI)
  haveI := isOpenImmersion_tateCurveOverlapChart R I q hq hI
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _
    (range_tateCurveOverlapChart_eq R I q hq hI)

/-- **The overlap identification is a morphism over `Spf A`**: composing
`tateOverlapChartIso` with the coproduct of the two overlap charts recovers the single basic-open
chart at `x + y`. This is the equation `AffineChartedFibreDatum`'s chart compatibility consumes. -/
@[reassoc (attr := simp)]
theorem tateOverlapChartIso_hom_fac (hq : q ∈ I) (hI : I.FG) :
    (tateOverlapChartIso R I q hq hI).hom ≫
        coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q) =
      basicOpenChart (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) := by
  haveI := isOpenImmersion_basicOpenChart (annulusIdealOfDefinition R I q)
    (overlapX R I q + overlapY R I q) (annulusIdealOfDefinition_fg R I q hI)
  haveI := isOpenImmersion_tateCurveOverlapChart R I q hq hI
  exact LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _
    (range_tateCurveOverlapChart_eq R I q hq hI)

/-- The reverse factorisation of `tateOverlapChartIso_hom_fac`: composing the inverse with the
single basic-open chart at `x + y` recovers the coproduct of the two overlap charts. Shipped
alongside the forward law because the glue-datum assembly rewrites in both directions. -/
@[reassoc (attr := simp)]
theorem tateOverlapChartIso_inv_fac (hq : q ∈ I) (hI : I.FG) :
    (tateOverlapChartIso R I q hq hI).inv ≫
        basicOpenChart (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) =
      coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q) := by
  haveI := isOpenImmersion_basicOpenChart (annulusIdealOfDefinition R I q)
    (overlapX R I q + overlapY R I q) (annulusIdealOfDefinition_fg R I q hI)
  haveI := isOpenImmersion_tateCurveOverlapChart R I q hq hI
  exact LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_inv_fac _ _
    (range_tateCurveOverlapChart_eq R I q hq hI)

end AlgebraicGeometry
