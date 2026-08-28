import FormalSchemes.BasicOpenImmersionLRS
import FormalSchemes.PullbackRangeLRS

set_option linter.style.header false

/-!
# The overlap of two basic-open charts of `Spf A` (EGA I, §10.8, §10.15)

For an adic ring `(A, I)` with `I` finitely generated and elements `f g : A`, the two basic-open
charts `Spf A{1/f} ⟶ Spf A` and `Spf A{1/g} ⟶ Spf A` (`FormalSpectrum.basicOpenChart`, issue 163)
are open immersions of locally ringed spaces with ranges the basic opens `D(f)` and `D(g)`
(`isOpenImmersion_basicOpenChart`, `range_basicOpenChart_base`). Their **overlap** is the basic
open `D(f) ∩ D(g) = D(f·g)`, again a basic-open chart `Spf A{1/(f·g)}`. This file records that
overlap datum:

* `FormalSpectrum.range_basicOpenChart_base_inter`: the set-theoretic core, `D(f) ⊓ D(g) = D(f·g)`
  read as an equality of ranges;
* `FormalSpectrum.basicOpenChartOverlapIso`: the resulting identification of the overlap object
  `Spf A{1/(f·g)}` with the fibre product `pullback (basicOpenChart I f) (basicOpenChart I g)`,
  via the merged open-immersion pullback identification
  `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq`;
* `basicOpenChartOverlapIso_hom_fst_comp` / `_hom_snd_comp` / `_inv_comp`: the chart-inclusion
  compatibilities — the identification followed by either projection and the corresponding chart
  is the basic-open chart at the product.

## Why this shape

This is the `Spf A` analogue of the merged `FormalSchemes/CompletionBasicOpenOverlap.lean`, which
records the same datum for `basicOpenImmersion` on `formalCompletion R I`. The chart version is the
one the general glued-`X` machinery uses: `AffineChartedFibreDatumX.xGlueData'`
(`FormalSchemes/GeneralFibreProductExposeX.lean`) takes `f i j := basicOpenChart (I·A_i) (g i j)`,
so its geometric triple-overlap field `xt'` is a morphism
`pullback (basicOpenChart (I·A_i) (g i j)) (basicOpenChart (I·A_i) (g i k)) ⟶ …`.
Instantiating `basicOpenChartOverlapIso` at `I·A_i`, `g i j`, `g i k` presents that pullback as the
affine chart `Spf (A_i{1/(g_ij · g_ik)})`, which is the first thing any construction of `xt'`
needs — and that is how every non-vacuous `xt'` on this tree is in fact built.
`AffineChartedFibreDatumX.xAlgDataT'`
(`FormalSchemes/GeneralFibreProductExposeXAlgebraData.lean`) is precisely the composite of
`(basicOpenChartOverlapIso (I·A_i) (g i j) (g i k)).inv`, the transported single-overlap map
`awayCompletionTransition σ`, and `(basicOpenChartOverlapIso (I·A_j) (g j k) (g j i)).hom`; the
smart constructor `AffineChartedFibreDatumX.ofAlgebraData` feeds it to the datum's `xt'` field.
Two datum values on master have a pairwise distinct triple of indices and so reach it with real
content: `ThreeChartDatum.datumX` and `ThreeChartCoverDatum.datumX`, both on `ULift (Fin 3)` — the
second being a single `Spf A` covered by three basic opens, which is exactly this file's situation.
That `xt'` is genuinely `xAlgDataT'` rather than `False.elim` there is the theorem
`ThreeChartDatum.datumX_xt'_eq`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8, §10.15.
* [The Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f g : R)

/-- **The ranges of two basic-open charts intersect in the range of the chart at the product**:
`im (bOC f) ∩ im (bOC g) = im (bOC (f·g))`. On underlying spaces this is the basic-open identity
`D(f) ⊓ D(g) = D(f·g)` in `FormalSpectrum I`, using the merged range computation
`range_basicOpenChart_base` and the multiplicativity `basicOpen_mul`. -/
theorem range_basicOpenChart_base_inter (hI : I.FG) :
    Set.range (basicOpenChart I f).base ∩ Set.range (basicOpenChart I g).base =
      Set.range (basicOpenChart I (f * g)).base := by
  rw [range_basicOpenChart_base I f hI, range_basicOpenChart_base I g hI,
    range_basicOpenChart_base I (f * g) hI, basicOpen_mul, Opens.coe_inf]
  rfl

/-- **The overlap object of two basic-open charts is their fibre product.** The chart
`Spf A{1/(f·g)}` at the product, whose range in `Spf A` is `D(f) ∩ D(g)`
(`range_basicOpenChart_base_inter`), identifies with the pullback of the two charts at `f` and `g`,
via the merged open-immersion pullback identification.

Note that `basicOpenChart` carries no global `IsOpenImmersion` instance; the three instances (at
`f`, `g` and `f * g`) are supplied by `letI` from `isOpenImmersion_basicOpenChart`, in the
signature as well as the body, following the idiom of `AffineChartedFibreDatumX`'s own fields. -/
def basicOpenChartOverlapIso (hI : I.FG) :
    letI := isOpenImmersion_basicOpenChart I f hI
    letI := isOpenImmersion_basicOpenChart I g hI
    locallyRingedSpaceObj (awayCompletionIdeal I (f * g)) ≅
      pullback (basicOpenChart I f) (basicOpenChart I g) :=
  letI := isOpenImmersion_basicOpenChart I f hI
  letI := isOpenImmersion_basicOpenChart I g hI
  letI := isOpenImmersion_basicOpenChart I (f * g) hI
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
    (basicOpenChart I f) (basicOpenChart I g) (basicOpenChart I (f * g))
    (range_basicOpenChart_base_inter I f g hI).symm

/-- The overlap identification is compatible with the first chart inclusion: mapping the overlap
object to the fibre product, projecting to the first factor, and including into `Spf A` recovers the
basic-open chart at the product. -/
@[reassoc]
theorem basicOpenChartOverlapIso_hom_fst_comp (hI : I.FG) :
    letI := isOpenImmersion_basicOpenChart I f hI
    letI := isOpenImmersion_basicOpenChart I g hI
    (basicOpenChartOverlapIso I f g hI).hom ≫
        pullback.fst (basicOpenChart I f) (basicOpenChart I g) ≫ basicOpenChart I f =
      basicOpenChart I (f * g) :=
  letI := isOpenImmersion_basicOpenChart I f hI
  letI := isOpenImmersion_basicOpenChart I g hI
  letI := isOpenImmersion_basicOpenChart I (f * g) hI
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_fst_comp _ _ _ _

/-- The overlap identification is compatible with the second chart inclusion: mapping the overlap
object to the fibre product, projecting to the second factor, and including into `Spf A` recovers
the basic-open chart at the product. -/
@[reassoc]
theorem basicOpenChartOverlapIso_hom_snd_comp (hI : I.FG) :
    letI := isOpenImmersion_basicOpenChart I f hI
    letI := isOpenImmersion_basicOpenChart I g hI
    (basicOpenChartOverlapIso I f g hI).hom ≫
        pullback.snd (basicOpenChart I f) (basicOpenChart I g) ≫ basicOpenChart I g =
      basicOpenChart I (f * g) :=
  letI := isOpenImmersion_basicOpenChart I f hI
  letI := isOpenImmersion_basicOpenChart I g hI
  letI := isOpenImmersion_basicOpenChart I (f * g) hI
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_snd_comp _ _ _ _

/-- The inverse identification presents the canonical map `X ×_Z Y ⟶ Z` of the two charts as the
basic-open chart at the product: `(overlapIso).inv ≫ bOC (f·g) = pullback.fst ≫ bOC f`. -/
@[reassoc]
theorem basicOpenChartOverlapIso_inv_comp (hI : I.FG) :
    letI := isOpenImmersion_basicOpenChart I f hI
    letI := isOpenImmersion_basicOpenChart I g hI
    (basicOpenChartOverlapIso I f g hI).inv ≫ basicOpenChart I (f * g) =
      pullback.fst (basicOpenChart I f) (basicOpenChart I g) ≫ basicOpenChart I f :=
  letI := isOpenImmersion_basicOpenChart I f hI
  letI := isOpenImmersion_basicOpenChart I g hI
  letI := isOpenImmersion_basicOpenChart I (f * g) hI
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_inv_comp _ _ _ _

end FormalSpectrum

end
