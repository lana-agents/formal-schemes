import FormalSchemes.GeneralFibreProductBothExposeXY
import FormalSchemes.GeneralFibreProductBothAlgebraDataCocycle

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Assembling `X ×_{Spf R} Y` from two exposed single-factor data

`AlgebraicGeometry.BothChartedFibreDatumXY` (`FormalSchemes.GeneralFibreProductBothExposeXY`)
packages the two-sided fibre product together with each factor exposed as a glued formal scheme.
Until now it was only instantiated on the subsingleton witness `punitBothExposeXYDatum`: nothing
built a datum for two genuinely glued factors. This file supplies the general two-factor
constructor `BothChartedFibreDatumXY.ofFactors`, which assembles the datum from two single-factor
`AlgebraicGeometry.AffineChartedFibreDatumX` inputs (`FormalSchemes.GeneralFibreProductExposeX`).

## The product-overlap glue: `bothAlgData*` vs. the single factors

The hard product-overlap glue laws (`t_inv`, `t_fac`, the triple `cocycle`) are the reusable
`bothAlgData*` lemmas over arbitrary `gX`/`gY`, exactly as consumed by the smart constructor
`BothChartedFibreDatum.ofAlgebraData`. Those lemmas are keyed on the **double-overlap** algebra
transitions `σX`/`σY` together with their σ/τ compatibilities `hστX`/`hστY` and algebra cocycles
`hσcX`/`hσcY`. A single-factor `AffineChartedFibreDatumX` carries only its **own** basic-open
triple-overlap cocycle (`xt'`/`xt_fac`/`xcocycle`) and the double transitions `τ`; it does **not**
record the `σ` data. So `ofFactors` takes the per-factor `σX`/`hστX`/`hσcX` (resp. `σY`/`hστY`/
`hσcY`) as additional inputs — the same data `ofAlgebraData` needs — and copies each factor's
exposed fields (`topology`/`isAdic`/`xt'`/`xt_fac`/`xcocycle`) verbatim into the `X`- resp.
`Y`-side of the two-sided datum.

Because the product-overlap fields are *definitionally* `bothAlgData…`, the fibre-product
hypotheses `hV`/`hf`/`ht` (`FormalSchemes.GeneralFibreProductLiftCharts`) become trivial: `hV` is
`rfl` and `hf`/`ht` collapse the `eqToHom rfl = 𝟙`. And because the exposed `X`-side (resp.
`Y`-side) fields are copied verbatim from `DX` (resp. `DY`), the glued factor and its structural
map agree definitionally with `DX`'s (resp. `DY`'s):
`ofFactors_xGlued`/`ofFactors_yGlued`/`ofFactors_xStructMap`/
`ofFactors_yStructMap` are all `rfl`. These bridges are what the general diagonal (issue 235b/c)
consumes: feeding the same factor twice makes `yGlued` defeq `xGlued`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable {BX BY : Type u} [CommRing BX] [Algebra R BX] [CommRing BY] [Algebra R BY]
variable (DX : AffineChartedFibreDatumX R I hI BX) (DY : AffineChartedFibreDatumX R I hI BY)
variable
  (σX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (DX.A i'))) (DX.g i' i'' * DX.g i' i)))
  (σY : letI := DY.commRing; letI := DY.algebra;
    ∀ (j j' j'' : DY.J), j ≠ j' → j ≠ j'' → j' ≠ j'' →
    (awayCompletion (I.map (algebraMap R (DY.A j))) (DY.g j j' * DY.g j j'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (DY.A j'))) (DY.g j' j'' * DY.g j' j)))
  (hστX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (DX.g i' i'') (DX.g i' i) hI) =
      (furtherLocFst I (DX.g i i') (DX.g i i'') hI).comp (DX.τ i i' h1).symm.toAlgHom)
  (hστY : letI := DY.commRing; letI := DY.algebra;
    ∀ (j j' j'' : DY.J) (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j''),
    (σY j j' j'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (DY.g j' j'') (DY.g j' j) hI) =
      (furtherLocFst I (DY.g j j') (DY.g j j'') hI).comp (DY.τ j j' h1).symm.toAlgHom)
  (hσcX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
      (σX i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'')))
  (hσcY : letI := DY.commRing; letI := DY.algebra;
    ∀ (j j' j'' : DY.J) (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j''),
    (σY j j' j'' h1 h2 h3).trans ((σY j' j'' j h3 h1.symm h2.symm).trans
      (σY j'' j j' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (DY.A j))) (DY.g j j' * DY.g j j'')))

/-- **The two-factor constructor for `BothChartedFibreDatumXY`.** From two exposed single-factor
data `DX`, `DY` (an `AffineChartedFibreDatumX` each) together with the double-overlap algebra
transitions `σX`/`σY`, their σ/τ compatibilities `hστX`/`hστY` and algebra cocycles `hσcX`/`hσcY`,
assemble the two-sided fibre-product datum `X ×_{Spf R} Y`.

The base (`BothChartedFibreDatum`) fields are exactly `BothChartedFibreDatum.ofAlgebraData` on the
combined data (`A := DX.A`, `B := DY.A`, `gX := DX.g`, `gY := DY.g`, `τX := DX.τ`, `τY := DY.τ`),
so the product-overlap glue is the proven `bothAlgData…` lemmas. The exposed-factor fields are
copied verbatim: the `X`-side from `DX` and the `Y`-side from `DY`. -/
def ofFactors : BothChartedFibreDatumXY R I hI :=
  letI := DX.commRing
  letI := DX.algebra
  letI := DY.commRing
  letI := DY.algebra
  letI := DX.topology
  letI := DX.isAdic
  letI := DY.topology
  letI := DY.isAdic
  { toBothChartedFibreDatum := BothChartedFibreDatum.ofAlgebraData
      (A := DX.A) (B := DY.A) (gX := DX.g) (gY := DY.g)
      (τX := DX.τ) (τX_symm := DX.τ_symm) (τY := DY.τ) (τY_symm := DY.τ_symm)
      (σX := σX) (σY := σY) (hσcX := hσcX) (hσcY := hσcY) (hI := hI)
      (hστX := hστX) (hστY := hστY)
    topologyA := DX.topology
    isAdicA := DX.isAdic
    xt' := DX.xt'
    xt_fac := DX.xt_fac
    xcocycle := DX.xcocycle
    topologyB := DY.topology
    isAdicB := DY.isAdic
    yt' := DY.xt'
    yt_fac := DY.xt_fac
    ycocycle := DY.xcocycle }

/-- The overlap objects of `ofFactors` are the `bothAlgData` overlap objects — the `hV` input to
`fibreLift`. -/
theorem ofFactors_hV :
    letI := (ofFactors DX DY σX σY hστX hστY hσcX hσcY).commRingA
    letI := (ofFactors DX DY σX σY hστX hστY hσcX hσcY).algebraA
    letI := (ofFactors DX DY σX σY hστX hστY hσcX hσcY).commRingB
    letI := (ofFactors DX DY σX σY hστX hστY hσcX hσcY).algebraB
    ∀ (p p' : (ofFactors DX DY σX σY hστX hστY hσcX hσcY).JX ×
        (ofFactors DX DY σX σY hστX hστY hσcX hσcY).JY) (h : p ≠ p'),
      (ofFactors DX DY σX σY hστX hστY hσcX hσcY).V p p' h =
        bothAlgDataV hI (ofFactors DX DY σX σY hστX hστY hσcX hσcY).gX
          (ofFactors DX DY σX σY hστX hστY hσcX hσcY).gY p p' h :=
  fun _ _ _ => rfl

/-- The overlap immersions of `ofFactors` are the `bothAlgData` immersions — the `hf` input to
`fibreLift`. -/
theorem ofFactors_hf :
    letI := (ofFactors DX DY σX σY hστX hστY hσcX hσcY).commRingA
    letI := (ofFactors DX DY σX σY hστX hστY hσcX hσcY).algebraA
    letI := (ofFactors DX DY σX σY hστX hστY hσcX hσcY).commRingB
    letI := (ofFactors DX DY σX σY hστX hστY hσcX hσcY).algebraB
    ∀ (p p' : (ofFactors DX DY σX σY hστX hστY hσcX hσcY).JX ×
        (ofFactors DX DY σX σY hστX hστY hσcX hσcY).JY) (h : p ≠ p'),
      (ofFactors DX DY σX σY hστX hστY hσcX hσcY).f p p' h =
        eqToHom (ofFactors_hV DX DY σX σY hστX hστY hσcX hσcY p p' h) ≫
          bothAlgDataF hI (ofFactors DX DY σX σY hστX hστY hσcX hσcY).gX
            (ofFactors DX DY σX σY hστX hστY hσcX hσcY).gY p p' h :=
  fun _ _ _ => rfl

/-- The overlap transitions of `ofFactors` are the `bothAlgData` transitions — the `ht` input to
`fibreLift`. -/
theorem ofFactors_ht :
    letI := (ofFactors DX DY σX σY hστX hστY hσcX hσcY).commRingA
    letI := (ofFactors DX DY σX σY hστX hστY hσcX hσcY).algebraA
    letI := (ofFactors DX DY σX σY hστX hστY hσcX hσcY).commRingB
    letI := (ofFactors DX DY σX σY hστX hστY hσcX hσcY).algebraB
    ∀ (p p' : (ofFactors DX DY σX σY hστX hστY hσcX hσcY).JX ×
        (ofFactors DX DY σX σY hστX hστY hσcX hσcY).JY) (h : p ≠ p'),
      (ofFactors DX DY σX σY hστX hστY hσcX hσcY).t p p' h =
        eqToHom (ofFactors_hV DX DY σX σY hστX hστY hσcX hσcY p p' h) ≫
          bothAlgDataT hI (ofFactors DX DY σX σY hστX hστY hσcX hσcY).gX
            (ofFactors DX DY σX σY hστX hστY hσcX hσcY).gY
            (ofFactors DX DY σX σY hστX hστY hσcX hσcY).τX
            (ofFactors DX DY σX σY hστX hστY hσcX hσcY).τY p p' h ≫
          eqToHom (ofFactors_hV DX DY σX σY hστX hστY hσcX hσcY p' p h.symm).symm :=
  fun _ _ _ => rfl

/-- **The exposed glued factor `X` of `ofFactors` is `DX`'s glued scheme.** -/
@[simp]
theorem ofFactors_xGlued :
    (ofFactors DX DY σX σY hστX hστY hσcX hσcY).xGlued = DX.xGlued :=
  rfl

/-- **The exposed glued factor `Y` of `ofFactors` is `DY`'s glued scheme.** -/
@[simp]
theorem ofFactors_yGlued :
    (ofFactors DX DY σX σY hστX hστY hσcX hσcY).yGlued = DY.xGlued :=
  rfl

/-- **The `X`-structural morphism of `ofFactors` is `DX`'s.** -/
@[simp]
theorem ofFactors_xStructMap :
    (ofFactors DX DY σX σY hστX hστY hσcX hσcY).xStructMap = DX.xStructMap :=
  rfl

/-- **The `Y`-structural morphism of `ofFactors` is `DY`'s.** -/
@[simp]
theorem ofFactors_yStructMap :
    (ofFactors DX DY σX σY hστX hστY hσcX hσcY).yStructMap = DY.xStructMap :=
  rfl

end BothChartedFibreDatumXY

end AlgebraicGeometry
