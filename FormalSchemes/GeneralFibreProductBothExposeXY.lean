import FormalSchemes.GeneralFibreProductBothObject
import FormalSchemes.GeneralFibreProductExposeXStructMap

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Exposing the glued factors `X` and `Y` inside the two-sided fibre-product datum

`AlgebraicGeometry.BothChartedFibreDatum` (`FormalSchemes.GeneralFibreProductBothObject`) packages
the two-sided general fibre product `X ×_{Spf R} Y` — where both factors are affine-charted glued
formal schemes — through the chart **algebra data** of each factor (`A`/`gX`/`τX` for `X`,
`B`/`gY`/`τY` for `Y`) together with the *carried* geometric glue of the product itself. It never
builds the glued factor schemes `X` or `Y`.

This file exposes both. It extends `BothChartedFibreDatum` to `BothChartedFibreDatumXY` with each
factor's **own** basic-open glue cocycle, and builds each factor's glue pipeline
`glueData' → lrsGlueData → formalGlueData → glued` (mirroring the one-sided
`AlgebraicGeometry.AffineChartedFibreDatumX` of `FormalSchemes.GeneralFibreProductExposeX`, applied
once to the `A`/`gX`/`τX` data and symmetrically once to the `B`/`gY`/`τY` data), cleanly in the
`I·A_i = I.map (algebraMap R (A i))` / `I·B_j = I.map (algebraMap R (B j))` convention (via
`CompletedTensorAwayInterchange.idealOfDef_base_eq`, so overlaps live over
`FormalSpectrum.basicOpenChart` with no ideal bridges). It also builds each factor's structural
morphism to the base, `xStructMap : X ⟶ Spf R` and `yStructMap : Y ⟶ Spf R` (mirroring
`FormalSchemes.GeneralFibreProductExposeXStructMap`).

Together with the product object `BothChartedFibreDatum.generalFibreProduct` these are the inputs
the projections `pr₁ : X ×_{Spf R} Y ⟶ X`, `pr₂ : X ×_{Spf R} Y ⟶ Y` and the cone identity
`pr₁ ≫ xStructMap = pr₂ ≫ yStructMap` of the general fibre product consume (issues 387/388/389).

## Main definitions

* `AlgebraicGeometry.BothChartedFibreDatumXY`: extends `BothChartedFibreDatum` with each factor's
  own geometric triple-overlap cocycle over the basic-open charts, plus the per-chart topology and
  adic-ring data.
* `BothChartedFibreDatumXY.xGlued` / `yGlued`: the glued factor schemes `X` and `Y`.
* `BothChartedFibreDatumXY.xStructMap` / `yStructMap`: their structural morphisms to `Spf R`, with
  the restriction laws `ι_xStructMap` / `ι_yStructMap`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

/-! ### The two-sided expose-both input datum -/

set_option linter.unusedVariables false in
/-- **A two-sided affine-charted fibre-product datum with both factors exposed as glueable
objects.** This extends `BothChartedFibreDatum` (which packages `X` and `Y` only through their
algebra data and the carried product cocycle) with each factor's **own** geometric triple-overlap
cocycle over the basic-open charts, together with the per-chart topology and adic-ring data needed
to view each `Spf (A i)` and `Spf (B j)` as a formal scheme.

The `X`-side fields `xt'`, `xt_fac`, `xcocycle` live over
`FormalSpectrum.basicOpenChart (I·A_i) (gX i i')` with transition the `X`-side
`awayCompletionTransition`; the `Y`-side fields `yt'`, `yt_fac`, `ycocycle` are the symmetric copy
over `FormalSpectrum.basicOpenChart (I·B_j) (gY j j')`. -/
structure BothChartedFibreDatumXY (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
    extends BothChartedFibreDatum R I hI where
  /-- The `I·A_i`-adic topology on each `X`-chart algebra `A i`. -/
  [topologyA : ∀ i : JX, TopologicalSpace (A i)]
  /-- Each `X`-chart `A i` is a complete adic ring with ideal of definition `I·A_i`. -/
  [isAdicA : ∀ i : JX, IsAdicRing (I.map (algebraMap R (A i)))]
  /-- The geometric triple-overlap transition of `X`'s own glue. -/
  xt' : ∀ (i j k : JX) (_hij : i ≠ j) (_hik : i ≠ k) (_hjk : j ≠ k),
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (gX i j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (gX i k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (gX j k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (gX j i) (hI.map _)
    (pullback (basicOpenChart (I.map (algebraMap R (A i))) (gX i j))
        (basicOpenChart (I.map (algebraMap R (A i))) (gX i k)) ⟶
      pullback (basicOpenChart (I.map (algebraMap R (A j))) (gX j k))
        (basicOpenChart (I.map (algebraMap R (A j))) (gX j i)))
  /-- Compatibility of `xt'` with the `X`-side transition (the `t_fac` law). -/
  xt_fac : ∀ (i j k : JX) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (gX i j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (gX i k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (gX j k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (gX j i) (hI.map _)
    xt' i j k hij hik hjk ≫
        pullback.snd (basicOpenChart (I.map (algebraMap R (A j))) (gX j k))
          (basicOpenChart (I.map (algebraMap R (A j))) (gX j i)) =
      pullback.fst (basicOpenChart (I.map (algebraMap R (A i))) (gX i j))
          (basicOpenChart (I.map (algebraMap R (A i))) (gX i k)) ≫
        awayCompletionTransition (gX i j) (gX j i) (τX i j hij)
  /-- The triple cocycle of `X`'s own glue. -/
  xcocycle : ∀ (i j k : JX) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (gX i j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (gX i k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (gX j k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (gX j i) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A k))) (gX k i) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A k))) (gX k j) (hI.map _)
    xt' i j k hij hik hjk ≫ xt' j k i hjk hij.symm hik.symm ≫
      xt' k i j hik.symm hjk.symm hij = 𝟙 _
  /-- The `I·B_j`-adic topology on each `Y`-chart algebra `B j`. -/
  [topologyB : ∀ j : JY, TopologicalSpace (B j)]
  /-- Each `Y`-chart `B j` is a complete adic ring with ideal of definition `I·B_j`. -/
  [isAdicB : ∀ j : JY, IsAdicRing (I.map (algebraMap R (B j)))]
  /-- The geometric triple-overlap transition of `Y`'s own glue. -/
  yt' : ∀ (j j' j'' : JY) (_hjj' : j ≠ j') (_hjj'' : j ≠ j'') (_hj'j'' : j' ≠ j''),
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j))) (gY j j') (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j))) (gY j j'') (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j'))) (gY j' j'') (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j'))) (gY j' j) (hI.map _)
    (pullback (basicOpenChart (I.map (algebraMap R (B j))) (gY j j'))
        (basicOpenChart (I.map (algebraMap R (B j))) (gY j j'')) ⟶
      pullback (basicOpenChart (I.map (algebraMap R (B j'))) (gY j' j''))
        (basicOpenChart (I.map (algebraMap R (B j'))) (gY j' j)))
  /-- Compatibility of `yt'` with the `Y`-side transition (the `t_fac` law). -/
  yt_fac : ∀ (j j' j'' : JY) (hjj' : j ≠ j') (hjj'' : j ≠ j'') (hj'j'' : j' ≠ j''),
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j))) (gY j j') (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j))) (gY j j'') (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j'))) (gY j' j'') (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j'))) (gY j' j) (hI.map _)
    yt' j j' j'' hjj' hjj'' hj'j'' ≫
        pullback.snd (basicOpenChart (I.map (algebraMap R (B j'))) (gY j' j''))
          (basicOpenChart (I.map (algebraMap R (B j'))) (gY j' j)) =
      pullback.fst (basicOpenChart (I.map (algebraMap R (B j))) (gY j j'))
          (basicOpenChart (I.map (algebraMap R (B j))) (gY j j'')) ≫
        awayCompletionTransition (gY j j') (gY j' j) (τY j j' hjj')
  /-- The triple cocycle of `Y`'s own glue. -/
  ycocycle : ∀ (j j' j'' : JY) (hjj' : j ≠ j') (hjj'' : j ≠ j'') (hj'j'' : j' ≠ j''),
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j))) (gY j j') (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j))) (gY j j'') (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j'))) (gY j' j'') (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j'))) (gY j' j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j''))) (gY j'' j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j''))) (gY j'' j') (hI.map _)
    yt' j j' j'' hjj' hjj'' hj'j'' ≫ yt' j' j'' j hj'j'' hjj'.symm hjj''.symm ≫
      yt' j'' j j' hjj''.symm hj'j''.symm hjj' = 𝟙 _

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable (D : BothChartedFibreDatumXY R I hI)

/-! ### The glued factor `X` -/

/-- **The `X`-factor glue datum** as a `CategoryTheory.GlueData'` on `D.JX`: the `i`-th chart is
`Spf(A i)`, the overlap immersion is `basicOpenChart (I·A_i) (gX i j)`, the transition is the
`X`-side `awayCompletionTransition`, and the cocycle fields are the carried `X`-geometric datum. -/
def xGlueData' : CategoryTheory.GlueData' LocallyRingedSpace.{u} :=
  letI := D.commRingA
  letI := D.algebraA
  { J := D.JX
    U := fun i => locallyRingedSpaceObj (I.map (algebraMap R (D.A i)))
    V := fun i j _ =>
      locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R (D.A i))) (D.gX i j))
    f := fun i j _ => basicOpenChart (I.map (algebraMap R (D.A i))) (D.gX i j)
    f_mono := fun i j _ => by
      haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.A i))) (D.gX i j) (hI.map _)
      infer_instance
    f_hasPullback := fun i j k _ _ => by
      haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.A i))) (D.gX i j) (hI.map _)
      haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.A i))) (D.gX i k) (hI.map _)
      infer_instance
    t := fun i j h => awayCompletionTransition (D.gX i j) (D.gX j i) (D.τX i j h)
    t' := D.xt'
    t_fac := D.xt_fac
    t_inv := fun i j h => by
      rw [D.τX_symm i j h]
      exact awayCompletionTransition_comp (D.gX i j) (D.gX j i) (D.τX i j h)
    cocycle := D.xcocycle }

/-- **The `X`-factor glue datum as a `LocallyRingedSpace.GlueData`**, via `GlueData.ofGlueData'` and
the open-immersion field `f_open`. -/
def xLrsGlueData : LocallyRingedSpace.GlueData.{u} :=
  letI := D.commRingA
  letI := D.algebraA
  { CategoryTheory.GlueData.ofGlueData' D.xGlueData' with
    f_open := by
      rintro i j
      simp only [xGlueData', CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.A i))) (D.gX i j) (hI.map _)
        exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
          (eqToHom _ ≫ basicOpenChart (I.map (algebraMap R (D.A i))) (D.gX i j))) }

/-- **The `X`-factor glue datum as a `FormalScheme.GlueData`**: each chart is the affine formal
scheme `Spf(A i)`. -/
def xFormalGlueData : FormalScheme.GlueData.{u} :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.topologyA
  letI := D.isAdicA
  { toLocallyRingedSpaceGlueData := D.xLrsGlueData
    isFormalScheme := fun i =>
      ⟨FormalScheme.Spf (I.map (algebraMap R (D.A i))), ⟨Iso.refl _⟩⟩ }

/-- **The glued factor scheme `X`.** -/
def xGlued : FormalScheme.{u} :=
  D.xFormalGlueData.gluedFormalScheme

/-- **The per-chart structural morphism** `Spf(A i) ⟶ Spf R`, the map of formal spectra induced by
the `R`-algebra structure map `algebraMap R (A i)`, over `I·A_i = I.map (algebraMap R (A i))`. -/
def xStructMapChart (i : D.JX) :
    letI := D.commRingA
    letI := D.algebraA
    locallyRingedSpaceObj (I.map (algebraMap R (D.A i))) ⟶ locallyRingedSpaceObj I :=
  letI := D.commRingA
  letI := D.algebraA
  locallyRingedSpaceMap I (I.map (algebraMap R (D.A i))) (algebraMap R (D.A i)) Ideal.le_comap_map

/-- **The double-overlap compatibility square of the `X`-structural morphism.** -/
theorem xStructMap_naturality (i j : D.JX) (h : i ≠ j) :
    letI := D.commRingA
    letI := D.algebraA
    basicOpenChart (I.map (algebraMap R (D.A i))) (D.gX i j) ≫ D.xStructMapChart i =
      awayCompletionTransition (D.gX i j) (D.gX j i) (D.τX i j h) ≫
        basicOpenChart (I.map (algebraMap R (D.A j))) (D.gX j i) ≫ D.xStructMapChart j := by
  letI := D.commRingA
  letI := D.algebraA
  rw [xStructMapChart, xStructMapChart, basicOpenChart, basicOpenChart, awayCompletionTransition,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp (algebraMap R (D.A i))
        (awayCompletionHom (I.map (algebraMap R (D.A i))) (D.gX i j))
        Ideal.le_comap_map (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp (algebraMap R (D.A j))
        (awayCompletionHom (I.map (algebraMap R (D.A j))) (D.gX j i))
        Ideal.le_comap_map (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp
        ((awayCompletionHom (I.map (algebraMap R (D.A j))) (D.gX j i)).comp (algebraMap R (D.A j)))
        (D.τX i j h).symm.toRingHom
        (le_comap_comp (algebraMap R (D.A j))
          (awayCompletionHom (I.map (algebraMap R (D.A j))) (D.gX j i))
          Ideal.le_comap_map (le_comap_awayCompletionHom _ _))
        (awayCompletionTransition_le_comap (D.gX i j) (D.gX j i) (D.τX i j h)))]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  rw [awayCompletionHom_comp_algebraMap, awayCompletionHom_comp_algebraMap]
  exact RingHom.ext fun r => ((D.τX i j h).symm.commutes r).symm

/-- **The glued structural morphism of the factor `X`** `X ⟶ Spf R`, assembled from the per-chart
structural morphisms via `glueMorphisms`. -/
def xStructMap :
    D.xGlued.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  D.xFormalGlueData.glueMorphisms (fun i => D.xStructMapChart i) (by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · have hij' : ¬ @Eq D.JX i j := hij
      have hji' : ¬ @Eq D.JX j i := fun heq => hij heq.symm
      simp only [xFormalGlueData, xLrsGlueData, xGlueData', CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji', Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [D.xStructMap_naturality i j hij'])

/-- **The `X`-structural morphism restricts to `xStructMapChart i` along each glue inclusion.** -/
@[reassoc (attr := simp)]
theorem ι_xStructMap (i : D.JX) :
    D.xFormalGlueData.ι i ≫ D.xStructMap = D.xStructMapChart i :=
  D.xFormalGlueData.ι_glueMorphisms _ _ i

/-! ### The glued factor `Y` -/

/-- **The `Y`-factor glue datum** as a `CategoryTheory.GlueData'` on `D.JY`: the `j`-th chart is
`Spf(B j)`, the overlap immersion is `basicOpenChart (I·B_j) (gY j j')`, the transition is the
`Y`-side `awayCompletionTransition`, and the cocycle fields are the carried `Y`-geometric datum. -/
def yGlueData' : CategoryTheory.GlueData' LocallyRingedSpace.{u} :=
  letI := D.commRingB
  letI := D.algebraB
  { J := D.JY
    U := fun j => locallyRingedSpaceObj (I.map (algebraMap R (D.B j)))
    V := fun j j' _ =>
      locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R (D.B j))) (D.gY j j'))
    f := fun j j' _ => basicOpenChart (I.map (algebraMap R (D.B j))) (D.gY j j')
    f_mono := fun j j' _ => by
      haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.B j))) (D.gY j j') (hI.map _)
      infer_instance
    f_hasPullback := fun j j' j'' _ _ => by
      haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.B j))) (D.gY j j') (hI.map _)
      haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.B j))) (D.gY j j'') (hI.map _)
      infer_instance
    t := fun j j' h => awayCompletionTransition (D.gY j j') (D.gY j' j) (D.τY j j' h)
    t' := D.yt'
    t_fac := D.yt_fac
    t_inv := fun j j' h => by
      rw [D.τY_symm j j' h]
      exact awayCompletionTransition_comp (D.gY j j') (D.gY j' j) (D.τY j j' h)
    cocycle := D.ycocycle }

/-- **The `Y`-factor glue datum as a `LocallyRingedSpace.GlueData`**, via `GlueData.ofGlueData'` and
the open-immersion field `f_open`. -/
def yLrsGlueData : LocallyRingedSpace.GlueData.{u} :=
  letI := D.commRingB
  letI := D.algebraB
  { CategoryTheory.GlueData.ofGlueData' D.yGlueData' with
    f_open := by
      rintro j j'
      simp only [yGlueData', CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.B j))) (D.gY j j')
          (hI.map _)
        exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
          (eqToHom _ ≫ basicOpenChart (I.map (algebraMap R (D.B j))) (D.gY j j'))) }

/-- **The `Y`-factor glue datum as a `FormalScheme.GlueData`**: each chart is the affine formal
scheme `Spf(B j)`. -/
def yFormalGlueData : FormalScheme.GlueData.{u} :=
  letI := D.commRingB
  letI := D.algebraB
  letI := D.topologyB
  letI := D.isAdicB
  { toLocallyRingedSpaceGlueData := D.yLrsGlueData
    isFormalScheme := fun j =>
      ⟨FormalScheme.Spf (I.map (algebraMap R (D.B j))), ⟨Iso.refl _⟩⟩ }

/-- **The glued factor scheme `Y`.** -/
def yGlued : FormalScheme.{u} :=
  D.yFormalGlueData.gluedFormalScheme

/-- **The per-chart structural morphism** `Spf(B j) ⟶ Spf R`, the map of formal spectra induced by
the `R`-algebra structure map `algebraMap R (B j)`, over `I·B_j = I.map (algebraMap R (B j))`. -/
def yStructMapChart (j : D.JY) :
    letI := D.commRingB
    letI := D.algebraB
    locallyRingedSpaceObj (I.map (algebraMap R (D.B j))) ⟶ locallyRingedSpaceObj I :=
  letI := D.commRingB
  letI := D.algebraB
  locallyRingedSpaceMap I (I.map (algebraMap R (D.B j))) (algebraMap R (D.B j)) Ideal.le_comap_map

/-- **The double-overlap compatibility square of the `Y`-structural morphism.** -/
theorem yStructMap_naturality (j j' : D.JY) (h : j ≠ j') :
    letI := D.commRingB
    letI := D.algebraB
    basicOpenChart (I.map (algebraMap R (D.B j))) (D.gY j j') ≫ D.yStructMapChart j =
      awayCompletionTransition (D.gY j j') (D.gY j' j) (D.τY j j' h) ≫
        basicOpenChart (I.map (algebraMap R (D.B j'))) (D.gY j' j) ≫ D.yStructMapChart j' := by
  letI := D.commRingB
  letI := D.algebraB
  rw [yStructMapChart, yStructMapChart, basicOpenChart, basicOpenChart, awayCompletionTransition,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp (algebraMap R (D.B j))
        (awayCompletionHom (I.map (algebraMap R (D.B j))) (D.gY j j'))
        Ideal.le_comap_map (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp (algebraMap R (D.B j'))
        (awayCompletionHom (I.map (algebraMap R (D.B j'))) (D.gY j' j))
        Ideal.le_comap_map (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp
        ((awayCompletionHom (I.map (algebraMap R (D.B j'))) (D.gY j' j)).comp
          (algebraMap R (D.B j')))
        (D.τY j j' h).symm.toRingHom
        (le_comap_comp (algebraMap R (D.B j'))
          (awayCompletionHom (I.map (algebraMap R (D.B j'))) (D.gY j' j))
          Ideal.le_comap_map (le_comap_awayCompletionHom _ _))
        (awayCompletionTransition_le_comap (D.gY j j') (D.gY j' j) (D.τY j j' h)))]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  rw [awayCompletionHom_comp_algebraMap, awayCompletionHom_comp_algebraMap]
  exact RingHom.ext fun r => ((D.τY j j' h).symm.commutes r).symm

/-- **The glued structural morphism of the factor `Y`** `Y ⟶ Spf R`, assembled from the per-chart
structural morphisms via `glueMorphisms`. -/
def yStructMap :
    D.yGlued.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  D.yFormalGlueData.glueMorphisms (fun j => D.yStructMapChart j) (by
    intro j j'
    by_cases hjj' : j = j'
    · subst hjj'
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · have hjj'' : ¬ @Eq D.JY j j' := hjj'
      have hj'j : ¬ @Eq D.JY j' j := fun heq => hjj' heq.symm
      simp only [yFormalGlueData, yLrsGlueData, yGlueData', CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hjj'', dif_neg hj'j, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [D.yStructMap_naturality j j' hjj''])

/-- **The `Y`-structural morphism restricts to `yStructMapChart j` along each glue inclusion.** -/
@[reassoc (attr := simp)]
theorem ι_yStructMap (j : D.JY) :
    D.yFormalGlueData.ι j ≫ D.yStructMap = D.yStructMapChart j :=
  D.yFormalGlueData.ι_glueMorphisms _ _ j

end BothChartedFibreDatumXY

/-! ### Validation: a subsingleton-index witness

We extend the subsingleton-index witness `punitBothDatum` (charts `Spf R` on the singleton index
`PUnit`) to a `BothChartedFibreDatumXY`: every off-diagonal cocycle field is vacuous, and the
per-chart adic data reduces to the base's own `IsAdicRing I` via `Ideal.map_id`. This witnesses that
`BothChartedFibreDatumXY` is inhabitable and its factor-glue pipeline (`xGlued`, `yGlued`,
`xStructMap`, `yStructMap`) typechecks end-to-end and yields real objects. -/

/-- **A subsingleton-index witness `BothChartedFibreDatumXY`.** On `JX = JY = PUnit` no two charts
are distinct, so every geometric cocycle field is vacuous; the chart algebras are `R` itself, so the
per-chart adic data is the base's `IsAdicRing I` transported along `I.map (algebraMap R R) = I`.
This is the `punitBothDatum` (`GeneralFibreProductBothObject`) data augmented with the
exposed-factor fields, witnessing that `BothChartedFibreDatumXY` is inhabitable. -/
def punitBothExposeXYDatum (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
    [TopologicalSpace R] [IsAdicRing I] : BothChartedFibreDatumXY R I hI :=
  have hmap : I.map (algebraMap R R) = I := Ideal.map_id I
  { JX := PUnit
    JY := PUnit
    A := fun _ => R
    B := fun _ => R
    gX := fun _ _ => 1
    gY := fun _ _ => 1
    τX := fun i i' h => (h (Subsingleton.elim i i')).elim
    τX_symm := fun i i' h => (h (Subsingleton.elim i i')).elim
    τY := fun j j' h => (h (Subsingleton.elim j j')).elim
    τY_symm := fun j j' h => (h (Subsingleton.elim j j')).elim
    V := fun p p' h => (h (Subsingleton.elim p p')).elim
    f := fun p p' h => (h (Subsingleton.elim p p')).elim
    hf := fun p p' h => (h (Subsingleton.elim p p')).elim
    t := fun p p' h => (h (Subsingleton.elim p p')).elim
    t_inv := fun p p' h => (h (Subsingleton.elim p p')).elim
    t' := fun p p' _ hpp' _ _ => (hpp' (Subsingleton.elim p p')).elim
    t_fac := fun p p' _ hpp' _ _ => (hpp' (Subsingleton.elim p p')).elim
    cocycle := fun p p' _ hpp' _ _ => (hpp' (Subsingleton.elim p p')).elim
    topologyA := fun _ => inferInstance
    isAdicA := fun _ => by rw [hmap]; infer_instance
    xt' := fun i j _ hij _ _ => (hij (Subsingleton.elim i j)).elim
    xt_fac := fun i j _ hij _ _ => (hij (Subsingleton.elim i j)).elim
    xcocycle := fun i j _ hij _ _ => (hij (Subsingleton.elim i j)).elim
    topologyB := fun _ => inferInstance
    isAdicB := fun _ => by rw [hmap]; infer_instance
    yt' := fun j j' _ hjj' _ _ => (hjj' (Subsingleton.elim j j')).elim
    yt_fac := fun j j' _ hjj' _ _ => (hjj' (Subsingleton.elim j j')).elim
    ycocycle := fun j j' _ hjj' _ _ => (hjj' (Subsingleton.elim j j')).elim }

end AlgebraicGeometry
