import FormalSchemes.GeneralFibreProductExposeXStructMap
import FormalSchemes.GeneralFibreProductBothObject

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Exposing the glued factors `X` and `Y` inside the two-sided fibre-product datum

`AlgebraicGeometry.BothChartedFibreDatum` (`FormalSchemes.GeneralFibreProductBothObject`) packages
the fully-general fibre product `X ×_{Spf R} Y` of two glued formal schemes over the affine base
`Spf R`, but only through the **algebra data** of the factors (the chart `R`-algebras `A i`/`B j`,
the away elements `gX i i'`/`gY j j'`, and the transitions `τX i i'`/`τY j j'`) together with the
*fibre-product* geometric cocycle triple `t'`/`t_fac`/`cocycle`. It never builds the glued factor
schemes `X` or `Y` themselves.

This file exposes both, mirroring — once per factor — the affine-base pipeline
`AffineChartedFibreDatumX.xGlueData' → xLrsGlueData → xFormalGlueData → xGlued` of
`FormalSchemes.GeneralFibreProductExposeX` and its structural morphism
`AffineChartedFibreDatumX.xStructMap` of `FormalSchemes.GeneralFibreProductExposeXStructMap`. Each
factor is glued in the `I·A_i = I.map (algebraMap R (A i))` convention, so its overlaps live
over `FormalSpectrum.basicOpenChart` with no ideal-convention bridges
(`CompletedTensorAwayInterchange.idealOfDef_base_eq`); the reusable `X`-side transition
`AlgebraicGeometry.awayCompletionTransition` serves both factors.

## Main definitions

* `AlgebraicGeometry.BothChartedFibreDatumXY`: extends `BothChartedFibreDatum` with each factor's
  own geometric triple-overlap cocycle (`xt'`/`xt_fac`/`xcocycle` for `X`, `yt'`/`yt_fac`/`ycocycle`
  for `Y`) over the basic-open charts, plus the per-chart topology and adic data of each factor.
* `BothChartedFibreDatumXY.xGlued` / `yGlued`: the glued factor schemes `X` and `Y`.
* `BothChartedFibreDatumXY.xStructMap` / `yStructMap`: their structural morphisms to `Spf R`.
* `BothChartedFibreDatumXY.ι_xStructMap` / `ι_yStructMap`: the per-chart restriction laws.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* Stacks Tag 01JO.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

/-- Continuity of a composite ring homomorphism: if `φ` carries `I` into `J` and `ψ` carries `J`
into `K` (in the `comap` sense), then `ψ.comp φ` carries `I` into `K`. -/
private theorem le_comap_comp'' {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    {I : Ideal A} {J : Ideal B} {K : Ideal C} (φ : A →+* B) (ψ : B →+* C)
    (hIJ : I ≤ J.comap φ) (hJK : J ≤ K.comap ψ) : I ≤ K.comap (ψ.comp φ) :=
  fun _ hx => hJK (hIJ hx)

/-! ### The two-sided expose datum -/

set_option linter.unusedVariables false in
/-- **A two-sided fibre-product datum whose factors are exposed as glueable objects.** This extends
`BothChartedFibreDatum` with each factor's **own** geometric triple-overlap cocycle over the
basic-open charts, together with the per-chart topology and adic-ring data needed to view each
`Spf (A i)` and `Spf (B j)` as a formal scheme. The fields `xt'`/`xt_fac`/`xcocycle` and
`yt'`/`yt_fac`/`ycocycle` are the direct per-factor analogues of the `AffineChartedFibreDatumX`
fields `xt'`/`xt_fac`/`xcocycle`, living over `FormalSpectrum.basicOpenChart` with the factor's own
`awayCompletionTransition`. -/
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
  yt' : ∀ (i j k : JY) (_hij : i ≠ j) (_hik : i ≠ k) (_hjk : j ≠ k),
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B i))) (gY i j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B i))) (gY i k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j))) (gY j k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j))) (gY j i) (hI.map _)
    (pullback (basicOpenChart (I.map (algebraMap R (B i))) (gY i j))
        (basicOpenChart (I.map (algebraMap R (B i))) (gY i k)) ⟶
      pullback (basicOpenChart (I.map (algebraMap R (B j))) (gY j k))
        (basicOpenChart (I.map (algebraMap R (B j))) (gY j i)))
  /-- Compatibility of `yt'` with the `Y`-side transition (the `t_fac` law). -/
  yt_fac : ∀ (i j k : JY) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B i))) (gY i j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B i))) (gY i k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j))) (gY j k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j))) (gY j i) (hI.map _)
    yt' i j k hij hik hjk ≫
        pullback.snd (basicOpenChart (I.map (algebraMap R (B j))) (gY j k))
          (basicOpenChart (I.map (algebraMap R (B j))) (gY j i)) =
      pullback.fst (basicOpenChart (I.map (algebraMap R (B i))) (gY i j))
          (basicOpenChart (I.map (algebraMap R (B i))) (gY i k)) ≫
        awayCompletionTransition (gY i j) (gY j i) (τY i j hij)
  /-- The triple cocycle of `Y`'s own glue. -/
  ycocycle : ∀ (i j k : JY) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B i))) (gY i j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B i))) (gY i k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j))) (gY j k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B j))) (gY j i) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B k))) (gY k i) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (B k))) (gY k j) (hI.map _)
    yt' i j k hij hik hjk ≫ yt' j k i hjk hij.symm hik.symm ≫
      yt' k i j hik.symm hjk.symm hij = 𝟙 _

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable (D : BothChartedFibreDatumXY R I hI)

/-! ### The glued factor `X` -/

/-- **The `X`-factor glue datum** as a `CategoryTheory.GlueData'` on `D.JX`: the `i`-th chart is
`Spf(A i)`, the overlap immersion is `basicOpenChart (I·A_i) (gX i j)`, the transition is the
`X`-side `awayCompletionTransition`, and the cocycle fields are `D`'s `xt'`/`xt_fac`/`xcocycle`. -/
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

/-- **The `X`-factor glue datum as a `LocallyRingedSpace.GlueData`**, via `GlueData.ofGlueData'`. -/
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

/-- **The `X`-factor glue datum as a `FormalScheme.GlueData`**: each chart is `Spf(A i)`. -/
def xFormalGlueData : FormalScheme.GlueData.{u} :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.topologyA
  letI := D.isAdicA
  { toLocallyRingedSpaceGlueData := D.xLrsGlueData
    isFormalScheme := fun i =>
      ⟨FormalScheme.Spf (I.map (algebraMap R (D.A i))), ⟨Iso.refl _⟩⟩ }

/-- **The glued factor `X`.** -/
def xGlued : FormalScheme.{u} :=
  D.xFormalGlueData.gluedFormalScheme

/-! ### The glued factor `Y` -/

/-- **The `Y`-factor glue datum** as a `CategoryTheory.GlueData'` on `D.JY`, the mirror of
`xGlueData'`. -/
def yGlueData' : CategoryTheory.GlueData' LocallyRingedSpace.{u} :=
  letI := D.commRingB
  letI := D.algebraB
  { J := D.JY
    U := fun j => locallyRingedSpaceObj (I.map (algebraMap R (D.B j)))
    V := fun i j _ =>
      locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R (D.B i))) (D.gY i j))
    f := fun i j _ => basicOpenChart (I.map (algebraMap R (D.B i))) (D.gY i j)
    f_mono := fun i j _ => by
      haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.B i))) (D.gY i j) (hI.map _)
      infer_instance
    f_hasPullback := fun i j k _ _ => by
      haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.B i))) (D.gY i j) (hI.map _)
      haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.B i))) (D.gY i k) (hI.map _)
      infer_instance
    t := fun i j h => awayCompletionTransition (D.gY i j) (D.gY j i) (D.τY i j h)
    t' := D.yt'
    t_fac := D.yt_fac
    t_inv := fun i j h => by
      rw [D.τY_symm i j h]
      exact awayCompletionTransition_comp (D.gY i j) (D.gY j i) (D.τY i j h)
    cocycle := D.ycocycle }

/-- **The `Y`-factor glue datum as a `LocallyRingedSpace.GlueData`.** -/
def yLrsGlueData : LocallyRingedSpace.GlueData.{u} :=
  letI := D.commRingB
  letI := D.algebraB
  { CategoryTheory.GlueData.ofGlueData' D.yGlueData' with
    f_open := by
      rintro i j
      simp only [yGlueData', CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.B i))) (D.gY i j) (hI.map _)
        exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
          (eqToHom _ ≫ basicOpenChart (I.map (algebraMap R (D.B i))) (D.gY i j))) }

/-- **The `Y`-factor glue datum as a `FormalScheme.GlueData`**: each chart is `Spf(B j)`. -/
def yFormalGlueData : FormalScheme.GlueData.{u} :=
  letI := D.commRingB
  letI := D.algebraB
  letI := D.topologyB
  letI := D.isAdicB
  { toLocallyRingedSpaceGlueData := D.yLrsGlueData
    isFormalScheme := fun j =>
      ⟨FormalScheme.Spf (I.map (algebraMap R (D.B j))), ⟨Iso.refl _⟩⟩ }

/-- **The glued factor `Y`.** -/
def yGlued : FormalScheme.{u} :=
  D.yFormalGlueData.gluedFormalScheme

/-! ### The structural morphism of `X` -/

/-- **The per-chart structural morphism** `Spf(A i) ⟶ Spf R`. -/
def xStructMapChart (i : D.JX) :
    letI := D.commRingA
    letI := D.algebraA
    locallyRingedSpaceObj (I.map (algebraMap R (D.A i))) ⟶ locallyRingedSpaceObj I :=
  letI := D.commRingA
  letI := D.algebraA
  locallyRingedSpaceMap I (I.map (algebraMap R (D.A i))) (algebraMap R (D.A i)) Ideal.le_comap_map

/-- **The double-overlap compatibility square of `X`'s structural morphism.** -/
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
      (hIK := le_comap_comp'' (algebraMap R (D.A i))
        (awayCompletionHom (I.map (algebraMap R (D.A i))) (D.gX i j))
        Ideal.le_comap_map (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp'' (algebraMap R (D.A j))
        (awayCompletionHom (I.map (algebraMap R (D.A j))) (D.gX j i))
        Ideal.le_comap_map (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp''
        ((awayCompletionHom (I.map (algebraMap R (D.A j))) (D.gX j i)).comp (algebraMap R (D.A j)))
        (D.τX i j h).symm.toRingHom
        (le_comap_comp'' (algebraMap R (D.A j))
          (awayCompletionHom (I.map (algebraMap R (D.A j))) (D.gX j i))
          Ideal.le_comap_map (le_comap_awayCompletionHom _ _))
        (awayCompletionTransition_le_comap (D.gX i j) (D.gX j i) (D.τX i j h)))]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  rw [awayCompletionHom_comp_algebraMap_base, awayCompletionHom_comp_algebraMap_base]
  exact RingHom.ext fun r => ((D.τX i j h).symm.commutes r).symm

/-- **The glued structural morphism of the exposed factor `X`** `X ⟶ Spf R`. -/
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

/-- **`xStructMap` restricts to `xStructMapChart i` along each glue inclusion.** -/
@[reassoc (attr := simp)]
theorem ι_xStructMap (i : D.JX) :
    D.xFormalGlueData.ι i ≫ D.xStructMap = D.xStructMapChart i :=
  D.xFormalGlueData.ι_glueMorphisms _ _ i

/-! ### The structural morphism of `Y` -/

/-- **The per-chart structural morphism** `Spf(B j) ⟶ Spf R`. -/
def yStructMapChart (j : D.JY) :
    letI := D.commRingB
    letI := D.algebraB
    locallyRingedSpaceObj (I.map (algebraMap R (D.B j))) ⟶ locallyRingedSpaceObj I :=
  letI := D.commRingB
  letI := D.algebraB
  locallyRingedSpaceMap I (I.map (algebraMap R (D.B j))) (algebraMap R (D.B j)) Ideal.le_comap_map

/-- **The double-overlap compatibility square of `Y`'s structural morphism.** -/
theorem yStructMap_naturality (i j : D.JY) (h : i ≠ j) :
    letI := D.commRingB
    letI := D.algebraB
    basicOpenChart (I.map (algebraMap R (D.B i))) (D.gY i j) ≫ D.yStructMapChart i =
      awayCompletionTransition (D.gY i j) (D.gY j i) (D.τY i j h) ≫
        basicOpenChart (I.map (algebraMap R (D.B j))) (D.gY j i) ≫ D.yStructMapChart j := by
  letI := D.commRingB
  letI := D.algebraB
  rw [yStructMapChart, yStructMapChart, basicOpenChart, basicOpenChart, awayCompletionTransition,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp'' (algebraMap R (D.B i))
        (awayCompletionHom (I.map (algebraMap R (D.B i))) (D.gY i j))
        Ideal.le_comap_map (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp'' (algebraMap R (D.B j))
        (awayCompletionHom (I.map (algebraMap R (D.B j))) (D.gY j i))
        Ideal.le_comap_map (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp''
        ((awayCompletionHom (I.map (algebraMap R (D.B j))) (D.gY j i)).comp (algebraMap R (D.B j)))
        (D.τY i j h).symm.toRingHom
        (le_comap_comp'' (algebraMap R (D.B j))
          (awayCompletionHom (I.map (algebraMap R (D.B j))) (D.gY j i))
          Ideal.le_comap_map (le_comap_awayCompletionHom _ _))
        (awayCompletionTransition_le_comap (D.gY i j) (D.gY j i) (D.τY i j h)))]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  rw [awayCompletionHom_comp_algebraMap_base, awayCompletionHom_comp_algebraMap_base]
  exact RingHom.ext fun r => ((D.τY i j h).symm.commutes r).symm

/-- **The glued structural morphism of the exposed factor `Y`** `Y ⟶ Spf R`. -/
def yStructMap :
    D.yGlued.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  D.yFormalGlueData.glueMorphisms (fun j => D.yStructMapChart j) (by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · have hij' : ¬ @Eq D.JY i j := hij
      have hji' : ¬ @Eq D.JY j i := fun heq => hij heq.symm
      simp only [yFormalGlueData, yLrsGlueData, yGlueData', CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji', Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [D.yStructMap_naturality i j hij'])

/-- **`yStructMap` restricts to `yStructMapChart j` along each glue inclusion.** -/
@[reassoc (attr := simp)]
theorem ι_yStructMap (j : D.JY) :
    D.yFormalGlueData.ι j ≫ D.yStructMap = D.yStructMapChart j :=
  D.yFormalGlueData.ι_glueMorphisms _ _ j

end BothChartedFibreDatumXY

end AlgebraicGeometry
