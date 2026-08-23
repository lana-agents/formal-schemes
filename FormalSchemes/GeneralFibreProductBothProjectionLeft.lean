import FormalSchemes.GeneralFibreProductBothExposeXY
import FormalSchemes.GeneralFibreProductBothAlgebraDataObject
import FormalSchemes.GeneralFibreProductProjectionLeft
import FormalSchemes.TateSelfProductProjectionLeft
import FormalSchemes.CompletedTensorAwayInterchangeBothPullback
import FormalSchemes.CompletedTensorAwayInterchangeMixedPullback
import FormalSchemes.GlueMorphisms

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The first projection of the fully general two-sided fibre product `X ×_{Spf R} Y`

`FormalSchemes.GeneralFibreProductBothObject` assembles, from a `BothChartedFibreDatum`, the general
two-sided fibre product `X ×_{Spf R} Y` of two affine-charted glued formal schemes `X` (charts
`Spf(A i)`, `i : JX`) and `Y` (charts `Spf(B j)`, `j : JY`) over the affine adic base `Spf R`, glued
from the double completed-tensor charts `Spf(A_{p.1} ⊗̂_R B_{p.2})` (`p : JX × JY`).
`FormalSchemes.GeneralFibreProductBothExposeXY` exposes the glued factor `X` itself as
`BothChartedFibreDatumXY.xGlued`.

This file builds the **first projection** `pr₁ : X ×_{Spf R} Y ⟶ X` into the *glued* factor `X`,
gluing the affine first projections `Spf(inl) : Spf(A_{p.1} ⊗̂_R B_{p.2}) ⟶ Spf(A_{p.1})` across the
product cover and composing with the glue inclusions `ι` of the exposed `X`, via
`FormalScheme.GlueData.glueMorphisms`.

## The concreteness hypotheses

`BothChartedFibreDatum` carries its fibre-product glue `V`/`f`/`t` as *abstract* structure fields,
so `glueMorphisms`'s overlap obligation `f p p' ≫ k p = t p p' ≫ f p' p ≫ k p'` is unprovable for
an arbitrary datum. We state `pr₁` under three concreteness hypotheses `hV`/`hf`/`ht` pinning `D`'s
carried glue to the concrete 3-way-dispatched `bothAlgData*`
(`FormalSchemes.GeneralFibreProductBothAlgebraDataObject`); they hold by `rfl` for any datum built
by the smart constructor `ofAlgebraData`.

## The 3-shape dispatch

The overlap obligation dispatches by which coordinate of `p, p'` differs:

* second coordinate differs (`p.1 = p'.1`): the first projection is *invariant* under the
  `B`-localization transition (`snd_base`), so both sides land in the same glue chart `ι p.1`;
* first coordinate differs (`p.1 ≠ p'.1`, `p.2 = p'.2`): the *genuine* case, a verbatim port of the
  affine-base first-projection naturality (`fst_base`), assembled from the interchange `inl`-factor
  law, the base-changed transition sliding through `inl`, and the exposed `X`'s own glue relation
  `x_glue_rel`;
* both coordinates differ (`both_base`): the coordinate flip realises the `fst_base` relation after
  forgetting the `B`-localization.

## Main definitions

* `BothChartedFibreDatumXY.pr₁ChartSelf`: the per-chart first projection
  `Spf(A_{p.1} ⊗̂_R B_{p.2}) ⟶ Spf(A_{p.1})`.
* `BothChartedFibreDatumXY.pr₁`: the glued first projection `X ×_{Spf R} Y ⟶ X`.
* `BothChartedFibreDatumXY.ι_pr₁`: it restricts to `pr₁ChartSelf p ≫ ι p.1` along each glue
  inclusion.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

/-- The identity-index transport `eqAlgEquivA` at a reflexive equality is the identity. -/
private theorem eqAlgEquivA_self {R : Type u} [CommRing R] {JX : Type u} {A : JX → Type u}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] {i : JX} (h : i = i) :
    eqAlgEquivA (R := R) (A := A) h = AlgEquiv.refl := rfl

/-- The identity-index transport `eqAlgEquivB` at a reflexive equality is the identity. -/
private theorem eqAlgEquivB_self {R : Type u} [CommRing R] {JY : Type u} {B : JY → Type u}
    [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)] {j : JY} (h : j = j) :
    eqAlgEquivB (R := R) (B := B) h = AlgEquiv.refl := rfl

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable (D : BothChartedFibreDatumXY R I hI)

/-! ### The per-chart first projection -/

/-- **The per-chart first projection** `Spf(A_{p.1} ⊗̂_R B_{p.2}) ⟶ Spf(A_{p.1})`: the raw
`Spf(inl)` map of formal spectra, landing in the `I·A_{p.1}` convention of the exposed `X`. -/
def pr₁ChartSelf (p : D.JX × D.JY) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2)) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (D.A p.1))) :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.A p.1)))
    (CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2))
    (CompletedTensorProduct.inl R I (D.A p.1) (D.B p.2)).toRingHom
    CompletedTensorProduct.inl_isAdicHom.le_comap

/-! ### The exposed `X` glue relation -/

/-- **The exposed `X`'s glue relation on the double overlap.** For distinct `X`-charts `i ≠ i'`,
`X`'s basic-open overlap chart followed by the glue inclusion `ι_i` equals the `X`-side transition
`awayCompletionTransition` followed by the `(i',i)`-overlap chart and `ι_{i'}`. This is the glue
condition of `xLrsGlueData` on the `(i,i')`-overlap, unfolded through `GlueData.ofGlueData'`. -/
theorem x_glue_rel (i i' : D.JX) (h : i ≠ i') :
    letI := D.commRingA
    letI := D.algebraA
    basicOpenChart (I.map (algebraMap R (D.A i))) (D.gX i i') ≫ D.xFormalGlueData.ι i =
      awayCompletionTransition (D.gX i i') (D.gX i' i) (D.τX i i' h) ≫
        basicOpenChart (I.map (algebraMap R (D.A i'))) (D.gX i' i) ≫ D.xFormalGlueData.ι i' := by
  letI := D.commRingA
  letI := D.algebraA
  have hij' : ¬ @Eq D.JX i i' := h
  have hji' : ¬ @Eq D.JX i' i := fun heq => h heq.symm
  have key := D.xLrsGlueData.toGlueData.glue_condition i i'
  simp only [xLrsGlueData, xGlueData', CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji', Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  rw [cancel_epi] at key
  exact key.symm

/-! ### The overlap ideal-convention bridge and its two squares (first-differ shape) -/

/-- **The overlap bridge** `Spf(I·(A_i{1/g})) ⟶ Spf(awayCompletionIdeal (I·A_i) g)`.
`Spf` of the identity ring hom across the two ideals of definition of the away completion
`A_i{1/g}`, which are equal by `FormalSpectrum.map_algebraMap_awayCompletion_eq`. Reconciles the
`I·(A_i{1/g})` convention produced by
`interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl` with the `awayCompletionIdeal` convention
of the exposed `X`'s overlap charts. -/
def xOverlapBridge (i i' : D.JX) :
    letI := D.commRingA
    letI := D.algebraA
    locallyRingedSpaceObj
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i))) (D.gX i i')))) ⟶
      locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R (D.A i))) (D.gX i i')) :=
  letI := D.commRingA
  letI := D.algebraA
  FormalSpectrum.locallyRingedSpaceMap
    (awayCompletionIdeal (I.map (algebraMap R (D.A i))) (D.gX i i'))
    (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i))) (D.gX i i'))))
    (RingHom.id _) (by
      rw [Ideal.comap_id]
      exact (FormalSpectrum.map_algebraMap_awayCompletion_eq I (D.gX i i')).ge)

/-- **The interchange `inl`-factor of chart `i` factors through the overlap bridge and `X`'s
basic-open chart.** -/
theorem spfAwayInl (i i' : D.JX) :
    letI := D.commRingA
    letI := D.algebraA
    FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.A i)))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i))) (D.gX i i'))))
        (awayCompletionHom (I.map (algebraMap R (D.A i))) (D.gX i i'))
        (le_comap_awayCompletionHom_base I (D.gX i i')) =
      D.xOverlapBridge i i' ≫ basicOpenChart (I.map (algebraMap R (D.A i))) (D.gX i i') := by
  letI := D.commRingA
  letI := D.algebraA
  rw [xOverlapBridge, basicOpenChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := awayCompletionHom (I.map (algebraMap R (D.A i))) (D.gX i i')) (ψ := RingHom.id _)
      (hIK := by rw [RingHom.id_comp]; exact le_comap_awayCompletionHom_base I (D.gX i i'))]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ (RingHom.id_comp _).symm

/-- **The transition-side bridge square.** The base-changed `Spf(inl)`-transition followed by the
interchange `inl`-factor of chart `i'` equals the overlap bridge, the `X`-side transition
`awayCompletionTransition`, and `X`'s basic-open chart of `i'`. -/
theorem spfτsymm_awayInl (i i' : D.JX) (h : i ≠ i') :
    letI := D.commRingA
    letI := D.algebraA
    FormalSpectrum.locallyRingedSpaceMap
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i'))) (D.gX i' i))))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i))) (D.gX i i'))))
        (D.τX i i' h).symm.toAlgHom.toRingHom
        (CompletedTensorProduct.algHom_mapIdeal_isAdicHom (D.τX i i' h).symm.toAlgHom).le_comap ≫
      FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.A i')))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i'))) (D.gX i' i))))
        (awayCompletionHom (I.map (algebraMap R (D.A i'))) (D.gX i' i))
        (le_comap_awayCompletionHom_base I (D.gX i' i)) =
      D.xOverlapBridge i i' ≫ awayCompletionTransition (D.gX i i') (D.gX i' i) (D.τX i i' h) ≫
        basicOpenChart (I.map (algebraMap R (D.A i'))) (D.gX i' i) := by
  letI := D.commRingA
  letI := D.algebraA
  rw [xOverlapBridge, awayCompletionTransition, basicOpenChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := awayCompletionHom (I.map (algebraMap R (D.A i'))) (D.gX i' i))
      (ψ := (D.τX i i' h).symm.toAlgHom.toRingHom)
      (hIK := le_comap_comp _ _ (le_comap_awayCompletionHom_base I (D.gX i' i))
        (CompletedTensorProduct.algHom_mapIdeal_isAdicHom (D.τX i i' h).symm.toAlgHom).le_comap),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := awayCompletionHom (I.map (algebraMap R (D.A i'))) (D.gX i' i))
      (ψ := (D.τX i i' h).symm.toRingHom)
      (hIK := le_comap_comp _ _ (FormalSpectrum.le_comap_awayCompletionHom _ _)
        (awayCompletionTransition_le_comap (D.gX i i') (D.gX i' i) (D.τX i i' h))),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := ((D.τX i i' h).symm.toRingHom).comp
        (awayCompletionHom (I.map (algebraMap R (D.A i'))) (D.gX i' i)))
      (ψ := RingHom.id _)
      (hIK := by
        rw [RingHom.id_comp, FormalSpectrum.map_algebraMap_awayCompletion_eq]
        exact le_comap_comp _ _ (FormalSpectrum.le_comap_awayCompletionHom _ _)
          (awayCompletionTransition_le_comap (D.gX i i') (D.gX i' i) (D.τX i i' h)))]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  rw [RingHom.id_comp]
  rfl

/-! ### SHAPE fst: the genuine first-differ naturality square -/

/-- **The first-differ base naturality square.** For distinct `X`-charts `i ≠ i'` and a fixed
`Y`-chart `j`, the `(i,i')`-interchange chart (localizing the `A`-factor) followed by `pr₁ChartSelf`
and `ι_i` equals the base-changed transition `t = (mapSpfIso (τX i i') (refl B_j)).hom` followed by
the `(i',i)`-interchange chart, `pr₁ChartSelf` and `ι_{i'}`. Verbatim port of the affine-base
`AffineChartedFibreDatumX.pr₁_naturality` with base `B := B_j`. -/
theorem fst_base (i i' : D.JX) (h : i ≠ i') (j : D.JY) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    interchangeOpenImmersion (B := D.B j) I (D.gX i i') hI ≫
        D.pr₁ChartSelf (i, j) ≫ D.xFormalGlueData.ι i =
      (mapSpfIso hI (D.τX i i' h) (AlgEquiv.refl (R := R) (A₁ := D.B j))).hom ≫
        interchangeOpenImmersion (B := D.B j) I (D.gX i' i) hI ≫
          D.pr₁ChartSelf (i', j) ≫ D.xFormalGlueData.ι i' := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  simp only [pr₁ChartSelf]
  rw [reassoc_of% (interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl
        (A := D.A i) (B := D.B j) I (D.gX i i') hI),
    reassoc_of% (interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl
        (A := D.A i') (B := D.B j) I (D.gX i' i) hI),
    mapSpfIso_hom,
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inlMap hI (D.τX i i' h).symm.toAlgHom
      (AlgEquiv.refl (R := R) (A₁ := D.B j)).symm.toAlgHom),
    reassoc_of% (D.spfAwayInl i i'),
    D.x_glue_rel i i' h,
    reassoc_of% (D.spfτsymm_awayInl i i' h)]

/-- **The `A`-base glue relation.** Extracts from the interchange bridge squares and `x_glue_rel`
the first-projection glue relation purely at the level of the `A`-base charts `Spf(I·A_i)`: the
away-completion structural map into `ι_i` equals the base-changed transition `Spf(τX⁻¹)` followed by
the away-completion structural map into `ι_{i'}`. Common core of the first-differ and both-differ
shapes. -/
theorem aBaseGlue (i i' : D.JX) (h : i ≠ i') :
    letI := D.commRingA
    letI := D.algebraA
    FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.A i)))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i))) (D.gX i i'))))
        (awayCompletionHom (I.map (algebraMap R (D.A i))) (D.gX i i'))
        (le_comap_awayCompletionHom_base I (D.gX i i')) ≫ D.xFormalGlueData.ι i =
      FormalSpectrum.locallyRingedSpaceMap
          (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i'))) (D.gX i' i))))
          (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i))) (D.gX i i'))))
          (D.τX i i' h).symm.toAlgHom.toRingHom
          (CompletedTensorProduct.algHom_mapIdeal_isAdicHom (D.τX i i' h).symm.toAlgHom).le_comap ≫
        FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.A i')))
          (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i'))) (D.gX i' i))))
          (awayCompletionHom (I.map (algebraMap R (D.A i'))) (D.gX i' i))
          (le_comap_awayCompletionHom_base I (D.gX i' i)) ≫ D.xFormalGlueData.ι i' := by
  letI := D.commRingA
  letI := D.algebraA
  rw [reassoc_of% (D.spfAwayInl i i'), D.x_glue_rel i i' h,
    ← reassoc_of% (D.spfτsymm_awayInl i i' h)]

/-! ### SHAPE snd: the invariant second-differ base square -/

/-- **The second-differ base square.** For a fixed `X`-chart `i` and distinct `Y`-charts `j ≠ j'`,
the `B`-localization `rightInterchangeOpenImmersion` is *forgotten* by the first projection
`Spf(inl)` (the `A`-factor is untouched), so both sides land in the same `A`-base chart. Port of
`rightInterchange_pr₁_naturality`. -/
theorem snd_base (i : D.JX) (j j' : D.JY) (h : j ≠ j') :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    rightInterchangeOpenImmersion (A := D.A i) I (D.gY j j') hI ≫ D.pr₁ChartSelf (i, j) =
      (mapSpfIso hI (AlgEquiv.refl (R := R) (A₁ := D.A i)) (D.τY j j' h)).hom ≫
        rightInterchangeOpenImmersion (A := D.A i) I (D.gY j' j) hI ≫ D.pr₁ChartSelf (i, j') := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  simp only [pr₁ChartSelf]
  rw [rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inl (A := D.A i) I (D.gY j j') hI,
    rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inl (A := D.A i) I (D.gY j' j) hI,
    mapSpfIso_hom,
    CompletedTensorProduct.mapSpf_comp_inlMap hI
      (AlgEquiv.refl (R := R) (A₁ := D.A i)).symm.toAlgHom (D.τY j j' h).symm.toAlgHom]
  have hf : (((AlgEquiv.refl (R := R) (A₁ := D.A i)).symm.toAlgHom :
        D.A i →ₐ[R] D.A i)).toRingHom = RingHom.id (D.A i) := by
    ext a; simp
  rw [FormalSpectrum.locallyRingedSpaceMap_congr (φ₂ := RingHom.id (D.A i))
      (h₂ := (Ideal.comap_id (I.map (algebraMap R (D.A i)))).ge) (hφ := hf),
    FormalSpectrum.locallyRingedSpaceMap_id, Category.comp_id]

/-! ### SHAPE both: the both-differ base square -/

/-- The `A`-base structural map `IsScalarTower.toAlgHom` coincides with `awayCompletionHom` as a
ring homomorphism, letting the `mapSpf` first-projection naturality (which produces the former) feed
`aBaseGlue` (which is phrased with the latter). -/
theorem toAlgHom_toRingHom_eq (i i' : D.JX) :
    letI := D.commRingA
    letI := D.algebraA
    (IsScalarTower.toAlgHom R (D.A i)
        (awayCompletion (I.map (algebraMap R (D.A i))) (D.gX i i'))).toRingHom =
      awayCompletionHom (I.map (algebraMap R (D.A i))) (D.gX i i') := by
  letI := D.commRingA
  letI := D.algebraA
  rfl

/-- **The both-differ base square.** For distinct `X`-charts `i ≠ i'` and distinct `Y`-charts
`j ≠ j'`, the both-factor interchange chart followed by `pr₁ChartSelf` and `ι_i` equals the
base-changed transition `(mapSpfIso (τX i i') (τY j j')).hom` followed by the flipped both chart,
`pr₁ChartSelf` and `ι_{i'}`. The `B`-localizations are forgotten by the first projection (the two
`inl`-factor naturalities of `mapSpf`), reducing the square to the shared `A`-base relation
`aBaseGlue`, with the `A`/`B`-transition sliding through `inl`. -/
theorem both_base (i i' : D.JX) (h : i ≠ i') (j j' : D.JY) (h' : j ≠ j') :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    bothInterchangeOpenImmersion I (D.gX i i') (D.gY j j') hI ≫
        D.pr₁ChartSelf (i, j) ≫ D.xFormalGlueData.ι i =
      (mapSpfIso hI (D.τX i i' h) (D.τY j j' h')).hom ≫
        bothInterchangeOpenImmersion I (D.gX i' i) (D.gY j' j) hI ≫
          D.pr₁ChartSelf (i', j') ≫ D.xFormalGlueData.ι i' := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  simp only [pr₁ChartSelf]
  rw [bothInterchangeOpenImmersion_eq_mapSpf (A := D.A i) (B := D.B j) I (D.gX i i') (D.gY j j') hI,
    bothInterchangeOpenImmersion_eq_mapSpf (A := D.A i') (B := D.B j') I (D.gX i' i) (D.gY j' j) hI,
    mapSpfIso_hom,
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inlMap hI
      (IsScalarTower.toAlgHom R (D.A i)
        (awayCompletion (I.map (algebraMap R (D.A i))) (D.gX i i')))
      (IsScalarTower.toAlgHom R (D.B j)
        (awayCompletion (I.map (algebraMap R (D.B j))) (D.gY j j')))),
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inlMap hI
      (IsScalarTower.toAlgHom R (D.A i')
        (awayCompletion (I.map (algebraMap R (D.A i'))) (D.gX i' i)))
      (IsScalarTower.toAlgHom R (D.B j')
        (awayCompletion (I.map (algebraMap R (D.B j'))) (D.gY j' j))))]
  rw [FormalSpectrum.locallyRingedSpaceMap_congr
      (φ₂ := awayCompletionHom (I.map (algebraMap R (D.A i))) (D.gX i i'))
      (h₂ := le_comap_awayCompletionHom_base I (D.gX i i')) (hφ := D.toAlgHom_toRingHom_eq i i'),
    FormalSpectrum.locallyRingedSpaceMap_congr
      (φ₂ := awayCompletionHom (I.map (algebraMap R (D.A i'))) (D.gX i' i))
      (h₂ := le_comap_awayCompletionHom_base I (D.gX i' i)) (hφ := D.toAlgHom_toRingHom_eq i' i),
    D.aBaseGlue i i' h,
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inlMap hI (D.τX i i' h).symm.toAlgHom
      (D.τY j j' h').symm.toAlgHom)]

/-! ### The reduced overlap obligation, dispatched by shape -/

/-- **The reduced overlap obligation of the first projection**, on the concrete `bothAlgData*` glue.
For distinct product-index charts `(i, j) ≠ (i', j')`, the concrete overlap immersion followed by
the per-chart first projection into its glue chart equals the concrete transition then the flipped
overlap immersion and its first projection — the datum `glueMorphisms` consumes once the abstract
carried glue has been pinned to `bothAlgData*` by the concreteness hypotheses. Dispatched by which
coordinate differs (`snd_base`/`fst_base`/`both_base`). -/
theorem bothAlgData_pr₁_naturality (i i' : D.JX) (j j' : D.JY) (h : (i, j) ≠ (i', j')) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    bothAlgDataF hI D.gX D.gY (i, j) (i', j') h ≫
        D.pr₁ChartSelf (i, j) ≫ D.xFormalGlueData.ι i =
      bothAlgDataT hI D.gX D.gY D.τX D.τY (i, j) (i', j') h ≫
        bothAlgDataF hI D.gX D.gY (i', j') (i, j) h.symm ≫
          D.pr₁ChartSelf (i', j') ≫ D.xFormalGlueData.ι i' := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  by_cases hii : i = i'
  · -- second coordinate differs
    subst hii
    have hb : j ≠ j' := fun e => h (by rw [e])
    have hc1 : ((i, j) : D.JX × D.JY).1 = ((i, j') : D.JX × D.JY).1 := rfl
    have hc2 : ((i, j') : D.JX × D.JY).1 = ((i, j) : D.JX × D.JY).1 := rfl
    unfold bothAlgDataF bothAlgDataT
    rw [dif_pos hc1, dif_pos hc1, dif_pos hc2]
    simp only [eqAlgEquivA_self, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [reassoc_of% (D.snd_base i j j' hb)]
  · by_cases hjj : j = j'
    · -- first coordinate differs
      subst hjj
      have hc1 : ¬ ((i, j) : D.JX × D.JY).1 = ((i', j) : D.JX × D.JY).1 := hii
      have hc1' : ¬ ((i', j) : D.JX × D.JY).1 = ((i, j) : D.JX × D.JY).1 := fun e => hii e.symm
      have hc2 : ((i, j) : D.JX × D.JY).2 = ((i', j) : D.JX × D.JY).2 := rfl
      have hc2' : ((i', j) : D.JX × D.JY).2 = ((i, j) : D.JX × D.JY).2 := rfl
      unfold bothAlgDataF bothAlgDataT
      rw [dif_neg hc1, dif_pos hc2, dif_neg hc1, dif_pos hc2, dif_neg hc1', dif_pos hc2']
      simp only [eqAlgEquivB_self, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      rw [D.fst_base i i' hii j]
    · -- both coordinates differ
      have hc1 : ¬ ((i, j) : D.JX × D.JY).1 = ((i', j') : D.JX × D.JY).1 := hii
      have hc1' : ¬ ((i', j') : D.JX × D.JY).1 = ((i, j) : D.JX × D.JY).1 := fun e => hii e.symm
      have hc2 : ¬ ((i, j) : D.JX × D.JY).2 = ((i', j') : D.JX × D.JY).2 := hjj
      have hc2' : ¬ ((i', j') : D.JX × D.JY).2 = ((i, j) : D.JX × D.JY).2 := fun e => hjj e.symm
      unfold bothAlgDataF bothAlgDataT
      rw [dif_neg hc1, dif_neg hc2, dif_neg hc1, dif_neg hc2, dif_neg hc1', dif_neg hc2']
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [D.both_base i i' hii j j' hjj]

/-! ### The glued first projection -/

/-- **The first projection of the fully general two-sided fibre product** `pr₁ : X ×_{Spf R} Y ⟶ X`
into the glued factor `X`, glued from the per-chart first projections `pr₁ChartSelf p` composed with
the glue inclusions of the exposed `X`, via `FormalScheme.GlueData.glueMorphisms`. The three
concreteness hypotheses `hV`/`hf`/`ht` pin the carried abstract glue of `D` to the concrete
`bothAlgData*` (holding by `rfl` for any `ofAlgebraData`-built datum); off the diagonal the overlap
obligation reduces to `bothAlgData_pr₁_naturality`, on the diagonal it collapses through
`GlueData.t_id`. -/
def pr₁
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm) :
    D.toBothChartedFibreDatum.generalFibreProduct.toLocallyRingedSpace ⟶
      D.xGlued.toLocallyRingedSpace :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  letI := D.topologyA
  letI := D.isAdicA
  D.formalGlueData.glueMorphisms (fun p => D.pr₁ChartSelf p ≫ D.xFormalGlueData.ι p.1) (by
    intro p p'
    by_cases hpp : p = p'
    · subst hpp
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · obtain ⟨i, j⟩ := p
      obtain ⟨i', j'⟩ := p'
      have hpp' : ((i, j) : D.JX × D.JY) ≠ (i', j') := hpp
      have hp'p : ((i', j') : D.JX × D.JY) ≠ (i, j) := fun heq => hpp heq.symm
      simp only [BothChartedFibreDatum.formalGlueData, BothChartedFibreDatum.lrsGlueData,
        BothChartedFibreDatum.glueData', CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hpp', dif_neg hp'p, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [hf (i, j) (i', j') hpp', ht (i, j) (i', j') hpp', hf (i', j') (i, j) hpp'.symm]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      congr 1
      exact D.bothAlgData_pr₁_naturality i i' j j' hpp')

/-- **The first projection restricts to `pr₁ChartSelf p ≫ ι p.1` along each glue inclusion.** -/
@[reassoc (attr := simp)]
theorem ι_pr₁
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (p : D.JX × D.JY) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    letI := D.topologyA
    letI := D.isAdicA
    D.formalGlueData.ι p ≫ D.pr₁ hV hf ht = D.pr₁ChartSelf p ≫ D.xFormalGlueData.ι p.1 :=
  D.formalGlueData.ι_glueMorphisms _ _ p

end BothChartedFibreDatumXY

end AlgebraicGeometry
