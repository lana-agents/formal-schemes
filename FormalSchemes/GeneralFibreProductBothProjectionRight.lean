import FormalSchemes.GeneralFibreProductBothExposeXY
import FormalSchemes.GeneralFibreProductBothAlgebraDataObject
import FormalSchemes.TateSelfProductProjectionRight
import FormalSchemes.CompletedTensorAwayInterchangePr
import FormalSchemes.CompletedTensorAwayInterchangeBothPullback
import FormalSchemes.CompletedTensorAwayInterchangeMixedPullback
import FormalSchemes.GlueMorphisms

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The second projection of the fully general two-sided fibre product `X ×_{Spf R} Y`

`FormalSchemes.GeneralFibreProductBothObject` assembles, from a `BothChartedFibreDatum`, the general
two-sided fibre product `X ×_{Spf R} Y` of two affine-charted glued formal schemes `X` (charts
`Spf(A i)`, `i : JX`) and `Y` (charts `Spf(B j)`, `j : JY`) over the affine adic base `Spf R`, glued
from the double completed-tensor charts `Spf(A_{p.1} ⊗̂_R B_{p.2})` (`p : JX × JY`).
`FormalSchemes.GeneralFibreProductBothExposeXY` exposes the glued factor `Y` itself as
`BothChartedFibreDatumXY.yGlued`.

This file builds the **second projection** `pr₂ : X ×_{Spf R} Y ⟶ Y` into the *glued* factor `Y`,
gluing the affine second projections `Spf(inr) : Spf(A_{p.1} ⊗̂_R B_{p.2}) ⟶ Spf(B_{p.2})` across
the product cover and composing with the glue inclusions `ι` of the exposed `Y`, via
`FormalScheme.GlueData.glueMorphisms`. It is the factor-swap mirror of
`FormalSchemes.GeneralFibreProductBothProjectionLeft` (the first projection `pr₁`).

## The concreteness hypotheses

`BothChartedFibreDatum` carries its fibre-product glue `V`/`f`/`t` as *abstract* structure fields,
so `glueMorphisms`'s overlap obligation `f p p' ≫ k p = t p p' ≫ f p' p ≫ k p'` is unprovable for
an arbitrary datum. We state `pr₂` under three concreteness hypotheses `hV`/`hf`/`ht` pinning `D`'s
carried glue to the concrete 3-way-dispatched `bothAlgData*`
(`FormalSchemes.GeneralFibreProductBothAlgebraDataObject`); they hold by `rfl` for any datum built
by the smart constructor `ofAlgebraData`. These are the same hypotheses `pr₁` (308b) takes.

## The 3-shape dispatch

The overlap obligation dispatches by which coordinate of `p, p'` differs. Compared with `pr₁`, the
roles of the two genuine/invariant shapes are *swapped* (the second projection forgets the `A`
factor):

* first coordinate differs (`p.1 ≠ p'.1`, `p.2 = p'.2`): the second projection is *invariant* under
  the `A`-localization transition (`fst_base`), so both sides land in the same glue chart `ι p.2`;
* second coordinate differs (`p.1 = p'.1`, `p.2 ≠ p'.2`): the *genuine* case, a verbatim port of the
  affine-base second-projection naturality (`snd_base`), assembled from the interchange `inr`-factor
  law, the base-changed transition sliding through `inr`, and the exposed `Y`'s own glue relation
  `y_glue_rel`;
* both coordinates differ (`both_base`): the coordinate flip realises the `snd_base` relation after
  forgetting the `A`-localization.

## Main definitions

* `BothChartedFibreDatumXY.pr₂ChartSelf`: the per-chart second projection
  `Spf(A_{p.1} ⊗̂_R B_{p.2}) ⟶ Spf(B_{p.2})`.
* `BothChartedFibreDatumXY.pr₂`: the glued second projection `X ×_{Spf R} Y ⟶ Y`.
* `BothChartedFibreDatumXY.ι_pr₂`: it restricts to `pr₂ChartSelf p ≫ ι p.2` along each glue
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

/-- Continuity of a composite ring homomorphism, in `comap` form. -/
private theorem le_comap_comp''' {S T U : Type u} [CommRing S] [CommRing T] [CommRing U]
    {J : Ideal S} {K : Ideal T} {L : Ideal U} (φ : S →+* T) (ψ : T →+* U)
    (hJK : J ≤ K.comap φ) (hKL : K ≤ L.comap ψ) : J ≤ L.comap (ψ.comp φ) :=
  fun _ hx => hKL (hJK hx)

/-- The identity-index transport `eqAlgEquivA` at a reflexive equality is the identity. -/
private theorem eqAlgEquivA_self' {R : Type u} [CommRing R] {JX : Type u} {A : JX → Type u}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] {i : JX} (h : i = i) :
    eqAlgEquivA (R := R) (A := A) h = AlgEquiv.refl := rfl

/-- The identity-index transport `eqAlgEquivB` at a reflexive equality is the identity. -/
private theorem eqAlgEquivB_self' {R : Type u} [CommRing R] {JY : Type u} {B : JY → Type u}
    [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)] {j : JY} (h : j = j) :
    eqAlgEquivB (R := R) (B := B) h = AlgEquiv.refl := rfl

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable (D : BothChartedFibreDatumXY R I hI)

/-! ### The per-chart second projection -/

/-- **The per-chart second projection** `Spf(A_{p.1} ⊗̂_R B_{p.2}) ⟶ Spf(B_{p.2})`: the raw
`Spf(inr)` map of formal spectra, landing in the `I·B_{p.2}` convention of the exposed `Y`. -/
def pr₂ChartSelf (p : D.JX × D.JY) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2)) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (D.B p.2))) :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.B p.2)))
    (CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2))
    (CompletedTensorProduct.inr R I (D.A p.1) (D.B p.2)).toRingHom
    CompletedTensorProduct.inr_isAdicHom.le_comap

/-! ### The exposed `Y` glue relation -/

/-- **The exposed `Y`'s glue relation on the double overlap.** For distinct `Y`-charts `j ≠ j'`,
`Y`'s basic-open overlap chart followed by the glue inclusion `ι_j` equals the `Y`-side transition
`awayCompletionTransition` followed by the `(j',j)`-overlap chart and `ι_{j'}`. This is the glue
condition of `yLrsGlueData` on the `(j,j')`-overlap, unfolded through `GlueData.ofGlueData'`. -/
theorem y_glue_rel (j j' : D.JY) (h : j ≠ j') :
    letI := D.commRingB
    letI := D.algebraB
    basicOpenChart (I.map (algebraMap R (D.B j))) (D.gY j j') ≫ D.yFormalGlueData.ι j =
      awayCompletionTransition (D.gY j j') (D.gY j' j) (D.τY j j' h) ≫
        basicOpenChart (I.map (algebraMap R (D.B j'))) (D.gY j' j) ≫ D.yFormalGlueData.ι j' := by
  letI := D.commRingB
  letI := D.algebraB
  have hij' : ¬ @Eq D.JY j j' := h
  have hji' : ¬ @Eq D.JY j' j := fun heq => h heq.symm
  have key := D.yLrsGlueData.toGlueData.glue_condition j j'
  simp only [yLrsGlueData, yGlueData', CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji', Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  rw [cancel_epi] at key
  exact key.symm

/-! ### The overlap ideal-convention bridge and its two squares (second-differ shape) -/

/-- **The overlap bridge** `Spf(I·(B_j{1/g})) ⟶ Spf(awayCompletionIdeal (I·B_j) g)`.
`Spf` of the identity ring hom across the two (equal, by `idealOfDef_base_eq`) ideals of definition
of the away completion `B_j{1/g}`. Reconciles the `I·(B_j{1/g})` convention produced by
`rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inr` with the `awayCompletionIdeal`
convention of the exposed `Y`'s overlap charts. -/
def yOverlapBridge (j j' : D.JY) :
    letI := D.commRingB
    letI := D.algebraB
    locallyRingedSpaceObj
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.B j))) (D.gY j j')))) ⟶
      locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R (D.B j))) (D.gY j j')) :=
  letI := D.commRingB
  letI := D.algebraB
  FormalSpectrum.locallyRingedSpaceMap
    (awayCompletionIdeal (I.map (algebraMap R (D.B j))) (D.gY j j'))
    (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.B j))) (D.gY j j'))))
    (RingHom.id _) (by
      rw [Ideal.comap_id]
      exact (CompletedTensorAwayInterchange.idealOfDef_base_eq I (D.gY j j')).ge)

/-- **The interchange `inr`-factor of chart `j` factors through the overlap bridge and `Y`'s
basic-open chart.** -/
theorem spfAwayInr (j j' : D.JY) :
    letI := D.commRingB
    letI := D.algebraB
    FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.B j)))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.B j))) (D.gY j j'))))
        (awayCompletionHom (I.map (algebraMap R (D.B j))) (D.gY j j'))
        (le_comap_awayCompletionHom_base I (D.gY j j')) =
      D.yOverlapBridge j j' ≫ basicOpenChart (I.map (algebraMap R (D.B j))) (D.gY j j') := by
  letI := D.commRingB
  letI := D.algebraB
  rw [yOverlapBridge, basicOpenChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := awayCompletionHom (I.map (algebraMap R (D.B j))) (D.gY j j')) (ψ := RingHom.id _)
      (hIK := by rw [RingHom.id_comp]; exact le_comap_awayCompletionHom_base I (D.gY j j'))]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ (RingHom.id_comp _).symm

/-- **The transition-side bridge square.** The base-changed `Spf(inr)`-transition followed by the
interchange `inr`-factor of chart `j'` equals the overlap bridge, the `Y`-side transition
`awayCompletionTransition`, and `Y`'s basic-open chart of `j'`. -/
theorem spfτsymm_awayInr (j j' : D.JY) (h : j ≠ j') :
    letI := D.commRingB
    letI := D.algebraB
    FormalSpectrum.locallyRingedSpaceMap
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.B j'))) (D.gY j' j))))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.B j))) (D.gY j j'))))
        (D.τY j j' h).symm.toAlgHom.toRingHom
        (CompletedTensorProduct.algHom_mapIdeal_isAdicHom (D.τY j j' h).symm.toAlgHom).le_comap ≫
      FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.B j')))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.B j'))) (D.gY j' j))))
        (awayCompletionHom (I.map (algebraMap R (D.B j'))) (D.gY j' j))
        (le_comap_awayCompletionHom_base I (D.gY j' j)) =
      D.yOverlapBridge j j' ≫ awayCompletionTransition (D.gY j j') (D.gY j' j) (D.τY j j' h) ≫
        basicOpenChart (I.map (algebraMap R (D.B j'))) (D.gY j' j) := by
  letI := D.commRingB
  letI := D.algebraB
  rw [yOverlapBridge, awayCompletionTransition, basicOpenChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := awayCompletionHom (I.map (algebraMap R (D.B j'))) (D.gY j' j))
      (ψ := (D.τY j j' h).symm.toAlgHom.toRingHom)
      (hIK := le_comap_comp''' _ _ (le_comap_awayCompletionHom_base I (D.gY j' j))
        (CompletedTensorProduct.algHom_mapIdeal_isAdicHom (D.τY j j' h).symm.toAlgHom).le_comap),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := awayCompletionHom (I.map (algebraMap R (D.B j'))) (D.gY j' j))
      (ψ := (D.τY j j' h).symm.toRingHom)
      (hIK := le_comap_comp''' _ _ (FormalSpectrum.le_comap_awayCompletionHom _ _)
        (awayCompletionTransition_le_comap (D.gY j j') (D.gY j' j) (D.τY j j' h))),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := ((D.τY j j' h).symm.toRingHom).comp
        (awayCompletionHom (I.map (algebraMap R (D.B j'))) (D.gY j' j)))
      (ψ := RingHom.id _)
      (hIK := by
        rw [RingHom.id_comp, CompletedTensorAwayInterchange.idealOfDef_base_eq]
        exact le_comap_comp''' _ _ (FormalSpectrum.le_comap_awayCompletionHom _ _)
          (awayCompletionTransition_le_comap (D.gY j j') (D.gY j' j) (D.τY j j' h)))]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  rw [RingHom.id_comp]
  rfl

/-! ### SHAPE snd: the genuine second-differ naturality square -/

/-- **The second-differ base naturality square.** For a fixed `X`-chart `i` and distinct `Y`-charts
`j ≠ j'`, the `(j,j')`-interchange chart (localizing the `B`-factor) followed by `pr₂ChartSelf`
and `ι_j` equals the base-changed transition `t = (mapSpfIso (refl A_i) (τY j j')).hom` followed by
the `(j',j)`-interchange chart, `pr₂ChartSelf` and `ι_{j'}`. Factor-swap mirror of the first
projection's `fst_base` (the genuine glued-target square) with base `A := A_i`. -/
theorem snd_base (i : D.JX) (j j' : D.JY) (h : j ≠ j') :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    rightInterchangeOpenImmersion (A := D.A i) I (D.gY j j') hI ≫
        D.pr₂ChartSelf (i, j) ≫ D.yFormalGlueData.ι j =
      (mapSpfIso hI (AlgEquiv.refl (R := R) (A₁ := D.A i)) (D.τY j j' h)).hom ≫
        rightInterchangeOpenImmersion (A := D.A i) I (D.gY j' j) hI ≫
          D.pr₂ChartSelf (i, j') ≫ D.yFormalGlueData.ι j' := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  simp only [pr₂ChartSelf]
  rw [reassoc_of% (rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inr
        (A := D.A i) I (D.gY j j') hI),
    reassoc_of% (rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inr
        (A := D.A i) I (D.gY j' j) hI),
    mapSpfIso_hom,
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inrMap hI
      (AlgEquiv.refl (R := R) (A₁ := D.A i)).symm.toAlgHom (D.τY j j' h).symm.toAlgHom),
    reassoc_of% (D.spfAwayInr j j'),
    D.y_glue_rel j j' h,
    reassoc_of% (D.spfτsymm_awayInr j j' h)]

/-- **The `B`-base glue relation.** Extracts from the interchange bridge squares and `y_glue_rel`
the second-projection glue relation purely at the level of the `B`-base charts `Spf(I·B_j)`: the
away-completion structural map into `ι_j` equals the base-changed transition `Spf(τY⁻¹)` followed by
the away-completion structural map into `ι_{j'}`. Common core of the second-differ and both-differ
shapes. -/
theorem bBaseGlue (j j' : D.JY) (h : j ≠ j') :
    letI := D.commRingB
    letI := D.algebraB
    FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.B j)))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.B j))) (D.gY j j'))))
        (awayCompletionHom (I.map (algebraMap R (D.B j))) (D.gY j j'))
        (le_comap_awayCompletionHom_base I (D.gY j j')) ≫ D.yFormalGlueData.ι j =
      FormalSpectrum.locallyRingedSpaceMap
          (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.B j'))) (D.gY j' j))))
          (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.B j))) (D.gY j j'))))
          (D.τY j j' h).symm.toAlgHom.toRingHom
          (CompletedTensorProduct.algHom_mapIdeal_isAdicHom (D.τY j j' h).symm.toAlgHom).le_comap ≫
        FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.B j')))
          (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.B j'))) (D.gY j' j))))
          (awayCompletionHom (I.map (algebraMap R (D.B j'))) (D.gY j' j))
          (le_comap_awayCompletionHom_base I (D.gY j' j)) ≫ D.yFormalGlueData.ι j' := by
  letI := D.commRingB
  letI := D.algebraB
  rw [reassoc_of% (D.spfAwayInr j j'), D.y_glue_rel j j' h,
    ← reassoc_of% (D.spfτsymm_awayInr j j' h)]

/-! ### SHAPE fst: the invariant first-differ base square -/

/-- **The first-differ base square.** For distinct `X`-charts `i ≠ i'` and a fixed `Y`-chart `j`,
the `A`-localization `interchangeOpenImmersion` is *forgotten* by the second projection `Spf(inr)`
(the `B`-factor is untouched), so both sides land in the same `B`-base chart. Factor-swap mirror of
the first projection's invariant `snd_base`. -/
theorem fst_base (i i' : D.JX) (h : i ≠ i') (j : D.JY) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    interchangeOpenImmersion (B := D.B j) I (D.gX i i') hI ≫ D.pr₂ChartSelf (i, j) =
      (mapSpfIso hI (D.τX i i' h) (AlgEquiv.refl (R := R) (A₁ := D.B j))).hom ≫
        interchangeOpenImmersion (B := D.B j) I (D.gX i' i) hI ≫ D.pr₂ChartSelf (i', j) := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  simp only [pr₂ChartSelf]
  rw [interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr I (D.gX i i') hI,
    interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr I (D.gX i' i) hI,
    mapSpfIso_hom,
    CompletedTensorProduct.mapSpf_comp_inrMap hI (D.τX i i' h).symm.toAlgHom
      (AlgEquiv.refl (R := R) (A₁ := D.B j)).symm.toAlgHom]
  have hg : (((AlgEquiv.refl (R := R) (A₁ := D.B j)).symm.toAlgHom :
        D.B j →ₐ[R] D.B j)).toRingHom = RingHom.id (D.B j) := by
    ext b; simp
  rw [FormalSpectrum.locallyRingedSpaceMap_congr (φ₂ := RingHom.id (D.B j))
      (h₂ := (Ideal.comap_id (I.map (algebraMap R (D.B j)))).ge) (hφ := hg),
    FormalSpectrum.locallyRingedSpaceMap_id, Category.comp_id]

/-! ### SHAPE both: the both-differ base square -/

/-- The `B`-base structural map `IsScalarTower.toAlgHom` coincides with `awayCompletionHom` as a
ring homomorphism, letting the `mapSpf` second-projection naturality (which produces the former)
feed `bBaseGlue` (which is phrased with the latter). -/
theorem toAlgHom_toRingHom_eqB (j j' : D.JY) :
    letI := D.commRingB
    letI := D.algebraB
    (IsScalarTower.toAlgHom R (D.B j)
        (awayCompletion (I.map (algebraMap R (D.B j))) (D.gY j j'))).toRingHom =
      awayCompletionHom (I.map (algebraMap R (D.B j))) (D.gY j j') := by
  letI := D.commRingB
  letI := D.algebraB
  rfl

/-- **The both-differ base square.** For distinct `X`-charts `i ≠ i'` and distinct `Y`-charts
`j ≠ j'`, the both-factor interchange chart followed by `pr₂ChartSelf` and `ι_j` equals the
base-changed transition `(mapSpfIso (τX i i') (τY j j')).hom` followed by the flipped both chart,
`pr₂ChartSelf` and `ι_{j'}`. The `A`-localizations are forgotten by the second projection (the two
`inr`-factor naturalities of `mapSpf`), reducing the square to the shared `B`-base relation
`bBaseGlue`, with the `A`/`B`-transition sliding through `inr`. -/
theorem both_base (i i' : D.JX) (h : i ≠ i') (j j' : D.JY) (h' : j ≠ j') :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    bothInterchangeOpenImmersion I (D.gX i i') (D.gY j j') hI ≫
        D.pr₂ChartSelf (i, j) ≫ D.yFormalGlueData.ι j =
      (mapSpfIso hI (D.τX i i' h) (D.τY j j' h')).hom ≫
        bothInterchangeOpenImmersion I (D.gX i' i) (D.gY j' j) hI ≫
          D.pr₂ChartSelf (i', j') ≫ D.yFormalGlueData.ι j' := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  simp only [pr₂ChartSelf]
  rw [bothInterchangeOpenImmersion_eq_mapSpf (A := D.A i) (B := D.B j) I (D.gX i i') (D.gY j j') hI,
    bothInterchangeOpenImmersion_eq_mapSpf (A := D.A i') (B := D.B j') I (D.gX i' i) (D.gY j' j) hI,
    mapSpfIso_hom,
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inrMap hI
      (IsScalarTower.toAlgHom R (D.A i)
        (awayCompletion (I.map (algebraMap R (D.A i))) (D.gX i i')))
      (IsScalarTower.toAlgHom R (D.B j)
        (awayCompletion (I.map (algebraMap R (D.B j))) (D.gY j j')))),
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inrMap hI
      (IsScalarTower.toAlgHom R (D.A i')
        (awayCompletion (I.map (algebraMap R (D.A i'))) (D.gX i' i)))
      (IsScalarTower.toAlgHom R (D.B j')
        (awayCompletion (I.map (algebraMap R (D.B j'))) (D.gY j' j))))]
  rw [FormalSpectrum.locallyRingedSpaceMap_congr
      (φ₂ := awayCompletionHom (I.map (algebraMap R (D.B j))) (D.gY j j'))
      (h₂ := le_comap_awayCompletionHom_base I (D.gY j j')) (hφ := D.toAlgHom_toRingHom_eqB j j'),
    FormalSpectrum.locallyRingedSpaceMap_congr
      (φ₂ := awayCompletionHom (I.map (algebraMap R (D.B j'))) (D.gY j' j))
      (h₂ := le_comap_awayCompletionHom_base I (D.gY j' j)) (hφ := D.toAlgHom_toRingHom_eqB j' j),
    D.bBaseGlue j j' h',
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inrMap hI (D.τX i i' h).symm.toAlgHom
      (D.τY j j' h').symm.toAlgHom)]

/-! ### The reduced overlap obligation, dispatched by shape -/

/-- **The reduced overlap obligation of the second projection**, on the concrete `bothAlgData*`
glue. For distinct product-index charts `(i, j) ≠ (i', j')`, the concrete overlap immersion followed
by the per-chart second projection into its glue chart equals the concrete transition then the
flipped overlap immersion and its second projection — the datum `glueMorphisms` consumes once the
abstract carried glue has been pinned to `bothAlgData*` by the concreteness hypotheses. Dispatched
by which coordinate differs (`snd_base`/`fst_base`/`both_base`). -/
theorem bothAlgData_pr₂_naturality (i i' : D.JX) (j j' : D.JY) (h : (i, j) ≠ (i', j')) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    bothAlgDataF hI D.gX D.gY (i, j) (i', j') h ≫
        D.pr₂ChartSelf (i, j) ≫ D.yFormalGlueData.ι j =
      bothAlgDataT hI D.gX D.gY D.τX D.τY (i, j) (i', j') h ≫
        bothAlgDataF hI D.gX D.gY (i', j') (i, j) h.symm ≫
          D.pr₂ChartSelf (i', j') ≫ D.yFormalGlueData.ι j' := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  by_cases hii : i = i'
  · -- second coordinate differs: the genuine glued-`Y`-target case
    subst hii
    have hb : j ≠ j' := fun e => h (by rw [e])
    have hc1 : ((i, j) : D.JX × D.JY).1 = ((i, j') : D.JX × D.JY).1 := rfl
    have hc2 : ((i, j') : D.JX × D.JY).1 = ((i, j) : D.JX × D.JY).1 := rfl
    unfold bothAlgDataF bothAlgDataT
    rw [dif_pos hc1, dif_pos hc1, dif_pos hc2]
    simp only [eqAlgEquivA_self', Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [D.snd_base i j j' hb]
  · by_cases hjj : j = j'
    · -- first coordinate differs: invariant under `Spf(inr)`
      subst hjj
      have hc1 : ¬ ((i, j) : D.JX × D.JY).1 = ((i', j) : D.JX × D.JY).1 := hii
      have hc1' : ¬ ((i', j) : D.JX × D.JY).1 = ((i, j) : D.JX × D.JY).1 := fun e => hii e.symm
      have hc2 : ((i, j) : D.JX × D.JY).2 = ((i', j) : D.JX × D.JY).2 := rfl
      have hc2' : ((i', j) : D.JX × D.JY).2 = ((i, j) : D.JX × D.JY).2 := rfl
      unfold bothAlgDataF bothAlgDataT
      rw [dif_neg hc1, dif_pos hc2, dif_neg hc1, dif_pos hc2, dif_neg hc1', dif_pos hc2']
      simp only [eqAlgEquivB_self', Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      rw [reassoc_of% (D.fst_base i i' hii j)]
    · -- both coordinates differ
      have hc1 : ¬ ((i, j) : D.JX × D.JY).1 = ((i', j') : D.JX × D.JY).1 := hii
      have hc1' : ¬ ((i', j') : D.JX × D.JY).1 = ((i, j) : D.JX × D.JY).1 := fun e => hii e.symm
      have hc2 : ¬ ((i, j) : D.JX × D.JY).2 = ((i', j') : D.JX × D.JY).2 := hjj
      have hc2' : ¬ ((i', j') : D.JX × D.JY).2 = ((i, j) : D.JX × D.JY).2 := fun e => hjj e.symm
      unfold bothAlgDataF bothAlgDataT
      rw [dif_neg hc1, dif_neg hc2, dif_neg hc1, dif_neg hc2, dif_neg hc1', dif_neg hc2']
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [D.both_base i i' hii j j' hjj]

/-! ### The glued second projection -/

/-- **The second projection of the fully general two-sided fibre product** `pr₂ : X ×_{Spf R} Y ⟶ Y`
into the glued factor `Y`, glued from the per-chart second projections `pr₂ChartSelf p` composed
with the glue inclusions of the exposed `Y`, via `FormalScheme.GlueData.glueMorphisms`. The three
concreteness hypotheses `hV`/`hf`/`ht` pin the carried abstract glue of `D` to the concrete
`bothAlgData*` (holding by `rfl` for any `ofAlgebraData`-built datum); off the diagonal the overlap
obligation reduces to `bothAlgData_pr₂_naturality`, on the diagonal it collapses through
`GlueData.t_id`. -/
def pr₂
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
      D.yGlued.toLocallyRingedSpace :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  letI := D.topologyB
  letI := D.isAdicB
  D.formalGlueData.glueMorphisms (fun p => D.pr₂ChartSelf p ≫ D.yFormalGlueData.ι p.2) (by
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
      exact D.bothAlgData_pr₂_naturality i i' j j' hpp')

/-- **The second projection restricts to `pr₂ChartSelf p ≫ ι p.2` along each glue inclusion.** -/
@[reassoc (attr := simp)]
theorem ι_pr₂
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
    letI := D.topologyB
    letI := D.isAdicB
    D.formalGlueData.ι p ≫ D.pr₂ hV hf ht = D.pr₂ChartSelf p ≫ D.yFormalGlueData.ι p.2 :=
  D.formalGlueData.ι_glueMorphisms _ _ p

end BothChartedFibreDatumXY

end AlgebraicGeometry
