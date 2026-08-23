import FormalSchemes.GeneralFibreProductExposeX
import FormalSchemes.GeneralFibreProductProjection

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The first projection of the general fibre product `X ×_{Spf R} Spf B`

`FormalSchemes.GeneralFibreProductAffineBase` assembles, from an `AffineChartedFibreDatum`, the
fibre product `X ×_{Spf R} Spf B` of a general affine-charted glued `X` over the affine base `Spf B`
as `AffineChartedFibreDatum.fibreProduct`, and `FormalSchemes.GeneralFibreProductExposeX` exposes
the glued affine-charted `X` itself as `AffineChartedFibreDatumX.xGlued`. `FormalSchemes.
GeneralFibreProductProjection` built the **second** projection `pr₂ : X ×_{Spf R} Spf B ⟶ Spf B`.

This file builds the **first** projection `pr₁ : X ×_{Spf R} Spf B ⟶ X` into the *glued* target `X`,
gluing the affine first projections `Spf(inl) : Spf(A_i ⊗̂_R B) ⟶ Spf(A_i)` across the cover and
composing with the glue inclusions `ι` of the exposed `X`, via
`FormalScheme.GlueData.glueMorphisms`.
It generalises the two-patch first projection `AlgebraicGeometry.twoPatchFibreProductPr₁`
(`FormalSchemes.TwoPatchFibreProductProjectionLeft`, `J = ULift Bool`) to the general index `J`.

Because the exposed `X` is glued directly in the `I·A_i = I.map (algebraMap R (A i))` convention,
`pr₁Chart` is the raw `Spf(inl)` with **no base ideal-convention bridge** (unlike the two-patch,
whose target `tateTwoPatch` lived over `annulusIdealOfDefinition`). A single light *overlap* bridge
`xOverlapBridge` — `Spf(id)` across the equal ideals `I·(A_i{1/g_ij})` and
`FormalSpectrum.awayCompletionIdeal (I·A_i) (g_ij)`
(`CompletedTensorAwayInterchange.idealOfDef_base_eq`) — reconciles the interchange's `inl`-factor
with `X`'s basic-open overlap charts.

The compatibility datum `glueMorphisms` consumes on the double overlap is the naturality square

`interchange(g_ij) ≫ pr₁Chart_i ≫ ι_i = t.hom ≫ interchange(g_ji) ≫ pr₁Chart_j ≫ ι_j`

(`AffineChartedFibreDatumX.pr₁_naturality`), assembled from:

* the interchange chart, under the first projection, lands in the basic-open chart of `A_i`
  (`interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl`, #133);
* the base-changed transition `t = (mapSpfIso τ (refl B)).hom` commutes with `inl`
  (`CompletedTensorProduct.mapSpf_comp_inlMap`);
* the exposed `X`'s own glue relation `x_glue_rel` (its `LocallyRingedSpace.GlueData` glue
  condition, unfolded through `GlueData.ofGlueData'`).

## Main definitions

* `AffineChartedFibreDatumX.pr₁Chart`: the per-chart first projection `Spf(A_i ⊗̂_R B) ⟶ Spf(A_i)`.
* `AffineChartedFibreDatumX.pr₁_naturality`: the double-overlap compatibility square.
* `AffineChartedFibreDatumX.pr₁`: the glued first projection `X ×_{Spf R} Spf B ⟶ X`.
* `AffineChartedFibreDatumX.ι_pr₁`: it restricts to `pr₁Chart_i ≫ ι_i` along each glue inclusion.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum
open CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

namespace AffineChartedFibreDatumX

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable {B : Type u} [CommRing B] [Algebra R B]
variable (D : AffineChartedFibreDatumX R I hI B)

/-! ### The per-chart first projection and the overlap ideal-convention bridge -/

/-- **The per-chart first projection** `Spf(A_i ⊗̂_R B) ⟶ Spf(A_i)`: the raw `Spf(inl)` map of
formal spectra, landing directly in the `I·A_i` convention of the exposed `X` (no base bridge). -/
def pr₁Chart (i : D.J) :
    letI := D.commRing
    letI := D.algebra
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (D.A i) B) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (D.A i))) :=
  letI := D.commRing
  letI := D.algebra
  FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.A i)))
    (CompletedTensorProduct.idealOfDefinition R I (D.A i) B)
    (CompletedTensorProduct.inl R I (D.A i) B).toRingHom
    CompletedTensorProduct.inl_isAdicHom.le_comap

/-- **The overlap ideal-convention bridge** `Spf(I·(A_i{1/g_ij})) ⟶ Spf(awayCompletionIdeal (I·A_i)
g_ij)`: `Spf` of the identity ring hom across the two (equal, by `idealOfDef_base_eq`) ideals of
definition of the away completion `A_i{1/g_ij}`. Reconciles the `I·(A_i{1/g})` convention produced
by `interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl` with the `awayCompletionIdeal`
convention of `X`'s overlap charts. -/
def xOverlapBridge (i j : D.J) :
    letI := D.commRing
    letI := D.algebra
    locallyRingedSpaceObj
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i))) (D.g i j)))) ⟶
      locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R (D.A i))) (D.g i j)) :=
  letI := D.commRing
  letI := D.algebra
  FormalSpectrum.locallyRingedSpaceMap
    (awayCompletionIdeal (I.map (algebraMap R (D.A i))) (D.g i j))
    (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i))) (D.g i j))))
    (RingHom.id _) (by
      rw [Ideal.comap_id]
      exact (CompletedTensorAwayInterchange.idealOfDef_base_eq I (D.g i j)).ge)

/-! ### The two ideal-convention bridge squares -/

/-- **The interchange `inl`-factor of chart `i` factors through the overlap bridge and `X`'s
basic-open chart.** The away-completion structural map `Spf(awayCompletionHom (I·A_i) g_ij)` (the
last factor of `interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl`) equals the overlap bridge
followed by the basic-open chart `basicOpenChart (I·A_i) g_ij` of the exposed `X`. -/
theorem spfAwayInl (i j : D.J) :
    letI := D.commRing
    letI := D.algebra
    FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.A i)))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i))) (D.g i j))))
        (awayCompletionHom (I.map (algebraMap R (D.A i))) (D.g i j))
        (le_comap_awayCompletionHom_base I (D.g i j)) =
      D.xOverlapBridge i j ≫ basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i j) := by
  letI := D.commRing
  letI := D.algebra
  rw [xOverlapBridge, basicOpenChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := awayCompletionHom (I.map (algebraMap R (D.A i))) (D.g i j)) (ψ := RingHom.id _)
      (hIK := by rw [RingHom.id_comp]; exact le_comap_awayCompletionHom_base I (D.g i j))]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ (RingHom.id_comp _).symm

/-- **The transition-side bridge square.** The base-changed `Spf(inl)`-transition
`Spf((τ_ij)⁻¹)` (in the `I·(A{1/g})` convention, the second factor of `mapSpf_comp_inlMap`) followed
by the interchange `inl`-factor of chart `j` equals the overlap bridge of `i`, the `X`-side
transition `awayCompletionTransition`, and `X`'s basic-open chart of `j`. Both sides collapse to a
single `locallyRingedSpaceMap` out of `Spf(I·(A_i{1/g_ij}))`, whose ring maps agree by
`RingHom.comp_id`. -/
theorem spfτsymm_awayInl (i j : D.J) (h : i ≠ j) :
    letI := D.commRing
    letI := D.algebra
    FormalSpectrum.locallyRingedSpaceMap
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A j))) (D.g j i))))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A i))) (D.g i j))))
        (D.τ i j h).symm.toAlgHom.toRingHom
        (CompletedTensorProduct.algHom_mapIdeal_isAdicHom (D.τ i j h).symm.toAlgHom).le_comap ≫
      FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.A j)))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (D.A j))) (D.g j i))))
        (awayCompletionHom (I.map (algebraMap R (D.A j))) (D.g j i))
        (le_comap_awayCompletionHom_base I (D.g j i)) =
      D.xOverlapBridge i j ≫ awayCompletionTransition (D.g i j) (D.g j i) (D.τ i j h) ≫
        basicOpenChart (I.map (algebraMap R (D.A j))) (D.g j i) := by
  letI := D.commRing
  letI := D.algebra
  rw [xOverlapBridge, awayCompletionTransition, basicOpenChart,
    -- LHS: fuse `Spf(τ⁻¹) ≫ Spf(awayCompletionHom_j)` into one map out of `Spf(I·(A_i{1/g}))`.
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := awayCompletionHom (I.map (algebraMap R (D.A j))) (D.g j i))
      (ψ := (D.τ i j h).symm.toAlgHom.toRingHom)
      (hIK := le_comap_comp _ _ (le_comap_awayCompletionHom_base I (D.g j i))
        (CompletedTensorProduct.algHom_mapIdeal_isAdicHom (D.τ i j h).symm.toAlgHom).le_comap),
    -- RHS: fuse `awayCompletionTransition ≫ basicOpenChart_j`, then the overlap bridge.
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := awayCompletionHom (I.map (algebraMap R (D.A j))) (D.g j i))
      (ψ := (D.τ i j h).symm.toRingHom)
      (hIK := le_comap_comp _ _ (FormalSpectrum.le_comap_awayCompletionHom _ _)
        (awayCompletionTransition_le_comap (D.g i j) (D.g j i) (D.τ i j h))),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := ((D.τ i j h).symm.toRingHom).comp
        (awayCompletionHom (I.map (algebraMap R (D.A j))) (D.g j i)))
      (ψ := RingHom.id _)
      (hIK := by
        rw [RingHom.id_comp, CompletedTensorAwayInterchange.idealOfDef_base_eq]
        exact le_comap_comp _ _ (FormalSpectrum.le_comap_awayCompletionHom _ _)
          (awayCompletionTransition_le_comap (D.g i j) (D.g j i) (D.τ i j h)))]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  rw [RingHom.id_comp]
  rfl

/-! ### The exposed `X` glue relation -/

/-- **The exposed `X`'s glue relation on the double overlap.** For distinct charts `i ≠ j`, `X`'s
basic-open overlap chart followed by the glue inclusion `ι_i` equals the `X`-side transition
`awayCompletionTransition` followed by the `(j,i)`-overlap chart and `ι_j`. This is the glue
condition of `xLrsGlueData` on the `(i,j)`-overlap, unfolded through `GlueData.ofGlueData'`. -/
theorem x_glue_rel (i j : D.J) (h : i ≠ j) :
    letI := D.commRing
    letI := D.algebra
    basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i j) ≫ D.xFormalGlueData.ι i =
      awayCompletionTransition (D.g i j) (D.g j i) (D.τ i j h) ≫
        basicOpenChart (I.map (algebraMap R (D.A j))) (D.g j i) ≫ D.xFormalGlueData.ι j := by
  letI := D.commRing
  letI := D.algebra
  have hij' : ¬ @Eq D.J i j := h
  have hji' : ¬ @Eq D.J j i := fun heq => h heq.symm
  have key := D.xLrsGlueData.toGlueData.glue_condition i j
  simp only [xLrsGlueData, xGlueData', CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji', Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  rw [cancel_epi] at key
  exact key.symm

/-! ### The double-overlap compatibility square of the first projection -/

/-- **The double-overlap compatibility square of the first projection.** For distinct charts
`i ≠ j`, the `(i,j)`-overlap interchange chart followed by `pr₁Chart_i` and the glue inclusion `ι_i`
equals the base-changed transition `t i j = (mapSpfIso τ_ij (refl B)).hom` followed by the
`(j,i)`-overlap interchange chart, `pr₁Chart_j` and `ι_j` — the datum `glueMorphisms` consumes to
glue `pr₁` across the cover. -/
theorem pr₁_naturality (i j : D.J) (h : i ≠ j) :
    letI := D.commRing
    letI := D.algebra
    interchangeOpenImmersion (B := B) I (D.g i j) hI ≫ D.pr₁Chart i ≫ D.xFormalGlueData.ι i =
      (mapSpfIso hI (D.τ i j h) (AlgEquiv.refl (R := R) (A₁ := B))).hom ≫
        interchangeOpenImmersion (B := B) I (D.g j i) hI ≫
          D.pr₁Chart j ≫ D.xFormalGlueData.ι j := by
  letI := D.commRing
  letI := D.algebra
  simp only [pr₁Chart]
  rw [reassoc_of% (interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl I (D.g i j) hI),
    reassoc_of% (interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl I (D.g j i) hI),
    mapSpfIso_hom,
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inlMap hI (D.τ i j h).symm.toAlgHom
      (AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom),
    reassoc_of% (D.spfAwayInl i j),
    D.x_glue_rel i j h,
    reassoc_of% (D.spfτsymm_awayInl i j h)]

/-! ### The glued first projection -/

/-- **The first projection of the general fibre product** `pr₁ : X ×_{Spf R} Spf B ⟶ X`, glued from
the per-chart first projections `pr₁Chart_i` composed with the glue inclusions of the exposed `X`,
via `FormalScheme.GlueData.glueMorphisms`. Off the diagonal the overlap obligation is
`pr₁_naturality`; on the diagonal it collapses through `GlueData.t_id`. -/
def pr₁ :
    (D.fibreProduct).toLocallyRingedSpace ⟶ (D.xGlued).toLocallyRingedSpace :=
  letI := D.commRing
  letI := D.algebra
  D.formalGlueData.glueMorphisms (fun i => D.pr₁Chart i ≫ D.xFormalGlueData.ι i) (by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · have hij' : ¬ @Eq D.J i j := hij
      have hji' : ¬ @Eq D.J j i := fun heq => hij heq.symm
      simp only [AffineChartedFibreDatum.formalGlueData, AffineChartedFibreDatum.lrsGlueData,
        AffineChartedFibreDatum.glueData', CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji', Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      congr 1
      exact D.pr₁_naturality i j hij')

/-- **The first projection restricts to `pr₁Chart_i ≫ ι_i` along each glue inclusion.** -/
@[reassoc (attr := simp)]
theorem ι_pr₁ (i : D.J) :
    letI := D.commRing
    letI := D.algebra
    D.formalGlueData.ι i ≫ D.pr₁ = D.pr₁Chart i ≫ D.xFormalGlueData.ι i :=
  D.formalGlueData.ι_glueMorphisms _ _ i

end AffineChartedFibreDatumX

end AlgebraicGeometry
