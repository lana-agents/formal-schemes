import FormalSchemes.TateCurveModel
import FormalSchemes.TateSelfProductObject
import FormalSchemes.TateSelfProductGlueDatum
import FormalSchemes.TateSelfProductTransitionRangeRight
import FormalSchemes.TateSelfProductSummandNaturality
import FormalSchemes.TwoPatchFibreProductProjectionLeft
import FormalSchemes.CompletedTensorAwayInterchangeBothPullback
import FormalSchemes.GlueMorphisms

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The first projection of the four-chart Tate self-fibre-product into `𝔈_q`

The four-chart Tate self-fibre product `𝔈_q ×_{Spf R} 𝔈_q` (`tateSelfProduct`) is glued from four
copies of `Spf(A ⊗̂_R A)` (`A = R{x, y}/(x·y − q)`) indexed by `Bool × Bool`. This file builds the
**first projection** `pr₁ : 𝔈_q ×_{Spf R} 𝔈_q ⟶ 𝔈_q` into the glued Tate curve model `𝔈_q`
(`tateCurveModel`), gluing the affine first projections `pr₁Chart = Spf(inl)` (transported to the
base ideal convention) across the four charts and composing with the glue inclusions `ι` of `𝔈_q`,
via `FormalScheme.GlueData.glueMorphisms`.

The compatibility datum consumed by `glueMorphisms` on each of the sixteen chart pairs `(i, j)`
splits by the *difference type* of `i, j`:

* second coordinate differs (`i.1 = j.1`): the first projection is invariant under the second-factor
  swap transition (`rightTransition_comp_firstProj`), so both sides land in the same glue chart;
* first coordinate differs (`i.1 ≠ j.1`, `i.2 = j.2`): the port of the two-chart curve naturality
  squares (`firstShape`), assembled by `coprod.hom_ext` from the base-changed two-patch
  fibre-product first-projection naturality;
* both coordinates differ: the coordinate-flip realises the `𝔈_q` chart transition on the first
  factor (`bothShape`), using the both-factor transition naturality
  (`tateSelfProductBothTransition_naturality`) and the raw first-projection naturality of `mapSpf`.

## Main definitions

* `AlgebraicGeometry.tateSelfProductPr₁`: the glued first projection `𝔈_q ×_{Spf R} 𝔈_q ⟶ 𝔈_q`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]

/-! ### The per-chart first projection through the ideal-convention bridge -/

omit [IsNoetherianRing R] in
/-- `pr₁Chart` at `B = A` equals `pr₁ChartSelf ≫ annulusBaseBridge`: the raw first projection
`Spf(inl)` followed by the base ideal-convention bridge. -/
theorem pr₁Chart_eq :
    pr₁Chart R I q (annulusAlgebra R I q) =
      pr₁ChartSelf R I q ≫ annulusBaseBridge R I q := rfl

/-! ### The circular glue relations of `𝔈_q = tateCurveModel` -/

/-- **The `tateCurveModel` glue condition on the `(false, true)` overlap.** -/
theorem tateCurve_glue_condition (hq : q ∈ I) (hI : I.FG) :
    coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q) ≫
        (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      coprod.desc ((annulusChartTransitionSpf R I q hI).hom ≫ coprod.inr)
          ((annulusChartTransitionSpf R I q hI).inv ≫ coprod.inl) ≫
        coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q) ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  have h01 : ({ down := false } : ULift.{u} Bool) ≠ { down := true } := by decide
  have h10 : ({ down := true } : ULift.{u} Bool) ≠ { down := false } := by decide
  have key := (tateCurveLRSGlueData R I q hq hI).toGlueData.glue_condition ⟨false⟩ ⟨true⟩
  set ι0 := (tateCurveLRSGlueData R I q hq hI).toGlueData.ι ⟨false⟩ with hι0
  set ι1 := (tateCurveLRSGlueData R I q hq hI).toGlueData.ι ⟨true⟩ with hι1
  simp only [tateCurveLRSGlueData, tateCurveGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
    dif_neg h01, dif_neg h10, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  rw [cancel_epi] at key
  exact key.symm

/-- The `x`-overlap circular glue relation of `𝔈_q`. -/
theorem tateCurve_glue_rel_x (hq : q ∈ I) (hI : I.FG) :
    annulusOverlapChart R I q ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      (annulusChartTransitionSpf R I q hI).hom ≫ annulusOverlapChartY R I q ≫
        (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  have := tateCurve_glue_condition R I q hq hI
  have h := congrArg (fun m => coprod.inl ≫ m) this
  simpa only [coprod.inl_desc_assoc, coprod.inl_desc, Category.assoc, coprod.inr_desc_assoc]
    using h

/-- The `y`-overlap circular glue relation of `𝔈_q`. -/
theorem tateCurve_glue_rel_y (hq : q ∈ I) (hI : I.FG) :
    annulusOverlapChartY R I q ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      (annulusChartTransitionSpf R I q hI).inv ≫ annulusOverlapChart R I q ≫
        (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  have := tateCurve_glue_condition R I q hq hI
  have h := congrArg (fun m => coprod.inr ≫ m) this
  simpa only [coprod.inr_desc_assoc, coprod.inr_desc, Category.assoc, coprod.inl_desc_assoc]
    using h

/-! ### SHAPE 2: first-differ naturality squares (ported to `𝔈_q`) -/

/-- `x`-overlap first-projection naturality (`ι₀`-side, forward). -/
theorem firstShape_inl (hq : q ∈ I) (hI : I.FG) :
    interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI ≫
        pr₁Chart R I q (annulusAlgebra R I q) ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      (twoPatchFibreProductTransition R I q (annulusAlgebra R I q) hI).hom ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI ≫
          pr₁Chart R I q (annulusAlgebra R I q) ≫
            (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  simp only [pr₁Chart, Category.assoc]
  rw [reassoc_of% (interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl I (overlapX R I q) hI),
    reassoc_of% (interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl I (overlapY R I q) hI),
    twoPatchFibreProductTransition, mapSpfIso_hom,
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inlMap hI
      (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom
      (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom),
    reassoc_of% (spfAwayX_comp_baseBridge R I q),
    tateCurve_glue_rel_x R I q hq hI,
    reassoc_of% (spfESymm_comp_spfAwayY_comp_baseBridge R I q hI)]

/-- `y`-overlap first-projection naturality (`ι₀`-side, with prepended transition). -/
theorem firstShape_inr' (hq : q ∈ I) (hI : I.FG) :
    (twoPatchFibreProductTransition R I q (annulusAlgebra R I q) hI).hom ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI ≫
        pr₁Chart R I q (annulusAlgebra R I q) ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI ≫
        pr₁Chart R I q (annulusAlgebra R I q) ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  simp only [pr₁Chart, Category.assoc, twoPatchFibreProductTransition, mapSpfIso_hom]
  rw [reassoc_of% (interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl I (overlapY R I q) hI),
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inlMap hI
      (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom
      (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom),
    reassoc_of% (spfESymm_comp_spfAwayY_comp_baseBridge R I q hI),
    reassoc_of% (interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl I (overlapX R I q) hI),
    reassoc_of% (spfAwayX_comp_baseBridge R I q),
    tateCurve_glue_rel_y R I q hq hI]
  simp only [Iso.hom_inv_id_assoc]

/-- `y`-overlap first-projection naturality (`ι₀`-side, reverse). -/
theorem firstShape_inr (hq : q ∈ I) (hI : I.FG) :
    interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI ≫
        pr₁Chart R I q (annulusAlgebra R I q) ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      (twoPatchFibreProductTransition R I q (annulusAlgebra R I q) hI).inv ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI ≫
          pr₁Chart R I q (annulusAlgebra R I q) ≫
            (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  rw [← firstShape_inr' R I q hq hI, Iso.inv_hom_id_assoc]

/-- **SHAPE 2 forward** (`i.1 = false`, `j.1 = true`): the first-differ compatibility square, whose
`ι` indices go `false ↦ true`. Assembled by `coprod.hom_ext` from `firstShape_inl`/`firstShape_inr`
(`firstSummand = twoPatchFibreProductTransition`). -/
theorem firstShape_fwd (hq : q ∈ I) (hI : I.FG) :
    firstFactorOverlapChart R I q hI ≫ pr₁Chart R I q (annulusAlgebra R I q) ≫
        (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      (tateSelfProductFirstTransition R I q hI).hom ≫ firstFactorOverlapChart R I q hI ≫
        pr₁Chart R I q (annulusAlgebra R I q) ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  refine coprod.hom_ext ?_ ?_
  · simp only [firstFactorOverlapChart, tateSelfProductFirstTransition, firstSummand,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact firstShape_inl R I q hq hI
  · simp only [firstFactorOverlapChart, tateSelfProductFirstTransition, firstSummand,
      coprod.inr_desc_assoc, coprod.inl_desc_assoc, Category.assoc]
    exact firstShape_inr R I q hq hI

/-- **SHAPE 2 reverse** (`i.1 = true`, `j.1 = false`): the first-differ compatibility square, whose
`ι` indices go `true ↦ false`. -/
theorem firstShape_rev (hq : q ∈ I) (hI : I.FG) :
    firstFactorOverlapChart R I q hI ≫ pr₁Chart R I q (annulusAlgebra R I q) ≫
        (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ =
      (tateSelfProductFirstTransition R I q hI).hom ≫ firstFactorOverlapChart R I q hI ≫
        pr₁Chart R I q (annulusAlgebra R I q) ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ := by
  refine coprod.hom_ext ?_ ?_
  · simp only [firstFactorOverlapChart, tateSelfProductFirstTransition, firstSummand,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact (firstShape_inr' R I q hq hI).symm
  · simp only [firstFactorOverlapChart, tateSelfProductFirstTransition, firstSummand,
      coprod.inr_desc_assoc, coprod.inl_desc_assoc, Category.assoc]
    -- goal: interchangeY ≫ P ≫ ι₁ = t.inv ≫ interchangeX ≫ P ≫ ι₀
    rw [firstShape_inl R I q hq hI, Iso.inv_hom_id_assoc]

/-! ### SHAPE 1: second-differ (the first projection is invariant) -/

/-- **SHAPE 1** (`i.1 = j.1`): the second-factor swap transition is invisible to the first
projection, so both sides land in the *same* glue chart `ι b`. -/
theorem secondShape (hq : q ∈ I) (hI : I.FG) (b : ULift.{u} Bool) :
    secondFactorOverlapChart R I q hI ≫ pr₁Chart R I q (annulusAlgebra R I q) ≫
        (tateCurveFormalGlueData R I q hq hI).ι b =
      (tateSelfProductRightTransition R I q hI).hom ≫ secondFactorOverlapChart R I q hI ≫
        pr₁Chart R I q (annulusAlgebra R I q) ≫ (tateCurveFormalGlueData R I q hq hI).ι b := by
  simp only [pr₁Chart_eq, Category.assoc]
  rw [reassoc_of% (rightTransition_comp_firstProj R I q hI)]

/-! ### SHAPE 3: both-differ (the coordinate flip realises the chart transition) -/

/-- The base coordinate-flip `Spf(annulusFlip) : Spf(I·A) ⟶ Spf(I·A)`, the residual of the
both-factor transition under the first projection. -/
def spfFlipBase (hI : I.FG) :
    locallyRingedSpaceObj (I.map (algebraMap R (annulusAlgebra R I q))) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (annulusAlgebra R I q))) :=
  FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (annulusAlgebra R I q)))
    (I.map (algebraMap R (annulusAlgebra R I q)))
    (annulusFlip R I q hI).toAlgHom.toRingHom
    (CompletedTensorProduct.algHom_mapIdeal_isAdicHom (annulusFlip R I q hI).toAlgHom).le_comap

omit [IsNoetherianRing R] in
/-- **The first-factor transition is a morphism over the first projection, up to the base
coordinate-flip.** -/
theorem firstTransition_comp_firstProj (hI : I.FG) :
    (tateSelfProductFirstTransition R I q hI).hom ≫
        firstFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q =
      firstFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q ≫ spfFlipBase R I q hI := by
  rw [reassoc_of% (tateSelfProductFirstTransition_naturality R I q hI), spfFlipBase, pr₁ChartSelf,
    CompletedTensorProduct.mapSpf_comp_inlMap hI (annulusFlip R I q hI).toAlgHom
      (AlgHom.id R (annulusAlgebra R I q))]

/-- The first-factor base relation (forward): the first projection of the first-factor overlap chart
into `ι₀` equals its coordinate-flip into `ι₁`. Reformulation of `firstShape_fwd`. -/
theorem firstBaseRel_fwd (hq : q ∈ I) (hI : I.FG) :
    firstFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q ≫
        annulusBaseBridge R I q ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      firstFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q ≫ spfFlipBase R I q hI ≫
        annulusBaseBridge R I q ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  have h := firstShape_fwd R I q hq hI
  simp only [pr₁Chart_eq, Category.assoc] at h
  rw [reassoc_of% (firstTransition_comp_firstProj R I q hI)] at h
  exact h

/-- The first-factor base relation (reverse). Reformulation of `firstShape_rev`. -/
theorem firstBaseRel_rev (hq : q ∈ I) (hI : I.FG) :
    firstFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q ≫
        annulusBaseBridge R I q ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ =
      firstFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q ≫ spfFlipBase R I q hI ≫
        annulusBaseBridge R I q ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ := by
  have h := firstShape_rev R I q hq hI
  simp only [pr₁Chart_eq, Category.assoc] at h
  rw [reassoc_of% (firstTransition_comp_firstProj R I q hI)] at h
  exact h

omit [IsNoetherianRing R] in
/-- **The both-factor transition is a morphism over the first projection, up to the base
coordinate-flip.** Under the first projection `Spf(inl)`, the both-factor swap transition acts as
the coordinate-flip on the first tensor factor (the second factor being forgotten). -/
theorem bothTransition_comp_firstProj (hI : I.FG) :
    (tateSelfProductBothTransition R I q hI).hom ≫
        bothFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q =
      bothFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q ≫ spfFlipBase R I q hI := by
  rw [reassoc_of% (tateSelfProductBothTransition_naturality R I q hI), spfFlipBase, pr₁ChartSelf,
    CompletedTensorProduct.mapSpf_comp_inlMap hI (annulusFlip R I q hI).toAlgHom
      (annulusFlip R I q hI).toAlgHom]

omit [IsNoetherianRing R] in
/-- **Per-summand first-projection factorisation.** Under the first projection `Spf(inl)`, the
both-factor interchange chart at `(a, b)` collapses onto the first-factor interchange chart at `a`,
after the second-factor localization `rightInterchangeOpenImmersion` at `b`. Both sides reduce to
the normal form `Spf(inl_{A{1/a}, A{1/b}}) ≫ Spf(A →ₐ A{1/a})` via the raw first-projection
naturality `mapSpf_comp_inlMap`, the residual `Spf(id)` on the right collapsing to `𝟙`. -/
theorem bothInterchange_pr₁ChartSelf_factor (a b : annulusAlgebra R I q) (hI : I.FG) :
    bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I a b hI ≫
        pr₁ChartSelf R I q =
      rightInterchangeOpenImmersion
          (A := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a) I b hI ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I a hI ≫ pr₁ChartSelf R I q := by
  rw [bothInterchangeOpenImmersion_eq_mapSpf (A := annulusAlgebra R I q)
        (B := annulusAlgebra R I q) I a b hI,
    interchangeOpenImmersion_eq_mapSpf (B := annulusAlgebra R I q) I a hI,
    rightInterchangeOpenImmersion_eq_mapSpf
      (A := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a) I b hI]
  simp only [pr₁ChartSelf]
  rw [CompletedTensorProduct.mapSpf_comp_inlMap hI
      (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a))
      (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b)),
    CompletedTensorProduct.mapSpf_comp_inlMap hI
      (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a))
      (AlgHom.id R (annulusAlgebra R I q)),
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inlMap hI
      (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a))
      (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b)))]
  have hf :
      ((AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a)).toRingHom) =
        RingHom.id (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a) := by
    ext x
    simp
  rw [FormalSpectrum.locallyRingedSpaceMap_congr
      (φ₂ := RingHom.id (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a))
      (h₂ := (Ideal.comap_id (I.map (algebraMap R
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a)))).ge) (hφ := hf),
    FormalSpectrum.locallyRingedSpaceMap_id, Category.id_comp]

omit [IsNoetherianRing R] in
/-- **The first projection of the both-factor overlap chart factors through the first-factor overlap
chart.** Under the first projection `Spf(inl)`, the second tensor factor's localization is
forgotten, so the both chart collapses onto the first-factor chart after the second localization
`rightInterchangeOpenImmersion`. -/
theorem bothChart_firstProj_factor (hI : I.FG) :
    bothFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q =
      coprod.desc
        (coprod.desc
          (rightInterchangeOpenImmersion
              (A := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
              I (overlapX R I q) hI ≫ coprod.inl)
          (rightInterchangeOpenImmersion
              (A := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
              I (overlapY R I q) hI ≫ coprod.inl))
        (coprod.desc
          (rightInterchangeOpenImmersion
              (A := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
              I (overlapX R I q) hI ≫ coprod.inr)
          (rightInterchangeOpenImmersion
              (A := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
              I (overlapY R I q) hI ≫ coprod.inr)) ≫
        firstFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q := by
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_)
  · simp only [bothFactorOverlapChart, firstFactorOverlapChart, coprod.inl_desc_assoc,
      Category.assoc]
    exact bothInterchange_pr₁ChartSelf_factor R I q (overlapX R I q) (overlapX R I q) hI
  · simp only [bothFactorOverlapChart, firstFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc]
    exact bothInterchange_pr₁ChartSelf_factor R I q (overlapX R I q) (overlapY R I q) hI
  · simp only [bothFactorOverlapChart, firstFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc]
    exact bothInterchange_pr₁ChartSelf_factor R I q (overlapY R I q) (overlapX R I q) hI
  · simp only [bothFactorOverlapChart, firstFactorOverlapChart, coprod.inr_desc_assoc,
      Category.assoc]
    exact bothInterchange_pr₁ChartSelf_factor R I q (overlapY R I q) (overlapY R I q) hI

/-- **SHAPE 3 forward** (`i.1 = false`, `j.1 = true`). -/
theorem bothShape_fwd (hq : q ∈ I) (hI : I.FG) :
    bothFactorOverlapChart R I q hI ≫ pr₁Chart R I q (annulusAlgebra R I q) ≫
        (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      (tateSelfProductBothTransition R I q hI).hom ≫ bothFactorOverlapChart R I q hI ≫
        pr₁Chart R I q (annulusAlgebra R I q) ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  simp only [pr₁Chart_eq, Category.assoc]
  rw [reassoc_of% (bothTransition_comp_firstProj R I q hI)]
  simp only [reassoc_of% (bothChart_firstProj_factor R I q hI)]
  rw [firstBaseRel_fwd R I q hq hI]

/-- **SHAPE 3 reverse** (`i.1 = true`, `j.1 = false`). -/
theorem bothShape_rev (hq : q ∈ I) (hI : I.FG) :
    bothFactorOverlapChart R I q hI ≫ pr₁Chart R I q (annulusAlgebra R I q) ≫
        (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ =
      (tateSelfProductBothTransition R I q hI).hom ≫ bothFactorOverlapChart R I q hI ≫
        pr₁Chart R I q (annulusAlgebra R I q) ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ := by
  simp only [pr₁Chart_eq, Category.assoc]
  rw [reassoc_of% (bothTransition_comp_firstProj R I q hI)]
  simp only [reassoc_of% (bothChart_firstProj_factor R I q hI)]
  rw [firstBaseRel_rev R I q hq hI]

/-! ### The glued first projection -/

/-- **The first projection of the four-chart Tate self-fibre product** `pr₁ : 𝔈_q ×_{Spf R} 𝔈_q ⟶
𝔈_q`, glued from the four affine first projections `pr₁Chart` (composed with the glue inclusions of
`𝔈_q`) via `FormalScheme.GlueData.glueMorphisms`, using the sixteen-case compatibility squares. -/
def tateSelfProductPr₁ (hq : q ∈ I) (hI : I.FG) :
    (tateSelfProduct R I q hq hI).toLocallyRingedSpace ⟶
      (tateCurveModel R I q hq hI).toLocallyRingedSpace :=
  (tateSelfProductFormalGlueData R I q hq hI).glueMorphisms
    (fun i => pr₁Chart R I q (annulusAlgebra R I q) ≫
      (tateCurveFormalGlueData R I q hq hI).ι ⟨i.down.1⟩) (by
      intro i j
      by_cases hij : i = j
      · subst hij
        simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
      · have hij' : ¬ @Eq (ULift.{u} (Bool × Bool)) i j := hij
        have hji' : ¬ @Eq (ULift.{u} (Bool × Bool)) j i := fun heq => hij heq.symm
        simp only [tateSelfProductFormalGlueData, tateSelfProductLRSGlueData,
          tateSelfProductGlueData', CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji', Category.assoc,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        congr 1
        rcases i with ⟨⟨_ | _, _ | _⟩⟩ <;> rcases j with ⟨⟨_ | _, _ | _⟩⟩ <;>
          first
            | exact absurd rfl hij'
            | exact secondShape R I q hq hI _
            | exact firstShape_fwd R I q hq hI
            | exact firstShape_rev R I q hq hI
            | exact bothShape_fwd R I q hq hI
            | exact bothShape_rev R I q hq hI)

end AlgebraicGeometry

