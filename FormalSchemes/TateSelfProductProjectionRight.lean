import FormalSchemes.TateCurveModel
import FormalSchemes.TateSelfProductObject
import FormalSchemes.TateSelfProductGlueDatum
import FormalSchemes.TateSelfProductTransitionRange
import FormalSchemes.TateSelfProductTransitionRangeRight
import FormalSchemes.TateSelfProductSummandNaturality
import FormalSchemes.TateSelfProductProjectionLeft
import FormalSchemes.TwoPatchFibreProductProjection
import FormalSchemes.TwoPatchFibreProductProjectionLeft
import FormalSchemes.CompletedTensorAwayInterchangePrLeft
import FormalSchemes.CompletedTensorAwayInterchangeMixedPullback
import FormalSchemes.CompletedTensorAwayInterchangeBothPullback
import FormalSchemes.GlueMorphisms
import FormalSchemes.TwoPatchFibreProductProjectionLeftInv
import FormalSchemes.TateSelfProductObjectInv
import FormalSchemes.TateSelfProductTransitionInv
import FormalSchemes.TateSelfProductDSigmaInv

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The second projection of the four-chart Tate self-fibre-product into `𝔈_q`

The four-chart Tate self-fibre product `𝔈_q ×_{Spf R} 𝔈_q` (`tateSelfProductInv`) is glued from four
copies of `Spf(A ⊗̂_R A)` (`A = R{x, y}/(x·y − q)`) indexed by `Bool × Bool`. This file builds the
**second projection** `pr₂ : 𝔈_q ×_{Spf R} 𝔈_q ⟶ 𝔈_q` into the glued Tate curve model `𝔈_q`
(`tateCurveModel`), gluing the affine second projections `pr₂Chart = Spf(inr)` (transported to the
base ideal convention through `annulusBaseBridge`) across the four charts and composing with the
glue inclusions `ι` of `𝔈_q`, via `FormalScheme.GlueData.glueMorphisms`. It is the factor-swap
mirror of the first projection `tateSelfProductPr₁` (`FormalSchemes.TateSelfProductProjectionLeft`),
exchanging the two tensor factors and `inl ↔ inr`.

The `𝔈_q` model is now glued from two annulus charts by the **𝔾m-inversion** chart transition
(`annulusChartTransitionInvSpf`), and the self-product object is glued by the induced inversion
transitions (`tateSelfProductFirstTransitionInv`, `tateSelfProductRightTransitionInv`,
`tateSelfProductBothTransitionInv`).

The compatibility datum consumed by `glueMorphisms` on each of the sixteen chart pairs `(i, j)`
splits by the *difference type* of `i, j`:

* first coordinate differs (`i.2 = j.2`): the second projection is invariant under the first-factor
  inversion transition (`firstTransitionInv_comp_secondProj`), so both sides land in the same glue
  chart;
* second coordinate differs (`i.2 ≠ j.2`, `i.1 = j.1`): the port of the two-chart curve naturality
  squares (`secondShape`), assembled by `coprod.hom_ext` from the base-changed two-patch
  fibre-product second-projection naturality;
* both coordinates differ: the coordinate inversion realises the `𝔈_q` chart transition on the
  second factor (`bothShapeRight`), obtained by factoring the both-factor chart through the
  second-factor chart (`bothChart_secondProj_factor`) and porting `secondShape` across the residual
  first-factor localization (`bothTransitionInv_secondProj_naturality`).

## Main definitions

* `AlgebraicGeometry.tateSelfProductPr₂`: the glued second projection `𝔈_q ×_{Spf R} 𝔈_q ⟶ 𝔈_q`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace CompletedTensorAwayInterchange

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- **The second-factor interchange open immersion is a morphism over the second projection
`Spf(inr)`.** Composing the second-factor interchange chart `Spf(A ⊗̂_R (B{1/g})) ⟶ Spf(A ⊗̂_R B)`
with the second projection `Spf(inr_{A,B}) : Spf(A ⊗̂_R B) ⟶ Spf B` recovers the second projection
of the localised chart `Spf(A ⊗̂_R (B{1/g})) ⟶ Spf(B{1/g})` followed by the affine basic-open chart
`Spf(B{1/g}) ⟶ Spf B` (the first factor `A` is untouched by localising the second factor). This is
the `inr`/second-factor mirror of `rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inl`,
obtained by conjugating the merged `interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl` through
the commutativity isomorphism `commSpfIso` (the two `commSpfIso`-swaps-projection lemmas). -/
theorem rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inr (g : B) (hI : I.FG) :
    rightInterchangeOpenImmersion (A := A) I g hI ≫
        FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R B))
          (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inr R I A B).toRingHom
          CompletedTensorProduct.inr_isAdicHom.le_comap =
      FormalSpectrum.locallyRingedSpaceMap
          (I.map (algebraMap R (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) g)))
          (CompletedTensorProduct.idealOfDefinition R I A
            (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) g))
          (CompletedTensorProduct.inr R I A
            (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) g)).toRingHom
          CompletedTensorProduct.inr_isAdicHom.le_comap ≫
        FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R B))
          (I.map (algebraMap R (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) g)))
          (FormalSpectrum.awayCompletionHom (I.map (algebraMap R B)) g)
          (le_comap_awayCompletionHom_base I g) := by
  rw [rightInterchangeOpenImmersion, Category.assoc, Category.assoc,
    commSpfIso_hom_comp_inrMap (A := B) (B := A) I hI,
    interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl (A := B) (B := A) I g hI,
    reassoc_of% (commSpfIso_hom_comp_inlMap (A := A)
      (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) g) I hI)]

end CompletedTensorAwayInterchange

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]

/-! ### SHAPE 2: second-differ naturality squares (ported to `𝔈_q`) -/

/-- `x`-overlap second-projection naturality (`ι₀`-side, forward). -/
theorem secondShape_inl (hq : q ∈ I) (hI : I.FG) :
    rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      (rightSummandInv R I q hI).hom ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI ≫
          pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
            (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  simp only [pr₂Chart]
  rw [reassoc_of% (rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inr
      (A := annulusAlgebra R I q) I (overlapX R I q) hI),
    reassoc_of% (rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inr
      (A := annulusAlgebra R I q) I (overlapY R I q) hI),
    rightSummandInv, mapSpfIso_hom,
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inrMap hI
      (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom
      (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom),
    reassoc_of% (spfAwayX_comp_baseBridge R I q),
    tateCurve_glue_rel_x R I q hq hI,
    reassoc_of% (spfESymm_comp_spfAwayY_comp_baseBridge_inv R I q hI)]

/-- `y`-overlap second-projection naturality (`ι₀`-side, with prepended transition). -/
theorem secondShape_inr' (hq : q ∈ I) (hI : I.FG) :
    (rightSummandInv R I q hI).hom ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  simp only [pr₂Chart, rightSummandInv, mapSpfIso_hom]
  rw [reassoc_of% (rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inr
      (A := annulusAlgebra R I q) I (overlapY R I q) hI),
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inrMap hI
      (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom
      (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom),
    reassoc_of% (spfESymm_comp_spfAwayY_comp_baseBridge_inv R I q hI),
    reassoc_of% (rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inr
      (A := annulusAlgebra R I q) I (overlapX R I q) hI),
    reassoc_of% (spfAwayX_comp_baseBridge R I q),
    tateCurve_glue_rel_y R I q hq hI]
  simp only [Iso.hom_inv_id_assoc]

/-- `y`-overlap second-projection naturality (`ι₀`-side, reverse). -/
theorem secondShape_inr (hq : q ∈ I) (hI : I.FG) :
    rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      (rightSummandInv R I q hI).inv ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI ≫
          pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
            (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  rw [← secondShape_inr' R I q hq hI, Iso.inv_hom_id_assoc]

/-- **SHAPE 2 forward** (`i.2 = false`, `j.2 = true`): the second-differ compatibility square, whose
`ι` indices go `false ↦ true`. Assembled by `coprod.hom_ext` from
`secondShape_inl`/`secondShape_inr` (`rightSummand = mapSpfIso (refl A) (chart transition)`). -/
theorem secondShape_fwd (hq : q ∈ I) (hI : I.FG) :
    secondFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      (tateSelfProductRightTransitionInv R I q hI).hom ≫ secondFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  refine coprod.hom_ext ?_ ?_
  · simp only [secondFactorOverlapChart, tateSelfProductRightTransitionInv, rightSummandInv,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact secondShape_inl R I q hq hI
  · simp only [secondFactorOverlapChart, tateSelfProductRightTransitionInv, rightSummandInv,
      coprod.inr_desc_assoc, coprod.inl_desc_assoc, Category.assoc]
    exact secondShape_inr R I q hq hI

/-- **SHAPE 2 reverse** (`i.2 = true`, `j.2 = false`): the second-differ compatibility square, whose
`ι` indices go `true ↦ false`. -/
theorem secondShape_rev (hq : q ∈ I) (hI : I.FG) :
    secondFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ =
      (tateSelfProductRightTransitionInv R I q hI).hom ≫ secondFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ := by
  refine coprod.hom_ext ?_ ?_
  · simp only [secondFactorOverlapChart, tateSelfProductRightTransitionInv, rightSummandInv,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact (secondShape_inr' R I q hq hI).symm
  · simp only [secondFactorOverlapChart, tateSelfProductRightTransitionInv, rightSummandInv,
      coprod.inr_desc_assoc, coprod.inl_desc_assoc, Category.assoc]
    rw [secondShape_inl R I q hq hI, Iso.inv_hom_id_assoc]

/-! ### SHAPE 1: first-differ (the second projection is invariant) -/

/-- **SHAPE 1** (`i.2 = j.2`): the first-factor inversion transition is invisible to the second
projection, so both sides land in the *same* glue chart `ι b`. -/
theorem firstShapeInvariant (hq : q ∈ I) (hI : I.FG) (b : ULift.{u} Bool) :
    firstFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι b =
      (tateSelfProductFirstTransitionInv R I q hI).hom ≫ firstFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι b := by
  rw [reassoc_of% (firstTransitionInv_comp_secondProj R I q hI)]

/-! ### SHAPE 3: both-differ (the coordinate inversion realises the chart transition) -/

omit [IsNoetherianRing R] in
/-- **Per-summand second-projection factorisation.** Under the second projection `Spf(inr)`, the
both-factor interchange chart at `(a, b)` collapses onto the second-factor interchange chart at `b`,
after the first-factor localization `interchangeOpenImmersion` at `a`. Both sides reduce to the
normal form `Spf(inr_{A{1/a}, A{1/b}}) ≫ Spf(A →ₐ A{1/b})` via the raw second-projection naturality
`mapSpf_comp_inrMap`, the residual `Spf(id)` on the second factor collapsing to `𝟙`. -/
theorem bothInterchange_pr₂Chart_factor (a b : annulusAlgebra R I q) (hI : I.FG) :
    bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I a b hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) =
      interchangeOpenImmersion
          (B := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b) I a hI ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I b hI ≫
          pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) := by
  rw [bothInterchangeOpenImmersion_eq_mapSpf (A := annulusAlgebra R I q)
        (B := annulusAlgebra R I q) I a b hI,
    rightInterchangeOpenImmersion_eq_mapSpf (A := annulusAlgebra R I q) I b hI,
    interchangeOpenImmersion_eq_mapSpf
      (B := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b) I a hI]
  simp only [pr₂Chart]
  rw [CompletedTensorProduct.mapSpf_comp_inrMap hI
      (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a))
      (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b)),
    CompletedTensorProduct.mapSpf_comp_inrMap hI
      (AlgHom.id R (annulusAlgebra R I q))
      (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b)),
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inrMap hI
      (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a))
      (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b)))]
  have hf :
      ((AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b)).toRingHom) =
        RingHom.id (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b) := by
    ext x
    simp
  rw [FormalSpectrum.locallyRingedSpaceMap_congr
      (φ₂ := RingHom.id (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b))
      (h₂ := (Ideal.comap_id (I.map (algebraMap R
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b)))).ge) (hφ := hf),
    FormalSpectrum.locallyRingedSpaceMap_id, Category.id_comp]

omit [IsNoetherianRing R] in
/-- **The second projection of the both-factor overlap chart factors through the second-factor
overlap chart.** Under the second projection `Spf(inr)`, the first tensor factor's localization is
forgotten, so the both chart collapses onto the second-factor chart after the first localization
`interchangeOpenImmersion`. -/
theorem bothChart_secondProj_factor (hI : I.FG) :
    bothFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) =
      coprod.desc
        (coprod.desc
          (interchangeOpenImmersion
              (B := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
              I (overlapX R I q) hI ≫ coprod.inl)
          (interchangeOpenImmersion
              (B := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
              I (overlapX R I q) hI ≫ coprod.inr))
        (coprod.desc
          (interchangeOpenImmersion
              (B := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
              I (overlapY R I q) hI ≫ coprod.inl)
          (interchangeOpenImmersion
              (B := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
              I (overlapY R I q) hI ≫ coprod.inr)) ≫
        secondFactorOverlapChart R I q hI ≫
          pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) := by
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_)
  · simp only [bothFactorOverlapChart, secondFactorOverlapChart, coprod.inl_desc_assoc,
      Category.assoc]
    exact bothInterchange_pr₂Chart_factor R I q (overlapX R I q) (overlapX R I q) hI
  · simp only [bothFactorOverlapChart, secondFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc]
    exact bothInterchange_pr₂Chart_factor R I q (overlapX R I q) (overlapY R I q) hI
  · simp only [bothFactorOverlapChart, secondFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc]
    exact bothInterchange_pr₂Chart_factor R I q (overlapY R I q) (overlapX R I q) hI
  · simp only [bothFactorOverlapChart, secondFactorOverlapChart, coprod.inr_desc_assoc,
      Category.assoc]
    exact bothInterchange_pr₂Chart_factor R I q (overlapY R I q) (overlapY R I q) hI

omit [IsNoetherianRing R] in
/-- **Backbone naturality of the forget-first-factor collapse `Ξ'`.** The both-factor inversion
transition, followed by the both-chart collapse onto the second-factor chart (`Ξ'`), followed by the
second-factor chart and second projection, coincides with `Ξ'` followed by the second-factor
inversion transition (and second chart/projection). The first-factor localizations `Ξ'` carries are
invisible to the second projection, so only the second-factor inversion transition survives. This is
the residual of the both-transition under `pr₂`, replacing the swap file's base coordinate-flip. The
pr₂ mirror of `bothTransitionInv_firstProj_naturality`. -/
theorem bothTransitionInv_secondProj_naturality (hI : I.FG) :
    (tateSelfProductBothTransitionInv R I q hI).hom ≫
        bothFactorOverlapChart R I q hI ≫
          pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) =
      coprod.desc
        (coprod.desc
          (interchangeOpenImmersion
              (B := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
              I (overlapX R I q) hI ≫ coprod.inl)
          (interchangeOpenImmersion
              (B := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
              I (overlapX R I q) hI ≫ coprod.inr))
        (coprod.desc
          (interchangeOpenImmersion
              (B := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
              I (overlapY R I q) hI ≫ coprod.inl)
          (interchangeOpenImmersion
              (B := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
              I (overlapY R I q) hI ≫ coprod.inr)) ≫
        (tateSelfProductRightTransitionInv R I q hI).hom ≫
          secondFactorOverlapChart R I q hI ≫
            pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) := by
  rw [bothChart_secondProj_factor R I q hI]
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_)
  · simp only [tateSelfProductBothTransitionInv, tateSelfProductRightTransitionInv,
      secondFactorOverlapChart, bothSummandDiagInv, rightSummandInv,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc, mapSpfIso_hom, mapSpfIso_inv,
      rightInterchangeOpenImmersion_eq_mapSpf, interchangeOpenImmersion_eq_mapSpf, pr₂Chart]
    simp only [CompletedTensorProduct.mapSpf_comp_inrMap,
      reassoc_of% CompletedTensorProduct.mapSpf_comp_inrMap, locallyRingedSpaceMap_algHom_id,
      Category.id_comp]
  · simp only [tateSelfProductBothTransitionInv, tateSelfProductRightTransitionInv,
      secondFactorOverlapChart, bothSummandAntiInv, rightSummandInv,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc, mapSpfIso_hom, mapSpfIso_inv,
      rightInterchangeOpenImmersion_eq_mapSpf, interchangeOpenImmersion_eq_mapSpf, pr₂Chart]
    simp only [CompletedTensorProduct.mapSpf_comp_inrMap,
      reassoc_of% CompletedTensorProduct.mapSpf_comp_inrMap, locallyRingedSpaceMap_algHom_id,
      Category.id_comp]
    -- the surviving second factor is `transition.symm.symm`; collapse it (single rewrite, to
    -- avoid an expensive `AlgEquiv.symm_symm` simp over the completed-tensor-product terms)
    rw [AlgEquiv.symm_symm]
  · simp only [tateSelfProductBothTransitionInv, tateSelfProductRightTransitionInv,
      secondFactorOverlapChart, bothSummandAntiInv, rightSummandInv,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc, mapSpfIso_hom, mapSpfIso_inv,
      rightInterchangeOpenImmersion_eq_mapSpf, interchangeOpenImmersion_eq_mapSpf, pr₂Chart]
    simp only [CompletedTensorProduct.mapSpf_comp_inrMap,
      reassoc_of% CompletedTensorProduct.mapSpf_comp_inrMap, locallyRingedSpaceMap_algHom_id,
      Category.id_comp]
  · simp only [tateSelfProductBothTransitionInv, tateSelfProductRightTransitionInv,
      secondFactorOverlapChart, bothSummandDiagInv, rightSummandInv,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc, mapSpfIso_hom, mapSpfIso_inv,
      rightInterchangeOpenImmersion_eq_mapSpf, interchangeOpenImmersion_eq_mapSpf, pr₂Chart]
    simp only [CompletedTensorProduct.mapSpf_comp_inrMap,
      reassoc_of% CompletedTensorProduct.mapSpf_comp_inrMap, locallyRingedSpaceMap_algHom_id,
      Category.id_comp]

/-- **SHAPE 3 forward** (`i.2 = false`, `j.2 = true`). -/
theorem bothShapeRight_fwd (hq : q ∈ I) (hI : I.FG) :
    bothFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ =
      (tateSelfProductBothTransitionInv R I q hI).hom ≫ bothFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ := by
  rw [reassoc_of% (bothTransitionInv_secondProj_naturality R I q hI),
    reassoc_of% (bothChart_secondProj_factor R I q hI), secondShape_fwd R I q hq hI]

/-- **SHAPE 3 reverse** (`i.2 = true`, `j.2 = false`). -/
theorem bothShapeRight_rev (hq : q ∈ I) (hI : I.FG) :
    bothFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩ =
      (tateSelfProductBothTransitionInv R I q hI).hom ≫ bothFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩ := by
  rw [reassoc_of% (bothTransitionInv_secondProj_naturality R I q hI),
    reassoc_of% (bothChart_secondProj_factor R I q hI), secondShape_rev R I q hq hI]

/-! ### The glued second projection -/

/-- **The second projection of the four-chart Tate self-fibre product** `pr₂ : 𝔈_q ×_{Spf R} 𝔈_q ⟶
𝔈_q`, glued from the four affine second projections `pr₂Chart` (transported to the target convention
and composed with the glue inclusions of `𝔈_q`) via `FormalScheme.GlueData.glueMorphisms`, using the
sixteen-case compatibility squares. -/
def tateSelfProductPr₂ (hq : q ∈ I) (hI : I.FG) :
    (tateSelfProductInv R I q hq hI).toLocallyRingedSpace ⟶
      (tateCurveModel R I q hq hI).toLocallyRingedSpace :=
  (tateSelfProductFormalGlueDataInv R I q hq hI).glueMorphisms
    (fun i => pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫
      annulusBaseBridge R I q ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨i.down.2⟩) (by
      intro i j
      by_cases hij : i = j
      · subst hij
        simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
      · have hij' : ¬ @Eq (ULift.{u} (Bool × Bool)) i j := hij
        have hji' : ¬ @Eq (ULift.{u} (Bool × Bool)) j i := fun heq => hij heq.symm
        simp only [tateSelfProductFormalGlueDataInv, tateSelfProductLRSGlueDataInv,
          tateSelfProductGlueData'Inv, CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji', Category.assoc,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        congr 1
        rcases i with ⟨⟨_ | _, _ | _⟩⟩ <;> rcases j with ⟨⟨_ | _, _ | _⟩⟩ <;>
          first
            | exact absurd rfl hij'
            | exact firstShapeInvariant R I q hq hI _
            | exact secondShape_fwd R I q hq hI
            | exact secondShape_rev R I q hq hI
            | exact bothShapeRight_fwd R I q hq hI
            | exact bothShapeRight_rev R I q hq hI)

end AlgebraicGeometry
