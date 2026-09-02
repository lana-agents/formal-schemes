import FormalSchemes.TateSelfProductTripleOverlap
import FormalSchemes.TateSelfProductTransition
import FormalSchemes.TateTransition
import FormalSchemes.TwoPatchFibreProductObject
import FormalSchemes.TateChartTransitionAlgEq
import FormalSchemes.CompletedTensorAwayInterchangeMixedPullback
import FormalSchemes.CompletedTensorAwayInterchangeBothPullback

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Transition-through-chart naturality of the Tate self-product overlaps (Family B)

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q` the coordinate
ring of the formal Tate annulus and `C = A ⊗̂_R A`. The four-chart Tate self-fibre-product
`𝔈_q ×_{Spf R} 𝔈_q` glue (`TateSelfProductGlueDatum`) has three overlap transitions
(`TateSelfProductTransition`) which permute the summands of the three overlap objects, and three
interchange overlap charts into `Spf C` (`TateSelfProductTripleOverlap`).

This file records the **full morphism-level naturality** of each transition against the interchange
overlap charts, landing in `Spf C`:

* `tateSelfProductFirstTransition_naturality`:
  `t_first.hom ≫ firstFactorOverlapChart = firstFactorOverlapChart ≫ mapSpf hI flip id`;
* `tateSelfProductRightTransition_naturality`:
  `t_right.hom ≫ secondFactorOverlapChart = secondFactorOverlapChart ≫ mapSpf hI id flip`;
* `tateSelfProductBothTransition_naturality`:
  `t_both.hom ≫ bothFactorOverlapChart = bothFactorOverlapChart ≫ mapSpf hI flip flip`,

where `flip = annulusFlip R I q hI : A ≃ₐ[R] A` is the coordinate-swap involution
(`TateTransition`). These upgrade the projection-level naturality lemmas (`TransitionRange{,Right}`)
to the full morphism into `Spf(A ⊗̂_R A)`.

The reduction is pure `mapSpf` functoriality: every interchange chart is `mapSpf` of a localization
`R`-algebra map (`interchangeOpenImmersion_eq_mapSpf` / `rightInterchangeOpenImmersion_eq_mapSpf` /
`bothInterchangeOpenImmersion_eq_mapSpf`), and every transition is `mapSpfIso` of the chart
transition, so each per-summand square collapses via `mapSpf_comp` to the crux algebra-map identity
`annulusFibreChartTransitionAlg (locX a) = locY (annulusFlip a)`
(`annulusFibreChartTransitionAlg_algebraMap`), which expresses that the chart transition is the
completed localization of the coordinate swap.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The crux algebra-map identity

All the completion ideal-transports (`congrIdealₐ`) are handled at the `RingHom.comp` level with the
black-box lemmas `congrIdeal_toRingHom_comp_algebraMap` and its `symm` variant
(keeping `congrIdeal` opaque, avoiding the pathologically expensive concrete pointwise route), and
`awayCompletionHom` is identified with `algebraMap` of the base annulus algebra by
`FormalSpectrum.awayCompletionHom_eq_algebraMap` (`FormalSchemes/BasicOpenChart.lean`), which is
that scalar tower at an arbitrary base; this file carried a `private` copy of it, specialised to
the annulus algebra, until issue 1456 rehomed the general one. -/

/-- The localized coordinate swap on the localizations `A[x⁻¹] → A[y⁻¹]` restricted to `A`. -/
private theorem locTransition_comp_algebraMap_A (hI : I.FG) :
    (annulusLocTransition R I q hI : annulusLoc R I q →+* annulusLocY R I q).comp
        (algebraMap (annulusAlgebra R I q) (annulusLoc R I q)) =
      (algebraMap (annulusAlgebra R I q) (annulusLocY R I q)).comp
        (annulusFlip R I q hI).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply]
  exact annulusLocTransition_algebraMap R I q hI a

/-- The completed overlap transition on the structural map from `A[x⁻¹]`. -/
private theorem overlapTransitionHom_comp_algebraMap (hI : I.FG) :
    (annulusOverlapTransitionHom R I q hI).comp
        (algebraMap (annulusLoc R I q) (annulusOverlap R I q)) =
      (algebraMap (annulusLocY R I q) (annulusOverlapY R I q)).comp
        (annulusLocTransition R I q hI : annulusLoc R I q →+* annulusLocY R I q) := by
  refine RingHom.ext fun b => ?_
  simp only [RingHom.comp_apply]
  exact annulusOverlapTransitionHom_algebraMap R I q hI b

private theorem overlapTransAlg_toRingHom (hI : I.FG) :
    (annulusOverlapTransitionAlg R I q hI).toRingHom = annulusOverlapTransitionHom R I q hI := rfl

private theorem chartTrans_toRingHom_eq (hI : I.FG) :
    (annulusChartTransitionAlg R I q hI).toRingHom =
      (annulusChartOverlapAlgY R I q).symm.toRingHom.comp
        ((annulusOverlapTransitionHom R I q hI).comp
          (annulusChartOverlapAlgX R I q).toRingHom) := by
  rw [annulusChartTransitionAlg, algEquiv_trans_toRingHom, algEquiv_trans_toRingHom,
    overlapTransAlg_toRingHom, RingHom.comp_assoc]

private theorem L1 :
    (annulusChartOverlapAlgX R I q).toRingHom.comp
        (FormalSpectrum.awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)) =
      algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) := by
  rw [annulusChartOverlapAlgX, AdicCompletion.congrIdealₐ_toRingHom,
    FormalSpectrum.awayCompletionHom, ← RingHom.comp_assoc,
    AdicCompletion.congrIdeal_toRingHom_comp_algebraMap]
  exact (IsScalarTower.algebraMap_eq (annulusAlgebra R I q) (annulusLoc R I q)
    (annulusOverlap R I q)).symm

private theorem L2 (hI : I.FG) :
    (annulusOverlapTransitionHom R I q hI).comp
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) =
      (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q)).comp
        (annulusFlip R I q hI).toRingHom := by
  rw [IsScalarTower.algebraMap_eq (annulusAlgebra R I q) (annulusLoc R I q) (annulusOverlap R I q),
    ← RingHom.comp_assoc, overlapTransitionHom_comp_algebraMap, RingHom.comp_assoc,
    locTransition_comp_algebraMap_A, ← RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq (annulusAlgebra R I q) (annulusLocY R I q)
      (annulusOverlapY R I q)]

private theorem L3 :
    (annulusChartOverlapAlgY R I q).symm.toRingHom.comp
        (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q)) =
      algebraMap (annulusAlgebra R I q)
        (awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q)) := by
  rw [annulusChartOverlapAlgY, AdicCompletion.congrIdealₐ_symm_toRingHom,
    IsScalarTower.algebraMap_eq (annulusAlgebra R I q) (annulusLocY R I q) (annulusOverlapY R I q),
    ← RingHom.comp_assoc, AdicCompletion.congrIdeal_symm_toRingHom_comp_algebraMap,
    ← IsScalarTower.algebraMap_eq (annulusAlgebra R I q) (annulusLocY R I q)
      (awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q))]

private theorem middle_comp (hI : I.FG) :
    (annulusChartTransitionAlg R I q hI).toRingHom.comp
        (FormalSpectrum.awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)) =
      (FormalSpectrum.awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)).comp
        (annulusFlip R I q hI).toRingHom := by
  rw [chartTrans_toRingHom_eq, RingHom.comp_assoc, RingHom.comp_assoc, L1, L2,
    ← RingHom.comp_assoc, L3, FormalSpectrum.awayCompletionHom_eq_algebraMap]

private theorem B1 :
    (annulusFibreChartBridgeX R I q).toRingHom.comp
        (FormalSpectrum.awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q)) =
      FormalSpectrum.awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q) := by
  rw [annulusFibreChartBridgeX, AdicCompletion.congrIdealₐ_toRingHom]
  simp only [FormalSpectrum.awayCompletionHom]
  rw [← RingHom.comp_assoc, AdicCompletion.congrIdeal_toRingHom_comp_algebraMap]

private theorem B3 :
    (annulusFibreChartBridgeY R I q).symm.toRingHom.comp
        (FormalSpectrum.awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)) =
      FormalSpectrum.awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q) := by
  rw [annulusFibreChartBridgeY, AdicCompletion.congrIdealₐ_symm_toRingHom]
  simp only [FormalSpectrum.awayCompletionHom]
  rw [← RingHom.comp_assoc, AdicCompletion.congrIdeal_symm_toRingHom_comp_algebraMap]

private theorem fibreChartTrans_toRingHom_eq (hI : I.FG) :
    (annulusFibreChartTransitionAlg R I q hI).toRingHom =
      (annulusFibreChartBridgeY R I q).symm.toRingHom.comp
        ((annulusChartTransitionAlg R I q hI).toRingHom.comp
          (annulusFibreChartBridgeX R I q).toRingHom) := by
  rw [annulusFibreChartTransitionAlg, algEquiv_trans_toRingHom, algEquiv_trans_toRingHom,
    RingHom.comp_assoc]

/-- The chart transition, as a ring hom, restricted to `A` (via the structural completion maps),
intertwines the `x`-localization with the `y`-localization through the coordinate swap. -/
private theorem crux_comp (hI : I.FG) :
    (annulusFibreChartTransitionAlg R I q hI).toRingHom.comp
        (FormalSpectrum.awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q)) =
      (FormalSpectrum.awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q)).comp (annulusFlip R I q hI).toRingHom := by
  rw [fibreChartTrans_toRingHom_eq, RingHom.comp_assoc, RingHom.comp_assoc, B1, middle_comp,
    ← RingHom.comp_assoc, B3]

/-- **Crux algebra-map identity.** The `R`-algebra chart transition `A{1/x} ≃ₐ[R] A{1/y}` sends the
image of `a` under the localization `A → A{1/x}` to the image of `annulusFlip a` under `A → A{1/y}`:
the transition is the completed localization of the coordinate-swap automorphism. -/
theorem annulusFibreChartTransitionAlg_algebraMap (hI : I.FG) (a : annulusAlgebra R I q) :
    annulusFibreChartTransitionAlg R I q hI
        (algebraMap (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) a) =
      algebraMap (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusFlip R I q hI a) := by
  have h := RingHom.congr_fun (crux_comp R I q hI) a
  simp only [RingHom.comp_apply, FormalSpectrum.awayCompletionHom_eq_algebraMap] at h
  exact h

private theorem flip_flip (hI : I.FG) (a : annulusAlgebra R I q) :
    annulusFlip R I q hI (annulusFlip R I q hI a) = a := by
  rw [annulusFlip_apply, annulusFlip_apply, ← AlgHom.comp_apply, annulusFlipHom_annulusFlipHom,
    AlgHom.id_apply]

/-- The `symm` form of the crux identity. -/
theorem annulusFibreChartTransitionAlg_symm_algebraMap (hI : I.FG) (a : annulusAlgebra R I q) :
    (annulusFibreChartTransitionAlg R I q hI).symm
        (algebraMap (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) a) =
      algebraMap (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusFlip R I q hI a) := by
  rw [AlgEquiv.symm_apply_eq, annulusFibreChartTransitionAlg_algebraMap, flip_flip]

/-! ### The AlgHom-composite forms and `mapSpf` congruence -/

/-- Abbreviation for the localization `R`-algebra map `A →ₐ[R] A{1/f}`. -/
private abbrev locHom (f : annulusAlgebra R I q) :
    annulusAlgebra R I q →ₐ[R]
      awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) f :=
  IsScalarTower.toAlgHom R (annulusAlgebra R I q)
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) f)

/-- The chart transition composed with the `x`-localization equals the `y`-localization composed
with the coordinate swap (algebra-hom form of the crux). -/
private theorem chartTrans_comp_locX (hI : I.FG) :
    (annulusFibreChartTransitionAlg R I q hI).toAlgHom.comp (locHom R I q (overlapX R I q)) =
      (locHom R I q (overlapY R I q)).comp (annulusFlip R I q hI).toAlgHom := by
  refine AlgHom.ext fun a => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
    IsScalarTower.toAlgHom_apply]
  exact annulusFibreChartTransitionAlg_algebraMap R I q hI a

/-- The inverse chart transition composed with the `y`-localization equals the `x`-localization
composed with the coordinate swap. -/
private theorem chartTrans_symm_comp_locY (hI : I.FG) :
    (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom.comp (locHom R I q (overlapY R I q)) =
      (locHom R I q (overlapX R I q)).comp (annulusFlip R I q hI).toAlgHom := by
  refine AlgHom.ext fun a => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
    IsScalarTower.toAlgHom_apply]
  exact annulusFibreChartTransitionAlg_symm_algebraMap R I q hI a

/-- `mapSpf` depends only on the two `R`-algebra maps. -/
private theorem mapSpf_congr {A₀ B₀ A₁ B₁ : Type u} [CommRing A₀] [CommRing B₀] [CommRing A₁]
    [CommRing B₁] [Algebra R A₀] [Algebra R B₀] [Algebra R A₁] [Algebra R B₁] (hI : I.FG)
    {f₁ f₂ : A₀ →ₐ[R] A₁} {g₁ g₂ : B₀ →ₐ[R] B₁} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    CompletedTensorProduct.mapSpf hI f₁ g₁ = CompletedTensorProduct.mapSpf hI f₂ g₂ := by
  subst hf hg; rfl

/-- The identity-pair `refl.symm ∘ id = id ∘ id` collapse for the untouched tensor factor. -/
private theorem refl_symm_comp_id :
    (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom.comp
        (AlgHom.id R (annulusAlgebra R I q)) =
      (AlgHom.id R (annulusAlgebra R I q)).comp (AlgHom.id R (annulusAlgebra R I q)) := by
  ext a; simp

private theorem refl_comp_id :
    (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom.comp
        (AlgHom.id R (annulusAlgebra R I q)) =
      (AlgHom.id R (annulusAlgebra R I q)).comp (AlgHom.id R (annulusAlgebra R I q)) := by
  ext a; simp

/-! ### The three morphism-level naturality squares -/

/-- **First-factor transition naturality.** The first-factor overlap transition, composed with the
first-factor overlap chart into `Spf(A ⊗̂_R A)`, is `mapSpf` of the coordinate swap on the first
tensor factor (the second factor untouched). -/
theorem tateSelfProductFirstTransition_naturality (hI : I.FG) :
    (tateSelfProductFirstTransition R I q hI).hom ≫ firstFactorOverlapChart R I q hI =
      firstFactorOverlapChart R I q hI ≫
        CompletedTensorProduct.mapSpf hI (annulusFlip R I q hI).toAlgHom
          (AlgHom.id R (annulusAlgebra R I q)) := by
  refine coprod.hom_ext ?_ ?_
  · simp only [tateSelfProductFirstTransition, firstFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inr_desc, Category.assoc]
    rw [firstSummand, twoPatchFibreProductTransition, mapSpfIso_hom,
      interchangeOpenImmersion_eq_mapSpf, interchangeOpenImmersion_eq_mapSpf,
      ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (chartTrans_symm_comp_locY R I q hI) (refl_symm_comp_id R I q)
  · simp only [tateSelfProductFirstTransition, firstFactorOverlapChart, coprod.inr_desc_assoc,
      coprod.inl_desc, Category.assoc]
    rw [firstSummand, twoPatchFibreProductTransition, mapSpfIso_inv,
      interchangeOpenImmersion_eq_mapSpf, interchangeOpenImmersion_eq_mapSpf,
      ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (chartTrans_comp_locX R I q hI) (refl_comp_id R I q)

/-- **Second-factor transition naturality.** The second-factor overlap transition, composed with the
second-factor overlap chart into `Spf(A ⊗̂_R A)`, is `mapSpf` of the coordinate swap on the second
tensor factor (the first factor untouched). -/
theorem tateSelfProductRightTransition_naturality (hI : I.FG) :
    (tateSelfProductRightTransition R I q hI).hom ≫ secondFactorOverlapChart R I q hI =
      secondFactorOverlapChart R I q hI ≫
        CompletedTensorProduct.mapSpf hI (AlgHom.id R (annulusAlgebra R I q))
          (annulusFlip R I q hI).toAlgHom := by
  refine coprod.hom_ext ?_ ?_
  · simp only [tateSelfProductRightTransition, secondFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inr_desc, Category.assoc]
    rw [rightSummand, mapSpfIso_hom, rightInterchangeOpenImmersion_eq_mapSpf,
      rightInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (refl_symm_comp_id R I q) (chartTrans_symm_comp_locY R I q hI)
  · simp only [tateSelfProductRightTransition, secondFactorOverlapChart, coprod.inr_desc_assoc,
      coprod.inl_desc, Category.assoc]
    rw [rightSummand, mapSpfIso_inv, rightInterchangeOpenImmersion_eq_mapSpf,
      rightInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (refl_comp_id R I q) (chartTrans_comp_locX R I q hI)

/-- **Both-factor transition naturality.** The both-factor overlap transition, composed with the
both-factor overlap chart into `Spf(A ⊗̂_R A)`, is `mapSpf` of the coordinate swap on *both* tensor
factors. -/
theorem tateSelfProductBothTransition_naturality (hI : I.FG) :
    (tateSelfProductBothTransition R I q hI).hom ≫ bothFactorOverlapChart R I q hI =
      bothFactorOverlapChart R I q hI ≫
        CompletedTensorProduct.mapSpf hI (annulusFlip R I q hI).toAlgHom
          (annulusFlip R I q hI).toAlgHom := by
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_)
  · simp only [tateSelfProductBothTransition, bothFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inr_desc, Category.assoc]
    rw [bothSummandDiag, mapSpfIso_hom, bothInterchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (chartTrans_symm_comp_locY R I q hI)
      (chartTrans_symm_comp_locY R I q hI)
  · simp only [tateSelfProductBothTransition, bothFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, coprod.inl_desc, coprod.inr_desc, Category.assoc]
    rw [bothSummandAnti, mapSpfIso_hom, AlgEquiv.symm_symm, bothInterchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (chartTrans_symm_comp_locY R I q hI) (chartTrans_comp_locX R I q hI)
  · simp only [tateSelfProductBothTransition, bothFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, coprod.inl_desc, coprod.inr_desc, Category.assoc]
    rw [bothSummandAnti, mapSpfIso_inv, bothInterchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (chartTrans_comp_locX R I q hI) (chartTrans_symm_comp_locY R I q hI)
  · simp only [tateSelfProductBothTransition, bothFactorOverlapChart, coprod.inr_desc_assoc,
      coprod.inl_desc, Category.assoc]
    rw [bothSummandDiag, mapSpfIso_inv, bothInterchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (chartTrans_comp_locX R I q hI) (chartTrans_comp_locX R I q hI)

end AlgebraicGeometry
