import FormalSchemes.TateSelfProductDSigmaInv
import FormalSchemes.TateSelfProductGlueDatum

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The four-chart Tate self-product `GlueData'` cocycle (𝔾m-inversion model)

This is the 𝔾m-**inversion** (issue 442/435c) analogue of `TateSelfProductCocycle`. It closes the
`cocycle` field of the eventual `GlueData'` on `J = Bool × Bool` for the corrected (separated) Tate
self-fibre-product,

`t' i j k ≫ t' j k i ≫ t' k i j = 𝟙`,

for every pairwise-distinct triple `i j k : Bool × Bool`.

## The route (why it differs from the swap)

The swap cocycle collapses the `σ`-triple through the naturality square
`tateSelfProductSigma_hom_comp_bothChart`, which lands in a common endomorphism `mapSpf hI (A-endo)
(A-endo)` because the swap `annulusFlip` is an `A`-algebra automorphism. The 𝔾m inversion
`annulusFibreChartTransitionInvAlg` is **not** an `A`-algebra automorphism, so that route does not
transfer (see `2026-08-15-issue446-DSigma-inv-naturality-NOT-a-mirror.md`).

Instead we exploit that `tateSelfProductSigmaInv i j k` is, on the four summands
`(dXX ⨿ dXY) ⨿ (dYX ⨿ dYY)`, the **regular representation of the Klein 4-group**: the three
transitions `tateSelfProductSwapFirstTransitionInv`, `tateSelfProductSwapSecondTransitionInv`,
`tateSelfProductBothTransitionInv` are the three non-identity involutions, with
`both = swapFirst ≫ swapSecond = swapSecond ≫ swapFirst`. Each of these two summand identities
(`e1`/`e2`) reduces summand-by-summand to a single `mapSpf` collapse (`mapSpf_comp` + a composition
with `AlgEquiv.refl`), which is cheap. All six ordered triples of the three distinct Klein elements
then compose to `𝟙` by pure category algebra, and `tateSelfProductSigmaInv_triple` follows by a
`Bool × Bool` case split. This avoids the heavy coproduct re-expansion the naive route requires.

## Main results

* `AlgebraicGeometry.tateSelfProductSigmaInv_triple`: the `σ`-triple identity (inversion).
* `AlgebraicGeometry.tateSelfProductGlueTInv_fac`: the `t_fac` field (for free from the lift API).
* `AlgebraicGeometry.tateSelfProductGlueCocycleInv`: the four-chart cocycle (inversion).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* Mathlib `CategoryTheory.GlueData'` (the `t'`/`t_fac`/`cocycle` fields).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- `mapSpf` depends only on the two `R`-algebra maps (local copy of the `mapSpf_congr` idiom of
`TateSelfProductDSigmaInv`). -/
private theorem mapSpf_congr {A₀ B₀ A₁ B₁ : Type u} [CommRing A₀] [CommRing B₀] [CommRing A₁]
    [CommRing B₁] [Algebra R A₀] [Algebra R B₀] [Algebra R A₁] [Algebra R B₁] (hI : I.FG)
    {f₁ f₂ : A₀ →ₐ[R] A₁} {g₁ g₂ : B₀ →ₐ[R] B₁} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    CompletedTensorProduct.mapSpf hI f₁ g₁ = CompletedTensorProduct.mapSpf hI f₂ g₂ := by
  subst hf hg; rfl

/-- Normalise the `AlgEquiv.refl`/`symm` clutter left after `mapSpf_comp`, without touching the
inversion transition `annulusFibreChartTransitionInvAlg` (a `simp` here would unfold it and blow
up). -/
local macro "norm_refl" : tactic =>
  `(tactic| first
    | rw [AlgEquiv.refl_symm, AlgEquiv.refl_toAlgHom, AlgEquiv.symm_symm]
    | rw [AlgEquiv.refl_symm, AlgEquiv.refl_toAlgHom]
    | rw [AlgEquiv.refl_toAlgHom, AlgEquiv.symm_symm]
    | rw [AlgEquiv.refl_toAlgHom])

/-! ### `both = swapFirst ≫ swapSecond`, summand by summand -/

@[reassoc]
theorem e1_XX (hI : I.FG) :
    (swapFirstSummandXXInv R I q hI).hom ≫ (swapSecondSummandYXInv R I q hI).hom =
      (bothSummandDiagInv R I q hI).hom := by
  simp only [swapFirstSummandXXInv, swapSecondSummandYXInv, bothSummandDiagInv, mapSpfIso_hom]
  rw [← CompletedTensorProduct.mapSpf_comp]
  refine mapSpf_congr R I hI ?_ ?_
  · norm_refl; exact AlgHom.comp_id _
  · norm_refl; exact AlgHom.id_comp _

@[reassoc]
theorem e1_XY (hI : I.FG) :
    (swapFirstSummandXYInv R I q hI).hom ≫ (swapSecondSummandYXInv R I q hI).inv =
      (bothSummandAntiInv R I q hI).hom := by
  simp only [swapFirstSummandXYInv, swapSecondSummandYXInv, bothSummandAntiInv, mapSpfIso_hom,
    mapSpfIso_inv]
  rw [← CompletedTensorProduct.mapSpf_comp]
  refine mapSpf_congr R I hI ?_ ?_
  · norm_refl; exact AlgHom.comp_id _
  · norm_refl; exact AlgHom.id_comp _

@[reassoc]
theorem e1_YX (hI : I.FG) :
    (swapFirstSummandXXInv R I q hI).inv ≫ (swapSecondSummandXXInv R I q hI).hom =
      (bothSummandAntiInv R I q hI).inv := by
  simp only [swapFirstSummandXXInv, swapSecondSummandXXInv, bothSummandAntiInv, mapSpfIso_hom,
    mapSpfIso_inv]
  rw [← CompletedTensorProduct.mapSpf_comp]
  refine mapSpf_congr R I hI ?_ ?_
  · norm_refl; exact AlgHom.comp_id _
  · norm_refl; exact AlgHom.id_comp _

@[reassoc]
theorem e1_YY (hI : I.FG) :
    (swapFirstSummandXYInv R I q hI).inv ≫ (swapSecondSummandXXInv R I q hI).inv =
      (bothSummandDiagInv R I q hI).inv := by
  simp only [swapFirstSummandXYInv, swapSecondSummandXXInv, bothSummandDiagInv, mapSpfIso_inv]
  rw [← CompletedTensorProduct.mapSpf_comp]
  refine mapSpf_congr R I hI ?_ ?_
  · norm_refl; exact AlgHom.comp_id _
  · norm_refl; exact AlgHom.id_comp _

/-- **Klein e1: `both = swapFirst ≫ swapSecond`.** -/
theorem tateSelfProductBothTransitionInv_eq_swapFirst_swapSecond (hI : I.FG) :
    (tateSelfProductSwapFirstTransitionInv R I q hI).hom ≫
        (tateSelfProductSwapSecondTransitionInv R I q hI).hom =
      (tateSelfProductBothTransitionInv R I q hI).hom := by
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
    simp only [tateSelfProductSwapFirstTransitionInv, tateSelfProductSwapSecondTransitionInv,
      tateSelfProductBothTransitionInv, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc, e1_XX_assoc, e1_XY_assoc, e1_YX_assoc, e1_YY_assoc]

/-! ### `both = swapSecond ≫ swapFirst`, summand by summand -/

@[reassoc]
theorem e2_XX (hI : I.FG) :
    (swapSecondSummandXXInv R I q hI).hom ≫ (swapFirstSummandXYInv R I q hI).hom =
      (bothSummandDiagInv R I q hI).hom := by
  simp only [swapSecondSummandXXInv, swapFirstSummandXYInv, bothSummandDiagInv, mapSpfIso_hom]
  rw [← CompletedTensorProduct.mapSpf_comp]
  refine mapSpf_congr R I hI ?_ ?_
  · norm_refl; exact AlgHom.id_comp _
  · norm_refl; exact AlgHom.comp_id _

@[reassoc]
theorem e2_XY (hI : I.FG) :
    (swapSecondSummandXXInv R I q hI).inv ≫ (swapFirstSummandXXInv R I q hI).hom =
      (bothSummandAntiInv R I q hI).hom := by
  simp only [swapSecondSummandXXInv, swapFirstSummandXXInv, bothSummandAntiInv, mapSpfIso_hom,
    mapSpfIso_inv]
  rw [← CompletedTensorProduct.mapSpf_comp]
  refine mapSpf_congr R I hI ?_ ?_
  · norm_refl; exact AlgHom.id_comp _
  · norm_refl; exact AlgHom.comp_id _

@[reassoc]
theorem e2_YX (hI : I.FG) :
    (swapSecondSummandYXInv R I q hI).hom ≫ (swapFirstSummandXYInv R I q hI).inv =
      (bothSummandAntiInv R I q hI).inv := by
  simp only [swapSecondSummandYXInv, swapFirstSummandXYInv, bothSummandAntiInv, mapSpfIso_hom,
    mapSpfIso_inv]
  rw [← CompletedTensorProduct.mapSpf_comp]
  refine mapSpf_congr R I hI ?_ ?_
  · norm_refl; exact AlgHom.id_comp _
  · norm_refl; exact AlgHom.comp_id _

@[reassoc]
theorem e2_YY (hI : I.FG) :
    (swapSecondSummandYXInv R I q hI).inv ≫ (swapFirstSummandXXInv R I q hI).inv =
      (bothSummandDiagInv R I q hI).inv := by
  simp only [swapSecondSummandYXInv, swapFirstSummandXXInv, bothSummandDiagInv, mapSpfIso_inv]
  rw [← CompletedTensorProduct.mapSpf_comp]
  refine mapSpf_congr R I hI ?_ ?_
  · norm_refl; exact AlgHom.id_comp _
  · norm_refl; exact AlgHom.comp_id _

/-- **Klein e2: `both = swapSecond ≫ swapFirst`.** -/
theorem tateSelfProductBothTransitionInv_eq_swapSecond_swapFirst (hI : I.FG) :
    (tateSelfProductSwapSecondTransitionInv R I q hI).hom ≫
        (tateSelfProductSwapFirstTransitionInv R I q hI).hom =
      (tateSelfProductBothTransitionInv R I q hI).hom := by
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
    simp only [tateSelfProductSwapSecondTransitionInv, tateSelfProductSwapFirstTransitionInv,
      tateSelfProductBothTransitionInv, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc, e2_XX_assoc, e2_XY_assoc, e2_YX_assoc, e2_YY_assoc]

/-! ### The Klein four-group relations and the `σ`-triple identity -/

/-- `tateSelfProductSwapFirstTransitionInv` is an involution (its `Iso.inv` equals its `Iso.hom`).
-/
theorem swapFirstInv_hom_hom (hI : I.FG) :
    (tateSelfProductSwapFirstTransitionInv R I q hI).hom ≫
        (tateSelfProductSwapFirstTransitionInv R I q hI).hom = 𝟙 _ :=
  (tateSelfProductSwapFirstTransitionInv R I q hI).hom_inv_id

/-- `swapSecond` is an involution. -/
theorem swapSecondInv_hom_hom (hI : I.FG) :
    (tateSelfProductSwapSecondTransitionInv R I q hI).hom ≫
        (tateSelfProductSwapSecondTransitionInv R I q hI).hom = 𝟙 _ :=
  (tateSelfProductSwapSecondTransitionInv R I q hI).hom_inv_id

/-- `both` is an involution. -/
theorem bothInv_hom_hom (hI : I.FG) :
    (tateSelfProductBothTransitionInv R I q hI).hom ≫
        (tateSelfProductBothTransitionInv R I q hI).hom = 𝟙 _ :=
  (tateSelfProductBothTransitionInv R I q hI).hom_inv_id

/-- The three ordered triples starting with `both`, and the two starting with a swap followed by the
other swap, all compose to `𝟙`: any ordered product of the three distinct Klein elements is `𝟙`.
Abbreviations: `F`/`S`/`B` = `swapFirst`/`swapSecond`/`both` `.hom`. -/
private theorem klein_FSB (hI : I.FG) :
    (tateSelfProductSwapFirstTransitionInv R I q hI).hom ≫
        (tateSelfProductSwapSecondTransitionInv R I q hI).hom ≫
          (tateSelfProductBothTransitionInv R I q hI).hom = 𝟙 _ := by
  rw [← Category.assoc, tateSelfProductBothTransitionInv_eq_swapFirst_swapSecond]
  exact bothInv_hom_hom R I q hI

private theorem klein_SFB (hI : I.FG) :
    (tateSelfProductSwapSecondTransitionInv R I q hI).hom ≫
        (tateSelfProductSwapFirstTransitionInv R I q hI).hom ≫
          (tateSelfProductBothTransitionInv R I q hI).hom = 𝟙 _ := by
  rw [← Category.assoc, tateSelfProductBothTransitionInv_eq_swapSecond_swapFirst]
  exact bothInv_hom_hom R I q hI

private theorem klein_BFS (hI : I.FG) :
    (tateSelfProductBothTransitionInv R I q hI).hom ≫
        (tateSelfProductSwapFirstTransitionInv R I q hI).hom ≫
          (tateSelfProductSwapSecondTransitionInv R I q hI).hom = 𝟙 _ := by
  rw [tateSelfProductBothTransitionInv_eq_swapFirst_swapSecond]
  exact bothInv_hom_hom R I q hI

private theorem klein_BSF (hI : I.FG) :
    (tateSelfProductBothTransitionInv R I q hI).hom ≫
        (tateSelfProductSwapSecondTransitionInv R I q hI).hom ≫
          (tateSelfProductSwapFirstTransitionInv R I q hI).hom = 𝟙 _ := by
  rw [tateSelfProductBothTransitionInv_eq_swapSecond_swapFirst]
  exact bothInv_hom_hom R I q hI

private theorem klein_FBS (hI : I.FG) :
    (tateSelfProductSwapFirstTransitionInv R I q hI).hom ≫
        (tateSelfProductBothTransitionInv R I q hI).hom ≫
          (tateSelfProductSwapSecondTransitionInv R I q hI).hom = 𝟙 _ := by
  rw [← tateSelfProductBothTransitionInv_eq_swapFirst_swapSecond, Category.assoc,
    swapSecondInv_hom_hom, Category.comp_id]
  exact swapFirstInv_hom_hom R I q hI

private theorem klein_SBF (hI : I.FG) :
    (tateSelfProductSwapSecondTransitionInv R I q hI).hom ≫
        (tateSelfProductBothTransitionInv R I q hI).hom ≫
          (tateSelfProductSwapFirstTransitionInv R I q hI).hom = 𝟙 _ := by
  rw [← tateSelfProductBothTransitionInv_eq_swapSecond_swapFirst, Category.assoc,
    swapFirstInv_hom_hom, Category.comp_id]
  exact swapSecondInv_hom_hom R I q hI

/-- **The `σ`-triple identity (inversion).** For every pairwise-distinct triple `i j k` in
`Bool × Bool` the three summand permutations of the cyclic triple compose to the identity of the
both-overlap object. Each `tateSelfProductSigmaInv` reduces (by `Bool × Bool` case split) to one of
the three non-identity Klein elements `{swapFirst, swapSecond, both}`; the three that appear are
always distinct, and any ordered product of the three distinct Klein elements is the identity. -/
theorem tateSelfProductSigmaInv_triple (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (tateSelfProductSigmaInv R I q hI i j k hij hik hjk).hom ≫
        (tateSelfProductSigmaInv R I q hI j k i hjk hij.symm hik.symm).hom ≫
          (tateSelfProductSigmaInv R I q hI k i j hik.symm hjk.symm hij).hom =
      𝟙 _ := by
  obtain ⟨a, b⟩ := i; obtain ⟨c, d⟩ := j; obtain ⟨e, f⟩ := k
  revert hij hik hjk
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> intro hij hik hjk <;>
    first
      | exact absurd rfl hij
      | exact absurd rfl hik
      | exact absurd rfl hjk
      | (simp only [tateSelfProductSigmaInv]
         first
           | exact klein_FSB R I q hI | exact klein_SFB R I q hI | exact klein_BFS R I q hI
           | exact klein_BSF R I q hI | exact klein_FBS R I q hI | exact klein_SBF R I q hI)

/-! ### The `t_fac` field and the cocycle -/

/-- **The `t_fac` law of `tateSelfProductGlueTInv'`, for free** (`glueTPrimeOfLift_fac`). The
inversion analogue of `tateSelfProductGlueT_fac`; this is exactly the `GlueData'.t_fac` field. -/
theorem tateSelfProductGlueTInv_fac (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)] :
    tateSelfProductGlueTInv' R I q hI i j k hij hik hjk ≫
        pullback.snd (tateSelfProductGlueF R I q hI j k hjk)
          (tateSelfProductGlueF R I q hI j i hij.symm) =
      pullback.fst (tateSelfProductGlueF R I q hI i j hij)
          (tateSelfProductGlueF R I q hI i k hik) ≫
        tateSelfProductGlueTInv R I q hI i j hij :=
  glueTPrimeOfLift_fac (tateSelfProductGlueF R I q hI i j hij)
    (tateSelfProductGlueF R I q hI i k hik) (tateSelfProductGlueF R I q hI j k hjk)
    (tateSelfProductGlueF R I q hI j i hij.symm) (tateSelfProductGlueTInv R I q hI i j hij)
    (tateSelfProductGlueTInv'_range R I q hI i j k hij hik hjk)

/-- **The four-chart Tate self-product `GlueData'` cocycle (𝔾m-inversion model).** For every
pairwise-distinct triple `i j k : Bool × Bool` the three transitions-of-transitions of the cyclic
triple compose to the identity, matching the `GlueData'.cocycle` field. Obtained by conjugating to
the both-overlap object: the cyclic both-overlap isos telescope, `tateSelfProductD_eq_sigma_inv`
identifies each conjugated factor with a summand permutation, and `tateSelfProductSigmaInv_triple`
closes the `σ`-triple. The inversion analogue of `tateSelfProductGlueCocycle`. -/
theorem tateSelfProductGlueCocycleInv (hq : q ∈ I) (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j i hij.symm)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI k i hik.symm)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI k j hjk.symm)] :
    tateSelfProductGlueTInv' R I q hI i j k hij hik hjk ≫
        tateSelfProductGlueTInv' R I q hI j k i hjk hij.symm hik.symm ≫
          tateSelfProductGlueTInv' R I q hI k i j hik.symm hjk.symm hij =
      𝟙 _ := by
  haveI := isOpenImmersion_bothFactorOverlapChart R I q hq hI
  have hσ := tateSelfProductSigmaInv_triple R I q hI i j k hij hik hjk
  rw [← tateSelfProductD_eq_sigma_inv R I q hq hI i j k hij hik hjk,
    ← tateSelfProductD_eq_sigma_inv R I q hq hI j k i hjk hij.symm hik.symm,
    ← tateSelfProductD_eq_sigma_inv R I q hq hI k i j hik.symm hjk.symm hij,
    tateSelfProductDInv, tateSelfProductDInv, tateSelfProductDInv] at hσ
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hσ
  rw [Iso.hom_comp_eq_id] at hσ
  rw [← cancel_mono (tateSelfProductBothChartIso R I q hI i j k hij hik hjk).inv,
    Category.id_comp, Category.assoc, Category.assoc]
  exact hσ

end AlgebraicGeometry

end
