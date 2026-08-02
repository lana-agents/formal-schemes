import FormalSchemes.TateSelfProductTPrimeSummandIdentify
import FormalSchemes.TateSelfProductSummandNaturality

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Naturality of the swap involutions against the both-overlap chart (Family A)

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q` and
`C = A ⊗̂_R A`. The summand-permutation scaffold `TateSelfProductTPrimeSummandIdentify` introduces
the two new self-involutions of the both-overlap object
`bothOverlapObj = (dXX ⨿ dXY) ⨿ (dYX ⨿ dYY)`:

* `tateSelfProductSwapFirstTransition` — the first-coordinate swap (`dXX ↔ dYX`, `dXY ↔ dYY`), the
  summand-permutation form of `tateSelfProductD i j k` for chart pairs `(i, j)` differing only in
  the first coordinate;
* `tateSelfProductSwapSecondTransition` — the second-coordinate swap (`dXX ↔ dXY`, `dYX ↔ dYY`),
  the form for pairs differing only in the second coordinate.

This file records the **morphism-level naturality** of both swaps against the both-factor overlap
chart `bothFactorOverlapChart`, landing in `Spf C`:

* `tateSelfProductSwapFirstTransition_naturality`:
  `swapFirst.hom ≫ bothChart = bothChart ≫ mapSpf hI flip id`;
* `tateSelfProductSwapSecondTransition_naturality`:
  `swapSecond.hom ≫ bothChart = bothChart ≫ mapSpf hI id flip`,

where `flip = annulusFlip R I q hI : A ≃ₐ[R] A` is the coordinate-swap involution. These mirror the
transition-through-chart squares of `TateSelfProductSummandNaturality` (Family B) for the three
*original* transitions; together with those and the both-overlap iso leg law
`tateSelfProductBothChartIso_hom_fst_comp`, they are exactly the summand-level input the step-3
identification `tateSelfProductD i j k = (tateSelfProductSigma i j k).hom` (issue 335 / brick c3a)
consumes: the reduced goal `σ.hom ≫ bothChart = p ≫ t i j ≫ f j i` closes shape-by-shape by
rewriting `t i j ≫ f j i` with Family B and `σ.hom ≫ bothChart` with these two squares, both sides
becoming `bothChart ≫ mapSpf(flip-combination)`.

The reduction is pure `mapSpf` functoriality: each swap per-summand map is `mapSpfIso` of the
annulus chart transition on the swapped tensor factor and the identity on the other, every
both-overlap chart is `mapSpf` of a pair of localizations
(`bothInterchangeOpenImmersion_eq_mapSpf`), so each per-summand square collapses via `mapSpf_comp`
to the crux algebra-map identity `annulusFibreChartTransitionAlg_algebraMap` (the chart transition
is the completed localization of the coordinate swap) on the touched factor and a trivial
`refl`/`id` identity on the untouched factor.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The AlgHom-composite forms of the crux and the `mapSpf` congruence

These re-derive, from the *public* crux `annulusFibreChartTransitionAlg_algebraMap` and its `symm`
variant (`TateSelfProductSummandNaturality`), the `AlgHom.comp` identities the per-summand squares
need. They mirror the `private` helpers of Family B (which are not exported). -/

/-- The localization `R`-algebra map `A →ₐ[R] A{1/f}`. -/
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

/-! ### The two swap naturality squares -/

/-- **Swap-first naturality.** The first-coordinate swap involution of the both-overlap object,
composed with the both-factor overlap chart into `Spf(A ⊗̂_R A)`, is `mapSpf` of the coordinate swap
on the first tensor factor (the second factor untouched). -/
theorem tateSelfProductSwapFirstTransition_naturality (hI : I.FG) :
    (tateSelfProductSwapFirstTransition R I q hI).hom ≫ bothFactorOverlapChart R I q hI =
      bothFactorOverlapChart R I q hI ≫
        CompletedTensorProduct.mapSpf hI (annulusFlip R I q hI).toAlgHom
          (AlgHom.id R (annulusAlgebra R I q)) := by
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_)
  · simp only [tateSelfProductSwapFirstTransition, bothFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inr_desc, coprod.inl_desc, Category.assoc]
    rw [swapFirstSummandXX, mapSpfIso_hom, bothInterchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (chartTrans_symm_comp_locY R I q hI) (by ext a; simp)
  · simp only [tateSelfProductSwapFirstTransition, bothFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inr_desc, coprod.inr_desc_assoc, Category.assoc]
    rw [swapFirstSummandXY, mapSpfIso_hom, bothInterchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (chartTrans_symm_comp_locY R I q hI) (by ext a; simp)
  · simp only [tateSelfProductSwapFirstTransition, bothFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inl_desc, coprod.inr_desc_assoc, Category.assoc]
    rw [swapFirstSummandXX, mapSpfIso_inv, bothInterchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (chartTrans_comp_locX R I q hI) (by ext a; simp)
  · simp only [tateSelfProductSwapFirstTransition, bothFactorOverlapChart,
      coprod.inr_desc, coprod.inl_desc, coprod.inr_desc_assoc, Category.assoc]
    rw [swapFirstSummandXY, mapSpfIso_inv, bothInterchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (chartTrans_comp_locX R I q hI) (by ext a; simp)

/-- **Swap-second naturality.** The second-coordinate swap involution of the both-overlap object,
composed with the both-factor overlap chart into `Spf(A ⊗̂_R A)`, is `mapSpf` of the coordinate swap
on the second tensor factor (the first factor untouched). -/
theorem tateSelfProductSwapSecondTransition_naturality (hI : I.FG) :
    (tateSelfProductSwapSecondTransition R I q hI).hom ≫ bothFactorOverlapChart R I q hI =
      bothFactorOverlapChart R I q hI ≫
        CompletedTensorProduct.mapSpf hI (AlgHom.id R (annulusAlgebra R I q))
          (annulusFlip R I q hI).toAlgHom := by
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_)
  · simp only [tateSelfProductSwapSecondTransition, bothFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inr_desc, coprod.inl_desc, Category.assoc]
    rw [swapSecondSummandXX, mapSpfIso_hom, bothInterchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (by ext a; simp) (chartTrans_symm_comp_locY R I q hI)
  · simp only [tateSelfProductSwapSecondTransition, bothFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inl_desc, coprod.inr_desc_assoc, Category.assoc]
    rw [swapSecondSummandXX, mapSpfIso_inv, bothInterchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (by ext a; simp) (chartTrans_comp_locX R I q hI)
  · simp only [tateSelfProductSwapSecondTransition, bothFactorOverlapChart, coprod.inl_desc_assoc,
      coprod.inr_desc, coprod.inr_desc_assoc, Category.assoc]
    rw [swapSecondSummandYX, mapSpfIso_hom, bothInterchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (by ext a; simp) (chartTrans_symm_comp_locY R I q hI)
  · simp only [tateSelfProductSwapSecondTransition, bothFactorOverlapChart,
      coprod.inr_desc, coprod.inl_desc, coprod.inr_desc_assoc, Category.assoc]
    rw [swapSecondSummandYX, mapSpfIso_inv, bothInterchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (by ext a; simp) (chartTrans_comp_locX R I q hI)

end AlgebraicGeometry

end
