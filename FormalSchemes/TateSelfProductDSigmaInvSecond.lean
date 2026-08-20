import FormalSchemes.TateSelfProductDSigmaInvFirst

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The 𝔾m-inversion summand comparison: the second shape

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. Unlike the swap, the 𝔾m inversion has **no `A`-algebra automorphism** (`rlsInv` is
`R`-linear, `X ↦ X⁻¹`), so the swap route through a common endomorphism `mapSpf hI (A-endo)
(A-endo)` of `Spf(A ⊗̂ A)` does not exist. The summand permutation is instead compared with
`tateSelfProductDInv` one *shape* at a time — first-factor, second-factor, both-factor — each shape
collapsing both sides, via `mapSpf_comp` and the `interchange…_eq_mapSpf` family, to `mapSpf hI u v`
for the same `annulusFibreChartTransitionInvAlg`-composite.

This file carries the **second-factor** shape lemma; the first is in
`FormalSchemes.TateSelfProductDSigmaInvFirst`.

**Why this is its own file.** Layers 1–6 of the inversion scaffold were a single module until
they no longer fit in memory: elaborating them together peaked above 17.8 GB of resident memory and
was OOM-killed on a shared box, and even layer 6 alone still peaked at 12.3 GB. The shape lemmas are
therefore one per file. No statement is changed — the declarations below are verbatim what they
were, in the same order and namespace. The only edit is that the ones a later file consumes are no
longer `private`, since `private` does not cross a module boundary; they remain internal by
convention and nothing outside this group should use them.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* Mathlib `CategoryTheory.GlueData'` (the `t'`/`t_fac`/`cocycle` fields).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorAwayInterchange CompletedTensorProduct
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- **Second shape (inversion).** The second-factor analogue of `firstShapeDInv`. -/
theorem secondShapeDInv (hq : q ∈ I) (hI : I.FG)
    (p : ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶ (dAX R I q ⨿ dAY R I q))
    (hp : p ≫ secondFactorOverlapChart R I q hI = bothFactorOverlapChart R I q hI) :
    p ≫ (tateSelfProductRightTransitionInv R I q hI).hom ≫ secondFactorOverlapChart R I q hI =
      (tateSelfProductSwapSecondTransitionInv R I q hI).hom ≫ bothFactorOverlapChart R I q hI := by
  haveI := isOpenImmersion_secondFactorOverlapChart R I q hq hI
  have hp_eq : p =
      coprod.desc
        (coprod.desc
          (CompletedTensorProduct.mapSpf hI (locXInv R I q) (AlgHom.id R (awXInv R I q)) ≫
            coprod.inl)
          (CompletedTensorProduct.mapSpf hI (locXInv R I q) (AlgHom.id R (awYInv R I q)) ≫
            coprod.inr))
        (coprod.desc
          (CompletedTensorProduct.mapSpf hI (locYInv R I q) (AlgHom.id R (awXInv R I q)) ≫
            coprod.inl)
          (CompletedTensorProduct.mapSpf hI (locYInv R I q) (AlgHom.id R (awYInv R I q)) ≫
            coprod.inr)) := by
    rw [← cancel_mono (secondFactorOverlapChart R I q hI), hp]
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
    · simp only [bothFactorOverlapChart, secondFactorOverlapChart, coprod.inl_desc,
        coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
      rw [bothInterchangeOpenImmersion_eq_mapSpf, rightInterchangeOpenImmersion_eq_mapSpf,
        ← CompletedTensorProduct.mapSpf_comp]
      exact mapSpf_congr R I hI (by ext a; simp) (by ext a; simp)
  rw [hp_eq]
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_)
  · simp only [coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      Category.assoc, tateSelfProductRightTransitionInv, tateSelfProductSwapSecondTransitionInv,
      secondFactorOverlapChart, bothFactorOverlapChart]
    rw [rightSummandInv, mapSpfIso_hom, swapSecondSummandXXInv, mapSpfIso_hom,
      rightInterchangeOpenImmersion_eq_mapSpf, bothInterchangeOpenImmersion_eq_mapSpf,
      ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (by ext a; simp) (by ext a; simp)
  · simp only [coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      Category.assoc, tateSelfProductRightTransitionInv, tateSelfProductSwapSecondTransitionInv,
      secondFactorOverlapChart, bothFactorOverlapChart]
    rw [rightSummandInv, mapSpfIso_inv, swapSecondSummandXXInv, mapSpfIso_inv,
      rightInterchangeOpenImmersion_eq_mapSpf, bothInterchangeOpenImmersion_eq_mapSpf,
      ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (by ext a; simp) (by ext a; simp)
  · simp only [coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      Category.assoc, tateSelfProductRightTransitionInv, tateSelfProductSwapSecondTransitionInv,
      secondFactorOverlapChart, bothFactorOverlapChart]
    rw [rightSummandInv, mapSpfIso_hom, swapSecondSummandYXInv, mapSpfIso_hom,
      rightInterchangeOpenImmersion_eq_mapSpf, bothInterchangeOpenImmersion_eq_mapSpf,
      ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (by ext a; simp) (by ext a; simp)
  · simp only [coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      Category.assoc, tateSelfProductRightTransitionInv, tateSelfProductSwapSecondTransitionInv,
      secondFactorOverlapChart, bothFactorOverlapChart]
    rw [rightSummandInv, mapSpfIso_inv, swapSecondSummandYXInv, mapSpfIso_inv,
      rightInterchangeOpenImmersion_eq_mapSpf, bothInterchangeOpenImmersion_eq_mapSpf,
      ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (by ext a; simp) (by ext a; simp)

end AlgebraicGeometry

end
