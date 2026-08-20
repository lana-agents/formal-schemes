import FormalSchemes.TateSelfProductSigmaInv

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The 𝔾m-inversion summand comparison: the first shape

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. Unlike the swap, the 𝔾m inversion has **no `A`-algebra automorphism** (`rlsInv` is
`R`-linear, `X ↦ X⁻¹`), so the swap route through a common endomorphism `mapSpf hI (A-endo)
(A-endo)` of `Spf(A ⊗̂ A)` does not exist. The summand permutation is instead compared with
`tateSelfProductDInv` one *shape* at a time — first-factor, second-factor, both-factor — each shape
collapsing both sides, via `mapSpf_comp` and the `interchange…_eq_mapSpf` family, to `mapSpf hI u v`
for the same `annulusFibreChartTransitionInvAlg`-composite.

This file carries the shared abbreviations and the **first-factor** shape lemma.

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

/-! ### Layer 6: the direct summand-comparison identification `tateSelfProductD_eq_sigma_inv`

Unlike the swap, the 𝔾m inversion has no `A`-algebra automorphism, so the swap route through a
common endomorphism `mapSpf hI (A-endo) (A-endo)` of `Spf(A ⊗̂ A)` does not exist. We compare the
two sides directly, summand by summand: on each summand both `tateSelfProductDInv i j k ≫ bothChart`
and `(tateSelfProductSigmaInv i j k).hom ≫ bothChart` collapse — via `mapSpf_comp` and the
`interchange…_eq_mapSpf` family — to `mapSpf hI u v` for the *same* `R`-algebra composites. -/

/-- `A{1/x}` over the `I.map (algebraMap R A)` ideal convention the interchange charts use. -/
abbrev awXInv : Type u :=
  awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)

/-- `A{1/y}` over the `I.map (algebraMap R A)` ideal convention. -/
abbrev awYInv : Type u :=
  awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)

/-- The localization `R`-algebra map `A →ₐ A{1/x}`. -/
abbrev locXInv : annulusAlgebra R I q →ₐ[R] awXInv R I q :=
  IsScalarTower.toAlgHom R (annulusAlgebra R I q)
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))

/-- The localization `R`-algebra map `A →ₐ A{1/y}`. -/
abbrev locYInv : annulusAlgebra R I q →ₐ[R] awYInv R I q :=
  IsScalarTower.toAlgHom R (annulusAlgebra R I q)
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))

/-- `mapSpf` depends only on the two `R`-algebra maps (local copy of the `mapSpf_congr` idiom). -/
theorem mapSpf_congr {A₀ B₀ A₁ B₁ : Type u} [CommRing A₀] [CommRing B₀] [CommRing A₁]
    [CommRing B₁] [Algebra R A₀] [Algebra R B₀] [Algebra R A₁] [Algebra R B₁] (hI : I.FG)
    {f₁ f₂ : A₀ →ₐ[R] A₁} {g₁ g₂ : B₀ →ₐ[R] B₁} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    CompletedTensorProduct.mapSpf hI f₁ g₁ = CompletedTensorProduct.mapSpf hI f₂ g₂ := by
  subst hf hg; rfl

/-- **First shape (inversion).** For a prefix `p` cut out over the first-factor overlap chart
(`p ≫ firstFactorOverlapChart = bothFactorOverlapChart`), the first-factor inversion transition
followed by the return chart matches the swap-first permutation followed by the both-chart. Each
summand is pinned by `cancel_mono` and both sides collapse to the same `mapSpf`. -/
/-- **The prefix is pinned by its composite with the first-factor overlap chart.** Extracted from
`firstShapeDInv`, whose proof it opened with as a `have`. It is a separate declaration purely for
memory: elaborating it together with the four summand comparisons below holds all eight heavy
branches in one declaration, which is what pushed the module past the box's limit. The statement
and proof are verbatim what they were as a `have`. -/
theorem firstShapePrefix (hq : q ∈ I) (hI : I.FG)
    (p : ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶ (dXA R I q ⨿ dYA R I q))
    (hp : p ≫ firstFactorOverlapChart R I q hI = bothFactorOverlapChart R I q hI) :
    p =
      coprod.desc
        (coprod.desc
          (CompletedTensorProduct.mapSpf hI (AlgHom.id R (awXInv R I q)) (locXInv R I q) ≫
            coprod.inl)
          (CompletedTensorProduct.mapSpf hI (AlgHom.id R (awXInv R I q)) (locYInv R I q) ≫
            coprod.inl))
        (coprod.desc
          (CompletedTensorProduct.mapSpf hI (AlgHom.id R (awYInv R I q)) (locXInv R I q) ≫
            coprod.inr)
          (CompletedTensorProduct.mapSpf hI (AlgHom.id R (awYInv R I q)) (locYInv R I q) ≫
            coprod.inr)) := by
  haveI := isOpenImmersion_firstFactorOverlapChart R I q hq hI
  rw [← cancel_mono (firstFactorOverlapChart R I q hI), hp]
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
  · simp only [bothFactorOverlapChart, firstFactorOverlapChart, coprod.inl_desc,
      coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    rw [bothInterchangeOpenImmersion_eq_mapSpf, interchangeOpenImmersion_eq_mapSpf,
      ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (by ext a; simp) (by ext a; simp)

theorem firstShapeDInv (hq : q ∈ I) (hI : I.FG)
    (p : ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶ (dXA R I q ⨿ dYA R I q))
    (hp : p ≫ firstFactorOverlapChart R I q hI = bothFactorOverlapChart R I q hI) :
    p ≫ (tateSelfProductFirstTransitionInv R I q hI).hom ≫ firstFactorOverlapChart R I q hI =
      (tateSelfProductSwapFirstTransitionInv R I q hI).hom ≫ bothFactorOverlapChart R I q hI := by
  rw [firstShapePrefix R I q hq hI p hp]
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_)
  · simp only [coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      Category.assoc, tateSelfProductFirstTransitionInv, tateSelfProductSwapFirstTransitionInv,
      firstFactorOverlapChart, bothFactorOverlapChart]
    rw [firstSummandInv, twoPatchFibreProductInvTransition, mapSpfIso_hom,
      swapFirstSummandXXInv, mapSpfIso_hom, interchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (by ext a; simp) (by ext a; simp)
  · simp only [coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      Category.assoc, tateSelfProductFirstTransitionInv, tateSelfProductSwapFirstTransitionInv,
      firstFactorOverlapChart, bothFactorOverlapChart]
    rw [firstSummandInv, twoPatchFibreProductInvTransition, mapSpfIso_hom,
      swapFirstSummandXYInv, mapSpfIso_hom, interchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (by ext a; simp) (by ext a; simp)
  · simp only [coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      Category.assoc, tateSelfProductFirstTransitionInv, tateSelfProductSwapFirstTransitionInv,
      firstFactorOverlapChart, bothFactorOverlapChart]
    rw [firstSummandInv, twoPatchFibreProductInvTransition, mapSpfIso_inv,
      swapFirstSummandXXInv, mapSpfIso_inv, interchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (by ext a; simp) (by ext a; simp)
  · simp only [coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      Category.assoc, tateSelfProductFirstTransitionInv, tateSelfProductSwapFirstTransitionInv,
      firstFactorOverlapChart, bothFactorOverlapChart]
    rw [firstSummandInv, twoPatchFibreProductInvTransition, mapSpfIso_inv,
      swapFirstSummandXYInv, mapSpfIso_inv, interchangeOpenImmersion_eq_mapSpf,
      bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
      ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp]
    exact mapSpf_congr R I hI (by ext a; simp) (by ext a; simp)

end AlgebraicGeometry

end
