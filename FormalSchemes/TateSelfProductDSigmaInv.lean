import FormalSchemes.TateSelfProductTransitionInv
import FormalSchemes.TateSelfProductTPrimeSummandIdentify
import FormalSchemes.CompletedTensorAwayInterchangeMixedPullback
import FormalSchemes.CompletedTensorAwayInterchangeBothPullback

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The 𝔾m-inversion self-product cocycle payload `tateSelfProductD_eq_sigma_inv`

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. This file is the 𝔾m-**inversion** (issue 450 / 442d) analogue of
`TateSelfProductDSigma`, delivering the `GlueData'` cocycle payload

`tateSelfProductD_eq_sigma_inv : tateSelfProductDInv i j k = (tateSelfProductSigmaInv i j k).hom`

for the corrected (separated, inversion) Tate self-fibre-product `𝔈_q ×_{Spf R} 𝔈_q`.

Layers 1–5 are byte-for-byte mirrors of the swap scaffold with the swap transitions
(`tateSelfProduct*Transition`) replaced by the 𝔾m-inversion transitions
(`tateSelfProduct*TransitionInv`, on master in `TateSelfProductTransitionInv`); every
model-independent declaration (`tateSelfProductGlueV`/`GlueF`, `tateSelfProductBothChartIso` and its
leg laws, the range-saturation helpers, `glueTPrimeOfLift`) is reused verbatim.

Layer 6 is genuinely new: unlike the swap, the 𝔾m inversion has **no `A`-algebra automorphism**
(`rlsInv` is `R`-linear, `X ↦ X⁻¹`), so the swap route through a common endomorphism
`mapSpf hI (A-endo) (A-endo)` of `Spf(A ⊗̂ A)` does **not** exist. The identification is proved by
direct summand comparison: both `tateSelfProductDInv i j k ≫ bothChart` and
`(tateSelfProductSigmaInv i j k).hom ≫ bothChart`, restricted to each of the four summands, collapse
via `mapSpf_comp` / `interchangeOpenImmersion_eq_mapSpf` (and siblings) to `mapSpf hI u v` for the
*same* `annulusFibreChartTransitionInvAlg`-composite.

## Build cost — do not inline the leg lemmas back into the shape lemmas (issue 636)

This module used to be the most expensive file in the project: it needed **more than 19 GB** of
resident memory and was OOM-killed (`Lean exited with code 137`, no Lean diagnostic) on any
contended box, which made *every* pull request in this repository unmergeable at random.

The cost was **not** elaboration — the whole file elaborates in about two minutes and 3.5 GB — but
**kernel type-checking**, which Lean 4.32 performs in asynchronous tasks that
`set_option profiler true` does not attribute to any command. `set_option debug.skipKernelTC true`
is the diagnostic that finds this class of problem; the profiler cannot.

All of it sat in **one declaration**: layer 6's `firstShapeDInv`, on its own, needed 16.2 GB.
It compared composites of `mapSpf`s *at the concrete completion tower* and closed each of its eight
branches with `mapSpf_congr … (by ext a; simp) (by ext a; simp)`. Those `AlgHom` identities are
pure `AlgHom.id_comp`/`comp_id`/`AlgEquiv.refl` bookkeeping — there is no annulus mathematics in
them — but performing that bookkeeping at `awayCompletion … ⊗̂ awayCompletion …` forces the kernel
to `whnf` the whole nested `AdicCompletion`/`CompletedTensorProduct` tower.

The fix, and the rule to preserve: **do the `mapSpf` bookkeeping at abstract types and then
instantiate.**
`legFirstShape`/`legSecondShape` below state it with four *variable* algebras; the eight concrete
`…Leg…` lemmas are `coprod`-free and end in a single `exact legFirstShape …`; the shape lemmas do
nothing but `coprod.hom_ext` and dispatch. After the restructuring the whole module builds in
**221 s at 3.6 GB** under `lake build`.

A file split does **not** substitute for this: the cost is one declaration, so no partition into
modules or declarations reaches below it. Measured, twice. Conversely, re-inlining any leg lemma
into its shape lemma restores the 16 GB — measure under `lake build` (not `lake env lean`, which
succeeds on trees that `lake build` then OOM-kills) before changing anything here.

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

/-! ### Layer 1: the 𝔾m-inversion transition datum `t_inv` and its self-inverse law -/

/-- **The 𝔾m-inversion overlap transitions** `t_inv i j h : V i j h ⟶ V j i h.symm` of the
four-chart Tate self-fibre-product glue: the `hom` leg of the first-, second- or both-factor
inversion transition of `TateSelfProductTransitionInv` according to the difference type of `i` and
`j`. The inversion analogue of `tateSelfProductGlueT`; reuses the model-independent overlap objects
`tateSelfProductGlueV`. -/
def tateSelfProductGlueTInv (hI : I.FG) :
    ∀ (i j : Bool × Bool) (h : i ≠ j),
      tateSelfProductGlueV R I q hI i j h ⟶ tateSelfProductGlueV R I q hI j i h.symm :=
  fun i j h => match i, j, h with
  | (false, false), (false, false), h => (h rfl).elim
  | (false, false), (false, true), _ => (tateSelfProductRightTransitionInv R I q hI).hom
  | (false, false), (true, false), _ => (tateSelfProductFirstTransitionInv R I q hI).hom
  | (false, false), (true, true), _ => (tateSelfProductBothTransitionInv R I q hI).hom
  | (false, true), (false, false), _ => (tateSelfProductRightTransitionInv R I q hI).hom
  | (false, true), (false, true), h => (h rfl).elim
  | (false, true), (true, false), _ => (tateSelfProductBothTransitionInv R I q hI).hom
  | (false, true), (true, true), _ => (tateSelfProductFirstTransitionInv R I q hI).hom
  | (true, false), (false, false), _ => (tateSelfProductFirstTransitionInv R I q hI).hom
  | (true, false), (false, true), _ => (tateSelfProductBothTransitionInv R I q hI).hom
  | (true, false), (true, false), h => (h rfl).elim
  | (true, false), (true, true), _ => (tateSelfProductRightTransitionInv R I q hI).hom
  | (true, true), (false, false), _ => (tateSelfProductBothTransitionInv R I q hI).hom
  | (true, true), (false, true), _ => (tateSelfProductFirstTransitionInv R I q hI).hom
  | (true, true), (true, false), _ => (tateSelfProductRightTransitionInv R I q hI).hom
  | (true, true), (true, true), h => (h rfl).elim

/-- **`t_inv` is its own inverse:** `t_inv i j h ≫ t_inv j i h.symm = 𝟙`. Each case is
`Iso.hom_inv_id` of the corresponding inversion transition (whose `hom` and `inv` legs coincide).
The inversion analogue of `tateSelfProductGlueT_inv`. -/
theorem tateSelfProductGlueTInv_inv (hI : I.FG) :
    ∀ (i j : Bool × Bool) (h : i ≠ j),
      tateSelfProductGlueTInv R I q hI i j h ≫
        tateSelfProductGlueTInv R I q hI j i h.symm = 𝟙 _ := by
  rintro ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ h <;>
    first
    | exact absurd rfl h
    | exact (tateSelfProductFirstTransitionInv R I q hI).hom_inv_id
    | exact (tateSelfProductRightTransitionInv R I q hI).hom_inv_id
    | exact (tateSelfProductBothTransitionInv R I q hI).hom_inv_id

/-! ### Layer 2: the range inclusion `H` for the inversion transitions

The inversion transitions have the same per-factor `refl` shape as the swap ones
(`firstSummandInv = mapSpfIso _ (refl A)`, `rightSummandInv = mapSpfIso (refl A) _`), so the
projection-naturality proofs transfer mechanically. Only the transition-dependent lemmas are
re-derived; the set-theoretic saturation helpers are reused verbatim. -/

/-- **First-factor inversion transition naturality over the second projection**, base-changed form.
The inversion analogue of `twoPatchFibreProduct_pr₂_naturality`; identical proof with
`annulusFibreChartTransitionInvAlg` in place of `annulusFibreChartTransitionAlg`. -/
theorem twoPatchFibreProduct_pr₂_naturality_inv (B : Type u) [CommRing B] [Algebra R B]
    (hI : I.FG) :
    interchangeOpenImmersion (B := B) I (overlapX R I q) hI ≫
        pr₂Chart R I B (annulusAlgebra R I q) =
      (twoPatchFibreProductInvTransition R I q B hI).hom ≫
        interchangeOpenImmersion (B := B) I (overlapY R I q) hI ≫
          pr₂Chart R I B (annulusAlgebra R I q) := by
  simp only [pr₂Chart]
  rw [interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr I (overlapX R I q) hI,
    interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr I (overlapY R I q) hI,
    twoPatchFibreProductInvTransition, mapSpfIso_hom,
    mapSpf_comp_inrMap hI (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom
      (AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom]
  have hg : (((AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom : B →ₐ[R] B)).toRingHom =
      RingHom.id B := by
    ext b; simp
  rw [FormalSpectrum.locallyRingedSpaceMap_congr (φ₂ := RingHom.id B)
      (h₂ := (Ideal.comap_id (I.map (algebraMap R B))).ge) (hφ := hg),
    FormalSpectrum.locallyRingedSpaceMap_id, Category.comp_id]

/-- The reverse (`y`-side) form of `twoPatchFibreProduct_pr₂_naturality_inv`. -/
theorem twoPatchFibreProduct_pr₂_naturality_inv' (B : Type u) [CommRing B] [Algebra R B]
    (hI : I.FG) :
    interchangeOpenImmersion (B := B) I (overlapY R I q) hI ≫
        pr₂Chart R I B (annulusAlgebra R I q) =
      (twoPatchFibreProductInvTransition R I q B hI).inv ≫
        interchangeOpenImmersion (B := B) I (overlapX R I q) hI ≫
          pr₂Chart R I B (annulusAlgebra R I q) := by
  rw [twoPatchFibreProduct_pr₂_naturality_inv R I q B hI, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- **The first-factor inversion transition is a morphism over the second projection.** The
inversion analogue of `firstTransition_comp_secondProj`. -/
theorem firstTransitionInv_comp_secondProj (hI : I.FG) :
    (tateSelfProductFirstTransitionInv R I q hI).hom ≫
        firstFactorOverlapChart R I q hI ≫
          pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) =
      firstFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) := by
  refine coprod.hom_ext ?_ ?_
  · simp only [tateSelfProductFirstTransitionInv, firstFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact (twoPatchFibreProduct_pr₂_naturality_inv R I q (annulusAlgebra R I q) hI).symm
  · simp only [tateSelfProductFirstTransitionInv, firstFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact (twoPatchFibreProduct_pr₂_naturality_inv' R I q (annulusAlgebra R I q) hI).symm

/-- **First shape (inversion).** The inversion analogue of
`tateSelfProductFirstTransition_image_subset`. -/
theorem tateSelfProductFirstTransitionInv_image_subset (hI : I.FG) :
    (tateSelfProductFirstTransitionInv R I q hI).hom.base ''
        (⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (secondFactorOverlapChart R I q hI).base) ⊆
      ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (bothFactorOverlapChart R I q hI).base := by
  rw [range_bothFactorOverlapChart_eq_inter_first_second R I q hI, Set.preimage_inter,
    Set.preimage_range, Set.univ_inter, secondFactorOverlapChart_range_eq_preimage R I q hI,
    ← Set.preimage_comp]
  apply image_preimage_subset_of_comp_eq
  have h1 : ⇑((tateSelfProductFirstTransitionInv R I q hI).hom ≫
        firstFactorOverlapChart R I q hI ≫
          pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q)).base =
      ⇑(firstFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q)).base := by
    rw [firstTransitionInv_comp_secondProj R I q hI]
  simpa only [LocallyRingedSpace.comp_base, TopCat.coe_comp] using h1

/-- **Both shape (inversion).** The inversion analogue of
`tateSelfProductBothTransition_image_subset`; the transition never enters (target region is `univ`).
-/
theorem tateSelfProductBothTransitionInv_image_subset (hI : I.FG) :
    (tateSelfProductBothTransitionInv R I q hI).hom.base ''
        (⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (firstFactorOverlapChart R I q hI).base) ⊆
      ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (secondFactorOverlapChart R I q hI).base := by
  have huniv : ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
      Set.range (secondFactorOverlapChart R I q hI).base = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    exact fun y =>
      range_bothFactorOverlapChart_subset_second R I q hI (Set.mem_range_self y)
  rw [huniv]
  exact Set.subset_univ _

/-- **Second-factor inversion transition naturality over the first projection**, per-summand form.
The inversion analogue of `rightInterchange_pr₁_naturality`. -/
theorem rightInterchange_pr₁_naturality_inv (hI : I.FG) :
    rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI ≫
        pr₁ChartSelf R I q =
      (CompletedTensorProduct.mapSpfIso hI (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q))
          (annulusFibreChartTransitionInvAlg R I q hI)).hom ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI ≫
          pr₁ChartSelf R I q := by
  simp only [pr₁ChartSelf]
  rw [rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inl
      (A := annulusAlgebra R I q) I (overlapX R I q) hI,
    rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inl
      (A := annulusAlgebra R I q) I (overlapY R I q) hI,
    CompletedTensorProduct.mapSpfIso_hom,
    CompletedTensorProduct.mapSpf_comp_inlMap hI
      (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom
      (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom]
  have hf : (((AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom :
        annulusAlgebra R I q →ₐ[R] annulusAlgebra R I q)).toRingHom =
      RingHom.id (annulusAlgebra R I q) := by
    ext a; simp
  rw [FormalSpectrum.locallyRingedSpaceMap_congr (φ₂ := RingHom.id (annulusAlgebra R I q))
      (h₂ := (Ideal.comap_id (I.map (algebraMap R (annulusAlgebra R I q)))).ge) (hφ := hf),
    FormalSpectrum.locallyRingedSpaceMap_id, Category.comp_id]

/-- The reverse (`y`-side) form of `rightInterchange_pr₁_naturality_inv`. -/
theorem rightInterchange_pr₁_naturality_inv' (hI : I.FG) :
    rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI ≫
        pr₁ChartSelf R I q =
      (CompletedTensorProduct.mapSpfIso hI (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q))
          (annulusFibreChartTransitionInvAlg R I q hI)).inv ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI ≫
          pr₁ChartSelf R I q := by
  rw [rightInterchange_pr₁_naturality_inv R I q hI, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- **The second-factor inversion transition is a morphism over the first projection.** The
inversion analogue of `rightTransition_comp_firstProj`. -/
theorem rightTransitionInv_comp_firstProj (hI : I.FG) :
    (tateSelfProductRightTransitionInv R I q hI).hom ≫
        secondFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q =
      secondFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q := by
  refine coprod.hom_ext ?_ ?_
  · simp only [tateSelfProductRightTransitionInv, secondFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact (rightInterchange_pr₁_naturality_inv R I q hI).symm
  · simp only [tateSelfProductRightTransitionInv, secondFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact (rightInterchange_pr₁_naturality_inv' R I q hI).symm

/-- **Right shape (inversion).** The inversion analogue of
`tateSelfProductRightTransition_image_subset`. -/
theorem tateSelfProductRightTransitionInv_image_subset (hI : I.FG) :
    (tateSelfProductRightTransitionInv R I q hI).hom.base ''
        (⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (firstFactorOverlapChart R I q hI).base) ⊆
      ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (bothFactorOverlapChart R I q hI).base := by
  rw [range_bothFactorOverlapChart_eq_inter_first_second R I q hI, Set.preimage_inter,
    Set.preimage_range, Set.inter_univ, firstFactorOverlapChart_range_eq_preimage R I q hI,
    ← Set.preimage_comp]
  apply image_preimage_subset_of_comp_eq
  have h1 : ⇑((tateSelfProductRightTransitionInv R I q hI).hom ≫
        secondFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q).base =
      ⇑(secondFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q).base := by
    rw [rightTransitionInv_comp_firstProj R I q hI]
  simpa only [LocallyRingedSpace.comp_base, TopCat.coe_comp] using h1

/-- **First shape, swapped ordering (inversion).** Analogue of
`tateSelfProductFirstTransition_image_subset'`. -/
theorem tateSelfProductFirstTransitionInv_image_subset' (hI : I.FG) :
    (tateSelfProductFirstTransitionInv R I q hI).hom.base ''
        (⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (bothFactorOverlapChart R I q hI).base) ⊆
      ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (secondFactorOverlapChart R I q hI).base := by
  have hset : ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (bothFactorOverlapChart R I q hI).base =
      ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (secondFactorOverlapChart R I q hI).base := by
    rw [range_bothFactorOverlapChart_eq_inter_first_second R I q hI, Set.preimage_inter,
      Set.preimage_range, Set.univ_inter]
  rw [hset]
  calc (tateSelfProductFirstTransitionInv R I q hI).hom.base ''
          (⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
            Set.range (secondFactorOverlapChart R I q hI).base)
      ⊆ ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (bothFactorOverlapChart R I q hI).base :=
        tateSelfProductFirstTransitionInv_image_subset R I q hI
    _ = ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (secondFactorOverlapChart R I q hI).base := hset

/-- **Right shape, swapped ordering (inversion).** Analogue of
`tateSelfProductRightTransition_image_subset'`. -/
theorem tateSelfProductRightTransitionInv_image_subset' (hI : I.FG) :
    (tateSelfProductRightTransitionInv R I q hI).hom.base ''
        (⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (bothFactorOverlapChart R I q hI).base) ⊆
      ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (firstFactorOverlapChart R I q hI).base := by
  have hset : ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (bothFactorOverlapChart R I q hI).base =
      ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (firstFactorOverlapChart R I q hI).base := by
    rw [range_bothFactorOverlapChart_eq_inter_first_second R I q hI, Set.preimage_inter,
      Set.preimage_range, Set.inter_univ]
  rw [hset]
  calc (tateSelfProductRightTransitionInv R I q hI).hom.base ''
          (⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
            Set.range (firstFactorOverlapChart R I q hI).base)
      ⊆ ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (bothFactorOverlapChart R I q hI).base :=
        tateSelfProductRightTransitionInv_image_subset R I q hI
    _ = ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (firstFactorOverlapChart R I q hI).base := hset

/-- **Both shape, swapped ordering (inversion).** Analogue of
`tateSelfProductBothTransition_image_subset'`; target region is `univ`. -/
theorem tateSelfProductBothTransitionInv_image_subset' (hI : I.FG) :
    (tateSelfProductBothTransitionInv R I q hI).hom.base ''
        (⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (secondFactorOverlapChart R I q hI).base) ⊆
      ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (firstFactorOverlapChart R I q hI).base := by
  have huniv : ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
      Set.range (firstFactorOverlapChart R I q hI).base = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    exact fun y =>
      range_bothFactorOverlapChart_subset_first R I q hI (Set.mem_range_self y)
  rw [huniv]
  exact Set.subset_univ _

/-- **The reduced range inclusion `H` (inversion)**, dispatched by Klein-four shape. The inversion
analogue of `tateSelfProductGlueT'_range_reduced`. -/
theorem tateSelfProductGlueTInv'_range_reduced (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (tateSelfProductGlueTInv R I q hI i j hij).base ''
        (⇑(tateSelfProductGlueF R I q hI i j hij).base ⁻¹'
          Set.range (tateSelfProductGlueF R I q hI i k hik).base) ⊆
      ⇑(tateSelfProductGlueF R I q hI j i hij.symm).base ⁻¹'
        Set.range (tateSelfProductGlueF R I q hI j k hjk).base := by
  revert hij hik hjk
  rcases i with ⟨(_ | _), (_ | _)⟩ <;> rcases j with ⟨(_ | _), (_ | _)⟩ <;>
    rcases k with ⟨(_ | _), (_ | _)⟩ <;> intro hij hik hjk <;>
    first
      | exact absurd rfl hij
      | exact absurd rfl hik
      | exact absurd rfl hjk
      | (simp only [tateSelfProductGlueF, tateSelfProductGlueTInv]
         first
           | exact tateSelfProductFirstTransitionInv_image_subset R I q hI
           | exact tateSelfProductRightTransitionInv_image_subset R I q hI
           | exact tateSelfProductBothTransitionInv_image_subset R I q hI
           | exact tateSelfProductFirstTransitionInv_image_subset' R I q hI
           | exact tateSelfProductRightTransitionInv_image_subset' R I q hI
           | exact tateSelfProductBothTransitionInv_image_subset' R I q hI)

/-- **The range inclusion `H` (inversion)** in `pullback` form. The inversion analogue of
`tateSelfProductGlueT'_range`. -/
theorem tateSelfProductGlueTInv'_range (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)] :
    Set.range (pullback.fst (tateSelfProductGlueF R I q hI i j hij)
          (tateSelfProductGlueF R I q hI i k hik) ≫
        tateSelfProductGlueTInv R I q hI i j hij).base ⊆
      Set.range (pullback.snd (tateSelfProductGlueF R I q hI j k hjk)
        (tateSelfProductGlueF R I q hI j i hij.symm)).base := by
  rw [LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp,
    range_pullback_fst, range_pullback_snd]
  exact tateSelfProductGlueTInv'_range_reduced R I q hI i j k hij hik hjk

/-! ### Layer 3: the lift-built `t_inv'` and its first-leg law -/

/-- **The transition-of-transitions** `t_inv' i j k` (inversion). The inversion analogue of
`tateSelfProductGlueT'`. -/
def tateSelfProductGlueTInv' (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)] :
    pullback (tateSelfProductGlueF R I q hI i j hij) (tateSelfProductGlueF R I q hI i k hik) ⟶
      pullback (tateSelfProductGlueF R I q hI j k hjk)
        (tateSelfProductGlueF R I q hI j i hij.symm) :=
  glueTPrimeOfLift (tateSelfProductGlueF R I q hI i j hij)
    (tateSelfProductGlueF R I q hI i k hik) (tateSelfProductGlueF R I q hI j k hjk)
    (tateSelfProductGlueF R I q hI j i hij.symm) (tateSelfProductGlueTInv R I q hI i j hij)
    (tateSelfProductGlueTInv'_range R I q hI i j k hij hik hjk)

/-- **The first-leg-through-chart law of `tateSelfProductGlueTInv'`.** The inversion analogue of
`tateSelfProductGlueT'_fst_comp`. -/
theorem tateSelfProductGlueTInv'_fst_comp (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)] :
    tateSelfProductGlueTInv' R I q hI i j k hij hik hjk ≫
        pullback.fst (tateSelfProductGlueF R I q hI j k hjk)
            (tateSelfProductGlueF R I q hI j i hij.symm) ≫
          tateSelfProductGlueF R I q hI j k hjk =
      pullback.fst (tateSelfProductGlueF R I q hI i j hij)
          (tateSelfProductGlueF R I q hI i k hik) ≫
        tateSelfProductGlueTInv R I q hI i j hij ≫
          tateSelfProductGlueF R I q hI j i hij.symm :=
  glueTPrimeOfLift_fst_comp (tateSelfProductGlueF R I q hI i j hij)
    (tateSelfProductGlueF R I q hI i k hik) (tateSelfProductGlueF R I q hI j k hjk)
    (tateSelfProductGlueF R I q hI j i hij.symm) (tateSelfProductGlueTInv R I q hI i j hij)
    (tateSelfProductGlueTInv'_range R I q hI i j k hij hik hjk)

/-! ### Layer 4: the conjugated self-map `tateSelfProductDInv` -/

/-- **The conjugated self-map** `tateSelfProductDInv i j k` (inversion). The inversion analogue of
`tateSelfProductD`; reuses the model-independent `tateSelfProductBothChartIso`. -/
def tateSelfProductDInv (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j i hij.symm)]
    [LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI)] :=
  (tateSelfProductBothChartIso R I q hI i j k hij hik hjk).hom ≫
    tateSelfProductGlueTInv' R I q hI i j k hij hik hjk ≫
      (tateSelfProductBothChartIso R I q hI j k i hjk hij.symm hik.symm).inv

/-- **The defining law of `tateSelfProductDInv`.** The inversion analogue of
`tateSelfProductD_comp_bothChart`. -/
theorem tateSelfProductDInv_comp_bothChart (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j i hij.symm)]
    [LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI)] :
    tateSelfProductDInv R I q hI i j k hij hik hjk ≫ bothFactorOverlapChart R I q hI =
      (tateSelfProductBothChartIso R I q hI i j k hij hik hjk).hom ≫
        pullback.fst (tateSelfProductGlueF R I q hI i j hij)
            (tateSelfProductGlueF R I q hI i k hik) ≫
          tateSelfProductGlueTInv R I q hI i j hij ≫
            tateSelfProductGlueF R I q hI j i hij.symm := by
  rw [tateSelfProductDInv, Category.assoc, Category.assoc,
    tateSelfProductBothChartIso_inv_comp R I q hI j k i hjk hij.symm hik.symm]
  exact congrArg (fun m => (tateSelfProductBothChartIso R I q hI i j k hij hik hjk).hom ≫ m)
    (tateSelfProductGlueTInv'_fst_comp R I q hI i j k hij hik hjk)

/-! ### Layer 5: the summand permutation `tateSelfProductSigmaInv` -/

/-- Swap-first per-summand inversion transition `dXX ≅ dYX`. Analogue of `swapFirstSummandXX`. -/
abbrev swapFirstSummandXXInv (hI : I.FG) : dXX R I q ≅ dYX R I q :=
  mapSpfIso hI (annulusFibreChartTransitionInvAlg R I q hI)
    (AlgEquiv.refl (R := R)
      (A₁ := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))

/-- Swap-first per-summand inversion transition `dXY ≅ dYY`. Analogue of `swapFirstSummandXY`. -/
abbrev swapFirstSummandXYInv (hI : I.FG) : dXY R I q ≅ dYY R I q :=
  mapSpfIso hI (annulusFibreChartTransitionInvAlg R I q hI)
    (AlgEquiv.refl (R := R)
      (A₁ := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))

/-- Swap-second per-summand inversion transition `dXX ≅ dXY`. Analogue of `swapSecondSummandXX`. -/
abbrev swapSecondSummandXXInv (hI : I.FG) : dXX R I q ≅ dXY R I q :=
  mapSpfIso hI
    (AlgEquiv.refl (R := R)
      (A₁ := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
    (annulusFibreChartTransitionInvAlg R I q hI)

/-- Swap-second per-summand inversion transition `dYX ≅ dYY`. Analogue of `swapSecondSummandYX`. -/
abbrev swapSecondSummandYXInv (hI : I.FG) : dYX R I q ≅ dYY R I q :=
  mapSpfIso hI
    (AlgEquiv.refl (R := R)
      (A₁ := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))
    (annulusFibreChartTransitionInvAlg R I q hI)

/-- **The swap-first inversion involution.** Analogue of `tateSelfProductSwapFirstTransition`. -/
def tateSelfProductSwapFirstTransitionInv (hI : I.FG) :
    ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ≅
      ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) where
  hom := coprod.desc
    (coprod.desc ((swapFirstSummandXXInv R I q hI).hom ≫ coprod.inl ≫ coprod.inr)
      ((swapFirstSummandXYInv R I q hI).hom ≫ coprod.inr ≫ coprod.inr))
    (coprod.desc ((swapFirstSummandXXInv R I q hI).inv ≫ coprod.inl ≫ coprod.inl)
      ((swapFirstSummandXYInv R I q hI).inv ≫ coprod.inr ≫ coprod.inl))
  inv := coprod.desc
    (coprod.desc ((swapFirstSummandXXInv R I q hI).hom ≫ coprod.inl ≫ coprod.inr)
      ((swapFirstSummandXYInv R I q hI).hom ≫ coprod.inr ≫ coprod.inr))
    (coprod.desc ((swapFirstSummandXXInv R I q hI).inv ≫ coprod.inl ≫ coprod.inl)
      ((swapFirstSummandXYInv R I q hI).inv ≫ coprod.inr ≫ coprod.inl))
  hom_inv_id := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Category.comp_id]
  inv_hom_id := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Category.comp_id]

/-- **The swap-second inversion involution.** Analogue of `tateSelfProductSwapSecondTransition`. -/
def tateSelfProductSwapSecondTransitionInv (hI : I.FG) :
    ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ≅
      ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) where
  hom := coprod.desc
    (coprod.desc ((swapSecondSummandXXInv R I q hI).hom ≫ coprod.inr ≫ coprod.inl)
      ((swapSecondSummandXXInv R I q hI).inv ≫ coprod.inl ≫ coprod.inl))
    (coprod.desc ((swapSecondSummandYXInv R I q hI).hom ≫ coprod.inr ≫ coprod.inr)
      ((swapSecondSummandYXInv R I q hI).inv ≫ coprod.inl ≫ coprod.inr))
  inv := coprod.desc
    (coprod.desc ((swapSecondSummandXXInv R I q hI).hom ≫ coprod.inr ≫ coprod.inl)
      ((swapSecondSummandXXInv R I q hI).inv ≫ coprod.inl ≫ coprod.inl))
    (coprod.desc ((swapSecondSummandYXInv R I q hI).hom ≫ coprod.inr ≫ coprod.inr)
      ((swapSecondSummandYXInv R I q hI).inv ≫ coprod.inl ≫ coprod.inr))
  hom_inv_id := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Category.comp_id]
  inv_hom_id := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Category.comp_id]

/-- **The summand permutation** `tateSelfProductSigmaInv i j k` (inversion). Analogue of
`tateSelfProductSigma`; uses `tateSelfProductBothTransitionInv` on the both-differ shape. -/
def tateSelfProductSigmaInv (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (_hik : i ≠ k) (_hjk : j ≠ k) :
    (((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ≅
      ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q))) :=
  match i, j, hij with
  | (false, false), (false, false), h => (h rfl).elim
  | (false, false), (false, true), _ => tateSelfProductSwapSecondTransitionInv R I q hI
  | (false, false), (true, false), _ => tateSelfProductSwapFirstTransitionInv R I q hI
  | (false, false), (true, true), _ => tateSelfProductBothTransitionInv R I q hI
  | (false, true), (false, false), _ => tateSelfProductSwapSecondTransitionInv R I q hI
  | (false, true), (false, true), h => (h rfl).elim
  | (false, true), (true, false), _ => tateSelfProductBothTransitionInv R I q hI
  | (false, true), (true, true), _ => tateSelfProductSwapFirstTransitionInv R I q hI
  | (true, false), (false, false), _ => tateSelfProductSwapFirstTransitionInv R I q hI
  | (true, false), (false, true), _ => tateSelfProductBothTransitionInv R I q hI
  | (true, false), (true, false), h => (h rfl).elim
  | (true, false), (true, true), _ => tateSelfProductSwapSecondTransitionInv R I q hI
  | (true, true), (false, false), _ => tateSelfProductBothTransitionInv R I q hI
  | (true, true), (false, true), _ => tateSelfProductSwapFirstTransitionInv R I q hI
  | (true, true), (true, false), _ => tateSelfProductSwapSecondTransitionInv R I q hI
  | (true, true), (true, true), h => (h rfl).elim

/-! ### Layer 6: the direct summand-comparison identification `tateSelfProductD_eq_sigma_inv`

Unlike the swap, the 𝔾m inversion has no `A`-algebra automorphism, so the swap route through a
common endomorphism `mapSpf hI (A-endo) (A-endo)` of `Spf(A ⊗̂ A)` does not exist. We compare the
two sides directly, summand by summand: on each summand both `tateSelfProductDInv i j k ≫ bothChart`
and `(tateSelfProductSigmaInv i j k).hom ≫ bothChart` collapse — via `mapSpf_comp` and the
`interchange…_eq_mapSpf` family — to `mapSpf hI u v` for the *same* `R`-algebra composites. -/

/-- `A{1/x}` over the `I.map (algebraMap R A)` ideal convention the interchange charts use. -/
private abbrev awXInv : Type u :=
  awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)

/-- `A{1/y}` over the `I.map (algebraMap R A)` ideal convention. -/
private abbrev awYInv : Type u :=
  awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)

/-- The localization `R`-algebra map `A →ₐ A{1/x}`. -/
private abbrev locXInv : annulusAlgebra R I q →ₐ[R] awXInv R I q :=
  IsScalarTower.toAlgHom R (annulusAlgebra R I q)
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))

/-- The localization `R`-algebra map `A →ₐ A{1/y}`. -/
private abbrev locYInv : annulusAlgebra R I q →ₐ[R] awYInv R I q :=
  IsScalarTower.toAlgHom R (annulusAlgebra R I q)
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))

/-- `mapSpf` depends only on the two `R`-algebra maps (local copy of the `mapSpf_congr` idiom). -/
private theorem mapSpf_congr {A₀ B₀ A₁ B₁ : Type u} [CommRing A₀] [CommRing B₀] [CommRing A₁]
    [CommRing B₁] [Algebra R A₀] [Algebra R B₀] [Algebra R A₁] [Algebra R B₁] (hI : I.FG)
    {f₁ f₂ : A₀ →ₐ[R] A₁} {g₁ g₂ : B₀ →ₐ[R] B₁} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    CompletedTensorProduct.mapSpf hI f₁ g₁ = CompletedTensorProduct.mapSpf hI f₂ g₂ := by
  subst hf hg; rfl

/-! #### The two abstract leg identities

Both shapes' per-summand legs are instances of a single `mapSpf`-functoriality identity, stated
here with **all four algebras abstract**. Keeping this computation at abstract types is what makes
the module fit in memory: performing it at the concrete nested
`AdicCompletion`/`CompletedTensorProduct` towers is what OOM-killed the previous formulation
(issue 636). -/

private theorem reflSymmToAlgHom {X : Type u} [CommRing X] [Algebra R X] :
    (AlgEquiv.refl (R := R) (A₁ := X)).symm.toAlgHom = AlgHom.id R X := rfl

private theorem reflToAlgHom {X : Type u} [CommRing X] [Algebra R X] :
    (AlgEquiv.refl (R := R) (A₁ := X)).toAlgHom = AlgHom.id R X := rfl

/-- **The abstract first-shape leg.** Localizing the second tensor factor, then moving the first
factor along `σ` (leaving the second untouched), then localizing the first factor, is the same as
moving the first factor along `σ` and then localizing both factors at once. Pure `mapSpf`
functoriality. The two identity maps `ρ`, `ρ'` are taken as parameters together with proofs that
they are the identity, so that the call sites need no rewriting of the `AlgEquiv.refl` legs
produced by `mapSpfIso_hom`/`mapSpfIso_inv`. -/
private theorem legFirstShape {S T V W : Type u} [CommRing S] [CommRing T] [CommRing V]
    [CommRing W] [Algebra R S] [Algebra R T] [Algebra R V] [Algebra R W] (hI : I.FG)
    (σ : T →ₐ[R] S) (f : W →ₐ[R] T) (g : W →ₐ[R] V)
    (ρ : W →ₐ[R] W) (hρ : ρ = AlgHom.id R W)
    (ρ' : V →ₐ[R] V) (hρ' : ρ' = AlgHom.id R V) :
    CompletedTensorProduct.mapSpf hI (AlgHom.id R S) g ≫
        CompletedTensorProduct.mapSpf hI σ ρ ≫
          CompletedTensorProduct.mapSpf hI f (AlgHom.id R W) =
      CompletedTensorProduct.mapSpf hI σ ρ' ≫ CompletedTensorProduct.mapSpf hI f g := by
  subst hρ hρ'
  rw [← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
    ← CompletedTensorProduct.mapSpf_comp]
  exact mapSpf_congr R I hI (AlgHom.id_comp _) (by ext a; simp)

/-- **The abstract second-shape leg**: the mirror of `legFirstShape` with the roles of the two
tensor factors exchanged. -/
private theorem legSecondShape {S T V W : Type u} [CommRing S] [CommRing T] [CommRing V]
    [CommRing W] [Algebra R S] [Algebra R T] [Algebra R V] [Algebra R W] (hI : I.FG)
    (σ : T →ₐ[R] S) (f : W →ₐ[R] T) (g : W →ₐ[R] V)
    (ρ : W →ₐ[R] W) (hρ : ρ = AlgHom.id R W)
    (ρ' : V →ₐ[R] V) (hρ' : ρ' = AlgHom.id R V) :
    CompletedTensorProduct.mapSpf hI g (AlgHom.id R S) ≫
        CompletedTensorProduct.mapSpf hI ρ σ ≫
          CompletedTensorProduct.mapSpf hI (AlgHom.id R W) f =
      CompletedTensorProduct.mapSpf hI ρ' σ ≫ CompletedTensorProduct.mapSpf hI g f := by
  subst hρ hρ'
  rw [← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
    ← CompletedTensorProduct.mapSpf_comp]
  exact mapSpf_congr R I hI (by ext a; simp) (AlgHom.id_comp _)

/-! #### The eight per-summand leg identities

Each is a `coprod`-free equation between two composites of `mapSpf`s. Stating them separately —
rather than inlining them as branches of the shape lemmas — is what keeps this module inside the
kernel's memory budget: see the module docstring of `TateSelfProductDInvLegs`. -/

/-- First shape, `(x, x)` summand. -/
private theorem firstLegXX (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (AlgHom.id R (awXInv R I q)) (locXInv R I q) ≫
        (firstSummandInv R I q hI).hom ≫
          interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI =
      (swapFirstSummandXXInv R I q hI).hom ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapY R I q) (overlapX R I q) hI := by
  rw [firstSummandInv, twoPatchFibreProductInvTransition, mapSpfIso_hom,
    swapFirstSummandXXInv, mapSpfIso_hom, interchangeOpenImmersion_eq_mapSpf,
    bothInterchangeOpenImmersion_eq_mapSpf]
  exact legFirstShape R I hI _ _ _ _ (reflSymmToAlgHom R) _ (reflSymmToAlgHom R)

/-- First shape, `(x, y)` summand. -/
private theorem firstLegXY (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (AlgHom.id R (awXInv R I q)) (locYInv R I q) ≫
        (firstSummandInv R I q hI).hom ≫
          interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI =
      (swapFirstSummandXYInv R I q hI).hom ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapY R I q) (overlapY R I q) hI := by
  rw [firstSummandInv, twoPatchFibreProductInvTransition, mapSpfIso_hom,
    swapFirstSummandXYInv, mapSpfIso_hom, interchangeOpenImmersion_eq_mapSpf,
    bothInterchangeOpenImmersion_eq_mapSpf]
  exact legFirstShape R I hI _ _ _ _ (reflSymmToAlgHom R) _ (reflSymmToAlgHom R)

/-- First shape, `(y, x)` summand. -/
private theorem firstLegYX (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (AlgHom.id R (awYInv R I q)) (locXInv R I q) ≫
        (firstSummandInv R I q hI).inv ≫
          interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI =
      (swapFirstSummandXXInv R I q hI).inv ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapX R I q) (overlapX R I q) hI := by
  rw [firstSummandInv, twoPatchFibreProductInvTransition, mapSpfIso_inv,
    swapFirstSummandXXInv, mapSpfIso_inv, interchangeOpenImmersion_eq_mapSpf,
    bothInterchangeOpenImmersion_eq_mapSpf]
  exact legFirstShape R I hI _ _ _ _ (reflToAlgHom R) _ (reflToAlgHom R)

/-- First shape, `(y, y)` summand. -/
private theorem firstLegYY (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (AlgHom.id R (awYInv R I q)) (locYInv R I q) ≫
        (firstSummandInv R I q hI).inv ≫
          interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI =
      (swapFirstSummandXYInv R I q hI).inv ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapX R I q) (overlapY R I q) hI := by
  rw [firstSummandInv, twoPatchFibreProductInvTransition, mapSpfIso_inv,
    swapFirstSummandXYInv, mapSpfIso_inv, interchangeOpenImmersion_eq_mapSpf,
    bothInterchangeOpenImmersion_eq_mapSpf]
  exact legFirstShape R I hI _ _ _ _ (reflToAlgHom R) _ (reflToAlgHom R)

/-- Second shape, `(x, x)` summand. -/
private theorem secondLegXX (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (locXInv R I q) (AlgHom.id R (awXInv R I q)) ≫
        (rightSummandInv R I q hI).hom ≫
          rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI =
      (swapSecondSummandXXInv R I q hI).hom ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapX R I q) (overlapY R I q) hI := by
  rw [rightSummandInv, mapSpfIso_hom, swapSecondSummandXXInv, mapSpfIso_hom,
    rightInterchangeOpenImmersion_eq_mapSpf, bothInterchangeOpenImmersion_eq_mapSpf]
  exact legSecondShape R I hI _ _ _ _ (reflSymmToAlgHom R) _ (reflSymmToAlgHom R)

/-- Second shape, `(x, y)` summand. -/
private theorem secondLegXY (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (locXInv R I q) (AlgHom.id R (awYInv R I q)) ≫
        (rightSummandInv R I q hI).inv ≫
          rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI =
      (swapSecondSummandXXInv R I q hI).inv ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapX R I q) (overlapX R I q) hI := by
  rw [rightSummandInv, mapSpfIso_inv, swapSecondSummandXXInv, mapSpfIso_inv,
    rightInterchangeOpenImmersion_eq_mapSpf, bothInterchangeOpenImmersion_eq_mapSpf]
  exact legSecondShape R I hI _ _ _ _ (reflToAlgHom R) _ (reflToAlgHom R)

/-- Second shape, `(y, x)` summand. -/
private theorem secondLegYX (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (locYInv R I q) (AlgHom.id R (awXInv R I q)) ≫
        (rightSummandInv R I q hI).hom ≫
          rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI =
      (swapSecondSummandYXInv R I q hI).hom ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapY R I q) (overlapY R I q) hI := by
  rw [rightSummandInv, mapSpfIso_hom, swapSecondSummandYXInv, mapSpfIso_hom,
    rightInterchangeOpenImmersion_eq_mapSpf, bothInterchangeOpenImmersion_eq_mapSpf]
  exact legSecondShape R I hI _ _ _ _ (reflSymmToAlgHom R) _ (reflSymmToAlgHom R)

/-- Second shape, `(y, y)` summand. -/
private theorem secondLegYY (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (locYInv R I q) (AlgHom.id R (awYInv R I q)) ≫
        (rightSummandInv R I q hI).inv ≫
          rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI =
      (swapSecondSummandYXInv R I q hI).inv ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapY R I q) (overlapX R I q) hI := by
  rw [rightSummandInv, mapSpfIso_inv, swapSecondSummandYXInv, mapSpfIso_inv,
    rightInterchangeOpenImmersion_eq_mapSpf, bothInterchangeOpenImmersion_eq_mapSpf]
  exact legSecondShape R I hI _ _ _ _ (reflToAlgHom R) _ (reflToAlgHom R)

/-! #### The four `ι`-legs of each shape -/

/-- First shape: the canonical section of the first-factor overlap chart. -/
private theorem iotaFirstLeg (a b : annulusAlgebra R I q) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI
        (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a))
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b)) ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I a hI =
      bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
        a b hI := by
  rw [interchangeOpenImmersion_eq_mapSpf, bothInterchangeOpenImmersion_eq_mapSpf,
    ← CompletedTensorProduct.mapSpf_comp]
  exact mapSpf_congr R I hI (AlgHom.id_comp _) (AlgHom.comp_id _)

/-- Second shape: the canonical section of the second-factor overlap chart. -/
private theorem iotaSecondLeg (a b : annulusAlgebra R I q) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a))
        (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b)) ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I b hI =
      bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
        a b hI := by
  rw [rightInterchangeOpenImmersion_eq_mapSpf, bothInterchangeOpenImmersion_eq_mapSpf,
    ← CompletedTensorProduct.mapSpf_comp]
  exact mapSpf_congr R I hI (AlgHom.comp_id _) (AlgHom.id_comp _)

/-! #### The two shape lemmas -/

/-- The canonical section of the first-factor overlap chart on the both-overlap object. -/
private abbrev firstShapeIota (hI : I.FG) :
    ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶ (dXA R I q ⨿ dYA R I q) :=
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
        coprod.inr))

/-- `firstShapeIota` is a section of the first-factor overlap chart. -/
private theorem firstShapeIota_comp (hI : I.FG) :
    firstShapeIota R I q hI ≫ firstFactorOverlapChart R I q hI =
      bothFactorOverlapChart R I q hI := by
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
  · simp only [firstShapeIota, bothFactorOverlapChart, firstFactorOverlapChart, coprod.inl_desc,
      coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact iotaFirstLeg R I q _ _ hI

/-- The canonical section of the second-factor overlap chart on the both-overlap object. -/
private abbrev secondShapeIota (hI : I.FG) :
    ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶ (dAX R I q ⨿ dAY R I q) :=
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
        coprod.inr))

/-- `secondShapeIota` is a section of the second-factor overlap chart. -/
private theorem secondShapeIota_comp (hI : I.FG) :
    secondShapeIota R I q hI ≫ secondFactorOverlapChart R I q hI =
      bothFactorOverlapChart R I q hI := by
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
  · simp only [secondShapeIota, bothFactorOverlapChart, secondFactorOverlapChart, coprod.inl_desc,
      coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact iotaSecondLeg R I q _ _ hI

/-- **First shape (inversion).** For a prefix `p` cut out over the first-factor overlap chart
(`p ≫ firstFactorOverlapChart = bothFactorOverlapChart`), the first-factor inversion transition
followed by the return chart matches the swap-first permutation followed by the both-chart. -/
private theorem firstShapeDInv (hq : q ∈ I) (hI : I.FG)
    (p : ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶ (dXA R I q ⨿ dYA R I q))
    (hp : p ≫ firstFactorOverlapChart R I q hI = bothFactorOverlapChart R I q hI) :
    p ≫ (tateSelfProductFirstTransitionInv R I q hI).hom ≫ firstFactorOverlapChart R I q hI =
      (tateSelfProductSwapFirstTransitionInv R I q hI).hom ≫ bothFactorOverlapChart R I q hI := by
  haveI := isOpenImmersion_firstFactorOverlapChart R I q hq hI
  obtain rfl : p = firstShapeIota R I q hI := by
    rw [← cancel_mono (firstFactorOverlapChart R I q hI), hp, firstShapeIota_comp]
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_)
  · simp only [firstShapeIota, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc, tateSelfProductFirstTransitionInv,
      tateSelfProductSwapFirstTransitionInv, firstFactorOverlapChart, bothFactorOverlapChart]
    exact firstLegXX R I q hI
  · simp only [firstShapeIota, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc, tateSelfProductFirstTransitionInv,
      tateSelfProductSwapFirstTransitionInv, firstFactorOverlapChart, bothFactorOverlapChart]
    exact firstLegXY R I q hI
  · simp only [firstShapeIota, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc, tateSelfProductFirstTransitionInv,
      tateSelfProductSwapFirstTransitionInv, firstFactorOverlapChart, bothFactorOverlapChart]
    exact firstLegYX R I q hI
  · simp only [firstShapeIota, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc, tateSelfProductFirstTransitionInv,
      tateSelfProductSwapFirstTransitionInv, firstFactorOverlapChart, bothFactorOverlapChart]
    exact firstLegYY R I q hI

/-- **Second shape (inversion).** The second-factor analogue of `firstShapeDInv`. -/
private theorem secondShapeDInv (hq : q ∈ I) (hI : I.FG)
    (p : ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶ (dAX R I q ⨿ dAY R I q))
    (hp : p ≫ secondFactorOverlapChart R I q hI = bothFactorOverlapChart R I q hI) :
    p ≫ (tateSelfProductRightTransitionInv R I q hI).hom ≫ secondFactorOverlapChart R I q hI =
      (tateSelfProductSwapSecondTransitionInv R I q hI).hom ≫ bothFactorOverlapChart R I q hI := by
  haveI := isOpenImmersion_secondFactorOverlapChart R I q hq hI
  obtain rfl : p = secondShapeIota R I q hI := by
    rw [← cancel_mono (secondFactorOverlapChart R I q hI), hp, secondShapeIota_comp]
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_)
  · simp only [secondShapeIota, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc, tateSelfProductRightTransitionInv,
      tateSelfProductSwapSecondTransitionInv, secondFactorOverlapChart, bothFactorOverlapChart]
    exact secondLegXX R I q hI
  · simp only [secondShapeIota, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc, tateSelfProductRightTransitionInv,
      tateSelfProductSwapSecondTransitionInv, secondFactorOverlapChart, bothFactorOverlapChart]
    exact secondLegXY R I q hI
  · simp only [secondShapeIota, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc, tateSelfProductRightTransitionInv,
      tateSelfProductSwapSecondTransitionInv, secondFactorOverlapChart, bothFactorOverlapChart]
    exact secondLegYX R I q hI
  · simp only [secondShapeIota, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc, tateSelfProductRightTransitionInv,
      tateSelfProductSwapSecondTransitionInv, secondFactorOverlapChart, bothFactorOverlapChart]
    exact secondLegYY R I q hI

/-- **Both shape (inversion).** When `i` and `j` differ in both coordinates the prefix `p` is forced
to be the identity (it factors through the mono `bothFactorOverlapChart`), and both the transition
and the permutation are `tateSelfProductBothTransitionInv`. -/
private theorem bothShapeDInv (hq : q ∈ I) (hI : I.FG)
    (p : ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶
        ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)))
    (hp : p ≫ bothFactorOverlapChart R I q hI = bothFactorOverlapChart R I q hI) :
    p ≫ (tateSelfProductBothTransitionInv R I q hI).hom ≫ bothFactorOverlapChart R I q hI =
      (tateSelfProductBothTransitionInv R I q hI).hom ≫ bothFactorOverlapChart R I q hI := by
  haveI := isOpenImmersion_bothFactorOverlapChart R I q hq hI
  obtain rfl : p = 𝟙 _ := by
    rw [← cancel_mono (bothFactorOverlapChart R I q hI), Category.id_comp]; exact hp
  rw [Category.id_comp]
/-- **The shape-dispatched summand comparison.** For a prefix `p : bothOverlapObj ⟶ V i j` cut out
over the overlap chart `f i j` (`p ≫ f i j = bothChart`), the genuine transition `t_inv i j` on the
shared overlap, composed with the return chart `f j i`, agrees with the summand permutation
`σ_inv i j k` composed with the both-chart. Instance-free so the `Bool × Bool` case split reduces
the match definitions; each valid shape (first/second/both) is discharged by the corresponding shape
lemma, which is `k`-independent (the σ-permutation's `match` ignores `k`). -/
private theorem tateSelfProductDInv_dispatch (hq : q ∈ I) (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (p : ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶
      tateSelfProductGlueV R I q hI i j hij)
    (hp : p ≫ tateSelfProductGlueF R I q hI i j hij = bothFactorOverlapChart R I q hI) :
    p ≫ tateSelfProductGlueTInv R I q hI i j hij ≫
        tateSelfProductGlueF R I q hI j i hij.symm =
      (tateSelfProductSigmaInv R I q hI i j k hij hik hjk).hom ≫
        bothFactorOverlapChart R I q hI := by
  revert hij hik hjk p
  rcases i with ⟨_ | _, _ | _⟩ <;> rcases j with ⟨_ | _, _ | _⟩ <;>
    intro hij hik hjk p hp <;>
    first
      | exact absurd rfl hij
      | (simp only [tateSelfProductGlueTInv, tateSelfProductGlueF, tateSelfProductSigmaInv] at hp ⊢
         first
           | exact firstShapeDInv R I q hq hI p hp
           | exact secondShapeDInv R I q hq hI p hp
           | exact bothShapeDInv R I q hq hI p hp)

/-- **The 𝔾m-inversion self-product cocycle payload.** For every pairwise-distinct triple
`i j k : Bool × Bool` the conjugated self-map `tateSelfProductDInv i j k` equals the `hom` leg of
the explicit summand permutation `tateSelfProductSigmaInv i j k`. The inversion analogue of
`tateSelfProductD_eq_sigma`, proved by direct summand comparison. -/
theorem tateSelfProductD_eq_sigma_inv (hq : q ∈ I) (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j i hij.symm)]
    [LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI)] :
    tateSelfProductDInv R I q hI i j k hij hik hjk =
      (tateSelfProductSigmaInv R I q hI i j k hij hik hjk).hom := by
  rw [← cancel_mono (bothFactorOverlapChart R I q hI),
    tateSelfProductDInv_comp_bothChart R I q hI i j k hij hik hjk, ← Category.assoc]
  refine tateSelfProductDInv_dispatch R I q hq hI i j k hij hik hjk
    ((tateSelfProductBothChartIso R I q hI i j k hij hik hjk).hom ≫
      pullback.fst (tateSelfProductGlueF R I q hI i j hij)
        (tateSelfProductGlueF R I q hI i k hik)) ?_
  rw [Category.assoc]
  exact tateSelfProductBothChartIso_hom_fst_comp R I q hI i j k hij hik hjk

end AlgebraicGeometry

end
