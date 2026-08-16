import FormalSchemes.TateSelfProductTransitionInv
import FormalSchemes.TateSelfProductTPrimeSummandIdentify
import FormalSchemes.CompletedTensorAwayInterchangeMixedPullback
import FormalSchemes.CompletedTensorAwayInterchangeBothPullback

set_option linter.style.header false
set_option linter.style.setOption false
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

end AlgebraicGeometry

end
