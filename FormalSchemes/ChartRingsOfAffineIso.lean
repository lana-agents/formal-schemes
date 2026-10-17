/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartAlgebraStructureMap
import FormalSchemes.ChartRingsOfAffine

/-!
# An affine scheme over `ℙ¹_A` is the relative spectrum of its chart algebra

For an affine morphism `f : Y ⟶ ℙ¹_A`, the chart algebra `ProjectiveLine.algStrOfAffine f` (the
pushforward of `𝒪_Y`, given on the charts) has a relative spectrum over `ℙ¹_A`. This file
identifies it with `Y`: the chart morphisms `Spec Γ(Y, f⁻¹ U_k) → Y` glue
(`AlgebraicGeometry.ChartedSchemeDatum.desc`) to a morphism from the relative spectrum to `Y`
(`ProjectiveLine.fromRelSpec`), which is an isomorphism
(`ProjectiveLine.isIso_fromRelSpec`, by `AlgebraicGeometry.ChartedSchemeDatum.isIso_desc`: the
charts are open immersions onto `f⁻¹ U₀`, `f⁻¹ U₁`, which cover `Y` and meet exactly in the image
of the overlap) and lies over `ℙ¹_A` (`ProjectiveLine.fromRelSpec_comp`); as an isomorphism over
`ℙ¹_A` it is `ProjectiveLine.relSpecIso`.

So the two constructions `f ↦ ProjectiveLine.algStrOfAffine f` and
`B ↦ ProjectiveLine.ChartModule.AlgStr.toP1 B` are inverse in this direction.
-/

universe u

open AlgebraicGeometry CategoryTheory Polynomial
open scoped LaurentPolynomial

namespace ProjectiveLine

open ChartModule BTensor

variable {A : Type u} [CommRing A]


variable {Y : Scheme.{u}} (f : Y ⟶ scheme A) [IsAffineHom f]


/-! The ring instances of `ProjectiveLine.ChartModule.AlgStr.Ring0` etc. are keyed on a generic
chart module; for the chart module of `f` (an `abbrev` structure instance) they have to be
restated. -/

noncomputable instance : CommRing (algStrOfAffine f).Ring0 := AlgStr.instCommRingRing0 _

noncomputable instance : CommRing (algStrOfAffine f).Ring1 := AlgStr.instCommRingRing1 _

noncomputable instance : CommRing (algStrOfAffine f).Ring01 := AlgStr.instCommRingRing01 _

/-- The ring of sections of the chart algebra of `f` over the first chart is `Γ(Y, f⁻¹ U₀)`. -/
noncomputable def ring0Equiv : (algStrOfAffine f).Ring0 ≃+* Γ(Y, f ⁻¹ᵁ U A 0) where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' a b :=
    TwoChartRings.bmul_tm A (R := (twoChartRingsOfAffine f).R0) (chartPullback f 0 X) a b
  map_add' _ _ := rfl

/-- The ring of sections of the chart algebra of `f` over the second chart is `Γ(Y, f⁻¹ U₁)`. -/
noncomputable def ring1Equiv : (algStrOfAffine f).Ring1 ≃+* Γ(Y, f ⁻¹ᵁ U A 1) where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' a b :=
    TwoChartRings.bmul_tm A (R := (twoChartRingsOfAffine f).R1) (chartPullback f 1 X) a b
  map_add' _ _ := rfl

/-- The ring of sections of the chart algebra of `f` over the overlap is
`Γ(Y, f⁻¹ (U₀ ∩ U₁))`. -/
noncomputable def ring01Equiv :
    (algStrOfAffine f).Ring01 ≃+* Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1)) where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' a b :=
    TwoChartRings.bmul_tm A (R := (twoChartRingsOfAffine f).R01)
      (overlapUnit f : Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1))) a b
  map_add' _ _ := rfl

lemma ring01Equiv_r0Hom (z : (algStrOfAffine f).Ring0) :
    ring01Equiv f ((algStrOfAffine f).r0Hom z) = preimageRes f 0 (ring0Equiv f z) := rfl

lemma ring01Equiv_r1Hom (z : (algStrOfAffine f).Ring1) :
    ring01Equiv f ((algStrOfAffine f).r1Hom z) = preimageRes f 1 (ring1Equiv f z) := rfl

lemma ring0Equiv_X0 : ring0Equiv f (algStrOfAffine f).X0 = chartPullback f 0 X :=
  mul_one (chartPullback f 0 X)

lemma ring1Equiv_X1 : ring1Equiv f (algStrOfAffine f).X1 = chartPullback f 1 X :=
  mul_one (chartPullback f 1 X)

/-- `f⁻¹ U_k` is affine. -/
lemma isAffineOpen_preimage_U (k : Fin 2) : IsAffineOpen (f ⁻¹ᵁ U A k) :=
  (isAffineOpen_U A k).preimage f

/-- `f⁻¹ (U₀ ∩ U₁)` is affine. -/
lemma isAffineOpen_preimage_inf : IsAffineOpen (f ⁻¹ᵁ (U A 0 ⊓ U A 1)) :=
  (isAffineOpen_U_inf A).preimage f

/-- Two ring maps out of the sections over `f⁻¹ U₀` and `f⁻¹ U₁` which factor through restriction
to `f⁻¹ (U₀ ∩ U₁)` by the same map give the same morphism to `Y`. -/
lemma specMap_comp_fromSpec_eq {S : CommRingCat.{u}} (χ : Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1)) ⟶ S)
    (u0 : Γ(Y, f ⁻¹ᵁ U A 0) ⟶ S) (u1 : Γ(Y, f ⁻¹ᵁ U A 1) ⟶ S)
    (h0 : u0 = Y.presheaf.map (homOfLE (preimage_inf_le f 0)).op ≫ χ)
    (h1 : u1 = Y.presheaf.map (homOfLE (preimage_inf_le f 1)).op ≫ χ) :
    Spec.map u0 ≫ (isAffineOpen_preimage_U f 0).fromSpec =
      Spec.map u1 ≫ (isAffineOpen_preimage_U f 1).fromSpec := by
  rw [h0, h1, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    IsAffineOpen.map_fromSpec _ (isAffineOpen_preimage_inf f),
    IsAffineOpen.map_fromSpec _ (isAffineOpen_preimage_inf f)]

lemma specMap_comp_fromSpec_zero {S : CommRingCat.{u}}
    (χ : Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1)) ⟶ S) (u0 : Γ(Y, f ⁻¹ᵁ U A 0) ⟶ S)
    (h0 : u0 = Y.presheaf.map (homOfLE (preimage_inf_le f 0)).op ≫ χ) :
    Spec.map u0 ≫ (isAffineOpen_preimage_U f 0).fromSpec =
      Spec.map χ ≫ (isAffineOpen_preimage_inf f).fromSpec := by
  rw [h0, Spec.map_comp, Category.assoc,
    IsAffineOpen.map_fromSpec _ (isAffineOpen_preimage_inf f)]


/-! ### The chart morphisms to `Y` -/

/-- `Γ(Y, f⁻¹ U₀) → B₀` (the identity). -/
noncomputable def toRing0 : Γ(Y, f ⁻¹ᵁ U A 0) ⟶ CommRingCat.of (algStrOfAffine f).Ring0 :=
  (ring0Equiv f).symm.toCommRingCatIso.hom

/-- `Γ(Y, f⁻¹ U₁) → B₁` (the identity). -/
noncomputable def toRing1 : Γ(Y, f ⁻¹ᵁ U A 1) ⟶ CommRingCat.of (algStrOfAffine f).Ring1 :=
  (ring1Equiv f).symm.toCommRingCatIso.hom

instance : IsIso (toRing0 f) := (ring0Equiv f).symm.toCommRingCatIso.isIso_hom

instance : IsIso (toRing1 f) := (ring1Equiv f).symm.toCommRingCatIso.isIso_hom

/-- The first chart `Spec B₀ ≅ f⁻¹ U₀ ⊆ Y`. -/
noncomputable def chartToY0 : Spec (CommRingCat.of (algStrOfAffine f).Ring0) ⟶ Y :=
  Spec.map (toRing0 f) ≫ (isAffineOpen_preimage_U f 0).fromSpec

/-- The second chart `Spec B₁ ≅ f⁻¹ U₁ ⊆ Y`. -/
noncomputable def chartToY1 : Spec (CommRingCat.of (algStrOfAffine f).Ring1) ⟶ Y :=
  Spec.map (toRing1 f) ≫ (isAffineOpen_preimage_U f 1).fromSpec

instance : IsOpenImmersion (chartToY0 f) := by unfold chartToY0; infer_instance

instance : IsOpenImmersion (chartToY1 f) := by unfold chartToY1; infer_instance

/-- `Γ(Y, f⁻¹ (U₀ ∩ U₁)) ≅ B₀[1/X]`. -/
noncomputable def overlapToLoc0 :
    Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1)) ⟶ CommRingCat.of (Localization.Away (algStrOfAffine f).X0) :=
  ((ring01Equiv f).symm.trans (algStrOfAffine f).locEquiv0.symm).toCommRingCatIso.hom

/-- `Γ(Y, f⁻¹ (U₀ ∩ U₁)) ≅ B₁[1/Y]`. -/
noncomputable def overlapToLoc1 :
    Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1)) ⟶ CommRingCat.of (Localization.Away (algStrOfAffine f).X1) :=
  ((ring01Equiv f).symm.trans (algStrOfAffine f).locEquiv1.symm).toCommRingCatIso.hom

instance : IsIso (overlapToLoc0 f) := RingEquiv.toCommRingCatIso _ |>.isIso_hom

instance : IsIso (overlapToLoc1 f) := RingEquiv.toCommRingCatIso _ |>.isIso_hom

lemma toRing0_algebraMap :
    toRing0 f ≫ CommRingCat.ofHom (algebraMap _ (Localization.Away (algStrOfAffine f).X0)) =
      Y.presheaf.map (homOfLE (preimage_inf_le f 0)).op ≫ overlapToLoc0 f := by
  ext s
  change algebraMap _ _ ((ring0Equiv f).symm s) =
    (algStrOfAffine f).locEquiv0.symm ((ring01Equiv f).symm (preimageRes f 0 s))
  apply (algStrOfAffine f).locEquiv0.injective
  rw [RingEquiv.apply_symm_apply, AlgStr.locEquiv0_algebraMap]
  rfl

lemma toRing1_algebraMap :
    toRing1 f ≫ CommRingCat.ofHom (algebraMap _ (Localization.Away (algStrOfAffine f).X1)) =
      Y.presheaf.map (homOfLE (preimage_inf_le f 1)).op ≫ overlapToLoc1 f := by
  ext s
  change algebraMap _ _ ((ring1Equiv f).symm s) =
    (algStrOfAffine f).locEquiv1.symm ((ring01Equiv f).symm (preimageRes f 1 s))
  apply (algStrOfAffine f).locEquiv1.injective
  rw [RingEquiv.apply_symm_apply, AlgStr.locEquiv1_algebraMap]
  rfl

lemma overlapToLoc1_symm :
    overlapToLoc1 f ≫ CommRingCat.ofHom (algStrOfAffine f).overlapEquiv.symm.toRingHom =
      overlapToLoc0 f := by
  ext s
  change (algStrOfAffine f).overlapEquiv.symm ((algStrOfAffine f).locEquiv1.symm _) =
    (algStrOfAffine f).locEquiv0.symm _
  rw [AlgStr.overlapEquiv_eq, RingEquiv.symm_trans_apply, RingEquiv.symm_symm,
    RingEquiv.apply_symm_apply]

lemma overlapToLoc0_equiv :
    overlapToLoc0 f ≫ CommRingCat.ofHom (algStrOfAffine f).overlapEquiv.toRingHom =
      overlapToLoc1 f := by
  ext s
  change (algStrOfAffine f).overlapEquiv ((algStrOfAffine f).locEquiv0.symm _) =
    (algStrOfAffine f).locEquiv1.symm _
  rw [AlgStr.overlapEquiv_eq, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]

lemma algebraMap_chartToY0 :
    Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away (algStrOfAffine f).X0))) ≫
      chartToY0 f = Spec.map (overlapToLoc0 f) ≫ (isAffineOpen_preimage_inf f).fromSpec := by
  rw [chartToY0, ← Category.assoc, ← Spec.map_comp, toRing0_algebraMap,
    specMap_comp_fromSpec_zero f _ _ rfl]

lemma algebraMap_chartToY1 :
    Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away (algStrOfAffine f).X1))) ≫
      chartToY1 f = Spec.map (overlapToLoc1 f) ≫ (isAffineOpen_preimage_inf f).fromSpec := by
  rw [chartToY1, ← Category.assoc, ← Spec.map_comp, toRing1_algebraMap, Spec.map_comp,
    Category.assoc, IsAffineOpen.map_fromSpec _ (isAffineOpen_preimage_inf f)]

lemma compatY01 :
    Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away (algStrOfAffine f).X0))) ≫
      chartToY0 f =
      Spec.map (CommRingCat.ofHom (algStrOfAffine f).overlapEquiv.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away (algStrOfAffine f).X1))) ≫
          chartToY1 f := by
  rw [algebraMap_chartToY0, algebraMap_chartToY1, ← Category.assoc, ← Spec.map_comp,
    overlapToLoc1_symm]

lemma compatY10 :
    Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away (algStrOfAffine f).X1))) ≫
      chartToY1 f =
      Spec.map (CommRingCat.ofHom (algStrOfAffine f).overlapEquiv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away (algStrOfAffine f).X0))) ≫
          chartToY0 f := by
  rw [algebraMap_chartToY0, algebraMap_chartToY1, ← Category.assoc, ← Spec.map_comp,
    overlapToLoc0_equiv]

/-- The chart morphisms to `Y`, indexed by the charts of the gluing datum. -/
noncomputable def chartFamilyY (i : (algStrOfAffine f).datum.J) :
    Spec.locallyRingedSpaceObj (CommRingCat.of ((algStrOfAffine f).datum.C i)) ⟶
      Y.toLocallyRingedSpace :=
  match i with
  | ⟨false⟩ => (chartToY0 f).toLRSHom
  | ⟨true⟩ => (chartToY1 f).toLRSHom

lemma chartFamilyY_compat (i j : (algStrOfAffine f).datum.J) (hij : i ≠ j) :
    specAwayMap ((algStrOfAffine f).datum.g i j) ≫ chartFamilyY f i =
      (specGlueIso ((algStrOfAffine f).datum.g i j) ((algStrOfAffine f).datum.g j i)
        ((algStrOfAffine f).datum.θ i j hij)).hom ≫
        specAwayMap ((algStrOfAffine f).datum.g j i) ≫ chartFamilyY f j := by
  rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
  · exact absurd rfl hij
  · exact congrArg Scheme.Hom.toLRSHom (compatY01 f)
  · exact congrArg Scheme.Hom.toLRSHom (compatY10 f)
  · exact absurd rfl hij

/-- **The relative spectrum of the chart algebra of `f` maps to `Y`**, by the charts
`Spec Γ(Y, f⁻¹ U_k) → Y`. -/
noncomputable def fromRelSpec : (algStrOfAffine f).scheme ⟶ Y :=
  ⟨(algStrOfAffine f).datum.desc (chartFamilyY f) (chartFamilyY_compat f)⟩

lemma schemeι_fromRelSpec_zero :
    (algStrOfAffine f).schemeι ⟨false⟩ ≫ fromRelSpec f = chartToY0 f :=
  Scheme.Hom.ext' ((algStrOfAffine f).datum.specι_desc _ (chartFamilyY_compat f) ⟨false⟩)

lemma schemeι_fromRelSpec_one :
    (algStrOfAffine f).schemeι ⟨true⟩ ≫ fromRelSpec f = chartToY1 f :=
  Scheme.Hom.ext' ((algStrOfAffine f).datum.specι_desc _ (chartFamilyY_compat f) ⟨true⟩)

/-! ### `ProjectiveLine.fromRelSpec` is an isomorphism over `ℙ¹_A` -/

lemma range_isIso_comp_base {X X' Z : Scheme.{u}} (g : X ⟶ X') [IsIso g] (h : X' ⟶ Z) :
    Set.range (g ≫ h).base = Set.range h.base := by
  have hs : Function.Surjective g.base := fun y ↦ ⟨g.homeomorph.symm y, by
    rw [← Scheme.Hom.homeomorph_apply]; exact g.homeomorph.apply_symm_apply y⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hs.range_eq, Set.image_univ]

lemma range_chartToY0 : Set.range (chartToY0 f).base = (f ⁻¹ᵁ U A 0 : Set Y) := by
  rw [chartToY0, range_isIso_comp_base, IsAffineOpen.range_fromSpec]

lemma range_chartToY1 : Set.range (chartToY1 f).base = (f ⁻¹ᵁ U A 1 : Set Y) := by
  rw [chartToY1, range_isIso_comp_base, IsAffineOpen.range_fromSpec]

lemma range_algebraMap_chartToY0 :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap _
      (Localization.Away (algStrOfAffine f).X0))) ≫ chartToY0 f).base =
      (f ⁻¹ᵁ (U A 0 ⊓ U A 1) : Set Y) := by
  rw [algebraMap_chartToY0, range_isIso_comp_base, IsAffineOpen.range_fromSpec]

lemma range_algebraMap_chartToY1 :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap _
      (Localization.Away (algStrOfAffine f).X1))) ≫ chartToY1 f).base =
      (f ⁻¹ᵁ (U A 0 ⊓ U A 1) : Set Y) := by
  rw [algebraMap_chartToY1, range_isIso_comp_base, IsAffineOpen.range_fromSpec]

lemma isIso_fromRelSpec_toLRSHom : IsIso (fromRelSpec f).toLRSHom := by
  refine (algStrOfAffine f).datum.isIso_desc (chartFamilyY f) (chartFamilyY_compat f)
    (fun i ↦ ?_) (fun i j hij ↦ ?_) ?_
  · rcases i with ⟨_ | _⟩
    · exact (inferInstance : IsOpenImmersion (chartToY0 f))
    · exact (inferInstance : IsOpenImmersion (chartToY1 f))
  · rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
    · exact absurd rfl hij
    · change Set.range (chartToY0 f).base ∩ Set.range (chartToY1 f).base ⊆
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap _
          (Localization.Away (algStrOfAffine f).X0))) ≫ chartToY0 f).base
      rw [range_chartToY0, range_chartToY1]
      intro y hy
      have hy' : y ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap _
          (Localization.Away (algStrOfAffine f).X0))) ≫ chartToY0 f).base := by
        rw [range_algebraMap_chartToY0]; exact hy
      exact hy'
    · change Set.range (chartToY1 f).base ∩ Set.range (chartToY0 f).base ⊆
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap _
          (Localization.Away (algStrOfAffine f).X1))) ≫ chartToY1 f).base
      rw [range_chartToY0, range_chartToY1]
      intro y hy
      have hy' : y ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap _
          (Localization.Away (algStrOfAffine f).X1))) ≫ chartToY1 f).base := by
        rw [range_algebraMap_chartToY1]; exact ⟨hy.2, hy.1⟩
      exact hy'
    · exact absurd rfl hij
  · refine Set.eq_univ_of_forall fun y ↦ ?_
    have hy : y ∈ f ⁻¹ᵁ (U A 0 ⊔ U A 1) := by rw [U_sup]; trivial
    rcases hy with hy | hy
    · exact Set.mem_iUnion.2 ⟨⟨false⟩, by
        change y ∈ Set.range (chartToY0 f).base
        rw [range_chartToY0]; exact hy⟩
    · exact Set.mem_iUnion.2 ⟨⟨true⟩, by
        change y ∈ Set.range (chartToY1 f).base
        rw [range_chartToY1]; exact hy⟩

/-- **`fromRelSpec f` is an isomorphism**: an affine scheme over `ℙ¹_A` is the relative spectrum of
its chart algebra. -/
instance isIso_fromRelSpec : IsIso (fromRelSpec f) := by
  haveI : IsIso (Scheme.forgetToLocallyRingedSpace.map (fromRelSpec f)) :=
    isIso_fromRelSpec_toLRSHom f
  exact isIso_of_reflects_iso (fromRelSpec f) Scheme.forgetToLocallyRingedSpace

lemma toRing0_polyHom0 (p : A[X]) :
    ring0Equiv f ((algStrOfAffine f).polyHom0 p) = chartPullback f 0 p := by
  have h : (ring0Equiv f).toRingHom.comp (algStrOfAffine f).polyHom0 = chartPullback f 0 := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [AlgStr.polyHom0, RingHom.coe_comp, Function.comp_apply,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      change (a • (1 : (twoChartRingsOfAffine f).R0) : (twoChartRingsOfAffine f).R0) = _
      rw [Algebra.smul_def, mul_one]
      rfl
    · simp only [AlgStr.polyHom0, RingHom.coe_comp, Function.comp_apply,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      exact ring0Equiv_X0 f
  exact RingHom.congr_fun h p

lemma toRing1_polyHom1 (p : A[X]) :
    ring1Equiv f ((algStrOfAffine f).polyHom1 p) = chartPullback f 1 p := by
  have h : (ring1Equiv f).toRingHom.comp (algStrOfAffine f).polyHom1 = chartPullback f 1 := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [AlgStr.polyHom1, RingHom.coe_comp, Function.comp_apply,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      change (a • (1 : (twoChartRingsOfAffine f).R1) : (twoChartRingsOfAffine f).R1) = _
      rw [Algebra.smul_def, mul_one]
      rfl
    · simp only [AlgStr.polyHom1, RingHom.coe_comp, Function.comp_apply,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      exact ring1Equiv_X1 f
  exact RingHom.congr_fun h p

lemma chartToY0_comp : chartToY0 f ≫ f = (algStrOfAffine f).chartMap0 := by
  rw [chartToY0, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_U A 0)
    (isAffineOpen_preimage_U f 0) le_rfl, ← Category.assoc, ← Spec.map_comp, AlgStr.chartMap0]
  congr 2
  ext s
  apply (ring0Equiv f).injective
  change ring0Equiv f ((ring0Equiv f).symm (f.appLE (U A 0) (f ⁻¹ᵁ U A 0) le_rfl s)) =
    ring0Equiv f ((algStrOfAffine f).polyHom0 (chartSections A 0 s))
  rw [RingEquiv.apply_symm_apply, toRing0_polyHom0, chartPullback, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply,
    Scheme.Hom.appLE_eq_app]

lemma chartToY1_comp : chartToY1 f ≫ f = (algStrOfAffine f).chartMap1 := by
  rw [chartToY1, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_U A 1)
    (isAffineOpen_preimage_U f 1) le_rfl, ← Category.assoc, ← Spec.map_comp, AlgStr.chartMap1]
  congr 2
  ext s
  apply (ring1Equiv f).injective
  change ring1Equiv f ((ring1Equiv f).symm (f.appLE (U A 1) (f ⁻¹ᵁ U A 1) le_rfl s)) =
    ring1Equiv f ((algStrOfAffine f).polyHom1 (chartSections A 1 s))
  rw [RingEquiv.apply_symm_apply, toRing1_polyHom1, chartPullback, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply,
    Scheme.Hom.appLE_eq_app]

/-- **`fromRelSpec f` lies over `ℙ¹_A`**: it identifies the structure morphism of the relative
spectrum with `f`. -/
lemma fromRelSpec_comp : fromRelSpec f ≫ f = (algStrOfAffine f).toP1 := by
  refine Scheme.Hom.ext' ((algStrOfAffine f).datum.hom_ext fun i ↦ ?_)
  rcases i with ⟨_ | _⟩
  · have h : (algStrOfAffine f).schemeι ⟨false⟩ ≫ fromRelSpec f ≫ f =
        (algStrOfAffine f).schemeι ⟨false⟩ ≫ (algStrOfAffine f).toP1 := by
      rw [← Category.assoc, schemeι_fromRelSpec_zero, AlgStr.schemeι_toP1_zero]
      exact chartToY0_comp f
    exact congrArg Scheme.Hom.toLRSHom h
  · have h : (algStrOfAffine f).schemeι ⟨true⟩ ≫ fromRelSpec f ≫ f =
        (algStrOfAffine f).schemeι ⟨true⟩ ≫ (algStrOfAffine f).toP1 := by
      rw [← Category.assoc, schemeι_fromRelSpec_one, AlgStr.schemeι_toP1_one]
      exact chartToY1_comp f
    exact congrArg Scheme.Hom.toLRSHom h

/-- **An affine scheme over `ℙ¹_A` is the relative spectrum of its chart algebra**, over
`ℙ¹_A`. -/
noncomputable def relSpecIso : (algStrOfAffine f).scheme ≅ Y := asIso (fromRelSpec f)

lemma relSpecIso_hom_comp : (relSpecIso f).hom ≫ f = (algStrOfAffine f).toP1 :=
  fromRelSpec_comp f

end ProjectiveLine
