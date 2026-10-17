/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartAlgebraStructureMap

/-!
# The relative spectrum of a chart algebra is affine over `ℙ¹_A`

For a commutative chart algebra `B` on `ℙ¹_A`, the preimage of the `k`-th chart under the structure
morphism `ProjectiveLine.ChartModule.AlgStr.toP1` is exactly the `k`-th chart of the relative
spectrum (`ProjectiveLine.ChartModule.AlgStr.toP1_preimage_U_zero`,
`ProjectiveLine.ChartModule.AlgStr.toP1_preimage_U_one`): a point of the other chart lying over
that chart lies over the overlap, hence in the image of the localization at the chart coordinate,
which is glued into the `k`-th chart. Hence the structure morphism is affine
(`ProjectiveLine.ChartModule.AlgStr.isAffineHom_toP1`), and its rings of sections over the
preimages of the charts are the rings of `B`
(`ProjectiveLine.ChartModule.AlgStr.sectionsEquiv0`,
`ProjectiveLine.ChartModule.AlgStr.sectionsEquiv1`).
-/

universe u

open Polynomial AlgebraicGeometry CategoryTheory

namespace ProjectiveLine

namespace ChartModule

namespace AlgStr

variable {A : Type u} [CommRing A] {M : ChartModule A} (B : AlgStr M)

lemma chartHom0_coord : B.chartHom0 (coord A 0) = B.X0 := by
  change B.polyHom0 (chartSections A 0 (coord A 0)) = B.X0
  rw [chartSections_coord]
  simp [polyHom0]

lemma chartHom1_coord : B.chartHom1 (coord A 1) = B.X1 := by
  change B.polyHom1 (chartSections A 1 (coord A 1)) = B.X1
  rw [chartSections_coord]
  simp [polyHom1]

lemma toP1_schemeι_zero_mem (y : Spec (CommRingCat.of B.Ring0)) :
    B.toP1.base ((B.schemeι ⟨false⟩).base y) ∈ U A 0 := by
  change (B.schemeι ⟨false⟩ ≫ B.toP1).base y ∈ U A 0
  rw [schemeι_toP1_zero, chartMap0]
  change (chartι A 0).base ((Spec.map B.chartHom0).base y) ∈ U A 0
  rw [← SetLike.mem_coe, ← IsAffineOpen.range_fromSpec (isAffineOpen_U A 0)]
  exact ⟨_, rfl⟩

lemma toP1_schemeι_one_mem (y : Spec (CommRingCat.of B.Ring1)) :
    B.toP1.base ((B.schemeι ⟨true⟩).base y) ∈ U A 1 := by
  change (B.schemeι ⟨true⟩ ≫ B.toP1).base y ∈ U A 1
  rw [schemeι_toP1_one, chartMap1]
  change (chartι A 1).base ((Spec.map B.chartHom1).base y) ∈ U A 1
  rw [← SetLike.mem_coe, ← IsAffineOpen.range_fromSpec (isAffineOpen_U A 1)]
  exact ⟨_, rfl⟩

/-- A point of the second chart lying over `U₀` lies in the first chart. -/
lemma mem_range_schemeι_zero_of_one (y : Spec (CommRingCat.of B.Ring1))
    (hy : B.toP1.base ((B.schemeι ⟨true⟩).base y) ∈ U A 0) :
    (B.schemeι ⟨true⟩).base y ∈ Set.range (B.schemeι ⟨false⟩).base := by
  have h1 : (Spec.map B.chartHom1).base y ∈ chartι A 1 ⁻¹ᵁ U A (1 : Fin 2).rev := by
    change (B.schemeι ⟨true⟩ ≫ B.toP1).base y ∈ U A 0 at hy
    rw [schemeι_toP1_one, chartMap1] at hy
    exact hy
  rw [chartι_preimage_rev] at h1
  have h2 : y ∈ PrimeSpectrum.basicOpen B.X1 := by
    rw [← chartHom1_coord]
    exact h1
  obtain ⟨z, hz⟩ : (show PrimeSpectrum B.Ring1 from y) ∈ Set.range (PrimeSpectrum.comap
      (algebraMap B.Ring1 (Localization.Away B.X1))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away B.X1) B.X1]
    exact h2
  have hne : (ULift.up true : ULift.{u} Bool) ≠ ULift.up false :=
    fun h ↦ Bool.noConfusion (congrArg ULift.down h)
  have e := congrArg (fun g ↦ g.base z) (B.datum.specAwayMap_comp_specι _ _ hne)
  refine ⟨((specGlueIso (B.datum.g ⟨true⟩ ⟨false⟩) (B.datum.g ⟨false⟩ ⟨true⟩)
    (B.datum.θ _ _ hne)).hom ≫ specAwayMap (B.datum.g ⟨false⟩ ⟨true⟩)).base z, ?_⟩
  rw [← hz]
  exact e.symm

/-- A point of the first chart lying over `U₁` lies in the second chart. -/
lemma mem_range_schemeι_one_of_zero (y : Spec (CommRingCat.of B.Ring0))
    (hy : B.toP1.base ((B.schemeι ⟨false⟩).base y) ∈ U A 1) :
    (B.schemeι ⟨false⟩).base y ∈ Set.range (B.schemeι ⟨true⟩).base := by
  have h1 : (Spec.map B.chartHom0).base y ∈ chartι A 0 ⁻¹ᵁ U A (0 : Fin 2).rev := by
    change (B.schemeι ⟨false⟩ ≫ B.toP1).base y ∈ U A 1 at hy
    rw [schemeι_toP1_zero, chartMap0] at hy
    exact hy
  rw [chartι_preimage_rev] at h1
  have h2 : y ∈ PrimeSpectrum.basicOpen B.X0 := by
    rw [← chartHom0_coord]
    exact h1
  obtain ⟨z, hz⟩ : (show PrimeSpectrum B.Ring0 from y) ∈ Set.range (PrimeSpectrum.comap
      (algebraMap B.Ring0 (Localization.Away B.X0))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away B.X0) B.X0]
    exact h2
  have hne : (ULift.up false : ULift.{u} Bool) ≠ ULift.up true :=
    fun h ↦ Bool.noConfusion (congrArg ULift.down h)
  have e := congrArg (fun g ↦ g.base z) (B.datum.specAwayMap_comp_specι _ _ hne)
  refine ⟨((specGlueIso (B.datum.g ⟨false⟩ ⟨true⟩) (B.datum.g ⟨true⟩ ⟨false⟩)
    (B.datum.θ _ _ hne)).hom ≫ specAwayMap (B.datum.g ⟨true⟩ ⟨false⟩)).base z, ?_⟩
  rw [← hz]
  exact e.symm

/-- **The preimage of the first chart is the first chart of the relative spectrum.** -/
lemma toP1_preimage_U_zero : B.toP1 ⁻¹ᵁ U A 0 = (B.schemeι ⟨false⟩).opensRange := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, y, rfl⟩ := B.datum.specScheme_jointly_surjective x
    rcases i with ⟨_ | _⟩
    · exact ⟨y, rfl⟩
    · exact B.mem_range_schemeι_zero_of_one y hx
  · rintro ⟨y, rfl⟩
    exact B.toP1_schemeι_zero_mem y

/-- **The preimage of the second chart is the second chart of the relative spectrum.** -/
lemma toP1_preimage_U_one : B.toP1 ⁻¹ᵁ U A 1 = (B.schemeι ⟨true⟩).opensRange := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, y, rfl⟩ := B.datum.specScheme_jointly_surjective x
    rcases i with ⟨_ | _⟩
    · exact B.mem_range_schemeι_one_of_zero y hx
    · exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact B.toP1_schemeι_one_mem y

/-- **The structure morphism of the relative spectrum is affine.** -/
instance isAffineHom_toP1 : IsAffineHom B.toP1 := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x ↦ ?_
  have hx : x ∈ U A 0 ⊔ U A 1 := by rw [U_sup]; trivial
  rcases hx with hx | hx
  · refine ⟨U A 0, hx, isAffineOpen_U A 0, ?_⟩
    rw [toP1_preimage_U_zero]
    exact B.datum.isAffineOpen_specSchemeι _
  · refine ⟨U A 1, hx, isAffineOpen_U A 1, ?_⟩
    rw [toP1_preimage_U_one]
    exact B.datum.isAffineOpen_specSchemeι _

lemma top_le_preimage_zero : ⊤ ≤ B.schemeι ⟨false⟩ ⁻¹ᵁ (B.toP1 ⁻¹ᵁ U A 0) :=
  fun y _ ↦ B.toP1_schemeι_zero_mem y

lemma top_le_preimage_one : ⊤ ≤ B.schemeι ⟨true⟩ ⁻¹ᵁ (B.toP1 ⁻¹ᵁ U A 1) :=
  fun y _ ↦ B.toP1_schemeι_one_mem y

/-- Restriction of sections over the preimage of `U₀` to the first chart, `Γ(f⁻¹ U₀) → B₀`. -/
noncomputable def sectionsHom0 :
    Γ(B.scheme, B.toP1 ⁻¹ᵁ U A 0) ⟶ CommRingCat.of B.Ring0 :=
  (B.schemeι ⟨false⟩).appLE _ ⊤ B.top_le_preimage_zero ≫ (Scheme.ΓSpecIso _).hom

/-- Restriction of sections over the preimage of `U₁` to the second chart, `Γ(f⁻¹ U₁) → B₁`. -/
noncomputable def sectionsHom1 :
    Γ(B.scheme, B.toP1 ⁻¹ᵁ U A 1) ⟶ CommRingCat.of B.Ring1 :=
  (B.schemeι ⟨true⟩).appLE _ ⊤ B.top_le_preimage_one ≫ (Scheme.ΓSpecIso _).hom

/-- **The pullback of functions on `U₀` to the first chart is `A[X] → B₀`.** -/
lemma app_sectionsHom0 : B.toP1.app (U A 0) ≫ B.sectionsHom0 = B.chartHom0 := by
  rw [sectionsHom0, ← Category.assoc, ← Scheme.Hom.comp_appLE]
  have key : ∀ (g : Spec (CommRingCat.of B.Ring0) ⟶ ProjectiveLine.scheme A)
      (_ : g = B.chartMap0) (e : ⊤ ≤ g ⁻¹ᵁ U A 0),
      g.appLE (U A 0) ⊤ e ≫ (Scheme.ΓSpecIso _).hom = B.chartHom0 := by
    rintro g rfl e
    change (Spec.map B.chartHom0 ≫ chartι A 0).appLE (U A 0) ⊤ e ≫ _ = _
    rw [Scheme.Hom.comp_appLE, IsAffineOpen.fromSpec_app_self, Category.assoc,
      Category.assoc, Scheme.Hom.map_appLE_assoc]
    have h : (Spec.map B.chartHom0).appLE ⊤ ⊤ le_top = (Spec.map B.chartHom0).appTop :=
      Scheme.Hom.appLE_eq_app _
    erw [h, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact key _ B.schemeι_toP1_zero _

/-- **The pullback of functions on `U₁` to the second chart is `A[Y] → B₁`.** -/
lemma app_sectionsHom1 : B.toP1.app (U A 1) ≫ B.sectionsHom1 = B.chartHom1 := by
  rw [sectionsHom1, ← Category.assoc, ← Scheme.Hom.comp_appLE]
  have key : ∀ (g : Spec (CommRingCat.of B.Ring1) ⟶ ProjectiveLine.scheme A)
      (_ : g = B.chartMap1) (e : ⊤ ≤ g ⁻¹ᵁ U A 1),
      g.appLE (U A 1) ⊤ e ≫ (Scheme.ΓSpecIso _).hom = B.chartHom1 := by
    rintro g rfl e
    change (Spec.map B.chartHom1 ≫ chartι A 1).appLE (U A 1) ⊤ e ≫ _ = _
    rw [Scheme.Hom.comp_appLE, IsAffineOpen.fromSpec_app_self, Category.assoc,
      Category.assoc, Scheme.Hom.map_appLE_assoc]
    have h : (Spec.map B.chartHom1).appLE ⊤ ⊤ le_top = (Spec.map B.chartHom1).appTop :=
      Scheme.Hom.appLE_eq_app _
    erw [h, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact key _ B.schemeι_toP1_one _

instance : IsIso B.sectionsHom0 := by
  have i : B.schemeι ⟨false⟩ ''ᵁ ⊤ = B.toP1 ⁻¹ᵁ U A 0 :=
    (Scheme.Hom.image_top_eq_opensRange _).trans B.toP1_preimage_U_zero.symm
  have h : (B.schemeι ⟨false⟩).appLE _ ⊤ B.top_le_preimage_zero =
      B.scheme.presheaf.map (eqToHom i).op ≫ ((B.schemeι ⟨false⟩).appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE']
  rw [sectionsHom0, h]
  infer_instance

instance : IsIso B.sectionsHom1 := by
  have i : B.schemeι ⟨true⟩ ''ᵁ ⊤ = B.toP1 ⁻¹ᵁ U A 1 :=
    (Scheme.Hom.image_top_eq_opensRange _).trans B.toP1_preimage_U_one.symm
  have h : (B.schemeι ⟨true⟩).appLE _ ⊤ B.top_le_preimage_one =
      B.scheme.presheaf.map (eqToHom i).op ≫ ((B.schemeι ⟨true⟩).appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE']
  rw [sectionsHom1, h]
  infer_instance

/-- **The sections of the relative spectrum over the preimage of `U₀` are `B₀`.** -/
noncomputable def sectionsEquiv0 : Γ(B.scheme, B.toP1 ⁻¹ᵁ U A 0) ≃+* B.Ring0 :=
  (asIso B.sectionsHom0).commRingCatIsoToRingEquiv

/-- **The sections of the relative spectrum over the preimage of `U₁` are `B₁`.** -/
noncomputable def sectionsEquiv1 : Γ(B.scheme, B.toP1 ⁻¹ᵁ U A 1) ≃+* B.Ring1 :=
  (asIso B.sectionsHom1).commRingCatIsoToRingEquiv

lemma sectionsEquiv0_app (s : Γ(ProjectiveLine.scheme A, U A 0)) :
    B.sectionsEquiv0 (B.toP1.app (U A 0) s) = B.chartHom0 s :=
  ConcreteCategory.congr_hom B.app_sectionsHom0 s

lemma sectionsEquiv1_app (s : Γ(ProjectiveLine.scheme A, U A 1)) :
    B.sectionsEquiv1 (B.toP1.app (U A 1) s) = B.chartHom1 s :=
  ConcreteCategory.congr_hom B.app_sectionsHom1 s

/-- The chart coordinate pulls back to `X₀`. -/
lemma sectionsEquiv0_coord : B.sectionsEquiv0 (B.toP1.app (U A 0) (coord A 0)) = B.X0 := by
  rw [sectionsEquiv0_app, chartHom0_coord]

/-- The chart coordinate pulls back to `X₁`. -/
lemma sectionsEquiv1_coord : B.sectionsEquiv1 (B.toP1.app (U A 1) (coord A 1)) = B.X1 := by
  rw [sectionsEquiv1_app, chartHom1_coord]

end AlgStr

end ChartModule

end ProjectiveLine
