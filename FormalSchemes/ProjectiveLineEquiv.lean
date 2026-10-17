/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ProjectiveLineEta
import FormalSchemes.ProjectiveLineGlueMap
import FormalSchemes.ChartModuleCat

/-!
# Quasi-coherent modules on `ℙ¹_A` are chart modules

The functor `F ↦ chartModule F` from quasi-coherent modules on `ℙ¹_A` to chart modules
(`ProjectiveLine.chartFunctor`) is an equivalence of categories
(`ProjectiveLine.chartEquivalence`): it is faithful and full by the comparison
`F ≅ glue (chartModule F)` (`ProjectiveLine.etaGlue`) and the naturality of
`ChartModule.toGlue`, and essentially surjective by `ChartModule.toGlue`.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite AlgebraicGeometry.Scheme.Modules

namespace ProjectiveLine

variable (A : Type u) [CommRing A]

/-- The category of quasi-coherent modules on `ℙ¹_A`. -/
abbrev QCoh := (SheafOfModules.isQuasicoherent (scheme A).ringCatSheaf).FullSubcategory

variable {A}

/-- **The chart-module functor** on quasi-coherent modules on `ℙ¹_A`. -/
noncomputable def chartFunctor : QCoh A ⥤ ChartModule A where
  obj F := chartModule F.obj
  map φ := chartModuleMap φ.hom
  map_id _ := ChartModule.Hom.ext' rfl rfl rfl
  map_comp φ ψ := chartModuleMap_comp φ.hom ψ.hom

lemma chartFunctor_map {F G : QCoh A} (φ : F ⟶ G) : chartFunctor.map φ = chartModuleMap φ.hom :=
  rfl

/-- Morphisms out of a quasi-coherent module into a glued module are determined by their chart
modules. -/
lemma hom_ext_glue {F : (scheme A).Modules} [F.IsQuasicoherent] {N : ChartModule A}
    {a b : F ⟶ N.glue} (h : chartModuleMap a = chartModuleMap b) : a = b := by
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := R A 0) (F.restrict (chartι A 0))) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R A 0) _
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := R A 1) (F.restrict (chartι A 1))) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R A 1) _
  apply fiberProd.hom_ext
  · refine hom_ext_pushforward_tilde' (chartι A 0) F N.mod0 (U A 0) (image_chartι_top 0)
      fun x ↦ ?_
    exact congrArg (fun χ ↦ (fiberProd.fst N.φ0 N.φ1).app (U A 0) (ChartModule.Hom.f0 χ x)) h
  · refine hom_ext_pushforward_tilde' (chartι A 1) F N.mod1 (U A 1) (image_chartι_top 1)
      fun x ↦ ?_
    exact congrArg (fun χ ↦ (fiberProd.snd N.φ0 N.φ1).app (U A 1) (ChartModule.Hom.f1 χ x)) h

instance : (chartFunctor (A := A)).Faithful where
  map_injective {F G} {φ ψ} h := by
    haveI : F.obj.IsQuasicoherent := F.property
    haveI : G.obj.IsQuasicoherent := G.property
    haveI := isIso_etaGlue G.obj
    apply ObjectProperty.hom_ext
    apply (cancel_mono (etaGlue G.obj)).1
    apply hom_ext_glue
    rw [chartModuleMap_comp, chartModuleMap_comp]
    exact congrArg (fun χ ↦ ChartModule.Hom.comp (chartModuleMap (etaGlue G.obj)) χ) h

instance : (chartFunctor (A := A)).Full where
  map_surjective {F G} f := by
    haveI : F.obj.IsQuasicoherent := F.property
    haveI : G.obj.IsQuasicoherent := G.property
    let ηF := etaGlue F.obj
    let ηG := etaGlue G.obj
    obtain ⟨ψ, -, hψ⟩ := (isIso_etaGlue G.obj).out
    let φ : @Quiver.Hom (scheme A).Modules _ F.obj G.obj := ηF ≫ ChartModule.glueMap f ≫ ψ
    refine ⟨ObjectProperty.homMk φ, ?_⟩
    have e1 : φ ≫ ηG = ηF ≫ ChartModule.glueMap f :=
      (Category.assoc _ _ _).trans (congrArg (ηF ≫ ·) ((Category.assoc _ _ _).trans
        ((congrArg (ChartModule.glueMap f ≫ ·) hψ).trans (Category.comp_id _))))
    have key : (chartModuleMap ηG).comp (chartModuleMap φ) = (chartModuleMap ηG).comp f :=
      (chartModuleMap_comp φ ηG).symm.trans ((congrArg chartModuleMap e1).trans
        ((chartModuleMap_comp ηF (ChartModule.glueMap f)).trans
          ((congrArg (ChartModule.Hom.comp (chartModuleMap (ChartModule.glueMap f)))
            (chartModuleMap_etaGlue F.obj)).trans ((ChartModule.toGlue_naturality f).trans
              (congrArg (fun χ ↦ ChartModule.Hom.comp χ f) (chartModuleMap_etaGlue G.obj).symm)))))
    rw [chartModuleMap_etaGlue] at key
    refine ChartModule.Hom.ext_of_f0_f1 (LinearMap.ext fun m ↦ ?_) (LinearMap.ext fun m ↦ ?_)
    · exact (chartModule G.obj).toGlue_bijective0.1
        (congrArg (fun χ ↦ ChartModule.Hom.f0 χ m) key)
    · exact (chartModule G.obj).toGlue_bijective1.1
        (congrArg (fun χ ↦ ChartModule.Hom.f1 χ m) key)

instance : (chartFunctor (A := A)).EssSurj where
  mem_essImage N := by
    haveI := ChartModule.Hom.isIso_of_bijective (M := N) (N := chartModule N.glue) N.toGlue
      N.toGlue_bijective0 N.toGlue_bijective1 N.toGlue_bijective01
    exact ⟨⟨N.glue, N.isQuasicoherent_glue⟩, ⟨(asIso (C := ChartModule A) N.toGlue).symm⟩⟩

instance : (chartFunctor (A := A)).IsEquivalence where

/-- **Quasi-coherent modules on `ℙ¹_A` are chart modules**: the chart-module functor is an
equivalence of categories. -/
noncomputable def chartEquivalence : QCoh A ≌ ChartModule A :=
  (chartFunctor (A := A)).asEquivalence

end ProjectiveLine
