/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ProjectiveLineUnit

/-!
# A quasi-coherent module on `ℙ¹_A` is isomorphic to the glued module of its chart module

`ProjectiveLine.etaGlue F : F ⟶ (chartModule F).glue` is an isomorphism for quasi-coherent `F`
(`ProjectiveLine.isIso_etaGlue`), and its chart module is `ChartModule.toGlue`
(`ProjectiveLine.chartModuleMap_etaGlue`).
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite AlgebraicGeometry.Scheme.Modules
  Polynomial LaurentPolynomial

namespace ProjectiveLine

variable {A : Type u} [CommRing A]

instance isOpenImmersion_chartι01 : IsOpenImmersion (Spec.map (ρ A 0) ≫ chartι A 0) := by
  rw [IsAffineOpen.map_fromSpec (isAffineOpen_U A 0) (isAffineOpen_U_inf A)]
  infer_instance

lemma image_chartι01_top : (Spec.map (ρ A 0) ≫ chartι A 0) ''ᵁ ⊤ = U A 0 ⊓ U A 1 := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  apply TopologicalSpace.Opens.ext
  change Set.range (Spec.map (ρ A 0) ≫ chartι A 0) = _
  rw [IsAffineOpen.map_fromSpec (isAffineOpen_U A 0) (isAffineOpen_U_inf A)]
  exact (isAffineOpen_U_inf A).range_fromSpec

/-- `hom_ext_pushforward_tilde`, with the image of the open immersion named. -/
lemma hom_ext_pushforward_tilde' {X : Scheme.{u}} {R' : CommRingCat.{u}} (f : Spec R' ⟶ X)
    [IsOpenImmersion f] (P : X.Modules) [IsIso (Scheme.Modules.fromTildeΓ (R := R') (P.restrict f))]
    (M : ModuleCat.{u} R') {α β : P ⟶ (pushforward f).obj ((tilde.functor R').obj M)}
    (W : X.Opens) (hW : f ''ᵁ ⊤ = W) (h : ∀ x : Γ(P, W), α.app W x = β.app W x) : α = β := by
  subst hW
  exact hom_ext_pushforward_tilde f P M h

variable (F : (scheme A).Modules) [F.IsQuasicoherent]

lemma tA_pow_apply' (k : ℕ) (z : (chartModule F).M01) :
    ((chartModule F).t ^ k) z = smulA F (transition A 1 ^ k) z :=
  (tA_pow_apply F k z)

/-- Cancelling the action of a unit of `Γ(U₀ ∩ U₁)`. -/
lemma smul_cancel_G01 {c : R01 A} (hc : IsUnit c)
    {y y' : secA (chartModule F).G01 (U A 0 ⊓ U A 1)}
    (h : smulA (chartModule F).G01 c y = smulA (chartModule F).G01 c y') : y = y' :=
  MulAction.injective (β := Γ((chartModule F).G01, U A 0 ⊓ U A 1)) hc.unit h

lemma αφ0_app (s : Γ(F, U A 0 ⊓ U A 1)) :
    (α0 F ≫ (chartModule F).φ0).app (U A 0 ⊓ U A 1) s = (chartModule F).e01 s := by
  obtain ⟨m, k, hk⟩ := exists_pow_smul_eq_res' (isAffineOpen_U A 0) F (coord A 0)
    (basicOpen_coord_zero (A := A)) inf_le_left s
  have hc : IsUnit (ρ A 0 (coord A 0 ^ k)) := by
    rw [ChartModule.ρ_coord_zero_pow]
    exact (isUnit_transition A 1).pow k
  refine smul_cancel_G01 F hc ?_
  have s1 : (chartModule F).φ0.app (U A 0) ((chartModule F).e0 m) =
      tilde.toOpen (chartModule F).mod01 ((Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ U A 0)
        ((chartModule F).r0 m) :=
    (ChartModule.ψ0_toOpen (chartModule F) (chartι A 0 ⁻¹ᵁ U A 0) m).trans
      (tilde_toOpen_res (chartModule F).mod01
        (homOfLE (le_top : (Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ U A 0 ≤ ⊤)) _)
  have s2 : ∀ z, (chartModule F).G01.presheaf.map (homOfLE inf_le_left).op
      (tilde.toOpen (chartModule F).mod01 ((Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ U A 0) z) =
        (chartModule F).e01 z := fun z ↦
    tilde_toOpen_res (chartModule F).mod01 (homOfLE (Scheme.Hom.preimage_mono _
      (inf_le_left : U A 0 ⊓ U A 1 ≤ U A 0))) z
  have e1 : (α0 F ≫ (chartModule F).φ0).app (U A 0 ⊓ U A 1)
      (F.presheaf.map (homOfLE inf_le_left).op m) = (chartModule F).e01
        ((chartModule F).r0 m) := by
    rw [app_res, Hom.comp_app, ConcreteCategory.comp_apply, α0_app_self, s1]
    exact s2 _
  have e2 : smulA (chartModule F).G01 (ρ A 0 (coord A 0 ^ k)) ((chartModule F).e01 s) =
      (chartModule F).e01 ((chartModule F).r0 m) := by
    refine (ChartModule.smulA_e01 _ _ s).trans (congrArg (chartModule F).e01 ?_)
    rw [ChartModule.act01_ρ_coord_zero_pow, tA_pow_apply', ← ChartModule.ρ_coord_zero_pow]
    exact hk
  rw [e2, ← e1]
  refine Eq.trans ?_ (congrArg _ hk)
  exact (Scheme.Modules.Hom.app_smul (α0 F ≫ (chartModule F).φ0) _ s).symm

lemma αφ1_app (s : Γ(F, U A 0 ⊓ U A 1)) :
    (α1 F ≫ (chartModule F).φ1).app (U A 0 ⊓ U A 1) s = (chartModule F).e01 s := by
  obtain ⟨m, k, hk⟩ := exists_pow_smul_eq_res' (isAffineOpen_U A 1) F (coord A 1)
    (basicOpen_coord_one (A := A)) inf_le_right s
  have hc : IsUnit (ρ A 1 (coord A 1 ^ k)) := by
    rw [ChartModule.ρ_coord_one_pow]
    exact (isUnit_transition A (-1)).pow k
  refine smul_cancel_G01 F hc ?_
  have h : (Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ U A 1 =
      (Spec.map (ρ A 1) ≫ chartι A 1) ⁻¹ᵁ U A 1 := by rw [chartι_comp]
  have s1 : (chartModule F).φ1.app (U A 1) ((chartModule F).e1 m) =
      tilde.toOpen (chartModule F).mod01 ((Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ U A 1)
        ((chartModule F).r1 m) :=
    ((chartModule F).φ1_app_apply _ _).trans ((congrArg (ConcreteCategory.hom
      ((tilde (chartModule F).mod01).presheaf.map (eqToHom h).op))
        ((ChartModule.ψ1_toOpen (chartModule F) (chartι A 1 ⁻¹ᵁ U A 1) m).trans
          (tilde_toOpen_res (chartModule F).mod01
            (homOfLE (le_top : (Spec.map (ρ A 1) ≫ chartι A 1) ⁻¹ᵁ U A 1 ≤ ⊤)) _))).trans
        (tilde_toOpen_res (chartModule F).mod01 (eqToHom h) _))
  have s2 : ∀ z, (chartModule F).G01.presheaf.map (homOfLE inf_le_right).op
      (tilde.toOpen (chartModule F).mod01 ((Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ U A 1) z) =
        (chartModule F).e01 z := fun z ↦
    tilde_toOpen_res (chartModule F).mod01 (homOfLE (Scheme.Hom.preimage_mono _
      (inf_le_right : U A 0 ⊓ U A 1 ≤ U A 1))) z
  have e1 : (α1 F ≫ (chartModule F).φ1).app (U A 0 ⊓ U A 1)
      (F.presheaf.map (homOfLE inf_le_right).op m) = (chartModule F).e01
        ((chartModule F).r1 m) := by
    rw [app_res, Hom.comp_app, ConcreteCategory.comp_apply, α1_app_self, s1]
    exact s2 _
  have e2 : smulA (chartModule F).G01 (ρ A 1 (coord A 1 ^ k)) ((chartModule F).e01 s) =
      (chartModule F).e01 ((chartModule F).r1 m) := by
    refine (ChartModule.smulA_e01 _ _ s).trans (congrArg (chartModule F).e01 ?_)
    rw [ChartModule.act01_ρ_coord_one_pow]
    refine (tA_symm_pow_apply F k s).trans ?_
    rw [← ChartModule.ρ_coord_one_pow]
    exact hk
  rw [e2, ← e1]
  refine Eq.trans ?_ (congrArg _ hk)
  exact (Scheme.Modules.Hom.app_smul (α1 F ≫ (chartModule F).φ1) _ s).symm

lemma α_compat : α0 F ≫ (chartModule F).φ0 = α1 F ≫ (chartModule F).φ1 := by
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := R01 A)
      (F.restrict (Spec.map (ρ A 0) ≫ chartι A 0))) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R01 A) _
  exact hom_ext_pushforward_tilde' (Spec.map (ρ A 0) ≫ chartι A 0) F (chartModule F).mod01
    (U A 0 ⊓ U A 1) image_chartι01_top fun x ↦ (αφ0_app F x).trans (αφ1_app F x).symm

/-- **The comparison `F → glue (chartModule F)`.** -/
noncomputable def etaGlue : F ⟶ (chartModule F).glue :=
  fiberProd.lift (α0 F) (α1 F) (α_compat F)

/-- **A quasi-coherent module on `ℙ¹_A` is the glued module of its chart module.** -/
instance isIso_etaGlue : IsIso (etaGlue F) := by
  refine isIso_of_locally _ fun x ↦ ?_
  have hx : x ∈ U A 0 ⊔ U A 1 := by rw [U_sup]; trivial
  rcases TopologicalSpace.Opens.mem_sup.1 hx with h | h
  · exact ⟨U A 0, h, fun W hW ↦ (Function.Bijective.of_comp_iff'
      ((chartModule F).glue_fst_bijective W hW) _).1 (α0_app_bijective F W hW)⟩
  · exact ⟨U A 1, h, fun W hW ↦ (Function.Bijective.of_comp_iff'
      ((chartModule F).glue_snd_bijective W hW) _).1 (α1_app_bijective F W hW)⟩

/-- The chart module of `etaGlue F` is `toGlue`. -/
lemma chartModuleMap_etaGlue : chartModuleMap (etaGlue F) = (chartModule F).toGlue :=
  ChartModule.Hom.ext_of_f0_f1
    (LinearMap.ext fun s ↦ (chartModule F).fst0.injective
      ((α0_app_self F s).trans ((chartModule F).fst0.apply_symm_apply _).symm))
    (LinearMap.ext fun s ↦ (chartModule F).snd1.injective
      ((α1_app_self F s).trans ((chartModule F).snd1.apply_symm_apply _).symm))

end ProjectiveLine
