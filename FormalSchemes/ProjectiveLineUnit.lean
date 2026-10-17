/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ProjectiveLineGlueIso
import FormalSchemes.QcohHomExt
import FormalSchemes.ModulesLocalIso

/-!
# A quasi-coherent module on `ℙ¹_A` is the glued module of its chart module

For a quasi-coherent module `F` on `ℙ¹_A`, the restriction of `F` to the chart `U_k` is the `~` of
`Γ(F, U_k)`; this gives morphisms `F → Ñ_k` (`N = chartModule F`) on `ℙ¹_A`, bijective on
sections over the opens contained in `U_k`.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite AlgebraicGeometry.Scheme.Modules
  Polynomial LaurentPolynomial

namespace ProjectiveLine

variable {A : Type u} [CommRing A] (F : (scheme A).Modules)

/-- Multiplication by functions on `Γ(F, W)`, as a ring homomorphism. -/
noncomputable def smulRingHom (W : (scheme A).Opens) :
    Γ(scheme A, W) →+* Module.End A (secA F W) where
  toFun := smulA F
  map_one' := LinearMap.ext fun m ↦ one_smul _ (show Γ(F, W) from m)
  map_mul' r s := LinearMap.ext fun m ↦ mul_smul r s (show Γ(F, W) from m)
  map_zero' := LinearMap.ext fun m ↦ zero_smul _ (show Γ(F, W) from m)
  map_add' r s := LinearMap.ext fun m ↦ add_smul r s (show Γ(F, W) from m)

lemma chartSections_symm_C (k : Fin 2) (a : A) :
    (chartSections A k).symm (Polynomial.C a) = secMap A (U A k) a :=
  (chartSections A k).symm_apply_eq.2 (chartSections_secMap k a).symm

lemma chartSections_symm_X (k : Fin 2) :
    (chartSections A k).symm Polynomial.X = coord A k :=
  (chartSections A k).symm_apply_eq.2 (chartSections_coord k).symm

variable [F.IsQuasicoherent]

lemma chartModule_act0 (r : R A 0) : (chartModule F).act0 r = smulA F r := by
  obtain ⟨p, rfl⟩ := (chartSections A 0).symm.surjective r
  have h : ((Polynomial.aeval (chartModule F).x0).toRingHom : A[X] →+* _) =
      (smulRingHom F (U A 0)).comp (chartSections A 0).symm.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      refine LinearMap.ext fun m ↦ ?_
      change Polynomial.aeval (chartModule F).x0 (Polynomial.C a) m =
        (chartSections A 0).symm (Polynomial.C a) • (show Γ(F, U A 0) from m)
      rw [Polynomial.aeval_C, chartSections_symm_C]
      rfl
    · refine (Polynomial.aeval_X (chartModule F).x0).trans ?_
      change smulA F (coord A 0) = smulA F ((chartSections A 0).symm Polynomial.X)
      rw [chartSections_symm_X]
  have := congrArg (fun φ : A[X] →+* Module.End A (secA F (U A 0)) ↦ φ p) h
  change Polynomial.aeval (chartModule F).x0 (chartSections A 0 ((chartSections A 0).symm p)) = _
  rw [RingEquiv.apply_symm_apply]
  exact this

lemma chartModule_act1 (r : R A 1) : (chartModule F).act1 r = smulA F r := by
  obtain ⟨p, rfl⟩ := (chartSections A 1).symm.surjective r
  have h : ((Polynomial.aeval (chartModule F).x1).toRingHom : A[X] →+* _) =
      (smulRingHom F (U A 1)).comp (chartSections A 1).symm.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      refine LinearMap.ext fun m ↦ ?_
      change Polynomial.aeval (chartModule F).x1 (Polynomial.C a) m =
        (chartSections A 1).symm (Polynomial.C a) • (show Γ(F, U A 1) from m)
      rw [Polynomial.aeval_C, chartSections_symm_C]
      rfl
    · refine (Polynomial.aeval_X (chartModule F).x1).trans ?_
      change smulA F (coord A 1) = smulA F ((chartSections A 1).symm Polynomial.X)
      rw [chartSections_symm_X]
  have := congrArg (fun φ : A[X] →+* Module.End A (secA F (U A 1)) ↦ φ p) h
  change Polynomial.aeval (chartModule F).x1 (chartSections A 1 ((chartSections A 1).symm p)) = _
  rw [RingEquiv.apply_symm_apply]
  exact this

lemma image_chartι_top (k : Fin 2) : chartι A k ''ᵁ ⊤ = U A k :=
  image_fromSpec_top (isAffineOpen_U A k)

lemma scheme_res_res {X : Scheme.{u}} {U V : X.Opens} (h1 : V ≤ U) (h2 : U ≤ V) (r : Γ(X, U)) :
    X.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE h1).op r) = r := by
  rw [scheme_presheaf_map_map_comp, scheme_presheaf_map_congr _ (𝟙 _)]
  simp

lemma inv_app_app_apply {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) [IsIso φ] (V : X.Opens)
    (y : Γ(M, V)) : (inv φ).app V (φ.app V y) = y := by
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, IsIso.hom_inv_id]
  rfl

lemma presheaf_res_res {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h1 : V ≤ U) (h2 : U ≤ V)
    (m : Γ(M, U)) : M.presheaf.map (homOfLE h2).op (M.presheaf.map (homOfLE h1).op m) = m := by
  rw [presheaf_map_map_comp, presheaf_map_congr M _ (𝟙 _)]
  simp

/-- `Γ(F|_{U_0}, ⊤) ≃ Γ(F, U_0)`, `Γ(U_0)`-linearly. -/
noncomputable def θ0 : (moduleSpecΓFunctor (R := R A 0)).obj (F.restrict (chartι A 0)) ≃ₗ[R A 0]
    (chartModule F).mod0 where
  toFun x := F.presheaf.map (homOfLE (image_chartι_top (A := A) 0).ge).op
    (show Γ(F, chartι A 0 ''ᵁ ⊤) from x)
  invFun y := F.presheaf.map (homOfLE (image_chartι_top (A := A) 0).le).op
    (show Γ(F, U A 0) from y)
  map_add' x y := map_add (ConcreteCategory.hom (F.presheaf.map
    (homOfLE (image_chartι_top (A := A) 0).ge).op)) (show Γ(F, chartι A 0 ''ᵁ ⊤) from x) y
  map_smul' r x := by
    have e1 := smul_restrict_fromSpec (isAffineOpen_U A 0) F ⊤ r x
    change F.presheaf.map _ (r • x) = (chartModule F).act0 r (F.presheaf.map _ x)
    exact (congrArg _ e1).trans ((Scheme.Modules.map_smul F _ _ _).trans
      ((congrArg (fun c : Γ(scheme A, U A 0) ↦ c • (show Γ(F, U A 0) from F.presheaf.map
        (homOfLE (image_chartι_top (A := A) 0).ge).op (show Γ(F, chartι A 0 ''ᵁ ⊤) from x)))
          (scheme_res_res _ _ r)).trans
        (LinearMap.congr_fun (chartModule_act0 F r) _).symm))
  left_inv x := presheaf_res_res F _ _ _
  right_inv y := presheaf_res_res F _ _ _

lemma θ0_apply (x : (moduleSpecΓFunctor (R := R A 0)).obj (F.restrict (chartι A 0))) :
    θ0 F x = F.presheaf.map (homOfLE (image_chartι_top (A := A) 0).ge).op
      (show Γ(F, chartι A 0 ''ᵁ ⊤) from x) := rfl

/-- `F|_{U_0} ≅ Γ(F, U_0)^~` on `Spec Γ(U_0)`. -/
noncomputable def β0 :
    F.restrict (chartι A 0) ⟶ (tilde.functor (R A 0)).obj (chartModule F).mod0 :=
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := R A 0) (F.restrict (chartι A 0))) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R A 0) _
  inv (Scheme.Modules.fromTildeΓ (R := R A 0) (F.restrict (chartι A 0))) ≫
    (tilde.functor (R A 0)).map (ModuleCat.ofHom
      (X := (moduleSpecΓFunctor (R := R A 0)).obj (F.restrict (chartι A 0)))
      (Y := (chartModule F).mod0) (θ0 F).toLinearMap)

/-- `F → Ñ_0` on `ℙ¹_A`, for `N = chartModule F`. -/
noncomputable def α0 : F ⟶ (chartModule F).G0 :=
  ((restrictAdjunction (chartι A 0)).homEquiv _ _) (β0 F)

lemma α0_app (W : (scheme A).Opens) (s : Γ(F, W)) :
    (α0 F).app W s = (β0 F).app (chartι A 0 ⁻¹ᵁ W)
      (F.presheaf.map (homOfLE (Scheme.Hom.image_preimage_le _ W)).op s) := by
  rw [α0, Adjunction.homEquiv_unit]
  rfl

/-- `Γ(F|_{U_1}, ⊤) ≃ Γ(F, U_1)`, `Γ(U_1)`-linearly. -/
noncomputable def θ1 : (moduleSpecΓFunctor (R := R A 1)).obj (F.restrict (chartι A 1)) ≃ₗ[R A 1]
    (chartModule F).mod1 where
  toFun x := F.presheaf.map (homOfLE (image_chartι_top (A := A) 1).ge).op
    (show Γ(F, chartι A 1 ''ᵁ ⊤) from x)
  invFun y := F.presheaf.map (homOfLE (image_chartι_top (A := A) 1).le).op
    (show Γ(F, U A 1) from y)
  map_add' x y := map_add (ConcreteCategory.hom (F.presheaf.map
    (homOfLE (image_chartι_top (A := A) 1).ge).op)) (show Γ(F, chartι A 1 ''ᵁ ⊤) from x) y
  map_smul' r x := by
    have e1 := smul_restrict_fromSpec (isAffineOpen_U A 1) F ⊤ r x
    change F.presheaf.map _ (r • x) = (chartModule F).act1 r (F.presheaf.map _ x)
    exact (congrArg _ e1).trans ((Scheme.Modules.map_smul F _ _ _).trans
      ((congrArg (fun c : Γ(scheme A, U A 1) ↦ c • (show Γ(F, U A 1) from F.presheaf.map
        (homOfLE (image_chartι_top (A := A) 1).ge).op (show Γ(F, chartι A 1 ''ᵁ ⊤) from x)))
          (scheme_res_res _ _ r)).trans
        (LinearMap.congr_fun (chartModule_act1 F r) _).symm))
  left_inv x := presheaf_res_res F _ _ _
  right_inv y := presheaf_res_res F _ _ _

lemma θ1_apply (x : (moduleSpecΓFunctor (R := R A 1)).obj (F.restrict (chartι A 1))) :
    θ1 F x = F.presheaf.map (homOfLE (image_chartι_top (A := A) 1).ge).op
      (show Γ(F, chartι A 1 ''ᵁ ⊤) from x) := rfl

/-- `F|_{U_1} ≅ Γ(F, U_1)^~` on `Spec Γ(U_1)`. -/
noncomputable def β1 :
    F.restrict (chartι A 1) ⟶ (tilde.functor (R A 1)).obj (chartModule F).mod1 :=
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := R A 1) (F.restrict (chartι A 1))) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R A 1) _
  inv (Scheme.Modules.fromTildeΓ (R := R A 1) (F.restrict (chartι A 1))) ≫
    (tilde.functor (R A 1)).map (ModuleCat.ofHom
      (X := (moduleSpecΓFunctor (R := R A 1)).obj (F.restrict (chartι A 1)))
      (Y := (chartModule F).mod1) (θ1 F).toLinearMap)

/-- `F → Ñ_1` on `ℙ¹_A`, for `N = chartModule F`. -/
noncomputable def α1 : F ⟶ (chartModule F).G1 :=
  ((restrictAdjunction (chartι A 1)).homEquiv _ _) (β1 F)

lemma α1_app (W : (scheme A).Opens) (s : Γ(F, W)) :
    (α1 F).app W s = (β1 F).app (chartι A 1 ⁻¹ᵁ W)
      (F.presheaf.map (homOfLE (Scheme.Hom.image_preimage_le _ W)).op s) := by
  rw [α1, Adjunction.homEquiv_unit]
  rfl

lemma α0_app_self (s : Γ(F, U A 0)) : (α0 F).app (U A 0) s = (chartModule F).e0 s := by
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := R A 0) (F.restrict (chartι A 0))) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R A 0) _
  have hx : θ0 F ((θ0 F).symm s) = s := (θ0 F).apply_symm_apply s
  have h1 : F.presheaf.map (homOfLE (Scheme.Hom.image_preimage_le _ (U A 0))).op s =
      (F.restrict (chartι A 0)).presheaf.map
        (homOfLE (le_top : chartι A 0 ⁻¹ᵁ U A 0 ≤ ⊤)).op ((θ0 F).symm s) :=
    (presheaf_map_map F (homOfLE (image_chartι_top (A := A) 0).le)
      (homOfLE (Scheme.Hom.image_mono _ le_top)) _ s).symm
  have h2 := ConcreteCategory.congr_hom
    (Scheme.Modules.toOpen_fromTildeΓ_app (R := R A 0) (F.restrict (chartι A 0))
      (chartι A 0 ⁻¹ᵁ U A 0)) ((θ0 F).symm s)
  have h3 := ConcreteCategory.congr_hom (tilde.toOpen_map_app (ModuleCat.ofHom
    (X := (moduleSpecΓFunctor (R := R A 0)).obj (F.restrict (chartι A 0)))
    (Y := (chartModule F).mod0) (θ0 F).toLinearMap) (chartι A 0 ⁻¹ᵁ U A 0))
      ((θ0 F).symm s)
  have h4 := (congrArg ((inv (Scheme.Modules.fromTildeΓ (R := R A 0)
    (F.restrict (chartι A 0)))).app (chartι A 0 ⁻¹ᵁ U A 0)) h2.symm).trans
      (inv_app_app_apply _ _ _)
  exact (α0_app F _ s).trans ((congrArg ((β0 F).app _) h1).trans
    ((congrArg (((tilde.functor (R A 0)).map _).app _) h4).trans
      (h3.trans (congrArg (tilde.toOpen (chartModule F).mod0 _) hx))))

instance isIso_β0 : IsIso (β0 F) := by
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := R A 0) (F.restrict (chartι A 0))) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R A 0) _
  haveI : IsIso (ModuleCat.ofHom
      (X := (moduleSpecΓFunctor (R := R A 0)).obj (F.restrict (chartι A 0)))
      (Y := (chartModule F).mod0) (θ0 F).toLinearMap) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (θ0 F).bijective
  unfold β0
  exact IsIso.comp_isIso' inferInstance (Functor.map_isIso (tilde.functor (R A 0)) (ModuleCat.ofHom
    (X := (moduleSpecΓFunctor (R := R A 0)).obj (F.restrict (chartι A 0)))
    (Y := (chartModule F).mod0) (θ0 F).toLinearMap))

lemma α0_app_bijective (W : (scheme A).Opens) (hW : W ≤ U A 0) :
    Function.Bijective ((α0 F).app W) := by
  rw [show ⇑((α0 F).app W) = ⇑((β0 F).app (chartι A 0 ⁻¹ᵁ W)) ∘
    ⇑(F.presheaf.map (homOfLE (Scheme.Hom.image_preimage_le _ W)).op) from funext (α0_app F W)]
  refine Function.Bijective.comp (ConcreteCategory.bijective_of_isIso _) ?_
  have e : chartι A 0 ''ᵁ (chartι A 0 ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, (isAffineOpen_U A 0).opensRange_fromSpec,
      inf_eq_right.2 hW]
  rw [show homOfLE (Scheme.Hom.image_preimage_le (chartι A 0) W) = eqToHom e from
    Subsingleton.elim _ _]
  exact ConcreteCategory.bijective_of_isIso _

lemma α1_app_self (s : Γ(F, U A 1)) : (α1 F).app (U A 1) s = (chartModule F).e1 s := by
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := R A 1) (F.restrict (chartι A 1))) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R A 1) _
  have hx : θ1 F ((θ1 F).symm s) = s := (θ1 F).apply_symm_apply s
  have h1 : F.presheaf.map (homOfLE (Scheme.Hom.image_preimage_le _ (U A 1))).op s =
      (F.restrict (chartι A 1)).presheaf.map
        (homOfLE (le_top : chartι A 1 ⁻¹ᵁ U A 1 ≤ ⊤)).op ((θ1 F).symm s) :=
    (presheaf_map_map F (homOfLE (image_chartι_top (A := A) 1).le)
      (homOfLE (Scheme.Hom.image_mono _ le_top)) _ s).symm
  have h2 := ConcreteCategory.congr_hom
    (Scheme.Modules.toOpen_fromTildeΓ_app (R := R A 1) (F.restrict (chartι A 1))
      (chartι A 1 ⁻¹ᵁ U A 1)) ((θ1 F).symm s)
  have h3 := ConcreteCategory.congr_hom (tilde.toOpen_map_app (ModuleCat.ofHom
    (X := (moduleSpecΓFunctor (R := R A 1)).obj (F.restrict (chartι A 1)))
    (Y := (chartModule F).mod1) (θ1 F).toLinearMap) (chartι A 1 ⁻¹ᵁ U A 1))
      ((θ1 F).symm s)
  have h4 := (congrArg ((inv (Scheme.Modules.fromTildeΓ (R := R A 1)
    (F.restrict (chartι A 1)))).app (chartι A 1 ⁻¹ᵁ U A 1)) h2.symm).trans
      (inv_app_app_apply _ _ _)
  exact (α1_app F _ s).trans ((congrArg ((β1 F).app _) h1).trans
    ((congrArg (((tilde.functor (R A 1)).map _).app _) h4).trans
      (h3.trans (congrArg (tilde.toOpen (chartModule F).mod1 _) hx))))

instance isIso_β1 : IsIso (β1 F) := by
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := R A 1) (F.restrict (chartι A 1))) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R A 1) _
  haveI : IsIso (ModuleCat.ofHom
      (X := (moduleSpecΓFunctor (R := R A 1)).obj (F.restrict (chartι A 1)))
      (Y := (chartModule F).mod1) (θ1 F).toLinearMap) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (θ1 F).bijective
  unfold β1
  exact IsIso.comp_isIso' inferInstance (Functor.map_isIso (tilde.functor (R A 1)) (ModuleCat.ofHom
    (X := (moduleSpecΓFunctor (R := R A 1)).obj (F.restrict (chartι A 1)))
    (Y := (chartModule F).mod1) (θ1 F).toLinearMap))

lemma α1_app_bijective (W : (scheme A).Opens) (hW : W ≤ U A 1) :
    Function.Bijective ((α1 F).app W) := by
  rw [show ⇑((α1 F).app W) = ⇑((β1 F).app (chartι A 1 ⁻¹ᵁ W)) ∘
    ⇑(F.presheaf.map (homOfLE (Scheme.Hom.image_preimage_le _ W)).op) from funext (α1_app F W)]
  refine Function.Bijective.comp (ConcreteCategory.bijective_of_isIso _) ?_
  have e : chartι A 1 ''ᵁ (chartι A 1 ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, (isAffineOpen_U A 1).opensRange_fromSpec,
      inf_eq_right.2 hW]
  rw [show homOfLE (Scheme.Hom.image_preimage_le (chartι A 1) W) = eqToHom e from
    Subsingleton.elim _ _]
  exact ConcreteCategory.bijective_of_isIso _

end ProjectiveLine
