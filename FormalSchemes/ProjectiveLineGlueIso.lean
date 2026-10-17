/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ProjectiveLineGlue

/-!
# The chart module of the glued module

For a chart module `N`, the chart module of the glued quasi-coherent module `N.glue` on `ℙ¹_A` is
isomorphic to `N` (`ProjectiveLine.ChartModule.glueIso`).
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite AlgebraicGeometry.Scheme.Modules
  Polynomial LaurentPolynomial HomogeneousLocalization

namespace ProjectiveLine

variable {A : Type u} [CommRing A]

/-! ### The structure map on the charts -/

lemma fromSpec_appTop_apply (k : Fin 2) (y : Γ(scheme A, ⊤)) :
    (isAffineOpen_U A k).fromSpec.appTop y =
      (Scheme.ΓSpecIso (R A k)).inv ((scheme A).presheaf.map (homOfLE le_top : U A k ⟶ ⊤).op y) :=
  (ConcreteCategory.congr_hom ((isAffineOpen_U A k).fromSpec_app_of_le ⊤ le_top) y).trans
    (by
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
      have hm : (homOfLE (le_top : (isAffineOpen_U A k).fromSpec ⁻¹ᵁ ⊤ ≤ ⊤)) =
          𝟙 (⊤ : (Spec (R A k)).Opens) := Subsingleton.elim _ _
      erw [hm, op_id, CategoryTheory.Functor.map_id]
      rfl)

lemma secMap_U (k : Fin 2) (a : A) :
    secMap A (U A k) a = Proj.awayToSection (grading A) (MvPolynomial.X k)
      (fromZeroRingHom (grading A) _ (constZero A a)) := by
  have hcomp : (isAffineOpen_U A k).fromSpec ≫ Proj.toSpecZero (grading A) =
      Spec.map (CommRingCat.ofHom (fromZeroRingHom (grading A)
        (Submonoid.powers (MvPolynomial.X k))) ≫
          Proj.awayToSection (grading A) (MvPolynomial.X k)) := by
    rw [fromSpec_eq]
    exact (Category.assoc _ _ _).trans ((congrArg (Spec.map _ ≫ ·)
      (Proj.awayι_toSpecZero _ _ _ _)).trans (Spec.map_comp _ _).symm)
  have h := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop hcomp)
    ((Scheme.ΓSpecIso (CommRingCat.of (grading A 0))).inv (constZero A a))
  have h2 := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (fromZeroRingHom (grading A) (Submonoid.powers (MvPolynomial.X k))) ≫
      Proj.awayToSection (grading A) (MvPolynomial.X k))) (constZero A a)
  apply (Scheme.ΓSpecIso (R A k)).commRingCatIsoToRingEquiv.symm.injective
  refine (fromSpec_appTop_apply k (structMap A a)).symm.trans ?_
  exact h.trans h2.symm

lemma chartSections_secMap (k : Fin 2) (a : A) :
    chartSections A k (secMap A (U A k) a) = Polynomial.C a := by
  rw [secMap_U, chartSections_awayToSection, chartEquiv_fromZero]

lemma overlapSections_secMap (a : A) :
    overlapSections A (secMap A (U A 0 ⊓ U A 1) a) = LaurentPolynomial.C a := by
  rw [← res_secMap A (inf_le_left : U A 0 ⊓ U A 1 ≤ U A 0), overlapSections_res_zero,
    chartSections_secMap, Polynomial.toLaurent_C]

/-! ### Actions on sections of pushforwards of `~` -/

lemma pushforward_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (T : X.Modules) (W : Y.Opens)
    (r : Γ(Y, W)) (x : Γ((pushforward f).obj T, W)) :
    r • x = (show Γ(T, f ⁻¹ᵁ W) from f.app W r • (show Γ(T, f ⁻¹ᵁ W) from x)) := rfl

lemma tilde_toOpen_smul {R' : CommRingCat.{u}} (M : ModuleCat.{u} R') (V : (Spec R').Opens)
    (r : R') (m : M) :
    (Spec R').presheaf.map V.leTop.op ((Scheme.ΓSpecIso R').inv r) •
      (show Γ(tilde M, V) from tilde.toOpen M V m) = tilde.toOpen M V (r • m) :=
  ((tilde.toOpen M V).hom.map_smul r m).symm

lemma tilde_toOpen_res {R' : CommRingCat.{u}} (M : ModuleCat.{u} R') {V V' : (Spec R').Opens}
    (i : V' ⟶ V) (m : M) :
    (tilde M).presheaf.map i.op (show Γ(tilde M, V) from tilde.toOpen M V m) =
      tilde.toOpen M V' m := rfl

lemma tilde_toOpen_bijective_of_eq_top {R' : CommRingCat.{u}} (M : ModuleCat.{u} R')
    (V : (Spec R').Opens) (h : V = ⊤) : Function.Bijective (tilde.toOpen M V) := by
  subst h
  exact ConcreteCategory.bijective_of_isIso _

lemma chartι_app_self (k : Fin 2) (s : Γ(scheme A, U A k)) :
    (chartι A k).app (U A k) s =
      (Spec (R A k)).presheaf.map (chartι A k ⁻¹ᵁ U A k).leTop.op ((Scheme.ΓSpecIso _).inv s) :=
  (isAffineOpen_U A k).fromSpec_app_self_apply s

lemma preimage_U01 : (Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ (U A 0 ⊓ U A 1) = ⊤ := by
  rw [IsAffineOpen.map_fromSpec (isAffineOpen_U A 0) (isAffineOpen_U_inf A)]
  exact (isAffineOpen_U_inf A).fromSpec_preimage_self

lemma chartι01_app (s : R01 A) :
    (Spec.map (ρ A 0) ≫ chartι A 0).app (U A 0 ⊓ U A 1) s =
      (Spec (R01 A)).presheaf.map ((Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ
        (U A 0 ⊓ U A 1)).leTop.op ((Scheme.ΓSpecIso _).inv s) := by
  have e := ConcreteCategory.congr_hom (Scheme.Hom.congr_app (IsAffineOpen.map_fromSpec
    (isAffineOpen_U A 0) (isAffineOpen_U_inf A) (homOfLE inf_le_left).op) (U A 0 ⊓ U A 1)) s
  refine e.trans ?_
  erw [CommRingCat.comp_apply, (isAffineOpen_U_inf A).fromSpec_app_self_apply,
    ← CommRingCat.comp_apply, ← Functor.map_comp]

namespace ChartModule

variable (N : ChartModule A)

lemma act0_secMap (a : A) (m : N.M0) : N.act0 (secMap A (U A 0) a) m = a • m := by
  change Polynomial.aeval N.x0 (chartSections A 0 (secMap A (U A 0) a)) m = _
  rw [chartSections_secMap, Polynomial.aeval_C]
  rfl

lemma act1_secMap (a : A) (m : N.M1) : N.act1 (secMap A (U A 1) a) m = a • m := by
  change Polynomial.aeval N.x1 (chartSections A 1 (secMap A (U A 1) a)) m = _
  rw [chartSections_secMap, Polynomial.aeval_C]
  rfl

lemma act01_secMap (a : A) (z : N.M01) : N.act01 (secMap A (U A 0 ⊓ U A 1) a) z = a • z := by
  change N.lev (overlapSections A (secMap A (U A 0 ⊓ U A 1) a)) z = _
  rw [overlapSections_secMap]
  simpa using N.lev_C_mul_T a 0 z

lemma act01_transition_one (z : N.M01) : N.act01 (transition A 1) z = N.t z := by
  simpa using N.act01_transition_pow 1 1 z

lemma G0_smul (s : Γ(scheme A, U A 0)) (m : N.mod0) :
    s • (show Γ(N.G0, U A 0) from tilde.toOpen N.mod0 (chartι A 0 ⁻¹ᵁ U A 0) m) =
      tilde.toOpen N.mod0 (chartι A 0 ⁻¹ᵁ U A 0) (N.act0 s m) := by
  refine (pushforward_smul _ _ _ s _).trans ?_
  rw [chartι_app_self]
  exact tilde_toOpen_smul N.mod0 _ s m

lemma G1_smul (s : Γ(scheme A, U A 1)) (m : N.mod1) :
    s • (show Γ(N.G1, U A 1) from tilde.toOpen N.mod1 (chartι A 1 ⁻¹ᵁ U A 1) m) =
      tilde.toOpen N.mod1 (chartι A 1 ⁻¹ᵁ U A 1) (N.act1 s m) := by
  refine (pushforward_smul _ _ _ s _).trans ?_
  rw [chartι_app_self]
  exact tilde_toOpen_smul N.mod1 _ s m

lemma G01_smul (s : R01 A) (z : N.mod01) :
    s • (show Γ(N.G01, U A 0 ⊓ U A 1) from
      tilde.toOpen N.mod01 ((Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ (U A 0 ⊓ U A 1)) z) =
      tilde.toOpen N.mod01 _ (N.act01 s z) := by
  refine (pushforward_smul _ _ _ s _).trans ?_
  rw [chartι01_app]
  exact tilde_toOpen_smul N.mod01 _ s z

/-! ### The chart module of the glued module -/

/-- `N_0 → Γ(Ñ_0, U_0)`. -/
noncomputable def e0lin : N.M0 →ₗ[A] secA N.G0 (U A 0) where
  toFun m := tilde.toOpen N.mod0 (chartι A 0 ⁻¹ᵁ U A 0) m
  map_add' := map_add (tilde.toOpen N.mod0 (chartι A 0 ⁻¹ᵁ U A 0)).hom
  map_smul' a m :=
    (congrArg (tilde.toOpen N.mod0 (chartι A 0 ⁻¹ᵁ U A 0)).hom (N.act0_secMap a m).symm).trans
      (N.G0_smul (secMap A (U A 0) a) m).symm

/-- `N_0 ≃ Γ(Ñ_0, U_0)`. -/
noncomputable def e0 : N.M0 ≃ₗ[A] secA N.G0 (U A 0) :=
  LinearEquiv.ofBijective N.e0lin (by
    change Function.Bijective (tilde.toOpen N.mod0 (chartι A 0 ⁻¹ᵁ U A 0))
    exact tilde_toOpen_bijective_of_eq_top _ _ (chartι_preimage_self 0))

/-- `N_1 → Γ(Ñ_1, U_1)`. -/
noncomputable def e1lin : N.M1 →ₗ[A] secA N.G1 (U A 1) where
  toFun m := tilde.toOpen N.mod1 (chartι A 1 ⁻¹ᵁ U A 1) m
  map_add' := map_add (tilde.toOpen N.mod1 (chartι A 1 ⁻¹ᵁ U A 1)).hom
  map_smul' a m :=
    (congrArg (tilde.toOpen N.mod1 (chartι A 1 ⁻¹ᵁ U A 1)).hom (N.act1_secMap a m).symm).trans
      (N.G1_smul (secMap A (U A 1) a) m).symm

/-- `N_1 ≃ Γ(Ñ_1, U_1)`. -/
noncomputable def e1 : N.M1 ≃ₗ[A] secA N.G1 (U A 1) :=
  LinearEquiv.ofBijective N.e1lin (by
    change Function.Bijective (tilde.toOpen N.mod1 (chartι A 1 ⁻¹ᵁ U A 1))
    exact tilde_toOpen_bijective_of_eq_top _ _ (chartι_preimage_self 1))

/-- `N₀₁ → Γ(Ñ₀₁, U₀ ∩ U₁)`. -/
noncomputable def e01lin : N.M01 →ₗ[A] secA N.G01 (U A 0 ⊓ U A 1) where
  toFun z := tilde.toOpen N.mod01 ((Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ (U A 0 ⊓ U A 1)) z
  map_add' := map_add (tilde.toOpen N.mod01 _).hom
  map_smul' a z :=
    (congrArg (tilde.toOpen N.mod01 _).hom (N.act01_secMap a z).symm).trans
      (N.G01_smul (secMap A (U A 0 ⊓ U A 1) a) z).symm

/-- `N₀₁ ≃ Γ(Ñ₀₁, U₀ ∩ U₁)`. -/
noncomputable def e01 : N.M01 ≃ₗ[A] secA N.G01 (U A 0 ⊓ U A 1) :=
  LinearEquiv.ofBijective N.e01lin (by
    change Function.Bijective
      (tilde.toOpen N.mod01 ((Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ (U A 0 ⊓ U A 1)))
    exact tilde_toOpen_bijective_of_eq_top _ _ preimage_U01)

lemma e0_apply (m : N.M0) : N.e0 m = tilde.toOpen N.mod0 (chartι A 0 ⁻¹ᵁ U A 0) m := rfl
lemma e1_apply (m : N.M1) : N.e1 m = tilde.toOpen N.mod1 (chartι A 1 ⁻¹ᵁ U A 1) m := rfl
lemma e01_apply (z : N.M01) :
    N.e01 z = tilde.toOpen N.mod01 ((Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ (U A 0 ⊓ U A 1)) z :=
  rfl

/-- The first projection over `U₀`. -/
noncomputable def fst0 : secA N.glue (U A 0) ≃ₗ[A] secA N.G0 (U A 0) :=
  LinearEquiv.ofBijective (appA (fiberProd.fst N.φ0 N.φ1) (U A 0)) (N.glue_fst_bijective _ le_rfl)

/-- The second projection over `U₁`. -/
noncomputable def snd1 : secA N.glue (U A 1) ≃ₗ[A] secA N.G1 (U A 1) :=
  LinearEquiv.ofBijective (appA (fiberProd.snd N.φ0 N.φ1) (U A 1)) (N.glue_snd_bijective _ le_rfl)

/-- The composite `Γ(glue, U₀ ∩ U₁) → Γ(Ñ₀, U₀ ∩ U₁) → Γ(Ñ₀₁, U₀ ∩ U₁)`. -/
noncomputable def fst01 : secA N.glue (U A 0 ⊓ U A 1) ≃ₗ[A] secA N.G01 (U A 0 ⊓ U A 1) :=
  (LinearEquiv.ofBijective (appA (fiberProd.fst N.φ0 N.φ1) (U A 0 ⊓ U A 1))
    (N.glue_fst_bijective _ inf_le_left)).trans
      (LinearEquiv.ofBijective (appA N.φ0 (U A 0 ⊓ U A 1)) (N.φ0_app_bijective _ inf_le_right))

lemma fst0_apply (p : secA N.glue (U A 0)) :
    N.fst0 p = (fiberProd.fst N.φ0 N.φ1).app (U A 0) p := rfl
lemma snd1_apply (p : secA N.glue (U A 1)) :
    N.snd1 p = (fiberProd.snd N.φ0 N.φ1).app (U A 1) p := rfl
lemma fst01_apply (p : secA N.glue (U A 0 ⊓ U A 1)) :
    N.fst01 p = N.φ0.app _ ((fiberProd.fst N.φ0 N.φ1).app (U A 0 ⊓ U A 1) p) := rfl

lemma act0_coord : N.act0 (coord A 0) = N.x0 := by simpa using N.act0_coord_pow 1
lemma act1_coord : N.act1 (coord A 1) = N.x1 := by simpa using N.act1_coord_pow 1

lemma fst0_smul (c : Γ(scheme A, U A 0)) (p : secA N.glue (U A 0)) :
    N.fst0 (smulA N.glue c p) = smulA N.G0 c (N.fst0 p) :=
  Scheme.Modules.Hom.app_smul (fiberProd.fst N.φ0 N.φ1) c (show Γ(N.glue, U A 0) from p)

lemma snd1_smul (c : Γ(scheme A, U A 1)) (p : secA N.glue (U A 1)) :
    N.snd1 (smulA N.glue c p) = smulA N.G1 c (N.snd1 p) :=
  Scheme.Modules.Hom.app_smul (fiberProd.snd N.φ0 N.φ1) c (show Γ(N.glue, U A 1) from p)

lemma fst01_smul (c : R01 A) (p : secA N.glue (U A 0 ⊓ U A 1)) :
    N.fst01 (smulA N.glue c p) = smulA N.G01 c (N.fst01 p) :=
  (congrArg (N.φ0.app _) (Scheme.Modules.Hom.app_smul (fiberProd.fst N.φ0 N.φ1) c
    (show Γ(N.glue, U A 0 ⊓ U A 1) from p))).trans (Scheme.Modules.Hom.app_smul N.φ0 c _)

lemma smulA_e0 (c : Γ(scheme A, U A 0)) (m : N.M0) :
    smulA N.G0 c (N.e0 m) = N.e0 (N.act0 c m) := N.G0_smul c m

lemma smulA_e1 (c : Γ(scheme A, U A 1)) (m : N.M1) :
    smulA N.G1 c (N.e1 m) = N.e1 (N.act1 c m) := N.G1_smul c m

lemma smulA_e01 (c : R01 A) (z : N.M01) :
    smulA N.G01 c (N.e01 z) = N.e01 (N.act01 c z) := N.G01_smul c z

lemma fst01_resA0 (p : secA N.glue (U A 0)) :
    N.fst01 (resA N.glue (inf_le_left : U A 0 ⊓ U A 1 ≤ U A 0) p) =
      N.φ0.app _ (N.G0.presheaf.map (homOfLE inf_le_left).op (N.fst0 p)) :=
  congrArg (N.φ0.app _) (app_res (fiberProd.fst N.φ0 N.φ1) _ (show Γ(N.glue, U A 0) from p))

lemma fst01_resA1 (p : secA N.glue (U A 1)) :
    N.fst01 (resA N.glue (inf_le_right : U A 0 ⊓ U A 1 ≤ U A 1) p) =
      N.φ1.app _ (N.G1.presheaf.map (homOfLE inf_le_right).op (N.snd1 p)) :=
  (fiberProd.cond _).trans
    (congrArg (N.φ1.app _) (app_res (fiberProd.snd N.φ0 N.φ1) _ (show Γ(N.glue, U A 1) from p)))

lemma toGlue_x0 (m : N.M0) :
    N.fst0.symm (N.e0 (N.x0 m)) = smulA N.glue (coord A 0) (N.fst0.symm (N.e0 m)) := by
  apply N.fst0.injective
  rw [LinearEquiv.apply_symm_apply, fst0_smul, LinearEquiv.apply_symm_apply, smulA_e0,
    act0_coord]

lemma toGlue_x1 (m : N.M1) :
    N.snd1.symm (N.e1 (N.x1 m)) = smulA N.glue (coord A 1) (N.snd1.symm (N.e1 m)) := by
  apply N.snd1.injective
  rw [LinearEquiv.apply_symm_apply, snd1_smul, LinearEquiv.apply_symm_apply, smulA_e1,
    act1_coord]

lemma toGlue_t (z : N.M01) :
    N.fst01.symm (N.e01 (N.t z)) =
      smulA N.glue (transition A 1) (N.fst01.symm (N.e01 z)) := by
  apply N.fst01.injective
  rw [LinearEquiv.apply_symm_apply, fst01_smul, LinearEquiv.apply_symm_apply, smulA_e01,
    act01_transition_one]

lemma toGlue_r0 (m : N.M0) :
    N.fst01.symm (N.e01 (N.r0 m)) =
      resA N.glue (inf_le_left : U A 0 ⊓ U A 1 ≤ U A 0) (N.fst0.symm (N.e0 m)) := by
  apply N.fst01.injective
  rw [LinearEquiv.apply_symm_apply, fst01_resA0, LinearEquiv.apply_symm_apply]
  exact (N.ψ0_toOpen (chartι A 0 ⁻¹ᵁ (U A 0 ⊓ U A 1)) m).symm

lemma toGlue_r1 (m : N.M1) :
    N.fst01.symm (N.e01 (N.r1 m)) =
      resA N.glue (inf_le_right : U A 0 ⊓ U A 1 ≤ U A 1) (N.snd1.symm (N.e1 m)) := by
  have h : (Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ (U A 0 ⊓ U A 1) =
      (Spec.map (ρ A 1) ≫ chartι A 1) ⁻¹ᵁ (U A 0 ⊓ U A 1) := by rw [chartι_comp]
  have s1 : N.e01 (N.r1 m) = (tilde N.mod01).presheaf.map (eqToHom h).op
      (tilde.toOpen N.mod01 ((Spec.map (ρ A 1) ≫ chartι A 1) ⁻¹ᵁ (U A 0 ⊓ U A 1)) (N.r1 m)) :=
    (tilde_toOpen_res N.mod01 (eqToHom h) (N.r1 m)).symm
  have s2 : N.G1.presheaf.map (homOfLE inf_le_right).op (N.e1 m) =
      tilde.toOpen N.mod1 (chartι A 1 ⁻¹ᵁ (U A 0 ⊓ U A 1)) m :=
    tilde_toOpen_res N.mod1 _ m
  have s3 : tilde.toOpen N.mod01 ((Spec.map (ρ A 1) ≫ chartι A 1) ⁻¹ᵁ (U A 0 ⊓ U A 1)) (N.r1 m) =
      N.ψ1.app (chartι A 1 ⁻¹ᵁ (U A 0 ⊓ U A 1))
        (tilde.toOpen N.mod1 (chartι A 1 ⁻¹ᵁ (U A 0 ⊓ U A 1)) m) :=
    (tilde_toOpen_res N.mod01 (homOfLE le_top : Spec.map (ρ A 1) ⁻¹ᵁ
      (chartι A 1 ⁻¹ᵁ (U A 0 ⊓ U A 1)) ⟶ ⊤) (N.r1 m)).symm.trans
        (N.ψ1_toOpen (chartι A 1 ⁻¹ᵁ (U A 0 ⊓ U A 1)) m).symm
  apply N.fst01.injective
  rw [LinearEquiv.apply_symm_apply, fst01_resA1, LinearEquiv.apply_symm_apply, φ1_app_apply, s1,
    s2, s3]

/-- **`N → chartModule N.glue`**, an isomorphism on all three charts. -/
noncomputable def toGlue : ChartModule.Hom N (chartModule N.glue) where
  f0 := (N.e0.trans N.fst0.symm).toLinearMap
  f1 := (N.e1.trans N.snd1.symm).toLinearMap
  f01 := (N.e01.trans N.fst01.symm).toLinearMap
  comm_x0 := N.toGlue_x0
  comm_x1 := N.toGlue_x1
  comm_t := N.toGlue_t
  comm_r0 := N.toGlue_r0
  comm_r1 := N.toGlue_r1

lemma toGlue_bijective0 : Function.Bijective N.toGlue.f0 := (N.e0.trans N.fst0.symm).bijective
lemma toGlue_bijective1 : Function.Bijective N.toGlue.f1 := (N.e1.trans N.snd1.symm).bijective
lemma toGlue_bijective01 : Function.Bijective N.toGlue.f01 :=
  (N.e01.trans N.fst01.symm).bijective

end ChartModule

end ProjectiveLine
