/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ProjectiveLineGlueIso
import FormalSchemes.QcohHomExt

/-!
# Functoriality of the glued module

A morphism `f : N → N'` of chart modules induces `glueMap f : N.glue ⟶ N'.glue`, compatible with
`ChartModule.toGlue` (`ProjectiveLine.ChartModule.toGlue_naturality`).
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite AlgebraicGeometry.Scheme.Modules
  Polynomial LaurentPolynomial

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {G₀ G₁ H : X.Modules} {φ : G₀ ⟶ H} {ψ : G₁ ⟶ H}

lemma fiberProd.condition : fiberProd.fst φ ψ ≫ φ = fiberProd.snd φ ψ ≫ ψ :=
  hom_ext _ _ fun W ↦ by
    ext p
    exact fiberProd.cond p

lemma fiberProd.hom_ext {F : X.Modules} {a b : F ⟶ fiberProd φ ψ}
    (h₀ : a ≫ fiberProd.fst φ ψ = b ≫ fiberProd.fst φ ψ)
    (h₁ : a ≫ fiberProd.snd φ ψ = b ≫ fiberProd.snd φ ψ) : a = b :=
  Scheme.Modules.hom_ext _ _ fun W ↦ by
    ext s
    exact fiberProd.ext (congrArg (fun χ ↦ χ.app W s) h₀)
      (congrArg (fun χ ↦ χ.app W s) h₁)

end AlgebraicGeometry.Scheme.Modules

namespace ProjectiveLine

variable {A : Type u} [CommRing A]

namespace ChartModule

variable {N N' : ChartModule A} (f : ChartModule.Hom N N')

lemma Hom.lev_f01 (p : A[T;T⁻¹]) (z : N.M01) : f.f01 (N.lev p z) = N'.lev p (f.f01 z) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | C_mul_T n a => rw [lev_C_mul_T, lev_C_mul_T, _root_.map_smul, f.comm_t_zpow]

/-- `f₀` as a `Γ(U₀)`-linear map. -/
noncomputable def mapMod0 : N.mod0 ⟶ N'.mod0 :=
  ModuleCat.ofHom (X := N.mod0) (Y := N'.mod0)
    { toFun := f.f0
      map_add' := f.f0.map_add
      map_smul' _ m := f.aeval_f0 _ m }

/-- `f₁` as a `Γ(U₁)`-linear map. -/
noncomputable def mapMod1 : N.mod1 ⟶ N'.mod1 :=
  ModuleCat.ofHom (X := N.mod1) (Y := N'.mod1)
    { toFun := f.f1
      map_add' := f.f1.map_add
      map_smul' _ m := f.aeval_f1 _ m }

/-- `f₀₁` as a `Γ(U₀ ∩ U₁)`-linear map. -/
noncomputable def mapMod01 : N.mod01 ⟶ N'.mod01 :=
  ModuleCat.ofHom (X := N.mod01) (Y := N'.mod01)
    { toFun := f.f01
      map_add' := f.f01.map_add
      map_smul' _ z := f.lev_f01 _ z }

/-- `f̃₀ : Ñ₀ → Ñ'₀` on `ℙ¹_A`. -/
noncomputable def G0map : N.G0 ⟶ N'.G0 :=
  (pushforward (chartι A 0)).map ((tilde.functor (R A 0)).map (mapMod0 f))

/-- `f̃₁ : Ñ₁ → Ñ'₁` on `ℙ¹_A`. -/
noncomputable def G1map : N.G1 ⟶ N'.G1 :=
  (pushforward (chartι A 1)).map ((tilde.functor (R A 1)).map (mapMod1 f))

/-- `f̃₀₁ : Ñ₀₁ → Ñ'₀₁` on `ℙ¹_A`. -/
noncomputable def G01map : N.G01 ⟶ N'.G01 :=
  (pushforward (Spec.map (ρ A 0) ≫ chartι A 0)).map (tilde.map (mapMod01 f))

lemma tilde_map_toOpen {R' : CommRingCat.{u}} {M M' : ModuleCat.{u} R'} (g : M ⟶ M')
    (V : (Spec R').Opens) (m : M) :
    (tilde.map g).app V (tilde.toOpen M V m) = tilde.toOpen M' V (g m) :=
  ConcreteCategory.congr_hom (tilde.toOpen_map_app g V) m

lemma ψ0_naturality : N.ψ0 ≫ (pushforward (Spec.map (ρ A 0))).map (tilde.map (mapMod01 f)) =
    (tilde.functor (R A 0)).map (mapMod0 f) ≫ N'.ψ0 := by
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := R A 0) ((tilde.functor (R A 0)).obj N.mod0)) :=
    (isIso_fromTildeΓ_iff_isLocalizing (R := R A 0) _).2 (isLocalizing_tilde (R := R A 0) N.mod0)
  refine hom_ext_of_isIso_fromTildeΓ (R := R A 0) fun x ↦ ?_
  obtain ⟨m, rfl⟩ := (tilde_toOpen_bijective_of_eq_top N.mod0 ⊤ rfl).2 x
  have l1 : N.ψ0.app ⊤ (tilde.toOpen N.mod0 ⊤ m) =
      tilde.toOpen N.mod01 (Spec.map (ρ A 0) ⁻¹ᵁ ⊤) (N.r0 m) :=
    (N.ψ0_toOpen ⊤ m).trans (tilde_toOpen_res N.mod01
      (homOfLE (le_top : Spec.map (ρ A 0) ⁻¹ᵁ ⊤ ≤ ⊤)) _)
  have l2 : N'.ψ0.app ⊤ (tilde.toOpen N'.mod0 ⊤ (f.f0 m)) =
      tilde.toOpen N'.mod01 (Spec.map (ρ A 0) ⁻¹ᵁ ⊤) (N'.r0 (f.f0 m)) :=
    (N'.ψ0_toOpen ⊤ (f.f0 m)).trans (tilde_toOpen_res N'.mod01
      (homOfLE (le_top : Spec.map (ρ A 0) ⁻¹ᵁ ⊤ ≤ ⊤)) _)
  change (tilde.map (mapMod01 f)).app _ (N.ψ0.app ⊤ (tilde.toOpen N.mod0 ⊤ m)) =
    N'.ψ0.app ⊤ ((tilde.map (mapMod0 f)).app ⊤ (tilde.toOpen N.mod0 ⊤ m))
  rw [l1, tilde_map_toOpen, tilde_map_toOpen]
  change _ = N'.ψ0.app ⊤ (tilde.toOpen N'.mod0 ⊤ (f.f0 m))
  rw [l2]
  exact congrArg (tilde.toOpen N'.mod01 _) (f.comm_r0 m)

lemma ψ1_naturality : N.ψ1 ≫ (pushforward (Spec.map (ρ A 1))).map (tilde.map (mapMod01 f)) =
    (tilde.functor (R A 1)).map (mapMod1 f) ≫ N'.ψ1 := by
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := R A 1) ((tilde.functor (R A 1)).obj N.mod1)) :=
    (isIso_fromTildeΓ_iff_isLocalizing (R := R A 1) _).2 (isLocalizing_tilde (R := R A 1) N.mod1)
  refine hom_ext_of_isIso_fromTildeΓ (R := R A 1) fun x ↦ ?_
  obtain ⟨m, rfl⟩ := (tilde_toOpen_bijective_of_eq_top N.mod1 ⊤ rfl).2 x
  have l1 : N.ψ1.app ⊤ (tilde.toOpen N.mod1 ⊤ m) =
      tilde.toOpen N.mod01 (Spec.map (ρ A 1) ⁻¹ᵁ ⊤) (N.r1 m) :=
    (N.ψ1_toOpen ⊤ m).trans (tilde_toOpen_res N.mod01
      (homOfLE (le_top : Spec.map (ρ A 1) ⁻¹ᵁ ⊤ ≤ ⊤)) _)
  have l2 : N'.ψ1.app ⊤ (tilde.toOpen N'.mod1 ⊤ (f.f1 m)) =
      tilde.toOpen N'.mod01 (Spec.map (ρ A 1) ⁻¹ᵁ ⊤) (N'.r1 (f.f1 m)) :=
    (N'.ψ1_toOpen ⊤ (f.f1 m)).trans (tilde_toOpen_res N'.mod01
      (homOfLE (le_top : Spec.map (ρ A 1) ⁻¹ᵁ ⊤ ≤ ⊤)) _)
  change (tilde.map (mapMod01 f)).app _ (N.ψ1.app ⊤ (tilde.toOpen N.mod1 ⊤ m)) =
    N'.ψ1.app ⊤ ((tilde.map (mapMod1 f)).app ⊤ (tilde.toOpen N.mod1 ⊤ m))
  rw [l1, tilde_map_toOpen, tilde_map_toOpen]
  change _ = N'.ψ1.app ⊤ (tilde.toOpen N'.mod1 ⊤ (f.f1 m))
  rw [l2]
  exact congrArg (tilde.toOpen N'.mod01 _) (f.comm_r1 m)

lemma φ0_naturality : N.φ0 ≫ G01map f = G0map f ≫ N'.φ0 :=
  Scheme.Modules.hom_ext _ _ fun W ↦ by
    ext x
    exact congrArg (fun χ ↦ ConcreteCategory.hom (Hom.app χ (chartι A 0 ⁻¹ᵁ W)) x)
      (ψ0_naturality f)

lemma φ1_naturality : N.φ1 ≫ G01map f = G1map f ≫ N'.φ1 :=
  Scheme.Modules.hom_ext _ _ fun W ↦ by
    ext x
    have h : (Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ W =
        (Spec.map (ρ A 1) ≫ chartι A 1) ⁻¹ᵁ W := by
      rw [chartι_comp]
    have e := congrArg (fun χ ↦ ConcreteCategory.hom (Hom.app χ (chartι A 1 ⁻¹ᵁ W)) x)
      (ψ1_naturality f)
    have s1 : (N.φ1 ≫ G01map f).app W x = (tilde.map (mapMod01 f)).app _
        ((tilde N.mod01).presheaf.map (homOfLE h.le).op (N.ψ1.app (chartι A 1 ⁻¹ᵁ W) x)) :=
      congrArg ((tilde.map (mapMod01 f)).app _) (N.φ1_app_apply W x)
    have s2 : (G1map f ≫ N'.φ1).app W x = (tilde N'.mod01).presheaf.map (homOfLE h.le).op
        (N'.ψ1.app (chartι A 1 ⁻¹ᵁ W) ((tilde.map (mapMod1 f)).app _ x)) :=
      N'.φ1_app_apply W _
    refine s1.trans (Eq.trans ?_ s2.symm)
    exact (app_res (tilde.map (mapMod01 f)) h.le _).trans (congrArg _ e)

/-- **The morphism of glued modules** induced by a morphism of chart modules. -/
noncomputable def glueMap : N.glue ⟶ N'.glue :=
  fiberProd.lift (fiberProd.fst N.φ0 N.φ1 ≫ G0map f) (fiberProd.snd N.φ0 N.φ1 ≫ G1map f)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (φ0_naturality f).symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G01map f) fiberProd.condition).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (φ1_naturality f)).trans
          (Category.assoc _ _ _).symm))))))

/-- **`toGlue` is natural.** -/
lemma toGlue_naturality :
    (chartModuleMap (glueMap f)).comp N.toGlue = N'.toGlue.comp f :=
  Hom.ext_of_f0_f1
    (LinearMap.ext fun m ↦ N'.fst0.injective
      ((congrArg ((G0map f).app (U A 0)) (N.fst0.apply_symm_apply (N.e0 m))).trans
        ((tilde_map_toOpen (mapMod0 f) (chartι A 0 ⁻¹ᵁ U A 0) m).trans
          (N'.fst0.apply_symm_apply _).symm)))
    (LinearMap.ext fun m ↦ N'.snd1.injective
      ((congrArg ((G1map f).app (U A 1)) (N.snd1.apply_symm_apply (N.e1 m))).trans
        ((tilde_map_toOpen (mapMod1 f) (chartι A 1 ⁻¹ᵁ U A 1) m).trans
          (N'.snd1.apply_symm_apply _).symm)))

end ChartModule

end ProjectiveLine
