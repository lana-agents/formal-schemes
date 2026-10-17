/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ProjectiveLineBridge
import FormalSchemes.ModulesFiberProd
import FormalSchemes.QcohCover
import FormalSchemes.TildeLocal

/-!
# Gluing a chart module to a quasi-coherent module on `ℙ¹_A`
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite AlgebraicGeometry.Scheme.Modules
  Polynomial LaurentPolynomial

namespace ProjectiveLine

variable {A : Type u} [CommRing A]

/-- The ring of functions on the chart `U_k`. -/
noncomputable abbrev R (A : Type u) [CommRing A] (k : Fin 2) : CommRingCat.{u} :=
  Γ(scheme A, U A k)

/-- The ring of functions on the overlap. -/
noncomputable abbrev R01 (A : Type u) [CommRing A] : CommRingCat.{u} :=
  Γ(scheme A, U A 0 ⊓ U A 1)

/-- The restriction `Γ(U_k) → Γ(U₀ ∩ U₁)`. -/
noncomputable abbrev ρ (A : Type u) [CommRing A] (k : Fin 2) : R A k ⟶ R01 A :=
  (scheme A).presheaf.map (homOfLE (show U A 0 ⊓ U A 1 ≤ U A k by
    fin_cases k
    exacts [inf_le_left, inf_le_right])).op

lemma chartSections_coord (k : Fin 2) : chartSections A k (coord A k) = Polynomial.X := by
  rw [coord, chartSections_awayToSection, chartEquiv_chartCoord]

namespace ChartModule

variable (N : ChartModule A)

/-- `Γ(U₀)` acting on `N₀` through `Γ(U₀) ≃ A[X]`, `X ↦ x₀`. -/
noncomputable def act0 : R A 0 →+* Module.End A N.M0 :=
  (Polynomial.aeval N.x0).toRingHom.comp (chartSections A 0).toRingHom

/-- `Γ(U₁)` acting on `N₁` through `Γ(U₁) ≃ A[X]`, `X ↦ x₁`. -/
noncomputable def act1 : R A 1 →+* Module.End A N.M1 :=
  (Polynomial.aeval N.x1).toRingHom.comp (chartSections A 1).toRingHom

/-- `Γ(U₀ ∩ U₁)` acting on `N₀₁` through `Γ(U₀ ∩ U₁) ≃ A[T, T⁻¹]`, `T ↦ t`. -/
noncomputable def act01 : R01 A →+* Module.End A N.M01 :=
  N.lev.toRingHom.comp (overlapSections A).toRingHom

lemma act01_r0 (r : R A 0) (m : N.M0) : N.act01 (ρ A 0 r) (N.r0 m) = N.r0 (N.act0 r m) := by
  simp only [act01, act0, RingHom.coe_comp, Function.comp_apply]
  erw [overlapSections_res_zero]
  exact N.lev_toLaurent_r0 _ m

lemma act01_r1 (r : R A 1) (m : N.M1) : N.act01 (ρ A 1 r) (N.r1 m) = N.r1 (N.act1 r m) := by
  simp only [act01, act1, RingHom.coe_comp, Function.comp_apply]
  erw [overlapSections_res_one]
  exact N.lev_invert_r1 _ m

lemma act0_coord_pow (k : ℕ) : N.act0 (coord A 0 ^ k) = N.x0 ^ k := by
  rw [map_pow]
  congr 1
  change Polynomial.aeval N.x0 (chartSections A 0 (coord A 0)) = N.x0
  rw [chartSections_coord, aeval_X]

lemma act1_coord_pow (k : ℕ) : N.act1 (coord A 1 ^ k) = N.x1 ^ k := by
  rw [map_pow]
  congr 1
  change Polynomial.aeval N.x1 (chartSections A 1 (coord A 1)) = N.x1
  rw [chartSections_coord, aeval_X]

lemma act01_transition_pow (d : ℤ) (k : ℕ) (z : N.M01) :
    N.act01 (transition A d ^ k) z = (N.t ^ ((k : ℤ) * d)) z := by
  change N.lev (overlapSections A (transition A d ^ k)) z = _
  rw [map_pow, overlapSections_transition, T_pow]
  exact N.lev_T _ z

/-- `N₀` as a `Γ(U₀)`-module. -/
noncomputable def mod0 : ModuleCat.{u} (R A 0) :=
  letI : Module (R A 0) N.M0 := Module.compHom N.M0 N.act0
  ModuleCat.of _ N.M0

/-- `N₁` as a `Γ(U₁)`-module. -/
noncomputable def mod1 : ModuleCat.{u} (R A 1) :=
  letI : Module (R A 1) N.M1 := Module.compHom N.M1 N.act1
  ModuleCat.of _ N.M1

/-- `N₀₁` as a `Γ(U₀ ∩ U₁)`-module. -/
noncomputable def mod01 : ModuleCat.{u} (R01 A) :=
  letI : Module (R01 A) N.M01 := Module.compHom N.M01 N.act01
  ModuleCat.of _ N.M01

lemma mod0_smul (r : R A 0) (m : N.mod0) : r • m = N.act0 r (show N.M0 from m) := rfl
lemma mod1_smul (r : R A 1) (m : N.mod1) : r • m = N.act1 r (show N.M1 from m) := rfl
lemma mod01_smul (r : R01 A) (m : N.mod01) : r • m = N.act01 r (show N.M01 from m) := rfl

end ChartModule

/-! ### The sheaves on the charts -/

/-- `Spec Γ(U_k) → ℙ¹_A`. -/
noncomputable abbrev chartι (A : Type u) [CommRing A] (k : Fin 2) : Spec (R A k) ⟶ scheme A :=
  (isAffineOpen_U A k).fromSpec

lemma chartι_comp : Spec.map (ρ A 1) ≫ chartι A 1 = Spec.map (ρ A 0) ≫ chartι A 0 :=
  (IsAffineOpen.map_fromSpec _ (isAffineOpen_U_inf A) _).trans
    (IsAffineOpen.map_fromSpec _ (isAffineOpen_U_inf A) _).symm

lemma chartι_preimage_rev (k : Fin 2) :
    chartι A k ⁻¹ᵁ U A k.rev = PrimeSpectrum.basicOpen (coord A k) := by
  change (isAffineOpen_U A k).fromSpec ⁻¹ᵁ U A k.rev = _
  rw [fromSpec_eq]
  change Spec.map _ ⁻¹ᵁ (Proj.awayι (grading A) (MvPolynomial.X k) (X_mem k) one_pos ⁻¹ᵁ
    Proj.basicOpen (grading A) (MvPolynomial.X k.rev)) = _
  rw [Proj.awayι_preimage_basicOpen (grading A) (X_mem k) one_pos (X_mem k.rev) one_pos,
    isLocalizationElem_eq', SpecMap_preimage_basicOpen]
  rfl

lemma chartι_preimage_self (k : Fin 2) : chartι A k ⁻¹ᵁ U A k = ⊤ :=
  (isAffineOpen_U A k).fromSpec_preimage_self

/-- On `Spec R`, the action of `R` on the global sections of a pushforward along `Spec S → Spec R`
is through `R → S`. -/
lemma smul_pushforward_Spec {R' S : CommRingCat.{u}} (φ : R' ⟶ S) (M : (Spec S).Modules)
    (r : R') (x : moduleSpecΓFunctor.obj ((pushforward (Spec.map φ)).obj M)) :
    r • x = (show moduleSpecΓFunctor.obj M from φ r • (show moduleSpecΓFunctor.obj M from x)) := by
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) r
  change ((Spec.map φ).appTop ((Scheme.ΓSpecIso R').inv r) : Γ(Spec S, ⊤)) •
    (show Γ(M, ⊤) from x) = ((Scheme.ΓSpecIso S).inv (φ r) : Γ(Spec S, ⊤)) • (show Γ(M, ⊤) from x)
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
  rw [h]


namespace ChartModule

variable (N : ChartModule A)

/-- `Ñ₀₁` pushed forward to `Spec Γ(U_k)`. -/
noncomputable abbrev P (k : Fin 2) : (Spec (R A k)).Modules :=
  (pushforward (Spec.map (ρ A k))).obj (tilde N.mod01)

/-- `N₀ → Γ(Ñ₀₁)`, `m ↦ r₀ m`, as a `Γ(U₀)`-linear map. -/
noncomputable def gl0' : N.mod0 →ₗ[R A 0] (moduleSpecΓFunctor (R := R A 0)).obj (N.P 0) :=
    { toFun m := tilde.toOpen N.mod01 ⊤ (N.r0 m)
      map_add' m m' := (congrArg (tilde.toOpen N.mod01 ⊤).hom (map_add N.r0 m m')).trans
        ((tilde.toOpen N.mod01 ⊤).hom.map_add _ _)
      map_smul' r m := by
        refine Eq.trans ?_ (smul_pushforward_Spec (ρ A 0) (tilde N.mod01) r _).symm
        refine Eq.trans ?_ ((tilde.toOpen N.mod01 ⊤).hom.map_smul (ρ A 0 r) (N.r0 m))
        exact congrArg (tilde.toOpen N.mod01 ⊤).hom (N.act01_r0 r m).symm }

/-- `N₀ → Γ(Ñ₀₁)` in `ModuleCat`. -/
noncomputable def gl0 : N.mod0 ⟶ (moduleSpecΓFunctor (R := R A 0)).obj (N.P 0) :=
  ModuleCat.ofHom (X := N.mod0)
    (Y := (moduleSpecΓFunctor (R := R A 0)).obj (N.P 0)) N.gl0'

/-- `N₁ → Γ(Ñ₀₁)`, `m ↦ r₁ m`, as a `Γ(U₁)`-linear map. -/
noncomputable def gl1' : N.mod1 →ₗ[R A 1] (moduleSpecΓFunctor (R := R A 1)).obj (N.P 1) :=
    { toFun m := tilde.toOpen N.mod01 ⊤ (N.r1 m)
      map_add' m m' := (congrArg (tilde.toOpen N.mod01 ⊤).hom (map_add N.r1 m m')).trans
        ((tilde.toOpen N.mod01 ⊤).hom.map_add _ _)
      map_smul' r m := by
        refine Eq.trans ?_ (smul_pushforward_Spec (ρ A 1) (tilde N.mod01) r _).symm
        refine Eq.trans ?_ ((tilde.toOpen N.mod01 ⊤).hom.map_smul (ρ A 1 r) (N.r1 m))
        exact congrArg (tilde.toOpen N.mod01 ⊤).hom (N.act01_r1 r m).symm }

/-- `N₁ → Γ(Ñ₀₁)` in `ModuleCat`. -/
noncomputable def gl1 : N.mod1 ⟶ (moduleSpecΓFunctor (R := R A 1)).obj (N.P 1) :=
  ModuleCat.ofHom (X := N.mod1)
    (Y := (moduleSpecΓFunctor (R := R A 1)).obj (N.P 1)) N.gl1'

lemma ρ_coord_zero : ρ A 0 (coord A 0) = transition A 1 := res_coord_zero A

lemma ρ_coord_one : ρ A 1 (coord A 1) = transition A (-1) := res_coord_one A

lemma ρ_coord_zero_pow (k : ℕ) : ρ A 0 (coord A 0 ^ k) = transition A 1 ^ k :=
  (map_pow _ _ _).trans (congrArg (· ^ k) ρ_coord_zero)

lemma ρ_coord_one_pow (k : ℕ) : ρ A 1 (coord A 1 ^ k) = transition A (-1) ^ k :=
  (map_pow _ _ _).trans (congrArg (· ^ k) ρ_coord_one)

lemma act01_ρ_coord_zero_pow (k : ℕ) (z : N.M01) :
    N.act01 (ρ A 0 (coord A 0 ^ k)) z = (N.t ^ k) z := by
  rw [ρ_coord_zero_pow, act01_transition_pow, mul_one, zpow_natCast]

lemma act01_ρ_coord_one_pow (k : ℕ) (z : N.M01) :
    N.act01 (ρ A 1 (coord A 1 ^ k)) z = (N.t.symm ^ k) z := by
  rw [ρ_coord_one_pow, act01_transition_pow, mul_neg_one, zpow_neg, zpow_natCast, ← inv_pow]
  rfl

lemma gl0'_apply (m : N.mod0) : N.gl0' m = tilde.toOpen N.mod01 ⊤ (N.r0 m) := rfl
lemma gl1'_apply (m : N.mod1) : N.gl1' m = tilde.toOpen N.mod01 ⊤ (N.r1 m) := rfl

lemma toOpen_top_bijective : Function.Bijective (tilde.toOpen N.mod01 ⊤) :=
  ConcreteCategory.bijective_of_isIso _

/-- `r₀ : N₀ → N₀₁` is a localisation at the chart coordinate. -/
instance isLocalizedModule_gl0 : IsLocalizedModule (.powers (coord A 0)) N.gl0' where
  map_units := by
    rintro ⟨_, k, rfl⟩
    rw [Module.End.isUnit_iff]
    have hu : IsUnit (ρ A 0 (coord A 0 ^ k)) := by
      rw [ρ_coord_zero_pow]
      exact (isUnit_transition A 1).pow k
    have e : ∀ x : (moduleSpecΓFunctor (R := R A 0)).obj (N.P 0),
        algebraMap (R A 0) (Module.End (R A 0) ((moduleSpecΓFunctor (R := R A 0)).obj (N.P 0)))
          (coord A 0 ^ k) x = (show (moduleSpecΓFunctor (R := R01 A)).obj (tilde N.mod01) from
            ρ A 0 (coord A 0 ^ k) •
              (show (moduleSpecΓFunctor (R := R01 A)).obj (tilde N.mod01) from x)) :=
      fun x ↦ (Module.algebraMap_end_apply _ _ _ _ x).trans (smul_pushforward_Spec _ _ _ _)
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨(show (moduleSpecΓFunctor (R := R01 A)).obj (tilde N.mod01)
      from (↑hu.unit⁻¹ : R01 A) • (show (moduleSpecΓFunctor (R := R01 A)).obj (tilde N.mod01)
        from y)), ?_⟩⟩
    · exact MulAction.injective (β := (moduleSpecΓFunctor (R := R01 A)).obj (tilde N.mod01))
        hu.unit ((e x).symm.trans (hxy.trans (e y)))
    · refine (e _).trans ((smul_smul (α := (moduleSpecΓFunctor (R := R01 A)).obj (tilde N.mod01))
        _ _ _).trans ?_)
      rw [IsUnit.mul_val_inv, one_smul]
  surj y := by
    obtain ⟨z, rfl⟩ := N.toOpen_top_bijective.2 y
    obtain ⟨m, k, hk⟩ := N.exists_r0 z
    refine ⟨⟨m, ⟨coord A 0 ^ k, k, rfl⟩⟩, ?_⟩
    refine (smul_pushforward_Spec (ρ A 0) (tilde N.mod01) (coord A 0 ^ k) _).trans ?_
    refine ((tilde.toOpen N.mod01 ⊤).hom.map_smul _ z).symm.trans ?_
    exact congrArg (tilde.toOpen N.mod01 ⊤).hom ((N.act01_ρ_coord_zero_pow k z).trans hk)
  exists_of_eq {a b} hab := by
    have h1 : N.r0 a = N.r0 b := N.toOpen_top_bijective.1 hab
    obtain ⟨k, hk⟩ := N.ker_r0 (a - b) ((map_sub N.r0 a b).trans (sub_eq_zero.2 h1))
    refine ⟨⟨coord A 0 ^ k, k, rfl⟩, ?_⟩
    change N.act0 (coord A 0 ^ k) a = N.act0 (coord A 0 ^ k) b
    rw [N.act0_coord_pow]
    exact sub_eq_zero.1 ((map_sub _ a b).symm.trans hk)

/-- `r₁ : N₁ → N₀₁` is a localisation at the chart coordinate. -/
instance isLocalizedModule_gl1 : IsLocalizedModule (.powers (coord A 1)) N.gl1' where
  map_units := by
    rintro ⟨_, k, rfl⟩
    rw [Module.End.isUnit_iff]
    have hu : IsUnit (ρ A 1 (coord A 1 ^ k)) := by
      rw [ρ_coord_one_pow]
      exact (isUnit_transition A (-1)).pow k
    have e : ∀ x : (moduleSpecΓFunctor (R := R A 1)).obj (N.P 1),
        algebraMap (R A 1) (Module.End (R A 1) ((moduleSpecΓFunctor (R := R A 1)).obj (N.P 1)))
          (coord A 1 ^ k) x = (show (moduleSpecΓFunctor (R := R01 A)).obj (tilde N.mod01) from
            ρ A 1 (coord A 1 ^ k) •
              (show (moduleSpecΓFunctor (R := R01 A)).obj (tilde N.mod01) from x)) :=
      fun x ↦ (Module.algebraMap_end_apply _ _ _ _ x).trans (smul_pushforward_Spec _ _ _ _)
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨(show (moduleSpecΓFunctor (R := R01 A)).obj (tilde N.mod01)
      from (↑hu.unit⁻¹ : R01 A) • (show (moduleSpecΓFunctor (R := R01 A)).obj (tilde N.mod01)
        from y)), ?_⟩⟩
    · exact MulAction.injective (β := (moduleSpecΓFunctor (R := R01 A)).obj (tilde N.mod01))
        hu.unit ((e x).symm.trans (hxy.trans (e y)))
    · refine (e _).trans ((smul_smul (α := (moduleSpecΓFunctor (R := R01 A)).obj (tilde N.mod01))
        _ _ _).trans ?_)
      rw [IsUnit.mul_val_inv, one_smul]
  surj y := by
    obtain ⟨z, rfl⟩ := N.toOpen_top_bijective.2 y
    obtain ⟨m, k, hk⟩ := N.exists_r1 z
    refine ⟨⟨m, ⟨coord A 1 ^ k, k, rfl⟩⟩, ?_⟩
    refine (smul_pushforward_Spec (ρ A 1) (tilde N.mod01) (coord A 1 ^ k) _).trans ?_
    refine ((tilde.toOpen N.mod01 ⊤).hom.map_smul _ z).symm.trans ?_
    exact congrArg (tilde.toOpen N.mod01 ⊤).hom ((N.act01_ρ_coord_one_pow k z).trans hk)
  exists_of_eq {a b} hab := by
    have h1 : N.r1 a = N.r1 b := N.toOpen_top_bijective.1 hab
    obtain ⟨k, hk⟩ := N.ker_r1 (a - b) ((map_sub N.r1 a b).trans (sub_eq_zero.2 h1))
    refine ⟨⟨coord A 1 ^ k, k, rfl⟩, ?_⟩
    change N.act1 (coord A 1 ^ k) a = N.act1 (coord A 1 ^ k) b
    rw [N.act1_coord_pow]
    exact sub_eq_zero.1 ((map_sub _ a b).symm.trans hk)

/-- `Ñ₀ → Ñ₀₁` on `Spec Γ(U₀)`. -/
noncomputable def ψ0 : (tilde.functor (R A 0)).obj N.mod0 ⟶ N.P 0 :=
  (tilde.adjunction.homEquiv _ _).symm N.gl0

/-- `Ñ₁ → Ñ₀₁` on `Spec Γ(U₁)`. -/
noncomputable def ψ1 : (tilde.functor (R A 1)).obj N.mod1 ⟶ N.P 1 :=
  (tilde.adjunction.homEquiv _ _).symm N.gl1

lemma ψ0_toOpen (V : (Spec (R A 0)).Opens) (m : N.mod0) :
    N.ψ0.app V (tilde.toOpen N.mod0 V m) = (N.P 0).presheaf.map (homOfLE le_top).op (N.gl0 m) := by
  have h1 := ConcreteCategory.congr_hom (tilde.toOpen_map_app N.gl0 V) m
  have h2 := ConcreteCategory.congr_hom
    (Scheme.Modules.toOpen_fromTildeΓ_app (R := R A 0) (N.P 0) V) (N.gl0 m)
  rw [ψ0, Adjunction.homEquiv_counit]
  exact (congrArg _ h1).trans h2

lemma ψ1_toOpen (V : (Spec (R A 1)).Opens) (m : N.mod1) :
    N.ψ1.app V (tilde.toOpen N.mod1 V m) = (N.P 1).presheaf.map (homOfLE le_top).op (N.gl1 m) := by
  have h1 := ConcreteCategory.congr_hom (tilde.toOpen_map_app N.gl1 V) m
  have h2 := ConcreteCategory.congr_hom
    (Scheme.Modules.toOpen_fromTildeΓ_app (R := R A 1) (N.P 1) V) (N.gl1 m)
  rw [ψ1, Adjunction.homEquiv_counit]
  exact (congrArg _ h1).trans h2

/-! ### The glued module -/

/-- `Ñ₀` on `ℙ¹_A`. -/
noncomputable abbrev G0 : (scheme A).Modules :=
  (pushforward (chartι A 0)).obj ((tilde.functor (R A 0)).obj N.mod0)

/-- `Ñ₁` on `ℙ¹_A`. -/
noncomputable abbrev G1 : (scheme A).Modules :=
  (pushforward (chartι A 1)).obj ((tilde.functor (R A 1)).obj N.mod1)

/-- `Ñ₀₁` on `ℙ¹_A`. -/
noncomputable abbrev G01 : (scheme A).Modules :=
  (pushforward (Spec.map (ρ A 0) ≫ chartι A 0)).obj (tilde N.mod01)

/-- `Ñ₀ → Ñ₀₁` on `ℙ¹_A`. -/
noncomputable def φ0 : N.G0 ⟶ N.G01 :=
  (pushforward (chartι A 0)).map N.ψ0 ≫
    (pushforwardComp (Spec.map (ρ A 0)) (chartι A 0)).hom.app _

/-- `Ñ₁ → Ñ₀₁` on `ℙ¹_A`. -/
noncomputable def φ1 : N.G1 ⟶ N.G01 :=
  (pushforward (chartι A 1)).map N.ψ1 ≫
    (pushforwardComp (Spec.map (ρ A 1)) (chartι A 1)).hom.app _ ≫
      (pushforwardCongr chartι_comp).hom.app _

/-- **The glued module** of a chart module: `Ñ₀ ×_{Ñ₀₁} Ñ₁`. -/
noncomputable def glue : (scheme A).Modules := fiberProd N.φ0 N.φ1

/-! ### Sections of the glued module over the charts -/

lemma ψ0_app_bijective (V : (Spec (R A 0)).Opens) (hV : V ≤ PrimeSpectrum.basicOpen (coord A 0)) :
    Function.Bijective (N.ψ0.app V) := by
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := R A 0) (N.P 0)) :=
    isIso_fromTildeΓ_pushforward (R := R A 0) (S := R01 A) (ρ A 0) (tilde N.mod01)
  haveI : IsLocalizedModule (.powers (coord A 0)) N.gl0.hom := N.isLocalizedModule_gl0
  have h1 := tilde_map_app_bijective N.gl0 (coord A 0) V hV
  have h2 : Function.Bijective ((Scheme.Modules.fromTildeΓ (R := R A 0) (N.P 0)).app V) :=
    ConcreteCategory.bijective_of_isIso _
  rw [ψ0, Adjunction.homEquiv_counit]
  exact h2.comp h1

lemma ψ1_app_bijective (V : (Spec (R A 1)).Opens) (hV : V ≤ PrimeSpectrum.basicOpen (coord A 1)) :
    Function.Bijective (N.ψ1.app V) := by
  haveI : IsIso (Scheme.Modules.fromTildeΓ (R := R A 1) (N.P 1)) :=
    isIso_fromTildeΓ_pushforward (R := R A 1) (S := R01 A) (ρ A 1) (tilde N.mod01)
  haveI : IsLocalizedModule (.powers (coord A 1)) N.gl1.hom := N.isLocalizedModule_gl1
  have h1 := tilde_map_app_bijective N.gl1 (coord A 1) V hV
  have h2 : Function.Bijective ((Scheme.Modules.fromTildeΓ (R := R A 1) (N.P 1)).app V) :=
    ConcreteCategory.bijective_of_isIso _
  rw [ψ1, Adjunction.homEquiv_counit]
  exact h2.comp h1

lemma φ0_app_apply (W : (scheme A).Opens) (x : Γ(N.G0, W)) :
    N.φ0.app W x = N.ψ0.app (chartι A 0 ⁻¹ᵁ W) x := rfl

lemma φ1_app_apply (W : (scheme A).Opens) (x : Γ(N.G1, W)) :
    N.φ1.app W x = (tilde N.mod01).presheaf.map (eqToHom (by rw [chartι_comp] :
      (Spec.map (ρ A 0) ≫ chartι A 0) ⁻¹ᵁ W = (Spec.map (ρ A 1) ≫ chartι A 1) ⁻¹ᵁ W)).op
        (N.ψ1.app (chartι A 1 ⁻¹ᵁ W) x) := rfl

lemma φ0_app_bijective (W : (scheme A).Opens) (hW : W ≤ U A 1) :
    Function.Bijective (N.φ0.app W) := by
  have h1 := N.ψ0_app_bijective (chartι A 0 ⁻¹ᵁ W)
    ((Scheme.Hom.preimage_mono _ hW).trans (chartι_preimage_rev (A := A) 0).le)
  rw [show ⇑(N.φ0.app W) = ⇑(N.ψ0.app (chartι A 0 ⁻¹ᵁ W)) from funext (N.φ0_app_apply W)]
  exact h1

lemma φ1_app_bijective (W : (scheme A).Opens) (hW : W ≤ U A 0) :
    Function.Bijective (N.φ1.app W) := by
  have h1 := N.ψ1_app_bijective (chartι A 1 ⁻¹ᵁ W)
    ((Scheme.Hom.preimage_mono _ hW).trans (chartι_preimage_rev (A := A) 1).le)
  rw [show ⇑(N.φ1.app W) = _ ∘ ⇑(N.ψ1.app (chartι A 1 ⁻¹ᵁ W)) from funext (N.φ1_app_apply W)]
  exact (ConcreteCategory.bijective_of_isIso _).comp h1

/-- Over `W ⊆ U₀`, a section of the glued module is its `Ñ₀`-component. -/
lemma glue_fst_bijective (W : (scheme A).Opens) (hW : W ≤ U A 0) :
    Function.Bijective ((fiberProd.fst N.φ0 N.φ1).app W) := by
  have h := N.φ1_app_bijective W hW
  refine ⟨fun p q hpq ↦ fiberProd.ext hpq (h.1 ?_), fun a ↦ ?_⟩
  · rw [← fiberProd.cond, ← fiberProd.cond, hpq]
  · obtain ⟨b, hb⟩ := h.2 (N.φ0.app W a)
    exact ⟨fiberProd.mk a b hb.symm, rfl⟩

/-- Over `W ⊆ U₁`, a section of the glued module is its `Ñ₁`-component. -/
lemma glue_snd_bijective (W : (scheme A).Opens) (hW : W ≤ U A 1) :
    Function.Bijective ((fiberProd.snd N.φ0 N.φ1).app W) := by
  have h := N.φ0_app_bijective W hW
  refine ⟨fun p q hpq ↦ fiberProd.ext (h.1 ?_) hpq, fun b ↦ ?_⟩
  · rw [fiberProd.cond, fiberProd.cond, hpq]
  · obtain ⟨a, ha⟩ := h.2 (N.φ1.app W b)
    exact ⟨fiberProd.mk a b ha, rfl⟩

/-! ### The glued module is quasi-coherent -/

lemma restrict_fst_isIso :
    IsIso ((restrictFunctor (chartι A 0)).map (fiberProd.fst N.φ0 N.φ1)) := by
  rw [Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  exact N.glue_fst_bijective _ ((Scheme.Hom.image_le_opensRange _ V).trans
    (isAffineOpen_U A 0).opensRange_fromSpec.le)

lemma restrict_snd_isIso :
    IsIso ((restrictFunctor (chartι A 1)).map (fiberProd.snd N.φ0 N.φ1)) := by
  rw [Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  exact N.glue_snd_bijective _ ((Scheme.Hom.image_le_opensRange _ V).trans
    (isAffineOpen_U A 1).opensRange_fromSpec.le)

/-- `Ñ₀ ≅ (glued module)|_{U₀}`. -/
noncomputable def restrictIso0 :
    (tilde.functor (R A 0)).obj N.mod0 ≅ N.glue.restrict (chartι A 0) :=
  haveI := N.restrict_fst_isIso
  ((restrictFunctorAdjCounitIso (chartι A 0)).app _).symm ≪≫
    (asIso ((restrictFunctor (chartι A 0)).map (fiberProd.fst N.φ0 N.φ1))).symm

/-- `Ñ₁ ≅ (glued module)|_{U₁}`. -/
noncomputable def restrictIso1 :
    (tilde.functor (R A 1)).obj N.mod1 ≅ N.glue.restrict (chartι A 1) :=
  haveI := N.restrict_snd_isIso
  ((restrictFunctorAdjCounitIso (chartι A 1)).app _).symm ≪≫
    (asIso ((restrictFunctor (chartι A 1)).map (fiberProd.snd N.φ0 N.φ1))).symm

/-- The glued module has a presentation on each chart. -/
noncomputable def presentationChart : ∀ k : Fin 2, (N.glue.restrict (U A k).ι).Presentation
  | 0 => presentationRestrictι (isAffineOpen_U A 0) _
      ((presentationTildeSelf N.mod0).ofIsIso N.restrictIso0.hom)
  | 1 => presentationRestrictι (isAffineOpen_U A 1) _
      ((presentationTildeSelf N.mod1).ofIsIso N.restrictIso1.hom)

/-- **The glued module of a chart module is quasi-coherent.** -/
instance isQuasicoherent_glue : N.glue.IsQuasicoherent :=
  isQuasicoherent_of_presentation N.glue (fun i : ULift.{u} (Fin 2) ↦ U A i.down)
    (by
      refine le_antisymm le_top ((U_sup A).symm.le.trans (sup_le ?_ ?_))
      · exact le_iSup (fun i : ULift.{u} (Fin 2) ↦ U A i.down) ⟨0⟩
      · exact le_iSup (fun i : ULift.{u} (Fin 2) ↦ U A i.down) ⟨1⟩)
    fun i ↦ N.presentationChart i.down

end ChartModule

end ProjectiveLine
