/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ProjectiveLineTwistingSheaf
import FormalSchemes.ChartModuleHom
import FormalSchemes.QcohAffineLocalization

/-!
# Quasi-coherent modules on `ℙ¹_A` as chart modules

A quasi-coherent module `F` on `ℙ¹_A` gives a chart module (`ProjectiveLine.chartModule F`): the
`A`-modules `Γ(F, U₀)`, `Γ(F, U₁)`, `Γ(F, U₀ ∩ U₁)` with multiplication by the chart coordinates
`x₁/x₀`, `x₀/x₁` and by `T = x₁/x₀` on the overlap. The localisation axioms hold because
`U₀ ∩ U₁ = D(x₁/x₀) ⊆ U₀` (`ProjectiveLine.basicOpen_coord`) and restriction to a basic open of an
affine open is a localisation for quasi-coherent modules
(`Scheme.Modules.exists_pow_smul_eq_res`, `Scheme.Modules.exists_pow_smul_eq_zero`). Moreover:

* `ProjectiveLine.globalSectionsEquiv`: `Γ(ℙ¹_A, F) ≃ H⁰(chartModule F)` as `A`-modules;
* `ProjectiveLine.cechH0ChartModuleEquiv`, `ProjectiveLine.cechH1ChartModuleEquiv`: the Čech
  cohomology of `F` for the standard covering is the `H⁰`/`H¹` of its chart module;
* `ProjectiveLine.chartModuleMap`: morphisms of modules give morphisms of chart modules.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite AlgebraicGeometry.Scheme.Modules
  HomogeneousLocalization

namespace ProjectiveLine

variable (A : Type u) [CommRing A]

/-- The chart coordinate `x_{1-k}/x_k` as a section over `U_k`. -/
noncomputable def coord (k : Fin 2) : Γ(scheme A, U A k) :=
  Proj.awayToSection (grading A) (MvPolynomial.X k) (chartCoord k)

lemma isLocalizationElem_eq' (k : Fin 2) :
    Away.isLocalizationElem (X_mem (A := A) k) (X_mem k.rev) = chartCoord k := by
  apply val_injective
  simp [chartCoord, Away.val_mk]

lemma fromSpec_eq (k : Fin 2) : (isAffineOpen_U A k).fromSpec =
    Spec.map (Proj.awayToSection (grading A) (MvPolynomial.X k)) ≫
      Proj.awayι (grading A) (MvPolynomial.X k) (X_mem k) one_pos := by
  rw [Proj.awayι, ← IsAffineOpen.isoSpec_inv_ι, ← Category.assoc]
  congr 1
  refine (Iso.eq_comp_inv _).2 ?_
  rw [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec]
  exact IsAffineOpen.isoSpec_inv_toSpecΓ_assoc (isAffineOpen_U A k) _

lemma basicOpen_coord (k : Fin 2) : (scheme A).basicOpen (coord A k) = U A k ⊓ U A k.rev := by
  have hU := isAffineOpen_U A k
  have hpre : hU.fromSpec ⁻¹ᵁ U A k.rev = PrimeSpectrum.basicOpen (coord A k) := by
    rw [fromSpec_eq]
    change Spec.map _ ⁻¹ᵁ (Proj.awayι (grading A) (MvPolynomial.X k) (X_mem k) one_pos ⁻¹ᵁ
      Proj.basicOpen (grading A) (MvPolynomial.X k.rev)) = _
    rw [Proj.awayι_preimage_basicOpen (grading A) (X_mem k) one_pos (X_mem k.rev) one_pos,
      isLocalizationElem_eq', SpecMap_preimage_basicOpen]
    rfl
  rw [← hU.fromSpec_image_basicOpen, ← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf,
    hU.opensRange_fromSpec]


/-! ### The chart coordinates on the overlap -/

lemma transition_mul_neg (d : ℤ) : transition A d * transition A (-d) = 1 :=
  (overlapSections A).injective <| by
    rw [map_mul, overlapSections_transition, overlapSections_transition,
      ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, map_one]

lemma res_coord_zero :
    (scheme A).presheaf.map (homOfLE inf_le_left : U A 0 ⊓ U A 1 ⟶ U A 0).op (coord A 0) =
      transition A 1 :=
  (overlapSections A).injective <| by
    rw [overlapSections_res_zero, overlapSections_transition, coord,
      chartSections_awayToSection, chartEquiv_chartCoord, Polynomial.toLaurent_X]

lemma res_coord_one :
    (scheme A).presheaf.map (homOfLE inf_le_right : U A 0 ⊓ U A 1 ⟶ U A 1).op (coord A 1) =
      transition A (-1) :=
  (overlapSections A).injective <| by
    rw [overlapSections_res_one, overlapSections_transition, coord,
      chartSections_awayToSection, chartEquiv_chartCoord, Polynomial.toLaurent_X,
      LaurentPolynomial.invert_T]

/-! ### Sections as `A`-modules -/

/-- The structure map `A → Γ(ℙ¹_A, 𝒪)`. -/
noncomputable def structMap : A →+* Γ(scheme A, ⊤) :=
  ((Scheme.ΓSpecIso _).inv ≫ (Proj.toSpecZero (grading A)).appTop).hom.comp (constZero A)

/-- The structure map `A → Γ(W, 𝒪)`. -/
noncomputable def secMap (W : (scheme A).Opens) : A →+* Γ(scheme A, W) :=
  ((scheme A).presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom.comp (structMap A)

lemma res_secMap {W W' : (scheme A).Opens} (h : W' ≤ W) (a : A) :
    (scheme A).presheaf.map (homOfLE h).op (secMap A W a) = secMap A W' a := by
  simp only [secMap, RingHom.coe_comp, Function.comp_apply]
  rw [scheme_presheaf_map_map_comp]
  rfl

variable {A} (F : (scheme A).Modules)

/-- `Γ(F, W)` as an `A`-module. -/
noncomputable def secA (W : (scheme A).Opens) : ModuleCat.{u} A :=
  letI : Module A Γ(F, W) := Module.compHom _ (secMap A W)
  ModuleCat.of A Γ(F, W)

lemma secA_smul {W : (scheme A).Opens} (a : A) (m : secA F W) :
    a • m = (show Γ(F, W) from secMap A W a • (show Γ(F, W) from m)) := rfl

/-- The restriction `Γ(F, W) → Γ(F, W')`, as an `A`-linear map. -/
noncomputable def resA {W W' : (scheme A).Opens} (h : W' ≤ W) : secA F W →ₗ[A] secA F W' where
  toFun m := F.presheaf.map (homOfLE h).op (show Γ(F, W) from m)
  map_add' x y := map_add (ConcreteCategory.hom (F.presheaf.map (homOfLE h).op))
    (show Γ(F, W) from x) y
  map_smul' a m := (Scheme.Modules.map_smul F (homOfLE h) (secMap A W a)
    (show Γ(F, W) from m)).trans (congrArg (· • _) (res_secMap A h a))

/-- Multiplication by a function, as an `A`-linear map. -/
noncomputable def smulA {W : (scheme A).Opens} (r : Γ(scheme A, W)) : secA F W →ₗ[A] secA F W where
  toFun m := (show Γ(F, W) from r • (show Γ(F, W) from m))
  map_add' x y := smul_add r (show Γ(F, W) from x) y
  map_smul' a m := by
    change r • (secMap A W a • (show Γ(F, W) from m)) =
      (show Γ(F, W) from secMap A W a • (r • (show Γ(F, W) from m)))
    rw [smul_smul, smul_smul, mul_comm]

lemma smulA_apply {W : (scheme A).Opens} (r : Γ(scheme A, W)) (m : secA F W) :
    smulA F r m = (show Γ(F, W) from r • (show Γ(F, W) from m)) := rfl

lemma smulA_pow_apply {W : (scheme A).Opens} (r : Γ(scheme A, W)) (k : ℕ) (m : secA F W) :
    (smulA F r ^ k) m = (show Γ(F, W) from r ^ k • (show Γ(F, W) from m)) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact (one_smul Γ(scheme A, W) (show Γ(F, W) from m)).symm
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, smulA_apply]
    exact (smul_smul r (r ^ k) (show Γ(F, W) from m)).trans (by rw [← pow_succ'])

/-- Multiplication by `T` on `Γ(F, U₀ ∩ U₁)`. -/
noncomputable def tA : secA F (U A 0 ⊓ U A 1) ≃ₗ[A] secA F (U A 0 ⊓ U A 1) :=
  LinearEquiv.ofLinear (smulA F (transition A 1)) (smulA F (transition A (-1)))
    (LinearMap.ext fun m ↦ (smul_smul (transition A 1) (transition A (-1))
      (show Γ(F, U A 0 ⊓ U A 1) from m)).trans (by rw [transition_mul_neg A 1, one_smul]; rfl))
    (LinearMap.ext fun m ↦ (smul_smul (transition A (-1)) (transition A 1)
      (show Γ(F, U A 0 ⊓ U A 1) from m)).trans (by
        rw [mul_comm, transition_mul_neg A 1, one_smul]; rfl))

lemma tA_pow_apply (k : ℕ) (m : secA F (U A 0 ⊓ U A 1)) :
    (tA F ^ k) m = (show Γ(F, U A 0 ⊓ U A 1) from transition A 1 ^ k •
      (show Γ(F, U A 0 ⊓ U A 1) from m)) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact (one_smul Γ(scheme A, U A 0 ⊓ U A 1) (show Γ(F, U A 0 ⊓ U A 1) from m)).symm
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih]
    exact (smul_smul (transition A 1) (transition A 1 ^ k)
      (show Γ(F, U A 0 ⊓ U A 1) from m)).trans (by rw [← pow_succ'])

lemma tA_symm_pow_apply (k : ℕ) (m : secA F (U A 0 ⊓ U A 1)) :
    ((tA F).symm ^ k) m = (show Γ(F, U A 0 ⊓ U A 1) from transition A (-1) ^ k •
      (show Γ(F, U A 0 ⊓ U A 1) from m)) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact (one_smul Γ(scheme A, U A 0 ⊓ U A 1) (show Γ(F, U A 0 ⊓ U A 1) from m)).symm
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih]
    exact (smul_smul (transition A (-1)) (transition A (-1) ^ k)
      (show Γ(F, U A 0 ⊓ U A 1) from m)).trans (by rw [← pow_succ'])

/-! ### The chart module of a quasi-coherent module -/

lemma exists_pow_smul_eq_res' {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W)
    (M : X.Modules) [M.IsQuasicoherent] (f : Γ(X, W)) {V : X.Opens} (hV : X.basicOpen f = V)
    (hVW : V ≤ W) (z : Γ(M, V)) : ∃ (m : Γ(M, W)) (k : ℕ),
      X.presheaf.map (homOfLE hVW).op (f ^ k) • z = M.presheaf.map (homOfLE hVW).op m := by
  subst hV
  exact exists_pow_smul_eq_res hW M f z

lemma exists_pow_smul_eq_zero' {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W)
    (M : X.Modules) [M.IsQuasicoherent] (f : Γ(X, W)) {V : X.Opens} (hV : X.basicOpen f = V)
    (hVW : V ≤ W) (m : Γ(M, W)) (hm : M.presheaf.map (homOfLE hVW).op m = 0) :
    ∃ k : ℕ, f ^ k • m = 0 := by
  subst hV
  exact exists_pow_smul_eq_zero hW M f m hm

lemma basicOpen_coord_zero : (scheme A).basicOpen (coord A 0) = U A 0 ⊓ U A 1 :=
  basicOpen_coord A 0

lemma basicOpen_coord_one : (scheme A).basicOpen (coord A 1) = U A 0 ⊓ U A 1 :=
  (basicOpen_coord A 1).trans (inf_comm _ _)

/-- **The chart module of a quasi-coherent module `F` on `ℙ¹_A`**: its sections over the two
standard charts and their overlap, with multiplication by the chart coordinates. -/
noncomputable def chartModule [F.IsQuasicoherent] : ChartModule A where
  M0 := secA F (U A 0)
  M1 := secA F (U A 1)
  M01 := secA F (U A 0 ⊓ U A 1)
  x0 := smulA F (coord A 0)
  x1 := smulA F (coord A 1)
  t := tA F
  r0 := resA F inf_le_left
  r1 := resA F inf_le_right
  r0_x0 m := by
    change F.presheaf.map _ (coord A 0 • (show Γ(F, U A 0) from m)) =
      (show Γ(F, U A 0 ⊓ U A 1) from transition A 1 • F.presheaf.map _ m)
    rw [Scheme.Modules.map_smul, res_coord_zero]
  r1_x1 m := by
    change F.presheaf.map _ (coord A 1 • (show Γ(F, U A 1) from m)) =
      (show Γ(F, U A 0 ⊓ U A 1) from transition A (-1) • F.presheaf.map _ m)
    rw [Scheme.Modules.map_smul, res_coord_one]
  exists_r0 z := by
    obtain ⟨m, k, hk⟩ := exists_pow_smul_eq_res' (isAffineOpen_U A 0) F (coord A 0)
      (basicOpen_coord_zero (A := A)) inf_le_left z
    refine ⟨m, k, ?_⟩
    rw [tA_pow_apply, ← res_coord_zero, ← map_pow]
    exact hk
  ker_r0 m hm := by
    obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero' (isAffineOpen_U A 0) F (coord A 0)
      (basicOpen_coord_zero (A := A)) inf_le_left m hm
    exact ⟨k, (smulA_pow_apply F _ k m).trans hk⟩
  exists_r1 z := by
    obtain ⟨m, k, hk⟩ := exists_pow_smul_eq_res' (isAffineOpen_U A 1) F (coord A 1)
      (basicOpen_coord_one (A := A)) inf_le_right z
    refine ⟨m, k, ?_⟩
    rw [tA_symm_pow_apply, ← res_coord_one, ← map_pow]
    exact hk
  ker_r1 m hm := by
    obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero' (isAffineOpen_U A 1) F (coord A 1)
      (basicOpen_coord_one (A := A)) inf_le_right m hm
    exact ⟨k, (smulA_pow_apply F _ k m).trans hk⟩

/-- **Čech `H¹`**: the `H¹` of the chart module of `F` is the Čech `H¹` of `F` for the standard
covering. -/
noncomputable def cechH1ChartModuleEquiv [F.IsQuasicoherent] :
    cechH1 F (U A 0) (U A 1) ≃ₗ[ℤ] (chartModule F).H1 :=
  TwoCech.H1RestrictScalarsEquiv (chartModule F).r0 (chartModule F).r1

/-- **Čech `H⁰`**: the `H⁰` of the chart module of `F` is the Čech `H⁰` of `F`. -/
noncomputable def cechH0ChartModuleEquiv [F.IsQuasicoherent] :
    cechH0 F (U A 0) (U A 1) ≃ₗ[ℤ] (chartModule F).H0.restrictScalars ℤ :=
  TwoCech.H0RestrictScalarsEquiv (chartModule F).r0 (chartModule F).r1

/-- Restricting global sections to the two charts. -/
noncomputable def toH0 [F.IsQuasicoherent] : secA F ⊤ →ₗ[A] (chartModule F).H0 :=
  LinearMap.codRestrict _ ((resA F le_top).prod (resA F le_top)) fun s ↦ by
    rw [TwoCech.mem_H0]
    change F.presheaf.map _ (F.presheaf.map _ (show Γ(F, ⊤) from s)) =
      F.presheaf.map _ (F.presheaf.map _ (show Γ(F, ⊤) from s))
    rw [res_res F _ _ (homOfLE le_top), res_res]

/-- The composite `Γ(F, ⊤) ≃ Ȟ⁰(F) ≃ H⁰(chartModule F)` over `ℤ`. -/
noncomputable def globalSectionsEquivℤ [F.IsQuasicoherent] :
    Γ(F, ⊤) ≃ₗ[ℤ] (chartModule F).H0.restrictScalars ℤ :=
  (topSectionsEquiv A F).trans ((cechH0Equiv F (U A 0) (U A 1)).trans (cechH0ChartModuleEquiv F))

lemma toH0_eq [F.IsQuasicoherent] (s : secA F ⊤) :
    ((toH0 F s : (chartModule F).H0) : (chartModule F).M0 × (chartModule F).M1) =
      (globalSectionsEquivℤ F s : (chartModule F).M0 × (chartModule F).M1) :=
  Prod.ext (res_res F (eqToHom (U_sup A)) (homOfLE le_sup_left) _ s).symm
    (res_res F (eqToHom (U_sup A)) (homOfLE le_sup_right) _ s).symm

lemma toH0_bijective [F.IsQuasicoherent] : Function.Bijective (toH0 F) := by
  constructor
  · intro s s' h
    apply (globalSectionsEquivℤ F).injective
    apply Subtype.ext
    rw [← toH0_eq, ← toH0_eq, h]
  · intro x
    refine ⟨(globalSectionsEquivℤ F).symm ⟨x.1, x.2⟩, Subtype.ext ?_⟩
    rw [toH0_eq, LinearEquiv.apply_symm_apply]

/-- **Global sections**: `Γ(ℙ¹_A, F)` is the `H⁰` of the chart module of `F`, as `A`-modules
(the sheaf axiom for the standard covering). -/
noncomputable def globalSectionsEquiv [F.IsQuasicoherent] : secA F ⊤ ≃ₗ[A] (chartModule F).H0 :=
  LinearEquiv.ofBijective (toH0 F) (toH0_bijective F)

/-! ### Functoriality -/

variable {F} {G H : (scheme A).Modules}

/-- A morphism of modules on sections over `W`, as an `A`-linear map. -/
noncomputable def appA (φ : F ⟶ G) (W : (scheme A).Opens) : secA F W →ₗ[A] secA G W where
  toFun m := φ.app W (show Γ(F, W) from m)
  map_add' x y := map_add (ConcreteCategory.hom (φ.app W)) (show Γ(F, W) from x) y
  map_smul' a m := Scheme.Modules.Hom.app_smul φ (secMap A W a) (show Γ(F, W) from m)

/-- The morphism of chart modules induced by a morphism of quasi-coherent modules. -/
noncomputable def chartModuleMap [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    ChartModule.Hom (chartModule F) (chartModule G) where
  f0 := appA φ _
  f1 := appA φ _
  f01 := appA φ _
  comm_x0 m := Scheme.Modules.Hom.app_smul φ (coord A 0) (show Γ(F, U A 0) from m)
  comm_x1 m := Scheme.Modules.Hom.app_smul φ (coord A 1) (show Γ(F, U A 1) from m)
  comm_t z := Scheme.Modules.Hom.app_smul φ (transition A 1) (show Γ(F, U A 0 ⊓ U A 1) from z)
  comm_r0 m := LinearMap.congr_fun (appℤ_comp_resℤ φ (inf_le_left : U A 0 ⊓ U A 1 ≤ U A 0))
    (show Γ(F, U A 0) from m)
  comm_r1 m := LinearMap.congr_fun (appℤ_comp_resℤ φ (inf_le_right : U A 0 ⊓ U A 1 ≤ U A 1))
    (show Γ(F, U A 1) from m)

lemma chartModuleMap_comp [F.IsQuasicoherent] [G.IsQuasicoherent] [H.IsQuasicoherent]
    (φ : F ⟶ G) (ψ : G ⟶ H) :
    chartModuleMap (φ ≫ ψ) = (chartModuleMap ψ).comp (chartModuleMap φ) :=
  ChartModule.Hom.ext' rfl rfl rfl

end ProjectiveLine
