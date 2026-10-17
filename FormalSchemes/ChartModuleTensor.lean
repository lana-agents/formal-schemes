/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleTensorBalanced
import FormalSchemes.ChartModuleAdic

/-!
# The tensor product of chart modules

For chart modules `M`, `N` (quasi-coherent modules on `ℙ¹_A`, `ProjectiveLine.ChartModule`),
`ChartModule.tensor M N` is `M ⊗ N`: on the charts `Spec A[X]`, `Spec A[Y]` and
`Spec A[T, T⁻¹]` its sections are the tensor products `M₀ ⊗_{A[X]} N₀`, `M₁ ⊗_{A[Y]} N₁` and
`M₀₁ ⊗_{A[T, T⁻¹]} N₀₁` (the last one computed over `A[X]`, `X` acting by `T`, which is the same
since `T` acts invertibly). The localization axioms hold because tensor products commute with
localization (`BTensor.exists_xmul_pow_eq_zero`).

* `ChartModule.Hom.tensor`: functoriality, `Hom.tensor_comp`, `Hom.tensor_id`;
* `ChartModule.assoc`, `ChartModule.braid`: associativity and symmetry, natural
  (`ChartModule.assoc_natural`);
* `ChartModule.finite_tensor_x0`, `ChartModule.finite_tensor_x1`: the tensor product of
  coherent modules is coherent.
-/

universe u

open Polynomial TensorProduct

namespace ProjectiveLine

namespace ChartModule

open BTensor

variable {A : Type u} [CommRing A]

section TInv

variable {R S : Type u} [AddCommGroup R] [Module A R] [AddCommGroup S] [Module A S]
  (τ : R ≃ₗ[A] R) (σ : S ≃ₗ[A] S)

/-- Multiplication by `T`, an automorphism of `R ⊗_{A[T]} S`. -/
noncomputable def tEquiv :
    BTensor (τ : R →ₗ[A] R) (σ : S →ₗ[A] S) ≃ₗ[A] BTensor (τ : R →ₗ[A] R) (σ : S →ₗ[A] S) :=
  LinearEquiv.ofLinear (xmul _ _)
    (bmap τ.symm.toLinearMap LinearMap.id (fun p ↦ by simp) (fun _ ↦ rfl))
    (BTensor.ext fun p q ↦ by simp [xmul_tm])
    (BTensor.ext fun p q ↦ by simp [xmul_tm])

lemma tEquiv_apply (w : BTensor (τ : R →ₗ[A] R) (σ : S →ₗ[A] S)) :
    tEquiv τ σ w = xmul _ _ w := rfl

lemma tEquiv_symm_tm (p : R) (q : S) :
    (tEquiv τ σ).symm (tm _ _ p q) = tm _ _ (τ.symm p) q := by
  simp [tEquiv]

lemma tEquiv_symm_tm' (p : R) (q : S) :
    (tEquiv τ σ).symm (tm _ _ p q) = tm _ _ p (σ.symm q) := by
  rw [tEquiv_symm_tm]
  have := tm_f (f := (τ : R →ₗ[A] R)) (g := (σ : S →ₗ[A] S)) (τ.symm p) (σ.symm q)
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
  exact this.symm

/-- `R ⊗ S` computed with `X` acting by `T⁻¹` is `R ⊗ S` computed with `X` acting by `T`. -/
noncomputable def retensor :
    BTensor (τ.symm : R →ₗ[A] R) (σ.symm : S →ₗ[A] S) ≃ₗ[A]
      BTensor (τ : R →ₗ[A] R) (σ : S →ₗ[A] S) :=
  LinearEquiv.ofLinear
    (blift (tEquiv τ σ).symm.toLinearMap (tmBil _ _)
      (fun p q ↦ by simp [tEquiv_symm_tm]) (fun p q ↦ by simp [tEquiv_symm_tm']))
    (blift (tEquiv τ.symm σ.symm).symm.toLinearMap (tmBil _ _)
      (fun p q ↦ by simp [tEquiv_symm_tm]) (fun p q ↦ by simp [tEquiv_symm_tm']))
    (BTensor.ext fun p q ↦ by simp)
    (BTensor.ext fun p q ↦ by simp)

@[simp] lemma retensor_tm (p : R) (q : S) : retensor τ σ (tm _ _ p q) = tm _ _ p q := by
  simp [retensor]

lemma retensor_xmul (w : BTensor (τ.symm : R →ₗ[A] R) (σ.symm : S →ₗ[A] S)) :
    retensor τ σ (xmul _ _ w) = (tEquiv τ σ).symm (retensor τ σ w) := by
  simp only [retensor, LinearEquiv.ofLinear_apply]
  exact blift_xmul _ _ _ _ w

lemma equiv_pow_apply (e : R ≃ₗ[A] R) (k : ℕ) (z : R) : (e ^ k) z = ((e : R →ₗ[A] R) ^ k) z :=
  (BTensor.pow_apply_eq (τ := e) k z).symm

end TInv

section AEvalX

variable {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
  {f : P →ₗ[A] P} {g : Q →ₗ[A] Q}

/-- `BTensor f g`, viewed as `Module.AEval'` of an endomorphism acting as `X`. -/
noncomputable def aevalXmul (k : BTensor f g →ₗ[A] BTensor f g) (hk : ∀ w, k w = (X : A[X]) • w) :
    Module.AEval' k ≃ₗ[A[X]] BTensor f g :=
  LinearEquiv.ofAEval (R := A) (M := BTensor f g) k (LinearEquiv.refl A _) fun w ↦ by
    simp only [LinearEquiv.refl_apply, Module.End.smul_def]
    exact hk w

lemma aevalXmul_of (k : BTensor f g →ₗ[A] BTensor f g) (hk : ∀ w, k w = (X : A[X]) • w)
    (w : BTensor f g) : aevalXmul k hk (Module.AEval'.of k w) = w := rfl

lemma aevalXmul_symm (k : BTensor f g →ₗ[A] BTensor f g) (hk : ∀ w, k w = (X : A[X]) • w)
    (w : BTensor f g) : (aevalXmul k hk).symm w = Module.AEval'.of k w := rfl

end AEvalX

/-! ### The tensor product -/

variable (M N : ChartModule A)

/-- **The tensor product of chart modules.** -/
noncomputable abbrev tensor : ChartModule A where
  M0 := ModuleCat.of A (BTensor M.x0 N.x0)
  M1 := ModuleCat.of A (BTensor M.x1 N.x1)
  M01 := ModuleCat.of A (BTensor (M.t : M.M01 →ₗ[A] M.M01) (N.t : N.M01 →ₗ[A] N.M01))
  x0 := xmul _ _
  x1 := xmul _ _
  t := tEquiv M.t N.t
  r0 := bmap M.r0 N.r0 M.r0_x0 N.r0_x0
  r1 := (retensor M.t N.t).toLinearMap ∘ₗ
    bmap (f' := (M.t.symm : M.M01 →ₗ[A] M.M01)) (g' := (N.t.symm : N.M01 →ₗ[A] N.M01))
      M.r1 N.r1 M.r1_x1 N.r1_x1
  r0_x0 m := bmap_xmul _ _ _ _ m
  r1_x1 m := by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [bmap_xmul, retensor_xmul]
  exists_r0 z := by
    obtain ⟨w, k, hk⟩ := exists_bmap M.r0_x0 M.exists_r0 N.r0_x0 N.exists_r0 z
    exact ⟨w, k, by rw [equiv_pow_apply]; exact hk⟩
  ker_r0 m hm := exists_xmul_pow_eq_zero M.r0_x0 M.exists_r0 M.ker_r0 N.r0_x0 N.exists_r0
    N.ker_r0 m hm
  exists_r1 z := by
    obtain ⟨w, k, hk⟩ := exists_bmap (τ := M.t.symm) (σ := N.t.symm) M.r1_x1 M.exists_r1 N.r1_x1
      N.exists_r1 ((retensor M.t N.t).symm z)
    refine ⟨w, k, ?_⟩
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ← hk]
    clear hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, pow_succ', Module.End.mul_apply, retensor_xmul]
  ker_r1 m hm := by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.map_eq_zero_iff] at hm
    exact exists_xmul_pow_eq_zero (τ := M.t.symm) (σ := N.t.symm) M.r1_x1 M.exists_r1 M.ker_r1
      N.r1_x1 N.exists_r1 N.ker_r1 m hm

variable {M N}

@[simp] lemma tensor_x0_tm (a : M.M0) (b : N.M0) :
    (tensor M N).x0 (tm _ _ a b) = tm _ _ (M.x0 a) b := xmul_tm a b

@[simp] lemma tensor_x1_tm (a : M.M1) (b : N.M1) :
    (tensor M N).x1 (tm _ _ a b) = tm _ _ (M.x1 a) b := xmul_tm a b

@[simp] lemma tensor_t_tm (a : M.M01) (b : N.M01) :
    (tensor M N).t (tm _ _ a b) = tm _ _ (M.t a) b := xmul_tm a b

@[simp] lemma tensor_r0_tm (a : M.M0) (b : N.M0) :
    (tensor M N).r0 (tm _ _ a b) = tm _ _ (M.r0 a) (N.r0 b) := bmap_tm _ _ _ _ a b

@[simp] lemma tensor_r1_tm (a : M.M1) (b : N.M1) :
    (tensor M N).r1 (tm _ _ a b) = tm _ _ (M.r1 a) (N.r1 b) := by
  change retensor M.t N.t (bmap _ _ _ _ (tm _ _ a b)) = _
  rw [bmap_tm, retensor_tm]

/-! ### Finiteness -/

instance finite_aeval_xmul {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q]
    [Module A Q] {f : P →ₗ[A] P} {g : Q →ₗ[A] Q} [Module.Finite A[X] (Module.AEval' f)]
    [Module.Finite A[X] (Module.AEval' g)] : Module.Finite A[X] (Module.AEval' (xmul f g)) :=
  Module.Finite.equiv (aevalXmul (xmul f g) fun _ ↦ rfl).symm

lemma finite_tensor_x0 [Module.Finite A[X] (Module.AEval' M.x0)]
    [Module.Finite A[X] (Module.AEval' N.x0)] :
    Module.Finite A[X] (Module.AEval' (tensor M N).x0) := inferInstance

lemma finite_tensor_x1 [Module.Finite A[X] (Module.AEval' M.x1)]
    [Module.Finite A[X] (Module.AEval' N.x1)] :
    Module.Finite A[X] (Module.AEval' (tensor M N).x1) := inferInstance

/-! ### Functoriality -/

variable {M' N' M'' N'' : ChartModule A}

/-- **The tensor product of morphisms.** -/
noncomputable def Hom.tensor (φ : Hom M M') (ψ : Hom N N') :
    Hom (ChartModule.tensor M N) (ChartModule.tensor M' N') where
  f0 := bmap φ.f0 ψ.f0 φ.comm_x0 ψ.comm_x0
  f1 := bmap φ.f1 ψ.f1 φ.comm_x1 ψ.comm_x1
  f01 := bmap φ.f01 ψ.f01 φ.comm_t ψ.comm_t
  comm_x0 m := bmap_xmul _ _ _ _ m
  comm_x1 m := bmap_xmul _ _ _ _ m
  comm_t z := bmap_xmul _ _ _ _ z
  comm_r0 m := by
    induction m using BTensor.induction_on with
    | h0 => simp
    | htm a b =>
      change bmap _ _ _ _ ((ChartModule.tensor M N).r0 (tm _ _ a b)) =
        (ChartModule.tensor M' N').r0 (bmap _ _ _ _ (tm _ _ a b))
      simp [φ.comm_r0, ψ.comm_r0]
    | hadd x y hx hy => simp only [map_add, hx, hy]
  comm_r1 m := by
    induction m using BTensor.induction_on with
    | h0 => simp
    | htm a b =>
      change bmap _ _ _ _ ((ChartModule.tensor M N).r1 (tm _ _ a b)) =
        (ChartModule.tensor M' N').r1 (bmap _ _ _ _ (tm _ _ a b))
      simp [φ.comm_r1, ψ.comm_r1]
    | hadd x y hx hy => simp only [map_add, hx, hy]

@[simp] lemma Hom.tensor_f0_tm (φ : Hom M M') (ψ : Hom N N') (a : M.M0) (b : N.M0) :
    (φ.tensor ψ).f0 (tm _ _ a b) = tm _ _ (φ.f0 a) (ψ.f0 b) := bmap_tm _ _ _ _ a b

@[simp] lemma Hom.tensor_f1_tm (φ : Hom M M') (ψ : Hom N N') (a : M.M1) (b : N.M1) :
    (φ.tensor ψ).f1 (tm _ _ a b) = tm _ _ (φ.f1 a) (ψ.f1 b) := bmap_tm _ _ _ _ a b

lemma Hom.tensor_comp (φ : Hom M M') (ψ : Hom N N') (φ' : Hom M' M'') (ψ' : Hom N' N'') :
    (φ'.comp φ).tensor (ψ'.comp ψ) = (φ'.tensor ψ').comp (φ.tensor ψ) :=
  Hom.ext' (bmap_comp _ _ _ _ _ _ _ _).symm (bmap_comp _ _ _ _ _ _ _ _).symm
    (bmap_comp _ _ _ _ _ _ _ _).symm

lemma Hom.tensor_id : (Hom.id M).tensor (Hom.id N) = Hom.id (ChartModule.tensor M N) :=
  Hom.ext' bmap_id bmap_id bmap_id

/-! ### Associativity and symmetry -/

section Assoc

variable {P Q R : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
  [AddCommGroup R] [Module A R] {f : P →ₗ[A] P} {g : Q →ₗ[A] Q} {h : R →ₗ[A] R}
  (k : BTensor f g →ₗ[A] BTensor f g) (hk : ∀ w, k w = (X : A[X]) • w)
  (k' : BTensor g h →ₗ[A] BTensor g h) (hk' : ∀ w, k' w = (X : A[X]) • w)

/-- **Associativity** of `BTensor`, `A[X]`-linearly. -/
noncomputable def bassoc : BTensor k h ≃ₗ[A[X]] BTensor f k' :=
  (TensorProduct.congr (aevalXmul k hk) (LinearEquiv.refl _ _)) ≪≫ₗ
    TensorProduct.assoc A[X] _ _ _ ≪≫ₗ
    (TensorProduct.congr (LinearEquiv.refl _ _) (aevalXmul k' hk').symm)

lemma bassoc_tm (p : P) (q : Q) (r : R) :
    bassoc k hk k' hk' (tm _ _ (tm _ _ p q) r) = tm _ _ p (tm _ _ q r) := by
  simp only [bassoc, tm, LinearEquiv.trans_apply, TensorProduct.congr_tmul, aevalXmul_of,
    LinearEquiv.refl_apply, TensorProduct.assoc_tmul, aevalXmul_symm]

lemma ext3 {k : BTensor f g →ₗ[A] BTensor f g} {T : Type u} [AddCommGroup T] [Module A T]
    {φ ψ : BTensor k h →ₗ[A] T}
    (H : ∀ p q r, φ (tm _ _ (tm _ _ p q) r) = ψ (tm _ _ (tm _ _ p q) r)) : φ = ψ := by
  refine BTensor.ext fun w r ↦ ?_
  induction w using BTensor.induction_on with
  | h0 => simp
  | htm p q => exact H p q r
  | hadd x y hx hy => rw [tm_add_left, map_add, map_add, hx, hy]

end Assoc

variable (M N) (P : ChartModule A)

/-- **The associativity isomorphism** `(M ⊗ N) ⊗ P → M ⊗ (N ⊗ P)`. -/
noncomputable def assoc : Hom (tensor (tensor M N) P) (tensor M (tensor N P)) where
  f0 := (bassoc (tensor M N).x0 (fun _ ↦ rfl) (tensor N P).x0
    (fun _ ↦ rfl)).toLinearMap.restrictScalars A
  f1 := (bassoc (tensor M N).x1 (fun _ ↦ rfl) (tensor N P).x1
    (fun _ ↦ rfl)).toLinearMap.restrictScalars A
  f01 := (bassoc ((tensor M N).t : (tensor M N).M01 →ₗ[A] (tensor M N).M01) (fun _ ↦ rfl)
    ((tensor N P).t : (tensor N P).M01 →ₗ[A] (tensor N P).M01)
    (fun _ ↦ rfl)).toLinearMap.restrictScalars A
  comm_x0 m := (bassoc _ _ _ _).map_smul X m
  comm_x1 m := (bassoc _ _ _ _).map_smul X m
  comm_t z := (bassoc _ _ _ _).map_smul X z
  comm_r0 m := by
    induction m using BTensor.induction_on with
    | h0 => simp
    | htm w c =>
      induction w using BTensor.induction_on with
      | h0 => simp
      | htm a b =>
        simp [bassoc_tm]
      | hadd x y hx hy => simp only [tm_add_left, map_add, hx, hy]
    | hadd x y hx hy => simp only [map_add, hx, hy]
  comm_r1 m := by
    induction m using BTensor.induction_on with
    | h0 => simp
    | htm w c =>
      induction w using BTensor.induction_on with
      | h0 => simp
      | htm a b =>
        simp [bassoc_tm]
      | hadd x y hx hy => simp only [tm_add_left, map_add, hx, hy]
    | hadd x y hx hy => simp only [map_add, hx, hy]

@[simp] lemma assoc_f0_tm (a : M.M0) (b : N.M0) (c : P.M0) :
    (assoc M N P).f0 (tm _ _ (tm _ _ a b) c) = tm _ _ a (tm _ _ b c) :=
  bassoc_tm _ _ _ _ a b c

@[simp] lemma assoc_f1_tm (a : M.M1) (b : N.M1) (c : P.M1) :
    (assoc M N P).f1 (tm _ _ (tm _ _ a b) c) = tm _ _ a (tm _ _ b c) :=
  bassoc_tm _ _ _ _ a b c

section Braid

variable {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
  (f : P →ₗ[A] P) (g : Q →ₗ[A] Q)

/-- The symmetry `P ⊗ Q → Q ⊗ P`. -/
noncomputable def bbraid : BTensor f g →ₗ[A] BTensor g f :=
  blift (xmul g f) (tmBil g f).flip (fun p q ↦ by simp [xmul_tm']) (fun p q ↦ by simp [xmul_tm])

@[simp] lemma bbraid_tm (p : P) (q : Q) : bbraid f g (tm f g p q) = tm g f q p := by
  simp [bbraid]

end Braid

/-- **The symmetry isomorphism** `M ⊗ N → N ⊗ M`. -/
noncomputable def braid : Hom (tensor M N) (tensor N M) where
  f0 := bbraid M.x0 N.x0
  f1 := bbraid M.x1 N.x1
  f01 := bbraid (M.t : M.M01 →ₗ[A] M.M01) (N.t : N.M01 →ₗ[A] N.M01)
  comm_x0 m := blift_xmul _ _ _ _ m
  comm_x1 m := blift_xmul _ _ _ _ m
  comm_t z := blift_xmul _ _ _ _ z
  comm_r0 m := by
    induction m using BTensor.induction_on with
    | h0 => simp
    | htm a b => simp
    | hadd x y hx hy => simp only [map_add, hx, hy]
  comm_r1 m := by
    induction m using BTensor.induction_on with
    | h0 => simp
    | htm a b => simp
    | hadd x y hx hy => simp only [map_add, hx, hy]

@[simp] lemma braid_f0_tm (a : M.M0) (b : N.M0) :
    (braid M N).f0 (tm _ _ a b) = tm _ _ b a := bbraid_tm _ _ a b

@[simp] lemma braid_f1_tm (a : M.M1) (b : N.M1) :
    (braid M N).f1 (tm _ _ a b) = tm _ _ b a := bbraid_tm _ _ a b

/-! ### Multiplication by a global section -/

variable {M N P}

/-- For `μ : M ⊗ N → P` and a global section `e` of `M`, the morphism `n ↦ μ (e ⊗ n)`. -/
noncomputable def Hom.ofSection (μ : Hom (ChartModule.tensor M N) P) (e : M.H0) : Hom N P where
  f0 := μ.f0 ∘ₗ tmBil M.x0 N.x0 e.1.1
  f1 := μ.f1 ∘ₗ tmBil M.x1 N.x1 e.1.2
  f01 := μ.f01 ∘ₗ tmBil (M.t : M.M01 →ₗ[A] M.M01) (N.t : N.M01 →ₗ[A] N.M01) (M.r0 e.1.1)
  comm_x0 b := by
    change μ.f0 (tm _ _ _ (N.x0 b)) = P.x0 (μ.f0 (tm _ _ _ b))
    rw [← μ.comm_x0, ← xmul_tm']
  comm_x1 b := by
    change μ.f1 (tm _ _ _ (N.x1 b)) = P.x1 (μ.f1 (tm _ _ _ b))
    rw [← μ.comm_x1, ← xmul_tm']
  comm_t z := by
    change μ.f01 (tm _ _ _ (N.t z)) = P.t (μ.f01 (tm _ _ _ z))
    rw [← μ.comm_t]
    exact congrArg μ.f01 (xmul_tm' _ _).symm
  comm_r0 b := by
    change μ.f01 (tm _ _ _ (N.r0 b)) = P.r0 (μ.f0 (tm _ _ _ b))
    rw [← μ.comm_r0, tensor_r0_tm]
  comm_r1 b := by
    change μ.f01 (tm _ _ _ (N.r1 b)) = P.r1 (μ.f1 (tm _ _ _ b))
    rw [← μ.comm_r1, tensor_r1_tm, (TwoCech.mem_H0.1 e.2)]

@[simp] lemma Hom.ofSection_f0 (μ : Hom (ChartModule.tensor M N) P) (e : M.H0) (b : N.M0) :
    (μ.ofSection e).f0 b = μ.f0 (tm _ _ e.1.1 b) := rfl

@[simp] lemma Hom.ofSection_f1 (μ : Hom (ChartModule.tensor M N) P) (e : M.H0) (b : N.M1) :
    (μ.ofSection e).f1 b = μ.f1 (tm _ _ e.1.2 b) := rfl

end ChartModule

end ProjectiveLine
