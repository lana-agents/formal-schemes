/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleFormalH0

/-!
# Morphisms of chart modules: composition, maps out of `𝒪(-d)^ι`, and descent

* `ChartModule.Hom.comp`, `ChartModule.Hom.ext'`: composition and extensionality; a morphism is
  determined by its components on the two charts (`ChartModule.Hom.ext_of_f0_f1`).
* `ChartModule.homFreeEquiv`: morphisms `𝒪(-d)^ι → P` are families of sections of `P(d)`.
* `ChartModule.Hom.descend`: a morphism out of `G` vanishing on the kernel of a chart-surjective
  `π : G → N` factors through `N`.
-/

universe u

open Polynomial LaurentPolynomial

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A] {G M N P : ChartModule A}

/-- Composition of morphisms of chart modules. -/
def Hom.comp (ψ : Hom N P) (φ : Hom M N) : Hom M P where
  f0 := ψ.f0 ∘ₗ φ.f0
  f1 := ψ.f1 ∘ₗ φ.f1
  f01 := ψ.f01 ∘ₗ φ.f01
  comm_x0 m := by simp [φ.comm_x0, ψ.comm_x0]
  comm_x1 m := by simp [φ.comm_x1, ψ.comm_x1]
  comm_t z := by simp [φ.comm_t, ψ.comm_t]
  comm_r0 m := by simp [φ.comm_r0, ψ.comm_r0]
  comm_r1 m := by simp [φ.comm_r1, ψ.comm_r1]

@[simp] lemma Hom.comp_f0 (ψ : Hom N P) (φ : Hom M N) : (ψ.comp φ).f0 = ψ.f0 ∘ₗ φ.f0 := rfl
@[simp] lemma Hom.comp_f1 (ψ : Hom N P) (φ : Hom M N) : (ψ.comp φ).f1 = ψ.f1 ∘ₗ φ.f1 := rfl
@[simp] lemma Hom.comp_f01 (ψ : Hom N P) (φ : Hom M N) : (ψ.comp φ).f01 = ψ.f01 ∘ₗ φ.f01 := rfl

lemma Hom.ext' {φ ψ : Hom M N} (h0 : φ.f0 = ψ.f0) (h1 : φ.f1 = ψ.f1) (h01 : φ.f01 = ψ.f01) :
    φ = ψ := by
  cases φ; cases ψ; cases h0; cases h1; cases h01; rfl

/-- The component on the overlap is determined by the component on `Spec A[X]`. -/
lemma Hom.f01_eq_of_f0_eq {φ ψ : Hom M N} (h0 : φ.f0 = ψ.f0) : φ.f01 = ψ.f01 := by
  ext z
  obtain ⟨m, k, hk⟩ := M.exists_r0 z
  apply (N.t ^ k).injective
  rw [← zpow_natCast, ← φ.comm_t_zpow, ← ψ.comm_t_zpow, zpow_natCast, hk, φ.comm_r0,
    ψ.comm_r0, h0]

lemma Hom.ext_of_f0_f1 {φ ψ : Hom M N} (h0 : φ.f0 = ψ.f0) (h1 : φ.f1 = ψ.f1) : φ = ψ :=
  Hom.ext' h0 h1 (Hom.f01_eq_of_f0_eq h0)

lemma Hom.aeval_f0 (φ : Hom M N) (q : A[X]) (m : M.M0) :
    φ.f0 (Polynomial.aeval M.x0 q m) = Polynomial.aeval N.x0 q (φ.f0 m) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul]
    rw [φ.comm_x0_pow]

lemma Hom.aeval_f1 (φ : Hom M N) (q : A[X]) (m : M.M1) :
    φ.f1 (Polynomial.aeval M.x1 q m) = Polynomial.aeval N.x1 q (φ.f1 m) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul]
    rw [φ.comm_x1_pow]

/-! ### Morphisms out of `𝒪(-d)^ι` -/

section Free

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {d : ℕ}

lemma aeval_free_x0_single (q : A[X]) (i : ι) :
    Polynomial.aeval (free (A := A) ι d).x0 q (Pi.single i 1) = Pi.single i q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, Pi.single_add]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    funext j
    rw [Pi.smul_apply, pi_pow_apply, Pi.single_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      change a • (LinearMap.mulLeft A X ^ n) 1 = monomial n a
      rw [LinearMap.pow_mulLeft, LinearMap.mulLeft_apply, mul_one, ← C_mul_X_pow_eq_monomial,
        Polynomial.smul_eq_C_mul]
    · simp

lemma aeval_free_x1_single (q : A[X]) (i : ι) :
    Polynomial.aeval (free (A := A) ι d).x1 q (Pi.single i 1) = Pi.single i q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, Pi.single_add]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    funext j
    rw [Pi.smul_apply, pi_pow_apply, Pi.single_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      change a • (LinearMap.mulLeft A X ^ n) 1 = monomial n a
      rw [LinearMap.pow_mulLeft, LinearMap.mulLeft_apply, mul_one, ← C_mul_X_pow_eq_monomial,
        Polynomial.smul_eq_C_mul]
    · simp

lemma free_r0_single_eq (i : ι) :
    (free (A := A) ι d).r0 (Pi.single i 1) =
      ((free (A := A) ι d).t ^ d) ((free (A := A) ι d).r1 (Pi.single i 1)) := by
  funext j
  rw [piCongrRight_pow_apply]
  change toLaurent ((Pi.single i (1 : A[X]) : ι → A[X]) j) =
    (mulT A ^ d) (T (-(d : ℤ)) * invert (toLaurent ((Pi.single i (1 : A[X]) : ι → A[X]) j)))
  rw [mulT_pow_apply, Pi.single_apply]
  split_ifs
  · rw [map_one, map_one, mul_one, ← T_add, add_neg_cancel, T_zero]
  · simp

variable (P) in
/-- The sections of `P(d)` given by a morphism `𝒪(-d)^ι → P`. -/
noncomputable def homFreeSections (φ : Hom (free (A := A) ι d) P) (i : ι) : (P.twist d).H0 :=
  ⟨(φ.f0 (Pi.single i 1), φ.f1 (Pi.single i 1)), by
    rw [TwoCech.mem_H0]
    change P.r0 (φ.f0 _) = (P.t ^ (d : ℤ)) (P.r1 (φ.f1 _))
    rw [← φ.comm_r0, ← φ.comm_r1, free_r0_single_eq, ← zpow_natCast, φ.comm_t_zpow]⟩

omit [Fintype ι] [DecidableEq ι] in
lemma homFreeSections_mem (s : ι → (P.twist d).H0) (i : ι) :
    P.r0 (s i).1.1 = (P.t ^ (d : ℤ)) (P.r1 (s i).1.2) :=
  TwoCech.mem_H0.1 (s i).2

variable (P) in
/-- **Morphisms `𝒪(-d)^ι → P` are families of sections of `P(d)`.** -/
noncomputable def homFreeEquiv : Hom (free (A := A) ι d) P ≃ (ι → (P.twist d).H0) where
  toFun φ := homFreeSections P φ
  invFun s := sectionsHom P (fun i ↦ (s i).1) (homFreeSections_mem s)
  left_inv φ := by
    apply Hom.ext_of_f0_f1
    · refine LinearMap.ext fun p ↦ ?_
      change ∑ i, Polynomial.aeval P.x0 (p i) (φ.f0 (Pi.single i 1)) = φ.f0 p
      rw [show ∑ i, Polynomial.aeval P.x0 (p i) (φ.f0 (Pi.single i 1)) =
          ∑ i, φ.f0 (Pi.single i (p i)) from Finset.sum_congr rfl fun i _ ↦ by
            rw [← Hom.aeval_f0, aeval_free_x0_single], ← map_sum]
      congr 1
      exact Finset.univ_sum_single p
    · refine LinearMap.ext fun p ↦ ?_
      change ∑ i, Polynomial.aeval P.x1 (p i) (φ.f1 (Pi.single i 1)) = φ.f1 p
      rw [show ∑ i, Polynomial.aeval P.x1 (p i) (φ.f1 (Pi.single i 1)) =
          ∑ i, φ.f1 (Pi.single i (p i)) from Finset.sum_congr rfl fun i _ ↦ by
            rw [← Hom.aeval_f1, aeval_free_x1_single], ← map_sum]
      congr 1
      exact Finset.univ_sum_single p
  right_inv s := by
    funext i
    apply Subtype.ext
    apply Prod.ext
    · change ∑ j, Polynomial.aeval P.x0 ((Pi.single i (1 : A[X]) : ι → A[X]) j) (s j).1.1 =
        (s i).1.1
      rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj])
        (by simp)]
      simp
    · change ∑ j, Polynomial.aeval P.x1 ((Pi.single i (1 : A[X]) : ι → A[X]) j) (s j).1.2 =
        (s i).1.2
      rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj])
        (by simp)]
      simp

end Free

/-! ### Descent along a chart-surjective morphism -/

section Descend

/-- Factor `g` through a surjection `f` whose kernel `g` kills. -/
noncomputable def descendLin {P₁ Q₁ R₁ : Type u} [AddCommGroup P₁] [Module A P₁]
    [AddCommGroup Q₁] [Module A Q₁] [AddCommGroup R₁] [Module A R₁] (f : P₁ →ₗ[A] Q₁)
    (hf : Function.Surjective f) (g : P₁ →ₗ[A] R₁) (hg : LinearMap.ker f ≤ LinearMap.ker g) :
    Q₁ →ₗ[A] R₁ :=
  (LinearMap.ker f).liftQ g hg ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap

lemma descendLin_apply {P₁ Q₁ R₁ : Type u} [AddCommGroup P₁] [Module A P₁]
    [AddCommGroup Q₁] [Module A Q₁] [AddCommGroup R₁] [Module A R₁] (f : P₁ →ₗ[A] Q₁)
    (hf : Function.Surjective f) (g : P₁ →ₗ[A] R₁) (hg : LinearMap.ker f ≤ LinearMap.ker g)
    (x : P₁) : descendLin f hf g hg (f x) = g x := by
  have : (f.quotKerEquivOfSurjective hf).symm (f x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [descendLin, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
    Submodule.liftQ_apply]

variable (π : Hom G N) (h0 : Function.Surjective π.f0) (h1 : Function.Surjective π.f1)
  (φ : Hom G P) (hφ0 : LinearMap.ker π.f0 ≤ LinearMap.ker φ.f0)
  (hφ1 : LinearMap.ker π.f1 ≤ LinearMap.ker φ.f1)

include hφ0 in
lemma ker_f01_le_of_ker_f0_le : LinearMap.ker π.f01 ≤ LinearMap.ker φ.f01 := by
  intro z (hz : π.f01 z = 0)
  obtain ⟨m, k, hk⟩ := G.exists_r0 z
  have h1' : N.r0 (π.f0 m) = 0 := by
    rw [← π.comm_r0, ← hk, ← zpow_natCast, π.comm_t_zpow, hz, map_zero]
  obtain ⟨j, hj⟩ := N.ker_r0 _ h1'
  have hm : φ.f0 ((G.x0 ^ j) m) = 0 := hφ0 (show π.f0 _ = 0 by rw [π.comm_x0_pow, hj])
  change φ.f01 z = 0
  apply (P.t ^ (j + k)).injective
  rw [map_zero, ← zpow_natCast, ← φ.comm_t_zpow, zpow_natCast, pow_add_apply, hk, t_pow_r0,
    φ.comm_r0, hm, map_zero]

/-- **Descent**: a morphism out of `G` killing the kernel of a chart-surjective `π : G → N`
factors through `N`. -/
noncomputable def Hom.descend : Hom N P where
  f0 := descendLin π.f0 h0 φ.f0 hφ0
  f1 := descendLin π.f1 h1 φ.f1 hφ1
  f01 := descendLin π.f01 (π.surjective_f01 h0) φ.f01 (ker_f01_le_of_ker_f0_le π φ hφ0)
  comm_x0 n := by
    obtain ⟨g, rfl⟩ := h0 n
    rw [← π.comm_x0, descendLin_apply, descendLin_apply, φ.comm_x0]
  comm_x1 n := by
    obtain ⟨g, rfl⟩ := h1 n
    rw [← π.comm_x1, descendLin_apply, descendLin_apply, φ.comm_x1]
  comm_t z := by
    obtain ⟨g, rfl⟩ := π.surjective_f01 h0 z
    rw [← π.comm_t, descendLin_apply, descendLin_apply, φ.comm_t]
  comm_r0 n := by
    obtain ⟨g, rfl⟩ := h0 n
    rw [← π.comm_r0, descendLin_apply, descendLin_apply, φ.comm_r0]
  comm_r1 n := by
    obtain ⟨g, rfl⟩ := h1 n
    rw [← π.comm_r1, descendLin_apply, descendLin_apply, φ.comm_r1]

lemma Hom.descend_comp : (π.descend h0 h1 φ hφ0 hφ1).comp π = φ := by
  apply Hom.ext_of_f0_f1
  · refine LinearMap.ext fun g ↦ ?_
    change descendLin π.f0 h0 φ.f0 hφ0 (π.f0 g) = φ.f0 g
    exact descendLin_apply π.f0 h0 φ.f0 hφ0 g
  · refine LinearMap.ext fun g ↦ ?_
    change descendLin π.f1 h1 φ.f1 hφ1 (π.f1 g) = φ.f1 g
    exact descendLin_apply π.f1 h1 φ.f1 hφ1 g

end Descend

/-- A chart-surjective morphism is an epimorphism. -/
lemma Hom.comp_cancel (π : Hom G N) (h0 : Function.Surjective π.f0)
    (h1 : Function.Surjective π.f1) {ψ ψ' : Hom N P} (h : ψ.comp π = ψ'.comp π) : ψ = ψ' := by
  apply Hom.ext_of_f0_f1
  · refine LinearMap.ext fun n ↦ ?_
    obtain ⟨g, rfl⟩ := h0 n
    exact congrArg (fun χ : Hom G P ↦ χ.f0 g) h
  · refine LinearMap.ext fun n ↦ ?_
    obtain ⟨g, rfl⟩ := h1 n
    exact congrArg (fun χ : Hom G P ↦ χ.f1 g) h

end ChartModule

end ProjectiveLine
