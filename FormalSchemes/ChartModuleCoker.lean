/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleKernelSystem

/-!
# Cokernels of morphisms of chart modules

`ChartModule.Hom.coker u` is the chart module `Q / u(P)` of a morphism `u : P → Q` (the cokernel
of quasi-coherent modules on `ℙ¹_A`), with the projection `ChartModule.Hom.cokerπ u`, which is
surjective on the charts with kernel the image of `u`.
-/

universe u

open Polynomial LaurentPolynomial

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A] {P Q : ChartModule A} (u : Hom P Q)

lemma Hom.comm_t_symm (z : P.M01) : u.f01 (P.t.symm z) = Q.t.symm (u.f01 z) := by
  apply Q.t.injective
  rw [← u.comm_t]
  simp

lemma Hom.range_x0_le : LinearMap.range u.f0 ≤ (LinearMap.range u.f0).comap Q.x0 := by
  rintro _ ⟨p, rfl⟩
  exact ⟨P.x0 p, u.comm_x0 p⟩

lemma Hom.range_x1_le : LinearMap.range u.f1 ≤ (LinearMap.range u.f1).comap Q.x1 := by
  rintro _ ⟨p, rfl⟩
  exact ⟨P.x1 p, u.comm_x1 p⟩

lemma Hom.range_r0_le : LinearMap.range u.f0 ≤ (LinearMap.range u.f01).comap Q.r0 := by
  rintro _ ⟨p, rfl⟩
  exact ⟨P.r0 p, u.comm_r0 p⟩

lemma Hom.range_r1_le : LinearMap.range u.f1 ≤ (LinearMap.range u.f01).comap Q.r1 := by
  rintro _ ⟨p, rfl⟩
  exact ⟨P.r1 p, u.comm_r1 p⟩

lemma Hom.map_t_range :
    (LinearMap.range u.f01).map (Q.t : Q.M01 →ₗ[A] Q.M01) = LinearMap.range u.f01 := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨P.t z, u.comm_t z⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨u.f01 (P.t.symm z), ⟨P.t.symm z, rfl⟩, by
      change Q.t (u.f01 (P.t.symm z)) = u.f01 z
      rw [u.comm_t_symm, LinearEquiv.apply_symm_apply]⟩

lemma Hom.range_pow_t (k : ℕ) (z : P.M01) : (Q.t ^ k) (u.f01 z) = u.f01 ((P.t ^ k) z) := by
  rw [← zpow_natCast, ← zpow_natCast, u.comm_t_zpow]

lemma Hom.range_pow_t_symm (k : ℕ) (z : P.M01) :
    (Q.t.symm ^ k) (u.f01 z) = u.f01 ((P.t.symm ^ k) z) :=
  (u.comm_t_symm_pow k z).symm

/-- **The cokernel** `Q / u(P)`. -/
noncomputable def Hom.coker : ChartModule A where
  M0 := ModuleCat.of A (Q.M0 ⧸ LinearMap.range u.f0)
  M1 := ModuleCat.of A (Q.M1 ⧸ LinearMap.range u.f1)
  M01 := ModuleCat.of A (Q.M01 ⧸ LinearMap.range u.f01)
  x0 := Submodule.mapQ _ _ Q.x0 u.range_x0_le
  x1 := Submodule.mapQ _ _ Q.x1 u.range_x1_le
  t := Submodule.Quotient.equiv _ _ Q.t u.map_t_range
  r0 := Submodule.mapQ _ _ Q.r0 u.range_r0_le
  r1 := Submodule.mapQ _ _ Q.r1 u.range_r1_le
  r0_x0 m := by
    induction m using Submodule.Quotient.induction_on with
    | H m => exact congrArg Submodule.Quotient.mk (Q.r0_x0 m)
  r1_x1 m := by
    induction m using Submodule.Quotient.induction_on with
    | H m =>
      change Submodule.Quotient.mk (Q.r1 (Q.x1 m)) = Submodule.Quotient.mk (Q.t.symm (Q.r1 m))
      rw [Q.r1_x1]
  exists_r0 z := by
    induction z using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨m, k, hk⟩ := Q.exists_r0 z
      exact ⟨Submodule.Quotient.mk m, k, by rw [quotEquiv_pow_mk, hk]; rfl⟩
  ker_r0 m hm := by
    induction m using Submodule.Quotient.induction_on with
    | H q =>
      have hq : Q.r0 q ∈ LinearMap.range u.f01 := (Submodule.Quotient.mk_eq_zero _).1 hm
      obtain ⟨z', hz'⟩ := hq
      obtain ⟨p', j, hj⟩ := P.exists_r0 z'
      have h1 : Q.r0 ((Q.x0 ^ j) q - u.f0 p') = 0 := by
        rw [map_sub, ← t_pow_r0, ← hz', u.range_pow_t, hj, u.comm_r0, sub_self]
      obtain ⟨i, hi⟩ := Q.ker_r0 _ h1
      refine ⟨i + j, ?_⟩
      rw [mapQ_pow_mk, Submodule.Quotient.mk_eq_zero, end_pow_add_apply]
      rw [map_sub, sub_eq_zero] at hi
      rw [hi, ← u.comm_x0_pow]
      exact LinearMap.mem_range_self _ _
  exists_r1 z := by
    induction z using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨m, k, hk⟩ := Q.exists_r1 z
      exact ⟨Submodule.Quotient.mk m, k, by rw [quotEquiv_symm_pow_mk, hk]; rfl⟩
  ker_r1 m hm := by
    induction m using Submodule.Quotient.induction_on with
    | H q =>
      have hq : Q.r1 q ∈ LinearMap.range u.f01 := (Submodule.Quotient.mk_eq_zero _).1 hm
      obtain ⟨z', hz'⟩ := hq
      obtain ⟨p', j, hj⟩ := P.exists_r1 z'
      have h1 : Q.r1 ((Q.x1 ^ j) q - u.f1 p') = 0 := by
        rw [map_sub, ← t_symm_pow_r1, ← hz', u.range_pow_t_symm, hj, u.comm_r1, sub_self]
      obtain ⟨i, hi⟩ := Q.ker_r1 _ h1
      refine ⟨i + j, ?_⟩
      rw [mapQ_pow_mk, Submodule.Quotient.mk_eq_zero, end_pow_add_apply]
      rw [map_sub, sub_eq_zero] at hi
      rw [hi, ← u.comm_x1_pow]
      exact LinearMap.mem_range_self _ _

/-- The projection onto the cokernel. -/
noncomputable def Hom.cokerπ : Hom Q u.coker where
  f0 := (LinearMap.range u.f0).mkQ
  f1 := (LinearMap.range u.f1).mkQ
  f01 := (LinearMap.range u.f01).mkQ
  comm_x0 _ := rfl
  comm_x1 _ := rfl
  comm_t _ := rfl
  comm_r0 _ := rfl
  comm_r1 _ := rfl

lemma Hom.cokerπ_surjective0 : Function.Surjective u.cokerπ.f0 := Submodule.mkQ_surjective _
lemma Hom.cokerπ_surjective1 : Function.Surjective u.cokerπ.f1 := Submodule.mkQ_surjective _

lemma Hom.ker_cokerπ0 : LinearMap.ker u.cokerπ.f0 = LinearMap.range u.f0 := Submodule.ker_mkQ _
lemma Hom.ker_cokerπ1 : LinearMap.ker u.cokerπ.f1 = LinearMap.range u.f1 := Submodule.ker_mkQ _

lemma finite_coker_x0 [Module.Finite A[X] (Module.AEval' Q.x0)] :
    Module.Finite A[X] (Module.AEval' u.coker.x0) := by
  let q : Module.AEval' Q.x0 →ₗ[A[X]] Module.AEval' u.coker.x0 :=
    LinearMap.ofAEval _ ((Module.AEval'.of u.coker.x0).toLinearMap ∘ₗ
      (LinearMap.range u.f0).mkQ) fun m ↦ by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        rw [Module.AEval'.X_smul_of]
        rfl
  refine Module.Finite.of_surjective q fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (Module.AEval'.of u.coker.x0).surjective y
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Module.AEval'.of Q.x0 m, by simp [q, LinearMap.ofAEval]; rfl⟩

lemma finite_coker_x1 [Module.Finite A[X] (Module.AEval' Q.x1)] :
    Module.Finite A[X] (Module.AEval' u.coker.x1) := by
  let q : Module.AEval' Q.x1 →ₗ[A[X]] Module.AEval' u.coker.x1 :=
    LinearMap.ofAEval _ ((Module.AEval'.of u.coker.x1).toLinearMap ∘ₗ
      (LinearMap.range u.f1).mkQ) fun m ↦ by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        rw [Module.AEval'.X_smul_of]
        rfl
  refine Module.Finite.of_surjective q fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (Module.AEval'.of u.coker.x1).surjective y
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Module.AEval'.of Q.x1 m, by simp [q, LinearMap.ofAEval]; rfl⟩

end ChartModule

end ProjectiveLine
