/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ProjectiveLineEquiv
import FormalSchemes.ChartModuleExistence

/-!
# Grothendieck existence for coherent modules on `ℙ¹_A`

Via the equivalence between quasi-coherent modules on `ℙ¹_A` and chart modules
(`ProjectiveLine.chartEquivalence`), the chart-module results become statements about modules on
`ℙ¹_A`, for `A` Noetherian and `I`-adically complete:

* `ProjectiveLine.hom_bijective_toHomSystem`: for coherent `F`, `G`, morphisms `F → G` are the
  compatible systems of morphisms of the reductions modulo `Iⁿ` (cf. Stacks, Lemma 30.24.1,
  Tag 0883, for `X = ℙ¹_A`);
* `ProjectiveLine.exists_coherent_algebraization`: every adic system of coherent chart modules is
  the system of reductions of a coherent module on `ℙ¹_A` (Stacks, Lemma 30.24.3, Tag 0885, for
  `X = ℙ¹_A`).

Here a quasi-coherent module is *coherent* (`ProjectiveLine.IsCoherent`) if its sections over the
two standard charts `U_k ≅ Spec A[X]` are finite `A[X]`-modules (`X` acting by the chart coordinate,
i.e. through `Γ(ℙ¹_A, U_k) ≃ A[X]`, `ProjectiveLine.chartModule_act0`).
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite AlgebraicGeometry.Scheme.Modules Polynomial

namespace ProjectiveLine

variable {A : Type u} [CommRing A]

/-- A quasi-coherent module on `ℙ¹_A` is *coherent* if its sections over the two standard charts
are finite modules over their coordinate rings `A[X]`. -/
def IsCoherent (F : (scheme A).Modules) [F.IsQuasicoherent] : Prop :=
  Module.Finite A[X] (Module.AEval' (chartModule F).x0) ∧
    Module.Finite A[X] (Module.AEval' (chartModule F).x1)

lemma chartModuleMap_bijective (F G : (scheme A).Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] :
    Function.Bijective (fun φ : F ⟶ G ↦ chartModuleMap φ) := by
  let F' : QCoh A := ⟨F, inferInstance⟩
  let G' : QCoh A := ⟨G, inferInstance⟩
  refine ⟨fun φ ψ h ↦ ?_, fun f ↦ ?_⟩
  · have := (chartFunctor (A := A)).map_injective (X := F') (Y := G')
      (a₁ := ObjectProperty.homMk φ) (a₂ := ObjectProperty.homMk ψ) h
    exact congrArg (fun χ ↦ χ.hom) this
  · obtain ⟨φ, hφ⟩ := (chartFunctor (A := A)).map_surjective (X := F') (Y := G') f
    exact ⟨φ.hom, hφ⟩

variable (I : Ideal A) [IsNoetherianRing A] [IsAdicComplete I A]

/-- **Full faithfulness of completion for coherent modules on `ℙ¹_A`** (cf. Stacks,
Lemma 30.24.1, Tag 0883, for `X = ℙ¹_A`): a morphism of coherent modules is the same as a compatible
system of morphisms of their reductions modulo the powers of `I`. -/
theorem hom_bijective_toHomSystem (F G : (scheme A).Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (hF : IsCoherent F) (hG : IsCoherent G) :
    Function.Bijective (fun φ : F ⟶ G ↦ ChartModule.toHomSystem I (chartModuleMap φ)) := by
  haveI := hF.1
  haveI := hF.2
  haveI := hG.1
  haveI := hG.2
  exact Function.Bijective.comp
    (ChartModule.toHomSystem_bijective I (chartModule F) (chartModule G))
    (chartModuleMap_bijective F G)

namespace ChartModule

variable {I}

omit [IsNoetherianRing A] in
lemma finite_x0_of_hom {N N' : ChartModule A} (f : Hom N N') (hf : Function.Surjective f.f0)
    [Module.Finite A[X] (Module.AEval' N.x0)] : Module.Finite A[X] (Module.AEval' N'.x0) := by
  let q : Module.AEval' N.x0 →ₗ[A[X]] Module.AEval' N'.x0 :=
    LinearMap.ofAEval _ ((Module.AEval'.of N'.x0).toLinearMap ∘ₗ f.f0) fun m ↦ by
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      rw [Module.AEval'.X_smul_of]
      exact congrArg (Module.AEval'.of N'.x0) (f.comm_x0 m)
  refine Module.Finite.of_surjective q fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (Module.AEval'.of N'.x0).surjective y
  obtain ⟨m, rfl⟩ := hf x
  exact ⟨Module.AEval'.of N.x0 m, by simp [q, LinearMap.ofAEval]⟩

omit [IsNoetherianRing A] in
lemma finite_x1_of_hom {N N' : ChartModule A} (f : Hom N N') (hf : Function.Surjective f.f1)
    [Module.Finite A[X] (Module.AEval' N.x1)] : Module.Finite A[X] (Module.AEval' N'.x1) := by
  let q : Module.AEval' N.x1 →ₗ[A[X]] Module.AEval' N'.x1 :=
    LinearMap.ofAEval _ ((Module.AEval'.of N'.x1).toLinearMap ∘ₗ f.f1) fun m ↦ by
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      rw [Module.AEval'.X_smul_of]
      exact congrArg (Module.AEval'.of N'.x1) (f.comm_x1 m)
  refine Module.Finite.of_surjective q fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (Module.AEval'.of N'.x1).surjective y
  obtain ⟨m, rfl⟩ := hf x
  exact ⟨Module.AEval'.of N.x1 m, by simp [q, LinearMap.ofAEval]⟩

end ChartModule

omit [IsNoetherianRing A] in
lemma ker_comp_bijective {P Q R : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q]
    [Module A Q] [AddCommGroup R] [Module A R] (J : Ideal A) (f : Q →ₗ[A] R) (g : P →ₗ[A] Q)
    (hg : Function.Bijective g) (hk : LinearMap.ker f = J • ⊤) :
    LinearMap.ker (f ∘ₗ g) = J • ⊤ := by
  rw [LinearMap.ker_comp, hk]
  refine le_antisymm (fun x hx ↦ ?_) (Submodule.smul_le.2 fun r hr m _ ↦ ?_)
  · have : g x ∈ Submodule.map g (J • ⊤) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hg.2]
      exact hx
    obtain ⟨y, hy, hxy⟩ := this
    rwa [← hg.1 hxy]
  · change g (r • m) ∈ J • (⊤ : Submodule A Q)
    rw [_root_.map_smul]
    exact Submodule.smul_mem_smul hr (Submodule.mem_top (R := A) (x := g m))

/-- **Grothendieck existence for coherent modules on `ℙ¹_A`** (Stacks, Lemma 30.24.3, Tag 0885,
for `X = ℙ¹_A`): every adic system of coherent chart modules is the system of reductions of a
coherent module on `ℙ¹_A`. -/
theorem exists_coherent_algebraization (S : AdicChartSystem I) :
    ∃ (F : (scheme A).Modules) (_ : F.IsQuasicoherent) (_ : IsCoherent F)
      (α : ∀ n, ChartModule.Hom (chartModule F) (S.M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α n).f1 = I ^ n • ⊤) ∧
      ∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m := by
  obtain ⟨N, _, _, α, hα, hc⟩ := S.exists_algebraization
  let e := ChartModule.Hom.invOfBijective N.toGlue N.toGlue_bijective0 N.toGlue_bijective1
    N.toGlue_bijective01
  have he0 : Function.Bijective e.f0 :=
    (LinearEquiv.ofBijective _ N.toGlue_bijective0).symm.bijective
  have he1 : Function.Bijective e.f1 :=
    (LinearEquiv.ofBijective _ N.toGlue_bijective1).symm.bijective
  refine ⟨N.glue, N.isQuasicoherent_glue,
    ⟨ChartModule.finite_x0_of_hom N.toGlue N.toGlue_bijective0.2,
      ChartModule.finite_x1_of_hom N.toGlue N.toGlue_bijective1.2⟩,
    fun n ↦ (α n).comp e, fun n ↦ ⟨(hα n).1.comp he0.2, (hα n).2.1.comp he1.2,
      ker_comp_bijective _ _ _ he0 (hα n).2.2.1, ker_comp_bijective _ _ _ he1 (hα n).2.2.2⟩,
    fun m n h ↦ ?_⟩
  rw [← ChartModule.Hom.comp_assoc, hc m n h]

end ProjectiveLine
