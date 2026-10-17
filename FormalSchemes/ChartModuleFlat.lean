/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleAlgebra
import FormalSchemes.LocalFlatness

/-!
# Flatness of algebraizations on `ℙ¹_A` along the special fibre

Let `N` be a coherent chart module on `ℙ¹_A` (`A` Noetherian) with morphisms `α n : N → Mₙ`
inducing `N / Iⁿ N ≅ Mₙ` on both charts (as produced by
`ProjectiveLine.AdicChartSystem.exists_algebraization`). If every `Mₙ` is flat over
`ℙ¹_{A/Iⁿ}` on the charts (`(A[X] / Iⁿ) ⊗ Mₙ` flat over `A[X] / Iⁿ`), then `N` is flat over
`ℙ¹_A` at every point of the special fibre `V(I)`: `ProjectiveLine.ChartModule.flat_x0_of_system`,
`ProjectiveLine.ChartModule.flat_x1_of_system`. This is the local criterion of flatness
(`LocalFlatness.flat_localizedModule`, an adic form of Stacks, Tag 00MK) applied to the
chart modules, after identifying `(A[X] / Iⁿ) ⊗ N₀` with `(A[X] / Iⁿ) ⊗ Mₙ,₀`
(`LocalFlatness.flat_baseChange_of_surjective`).
-/

universe u

open Polynomial TensorProduct

namespace LocalFlatness

variable {R : Type u} [CommRing R] (J : Ideal R) {M M' : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']

/-- If `f : M → M'` is surjective with kernel `J M` and `J M' = 0`, then `(R / J) ⊗ M` and
`(R / J) ⊗ M'` are isomorphic, so flatness over `R / J` transfers. -/
theorem flat_baseChange_of_surjective (f : M →ₗ[R] M') (hf : Function.Surjective f)
    (hker : LinearMap.ker f = J • ⊤) (hM' : J • (⊤ : Submodule R M') = ⊥)
    (h : Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] M')) : Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] M) := by
  let g : (R ⧸ J) ⊗[R] M →ₗ[R ⧸ J] (R ⧸ J) ⊗[R] M' := AlgebraTensorModule.lTensor _ _ f
  let e := TensorProduct.quotTensorEquivQuotSMul M J
  let e' := TensorProduct.quotTensorEquivQuotSMul M' J
  let q : M ⧸ (J • ⊤ : Submodule R M) →ₗ[R] M' ⧸ (J • ⊤ : Submodule R M') :=
    Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top J f)
  have hq : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, hM',
        Submodule.mem_bot] at hy
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, ← hker]
      exact hy
  have hsq : ∀ w, e' (g w) = q (e w) := fun w ↦ by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      induction r using Submodule.Quotient.induction_on with
      | H r =>
        change e' (Ideal.Quotient.mk J r ⊗ₜ[R] f x) = q (e (Ideal.Quotient.mk J r ⊗ₜ[R] x))
        simp [e, e', q]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hg : Function.Bijective g := by
    refine ⟨fun a b hab ↦ ?_, LinearMap.lTensor_surjective _ hf⟩
    apply e.injective
    apply hq
    rw [← hsq, ← hsq, hab]
  haveI := h
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective g hg)

end LocalFlatness

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A]

lemma mem_mapC_smul_top_iff (J : Ideal A) {P : Type u} [AddCommGroup P] [Module A P]
    (f : P →ₗ[A] P) (x : P) :
    Module.AEval'.of f x ∈ ((J.map C) • ⊤ : Submodule A[X] (Module.AEval' f)) ↔
      x ∈ (J • ⊤ : Submodule A P) := by
  constructor
  · intro hx
    suffices ∀ y : Module.AEval' f, y ∈ ((J.map C) • ⊤ : Submodule A[X] (Module.AEval' f)) →
        (Module.AEval'.of f).symm y ∈ (J • ⊤ : Submodule A P) by
      simpa using this _ hx
    intro y hy
    refine Submodule.smul_induction_on (p := fun y ↦ (Module.AEval'.of f).symm y ∈
      (J • ⊤ : Submodule A P)) hy (fun q hq n _ ↦ ?_) (fun a b ha hb ↦ ?_)
    · obtain ⟨m, rfl⟩ := (Module.AEval'.of f).surjective n
      rw [← Module.AEval.of_aeval_smul, LinearEquiv.symm_apply_apply, aeval_eq_sum_range,
        Module.End.smul_def, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      rw [LinearMap.smul_apply]
      exact Submodule.smul_mem_smul (Ideal.mem_map_C_iff.1 hq i) trivial
    · rw [map_add]; exact add_mem ha hb
  · intro hx
    refine Submodule.smul_induction_on (p := fun x ↦ Module.AEval'.of f x ∈
      ((J.map C) • ⊤ : Submodule A[X] (Module.AEval' f))) hx (fun a ha m _ ↦ ?_)
      (fun a b ha hb ↦ ?_)
    · rw [map_smul, ← algebraMap_smul A[X] a]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem C ha) trivial
    · rw [map_add]; exact add_mem ha hb

variable [IsNoetherianRing A] (I : Ideal A)

/-- The local criterion for one chart. -/
theorem flat_of_system_aux {P : Type u} [AddCommGroup P] [Module A P] {f : P →ₗ[A] P}
    [Module.Finite A[X] (Module.AEval' f)] (Pn : ℕ → Type u) [∀ n, AddCommGroup (Pn n)]
    [∀ n, Module A (Pn n)] (fn : ∀ n, Pn n →ₗ[A] Pn n) (u : ∀ n, P →ₗ[A] Pn n)
    (hu : ∀ n p, u n (f p) = fn n (u n p)) (hs : ∀ n, Function.Surjective (u n))
    (hk : ∀ n, LinearMap.ker (u n) = I ^ n • ⊤) (hkill : ∀ n, I ^ n • (⊤ : Submodule A (Pn n)) = ⊥)
    (hflat : ∀ n, Module.Flat (A[X] ⧸ I.map C ^ n)
      ((A[X] ⧸ I.map C ^ n) ⊗[A[X]] Module.AEval' (fn n)))
    (p : Ideal A[X]) [p.IsPrime] (hp : I.map C ≤ p) :
    Module.Flat A[X] (LocalizedModule p.primeCompl (Module.AEval' f)) := by
  refine LocalFlatness.flat_localizedModule (I.map C) (fun n ↦ ?_) p hp
  refine LocalFlatness.flat_baseChange_of_surjective _ (BTensor.aevalMap (u n) (hu n))
    (fun y ↦ ?_) ?_ ?_ (hflat n)
  · obtain ⟨x, rfl⟩ := (Module.AEval'.of (fn n)).surjective y
    obtain ⟨p, rfl⟩ := hs n x
    exact ⟨Module.AEval'.of f p, BTensor.aevalMap_of _ _ _⟩
  · ext y
    obtain ⟨x, rfl⟩ := (Module.AEval'.of f).surjective y
    rw [LinearMap.mem_ker, BTensor.aevalMap_of, LinearEquiv.map_eq_zero_iff, ← Ideal.map_pow,
      mem_mapC_smul_top_iff, ← hk n, LinearMap.mem_ker]
  · rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := (Module.AEval'.of (fn n)).surjective y
    rw [← Ideal.map_pow, mem_mapC_smul_top_iff, hkill n, Submodule.mem_bot] at hy
    rw [hy, map_zero]
    exact Submodule.zero_mem _

/-- **Flatness of an algebraization along the special fibre**, chart `Spec A[X]`: if
`α n : N → Mₙ` induces `N₀ / Iⁿ N₀ ≅ Mₙ,₀` and every `Mₙ,₀` is flat over `A[X] / Iⁿ`, then `N₀`
is flat over `A[X]` at every prime containing `I`. -/
theorem flat_x0_of_system (N : ChartModule A) [Module.Finite A[X] (Module.AEval' N.x0)]
    (M : ℕ → ChartModule A) (α : ∀ n, Hom N (M n)) (hs : ∀ n, Function.Surjective (α n).f0)
    (hk : ∀ n, LinearMap.ker (α n).f0 = I ^ n • ⊤)
    (hkill : ∀ n, I ^ n • (⊤ : Submodule A (M n).M0) = ⊥)
    (hflat : ∀ n, Module.Flat (A[X] ⧸ I.map C ^ n)
      ((A[X] ⧸ I.map C ^ n) ⊗[A[X]] Module.AEval' (M n).x0))
    (p : Ideal A[X]) [p.IsPrime] (hp : I.map C ≤ p) :
    Module.Flat A[X] (LocalizedModule p.primeCompl (Module.AEval' N.x0)) :=
  flat_of_system_aux I (fun n ↦ (M n).M0) (fun n ↦ (M n).x0) (fun n ↦ (α n).f0)
    (fun n ↦ (α n).comm_x0) hs hk hkill hflat p hp

/-- **Flatness of an algebraization along the special fibre**, chart `Spec A[Y]`. -/
theorem flat_x1_of_system (N : ChartModule A) [Module.Finite A[X] (Module.AEval' N.x1)]
    (M : ℕ → ChartModule A) (α : ∀ n, Hom N (M n)) (hs : ∀ n, Function.Surjective (α n).f1)
    (hk : ∀ n, LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hkill : ∀ n, I ^ n • (⊤ : Submodule A (M n).M1) = ⊥)
    (hflat : ∀ n, Module.Flat (A[X] ⧸ I.map C ^ n)
      ((A[X] ⧸ I.map C ^ n) ⊗[A[X]] Module.AEval' (M n).x1))
    (p : Ideal A[X]) [p.IsPrime] (hp : I.map C ≤ p) :
    Module.Flat A[X] (LocalizedModule p.primeCompl (Module.AEval' N.x1)) :=
  flat_of_system_aux I (fun n ↦ (M n).M1) (fun n ↦ (M n).x1) (fun n ↦ (α n).f1)
    (fun n ↦ (α n).comm_x1) hs hk hkill hflat p hp

end ChartModule

end ProjectiveLine
