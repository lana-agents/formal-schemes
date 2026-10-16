/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleQuot
import Mathlib.RingTheory.Filtration

/-!
# The theorem on formal functions for `H⁰` on `ℙ¹_A`

For a chart module `M` of finite type over a Noetherian ring `A` and an ideal `I`, the comparison
of `H⁰(M / Iⁿ M)` with `H⁰(M) / Iⁿ H⁰(M)` goes through a presentation `0 → K → 𝒪(-d)^ι → M → 0`
with `d ≥ 1` (`FormalSchemes.ChartModule`), using that `H⁰(M) ↪ H¹(K)` and its reductions. This
file provides the two inputs beyond `FormalSchemes.ChartModuleQuot`:

* `ChartModule.H0_quot_free_eq_bot`: `H⁰(𝒪(-d)^ι / J) = 0` for every ideal `J` and `d ≥ 1`;
* `ChartModule.Hom.exists_artinRees`: the Artin–Rees lemma for the kernel of a morphism of chart
  modules, on all three charts (Stacks, Lemma 10.51.2, Tag 00IN, over `A[X]` and then on the
  overlap by clearing denominators).
-/

universe u

open Polynomial LaurentPolynomial

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A] (J : Ideal A)

lemma mem_smul_top_pi_poly {ι : Type u} [Finite ι] {f : ι → A[X]}
    (h : ∀ i n, (f i).coeff n ∈ J) : f ∈ (J • ⊤ : Submodule A (ι → A[X])) := by
  classical
  have := Fintype.ofFinite ι
  have hf : f = ∑ i, ∑ n ∈ (f i).support, (f i).coeff n • Pi.single i (monomial n (1 : A)) := by
    ext i : 1
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [Ne.symm hj]) (by simp)]
    simp only [if_true]
    conv_lhs => rw [(f i).as_sum_support]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hf]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun n _ ↦
    Submodule.smul_mem_smul (h i n) Submodule.mem_top

lemma coeff_mem_of_mem_smul_top_pi_laurent {ι : Type u} {f : ι → A[T;T⁻¹]}
    (hf : f ∈ (J • ⊤ : Submodule A (ι → A[T;T⁻¹]))) (i : ι) (n : ℤ) : (f i).coeff n ∈ J := by
  refine Submodule.smul_induction_on hf ?_ ?_
  · intro a ha g _
    change (a • g i).coeff n ∈ J
    rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    exact J.mul_mem_right _ ha
  · intro g g' hg hg'
    change (g i + g' i).coeff n ∈ J
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact add_mem hg hg'

/-- `H⁰(𝒪(-d)^ι / J) = 0` for `d ≥ 1`: the twisting sheaf `𝒪(-d)` has no sections over any base. -/
lemma H0_quot_free_eq_bot {ι : Type u} [Fintype ι] {d : ℕ} (hd : 1 ≤ d) :
    ((free (A := A) ι d).quot J).H0 = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨s', m'⟩ h
  induction s' using Submodule.Quotient.induction_on with | H s => ?_
  induction m' using Submodule.Quotient.induction_on with | H m => ?_
  have h' : (free (A := A) ι d).r0 s - (free (A := A) ι d).r1 m ∈
      (J • ⊤ : Submodule A (ι → A[T;T⁻¹])) := by
    rw [TwoCech.mem_H0] at h
    exact (Submodule.Quotient.eq _).1 h
  have hc := coeff_mem_of_mem_smul_top_pi_laurent J h'
  have hs : s ∈ (J • ⊤ : Submodule A (ι → A[X])) := by
    refine mem_smul_top_pi_poly J fun i n ↦ ?_
    have := hc i n
    change (res0 A (s i) - resInf A (-(d : ℤ)) (m i)).coeff (n : ℤ) ∈ J at this
    rwa [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_res0, coeff_resInf,
      if_pos (by omega), if_neg (by omega), sub_zero, Int.toNat_natCast] at this
  have hm : m ∈ (J • ⊤ : Submodule A (ι → A[X])) := by
    refine mem_smul_top_pi_poly J fun i n ↦ ?_
    have := hc i (-(d : ℤ) - n)
    change (res0 A (s i) - resInf A (-(d : ℤ)) (m i)).coeff (-(d : ℤ) - n) ∈ J at this
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_res0, coeff_resInf,
      if_neg (by omega), if_pos (by omega), zero_sub, neg_mem_iff] at this
    simpa using this
  rw [Submodule.mem_bot, Prod.mk_eq_zero]
  exact ⟨(Submodule.Quotient.mk_eq_zero _).2 hs, (Submodule.Quotient.mk_eq_zero _).2 hm⟩

/-! ### The Artin–Rees lemma on the charts -/

/-- **Artin–Rees on a chart.** Let `f : P → Q` be `A`-linear, compatible with endomorphisms
`φ`, `ψ`, and let `P` be finitely generated over `A[X]` via `φ`. Over a Noetherian ring, there is
`c` with `ker f ∩ Iⁿ P ⊆ Iⁿ⁻ᶜ ker f` for all `n ≥ c` (Stacks, Lemma 10.51.2, Tag 00IN, applied
over `A[X]` to the ideal `I A[X]`). -/
lemma exists_artinRees_aeval [IsNoetherianRing A] {P Q : Type u} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (φ : P →ₗ[A] P) (ψ : Q →ₗ[A] Q) (f : P →ₗ[A] Q)
    (hf : ∀ p, f (φ p) = ψ (f p)) [Module.Finite A[X] (Module.AEval' φ)] (I : Ideal A) :
    ∃ c : ℕ, ∀ n ≥ c, ∀ k ∈ LinearMap.ker f, k ∈ I ^ n • (⊤ : Submodule A P) →
      k ∈ I ^ (n - c) • LinearMap.ker f := by
  let F' : Module.AEval' φ →ₗ[A[X]] Module.AEval' ψ :=
    LinearMap.ofAEval φ ((Module.AEval'.of ψ).toLinearMap ∘ₗ f) fun p ↦ by
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      rw [Module.AEval'.X_smul_of, ← hf]
      rfl
  let I' : Ideal A[X] := I.map (algebraMap A A[X])
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I' (LinearMap.ker F')
  refine ⟨c, fun n hn k hk hkn ↦ ?_⟩
  set v := Module.AEval'.of φ k with hv
  have hvN : v ∈ LinearMap.ker F' := by
    rw [LinearMap.mem_ker] at hk ⊢
    change Module.AEval'.of ψ (f ((Module.AEval'.of φ).symm v)) = 0
    rw [hv, LinearEquiv.symm_apply_apply, hk, map_zero]
  have hvn : v ∈ I' ^ n • (⊤ : Submodule A[X] (Module.AEval' φ)) := by
    rw [← Submodule.restrictScalars_mem A, ← Ideal.map_pow, Ideal.smul_restrictScalars,
      Submodule.restrictScalars_top]
    have := Submodule.mem_map_of_mem (f := (Module.AEval'.of φ).toLinearMap) hkn
    rwa [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at this
  have hv' : v ∈ I' ^ (n - c) • LinearMap.ker F' := by
    have := hc n hn ▸ (show v ∈ I' ^ n • ⊤ ⊓ LinearMap.ker F' from ⟨hvn, hvN⟩)
    exact Submodule.smul_mono le_rfl inf_le_right this
  rw [← Submodule.restrictScalars_mem A, ← Ideal.map_pow, Ideal.smul_restrictScalars] at hv'
  have := Submodule.mem_map_of_mem (f := (Module.AEval'.of φ).symm.toLinearMap) hv'
  rw [Submodule.map_smul''] at this
  convert this using 2
  · ext p
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem, LinearMap.mem_ker,
      LinearEquiv.coe_coe]
    constructor
    · intro hp
      refine ⟨Module.AEval'.of φ p, ?_, by simp⟩
      change Module.AEval'.of ψ (f ((Module.AEval'.of φ).symm _)) = 0
      simp [hp]
    · rintro ⟨w, hw, rfl⟩
      have : Module.AEval'.of ψ (f ((Module.AEval'.of φ).symm w)) = 0 := hw
      simpa using this
  · simp [hv]

variable {M N : ChartModule A}

lemma smul_ker_mono {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (f : P →ₗ[A] Q) (I : Ideal A) {a b : ℕ} (hab : a ≤ b) :
    I ^ b • LinearMap.ker f ≤ I ^ a • LinearMap.ker f :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)

/-- **Artin–Rees for a morphism of chart modules**: over a Noetherian ring, for `φ : M → N` with
`M` of finite type, there is `c` with `ker φ ∩ Iⁿ M ⊆ Iⁿ⁻ᶜ ker φ` on all three charts. -/
lemma Hom.exists_artinRees [IsNoetherianRing A] (φ : Hom M N)
    [Module.Finite A[X] (Module.AEval' M.x0)] [Module.Finite A[X] (Module.AEval' M.x1)]
    (I : Ideal A) : ∃ c : ℕ, ∀ n ≥ c,
      (∀ k ∈ LinearMap.ker φ.f0, k ∈ I ^ n • (⊤ : Submodule A M.M0) →
        k ∈ I ^ (n - c) • LinearMap.ker φ.f0) ∧
      (∀ k ∈ LinearMap.ker φ.f1, k ∈ I ^ n • (⊤ : Submodule A M.M1) →
        k ∈ I ^ (n - c) • LinearMap.ker φ.f1) ∧
      (∀ k ∈ LinearMap.ker φ.f01, k ∈ I ^ n • (⊤ : Submodule A M.M01) →
        k ∈ I ^ (n - c) • LinearMap.ker φ.f01) := by
  obtain ⟨c0, h0⟩ := exists_artinRees_aeval M.x0 N.x0 φ.f0 φ.comm_x0 I
  obtain ⟨c1, h1⟩ := exists_artinRees_aeval M.x1 N.x1 φ.f1 φ.comm_x1 I
  refine ⟨max c0 c1, fun n hn ↦ ⟨fun k hk hkn ↦ ?_, fun k hk hkn ↦ ?_, fun z hz hzn ↦ ?_⟩⟩
  · exact smul_ker_mono _ I (by omega) (h0 n (le_of_max_le_left hn) k hk hkn)
  · exact smul_ker_mono _ I (by omega) (h1 n (le_of_max_le_right hn) k hk hkn)
  · -- reduce to the chart `Spec A[X]` by clearing denominators
    obtain ⟨m', k, hm', hk⟩ := M.exists_of_mem_smul_top_M01 (I ^ n) hzn
    have hzK : φ.f01 z = 0 := hz
    have h1' : N.r0 (φ.f0 m') = 0 := by
      rw [← φ.comm_r0, ← hk, ← zpow_natCast, φ.comm_t_zpow, hzK, map_zero]
    obtain ⟨j, hj⟩ := N.ker_r0 _ h1'
    set w := (M.x0 ^ j) m' with hw
    have hwK : w ∈ LinearMap.ker φ.f0 := by
      rw [LinearMap.mem_ker, hw, φ.comm_x0_pow, hj]
    have hwn : w ∈ I ^ n • (⊤ : Submodule A M.M0) := by
      rw [hw]
      clear hw hwK hj
      induction j with
      | zero => exact hm'
      | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact smul_top_le_comap _ M.x0 ih
    have hwc : w ∈ I ^ (n - max c0 c1) • LinearMap.ker φ.f0 :=
      smul_ker_mono (a := n - max c0 c1) _ I (by omega) (h0 n (le_of_max_le_left hn) w hwK hwn)
    -- `r₀ w = T^{j+k} z` lies in `I^{n-c} ker φ₀₁`
    have hr0 : M.r0 w ∈ I ^ (n - max c0 c1) • LinearMap.ker φ.f01 := by
      have := Submodule.mem_map_of_mem (f := M.r0) hwc
      rw [Submodule.map_smul''] at this
      refine Submodule.smul_mono le_rfl ?_ this
      rw [Submodule.map_le_iff_le_comap]
      intro m (hm : φ.f0 m = 0)
      change φ.f01 (M.r0 m) = 0
      rw [φ.comm_r0, hm, map_zero]
    have hzw : z = (M.t.symm ^ (j + k)) (M.r0 w) := by
      rw [hw, ← t_pow_r0, ← hk, ← pow_add_apply]
      change z = (M.t.symm ^ (j + k) * M.t ^ (j + k)) z
      rw [show M.t.symm = M.t⁻¹ from rfl, inv_pow, inv_mul_cancel]
      rfl
    rw [hzw]
    have := Submodule.mem_map_of_mem (f := ((M.t.symm ^ (j + k) : M.M01 ≃ₗ[A] M.M01) :
      M.M01 →ₗ[A] M.M01)) hr0
    rw [Submodule.map_smul''] at this
    refine Submodule.smul_mono le_rfl ?_ this
    rw [Submodule.map_le_iff_le_comap]
    intro y (hy : φ.f01 y = 0)
    change φ.f01 ((M.t.symm ^ (j + k)) y) = 0
    rw [φ.comm_t_symm_pow, hy, map_zero]

end ChartModule

end ProjectiveLine
