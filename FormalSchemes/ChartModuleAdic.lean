/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleFF
import FormalSchemes.UniformArtinRees

/-!
# Adic systems of coherent modules on `ℙ¹_A`

An object of `Coh(ℙ¹_A, I)` (the category of Stacks, Lemma 30.23.2, Tag 087X) is here an
`AdicChartSystem`: chart modules `Mₙ` of finite type with `Iⁿ Mₙ = 0` and
chart-surjective transition maps `Mₙ → Mₘ` (`m ≤ n`) whose kernels are `Iᵐ Mₙ`, i.e. with
`Mₙ / Iᵐ Mₙ = Mₘ`.

This file proves the uniform vanishing of `H¹` of twists for such a system
(`AdicChartSystem.exists_H1_twist_eq_bot`): `H¹(Mₙ(k)) = 0` for all `n` once `k` is large for
`M₁` — `H¹` commutes with reduction on `ℙ¹` and Nakayama does the rest.
-/

universe u

open Polynomial LaurentPolynomial

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A]

section Reduction

variable {P Q : ChartModule A} (J : Ideal A) (π : Hom P Q)

/-- If `J P₀ = ker π₀`, then `Q₀` is killed by `J`. -/
lemma smul_top_eq_bot_of_ker {P₁ Q₁ : Type u} [AddCommGroup P₁] [Module A P₁] [AddCommGroup Q₁]
    [Module A Q₁] (f : P₁ →ₗ[A] Q₁) (hf : Function.Surjective f)
    (hk : LinearMap.ker f = J • (⊤ : Submodule A P₁)) : J • (⊤ : Submodule A Q₁) = ⊥ := by
  rw [← LinearMap.range_eq_top.2 hf, LinearMap.range_eq_map, ← Submodule.map_smul'', ← hk,
    eq_bot_iff, Submodule.map_le_iff_le_comap]
  intro x hx
  simpa using hx

/-- A chart module whose chart `Spec A[X]` is killed by `J` is killed by `J` on the overlap. -/
lemma smul_top_M01_eq_bot (h : J • (⊤ : Submodule A Q.M0) = ⊥) :
    J • (⊤ : Submodule A Q.M01) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro a ha z _
  obtain ⟨m, k, hk⟩ := Q.exists_r0 z
  have ham : a • m = 0 := by
    have : a • m ∈ J • (⊤ : Submodule A Q.M0) := Submodule.smul_mem_smul ha Submodule.mem_top
    rwa [h, Submodule.mem_bot] at this
  rw [Submodule.mem_bot]
  apply (Q.t ^ k).injective
  rw [map_smul, hk, ← map_smul, ham, map_zero, map_zero]

variable {J π}

/-- For a chart-surjective `π` with `ker π = J P` on the two charts, also `ker π₀₁ = J P₀₁`. -/
lemma Hom.ker_f01_eq (h0 : Function.Surjective π.f0) (hk0 : LinearMap.ker π.f0 = J • ⊤) :
    LinearMap.ker π.f01 = J • (⊤ : Submodule A P.M01) := by
  apply le_antisymm
  · intro z (hz : π.f01 z = 0)
    obtain ⟨m, k, hk⟩ := P.exists_r0 z
    have h1 : Q.r0 (π.f0 m) = 0 := by
      rw [← π.comm_r0, ← hk, ← zpow_natCast, π.comm_t_zpow, hz, map_zero]
    obtain ⟨j, hj⟩ := Q.ker_r0 _ h1
    have hm : (P.x0 ^ j) m ∈ J • (⊤ : Submodule A P.M0) := by
      rw [← hk0, LinearMap.mem_ker, π.comm_x0_pow, hj]
    have h2 : (P.t ^ (j + k)) z ∈ J • (⊤ : Submodule A P.M01) := by
      rw [pow_add_apply, hk, t_pow_r0]
      exact smul_top_le_comap J P.r0 hm
    have h3 := smul_top_le_comap J ((P.t.symm ^ (j + k) : P.M01 ≃ₗ[A] P.M01) : P.M01 →ₗ[A] P.M01)
      h2
    have e : (P.t.symm ^ (j + k)) ((P.t ^ (j + k)) z) = z := by
      change (P.t.symm ^ (j + k) * P.t ^ (j + k)) z = z
      rw [show P.t.symm = P.t⁻¹ from rfl, inv_pow, inv_mul_cancel]
      rfl
    simpa [e] using h3
  · have hQ0 := smul_top_eq_bot_of_ker J π.f0 h0 hk0
    have hQ := smul_top_M01_eq_bot J (Q := Q) hQ0
    rw [Submodule.smul_le]
    intro a ha z _
    rw [LinearMap.mem_ker, map_smul]
    have : a • π.f01 z ∈ J • (⊤ : Submodule A Q.M01) :=
      Submodule.smul_mem_smul ha Submodule.mem_top
    rwa [hQ, Submodule.mem_bot] at this

/-- **`H¹` along a reduction**: the kernel of `H¹(P) → H¹(Q)` lies in `J H¹(P)`. -/
lemma Hom.ker_mapH1_le (h0 : Function.Surjective π.f0) (h1 : Function.Surjective π.f1)
    (hk0 : LinearMap.ker π.f0 = J • ⊤) :
    LinearMap.ker π.mapH1 ≤ J • (⊤ : Submodule A P.H1) := by
  intro w hw
  induction w using Submodule.Quotient.induction_on with | H z => ?_
  rw [LinearMap.mem_ker] at hw
  change Submodule.Quotient.mk (π.f01 z) = 0 at hw
  rw [Submodule.Quotient.mk_eq_zero] at hw
  obtain ⟨⟨a', b'⟩, hab⟩ := hw
  obtain ⟨a, rfl⟩ := h0 a'
  obtain ⟨b, rfl⟩ := h1 b'
  have hz : z - TwoCech.d P.r0 P.r1 (a, b) ∈ J • (⊤ : Submodule A P.M01) := by
    rw [← π.ker_f01_eq h0 hk0, LinearMap.mem_ker, map_sub, ← hab, TwoCech.d_apply,
      TwoCech.d_apply, map_sub, π.comm_r0, π.comm_r1, sub_self]
  have hmk : Submodule.Quotient.mk (p := LinearMap.range (TwoCech.d P.r0 P.r1)) z =
      (LinearMap.range (TwoCech.d P.r0 P.r1)).mkQ (z - TwoCech.d P.r0 P.r1 (a, b)) := by
    rw [map_sub, sub_eq_self.2 ((Submodule.Quotient.mk_eq_zero _).2
      (LinearMap.mem_range_self _ (a, b)))]
    rfl
  rw [hmk]
  have := Submodule.mem_map_of_mem (f := (LinearMap.range (TwoCech.d P.r0 P.r1)).mkQ) hz
  rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this

end Reduction

/-- Nakayama for a nilpotent ideal: `N = J N` and `Jⁿ N = 0` force `N = 0`. -/
lemma eq_bot_of_le_smul {N : Type u} [AddCommGroup N] [Module A N] (J : Ideal A) (n : ℕ)
    (h : (⊤ : Submodule A N) ≤ J • ⊤) (hn : J ^ n • (⊤ : Submodule A N) = ⊥) :
    (⊤ : Submodule A N) = ⊥ := by
  have : ∀ k : ℕ, (⊤ : Submodule A N) ≤ J ^ k • ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_comm, Submodule.mul_smul]
      exact h.trans (Submodule.smul_mono le_rfl ih)
  exact eq_bot_iff.2 ((this n).trans hn.le)

end ChartModule

variable {A : Type u} [CommRing A]

open ChartModule in
/-- **A compatible system of coherent modules on `ℙ¹_A`**: `Mₙ` of finite type, killed by `Iⁿ`,
with chart-surjective transition maps `Mₙ → Mₘ` whose kernels are `Iᵐ Mₙ`. -/
structure AdicChartSystem (I : Ideal A) where
  /-- the level `n`, a module on `ℙ¹_{A/Iⁿ}` -/
  M : ℕ → ChartModule A
  /-- the transition maps -/
  tr : ∀ {m n : ℕ}, m ≤ n → Hom (M n) (M m)
  tr_comp : ∀ {k m n : ℕ} (h₁ : k ≤ m) (h₂ : m ≤ n), (tr h₁).comp (tr h₂) = tr (h₁.trans h₂)
  surj0 : ∀ {m n : ℕ} (h : m ≤ n), Function.Surjective (tr h).f0
  surj1 : ∀ {m n : ℕ} (h : m ≤ n), Function.Surjective (tr h).f1
  ker0 : ∀ {m n : ℕ} (h : m ≤ n), LinearMap.ker (tr h).f0 = I ^ m • ⊤
  ker1 : ∀ {m n : ℕ} (h : m ≤ n), LinearMap.ker (tr h).f1 = I ^ m • ⊤
  kill0 : ∀ n, I ^ n • (⊤ : Submodule A (M n).M0) = ⊥
  fin0 : ∀ n, Module.Finite A[X] (Module.AEval' (M n).x0)
  fin1 : ∀ n, Module.Finite A[X] (Module.AEval' (M n).x1)

namespace AdicChartSystem

open ChartModule

variable {I : Ideal A} (S : AdicChartSystem I)

lemma kill01 (n : ℕ) : I ^ n • (⊤ : Submodule A (S.M n).M01) = ⊥ :=
  smul_top_M01_eq_bot _ (S.kill0 n)

/-- **Uniform vanishing of `H¹`** (the input of Stacks, Lemma 30.24.2, Tag 0884, for `ℙ¹`):
`H¹(Mₙ(k)) = 0` for all `n` and all `k ≥ k₀`. -/
theorem exists_H1_twist_eq_bot : ∃ k₀ : ℕ, ∀ k : ℤ, k₀ ≤ k → ∀ n,
    Subsingleton ((S.M n).twist k).H1 := by
  haveI := S.fin0 1
  obtain ⟨k₀, hk₀⟩ := (S.M 1).exists_subsingleton_H1_twist
  refine ⟨k₀, fun k hk n ↦ ?_⟩
  rcases Nat.lt_or_ge n 1 with hn | hn
  · -- `M₀ = 0`
    obtain rfl : n = 0 := by omega
    have h0 : (⊤ : Submodule A (S.M 0).M01) = ⊥ := by simpa using S.kill01 0
    refine Submodule.Quotient.subsingleton_iff.2 ?_
    rw [eq_top_iff]
    intro z _
    have : z = 0 := by
      have hz : z ∈ (⊤ : Submodule A (S.M 0).M01) := Submodule.mem_top
      rwa [h0, Submodule.mem_bot] at hz
    rw [this]
    exact zero_mem _
  · haveI := S.fin0 n
    haveI : Module.Finite A ((S.M n).twist k).H1 := (S.M n).finite_H1_twist k
    haveI := hk₀ k hk
    let π := (S.tr hn).twist k
    have hle : LinearMap.ker π.mapH1 ≤ I • (⊤ : Submodule A ((S.M n).twist k).H1) := by
      have := Hom.ker_mapH1_le (J := I) (π := π) (S.surj0 hn) (S.surj1 hn)
        (by have := S.ker0 hn; rw [pow_one] at this; exact this)
      exact this
    have htop : (⊤ : Submodule A ((S.M n).twist k).H1) ≤ I • ⊤ := by
      intro w _
      apply hle
      rw [LinearMap.mem_ker]
      exact Subsingleton.elim _ _
    have hkill : I ^ n • (⊤ : Submodule A ((S.M n).twist k).H1) = ⊥ := by
      rw [eq_bot_iff, Submodule.smul_le]
      intro a ha w _
      induction w using Submodule.Quotient.induction_on with | H z => ?_
      rw [← Submodule.Quotient.mk_smul, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      have hz : ∀ y : (S.M n).M01, a • y = 0 := fun y ↦ by
        have h := Submodule.smul_mem_smul ha (Submodule.mem_top (x := y))
        rwa [S.kill01 n, Submodule.mem_bot] at h
      rw [show a • z = 0 from hz z]
      exact zero_mem _
    have htb := eq_bot_of_le_smul I n htop hkill
    refine ⟨fun x y ↦ ?_⟩
    have hx : x ∈ (⊤ : Submodule A ((S.M n).twist k).H1) := Submodule.mem_top
    have hy : y ∈ (⊤ : Submodule A ((S.M n).twist k).H1) := Submodule.mem_top
    rw [htb, Submodule.mem_bot] at hx hy
    rw [hx, hy]

end AdicChartSystem

end ProjectiveLine
