/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleAdic

/-!
# Kernels of compatible surjections onto an adic system

Let `S` be an adic system of coherent modules on `ℙ¹_A` (`AdicChartSystem`) and
`φₙ : G → Mₙ` compatible chart-surjective morphisms from a chart module `G` of finite type. The
kernels `Lₙ = ker (G / Iⁿ G → Mₙ)` form an inverse system with surjective transitions, which is in
general not adic; by the uniform Artin–Rees lemma (`FormalSchemes.UniformArtinRees`) the system
`Kₙ = L_{n+c} / Iⁿ L_{n+c}` is adic and maps onto `Lₙ`. This is the construction of kernels in the
category of coherent formal modules (Stacks, Lemma 30.23.2, Tag 087X) in the case needed for the
Grothendieck existence theorem.
-/

universe u

open Polynomial LaurentPolynomial

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A]

/-! ### Finiteness of kernels and reductions -/

lemma finite_ker_x0 [IsNoetherianRing A] {P Q : ChartModule A} (φ : Hom P Q)
    [Module.Finite A[X] (Module.AEval' P.x0)] : Module.Finite A[X] (Module.AEval' φ.ker.x0) := by
  haveI : IsNoetherian A[X] (Module.AEval' P.x0) := inferInstance
  let j : Module.AEval' φ.ker.x0 →ₗ[A[X]] Module.AEval' P.x0 :=
    LinearMap.ofAEval _ ((Module.AEval'.of P.x0).toLinearMap ∘ₗ
      (LinearMap.ker φ.f0).subtype) fun m ↦ by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        rw [Module.AEval'.X_smul_of]
        rfl
  refine Module.Finite.of_injective j fun a b hab ↦ ?_
  have := congrArg (Module.AEval'.of P.x0).symm hab
  simp only [j, LinearMap.ofAEval, LinearMap.coe_mk] at this
  exact (Module.AEval'.of φ.ker.x0).symm.injective (Subtype.ext this)

lemma finite_ker_x1 [IsNoetherianRing A] {P Q : ChartModule A} (φ : Hom P Q)
    [Module.Finite A[X] (Module.AEval' P.x1)] : Module.Finite A[X] (Module.AEval' φ.ker.x1) := by
  haveI : IsNoetherian A[X] (Module.AEval' P.x1) := inferInstance
  let j : Module.AEval' φ.ker.x1 →ₗ[A[X]] Module.AEval' P.x1 :=
    LinearMap.ofAEval _ ((Module.AEval'.of P.x1).toLinearMap ∘ₗ
      (LinearMap.ker φ.f1).subtype) fun m ↦ by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        rw [Module.AEval'.X_smul_of]
        rfl
  refine Module.Finite.of_injective j fun a b hab ↦ ?_
  have := congrArg (Module.AEval'.of P.x1).symm hab
  simp only [j, LinearMap.ofAEval, LinearMap.coe_mk] at this
  exact (Module.AEval'.of φ.ker.x1).symm.injective (Subtype.ext this)

lemma finite_quot_x0 (P : ChartModule A) (J : Ideal A)
    [Module.Finite A[X] (Module.AEval' P.x0)] :
    Module.Finite A[X] (Module.AEval' (P.quot J).x0) := by
  let q : Module.AEval' P.x0 →ₗ[A[X]] Module.AEval' (P.quot J).x0 :=
    LinearMap.ofAEval _ ((Module.AEval'.of (P.quot J).x0).toLinearMap ∘ₗ
      (J • (⊤ : Submodule A P.M0)).mkQ) fun m ↦ by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        rw [Module.AEval'.X_smul_of]
        rfl
  refine Module.Finite.of_surjective q fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (Module.AEval'.of (P.quot J).x0).surjective y
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Module.AEval'.of P.x0 m, by simp [q, LinearMap.ofAEval]⟩

lemma finite_quot_x1 (P : ChartModule A) (J : Ideal A)
    [Module.Finite A[X] (Module.AEval' P.x1)] :
    Module.Finite A[X] (Module.AEval' (P.quot J).x1) := by
  let q : Module.AEval' P.x1 →ₗ[A[X]] Module.AEval' (P.quot J).x1 :=
    LinearMap.ofAEval _ ((Module.AEval'.of (P.quot J).x1).toLinearMap ∘ₗ
      (J • (⊤ : Submodule A P.M1)).mkQ) fun m ↦ by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        rw [Module.AEval'.X_smul_of]
        rfl
  refine Module.Finite.of_surjective q fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (Module.AEval'.of (P.quot J).x1).surjective y
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Module.AEval'.of P.x1 m, by simp [q, LinearMap.ofAEval]⟩

/-! ### Factoring through a reduction -/

/-- A morphism into a module killed by `J` factors through `P / J P`. -/
noncomputable def Hom.factorQuot {P Q : ChartModule A} (φ : Hom P Q) (J : Ideal A)
    (h0 : J • (⊤ : Submodule A Q.M0) = ⊥) (h1 : J • (⊤ : Submodule A Q.M1) = ⊥) :
    Hom (P.quot J) Q :=
  (P.quotHom J).descend (Submodule.mkQ_surjective _) (Submodule.mkQ_surjective _) φ
    (by
      intro x hx
      change Submodule.Quotient.mk x = 0 at hx
      rw [Submodule.Quotient.mk_eq_zero] at hx
      have := smul_top_le_comap J φ.f0 hx
      rw [h0] at this
      exact this)
    (by
      intro x hx
      change Submodule.Quotient.mk x = 0 at hx
      rw [Submodule.Quotient.mk_eq_zero] at hx
      have := smul_top_le_comap J φ.f1 hx
      rw [h1] at this
      exact this)

lemma Hom.factorQuot_comp {P Q : ChartModule A} (φ : Hom P Q) (J : Ideal A)
    (h0 : J • (⊤ : Submodule A Q.M0) = ⊥) (h1 : J • (⊤ : Submodule A Q.M1) = ⊥) :
    (φ.factorQuot J h0 h1).comp (P.quotHom J) = φ :=
  Hom.descend_comp _ _ _ _ _ _

/-! ### Kernels of compatible surjections from a sum of twisting sheaves -/

section FreeKernel

variable {ι : Type u}

lemma mem_powIdeal_smul_iff (I : Ideal A) (m : ℕ) (v : ι → A[X]) :
    v ∈ ((I.map (algebraMap A A[X])) ^ m • (⊤ : Submodule A[X] (ι → A[X]))) ↔
      v ∈ (I ^ m • (⊤ : Submodule A (ι → A[X]))) := by
  rw [← Submodule.restrictScalars_mem A, ← Ideal.map_pow, Ideal.smul_restrictScalars,
    Submodule.restrictScalars_top]

lemma restrictScalars_powIdeal_smul (I : Ideal A) (m : ℕ) (K : Submodule A[X] (ι → A[X])) :
    ((I.map (algebraMap A A[X])) ^ m • K).restrictScalars A = I ^ m • K.restrictScalars A := by
  rw [← Ideal.map_pow, Ideal.smul_restrictScalars]

/-- An `A`-submodule of `ι → A[X]` stable under `X` is an `A[X]`-submodule. -/
def toPolySubmodule (K : Submodule A (ι → A[X])) (hK : ∀ v ∈ K, (X : A[X]) • v ∈ K) :
    Submodule A[X] (ι → A[X]) where
  carrier := K
  add_mem' := K.add_mem
  zero_mem' := K.zero_mem
  smul_mem' p v hv := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [add_smul]; exact K.add_mem hp hq
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, mul_smul,
        show ∀ w : ι → A[X], (C a : A[X]) • w = a • w from fun w ↦ algebraMap_smul A[X] a w]
      refine K.smul_mem a ?_
      clear * - hK hv
      induction n with
      | zero => simpa using hv
      | succ n ih => rw [pow_succ', mul_smul]; exact hK _ ih

@[simp] lemma mem_toPolySubmodule (K : Submodule A (ι → A[X])) (hK) (v : ι → A[X]) :
    v ∈ toPolySubmodule K hK ↔ v ∈ K := Iff.rfl

end FreeKernel

end ChartModule

namespace AdicChartSystem

open ChartModule FormalSchemes.UniformArtinRees

variable {A : Type u} [CommRing A] {I : Ideal A} (S : AdicChartSystem I) {ι : Type u} [Fintype ι]
  {d : ℕ} {φ : ∀ n, Hom (free (A := A) ι d) (S.M n)}

section Stab

variable (hφ : ∀ m n (h : m ≤ n), (S.tr h).comp (φ n) = φ m)

include hφ in
lemma ker_f0_mono {m n : ℕ} (h : m ≤ n) : LinearMap.ker (φ n).f0 ≤ LinearMap.ker (φ m).f0 := by
  intro x (hx : (φ n).f0 x = 0)
  change (φ m).f0 x = 0
  rw [← hφ m n h]
  change (S.tr h).f0 ((φ n).f0 x) = 0
  rw [hx, map_zero]

include hφ in
lemma ker_f1_mono {m n : ℕ} (h : m ≤ n) : LinearMap.ker (φ n).f1 ≤ LinearMap.ker (φ m).f1 := by
  intro x (hx : (φ n).f1 x = 0)
  change (φ m).f1 x = 0
  rw [← hφ m n h]
  change (S.tr h).f1 ((φ n).f1 x) = 0
  rw [hx, map_zero]

lemma smul_top_le_ker_f0 (m : ℕ) : I ^ m • (⊤ : Submodule A (free (A := A) ι d).M0) ≤
    LinearMap.ker (φ m).f0 := by
  have := smul_top_le_comap (I ^ m) (φ m).f0
  rw [S.kill0] at this
  intro x hx
  exact this hx

lemma smul_top_le_ker_f1 (m : ℕ) : I ^ m • (⊤ : Submodule A (free (A := A) ι d).M1) ≤
    LinearMap.ker (φ m).f1 := by
  have := smul_top_le_comap (I ^ m) (φ m).f1
  rw [S.kill1] at this
  intro x hx
  exact this hx

variable (hs0 : ∀ n, Function.Surjective (φ n).f0) (hs1 : ∀ n, Function.Surjective (φ n).f1)

include hφ hs0 in
lemma ker_f0_sup {m n : ℕ} (h : m ≤ n) :
    LinearMap.ker (φ n).f0 ⊔ I ^ m • ⊤ = LinearMap.ker (φ m).f0 := by
  apply le_antisymm (sup_le (S.ker_f0_mono hφ h) (S.smul_top_le_ker_f0 m))
  intro x (hx : (φ m).f0 x = 0)
  have h1 : (φ n).f0 x ∈ I ^ m • (⊤ : Submodule A (S.M n).M0) := by
    rw [← S.ker0 h, LinearMap.mem_ker, ← hx]
    exact congrArg (fun χ : Hom (free (A := A) ι d) (S.M m) ↦ χ.f0 x) (hφ m n h)
  obtain ⟨k, hk, hxk⟩ := exists_ker_lift (φ n).f0 (hs0 n) (I ^ m) x h1
  rw [show x = k + (x - k) by abel]
  exact Submodule.add_mem_sup hk hxk

include hφ hs1 in
lemma ker_f1_sup {m n : ℕ} (h : m ≤ n) :
    LinearMap.ker (φ n).f1 ⊔ I ^ m • ⊤ = LinearMap.ker (φ m).f1 := by
  apply le_antisymm (sup_le (S.ker_f1_mono hφ h) (S.smul_top_le_ker_f1 m))
  intro x (hx : (φ m).f1 x = 0)
  have h1 : (φ n).f1 x ∈ I ^ m • (⊤ : Submodule A (S.M n).M1) := by
    rw [← S.ker1 h, LinearMap.mem_ker, ← hx]
    exact congrArg (fun χ : Hom (free (A := A) ι d) (S.M m) ↦ χ.f1 x) (hφ m n h)
  obtain ⟨k, hk, hxk⟩ := exists_ker_lift (φ n).f1 (hs1 n) (I ^ m) x h1
  rw [show x = k + (x - k) by abel]
  exact Submodule.add_mem_sup hk hxk

/-- The kernel on `Spec A[X]`, as an `A[X]`-submodule. -/
noncomputable def polyKer0 (m : ℕ) : Submodule A[X] (ι → A[X]) :=
  toPolySubmodule (LinearMap.ker (φ m).f0) fun v (hv : (φ m).f0 v = 0) ↦ by
    change (φ m).f0 ((free (A := A) ι d).x0 v) = 0
    rw [(φ m).comm_x0, hv, map_zero]

/-- The kernel on `Spec A[Y]`, as an `A[X]`-submodule. -/
noncomputable def polyKer1 (m : ℕ) : Submodule A[X] (ι → A[X]) :=
  toPolySubmodule (LinearMap.ker (φ m).f1) fun v (hv : (φ m).f1 v = 0) ↦ by
    change (φ m).f1 ((free (A := A) ι d).x1 v) = 0
    rw [(φ m).comm_x1, hv, map_zero]

include hφ hs0 hs1 in
/-- **Uniform stabilisation of the kernels** (Stacks, proof of Lemma 30.23.2, Tag 087X): there is
`c` such that for `n ≤ n'`, `ker φ_{n'+c} ∩ (Iⁿ ker φ_{n+c} + I^{n+c} G)` lies in
`Iⁿ ker φ_{n'+c} + I^{n'+c} G`, on both charts. -/
theorem exists_stab [IsNoetherianRing A] : ∃ c : ℕ, ∀ n n', n ≤ n' →
    (∀ x ∈ LinearMap.ker (φ (n' + c)).f0,
      x ∈ I ^ n • LinearMap.ker (φ (n + c)).f0 ⊔ I ^ (n + c) • ⊤ →
      x ∈ I ^ n • LinearMap.ker (φ (n' + c)).f0 ⊔ I ^ (n' + c) • ⊤) ∧
    (∀ x ∈ LinearMap.ker (φ (n' + c)).f1,
      x ∈ I ^ n • LinearMap.ker (φ (n + c)).f1 ⊔ I ^ (n + c) • ⊤ →
      x ∈ I ^ n • LinearMap.ker (φ (n' + c)).f1 ⊔ I ^ (n' + c) • ⊤) := by
  set J := I.map (algebraMap A A[X])
  have hKK0 : ∀ {m m' : ℕ}, m ≤ m' →
      S.polyKer0 (φ := φ) m' ⊔ J ^ m • ⊤ = S.polyKer0 (φ := φ) m := by
    intro m m' h
    apply Submodule.restrictScalars_injective A
    rw [Submodule.restrictScalars_sup, restrictScalars_powIdeal_smul,
      Submodule.restrictScalars_top]
    exact S.ker_f0_sup hφ hs0 h
  have hKK1 : ∀ {m m' : ℕ}, m ≤ m' →
      S.polyKer1 (φ := φ) m' ⊔ J ^ m • ⊤ = S.polyKer1 (φ := φ) m := by
    intro m m' h
    apply Submodule.restrictScalars_injective A
    rw [Submodule.restrictScalars_sup, restrictScalars_powIdeal_smul,
      Submodule.restrictScalars_top]
    exact S.ker_f1_sup hφ hs1 h
  obtain ⟨c0, hc0⟩ := uniform_artinRees' (J := J) (S.polyKer0 (φ := φ)) hKK0
  obtain ⟨c1, hc1⟩ := uniform_artinRees' (J := J) (S.polyKer1 (φ := φ)) hKK1
  refine ⟨max c0 c1, fun n n' hnn' ↦ ⟨fun x hx hxin ↦ ?_, fun x hx hxin ↦ ?_⟩⟩
  · set N := n + max c0 c1
    set N' := n' + max c0 c1
    have hsup := S.ker_f0_sup hφ hs0 (show N ≤ N' by omega)
    -- `x ∈ Iⁿ ker φ_{N'} + I^N G`
    have h1 : x ∈ I ^ n • LinearMap.ker (φ N').f0 ⊔ I ^ N • ⊤ := by
      have hle : I ^ n • LinearMap.ker (φ N).f0 ⊔ I ^ N • (⊤ : Submodule A _) ≤
          I ^ n • LinearMap.ker (φ N').f0 ⊔ I ^ N • ⊤ := by
        rw [← hsup, Submodule.smul_sup]
        refine sup_le (sup_le le_sup_left ?_) le_sup_right
        rw [← Submodule.mul_smul, ← pow_add]
        exact (pow_smul_top_anti I (by omega)).trans le_sup_right
      exact hle hxin
    obtain ⟨y, hy, g, hg, rfl⟩ := Submodule.mem_sup.1 h1
    have hgK : g ∈ LinearMap.ker (φ N').f0 := by
      have hyK : y ∈ LinearMap.ker (φ N').f0 := Submodule.smul_le_right hy
      have := sub_mem hx hyK
      rwa [add_sub_cancel_left] at this
    have hg' : g ∈ (J ^ N • ⊤ : Submodule A[X] (ι → A[X])) := (mem_powIdeal_smul_iff I N g).2 hg
    have h2 := hc0 N N' (by omega) (by omega) g hgK hg'
    rw [← Submodule.restrictScalars_mem A, Submodule.restrictScalars_sup,
      restrictScalars_powIdeal_smul, restrictScalars_powIdeal_smul,
      Submodule.restrictScalars_top] at h2
    have h3 : I ^ (N - c0) • (S.polyKer0 (φ := φ) N').restrictScalars A ≤
        I ^ n • LinearMap.ker (φ N').f0 :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
    obtain ⟨y', hy', g', hg', hyg⟩ := Submodule.mem_sup.1 h2
    rw [← hyg]
    have := add_mem (add_mem (Submodule.mem_sup_left hy)
      (Submodule.mem_sup_left (h3 hy'))) (Submodule.mem_sup_right hg' :
        g' ∈ I ^ n • LinearMap.ker (φ N').f0 ⊔ I ^ N' • ⊤)
    rwa [add_assoc] at this
  · set N := n + max c0 c1
    set N' := n' + max c0 c1
    have hsup := S.ker_f1_sup hφ hs1 (show N ≤ N' by omega)
    -- `x ∈ Iⁿ ker φ_{N'} + I^N G`
    have h1 : x ∈ I ^ n • LinearMap.ker (φ N').f1 ⊔ I ^ N • ⊤ := by
      have hle : I ^ n • LinearMap.ker (φ N).f1 ⊔ I ^ N • (⊤ : Submodule A _) ≤
          I ^ n • LinearMap.ker (φ N').f1 ⊔ I ^ N • ⊤ := by
        rw [← hsup, Submodule.smul_sup]
        refine sup_le (sup_le le_sup_left ?_) le_sup_right
        rw [← Submodule.mul_smul, ← pow_add]
        exact (pow_smul_top_anti I (by omega)).trans le_sup_right
      exact hle hxin
    obtain ⟨y, hy, g, hg, rfl⟩ := Submodule.mem_sup.1 h1
    have hgK : g ∈ LinearMap.ker (φ N').f1 := by
      have hyK : y ∈ LinearMap.ker (φ N').f1 := Submodule.smul_le_right hy
      have := sub_mem hx hyK
      rwa [add_sub_cancel_left] at this
    have hg' : g ∈ (J ^ N • ⊤ : Submodule A[X] (ι → A[X])) := (mem_powIdeal_smul_iff I N g).2 hg
    have h2 := hc1 N N' (by omega) (by omega) g hgK hg'
    rw [← Submodule.restrictScalars_mem A, Submodule.restrictScalars_sup,
      restrictScalars_powIdeal_smul, restrictScalars_powIdeal_smul,
      Submodule.restrictScalars_top] at h2
    have h3 : I ^ (N - c1) • (S.polyKer1 (φ := φ) N').restrictScalars A ≤
        I ^ n • LinearMap.ker (φ N').f1 :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
    obtain ⟨y', hy', g', hg', hyg⟩ := Submodule.mem_sup.1 h2
    rw [← hyg]
    have := add_mem (add_mem (Submodule.mem_sup_left hy)
      (Submodule.mem_sup_left (h3 hy'))) (Submodule.mem_sup_right hg' :
        g' ∈ I ^ n • LinearMap.ker (φ N').f1 ⊔ I ^ N' • ⊤)
    rwa [add_assoc] at this


end Stab

end AdicChartSystem

end ProjectiveLine
