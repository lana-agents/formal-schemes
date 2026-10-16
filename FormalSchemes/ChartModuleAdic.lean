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

/-- The identity morphism. -/
def Hom.id (M : ChartModule A) : Hom M M where
  f0 := LinearMap.id
  f1 := LinearMap.id
  f01 := LinearMap.id
  comm_x0 _ := rfl
  comm_x1 _ := rfl
  comm_t _ := rfl
  comm_r0 _ := rfl
  comm_r1 _ := rfl

@[simp] lemma Hom.comp_id {M N : ChartModule A} (φ : Hom M N) : φ.comp (Hom.id M) = φ :=
  Hom.ext' rfl rfl rfl

@[simp] lemma Hom.id_comp {M N : ChartModule A} (φ : Hom M N) : (Hom.id N).comp φ = φ :=
  Hom.ext' rfl rfl rfl

lemma homFreeSections_comp {M P : ChartModule A} {ι : Type u} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (ψ : Hom M P) (φ : Hom (free (A := A) ι d) M) (i : ι) :
    homFreeSections P (ψ.comp φ) i = (ψ.twist d).mapH0 (homFreeSections M φ i) := rfl

/-- If every `H¹(Nᵢ)` vanishes, so does `H¹(⊕ Nᵢ)`. -/
lemma subsingleton_H1_pi {ι : Type u} [Fintype ι] {N : ι → ChartModule A}
    (h : ∀ i, Subsingleton (N i).H1) : Subsingleton (pi N).H1 := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro z _
  have : ∀ i, z i ∈ LinearMap.range (TwoCech.d (N i).r0 (N i).r1) :=
    fun i ↦ Submodule.Quotient.subsingleton_iff.1 (h i) ▸ Submodule.mem_top
  choose y hy using this
  refine ⟨(fun i ↦ (y i).1, fun i ↦ (y i).2), funext fun i ↦ ?_⟩
  rw [TwoCech.d_apply]
  have := hy i
  rw [TwoCech.d_apply] at this
  exact this

/-! ### Morphisms out of finite sums, and multiplication by scalars -/

section PiLift

variable {ι : Type u} [Fintype ι] {N : ι → ChartModule A} {P : ChartModule A}

/-- The morphism out of a finite direct sum given by morphisms out of the summands. -/
noncomputable def Hom.piLift (g : ∀ i, Hom (N i) P) : Hom (pi N) P where
  f0 := ∑ i, (g i).f0 ∘ₗ LinearMap.proj i
  f1 := ∑ i, (g i).f1 ∘ₗ LinearMap.proj i
  f01 := ∑ i, (g i).f01 ∘ₗ LinearMap.proj i
  comm_x0 m := by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (g i).comm_x0 (m i)
  comm_x1 m := by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (g i).comm_x1 (m i)
  comm_t z := by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (g i).comm_t (z i)
  comm_r0 m := by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (g i).comm_r0 (m i)
  comm_r1 m := by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (g i).comm_r1 (m i)

lemma Hom.piLift_f0_apply (g : ∀ i, Hom (N i) P) (x : (pi N).M0) :
    (Hom.piLift g).f0 x = ∑ i, (g i).f0 (x i) := by
  simp [Hom.piLift]

lemma Hom.piLift_f1_apply (g : ∀ i, Hom (N i) P) (x : (pi N).M1) :
    (Hom.piLift g).f1 x = ∑ i, (g i).f1 (x i) := by
  simp [Hom.piLift]

/-- If every `H¹(Nᵢ(k))` vanishes, so does `H¹((⊕ Nᵢ)(k))`. -/
lemma subsingleton_H1_pi_twist (k : ℕ) (h : ∀ i, Subsingleton ((N i).twist k).H1) :
    Subsingleton ((pi N).twist k).H1 := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro z _
  have : ∀ i, z i ∈ LinearMap.range (TwoCech.d ((N i).twist k).r0 ((N i).twist k).r1) :=
    fun i ↦ Submodule.Quotient.subsingleton_iff.1 (h i) ▸ Submodule.mem_top
  choose y hy using this
  refine ⟨(fun i ↦ (y i).1, fun i ↦ (y i).2), funext fun i ↦ ?_⟩
  rw [TwoCech.d_apply]
  have := hy i
  rw [TwoCech.d_apply] at this
  rw [← this]
  change (N i).r0 (y i).1 - ((LinearEquiv.piCongrRight fun i ↦ (N i).t) ^ (k : ℤ))
    (fun j ↦ (N j).r1 (y j).2) i = _
  rw [zpow_natCast, piCongrRight_pow_apply, ← zpow_natCast]
  rfl

end PiLift

/-- Multiplication by `a` as a morphism into a kernel containing `a M`. -/
noncomputable def Hom.smulKer {P Q : ChartModule A} (π : Hom P Q) (a : A)
    (h0 : ∀ m, a • m ∈ LinearMap.ker π.f0) (h1 : ∀ m, a • m ∈ LinearMap.ker π.f1) :
    Hom P π.ker where
  f0 := LinearMap.codRestrict _ (a • LinearMap.id) h0
  f1 := LinearMap.codRestrict _ (a • LinearMap.id) h1
  f01 := LinearMap.codRestrict _ (a • LinearMap.id) fun z ↦ by
    change π.f01 (a • z) = 0
    obtain ⟨m, k, hk⟩ := P.exists_r0 z
    apply (Q.t ^ k).injective
    rw [map_zero, map_smul, map_smul, ← zpow_natCast, ← π.comm_t_zpow, zpow_natCast, hk,
      π.comm_r0, ← map_smul, ← map_smul, show π.f0 (a • m) = 0 from h0 m, map_zero]
  comm_x0 m := by
    apply Subtype.ext
    exact (map_smul P.x0 a m).symm
  comm_x1 m := by
    apply Subtype.ext
    exact (map_smul P.x1 a m).symm
  comm_t z := by
    apply Subtype.ext
    exact (map_smul P.t a z).symm
  comm_r0 m := by
    apply Subtype.ext
    exact (map_smul P.r0 a m).symm
  comm_r1 m := by
    apply Subtype.ext
    exact (map_smul P.r1 a m).symm

lemma le_range_sum_smul {N : Type u} [AddCommGroup N] [Module A N] (J : Ideal A) {ι : Type u}
    [Fintype ι] (a : ι → A) (ha : J = Ideal.span (Set.range a)) :
    J • (⊤ : Submodule A N) ≤ LinearMap.range (∑ i, a i • LinearMap.proj (R := A)
      (φ := fun _ : ι ↦ N) i) := by
  rw [Submodule.smul_le]
  intro c hc x _
  rw [ha, Ideal.span, Submodule.mem_span_range_iff_exists_fun] at hc
  obtain ⟨b, rfl⟩ := hc
  refine ⟨fun i ↦ b i • x, ?_⟩
  simp [Finset.sum_smul, smul_smul, mul_comm]

/-- Submodule Nakayama for a nilpotent ideal. -/
lemma eq_top_of_sup_smul {N : Type u} [AddCommGroup N] [Module A N] (J : Ideal A) (n : ℕ)
    (P : Submodule A N) (h : P ⊔ J • ⊤ = ⊤) (hn : J ^ n • (⊤ : Submodule A N) = ⊥) : P = ⊤ := by
  have : ∀ k : ℕ, (⊤ : Submodule A N) ≤ P ⊔ J ^ k • ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc (⊤ : Submodule A N) = P ⊔ J • ⊤ := h.symm
        _ ≤ P ⊔ J • (P ⊔ J ^ k • ⊤) := sup_le_sup_left (Submodule.smul_mono le_rfl ih) _
        _ ≤ P ⊔ J ^ (k + 1) • ⊤ := by
          rw [Submodule.smul_sup, pow_succ', Submodule.mul_smul]
          exact sup_le (le_sup_left.trans le_rfl)
            (sup_le ((Submodule.smul_le_right).trans le_sup_left) le_sup_right)
  rw [eq_top_iff]
  exact (this n).trans (by rw [hn, sup_bot_eq])

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
  tr_refl : ∀ n, tr (le_refl n) = Hom.id (M n)
  kill0 : ∀ n, I ^ n • (⊤ : Submodule A (M n).M0) = ⊥
  kill1 : ∀ n, I ^ n • (⊤ : Submodule A (M n).M1) = ⊥
  fin0 : ∀ n, Module.Finite A[X] (Module.AEval' (M n).x0)
  fin1 : ∀ n, Module.Finite A[X] (Module.AEval' (M n).x1)

namespace AdicChartSystem

open ChartModule

variable {I : Ideal A} (S : AdicChartSystem I)

lemma kill01 (n : ℕ) : I ^ n • (⊤ : Submodule A (S.M n).M01) = ⊥ :=
  smul_top_M01_eq_bot _ (S.kill0 n)

/-- **Uniform vanishing of `H¹`** (cf. Stacks, Lemma 30.24.2, Tag 0884, for `ℙ¹`):
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

/-- **`H⁰` of twists is surjective along the transitions** once `H¹(M₁(k)) = 0`: the kernel
`Iᵐ M_{m+1}` of `M_{m+1} → Mₘ` is a quotient of a sum of copies of `M₁`, so its `H¹(k)` vanishes. -/
lemma surjective_mapH0_tr_twist [IsNoetherianRing A] (k : ℕ)
    (hk : Subsingleton ((S.M 1).twist k).H1) (m : ℕ) :
    Function.Surjective ((S.tr (Nat.le_succ m)).twist k).mapH0 := by
  let π := (S.tr (Nat.le_succ m)).twist k
  obtain ⟨r, a₀, ha₀⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian (I ^ m))
  let a : ULift.{u} (Fin r) → A := fun i ↦ a₀ i.down
  have ha : Ideal.span (Set.range a) = I ^ m := by
    rw [← ha₀]
    congr 1
    ext x
    exact ⟨fun ⟨i, hi⟩ ↦ ⟨i.down, hi⟩, fun ⟨i, hi⟩ ↦ ⟨⟨i⟩, hi⟩⟩
  have haI : ∀ i, a i ∈ I ^ m := fun i ↦ ha ▸ Ideal.subset_span ⟨i, rfl⟩
  have hπ0 : ∀ i x, a i • x ∈ LinearMap.ker π.f0 := by
    intro i x
    change _ ∈ LinearMap.ker (S.tr (Nat.le_succ m)).f0
    rw [S.ker0]
    exact Submodule.smul_mem_smul (haI i) Submodule.mem_top
  have hπ1 : ∀ i x, a i • x ∈ LinearMap.ker π.f1 := by
    intro i x
    change _ ∈ LinearMap.ker (S.tr (Nat.le_succ m)).f1
    rw [S.ker1]
    exact Submodule.smul_mem_smul (haI i) Submodule.mem_top
  let μ : ULift.{u} (Fin r) → Hom ((S.M (m + 1)).twist k) π.ker := fun i ↦
    π.smulKer (a i) (hπ0 i) (hπ1 i)
  have h1n : 1 ≤ m + 1 := by omega
  let ρ := (S.tr h1n).twist k
  have hsmul : ∀ (i : ULift.{u} (Fin r)) {P : Type u} [AddCommGroup P] [Module A P] (x : P),
      x ∈ I • (⊤ : Submodule A P) → a i • x ∈ I ^ (m + 1) • (⊤ : Submodule A P) := by
    intro i P _ _ x hx
    rw [pow_succ, Submodule.mul_smul]
    exact Submodule.smul_mem_smul (haI i) hx
  have hρ0 : ∀ i, LinearMap.ker ρ.f0 ≤ LinearMap.ker (μ i).f0 := by
    intro i x hx
    change x ∈ LinearMap.ker (S.tr h1n).f0 at hx
    rw [S.ker0, pow_one] at hx
    have := hsmul i x hx
    rw [S.kill0 (m + 1), Submodule.mem_bot] at this
    exact Subtype.ext this
  have hρ1 : ∀ i, LinearMap.ker ρ.f1 ≤ LinearMap.ker (μ i).f1 := by
    intro i x hx
    change x ∈ LinearMap.ker (S.tr h1n).f1 at hx
    rw [S.ker1, pow_one] at hx
    have := hsmul i x hx
    rw [S.kill1 (m + 1), Submodule.mem_bot] at this
    exact Subtype.ext this
  let ν : ULift.{u} (Fin r) → Hom ((S.M 1).twist k) π.ker := fun i ↦
    ρ.descend (S.surj0 h1n) (S.surj1 h1n) (μ i) (hρ0 i) (hρ1 i)
  let g := Hom.piLift ν
  have hg0 : Function.Surjective g.f0 := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ I ^ m • (⊤ : Submodule A (S.M (m + 1)).M0) := by
      rw [← S.ker0 (Nat.le_succ m)]
      exact hy
    obtain ⟨z, hz⟩ := le_range_sum_smul (I ^ m) a ha.symm hy'
    refine ⟨fun i ↦ ρ.f0 (z i), Subtype.ext ?_⟩
    rw [Hom.piLift_f0_apply]
    have hν : ∀ i, (ν i).f0 (ρ.f0 (z i)) = (μ i).f0 (z i) := fun i ↦
      congrArg (fun χ : Hom ((S.M (m + 1)).twist k) π.ker ↦ χ.f0 (z i))
        (ρ.descend_comp (S.surj0 h1n) (S.surj1 h1n) (μ i) (hρ0 i) (hρ1 i))
    simp only [hν]
    rw [Submodule.coe_sum, ← hz]
    simp [μ, Hom.smulKer]
  haveI : Subsingleton (pi fun _ : ULift.{u} (Fin r) ↦ (S.M 1).twist k).H1 :=
    subsingleton_H1_pi fun _ ↦ hk
  have hs : Function.Surjective g.mapH1 :=
    TwoCech.mapH1_surjective _ _ _ _ _ (g.surjective_f01 hg0)
  haveI : Subsingleton π.ker.H1 := hs.subsingleton
  intro y
  exact (π.exact_mapH0_delta (S.surj0 _) (S.surj1 _) y).1 (Subsingleton.elim _ _)

lemma surjective_of_sup {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (f : P →ₗ[A] Q) (n : ℕ) (hn : I ^ n • (⊤ : Submodule A Q) = ⊥)
    (h : ∀ y : Q, ∃ x, y - f x ∈ I • (⊤ : Submodule A Q)) : Function.Surjective f := by
  rw [← LinearMap.range_eq_top]
  refine eq_top_of_sup_smul I n _ (eq_top_iff.2 fun y _ ↦ ?_) hn
  obtain ⟨x, hx⟩ := h y
  rw [show y = f x + (y - f x) by abel]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self f x) hx

lemma subsingleton_M0_zero : Subsingleton (S.M 0).M0 := by
  have h := S.kill0 0
  rw [pow_zero, Submodule.one_smul] at h
  refine ⟨fun x y ↦ ?_⟩
  have hx : x ∈ (⊤ : Submodule A (S.M 0).M0) := Submodule.mem_top
  have hy : y ∈ (⊤ : Submodule A (S.M 0).M0) := Submodule.mem_top
  rw [h, Submodule.mem_bot] at hx hy
  rw [hx, hy]

lemma subsingleton_M1_zero : Subsingleton (S.M 0).M1 := by
  have h := S.kill1 0
  rw [pow_zero, Submodule.one_smul] at h
  refine ⟨fun x y ↦ ?_⟩
  have hx : x ∈ (⊤ : Submodule A (S.M 0).M1) := Submodule.mem_top
  have hy : y ∈ (⊤ : Submodule A (S.M 0).M1) := Submodule.mem_top
  rw [h, Submodule.mem_bot] at hx hy
  rw [hx, hy]

/-- **Compatible surjections from a sum of twisting sheaves** (Stacks, proof of Lemma 30.24.3,
Tag 0885, for `ℙ¹`): there are `d`, finitely many sections and compatible morphisms
`𝒪(-d)^ι → Mₙ` surjective on both charts for every `n`. -/
theorem exists_compatible_surjection [IsNoetherianRing A] :
    ∃ (d : ℕ) (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
      (φ : ∀ n, Hom (free (A := A) ι d) (S.M n)),
      (∀ n, Function.Surjective (φ n).f0 ∧ Function.Surjective (φ n).f1) ∧
      ∀ m n (h : m ≤ n), (S.tr h).comp (φ n) = φ m := by
  classical
  haveI := S.fin0 1
  haveI := S.fin1 1
  obtain ⟨k₀, hk₀⟩ := (S.M 1).exists_subsingleton_H1_twist
  obtain ⟨n₀, hn₀⟩ := (S.M 1).exists_sectionsHom_surjective
  obtain ⟨ι, _, σ, hσ, h0, h1⟩ := hn₀ (max k₀ n₀) (le_max_right _ _)
  set d := max k₀ n₀ with hd
  have hk : Subsingleton ((S.M 1).twist (d : ℤ)).H1 :=
    hk₀ d (by exact_mod_cast le_max_left k₀ n₀)
  let Φ0 : Hom (free (A := A) ι d) (S.M 1) := sectionsHom (S.M 1) σ hσ
  have lift : ∀ j (φ : Hom (free (A := A) ι d) (S.M (j + 1))),
      ∃ φ' : Hom (free (A := A) ι d) (S.M (j + 1 + 1)),
        (S.tr (Nat.le_succ (j + 1))).comp φ' = φ := by
    intro j φ
    have hsurj := S.surjective_mapH0_tr_twist d hk (j + 1)
    choose τ hτ using fun i ↦ hsurj (homFreeSections _ φ i)
    refine ⟨(homFreeEquiv _).symm τ, ?_⟩
    apply (homFreeEquiv _).injective
    funext i
    change homFreeSections _ ((S.tr _).comp ((homFreeEquiv _).symm τ)) i =
      homFreeSections _ φ i
    rw [homFreeSections_comp]
    have : homFreeSections _ ((homFreeEquiv (S.M (j + 1 + 1))).symm τ) i = τ i :=
      congrFun ((homFreeEquiv _).apply_symm_apply τ) i
    rw [this, hτ]
  choose L hL using lift
  let Φ : ∀ j, Hom (free (A := A) ι d) (S.M (j + 1)) := fun j ↦ Nat.rec Φ0 (fun j φ ↦ L j φ) j
  have hΦ : ∀ j, (S.tr (Nat.le_succ (j + 1))).comp (Φ (j + 1)) = Φ j := fun j ↦ hL j (Φ j)
  let φ : ∀ n, Hom (free (A := A) ι d) (S.M n) := fun n ↦
    Nat.casesOn n ((S.tr (Nat.zero_le 1)).comp Φ0) (fun j ↦ Φ j)
  have hcons : ∀ n, (S.tr (Nat.le_succ n)).comp (φ (n + 1)) = φ n := by
    intro n
    cases n with
    | zero => rfl
    | succ j => exact hΦ j
  have hcompat : ∀ m n (h : m ≤ n), (S.tr h).comp (φ n) = φ m := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base => rw [S.tr_refl, Hom.id_comp]
    | succ n hmn ih => rw [← S.tr_comp hmn (Nat.le_succ n), Hom.comp_assoc, hcons, ih]
  refine ⟨d, ι, inferInstance, inferInstance, φ, fun n ↦ ?_, hcompat⟩
  rcases n with _ | n
  · haveI := S.subsingleton_M0_zero
    haveI := S.subsingleton_M1_zero
    exact ⟨fun y ↦ ⟨0, Subsingleton.elim _ _⟩, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · have h1n : 1 ≤ n + 1 := by omega
    have hc := hcompat 1 (n + 1) h1n
    constructor
    · refine surjective_of_sup (φ (n + 1)).f0 (n + 1) (S.kill0 (n + 1)) fun y ↦ ?_
      obtain ⟨x, hx⟩ := h0 ((S.tr h1n).f0 y)
      refine ⟨x, ?_⟩
      have hker := S.ker0 h1n
      rw [pow_one] at hker
      rw [← hker, LinearMap.mem_ker, map_sub]
      have : (S.tr h1n).f0 ((φ (n + 1)).f0 x) = (φ 1).f0 x :=
        congrArg (fun χ : Hom (free (A := A) ι d) (S.M 1) ↦ χ.f0 x) hc
      rw [this]
      exact sub_eq_zero.2 hx.symm
    · refine surjective_of_sup (φ (n + 1)).f1 (n + 1) (S.kill1 (n + 1)) fun y ↦ ?_
      obtain ⟨x, hx⟩ := h1 ((S.tr h1n).f1 y)
      refine ⟨x, ?_⟩
      have hker := S.ker1 h1n
      rw [pow_one] at hker
      rw [← hker, LinearMap.mem_ker, map_sub]
      have : (S.tr h1n).f1 ((φ (n + 1)).f1 x) = (φ 1).f1 x :=
        congrArg (fun χ : Hom (free (A := A) ι d) (S.M 1) ↦ χ.f1 x) hc
      rw [this]
      exact sub_eq_zero.2 hx.symm

end AdicChartSystem

end ProjectiveLine
