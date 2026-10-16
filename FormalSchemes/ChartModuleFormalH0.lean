/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleDelta

/-!
# The theorem on formal functions for `H⁰` on `ℙ¹_A`

Let `A` be Noetherian, `I ⊆ A` an ideal and `M` a chart module of finite type (a coherent module on
`ℙ¹_A`, `FormalSchemes.ChartModule`). Then the natural map
`H⁰(M)^ → lim_n H⁰(M / Iⁿ M)` is an isomorphism (`ChartModule.formalFunctionsH0`; Stacks,
Lemma 30.20.6, Tag 087U, for `p = 0`; the case `p = 1` is `ChartModule.formalFunctionsH1`).

The proof uses a presentation `φ : 𝒪(-d)^ι → M` (`d ≥ 1`, surjective on the charts). Since
`H⁰(𝒪(-d)^ι / Iⁿ) = 0`, the connecting maps embed `H⁰(M)` into `V = H¹(ker φ)` and `H⁰(M / Iⁿ M)`
into `Vₙ = H¹(ker (φ mod Iⁿ))`, compatibly with the reduction maps `aₙ : V → Vₙ`, which are
surjective with `Iⁿ V ⊆ ker aₙ ⊆ Iⁿ⁻ᶜ V` (Artin–Rees on the charts). Two further applications of the
Artin–Rees lemma, to `H⁰(M) ⊆ V` and to the image of `V → H¹(𝒪(-d)^ι)`, give injectivity and
surjectivity.
-/

universe u

open Polynomial LaurentPolynomial

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A]

/-- **Artin–Rees for the image of a linear map.** -/
lemma exists_artinRees_range [IsNoetherianRing A] {P Q : Type u} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] [Module.Finite A Q] (f : P →ₗ[A] Q) (I : Ideal A) :
    ∃ c : ℕ, ∀ n ≥ c, ∀ p : P, f p ∈ I ^ n • (⊤ : Submodule A Q) →
      ∃ p' ∈ I ^ (n - c) • (⊤ : Submodule A P), f p' = f p := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  refine ⟨c, fun n hn p hp ↦ ?_⟩
  have h1 : f p ∈ I ^ n • ⊤ ⊓ LinearMap.range f := ⟨hp, LinearMap.mem_range_self f p⟩
  rw [hc n hn] at h1
  have h2 := Submodule.smul_mono le_rfl inf_le_right h1
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
  obtain ⟨p', hp', hfp⟩ := h2
  exact ⟨p', hp', hfp⟩

lemma pow_smul_top_anti {P : Type u} [AddCommGroup P] [Module A P] (I : Ideal A) {a b : ℕ}
    (hab : a ≤ b) : I ^ b • (⊤ : Submodule A P) ≤ I ^ a • ⊤ :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)

variable (M : ChartModule A) (I : Ideal A)

/-- The compatible systems of sections of the reductions `M / Iⁿ M`. -/
def H0System : Submodule A (∀ n : ℕ, (M.quot (I ^ n)).H0) where
  carrier := {f | ∀ (m n : ℕ) (h : m ≤ n),
    (M.quotMap (Ideal.pow_le_pow_right h)).mapH0 (f n) = f m}
  add_mem' {f g} hf hg m n h := by
    simp only [Pi.add_apply, map_add, hf m n h, hg m n h]
  zero_mem' m n h := by simp
  smul_mem' a f hf m n h := by simp only [Pi.smul_apply, map_smul, hf m n h]

lemma smul_top_le_ker_quotHom_mapH0 (J : Ideal A) :
    J • (⊤ : Submodule A M.H0) ≤ LinearMap.ker (M.quotHom J).mapH0 := by
  rw [Submodule.smul_le]
  intro a ha x _
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  change (Submodule.Quotient.mk (a • x.1.1), Submodule.Quotient.mk (a • x.1.2)) = (0, 0)
  rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul ha Submodule.mem_top),
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul ha Submodule.mem_top)]

/-- `H⁰(M) / J H⁰(M) → H⁰(M / J M)`. -/
noncomputable def H0Reduce (J : Ideal A) :
    M.H0 ⧸ (J • (⊤ : Submodule A M.H0)) →ₗ[A] (M.quot J).H0 :=
  (J • (⊤ : Submodule A M.H0)).liftQ (M.quotHom J).mapH0 (M.smul_top_le_ker_quotHom_mapH0 J)

lemma H0Reduce_mk (J : Ideal A) (x : M.H0) :
    M.H0Reduce J (Submodule.Quotient.mk x) = (M.quotHom J).mapH0 x := rfl

/-- The natural map `H⁰(M)^ → lim H⁰(M / Iⁿ M)`. -/
noncomputable def toH0System : AdicCompletion I M.H0 →ₗ[A] M.H0System I where
  toFun x := ⟨fun n ↦ M.H0Reduce (I ^ n) (x.val n), fun m n h ↦ by
    simp only
    rw [← AdicCompletion.transitionMap_comp_eval_apply I M.H0 h x]
    induction x.val n using Submodule.Quotient.induction_on with | H y => rfl⟩
  map_add' x y := by ext n : 2; simp [AdicCompletion.val_add_apply]
  map_smul' a x := by ext n : 2; simp [AdicCompletion.val_smul_apply]

lemma finite_free_x0 {ι : Type u} [Fintype ι] (d : ℕ) :
    Module.Finite A[X] (Module.AEval' (free (A := A) ι d).x0) := by
  let F := free (A := A) ι d
  let e : Module.AEval' F.x0 ≃ₗ[A[X]] (ι → A[X]) :=
    LinearEquiv.ofAEval F.x0 (LinearEquiv.refl A (ι → A[X]) : F.M0 ≃ₗ[A] (ι → A[X]))
      fun _ ↦ rfl
  exact Module.Finite.equiv e.symm

lemma finite_free_x1 {ι : Type u} [Fintype ι] (d : ℕ) :
    Module.Finite A[X] (Module.AEval' (free (A := A) ι d).x1) := by
  let F := free (A := A) ι d
  let e : Module.AEval' F.x1 ≃ₗ[A[X]] (ι → A[X]) :=
    LinearEquiv.ofAEval F.x1 (LinearEquiv.refl A (ι → A[X]) : F.M1 ≃ₗ[A] (ι → A[X]))
      fun _ ↦ rfl
  exact Module.Finite.equiv e.symm

section Presentation

variable {M I} {ι : Type u} [Fintype ι] {d : ℕ} (φ : Hom (free (A := A) ι d) M)
  (h0 : Function.Surjective φ.f0) (h1 : Function.Surjective φ.f1)

lemma Hom.kerι_reduce_mapH1_toReduceKer (J : Ideal A) (w : φ.ker.H1) :
    (φ.reduce J).kerι.mapH1 ((φ.toReduceKer J).mapH1 w) =
      ((free (A := A) ι d).quotHom J).mapH1 (φ.kerι.mapH1 w) := by
  induction w using Submodule.Quotient.induction_on with | H z => rfl

include h0 h1 in
theorem toH0System_injective_of_presentation [IsNoetherianRing A] (hd : 1 ≤ d) :
    Function.Injective (M.toH0System I) := by
  haveI := finite_free_x0 (A := A) (ι := ι) d
  haveI := finite_free_x1 (A := A) (ι := ι) d
  haveI := finite_ker_free φ
  haveI : Module.Finite A φ.ker.H1 := φ.ker.finite_H1
  obtain ⟨c, hc⟩ := φ.exists_artinRees I
  obtain ⟨c', hc'⟩ := exists_artinRees_range (φ.delta h0 h1) I
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  ext n
  rw [AdicCompletion.val_zero, Pi.zero_apply]
  set N := n + c + c'
  obtain ⟨h, hh⟩ := Submodule.Quotient.mk_surjective _ (x.val N)
  have hψ : (M.quotHom (I ^ N)).mapH0 h = 0 := by
    have := congrArg (fun f : M.H0System I ↦ f.1 N) hx
    simp only [toH0System, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero,
      Pi.zero_apply] at this
    rwa [← hh, H0Reduce_mk] at this
  have ha : (φ.toReduceKer (I ^ N)).mapH1 (φ.delta h0 h1 h) = 0 := by
    rw [← φ.delta_reduce h0 h1 (I ^ N) h, hψ, map_zero]
  have hmem := φ.ker_toReduceKer_mapH1_le h0 h1 I c N (hc N (by omega)).2.2 ha
  obtain ⟨h', hh', he⟩ := hc' (N - c) (by omega) h hmem
  have hh'' : h' = h := φ.delta_injective h0 h1 (H0_free_eq_bot ι d hd) he
  rw [← AdicCompletion.transitionMap_comp_eval_apply I M.H0 (show n ≤ N by omega) x, ← hh]
  change Submodule.Quotient.mk h = 0
  rw [Submodule.Quotient.mk_eq_zero, ← hh'']
  exact pow_smul_top_anti I (by omega) hh'

include h0 h1 in
theorem toH0System_surjective_of_presentation [IsNoetherianRing A] (hd : 1 ≤ d) :
    Function.Surjective (M.toH0System I) := by
  classical
  haveI := finite_free_x0 (A := A) (ι := ι) d
  haveI := finite_free_x1 (A := A) (ι := ι) d
  haveI := finite_ker_free φ
  haveI : Module.Finite A φ.ker.H1 := φ.ker.finite_H1
  haveI : Module.Finite A (free (A := A) ι d).H1 := (free (A := A) ι d).finite_H1
  obtain ⟨c, hc⟩ := φ.exists_artinRees I
  obtain ⟨c', hc'⟩ := exists_artinRees_range (φ.delta h0 h1) I
  obtain ⟨c'', hc''⟩ := exists_artinRees_range φ.kerι.mapH1 I
  intro f
  -- notation
  let a : ∀ n : ℕ, φ.ker.H1 →ₗ[A] (φ.reduce (I ^ n)).ker.H1 :=
    fun n ↦ (φ.toReduceKer (I ^ n)).mapH1
  let δn : ∀ n : ℕ, (M.quot (I ^ n)).H0 →ₗ[A] (φ.reduce (I ^ n)).ker.H1 :=
    fun n ↦ (φ.reduce (I ^ n)).delta (φ.reduce_surjective0 h0 _) (φ.reduce_surjective1 h1 _)
  -- the kernel of `aₙ`
  have hker : ∀ n (w : φ.ker.H1), a n w = 0 → w ∈ I ^ (n - c) • (⊤ : Submodule A φ.ker.H1) := by
    intro n w hw
    rcases le_or_gt c n with hn | hn
    · exact φ.ker_toReduceKer_mapH1_le h0 h1 I c n (hc n hn).2.2 hw
    · rw [show n - c = 0 by omega, pow_zero, Submodule.one_smul]
      exact Submodule.mem_top
  choose w hw using fun n ↦ φ.toReduceKer_mapH1_surjective h0 (I ^ n) (δn n (f.1 n))
  have hA : ∀ n N, n ≤ N → a n (w N) = δn n (f.1 n) := by
    intro n N hnN
    have hle : I ^ N ≤ I ^ n := Ideal.pow_le_pow_right hnN
    change (φ.toReduceKer (I ^ n)).mapH1 (w N) = _
    rw [← φ.reduceKerMap_toReduceKer hle, hw N]
    change (φ.reduceKerMap hle).mapH1 ((φ.reduce (I ^ N)).delta _ _ (f.1 N)) = _
    rw [← φ.delta_quotMap hle h0 h1, f.2 n N hnN]
  have hB : ∀ n, φ.kerι.mapH1 (w n) ∈ I ^ n • (⊤ : Submodule A (free (A := A) ι d).H1) := by
    intro n
    rw [← (free (A := A) ι d).ker_quotHom_mapH1 (I ^ n), LinearMap.mem_ker,
      ← φ.kerι_reduce_mapH1_toReduceKer]
    change (φ.reduce (I ^ n)).kerι.mapH1 (a n (w n)) = 0
    rw [hA n n le_rfl]
    exact ((φ.reduce (I ^ n)).exact_delta_mapH1 _ _).apply_apply_eq_zero _
  have hv : ∀ n, ∃ v : φ.ker.H1, (c'' ≤ n → v ∈ I ^ (n - c'') • (⊤ : Submodule A φ.ker.H1)) ∧
      φ.kerι.mapH1 v = φ.kerι.mapH1 (w n) := by
    intro n
    rcases le_or_gt c'' n with hn | hn
    · obtain ⟨v, hv, hv'⟩ := hc'' n hn (w n) (hB n)
      exact ⟨v, fun _ ↦ hv, hv'⟩
    · exact ⟨w n, fun h ↦ absurd h (by omega), rfl⟩
  choose v hv1 hv2 using hv
  have hg : ∀ n, ∃ g : M.H0, φ.delta h0 h1 g = w n - v n := by
    intro n
    refine ((φ.exact_delta_mapH1 h0 h1) (w n - v n)).1 ?_
    rw [map_sub, hv2, sub_self]
  choose g hg using hg
  have vmem : ∀ n k, k ≤ n → v n ∈ I ^ (k - c'') • (⊤ : Submodule A φ.ker.H1) := by
    intro n k hkn
    rcases le_or_gt c'' n with hn | hn
    · exact pow_smul_top_anti I (by omega) (hv1 n hn)
    · rw [show k - c'' = 0 by omega, pow_zero, Submodule.one_smul]
      exact Submodule.mem_top
  set C := c + c'' + c' with hC
  have hcauchy : ∀ n N, n ≤ N → g N - g n ∈ I ^ (n - C) • (⊤ : Submodule A M.H0) := by
    intro n N hnN
    have hw1 : w N - w n ∈ I ^ (n - c) • (⊤ : Submodule A φ.ker.H1) :=
      hker n _ (by rw [map_sub, hA n N hnN, hA n n le_rfl, sub_self])
    have hδ : φ.delta h0 h1 (g N - g n) ∈ I ^ (n - c - c'') • (⊤ : Submodule A φ.ker.H1) := by
      rw [map_sub, hg, hg, show w N - v N - (w n - v n) = (w N - w n) - (v N - v n) by abel]
      exact sub_mem (pow_smul_top_anti I (by omega) hw1)
        (sub_mem (pow_smul_top_anti I (by omega) (vmem N n hnN))
          (pow_smul_top_anti I (by omega) (vmem n n le_rfl)))
    rcases le_or_gt c' (n - c - c'') with hn | hn
    · obtain ⟨g', hg', he⟩ := hc' _ hn _ hδ
      rw [← φ.delta_injective h0 h1 (H0_free_eq_bot ι d hd) he]
      exact pow_smul_top_anti I (by omega) hg'
    · rw [show n - C = 0 by omega, pow_zero, Submodule.one_smul]
      exact Submodule.mem_top
  let sq : AdicCompletion.AdicCauchySequence I M.H0 := ⟨fun k ↦ g (k + C), fun {m k} hmk ↦ by
    rw [SModEq.sub_mem]
    have := hcauchy (m + C) (k + C) (by omega)
    rw [show m + C - C = m by omega] at this
    rw [← neg_sub]
    exact neg_mem this⟩
  refine ⟨AdicCompletion.mk I M.H0 sq, ?_⟩
  apply Subtype.ext
  funext n
  change M.H0Reduce (I ^ n) (Submodule.Quotient.mk (g (n + C))) = f.1 n
  rw [H0Reduce_mk]
  apply (φ.reduce (I ^ n)).delta_injective (φ.reduce_surjective0 h0 _)
    (φ.reduce_surjective1 h1 _) (H0_quot_free_eq_bot (I ^ n) hd)
  rw [φ.delta_reduce h0 h1, hg, map_sub]
  change a n (w (n + C)) - a n (v (n + C)) = δn n (f.1 n)
  have hv0 : a n (v (n + C)) = 0 :=
    φ.smul_top_le_ker_toReduceKer_mapH1 (I ^ n)
      (pow_smul_top_anti I (by omega) (vmem (n + C) (n + C) le_rfl))
  rw [hv0, sub_zero, hA n (n + C) (by omega)]

end Presentation

variable [IsNoetherianRing A] [Module.Finite A[X] (Module.AEval' M.x0)]
  [Module.Finite A[X] (Module.AEval' M.x1)]

theorem bijective_toH0System : Function.Bijective (M.toH0System I) := by
  obtain ⟨n₀, hn₀⟩ := M.exists_sectionsHom_surjective
  obtain ⟨ι, _, σ, hσ, h0, h1⟩ := hn₀ (max n₀ 1) (le_max_left _ _)
  let φ := sectionsHom (n := max n₀ 1) M σ hσ
  exact ⟨toH0System_injective_of_presentation φ h0 h1 (le_max_right _ _),
    toH0System_surjective_of_presentation φ h0 h1 (le_max_right _ _)⟩

/-- **The theorem on formal functions for `H⁰` on `ℙ¹_A`** (Stacks, Lemma 30.20.6, Tag 087U, for
`p = 0`): for `A` Noetherian and `M` of finite type, `H⁰(M)^ ≃ lim_n H⁰(M / Iⁿ M)` via the natural
map. -/
noncomputable def formalFunctionsH0 : AdicCompletion I M.H0 ≃ₗ[A] M.H0System I :=
  LinearEquiv.ofBijective (M.toH0System I) (M.bijective_toH0System I)

@[simp] lemma formalFunctionsH0_apply (x : AdicCompletion I M.H0) :
    M.formalFunctionsH0 I x = M.toH0System I x := rfl

end ChartModule

end ProjectiveLine
