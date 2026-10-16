/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModule
import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Reduction of chart modules modulo an ideal, and the theorem on formal functions for `H¹`

For a chart module `M` (a quasi-coherent module on `ℙ¹_A`, `FormalSchemes.ChartModule`) and an
ideal `J ⊆ A`, `M.quot J` is `M / J M`, the restriction of `M` to `ℙ¹_{A/J}` (pushed forward to
`ℙ¹_A`). Since `H²` vanishes on `ℙ¹`, the functor `H¹` is right exact, and so it commutes with
reduction: `H¹(M / J M) = H¹(M) / J H¹(M)` (`ChartModule.H1QuotEquiv`). For `J = Iⁿ` this gives
the theorem on formal functions for `H¹` on `ℙ¹_A`, `lim_n H¹(M / Iⁿ M) = H¹(M)^` (cf. Stacks,
Lemma 30.20.6, Tag 087U, for `p = 1`; `ChartModule.formalFunctionsH1`), in the strong form that the
comparison holds at every finite level and with no hypothesis on `A` or `I`.
-/

universe u

open Polynomial LaurentPolynomial

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A] (M : ChartModule A) (J : Ideal A)

lemma smul_top_le_comap {N P : Type u} [AddCommGroup N] [Module A N] [AddCommGroup P]
    [Module A P] (f : N →ₗ[A] P) :
    J • (⊤ : Submodule A N) ≤ (J • (⊤ : Submodule A P)).comap f :=
  Submodule.smul_le.2 fun r hr n _ ↦ by
    simpa using Submodule.smul_mem_smul hr (Submodule.mem_top (x := f n))

lemma map_smul_top_equiv {N : Type u} [AddCommGroup N] [Module A N] (e : N ≃ₗ[A] N) :
    (J • (⊤ : Submodule A N)).map (e : N →ₗ[A] N) = J • ⊤ := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

/-- Every element of `J • M₀₁` is `T⁻ᵏ m|` for some `m ∈ J • M₀`. -/
lemma exists_of_mem_smul_top_M01 {z : M.M01} (hz : z ∈ J • (⊤ : Submodule A M.M01)) :
    ∃ (m : M.M0) (k : ℕ), m ∈ J • (⊤ : Submodule A M.M0) ∧ (M.t ^ k) z = M.r0 m := by
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro a ha z _
    obtain ⟨m, k, hk⟩ := M.exists_r0 z
    exact ⟨a • m, k, Submodule.smul_mem_smul ha trivial, by rw [map_smul, hk, map_smul]⟩
  · intro z w hz hw
    obtain ⟨m, k, hm, hk⟩ := hz
    obtain ⟨m', l, hm', hl⟩ := hw
    refine ⟨(M.x0 ^ l) m + (M.x0 ^ k) m', k + l,
      add_mem (smul_top_le_comap J _ hm) (smul_top_le_comap J _ hm'), ?_⟩
    rw [map_add, map_add, ← t_pow_r0, ← t_pow_r0, ← hk, ← hl, ← pow_add_apply,
      ← pow_add_apply, add_comm l k]

/-- Every element of `J • M₀₁` is `Tᵏ m|` for some `m ∈ J • M₁`. -/
lemma exists_of_mem_smul_top_M01' {z : M.M01} (hz : z ∈ J • (⊤ : Submodule A M.M01)) :
    ∃ (m : M.M1) (k : ℕ), m ∈ J • (⊤ : Submodule A M.M1) ∧ (M.t.symm ^ k) z = M.r1 m := by
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro a ha z _
    obtain ⟨m, k, hk⟩ := M.exists_r1 z
    exact ⟨a • m, k, Submodule.smul_mem_smul ha trivial, by rw [map_smul, hk, map_smul]⟩
  · intro z w hz hw
    obtain ⟨m, k, hm, hk⟩ := hz
    obtain ⟨m', l, hm', hl⟩ := hw
    refine ⟨(M.x1 ^ l) m + (M.x1 ^ k) m', k + l,
      add_mem (smul_top_le_comap J _ hm) (smul_top_le_comap J _ hm'), ?_⟩
    rw [map_add, map_add, ← t_symm_pow_r1, ← t_symm_pow_r1, ← hk, ← hl, ← pow_add_apply,
      ← pow_add_apply, add_comm l k]

section QuotPow

variable {N : Type u} [AddCommGroup N] [Module A N] (P : Submodule A N)

lemma mapQ_pow_mk (f : N →ₗ[A] N) (h : P ≤ P.comap f) (k : ℕ) (x : N) :
    ((P.mapQ P f h) ^ k) (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((f ^ k) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ, Module.End.mul_apply, Submodule.mapQ_apply, ih, pow_succ,
      Module.End.mul_apply]

lemma quotEquiv_pow_mk (e : N ≃ₗ[A] N) (h : P.map (e : N →ₗ[A] N) = P) (k : ℕ) (x : N) :
    ((Submodule.Quotient.equiv P P e h) ^ k) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((e ^ k) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, Submodule.Quotient.equiv_apply,
      Submodule.mapQ_apply, ih, pow_succ, LinearEquiv.mul_apply]; rfl

lemma quotEquiv_symm_pow_mk (e : N ≃ₗ[A] N) (h : P.map (e : N →ₗ[A] N) = P) (k : ℕ) (x : N) :
    ((Submodule.Quotient.equiv P P e h).symm ^ k) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((e.symm ^ k) x) := by
  rw [Submodule.Quotient.equiv_symm]
  exact quotEquiv_pow_mk P e.symm _ k x

end QuotPow

/-- **Reduction modulo an ideal**: `M / J M`. -/
noncomputable abbrev quot : ChartModule A where
  M0 := ModuleCat.of A (M.M0 ⧸ J • (⊤ : Submodule A M.M0))
  M1 := ModuleCat.of A (M.M1 ⧸ J • (⊤ : Submodule A M.M1))
  M01 := ModuleCat.of A (M.M01 ⧸ J • (⊤ : Submodule A M.M01))
  x0 := Submodule.mapQ (J • ⊤) (J • ⊤) M.x0 (smul_top_le_comap J M.x0)
  x1 := Submodule.mapQ (J • ⊤) (J • ⊤) M.x1 (smul_top_le_comap J M.x1)
  t := Submodule.Quotient.equiv (J • ⊤) (J • ⊤) M.t (map_smul_top_equiv J M.t)
  r0 := Submodule.mapQ (J • ⊤) (J • ⊤) M.r0 (smul_top_le_comap J M.r0)
  r1 := Submodule.mapQ (J • ⊤) (J • ⊤) M.r1 (smul_top_le_comap J M.r1)
  r0_x0 m := by
    induction m using Submodule.Quotient.induction_on with
    | H m =>
      simp only [Submodule.mapQ_apply, Submodule.Quotient.equiv_apply, M.r0_x0]
      rfl
  r1_x1 m := by
    induction m using Submodule.Quotient.induction_on with
    | H m =>
      simp only [Submodule.mapQ_apply, M.r1_x1, Submodule.Quotient.equiv_symm,
        Submodule.Quotient.equiv_apply]
      rfl
  exists_r0 z := by
    induction z using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨m, k, hk⟩ := M.exists_r0 z
      exact ⟨Submodule.Quotient.mk m, k, by rw [quotEquiv_pow_mk, hk]; rfl⟩
  ker_r0 m hm := by
    induction m using Submodule.Quotient.induction_on with
    | H m =>
      have hm' : M.r0 m ∈ J • (⊤ : Submodule A M.M01) := (Submodule.Quotient.mk_eq_zero _).1 hm
      obtain ⟨m'', k, hm'', hk⟩ := M.exists_of_mem_smul_top_M01 J hm'
      obtain ⟨j, hj⟩ := M.ker_r0 ((M.x0 ^ k) m - m'') (by rw [map_sub, ← t_pow_r0, hk, sub_self])
      refine ⟨j + k, ?_⟩
      rw [mapQ_pow_mk, Submodule.Quotient.mk_eq_zero, end_pow_add_apply]
      rw [map_sub, sub_eq_zero] at hj
      rw [hj]
      exact smul_top_le_comap J _ hm''
  exists_r1 z := by
    induction z using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨m, k, hk⟩ := M.exists_r1 z
      exact ⟨Submodule.Quotient.mk m, k, by rw [quotEquiv_symm_pow_mk, hk]; rfl⟩
  ker_r1 m hm := by
    induction m using Submodule.Quotient.induction_on with
    | H m =>
      have hm' : M.r1 m ∈ J • (⊤ : Submodule A M.M01) := (Submodule.Quotient.mk_eq_zero _).1 hm
      obtain ⟨m'', k, hm'', hk⟩ := M.exists_of_mem_smul_top_M01' J hm'
      obtain ⟨j, hj⟩ := M.ker_r1 ((M.x1 ^ k) m - m'')
        (by rw [map_sub, ← t_symm_pow_r1, hk, sub_self])
      refine ⟨j + k, ?_⟩
      rw [mapQ_pow_mk, Submodule.Quotient.mk_eq_zero, end_pow_add_apply]
      rw [map_sub, sub_eq_zero] at hj
      rw [hj]
      exact smul_top_le_comap J _ hm''

/-- The reduction map `M → M / J M`. -/
noncomputable def quotHom : Hom M (M.quot J) where
  f0 := (J • (⊤ : Submodule A M.M0)).mkQ
  f1 := (J • (⊤ : Submodule A M.M1)).mkQ
  f01 := (J • (⊤ : Submodule A M.M01)).mkQ
  comm_x0 _ := rfl
  comm_x1 _ := rfl
  comm_t _ := rfl
  comm_r0 _ := rfl
  comm_r1 _ := rfl

lemma surjective_quotHom_mapH1 : Function.Surjective (M.quotHom J).mapH1 :=
  TwoCech.mapH1_surjective _ _ _ _ _ (Submodule.mkQ_surjective _)

/-- The kernel of `H¹(M) → H¹(M / J M)` is `J H¹(M)`. -/
lemma ker_quotHom_mapH1 :
    LinearMap.ker (M.quotHom J).mapH1 = J • (⊤ : Submodule A M.H1) := by
  apply le_antisymm
  · intro x hx
    induction x using Submodule.Quotient.induction_on with | H z => ?_
    rw [LinearMap.mem_ker] at hx
    change Submodule.Quotient.mk ((J • (⊤ : Submodule A M.M01)).mkQ z) = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨⟨a, b⟩, hab⟩ := hx
    induction a using Submodule.Quotient.induction_on with | H a => ?_
    induction b using Submodule.Quotient.induction_on with | H b => ?_
    have hmem : z - TwoCech.d M.r0 M.r1 (a, b) ∈ J • (⊤ : Submodule A M.M01) := by
      have e : (J • (⊤ : Submodule A M.M01)).mkQ (TwoCech.d M.r0 M.r1 (a, b)) =
          (J • (⊤ : Submodule A M.M01)).mkQ z := by
        rw [TwoCech.d_apply, map_sub]
        rw [TwoCech.d_apply] at hab
        exact hab
      exact (Submodule.Quotient.eq _).1 e.symm
    have : Submodule.Quotient.mk (p := LinearMap.range (TwoCech.d M.r0 M.r1)) z =
        (LinearMap.range (TwoCech.d M.r0 M.r1)).mkQ (z - TwoCech.d M.r0 M.r1 (a, b)) := by
      rw [map_sub, sub_eq_self.2 ((Submodule.Quotient.mk_eq_zero _).2
        (LinearMap.mem_range_self _ (a, b)))]
      rfl
    rw [this]
    have h2 := Submodule.mem_map_of_mem (f := (LinearMap.range (TwoCech.d M.r0 M.r1)).mkQ) hmem
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h2
    exact h2
  · rw [Submodule.smul_le]
    intro a ha x _
    rw [LinearMap.mem_ker, map_smul]
    induction x using Submodule.Quotient.induction_on with | H z => ?_
    change a • Submodule.Quotient.mk ((J • (⊤ : Submodule A M.M01)).mkQ z) = 0
    rw [← Submodule.Quotient.mk_smul, ← map_smul]
    have : (J • (⊤ : Submodule A M.M01)).mkQ (a • z) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul ha Submodule.mem_top)
    rw [this]
    rfl

/-- **`H¹` commutes with reduction** (right exactness of `H¹` on `ℙ¹`):
`H¹(M / J M) ≃ H¹(M) / J H¹(M)`. -/
noncomputable def H1QuotEquiv : (M.quot J).H1 ≃ₗ[A] M.H1 ⧸ (J • (⊤ : Submodule A M.H1)) :=
  ((LinearMap.quotKerEquivOfSurjective _ (M.surjective_quotHom_mapH1 J)).symm.trans
    (Submodule.quotEquivOfEq _ _ (M.ker_quotHom_mapH1 J)))

lemma H1QuotEquiv_mapH1 (x : M.H1) :
    M.H1QuotEquiv J ((M.quotHom J).mapH1 x) = Submodule.Quotient.mk x := by
  simp only [H1QuotEquiv, LinearEquiv.trans_apply]
  have : (LinearMap.quotKerEquivOfSurjective _ (M.surjective_quotHom_mapH1 J)).symm
      ((M.quotHom J).mapH1 x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

variable {J} {J' : Ideal A}

lemma smul_top_mono {N : Type u} [AddCommGroup N] [Module A N] (h : J ≤ J') :
    J • (⊤ : Submodule A N) ≤ J' • ⊤ :=
  Submodule.smul_mono_left h

/-- The reduction map `M / J M → M / J' M` for `J ≤ J'`. -/
noncomputable def quotMap (h : J ≤ J') : Hom (M.quot J) (M.quot J') where
  f0 := Submodule.factor (smul_top_mono h)
  f1 := Submodule.factor (smul_top_mono h)
  f01 := Submodule.factor (smul_top_mono h)
  comm_x0 m := by induction m using Submodule.Quotient.induction_on with | H m => rfl
  comm_x1 m := by induction m using Submodule.Quotient.induction_on with | H m => rfl
  comm_t z := by induction z using Submodule.Quotient.induction_on with | H z => rfl
  comm_r0 m := by induction m using Submodule.Quotient.induction_on with | H m => rfl
  comm_r1 m := by induction m using Submodule.Quotient.induction_on with | H m => rfl

lemma H1QuotEquiv_quotMap (h : J ≤ J') (y : (M.quot J).H1) :
    M.H1QuotEquiv J' ((M.quotMap h).mapH1 y) =
      Submodule.factor (smul_top_mono h) (M.H1QuotEquiv J y) := by
  obtain ⟨x, rfl⟩ := M.surjective_quotHom_mapH1 J y
  have : (M.quotMap h).mapH1 ((M.quotHom J).mapH1 x) = (M.quotHom J').mapH1 x := by
    induction x using Submodule.Quotient.induction_on with | H z => rfl
  rw [this, H1QuotEquiv_mapH1, H1QuotEquiv_mapH1]
  rfl

variable (I : Ideal A)

/-- The compatible systems of classes in `H¹(M / Iⁿ M)`. -/
def H1System : Submodule A (∀ n : ℕ, (M.quot (I ^ n)).H1) where
  carrier := {f | ∀ (m n : ℕ) (h : m ≤ n),
    (M.quotMap (Ideal.pow_le_pow_right h)).mapH1 (f n) = f m}
  add_mem' {f g} hf hg m n h := by
    simp only [Pi.add_apply, map_add, hf m n h, hg m n h]
  zero_mem' m n h := by simp
  smul_mem' a f hf m n h := by simp only [Pi.smul_apply, map_smul, hf m n h]

/-- **The theorem on formal functions for `H¹` on `ℙ¹_A`** (Stacks, Lemma 30.20.6, Tag 087U, for
`i = 1`): `lim_n H¹(M / Iⁿ M)` is the `I`-adic completion of `H¹(M)`. On `ℙ¹` no hypothesis on `A`,
`I` or `M` is needed, since `H¹` commutes with reduction at every finite level. -/
noncomputable def formalFunctionsH1 : AdicCompletion I M.H1 ≃ₗ[A] M.H1System I where
  toFun x := ⟨fun n ↦ (M.H1QuotEquiv (I ^ n)).symm (x.val n), fun m n h ↦ by
    apply (M.H1QuotEquiv (I ^ m)).injective
    rw [H1QuotEquiv_quotMap, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact x.property h⟩
  invFun f := ⟨fun n ↦ M.H1QuotEquiv (I ^ n) (f.1 n), fun {m n} h ↦ by
    simp only
    rw [← f.2 m n h, H1QuotEquiv_quotMap]⟩
  map_add' x y := by ext n; simp [AdicCompletion.val_add_apply]
  map_smul' a x := by ext n; simp [AdicCompletion.val_smul_apply]
  left_inv x := by ext n; simp
  right_inv f := by ext n; simp

end ChartModule

end ProjectiveLine
