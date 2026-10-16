/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ProjectiveLineTwist
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Tactic.Group

/-!
# Quasi-coherent modules on `ℙ¹_A` in terms of the two charts

A quasi-coherent module `F` on `ℙ¹_A`, covered by `U₀ = Spec A[X]` and `U₁ = Spec A[Y]` with
`U₀ ∩ U₁ = Spec A[T, T⁻¹]` (`X ↦ T`, `Y ↦ T⁻¹`), is determined by `M₀ = Γ(U₀, F)`,
`M₁ = Γ(U₁, F)`, `M₀₁ = Γ(U₀ ∩ U₁, F)` and the two restriction maps, which are localizations:
`M₀₁ = (M₀)_X = (M₁)_Y`. `ProjectiveLine.ChartModule A` records exactly this, with all
three modules as `A`-modules, the actions of `X`, `Y`, `T` as `A`-linear maps, and the
localization property spelled out.

Its Čech complex for the covering `(U₀, U₁)` is `M₀ × M₁ → M₀₁`, `(s, t) ↦ s| - t|`, whose
cohomology `ChartModule.H0`, `ChartModule.H1` (as `A`-modules, via `FormalSchemes.TwoCech`) is
the cohomology of `F` (Stacks, Lemma 30.2.6, Tag 01XD). The Serre twist `M(n)` replaces the
second restriction by `Tⁿ ∘ r₁` (`ChartModule.twist`), and `ChartModule.O A d` is `𝒪(d)`, whose
cohomology is computed in `FormalSchemes.ProjectiveLineTwist`.
-/

universe u

open Polynomial LaurentPolynomial

namespace ProjectiveLine

/-- **A quasi-coherent module on `ℙ¹_A`, by its two charts.** `M₀`, `M₁`, `M₀₁` are the sections
over `Spec A[X]`, `Spec A[Y]` and `Spec A[T, T⁻¹]`, with `x₀ = X·`, `x₁ = Y·` and `t = T·`;
`r₀`, `r₁` are the restriction maps (`X ↦ T`, `Y ↦ T⁻¹`), and `M₀₁` is the localization of
`M₀` at `X` and of `M₁` at `Y`. -/
structure ChartModule (A : Type u) [CommRing A] where
  /-- sections over `Spec A[X]` -/
  M0 : ModuleCat.{u} A
  /-- sections over `Spec A[Y]` -/
  M1 : ModuleCat.{u} A
  /-- sections over `Spec A[T, T⁻¹]` -/
  M01 : ModuleCat.{u} A
  /-- multiplication by `X` -/
  x0 : M0 →ₗ[A] M0
  /-- multiplication by `Y` -/
  x1 : M1 →ₗ[A] M1
  /-- multiplication by `T` -/
  t : M01 ≃ₗ[A] M01
  /-- restriction from `Spec A[X]` -/
  r0 : M0 →ₗ[A] M01
  /-- restriction from `Spec A[Y]` -/
  r1 : M1 →ₗ[A] M01
  r0_x0 : ∀ m, r0 (x0 m) = t (r0 m)
  r1_x1 : ∀ m, r1 (x1 m) = t.symm (r1 m)
  exists_r0 : ∀ z, ∃ (m : M0) (k : ℕ), (t ^ k) z = r0 m
  ker_r0 : ∀ m, r0 m = 0 → ∃ k : ℕ, (x0 ^ k) m = 0
  exists_r1 : ∀ z, ∃ (m : M1) (k : ℕ), (t.symm ^ k) z = r1 m
  ker_r1 : ∀ m, r1 m = 0 → ∃ k : ℕ, (x1 ^ k) m = 0

namespace ChartModule

variable {A : Type u} [CommRing A] (M : ChartModule A)

/-- Čech `H⁰` of the standard covering. -/
abbrev H0 : Submodule A (M.M0 × M.M1) := TwoCech.H0 M.r0 M.r1

/-- Čech `H¹` of the standard covering. -/
abbrev H1 : Type u := TwoCech.H1 M.r0 M.r1

lemma t_zpow_r1_x1 (n : ℤ) (m : M.M1) :
    (M.t ^ n) (M.r1 (M.x1 m)) = M.t.symm ((M.t ^ n) (M.r1 m)) := by
  rw [M.r1_x1]
  change (M.t ^ n * M.t⁻¹) _ = (M.t⁻¹ * M.t ^ n) _
  rw [← zpow_neg_one, ← zpow_add, ← zpow_add, add_comm]

/-- **The Serre twist** `M(n)`: the second restriction map is multiplied by `Tⁿ`. -/
def twist (n : ℤ) : ChartModule A where
  M0 := M.M0
  M1 := M.M1
  M01 := M.M01
  x0 := M.x0
  x1 := M.x1
  t := M.t
  r0 := M.r0
  r1 := (M.t ^ n).toLinearMap ∘ₗ M.r1
  r0_x0 := M.r0_x0
  r1_x1 m := M.t_zpow_r1_x1 n m
  exists_r0 := M.exists_r0
  ker_r0 := M.ker_r0
  exists_r1 z := by
    obtain ⟨m, k, h⟩ := M.exists_r1 ((M.t ^ (-n)) z)
    refine ⟨m, k, ?_⟩
    have : (M.t.symm ^ k) z = (M.t ^ n) ((M.t.symm ^ k) ((M.t ^ (-n)) z)) := by
      change (M.t⁻¹ ^ k) z = (M.t ^ n * (M.t⁻¹ ^ k * M.t ^ (-n))) z
      rw [← zpow_natCast]
      have e : M.t ^ n * (M.t⁻¹ ^ (k : ℤ) * M.t ^ (-n)) = M.t⁻¹ ^ (k : ℤ) := by group
      rw [e]
    rw [this, h]
    rfl
  ker_r1 m h := M.ker_r1 m (by
    have : (M.t ^ n) (M.r1 m) = 0 := h
    simpa using congrArg (M.t ^ (-n)) this |>.trans (map_zero _) |> fun h' ↦ by
      rwa [← LinearEquiv.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero] at h')

/-! ### Powers of `T` -/

lemma t_pow_r0 (j : ℕ) (m : M.M0) : (M.t ^ j) (M.r0 m) = M.r0 ((M.x0 ^ j) m) := by
  induction j generalizing m with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, LinearEquiv.mul_apply, ← M.r0_x0, ih, pow_succ, Module.End.mul_apply]

lemma t_zpow_neg_r1 (j : ℕ) (m : M.M1) :
    (M.t ^ (-(j : ℤ))) (M.r1 m) = M.r1 ((M.x1 ^ j) m) := by
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  induction j generalizing m with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, LinearEquiv.mul_apply]
    change (M.t⁻¹ ^ j) (M.t.symm (M.r1 m)) = _
    rw [← M.r1_x1, ih, pow_succ, Module.End.mul_apply]

lemma t_zpow_apply_zpow (a b : ℤ) (z : M.M01) : (M.t ^ a) ((M.t ^ b) z) = (M.t ^ (a + b)) z := by
  rw [zpow_add, LinearEquiv.mul_apply]

/-! ### Serre's vanishing theorem -/

/-- The image of the twisted Čech differential of `M(n)`. -/
abbrev imD (n : ℤ) : Submodule A M.M01 := LinearMap.range (TwoCech.d (M.twist n).r0 (M.twist n).r1)

lemma r0_mem_imD (n : ℤ) (m : M.M0) : M.r0 m ∈ M.imD n :=
  ⟨(m, 0), by
    rw [TwoCech.d_apply]
    change M.r0 m - (M.t ^ n) (M.r1 0) = M.r0 m
    simp⟩

lemma t_zpow_r1_mem_imD (n : ℤ) (m : M.M1) : (M.t ^ n) (M.r1 m) ∈ M.imD n :=
  ⟨(0, -m), by
    rw [TwoCech.d_apply]
    change M.r0 0 - (M.t ^ n) (M.r1 (-m)) = (M.t ^ n) (M.r1 m)
    simp⟩

/-- **Generation of the overlap.** If `S` generates `M₀` over `A[X]`, a submodule `N` of `M₀₁`
containing the image of `r₀` and all `T⁻ʲ g|` (`g ∈ S`, `j > 0`) is everything: every section over
`U₀ ∩ U₁` is `T⁻ᵏ m|`. -/
lemma forall_mem_of_span (S : Finset (Module.AEval' M.x0))
    (hS : Submodule.span A[X] (S : Set (Module.AEval' M.x0)) = ⊤) (N : Submodule A M.M01)
    (h0 : ∀ m, M.r0 m ∈ N)
    (hneg : ∀ g ∈ S, ∀ j : ℕ, 0 < j →
      (M.t ^ (-(j : ℤ))) (M.r0 ((Module.AEval'.of M.x0).symm g)) ∈ N) :
    ∀ z, z ∈ N := by
  let P : M.M0 → Prop := fun m ↦ ∀ e : ℤ, (M.t ^ e) (M.r0 m) ∈ N
  have P_add : ∀ m m', P m → P m' → P (m + m') := fun m m' h h' e ↦ by
    rw [map_add, map_add]; exact add_mem (h e) (h' e)
  have P_zero : P 0 := fun e ↦ by rw [map_zero, map_zero]; exact zero_mem _
  have P_smul : ∀ (a : A) m, P m → P (a • m) := fun a m h e ↦ by
    rw [map_smul, map_smul]; exact Submodule.smul_mem _ a (h e)
  have P_x0 : ∀ m, P m → P (M.x0 m) := fun m h e ↦ by
    rw [M.r0_x0, ← LinearEquiv.mul_apply, ← zpow_add_one]
    exact h (e + 1)
  have P_gen : ∀ g ∈ S, P ((Module.AEval'.of M.x0).symm g) := by
    intro g hg' e
    rcases le_or_gt 0 e with he | he
    · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le he
      rw [zpow_natCast, t_pow_r0]
      exact h0 _
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, e = -(j : ℤ) := ⟨(-e).toNat, by omega⟩
      exact hneg g hg' j (by omega)
  have P_all : ∀ m, P m := by
    intro m
    have hm : Module.AEval'.of M.x0 m ∈ Submodule.span A[X] (S : Set (Module.AEval' M.x0)) := by
      rw [hS]; trivial
    suffices ∀ y ∈ Submodule.span A[X] (S : Set (Module.AEval' M.x0)),
        P ((Module.AEval'.of M.x0).symm y) by simpa using this _ hm
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact P_gen y hy
    | zero => simpa using P_zero
    | add y y' _ _ h h' => simpa using P_add _ _ h h'
    | smul p y _ h =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq => rw [add_smul, map_add]; exact P_add _ _ hp hq
      | monomial j a =>
        rw [← C_mul_X_pow_eq_monomial, mul_smul,
          show ∀ y : Module.AEval' M.x0, (C a : A[X]) • y = a • y from
            fun y ↦ algebraMap_smul A[X] a y]
        obtain ⟨y', rfl⟩ := (Module.AEval'.of M.x0).surjective y
        rw [Module.AEval'.X_pow_smul_of]
        simp only [map_smul, LinearEquiv.symm_apply_apply] at h ⊢
        refine P_smul a _ ?_
        clear * - h P_x0
        induction j with
        | zero => simpa using h
        | succ j ih =>
          rw [pow_succ', mul_smul]
          exact P_x0 _ ih
  intro z
  obtain ⟨m, k, hk⟩ := M.exists_r0 z
  have : z = (M.t ^ (-(k : ℤ))) (M.r0 m) := by
    rw [← hk, ← zpow_natCast, t_zpow_apply_zpow, neg_add_cancel, zpow_zero]
    rfl
  rw [this]
  exact P_all m _

lemma r0_eq_t_zpow_r1 {g : M.M0} {m : M.M1} {k : ℕ} (h : (M.t.symm ^ k) (M.r0 g) = M.r1 m) :
    M.r0 g = (M.t ^ (k : ℤ)) (M.r1 m) := by
  rw [← h]
  change _ = (M.t ^ (k : ℤ) * M.t.symm ^ k) _
  rw [show M.t.symm = M.t⁻¹ from rfl, inv_pow, zpow_natCast, mul_inv_cancel]
  rfl

/-- **Serre's vanishing theorem on `ℙ¹`** (Stacks, Lemma 30.14.1(4), Tag 01YS, for `ℙ¹_A`): if
`M₀` is a finitely generated `A[X]`-module, then `H¹(M(n)) = 0` for all `n ≫ 0`. -/
theorem exists_subsingleton_H1_twist [Module.Finite A[X] (Module.AEval' M.x0)] :
    ∃ n₀ : ℕ, ∀ n : ℤ, n₀ ≤ n → Subsingleton (M.twist n).H1 := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A[X]) (M := Module.AEval' M.x0)
  choose mg kg hg using fun g : Module.AEval' M.x0 ↦
    M.exists_r1 (M.r0 ((Module.AEval'.of M.x0).symm g))
  refine ⟨S.sup kg, fun n hn ↦ ?_⟩
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro z _
  refine M.forall_mem_of_span S hS _ (M.r0_mem_imD n) (fun g hg' j _ ↦ ?_) z
  have hk : (kg g : ℤ) ≤ n := le_trans (by exact_mod_cast Finset.le_sup hg') hn
  obtain ⟨i, hi⟩ : ∃ i : ℕ, -(j : ℤ) + kg g = n - i := ⟨(n + j - kg g).toNat, by omega⟩
  rw [M.r0_eq_t_zpow_r1 (hg g), t_zpow_apply_zpow, hi, sub_eq_add_neg, zpow_add,
    LinearEquiv.mul_apply, t_zpow_neg_r1]
  exact M.t_zpow_r1_mem_imD n _

/-- **Finiteness of `H¹`** (cf. Stacks, Lemma 30.19.2, Tag 02O6, here for `ℙ¹_A` and without any
Noetherian hypothesis): if `M₀` is a finitely generated `A[X]`-module, then `H¹(M(n))` is a
finitely generated `A`-module for every `n`. -/
theorem finite_H1_twist [Module.Finite A[X] (Module.AEval' M.x0)] (n : ℤ) :
    Module.Finite A (M.twist n).H1 := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A[X]) (M := Module.AEval' M.x0)
  choose mg kg hg using fun g : Module.AEval' M.x0 ↦
    M.exists_r1 (M.r0 ((Module.AEval'.of M.x0).symm g))
  let B := S.sup kg + n.natAbs + 1
  let G : Finset M.M01 := (S ×ˢ Finset.range B).image
    fun p ↦ (M.t ^ (-(p.2 : ℤ))) (M.r0 ((Module.AEval'.of M.x0).symm p.1))
  suffices Module.Finite A (M.M01 ⧸ M.imD n) from this
  refine ⟨⟨G.image (M.imD n).mkQ, ?_⟩⟩
  rw [Finset.coe_image, ← Submodule.map_span, eq_top_iff]
  rintro w -
  obtain ⟨z, rfl⟩ := (M.imD n).mkQ_surjective w
  have hz : z ∈ M.imD n ⊔ Submodule.span A (G : Set M.M01) := by
    refine M.forall_mem_of_span S hS _ (fun m ↦ Submodule.mem_sup_left (M.r0_mem_imD n m))
      (fun g hg' j hj ↦ ?_) z
    by_cases hjB : j < B
    · exact Submodule.mem_sup_right (Submodule.subset_span
        (Finset.mem_image.2 ⟨(g, j), Finset.mem_product.2 ⟨hg', Finset.mem_range.2 hjB⟩, rfl⟩))
    · refine Submodule.mem_sup_left ?_
      have hk : (kg g : ℤ) ≤ S.sup kg := by exact_mod_cast Finset.le_sup hg'
      obtain ⟨i, hi⟩ : ∃ i : ℕ, -(j : ℤ) + kg g = n - i := ⟨(n + j - kg g).toNat, by omega⟩
      rw [M.r0_eq_t_zpow_r1 (hg g), t_zpow_apply_zpow, hi, sub_eq_add_neg, zpow_add,
        LinearEquiv.mul_apply, t_zpow_neg_r1]
      exact M.t_zpow_r1_mem_imD n _
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
  refine ⟨b, hb, ?_⟩
  have h0 : (M.imD n).mkQ a = 0 := (Submodule.Quotient.mk_eq_zero _).2 ha
  rw [map_add, h0, zero_add]

/-! ### Morphisms -/

/-- A morphism of chart modules: compatible linear maps on the three charts. -/
structure Hom (M N : ChartModule A) where
  /-- on `Spec A[X]` -/
  f0 : M.M0 →ₗ[A] N.M0
  /-- on `Spec A[Y]` -/
  f1 : M.M1 →ₗ[A] N.M1
  /-- on `Spec A[T, T⁻¹]` -/
  f01 : M.M01 →ₗ[A] N.M01
  comm_x0 : ∀ m, f0 (M.x0 m) = N.x0 (f0 m)
  comm_x1 : ∀ m, f1 (M.x1 m) = N.x1 (f1 m)
  comm_t : ∀ z, f01 (M.t z) = N.t (f01 z)
  comm_r0 : ∀ m, f01 (M.r0 m) = N.r0 (f0 m)
  comm_r1 : ∀ m, f01 (M.r1 m) = N.r1 (f1 m)

variable {M} {N : ChartModule A}

lemma Hom.comm_r0' (φ : Hom M N) : N.r0 ∘ₗ φ.f0 = φ.f01 ∘ₗ M.r0 :=
  LinearMap.ext fun m ↦ (φ.comm_r0 m).symm

lemma Hom.comm_r1' (φ : Hom M N) : N.r1 ∘ₗ φ.f1 = φ.f01 ∘ₗ M.r1 :=
  LinearMap.ext fun m ↦ (φ.comm_r1 m).symm

/-- The map on `H⁰` induced by a morphism. -/
def Hom.mapH0 (φ : Hom M N) : M.H0 →ₗ[A] N.H0 :=
  TwoCech.mapH0 φ.f0 φ.f1 φ.f01 φ.comm_r0' φ.comm_r1'

/-- The map on `H¹` induced by a morphism. -/
def Hom.mapH1 (φ : Hom M N) : M.H1 →ₗ[A] N.H1 :=
  TwoCech.mapH1 φ.f0 φ.f1 φ.f01 φ.comm_r0' φ.comm_r1'

lemma Hom.comm_t_zpow (φ : Hom M N) (n : ℤ) (z : M.M01) :
    φ.f01 ((M.t ^ n) z) = (N.t ^ n) (φ.f01 z) := by
  have h1 : ∀ k : ℕ, ∀ z, φ.f01 ((M.t ^ k) z) = (N.t ^ k) (φ.f01 z) := by
    intro k
    induction k with
    | zero => intro z; rfl
    | succ k ih =>
      intro z
      rw [pow_succ, pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih, φ.comm_t]
  have h2 : ∀ z, φ.f01 (M.t.symm z) = N.t.symm (φ.f01 z) := fun z ↦ by
    apply N.t.injective
    rw [← φ.comm_t]
    simp
  have h3 : ∀ k : ℕ, ∀ z, φ.f01 ((M.t⁻¹ ^ k) z) = (N.t⁻¹ ^ k) (φ.f01 z) := by
    intro k
    induction k with
    | zero => intro z; rfl
    | succ k ih =>
      intro z
      rw [pow_succ, pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih]
      exact congrArg _ (h2 z)
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simpa using h1 k z
  · simpa [zpow_neg, ← inv_pow] using h3 k z

/-- A morphism `M ⟶ N` is also a morphism `M(n) ⟶ N(n)`. -/
def Hom.twist (φ : Hom M N) (n : ℤ) : Hom (M.twist n) (N.twist n) where
  f0 := φ.f0
  f1 := φ.f1
  f01 := φ.f01
  comm_x0 := φ.comm_x0
  comm_x1 := φ.comm_x1
  comm_t := φ.comm_t
  comm_r0 := φ.comm_r0
  comm_r1 m := by
    change φ.f01 ((M.t ^ n) (M.r1 m)) = (N.t ^ n) (N.r1 (φ.f1 m))
    rw [φ.comm_t_zpow, φ.comm_r1]

end ChartModule

/-! ### The twisting sheaves -/

variable (A : Type u) [CommRing A]

/-- Multiplication by `T` on `A[T, T⁻¹]`. -/
noncomputable def mulT : A[T;T⁻¹] ≃ₗ[A] A[T;T⁻¹] where
  toLinearMap := LinearMap.mulLeft A (T 1)
  invFun f := T (-1) * f
  left_inv f := by
    change T (-1) * (T 1 * f) = f
    rw [← mul_assoc, ← T_add]; simp
  right_inv f := by
    change T 1 * (T (-1) * f) = f
    rw [← mul_assoc, ← T_add]; simp

lemma mulT_pow_apply (k : ℕ) (f : A[T;T⁻¹]) : (mulT A ^ k) f = T k * f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih]
    change T 1 * (T k * f) = _
    rw [← mul_assoc, ← T_add]
    push_cast
    rw [add_comm]

lemma mulT_symm_pow_apply (k : ℕ) (f : A[T;T⁻¹]) : ((mulT A).symm ^ k) f = T (-k) * f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih]
    change T (-1) * (T (-k) * f) = _
    rw [← mul_assoc, ← T_add]
    push_cast
    congr 2
    ring

lemma mulT_zpow_apply (n : ℤ) (f : A[T;T⁻¹]) : (mulT A ^ n) f = T n * f := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simpa using mulT_pow_apply A k f
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact mulT_symm_pow_apply A k f

lemma invert_invert' (f : A[T;T⁻¹]) : invert (invert f) = f := by
  ext n
  simp

/-- **Serre's twisting sheaf `𝒪(d)` on `ℙ¹_A`**, by its charts: `A[X]`, `A[Y]`, `A[T, T⁻¹]`,
restrictions `p ↦ p(T)` and `q ↦ Tᵈ q(T⁻¹)`. -/
noncomputable def ChartModule.O (d : ℤ) : ChartModule A where
  M0 := ModuleCat.of A A[X]
  M1 := ModuleCat.of A A[X]
  M01 := ModuleCat.of A A[T;T⁻¹]
  x0 := LinearMap.mulLeft A X
  x1 := LinearMap.mulLeft A X
  t := mulT A
  r0 := res0 A
  r1 := resInf A d
  r0_x0 m := by
    change toLaurent (X * m) = T 1 * toLaurent m
    rw [map_mul, Polynomial.toLaurent_X]
  r1_x1 m := by
    change T d * invert (toLaurent (X * m)) = T (-1) * (T d * invert (toLaurent m))
    rw [map_mul, map_mul, Polynomial.toLaurent_X, invert_T]
    ring
  exists_r0 z := by
    obtain ⟨n, f', h⟩ := exists_T_pow z
    exact ⟨f', n, by rw [mulT_pow_apply, mul_comm]; exact h.symm⟩
  ker_r0 m h := ⟨0, by
    have : toLaurent m = 0 := h
    simpa using Polynomial.toLaurent_injective (this.trans (map_zero _).symm)⟩
  exists_r1 z := by
    obtain ⟨n, f', h⟩ := exists_T_pow (invert (T (-d) * z))
    refine ⟨f', n, ?_⟩
    rw [mulT_symm_pow_apply]
    change _ = T d * invert (toLaurent f')
    have hinv : invert (invert (T (-d) * z)) = T (-d) * z := invert_invert' A _
    rw [h, map_mul, invert_T, hinv, show T d * (T (-d) * z * T (-(n : ℤ))) =
      (T d * T (-d)) * T (-(n : ℤ)) * z by ring, ← T_add, add_neg_cancel, T_zero, one_mul]
  ker_r1 m h := ⟨0, by
    have : T d * invert (toLaurent m) = 0 := h
    have h2 : invert (toLaurent m) = 0 := by
      rw [← one_mul (invert (toLaurent m)), ← T_zero, ← neg_add_cancel d, T_add, mul_assoc, this,
        mul_zero]
    have h3 : toLaurent m = 0 := by
      simpa [invert_invert'] using congrArg invert h2
    simpa using Polynomial.toLaurent_injective (h3.trans (map_zero _).symm)⟩

end ProjectiveLine
