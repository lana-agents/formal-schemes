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

Main results (Serre's theorems for `ℙ¹_A`, Stacks, Lemma 30.14.1, Tag 01YS), for `M` with `M₀`
and `M₁` finitely generated over `A[X]` resp. `A[Y]` (i.e. `F` of finite type):
* `ChartModule.exists_subsingleton_H1_twist`: `H¹(M(n)) = 0` for `n ≫ 0`;
* `ChartModule.finite_H1_twist`, `ChartModule.finite_H1`: `H¹(M(n))` is a finite `A`-module
  (no Noetherian hypothesis is needed for `H¹` on `ℙ¹`);
* `ChartModule.exists_sectionsHom_surjective`: for `n ≫ 0` finitely many sections of `M(n)` give
  a morphism `𝒪(-n)^ι → M` surjective on all charts (`ChartModule.sectionsHom`);
* `ChartModule.finite_H0`: over a Noetherian ring, `H⁰(M)` is a finite `A`-module, by embedding it
  into `H¹` of the kernel (`ChartModule.Hom.ker`) of such a morphism with `n ≥ 1`.
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

lemma t_symm_pow_r1 (j : ℕ) (m : M.M1) :
    (M.t.symm ^ j) (M.r1 m) = M.r1 ((M.x1 ^ j) m) := by
  rw [← t_zpow_neg_r1, zpow_neg, zpow_natCast, ← inv_pow]
  rfl

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

/-! ### Laurent polynomials acting on the overlap -/

/-- The action of `A[T, T⁻¹]` on `M₀₁`, `T ↦ t`. -/
noncomputable def lev : A[T;T⁻¹] →ₐ[A] Module.End A M.M01 :=
  AddMonoidAlgebra.lift A (Module.End A M.M01) ℤ
    ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp (zpowersHom _ M.t))

lemma lev_C_mul_T (a : A) (n : ℤ) (z : M.M01) :
    M.lev (LaurentPolynomial.C a * T n) z = a • (M.t ^ n) z := by
  rw [← single_eq_C_mul_T, lev, AddMonoidAlgebra.lift_single]
  rfl

lemma lev_T (n : ℤ) (z : M.M01) : M.lev (T n) z = (M.t ^ n) z := by
  simpa using M.lev_C_mul_T 1 n z

lemma lev_toLaurent_r0 (p : A[X]) (m : M.M0) :
    M.lev (toLaurent p) (M.r0 m) = M.r0 (Polynomial.aeval M.x0 p m) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    rw [Polynomial.toLaurent_C_mul_T, M.lev_C_mul_T, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, zpow_natCast, t_pow_r0]

lemma lev_invert_r1 (q : A[X]) (m : M.M1) :
    M.lev (invert (toLaurent q)) (M.r1 m) = M.r1 (Polynomial.aeval M.x1 q m) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    rw [Polynomial.toLaurent_C_mul_T, map_mul, invert_C, invert_T, M.lev_C_mul_T,
      Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul,
      t_zpow_neg_r1]

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
noncomputable abbrev ChartModule.O (d : ℤ) : ChartModule A where
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

namespace ChartModule

variable {A}

/-! ### Finite direct sums -/

section Pi

variable {ι : Type u}

lemma piCongrRight_pow_apply {P : ι → Type u} [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    (e : ∀ i, P i ≃ₗ[A] P i) (k : ℕ) (z : ∀ i, P i) (i : ι) :
    ((LinearEquiv.piCongrRight e ^ k) z) i = (e i ^ k) (z i) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, LinearEquiv.mul_apply]
    rfl

lemma piCongrRight_symm_pow_apply {P : ι → Type u} [∀ i, AddCommGroup (P i)]
    [∀ i, Module A (P i)] (e : ∀ i, P i ≃ₗ[A] P i) (k : ℕ) (z : ∀ i, P i) (i : ι) :
    (((LinearEquiv.piCongrRight e).symm ^ k) z) i = ((e i).symm ^ k) (z i) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, LinearEquiv.mul_apply]
    rfl

lemma pow_add_apply {P : Type u} [AddCommGroup P] [Module A P] (e : P ≃ₗ[A] P) (a b : ℕ)
    (z : P) : (e ^ (a + b)) z = (e ^ a) ((e ^ b) z) := by
  rw [pow_add, LinearEquiv.mul_apply]

lemma end_pow_add_apply {P : Type u} [AddCommGroup P] [Module A P] (e : P →ₗ[A] P) (a b : ℕ)
    (z : P) : (e ^ (a + b)) z = (e ^ a) ((e ^ b) z) := by
  rw [pow_add, Module.End.mul_apply]

lemma pi_pow_apply {P : ι → Type u} [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    (e : ∀ i, P i →ₗ[A] P i) (k : ℕ) (z : ∀ i, P i) (i : ι) :
    ((LinearMap.pi fun i ↦ e i ∘ₗ LinearMap.proj i) ^ k) z i = (e i ^ k) (z i) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    rfl

variable [Fintype ι] (N : ι → ChartModule A)

/-- The direct sum of finitely many chart modules. -/
noncomputable abbrev pi : ChartModule A where
  M0 := ModuleCat.of A (∀ i, (N i).M0)
  M1 := ModuleCat.of A (∀ i, (N i).M1)
  M01 := ModuleCat.of A (∀ i, (N i).M01)
  x0 := LinearMap.pi fun i ↦ (N i).x0 ∘ₗ LinearMap.proj i
  x1 := LinearMap.pi fun i ↦ (N i).x1 ∘ₗ LinearMap.proj i
  t := LinearEquiv.piCongrRight fun i ↦ (N i).t
  r0 := LinearMap.pi fun i ↦ (N i).r0 ∘ₗ LinearMap.proj i
  r1 := LinearMap.pi fun i ↦ (N i).r1 ∘ₗ LinearMap.proj i
  r0_x0 m := funext fun i ↦ (N i).r0_x0 (m i)
  r1_x1 m := funext fun i ↦ (N i).r1_x1 (m i)
  exists_r0 z := by
    choose m k h using fun i ↦ (N i).exists_r0 (z i)
    let K := Finset.univ.sup k
    have hk : ∀ i, k i ≤ K := fun i ↦ Finset.le_sup (Finset.mem_univ i)
    refine ⟨fun i ↦ ((N i).x0 ^ (K - k i)) (m i), K, funext fun i ↦ ?_⟩
    change ((LinearEquiv.piCongrRight fun i ↦ (N i).t) ^ K) z i = (N i).r0 _
    rw [piCongrRight_pow_apply, ← Nat.sub_add_cancel (hk i), pow_add_apply, h,
      Nat.sub_add_cancel (hk i), t_pow_r0]
    rfl
  ker_r0 m hm := by
    choose k h using fun i ↦ (N i).ker_r0 (m i) (congrFun hm i)
    let K := Finset.univ.sup k
    have hk : ∀ i, k i ≤ K := fun i ↦ Finset.le_sup (Finset.mem_univ i)
    refine ⟨K, funext fun i ↦ ?_⟩
    change ((LinearMap.pi fun i ↦ (N i).x0 ∘ₗ LinearMap.proj i) ^ K) m i = 0
    rw [pi_pow_apply, ← Nat.sub_add_cancel (hk i), end_pow_add_apply, h, map_zero]
  exists_r1 z := by
    choose m k h using fun i ↦ (N i).exists_r1 (z i)
    let K := Finset.univ.sup k
    have hk : ∀ i, k i ≤ K := fun i ↦ Finset.le_sup (Finset.mem_univ i)
    refine ⟨fun i ↦ ((N i).x1 ^ (K - k i)) (m i), K, funext fun i ↦ ?_⟩
    change ((LinearEquiv.piCongrRight fun i ↦ (N i).t).symm ^ K) z i = (N i).r1 _
    rw [piCongrRight_symm_pow_apply, ← Nat.sub_add_cancel (hk i), pow_add_apply, h,
      Nat.sub_add_cancel (hk i), t_symm_pow_r1]
    rfl
  ker_r1 m hm := by
    choose k h using fun i ↦ (N i).ker_r1 (m i) (congrFun hm i)
    let K := Finset.univ.sup k
    have hk : ∀ i, k i ≤ K := fun i ↦ Finset.le_sup (Finset.mem_univ i)
    refine ⟨K, funext fun i ↦ ?_⟩
    change ((LinearMap.pi fun i ↦ (N i).x1 ∘ₗ LinearMap.proj i) ^ K) m i = 0
    rw [pi_pow_apply, ← Nat.sub_add_cancel (hk i), end_pow_add_apply, h, map_zero]

end Pi

/-! ### Maps from sums of twisting sheaves -/

section Sections

variable (ι : Type u) [Fintype ι] (n : ℕ)

/-- `𝒪(-n)^ι`. -/
noncomputable abbrev free : ChartModule A := pi fun _ : ι ↦ O A (-(n : ℤ))

/-- `H⁰(ℙ¹_A, 𝒪(-n)^ι) = 0` for `n ≥ 1`. -/
lemma H0_free_eq_bot (hn : 1 ≤ n) : (free (A := A) ι n).H0 = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨s, m⟩ h
  have hi : ∀ i, s i = 0 ∧ m i = 0 := fun i ↦ by
    have h' : res0 A (s i) = resInf A (-(n : ℤ)) (m i) := congrFun (TwoCech.mem_H0.1 h) i
    have hm : (show A[X] × A[X] from (s i, m i)) ∈ ProjectiveLine.H0 A (-(n : ℤ)) :=
      TwoCech.mem_H0.2 h'
    rw [H0_eq_bot (by omega), Submodule.mem_bot] at hm
    exact ⟨congrArg Prod.fst hm, congrArg Prod.snd hm⟩
  exact (Submodule.mem_bot _).2 (Prod.ext (funext fun i ↦ (hi i).1) (funext fun i ↦ (hi i).2))

variable {ι n} (M : ChartModule A) (σ : ι → M.M0 × M.M1)
  (hσ : ∀ i, M.r0 (σ i).1 = (M.t ^ (n : ℤ)) (M.r1 (σ i).2))

lemma free_t_apply (f : (free (A := A) ι n).M01) (i : ι) :
    ((free (A := A) ι n).t f) i = T 1 * f i := rfl

lemma free_x0_apply (p : (free (A := A) ι n).M0) (i : ι) :
    ((free (A := A) ι n).x0 p) i = X * p i := rfl

lemma free_x1_apply (p : (free (A := A) ι n).M1) (i : ι) :
    ((free (A := A) ι n).x1 p) i = X * p i := rfl

lemma free_r0_apply (p : (free (A := A) ι n).M0) (i : ι) :
    ((free (A := A) ι n).r0 p) i = toLaurent (p i) := rfl

lemma free_r1_apply (p : (free (A := A) ι n).M1) (i : ι) :
    ((free (A := A) ι n).r1 p) i = T (-(n : ℤ)) * invert (toLaurent (p i)) := rfl

/-- On `Spec A[X]`: `p ↦ ∑ pᵢ(X) sᵢ`. -/
noncomputable def sectionsF0 : (free (A := A) ι n).M0 →ₗ[A] M.M0 where
  toFun p := ∑ i, Polynomial.aeval M.x0 (p i) (σ i).1
  map_add' p q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦
      congrArg (fun φ : Module.End A M.M0 ↦ φ (σ i).1) (map_add (Polynomial.aeval M.x0) _ _)
  map_smul' a p := by
    rw [RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦
      congrArg (fun φ : Module.End A M.M0 ↦ φ (σ i).1) (map_smul (Polynomial.aeval M.x0) a _)

lemma sectionsF0_apply (p : (free (A := A) ι n).M0) :
    sectionsF0 M σ p = ∑ i, Polynomial.aeval M.x0 (p i) (σ i).1 := rfl

/-- On `Spec A[Y]`: `q ↦ ∑ qᵢ(Y) tᵢ`. -/
noncomputable def sectionsF1 : (free (A := A) ι n).M1 →ₗ[A] M.M1 where
  toFun q := ∑ i, Polynomial.aeval M.x1 (q i) (σ i).2
  map_add' p q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦
      congrArg (fun φ : Module.End A M.M1 ↦ φ (σ i).2) (map_add (Polynomial.aeval M.x1) _ _)
  map_smul' a p := by
    rw [RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦
      congrArg (fun φ : Module.End A M.M1 ↦ φ (σ i).2) (map_smul (Polynomial.aeval M.x1) a _)

lemma sectionsF1_apply (q : (free (A := A) ι n).M1) :
    sectionsF1 M σ q = ∑ i, Polynomial.aeval M.x1 (q i) (σ i).2 := rfl

/-- On `Spec A[T, T⁻¹]`: `f ↦ ∑ fᵢ(T) sᵢ|`. -/
noncomputable def sectionsF01 : (free (A := A) ι n).M01 →ₗ[A] M.M01 where
  toFun f := ∑ i, M.lev (f i) (M.r0 (σ i).1)
  map_add' p q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦
      congrArg (fun φ : Module.End A M.M01 ↦ φ (M.r0 (σ i).1)) (map_add M.lev _ _)
  map_smul' a p := by
    rw [RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦
      congrArg (fun φ : Module.End A M.M01 ↦ φ (M.r0 (σ i).1)) (map_smul M.lev a _)

lemma sectionsF01_apply (f : (free (A := A) ι n).M01) :
    sectionsF01 M σ f = ∑ i, M.lev (f i) (M.r0 (σ i).1) := rfl

/-- The morphism `𝒪(-n)^ι → M` given by sections `σ i` of `M(n)`. -/
noncomputable def sectionsHom : Hom (free (A := A) ι n) M where
  f0 := sectionsF0 M σ
  f1 := sectionsF1 M σ
  f01 := sectionsF01 M σ
  comm_x0 p := by
    rw [sectionsF0_apply, sectionsF0_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [free_x0_apply, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
  comm_x1 p := by
    rw [sectionsF1_apply, sectionsF1_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [free_x1_apply, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
  comm_t f := by
    rw [sectionsF01_apply, sectionsF01_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [free_t_apply, map_mul, Module.End.mul_apply, lev_T, zpow_one]
  comm_r0 p := by
    rw [sectionsF01_apply, sectionsF0_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [free_r0_apply, lev_toLaurent_r0]
  comm_r1 q := by
    rw [sectionsF01_apply, sectionsF1_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [free_r1_apply, hσ i, ← lev_T, ← Module.End.mul_apply, ← map_mul,
      show T (-(n : ℤ)) * invert (toLaurent (q i)) * T (n : ℤ) = invert (toLaurent (q i)) by
        rw [mul_comm, ← mul_assoc, ← T_add, add_neg_cancel, T_zero, one_mul],
      lev_invert_r1]

end Sections

/-! ### Generation -/

/-- If `S` generates `N` as an `A[X]`-module via `φ`, an `A`-submodule of `N` stable under `φ` and
containing `S` is everything. -/
lemma eq_top_of_span_aeval {N : Type u} [AddCommGroup N] [Module A N] (φ : N →ₗ[A] N)
    (S : Set (Module.AEval' φ)) (hS : Submodule.span A[X] S = ⊤) (P : Submodule A N)
    (hφ : ∀ m ∈ P, φ m ∈ P) (hP : ∀ g ∈ S, (Module.AEval'.of φ).symm g ∈ P) : P = ⊤ := by
  rw [eq_top_iff]
  intro m _
  have hm : Module.AEval'.of φ m ∈ Submodule.span A[X] S := by rw [hS]; trivial
  suffices ∀ y ∈ Submodule.span A[X] S, (Module.AEval'.of φ).symm y ∈ P by simpa using this _ hm
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact hP y hy
  | zero => simp
  | add y y' _ _ h h' => simpa using add_mem h h'
  | smul p y _ h =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [add_smul, map_add]; exact add_mem hp hq
    | monomial j a =>
      rw [← C_mul_X_pow_eq_monomial, mul_smul,
        show ∀ y : Module.AEval' φ, (C a : A[X]) • y = a • y from
          fun y ↦ algebraMap_smul A[X] a y]
      obtain ⟨y', rfl⟩ := (Module.AEval'.of φ).surjective y
      rw [Module.AEval'.X_pow_smul_of]
      simp only [map_smul, LinearEquiv.symm_apply_apply] at h ⊢
      refine P.smul_mem a ?_
      clear * - h hφ
      induction j with
      | zero => simpa using h
      | succ j ih =>
        rw [pow_succ', mul_smul]
        exact hφ _ ih

variable {M N : ChartModule A}

/-- A morphism which is surjective on `Spec A[X]` is surjective on `Spec A[T, T⁻¹]`. -/
lemma Hom.surjective_f01 (φ : Hom M N) (h0 : Function.Surjective φ.f0) :
    Function.Surjective φ.f01 := by
  intro z
  obtain ⟨m, k, hk⟩ := N.exists_r0 z
  obtain ⟨p, rfl⟩ := h0 m
  refine ⟨(M.t ^ (-(k : ℤ))) (M.r0 p), ?_⟩
  rw [φ.comm_t_zpow, φ.comm_r0, ← hk, ← zpow_natCast, t_zpow_apply_zpow, neg_add_cancel,
    zpow_zero]
  rfl

section Sections

variable (M) {ι : Type u} [Fintype ι] {n : ℕ} (σ : ι → M.M0 × M.M1)

lemma surjective_sectionsF0 (S : Set (Module.AEval' M.x0))
    (hS : Submodule.span A[X] S = ⊤) (hσ : ∀ g ∈ S, ∃ i, (σ i).1 = (Module.AEval'.of M.x0).symm g) :
    Function.Surjective (sectionsF0 (n := n) M σ) := by
  classical
  rw [← LinearMap.range_eq_top]
  refine eq_top_of_span_aeval M.x0 S hS _ ?_ ?_
  · rintro _ ⟨p, rfl⟩
    refine ⟨(free (A := A) ι n).x0 p, ?_⟩
    rw [sectionsF0_apply, sectionsF0_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [free_x0_apply, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
  · intro g hg
    obtain ⟨i, hi⟩ := hσ g hg
    refine ⟨Pi.single i 1, ?_⟩
    rw [sectionsF0_apply, ← hi, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp

lemma surjective_sectionsF1 (S : Set (Module.AEval' M.x1))
    (hS : Submodule.span A[X] S = ⊤) (hσ : ∀ g ∈ S, ∃ i, (σ i).2 = (Module.AEval'.of M.x1).symm g) :
    Function.Surjective (sectionsF1 (n := n) M σ) := by
  classical
  rw [← LinearMap.range_eq_top]
  refine eq_top_of_span_aeval M.x1 S hS _ ?_ ?_
  · rintro _ ⟨p, rfl⟩
    refine ⟨(free (A := A) ι n).x1 p, ?_⟩
    rw [sectionsF1_apply, sectionsF1_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [free_x1_apply, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
  · intro g hg
    obtain ⟨i, hi⟩ := hσ g hg
    refine ⟨Pi.single i 1, ?_⟩
    rw [sectionsF1_apply, ← hi, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp

end Sections

/-! ### Global generation -/

variable (M) in
/-- **`M(n)` is globally generated for `n ≫ 0`** (Stacks, Lemma 30.14.1(1), Tag 01YS, for `ℙ¹_A`):
if `M₀` and `M₁` are finitely generated, then for `n ≫ 0` finitely many sections of `M(n)` give a
morphism `𝒪(-n)^ι → M` which is surjective on both charts. -/
theorem exists_sectionsHom_surjective [Module.Finite A[X] (Module.AEval' M.x0)]
    [Module.Finite A[X] (Module.AEval' M.x1)] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ (ι : Type u) (_ : Fintype ι)
      (σ : ι → M.M0 × M.M1) (_ : ∀ i, M.r0 (σ i).1 = (M.t ^ (n : ℤ)) (M.r1 (σ i).2)),
      Function.Surjective (sectionsF0 (n := n) M σ) ∧
        Function.Surjective (sectionsF1 (n := n) M σ) := by
  classical
  obtain ⟨S0, hS0⟩ := Module.Finite.fg_top (R := A[X]) (M := Module.AEval' M.x0)
  obtain ⟨S1, hS1⟩ := Module.Finite.fg_top (R := A[X]) (M := Module.AEval' M.x1)
  choose mg kg hg using fun g : Module.AEval' M.x0 ↦
    M.exists_r1 (M.r0 ((Module.AEval'.of M.x0).symm g))
  choose mh kh hh using fun h : Module.AEval' M.x1 ↦
    M.exists_r0 (M.r1 ((Module.AEval'.of M.x1).symm h))
  refine ⟨max (S0.sup kg) (S1.sup kh), fun n hn ↦ ?_⟩
  have hng : ∀ g ∈ S0, kg g ≤ n := fun g hg' ↦
    (Finset.le_sup hg').trans ((le_max_left _ _).trans hn)
  have hnh : ∀ h ∈ S1, kh h ≤ n := fun h hh' ↦
    (Finset.le_sup hh').trans ((le_max_right _ _).trans hn)
  let σ : ({g // g ∈ S0} ⊕ {h // h ∈ S1}) → M.M0 × M.M1
    | Sum.inl g => ((Module.AEval'.of M.x0).symm g.1, (M.x1 ^ (n - kg g.1)) (mg g.1))
    | Sum.inr h => ((M.x0 ^ (n - kh h.1)) (mh h.1), (Module.AEval'.of M.x1).symm h.1)
  refine ⟨_, inferInstance, σ, ?_, ?_, ?_⟩
  · rintro (⟨g, hg'⟩ | ⟨h, hh'⟩)
    · change M.r0 _ = (M.t ^ (n : ℤ)) (M.r1 ((M.x1 ^ (n - kg g)) (mg g)))
      rw [M.r0_eq_t_zpow_r1 (hg g), ← t_zpow_neg_r1, t_zpow_apply_zpow]
      congr 2
      have := hng g hg'
      omega
    · change M.r0 ((M.x0 ^ (n - kh h)) (mh h)) = (M.t ^ (n : ℤ)) (M.r1 _)
      rw [← t_pow_r0, ← hh h, ← pow_add_apply, ← zpow_natCast]
      congr 3
      have := hnh h hh'
      omega
  · exact surjective_sectionsF0 M σ (S0 : Set _) hS0 fun g hg' ↦ ⟨Sum.inl ⟨g, hg'⟩, rfl⟩
  · exact surjective_sectionsF1 M σ (S1 : Set _) hS1 fun h hh' ↦ ⟨Sum.inr ⟨h, hh'⟩, rfl⟩

/-! ### Kernels -/

/-- The restriction of a linear automorphism to a stable submodule. -/
def restrictEquiv {P : Type u} [AddCommGroup P] [Module A P] (e : P ≃ₗ[A] P) (S : Submodule A P)
    (he : ∀ z ∈ S, e z ∈ S) (he' : ∀ z ∈ S, e.symm z ∈ S) : S ≃ₗ[A] S where
  toLinearMap := e.toLinearMap.restrict he
  invFun z := ⟨e.symm z.1, he' z.1 z.2⟩
  left_inv z := Subtype.ext (e.symm_apply_apply z.1)
  right_inv z := Subtype.ext (e.apply_symm_apply z.1)

lemma restrictEquiv_pow_val {P : Type u} [AddCommGroup P] [Module A P] (e : P ≃ₗ[A] P)
    (S : Submodule A P) (he : ∀ z ∈ S, e z ∈ S) (he' : ∀ z ∈ S, e.symm z ∈ S) (k : ℕ) (z : S) :
    ((restrictEquiv e S he he' ^ k) z).1 = (e ^ k) z.1 := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, LinearEquiv.mul_apply]; rfl

lemma restrictEquiv_symm_pow_val {P : Type u} [AddCommGroup P] [Module A P] (e : P ≃ₗ[A] P)
    (S : Submodule A P) (he : ∀ z ∈ S, e z ∈ S) (he' : ∀ z ∈ S, e.symm z ∈ S) (k : ℕ) (z : S) :
    (((restrictEquiv e S he he').symm ^ k) z).1 = (e.symm ^ k) z.1 := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, LinearEquiv.mul_apply]; rfl

lemma restrict_pow_val {P : Type u} [AddCommGroup P] [Module A P] (f : P →ₗ[A] P)
    (S : Submodule A P) (hf : ∀ z ∈ S, f z ∈ S) (k : ℕ) (z : S) :
    ((f.restrict hf ^ k) z).1 = (f ^ k) z.1 := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]; rfl

lemma Hom.comm_t_symm_pow (φ : Hom M N) (k : ℕ) (z : M.M01) :
    φ.f01 ((M.t.symm ^ k) z) = (N.t.symm ^ k) (φ.f01 z) := by
  have := φ.comm_t_zpow (-(k : ℤ)) z
  rwa [zpow_neg, zpow_natCast, ← inv_pow, zpow_neg, zpow_natCast, ← inv_pow] at this

lemma Hom.comm_x0_pow (φ : Hom M N) (k : ℕ) (m : M.M0) :
    φ.f0 ((M.x0 ^ k) m) = (N.x0 ^ k) (φ.f0 m) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, φ.comm_x0, ih, pow_succ',
      Module.End.mul_apply]

lemma Hom.comm_x1_pow (φ : Hom M N) (k : ℕ) (m : M.M1) :
    φ.f1 ((M.x1 ^ k) m) = (N.x1 ^ k) (φ.f1 m) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, φ.comm_x1, ih, pow_succ',
      Module.End.mul_apply]

/-- The kernel of a morphism of chart modules. -/
noncomputable def Hom.ker (φ : Hom M N) : ChartModule A where
  M0 := ModuleCat.of A (LinearMap.ker φ.f0)
  M1 := ModuleCat.of A (LinearMap.ker φ.f1)
  M01 := ModuleCat.of A (LinearMap.ker φ.f01)
  x0 := M.x0.restrict fun m (hm : φ.f0 m = 0) ↦ show φ.f0 _ = 0 by rw [φ.comm_x0, hm, map_zero]
  x1 := M.x1.restrict fun m (hm : φ.f1 m = 0) ↦ show φ.f1 _ = 0 by rw [φ.comm_x1, hm, map_zero]
  t := restrictEquiv M.t (LinearMap.ker φ.f01)
    (fun z (hz : φ.f01 z = 0) ↦ show φ.f01 (M.t z) = 0 by rw [φ.comm_t, hz, map_zero])
    (fun z (hz : φ.f01 z = 0) ↦ show φ.f01 (M.t.symm z) = 0 by
      apply N.t.injective
      rw [← φ.comm_t, LinearEquiv.apply_symm_apply, hz, map_zero])
  r0 := M.r0.restrict fun m (hm : φ.f0 m = 0) ↦ show φ.f01 _ = 0 by rw [φ.comm_r0, hm, map_zero]
  r1 := M.r1.restrict fun m (hm : φ.f1 m = 0) ↦ show φ.f01 _ = 0 by rw [φ.comm_r1, hm, map_zero]
  r0_x0 m := Subtype.ext (M.r0_x0 m.1)
  r1_x1 m := Subtype.ext (M.r1_x1 m.1)
  exists_r0 z := by
    obtain ⟨m, k, hk⟩ := M.exists_r0 z.1
    have h0 : N.r0 (φ.f0 m) = 0 := by
      rw [← φ.comm_r0, ← hk, ← zpow_natCast, φ.comm_t_zpow, show φ.f01 z.1 = 0 from z.2,
        map_zero]
    obtain ⟨j, hj⟩ := N.ker_r0 _ h0
    have hmem : φ.f0 ((M.x0 ^ j) m) = 0 := by rw [φ.comm_x0_pow, hj]
    refine ⟨⟨(M.x0 ^ j) m, hmem⟩, j + k, Subtype.ext ?_⟩
    rw [restrictEquiv_pow_val, pow_add_apply, hk, t_pow_r0]
    rfl
  ker_r0 m hm := by
    obtain ⟨k, hk⟩ := M.ker_r0 m.1 (congrArg Subtype.val hm)
    exact ⟨k, Subtype.ext ((restrict_pow_val _ _ _ k m).trans hk)⟩
  exists_r1 z := by
    obtain ⟨m, k, hk⟩ := M.exists_r1 z.1
    have h0 : N.r1 (φ.f1 m) = 0 := by
      rw [← φ.comm_r1, ← hk, φ.comm_t_symm_pow, show φ.f01 z.1 = 0 from z.2, map_zero]
    obtain ⟨j, hj⟩ := N.ker_r1 _ h0
    have hmem : φ.f1 ((M.x1 ^ j) m) = 0 := by rw [φ.comm_x1_pow, hj]
    refine ⟨⟨(M.x1 ^ j) m, hmem⟩, j + k, Subtype.ext ?_⟩
    rw [restrictEquiv_symm_pow_val, pow_add_apply, hk, t_symm_pow_r1]
    rfl
  ker_r1 m hm := by
    obtain ⟨k, hk⟩ := M.ker_r1 m.1 (congrArg Subtype.val hm)
    exact ⟨k, Subtype.ext ((restrict_pow_val _ _ _ k m).trans hk)⟩

lemma twist_zero : M.twist 0 = M := by
  cases M
  simp only [twist, mk.injEq, true_and, heq_eq_eq]
  ext m
  simp

variable (M) in
/-- **Finiteness of `H¹`**, untwisted. -/
theorem finite_H1 [Module.Finite A[X] (Module.AEval' M.x0)] : Module.Finite A M.H1 := by
  have := M.finite_H1_twist 0
  rwa [twist_zero] at this

/-- The kernel of a morphism out of `𝒪(-n)^ι` is finitely generated on `Spec A[X]`, over a
Noetherian ring. -/
lemma finite_ker_free [IsNoetherianRing A] {ι : Type u} [Fintype ι] {n : ℕ}
    (φ : Hom (free (A := A) ι n) M) : Module.Finite A[X] (Module.AEval' φ.ker.x0) := by
  let F := free (A := A) ι n
  let e : Module.AEval' F.x0 ≃ₗ[A[X]] (ι → A[X]) :=
    LinearEquiv.ofAEval F.x0 (LinearEquiv.refl A (ι → A[X]) : F.M0 ≃ₗ[A] (ι → A[X]))
      fun _ ↦ rfl
  haveI : Module.Finite A[X] (Module.AEval' F.x0) := Module.Finite.equiv e.symm
  haveI : IsNoetherian A[X] (Module.AEval' F.x0) := inferInstance
  let j : Module.AEval' φ.ker.x0 →ₗ[A[X]] Module.AEval' F.x0 :=
    LinearMap.ofAEval _ ((Module.AEval'.of F.x0).toLinearMap ∘ₗ
      (LinearMap.ker φ.f0).subtype) fun m ↦ by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        rw [Module.AEval'.X_smul_of]
        rfl
  refine Module.Finite.of_injective j fun a b hab ↦ ?_
  have := congrArg (Module.AEval'.of F.x0).symm hab
  simp only [j, LinearMap.ofAEval, LinearMap.coe_mk] at this
  exact (Module.AEval'.of φ.ker.x0).symm.injective (Subtype.ext this)

variable (M) in
/-- **Finiteness of `H⁰`** (Stacks, Lemma 30.14.1(3), Tag 01YS, for `ℙ¹_A`): over a Noetherian
ring, if `M₀` and `M₁` are finitely generated, `H⁰(M)` is a finitely generated `A`-module. -/
theorem finite_H0 [IsNoetherianRing A] [Module.Finite A[X] (Module.AEval' M.x0)]
    [Module.Finite A[X] (Module.AEval' M.x1)] : Module.Finite A M.H0 := by
  obtain ⟨n₀, hn₀⟩ := M.exists_sectionsHom_surjective
  obtain ⟨ι, _, σ, hσ, h0, h1⟩ := hn₀ (max n₀ 1) (le_max_left _ _)
  let φ := sectionsHom (n := max n₀ 1) M σ hσ
  have h01 : Function.Surjective φ.f01 := φ.surjective_f01 h0
  haveI := finite_ker_free φ
  haveI : Module.Finite A φ.ker.H1 := φ.ker.finite_H1
  let δ := TwoCech.δ (f' := φ.ker.r0) (g' := φ.ker.r1)
    (LinearMap.ker φ.f0).subtype (LinearMap.ker φ.f1).subtype (LinearMap.ker φ.f01).subtype
    φ.f0 φ.f1 φ.f01 (LinearMap.ext fun _ ↦ rfl) (LinearMap.ext fun _ ↦ rfl)
    φ.comm_r0' φ.comm_r1' φ.f0.exact_subtype_ker_map φ.f1.exact_subtype_ker_map
    φ.f01.exact_subtype_ker_map h0 h1 (Submodule.injective_subtype (LinearMap.ker φ.f01))
  have hex := TwoCech.exact_mapH0_δ (f' := φ.ker.r0) (g' := φ.ker.r1)
    (LinearMap.ker φ.f0).subtype (LinearMap.ker φ.f1).subtype (LinearMap.ker φ.f01).subtype
    φ.f0 φ.f1 φ.f01 (LinearMap.ext fun _ ↦ rfl) (LinearMap.ext fun _ ↦ rfl)
    φ.comm_r0' φ.comm_r1' φ.f0.exact_subtype_ker_map φ.f1.exact_subtype_ker_map
    φ.f01.exact_subtype_ker_map h0 h1 (Submodule.injective_subtype (LinearMap.ker φ.f01))
  have hinj : Function.Injective δ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (hex x).1 hx
    have hy : y = 0 := by
      have : (y : _ × _) ∈ (free (A := A) ι (max n₀ 1)).H0 := y.2
      rw [H0_free_eq_bot ι (max n₀ 1) (le_max_right _ _)] at this
      exact Subtype.ext ((Submodule.mem_bot _).1 this)
    rw [hy, map_zero]
  exact Module.Finite.of_injective δ hinj

end ChartModule

end ProjectiveLine
