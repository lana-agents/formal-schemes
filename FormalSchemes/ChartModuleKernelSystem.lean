/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleKernel

/-!
# The adic kernel system of a compatible surjection

For compatible chart-surjective morphisms `φₙ : G → Mₙ` from `G = 𝒪(-d)^ι` onto an adic system,
let `Lₙ = ker (G / Iⁿ G → Mₙ)`. With the stabilisation constant `c` of
`AdicChartSystem.exists_stab`, the reductions `Kₙ = L_{n+c} / Iⁿ L_{n+c}` form an adic system
(`AdicChartSystem.kerSystem`), with compatible surjections `Kₙ → Lₙ`
(`AdicChartSystem.kerSystemToL`). This is the kernel in `Coh(ℙ¹_A, I)` (Stacks, Lemma 30.23.2,
Tag 087X) of `Ĝ → M`.
-/

universe u

open Polynomial LaurentPolynomial

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A]

lemma quot_kill0 (P : ChartModule A) (J : Ideal A) :
    J • (⊤ : Submodule A (P.quot J).M0) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro a ha x _
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top

lemma quot_kill1 (P : ChartModule A) (J : Ideal A) :
    J • (⊤ : Submodule A (P.quot J).M1) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro a ha x _
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- A submodule of a module killed by `J` is killed by `J`. -/
lemma smul_top_sub_eq_bot {N : Type u} [AddCommGroup N] [Module A N] (J : Ideal A)
    (h : J • (⊤ : Submodule A N) = ⊥) (P : Submodule A N) : J • (⊤ : Submodule A P) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro a ha x _
  rw [Submodule.mem_bot]
  apply Subtype.ext
  have : a • (x : N) ∈ J • (⊤ : Submodule A N) := Submodule.smul_mem_smul ha Submodule.mem_top
  rw [h, Submodule.mem_bot] at this
  exact this

end ChartModule

namespace AdicChartSystem

open ChartModule

variable {A : Type u} [CommRing A] {I : Ideal A} (S : AdicChartSystem I) {ι : Type u} [Fintype ι]
  {d : ℕ} (φ : ∀ n, Hom (free (A := A) ι d) (S.M n))

/-- `φₙ` factored through `G / Iⁿ G`. -/
noncomputable def psi (n : ℕ) : Hom ((free (A := A) ι d).quot (I ^ n)) (S.M n) :=
  (φ n).factorQuot (I ^ n) (S.kill0 n) (S.kill1 n)

lemma psi_comp (n : ℕ) : (S.psi φ n).comp ((free (A := A) ι d).quotHom (I ^ n)) = φ n :=
  Hom.factorQuot_comp _ _ _ _

/-- The kernel `Lₙ` of `G / Iⁿ G → Mₙ`. -/
noncomputable abbrev L (n : ℕ) : ChartModule A := (S.psi φ n).ker

variable {φ} (hφ : ∀ m n (h : m ≤ n), (S.tr h).comp (φ n) = φ m)

include hφ in
lemma psi_quotMap {m n : ℕ} (h : m ≤ n) :
    (S.psi φ m).comp ((free (A := A) ι d).quotMap (Ideal.pow_le_pow_right h)) =
      (S.tr h).comp (S.psi φ n) := by
  apply ((free (A := A) ι d).quotHom (I ^ n)).comp_cancel (Submodule.mkQ_surjective _)
    (Submodule.mkQ_surjective _)
  rw [Hom.comp_assoc, Hom.comp_assoc, S.psi_comp φ n, hφ m n h]
  have : ((free (A := A) ι d).quotMap (Ideal.pow_le_pow_right h)).comp
      ((free (A := A) ι d).quotHom (I ^ n)) = (free (A := A) ι d).quotHom (I ^ m) :=
    Hom.ext' rfl rfl rfl
  rw [this, S.psi_comp φ m]

/-- The transition maps `Lₙ → Lₘ`. -/
noncomputable def Lmap {m n : ℕ} (h : m ≤ n) : Hom (S.L φ n) (S.L φ m) where
  f0 := LinearMap.codRestrict _ (((free (A := A) ι d).quotMap (Ideal.pow_le_pow_right h)).f0 ∘ₗ
    (LinearMap.ker (S.psi φ n).f0).subtype) fun x ↦ by
      change (S.psi φ m).f0 (((free (A := A) ι d).quotMap (Ideal.pow_le_pow_right h)).f0 x.1) = 0
      have := congrArg (fun χ : Hom _ (S.M m) ↦ χ.f0 x.1) (S.psi_quotMap hφ h)
      simp only [Hom.comp_f0, LinearMap.coe_comp, Function.comp_apply] at this
      rw [this, show (S.psi φ n).f0 x.1 = 0 from x.2, map_zero]
  f1 := LinearMap.codRestrict _ (((free (A := A) ι d).quotMap (Ideal.pow_le_pow_right h)).f1 ∘ₗ
    (LinearMap.ker (S.psi φ n).f1).subtype) fun x ↦ by
      change (S.psi φ m).f1 (((free (A := A) ι d).quotMap (Ideal.pow_le_pow_right h)).f1 x.1) = 0
      have := congrArg (fun χ : Hom _ (S.M m) ↦ χ.f1 x.1) (S.psi_quotMap hφ h)
      simp only [Hom.comp_f1, LinearMap.coe_comp, Function.comp_apply] at this
      rw [this, show (S.psi φ n).f1 x.1 = 0 from x.2, map_zero]
  f01 := LinearMap.codRestrict _ (((free (A := A) ι d).quotMap (Ideal.pow_le_pow_right h)).f01 ∘ₗ
    (LinearMap.ker (S.psi φ n).f01).subtype) fun x ↦ by
      change (S.psi φ m).f01 (((free (A := A) ι d).quotMap (Ideal.pow_le_pow_right h)).f01 x.1) = 0
      have := congrArg (fun χ : Hom _ (S.M m) ↦ χ.f01 x.1) (S.psi_quotMap hφ h)
      simp only [Hom.comp_f01, LinearMap.coe_comp, Function.comp_apply] at this
      rw [this, show (S.psi φ n).f01 x.1 = 0 from x.2, map_zero]
  comm_x0 x := Subtype.ext (((free (A := A) ι d).quotMap (Ideal.pow_le_pow_right h)).comm_x0 x.1)
  comm_x1 x := Subtype.ext (((free (A := A) ι d).quotMap (Ideal.pow_le_pow_right h)).comm_x1 x.1)
  comm_t z := Subtype.ext (((free (A := A) ι d).quotMap (Ideal.pow_le_pow_right h)).comm_t z.1)
  comm_r0 x := Subtype.ext (((free (A := A) ι d).quotMap (Ideal.pow_le_pow_right h)).comm_r0 x.1)
  comm_r1 x := Subtype.ext (((free (A := A) ι d).quotMap (Ideal.pow_le_pow_right h)).comm_r1 x.1)

lemma psi_f0_mk (n : ℕ) (x : (free (A := A) ι d).M0) :
    (S.psi φ n).f0 (Submodule.Quotient.mk x) = (φ n).f0 x :=
  congrArg (fun χ : Hom _ (S.M n) ↦ χ.f0 x) (S.psi_comp φ n)

lemma psi_f1_mk (n : ℕ) (x : (free (A := A) ι d).M1) :
    (S.psi φ n).f1 (Submodule.Quotient.mk x) = (φ n).f1 x :=
  congrArg (fun χ : Hom _ (S.M n) ↦ χ.f1 x) (S.psi_comp φ n)

lemma Lmap_comp {k m n : ℕ} (h₁ : k ≤ m) (h₂ : m ≤ n) :
    (S.Lmap hφ h₁).comp (S.Lmap hφ h₂) = S.Lmap hφ (h₁.trans h₂) := by
  refine Hom.ext' ?_ ?_ ?_ <;> refine LinearMap.ext fun x ↦ Subtype.ext ?_ <;>
    obtain ⟨x, hx⟩ := x <;> induction x using Submodule.Quotient.induction_on <;> rfl

lemma Lmap_refl (n : ℕ) : S.Lmap hφ (le_refl n) = Hom.id _ := by
  refine Hom.ext' ?_ ?_ ?_ <;> refine LinearMap.ext fun x ↦ Subtype.ext ?_ <;>
    obtain ⟨x, hx⟩ := x <;> induction x using Submodule.Quotient.induction_on <;> rfl

variable (hs0 : ∀ n, Function.Surjective (φ n).f0) (hs1 : ∀ n, Function.Surjective (φ n).f1)

include hs0 in
lemma Lmap_surjective0 {m n : ℕ} (h : m ≤ n) : Function.Surjective (S.Lmap hφ h).f0 := by
  rintro ⟨y, hy⟩
  induction y using Submodule.Quotient.induction_on with | H y => ?_
  have hy' : (φ m).f0 y = 0 := by rw [← S.psi_f0_mk]; exact hy
  have h1 : (φ n).f0 y ∈ I ^ m • (⊤ : Submodule A (S.M n).M0) := by
    rw [← S.ker0 h, LinearMap.mem_ker, ← hy']
    exact congrArg (fun χ : Hom _ (S.M m) ↦ χ.f0 y) (hφ m n h)
  obtain ⟨k, hk, hyk⟩ := exists_ker_lift (φ n).f0 (hs0 n) (I ^ m) y h1
  refine ⟨⟨Submodule.Quotient.mk k, by
    rw [LinearMap.mem_ker, S.psi_f0_mk]; exact hk⟩, Subtype.ext ?_⟩
  change Submodule.Quotient.mk k = Submodule.Quotient.mk y
  exact ((Submodule.Quotient.eq _).2 hyk).symm

include hs1 in
lemma Lmap_surjective1 {m n : ℕ} (h : m ≤ n) : Function.Surjective (S.Lmap hφ h).f1 := by
  rintro ⟨y, hy⟩
  induction y using Submodule.Quotient.induction_on with | H y => ?_
  have hy' : (φ m).f1 y = 0 := by rw [← S.psi_f1_mk]; exact hy
  have h1 : (φ n).f1 y ∈ I ^ m • (⊤ : Submodule A (S.M n).M1) := by
    rw [← S.ker1 h, LinearMap.mem_ker, ← hy']
    exact congrArg (fun χ : Hom _ (S.M m) ↦ χ.f1 y) (hφ m n h)
  obtain ⟨k, hk, hyk⟩ := exists_ker_lift (φ n).f1 (hs1 n) (I ^ m) y h1
  refine ⟨⟨Submodule.Quotient.mk k, by
    rw [LinearMap.mem_ker, S.psi_f1_mk]; exact hk⟩, Subtype.ext ?_⟩
  change Submodule.Quotient.mk k = Submodule.Quotient.mk y
  exact ((Submodule.Quotient.eq _).2 hyk).symm

omit hφ in
lemma ker_psi_f0 (N : ℕ) : LinearMap.ker (S.psi φ N).f0 =
    (LinearMap.ker (φ N).f0).map (I ^ N • (⊤ : Submodule A (free (A := A) ι d).M0)).mkQ := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [LinearMap.mem_ker, S.psi_f0_mk, Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : x - y ∈ I ^ N • (⊤ : Submodule A (free (A := A) ι d).M0) :=
        (Submodule.Quotient.eq _).1 hyx.symm
      have h2 := S.smul_top_le_ker_f0 (φ := φ) N this
      rw [LinearMap.mem_ker, map_sub, show (φ N).f0 y = 0 from hy, sub_zero] at h2
      exact h2

omit hφ in
lemma ker_psi_f1 (N : ℕ) : LinearMap.ker (S.psi φ N).f1 =
    (LinearMap.ker (φ N).f1).map (I ^ N • (⊤ : Submodule A (free (A := A) ι d).M1)).mkQ := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [LinearMap.mem_ker, S.psi_f1_mk, Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : x - y ∈ I ^ N • (⊤ : Submodule A (free (A := A) ι d).M1) :=
        (Submodule.Quotient.eq _).1 hyx.symm
      have h2 := S.smul_top_le_ker_f1 (φ := φ) N this
      rw [LinearMap.mem_ker, map_sub, show (φ N).f1 y = 0 from hy, sub_zero] at h2
      exact h2

variable (c : ℕ)

/-- The level `n` of the kernel system: `L_{n+c} / Iⁿ L_{n+c}`. -/
noncomputable abbrev KM (n : ℕ) : ChartModule A := (S.L φ (n + c)).quot (I ^ n)

/-- The transition maps of the kernel system. -/
noncomputable def Ktr {m n : ℕ} (h : m ≤ n) : Hom (S.KM (φ := φ) c n) (S.KM (φ := φ) c m) :=
  ((S.L φ (m + c)).quotMap (Ideal.pow_le_pow_right h)).comp
    ((S.Lmap hφ (Nat.add_le_add_right h c)).reduce (I ^ n))

lemma Ktr_quotHom {m n : ℕ} (h : m ≤ n) :
    (S.Ktr hφ c h).comp ((S.L φ (n + c)).quotHom (I ^ n)) =
      ((S.L φ (m + c)).quotHom (I ^ m)).comp (S.Lmap hφ (Nat.add_le_add_right h c)) :=
  Hom.ext' (LinearMap.ext fun _ ↦ rfl) (LinearMap.ext fun _ ↦ rfl) (LinearMap.ext fun _ ↦ rfl)

lemma Ktr_comp {k m n : ℕ} (h₁ : k ≤ m) (h₂ : m ≤ n) :
    (S.Ktr hφ c h₁).comp (S.Ktr hφ c h₂) = S.Ktr hφ c (h₁.trans h₂) := by
  apply ((S.L φ (n + c)).quotHom (I ^ n)).comp_cancel (Submodule.mkQ_surjective _)
    (Submodule.mkQ_surjective _)
  rw [Hom.comp_assoc, Ktr_quotHom, ← Hom.comp_assoc, Ktr_quotHom, Hom.comp_assoc, Lmap_comp,
    Ktr_quotHom]

lemma Ktr_refl (n : ℕ) : S.Ktr hφ c (le_refl n) = Hom.id _ := by
  apply ((S.L φ (n + c)).quotHom (I ^ n)).comp_cancel (Submodule.mkQ_surjective _)
    (Submodule.mkQ_surjective _)
  rw [Ktr_quotHom, Lmap_refl, Hom.comp_id, Hom.id_comp]

include hs0 in
lemma Ktr_surjective0 {m n : ℕ} (h : m ≤ n) : Function.Surjective (S.Ktr hφ c h).f0 := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨x, rfl⟩ := S.Lmap_surjective0 hφ hs0 (Nat.add_le_add_right h c) y
  exact ⟨Submodule.Quotient.mk x, congrArg (fun χ : Hom _ (S.KM (φ := φ) c m) ↦ χ.f0 x)
    (S.Ktr_quotHom hφ c h)⟩

include hs1 in
lemma Ktr_surjective1 {m n : ℕ} (h : m ≤ n) : Function.Surjective (S.Ktr hφ c h).f1 := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨x, rfl⟩ := S.Lmap_surjective1 hφ hs1 (Nat.add_le_add_right h c) y
  exact ⟨Submodule.Quotient.mk x, congrArg (fun χ : Hom _ (S.KM (φ := φ) c m) ↦ χ.f1 x)
    (S.Ktr_quotHom hφ c h)⟩

lemma Ktr_f0_mk {m n : ℕ} (h : m ≤ n) (x : (S.L φ (n + c)).M0) :
    (S.Ktr hφ c h).f0 (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((S.Lmap hφ (Nat.add_le_add_right h c)).f0 x) :=
  congrArg (fun χ : Hom _ (S.KM (φ := φ) c m) ↦ χ.f0 x) (S.Ktr_quotHom hφ c h)

lemma Ktr_f1_mk {m n : ℕ} (h : m ≤ n) (x : (S.L φ (n + c)).M1) :
    (S.Ktr hφ c h).f1 (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((S.Lmap hφ (Nat.add_le_add_right h c)).f1 x) :=
  congrArg (fun χ : Hom _ (S.KM (φ := φ) c m) ↦ χ.f1 x) (S.Ktr_quotHom hφ c h)

lemma smul_le_ker_of_kill {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q]
    [Module A Q] (f : P →ₗ[A] Q) (J : Ideal A) (hQ : J • (⊤ : Submodule A Q) = ⊥) :
    J • (⊤ : Submodule A P) ≤ LinearMap.ker f := by
  rw [Submodule.smul_le]
  intro a ha x _
  rw [LinearMap.mem_ker, map_smul]
  have : a • f x ∈ J • (⊤ : Submodule A Q) := Submodule.smul_mem_smul ha Submodule.mem_top
  rwa [hQ, Submodule.mem_bot] at this

lemma mem_of_mk_mem_smul {N : Type u} [AddCommGroup N] [Module A N] (J : Ideal A) (k : ℕ)
    (K : Submodule A N) (x : N)
    (hx : Submodule.Quotient.mk (p := (J ^ k • ⊤ : Submodule A N)) x ∈
      J ^ m • K.map (J ^ k • ⊤ : Submodule A N).mkQ) :
    x ∈ J ^ m • K ⊔ J ^ k • ⊤ := by
  rw [← Submodule.map_smul'', Submodule.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : x - y ∈ J ^ k • (⊤ : Submodule A N) := (Submodule.Quotient.eq _).1 hyx.symm
  rw [show x = y + (x - y) by abel]
  exact Submodule.add_mem_sup hy this

lemma mk_mem_smul_of_mem {N : Type u} [AddCommGroup N] [Module A N] (J : Ideal A) (k : ℕ)
    (K : Submodule A N) (x : N) (hx : x ∈ J ^ m • K ⊔ J ^ k • ⊤) :
    Submodule.Quotient.mk (p := (J ^ k • ⊤ : Submodule A N)) x ∈
      J ^ m • K.map (J ^ k • ⊤ : Submodule A N).mkQ := by
  rw [← Submodule.map_smul'']
  obtain ⟨y, hy, g, hg, rfl⟩ := Submodule.mem_sup.1 hx
  refine ⟨y, hy, ?_⟩
  change Submodule.Quotient.mk y = Submodule.Quotient.mk (y + g)
  rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hg, add_zero]

/-- The kernel condition of the kernel system on `Spec A[X]`. -/
lemma Ktr_ker0 (hc : ∀ n n', n ≤ n' → ∀ x ∈ LinearMap.ker (φ (n' + c)).f0,
      x ∈ I ^ n • LinearMap.ker (φ (n + c)).f0 ⊔ I ^ (n + c) • ⊤ →
      x ∈ I ^ n • LinearMap.ker (φ (n' + c)).f0 ⊔ I ^ (n' + c) • ⊤) {m n : ℕ} (h : m ≤ n) :
    LinearMap.ker (S.Ktr hφ c h).f0 = I ^ m • ⊤ := by
  apply le_antisymm
  · intro w hw
    obtain ⟨⟨xb, hxb⟩, rfl⟩ := Submodule.mkQ_surjective _ w
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ xb
    have hxK : x ∈ LinearMap.ker (φ (n + c)).f0 := by
      rw [LinearMap.mem_ker, ← S.psi_f0_mk]
      exact hxb
    rw [LinearMap.mem_ker] at hw
    change (S.Ktr hφ c h).f0 (Submodule.Quotient.mk _) = 0 at hw
    rw [S.Ktr_f0_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff] at hw
    change Submodule.Quotient.mk x ∈ I ^ m • LinearMap.ker (S.psi φ (m + c)).f0 at hw
    rw [S.ker_psi_f0] at hw
    have h1 := mem_of_mk_mem_smul I (m + c) _ x hw
    have h2 := hc m n h x hxK h1
    have h3 := mk_mem_smul_of_mem I (n + c) _ x h2
    rw [← S.ker_psi_f0] at h3
    have h4 : (⟨Submodule.Quotient.mk x, hxb⟩ : LinearMap.ker (S.psi φ (n + c)).f0) ∈
        I ^ m • (⊤ : Submodule A (LinearMap.ker (S.psi φ (n + c)).f0)) := by
      rw [Submodule.mem_smul_top_iff]
      exact h3
    have := Submodule.mem_map_of_mem (f := (I ^ n • (⊤ : Submodule A
      (LinearMap.ker (S.psi φ (n + c)).f0))).mkQ) h4
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
    exact this
  · exact smul_le_ker_of_kill _ _ (quot_kill0 _ _)

/-- The kernel condition of the kernel system on `Spec A[Y]`. -/
lemma Ktr_ker1 (hc : ∀ n n', n ≤ n' → ∀ x ∈ LinearMap.ker (φ (n' + c)).f1,
      x ∈ I ^ n • LinearMap.ker (φ (n + c)).f1 ⊔ I ^ (n + c) • ⊤ →
      x ∈ I ^ n • LinearMap.ker (φ (n' + c)).f1 ⊔ I ^ (n' + c) • ⊤) {m n : ℕ} (h : m ≤ n) :
    LinearMap.ker (S.Ktr hφ c h).f1 = I ^ m • ⊤ := by
  apply le_antisymm
  · intro w hw
    obtain ⟨⟨xb, hxb⟩, rfl⟩ := Submodule.mkQ_surjective _ w
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ xb
    have hxK : x ∈ LinearMap.ker (φ (n + c)).f1 := by
      rw [LinearMap.mem_ker, ← S.psi_f1_mk]
      exact hxb
    rw [LinearMap.mem_ker] at hw
    change (S.Ktr hφ c h).f1 (Submodule.Quotient.mk _) = 0 at hw
    rw [S.Ktr_f1_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff] at hw
    change Submodule.Quotient.mk x ∈ I ^ m • LinearMap.ker (S.psi φ (m + c)).f1 at hw
    rw [S.ker_psi_f1] at hw
    have h1 := mem_of_mk_mem_smul I (m + c) _ x hw
    have h2 := hc m n h x hxK h1
    have h3 := mk_mem_smul_of_mem I (n + c) _ x h2
    rw [← S.ker_psi_f1] at h3
    have h4 : (⟨Submodule.Quotient.mk x, hxb⟩ : LinearMap.ker (S.psi φ (n + c)).f1) ∈
        I ^ m • (⊤ : Submodule A (LinearMap.ker (S.psi φ (n + c)).f1)) := by
      rw [Submodule.mem_smul_top_iff]
      exact h3
    have := Submodule.mem_map_of_mem (f := (I ^ n • (⊤ : Submodule A
      (LinearMap.ker (S.psi φ (n + c)).f1))).mkQ) h4
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
    exact this
  · exact smul_le_ker_of_kill _ _ (quot_kill1 _ _)


variable [IsNoetherianRing A]

/-- **The kernel system** `Kₙ = L_{n+c} / Iⁿ L_{n+c}`, an adic system. -/
noncomputable def kerSystem
    (hc0 : ∀ n n', n ≤ n' → ∀ x ∈ LinearMap.ker (φ (n' + c)).f0,
      x ∈ I ^ n • LinearMap.ker (φ (n + c)).f0 ⊔ I ^ (n + c) • ⊤ →
      x ∈ I ^ n • LinearMap.ker (φ (n' + c)).f0 ⊔ I ^ (n' + c) • ⊤)
    (hc1 : ∀ n n', n ≤ n' → ∀ x ∈ LinearMap.ker (φ (n' + c)).f1,
      x ∈ I ^ n • LinearMap.ker (φ (n + c)).f1 ⊔ I ^ (n + c) • ⊤ →
      x ∈ I ^ n • LinearMap.ker (φ (n' + c)).f1 ⊔ I ^ (n' + c) • ⊤) :
    AdicChartSystem I where
  M := S.KM (φ := φ) c
  tr h := S.Ktr hφ c h
  tr_comp := S.Ktr_comp hφ c
  surj0 h := S.Ktr_surjective0 hφ hs0 c h
  surj1 h := S.Ktr_surjective1 hφ hs1 c h
  ker0 h := S.Ktr_ker0 hφ c hc0 h
  ker1 h := S.Ktr_ker1 hφ c hc1 h
  tr_refl := S.Ktr_refl hφ c
  kill0 _ := quot_kill0 _ _
  kill1 _ := quot_kill1 _ _
  fin0 n := by
    haveI := finite_free_x0 (A := A) (ι := ι) d
    haveI := finite_quot_x0 (free (A := A) ι d) (I ^ (n + c))
    haveI := finite_ker_x0 (S.psi φ (n + c))
    exact finite_quot_x0 _ _
  fin1 n := by
    haveI := finite_free_x1 (A := A) (ι := ι) d
    haveI := finite_quot_x1 (free (A := A) ι d) (I ^ (n + c))
    haveI := finite_ker_x1 (S.psi φ (n + c))
    exact finite_quot_x1 _ _

omit [IsNoetherianRing A] in
lemma L_kill0 (n : ℕ) : I ^ n • (⊤ : Submodule A (S.L φ n).M0) = ⊥ :=
  smul_top_sub_eq_bot _ (quot_kill0 _ _) _

omit [IsNoetherianRing A] in
lemma L_kill1 (n : ℕ) : I ^ n • (⊤ : Submodule A (S.L φ n).M1) = ⊥ :=
  smul_top_sub_eq_bot _ (quot_kill1 _ _) _

omit [IsNoetherianRing A] in
/-- The surjection `Kₙ → Lₙ`. -/
noncomputable def KtoL (n : ℕ) : Hom (S.KM (φ := φ) c n) (S.L φ n) :=
  (S.Lmap hφ (Nat.le_add_right n c)).factorQuot (I ^ n) (S.L_kill0 n) (S.L_kill1 n)

omit [IsNoetherianRing A] in
lemma KtoL_quotHom (n : ℕ) :
    (S.KtoL hφ c n).comp ((S.L φ (n + c)).quotHom (I ^ n)) = S.Lmap hφ (Nat.le_add_right n c) :=
  Hom.factorQuot_comp _ _ _ _

omit [IsNoetherianRing A] in
include hs0 in
lemma KtoL_surjective0 (n : ℕ) : Function.Surjective (S.KtoL hφ c n).f0 := by
  intro y
  obtain ⟨x, rfl⟩ := S.Lmap_surjective0 hφ hs0 (Nat.le_add_right n c) y
  exact ⟨Submodule.Quotient.mk x,
    congrArg (fun χ : Hom _ (S.L φ n) ↦ χ.f0 x) (S.KtoL_quotHom hφ c n)⟩

omit [IsNoetherianRing A] in
include hs1 in
lemma KtoL_surjective1 (n : ℕ) : Function.Surjective (S.KtoL hφ c n).f1 := by
  intro y
  obtain ⟨x, rfl⟩ := S.Lmap_surjective1 hφ hs1 (Nat.le_add_right n c) y
  exact ⟨Submodule.Quotient.mk x,
    congrArg (fun χ : Hom _ (S.L φ n) ↦ χ.f1 x) (S.KtoL_quotHom hφ c n)⟩

omit [IsNoetherianRing A] in
lemma KtoL_comp {m n : ℕ} (h : m ≤ n) :
    (S.Lmap hφ h).comp (S.KtoL hφ c n) = (S.KtoL hφ c m).comp (S.Ktr hφ c h) := by
  apply ((S.L φ (n + c)).quotHom (I ^ n)).comp_cancel (Submodule.mkQ_surjective _)
    (Submodule.mkQ_surjective _)
  rw [Hom.comp_assoc, KtoL_quotHom, Lmap_comp, Hom.comp_assoc, Ktr_quotHom, ← Hom.comp_assoc,
    KtoL_quotHom, Lmap_comp]

end AdicChartSystem

end ProjectiveLine
