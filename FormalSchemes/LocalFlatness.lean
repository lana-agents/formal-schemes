/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The local criterion of flatness, adic form

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `M` a finite `R`-module such that every
reduction `(R / Iⁿ) ⊗ M` is flat over `R / Iⁿ`. Then `M` is flat at every prime containing `I`
(`LocalFlatness.flat_localizedModule`; an adic form of the local criterion for flatness, cf.
Stacks, Section 10.99, Lemma 10.99.7, Tag 00MK).

The proof is the usual one: for an ideal `J` and `x ∈ J ⊗ M` mapping to `0` in `M`, the
Artin–Rees lemma gives `J ∩ I^{m+k} ⊆ I^m J`, flatness of the reduction modulo `I^{m+k}` shows that
`x` dies in `(J / J ∩ I^{m+k}) ⊗ M`, hence `x ∈ I^m (J ⊗ M)` for all `m`
(`LocalFlatness.mem_smul_top_of_rTensor_eq_zero`); by Krull's intersection theorem `x` is killed
by an element of `1 + I` (`LocalFlatness.exists_mem_smul_eq_of_rTensor_eq_zero`), which is
invertible at every prime containing `I`.
-/

universe u

open TensorProduct

namespace LocalFlatness

variable {R : Type u} [CommRing R] (I : Ideal R) {M : Type u} [AddCommGroup M] [Module R M]

lemma mem_smul_top_of_mem (J : Ideal R) (m : ℕ) (j : J) (hj : (j : R) ∈ I ^ m • J) :
    j ∈ (I ^ m • ⊤ : Submodule R J) := by
  have h : (I ^ m • ⊤ : Submodule R J).map J.subtype = I ^ m • J := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← h] at hj
  obtain ⟨j', hj', hjj⟩ := hj
  rwa [← Subtype.ext hjj]

lemma tmul_mem_smul_top (J : Ideal R) (m : ℕ) {j : J} (hj : j ∈ (I ^ m • ⊤ : Submodule R J))
    (y : M) : j ⊗ₜ[R] y ∈ (I ^ m • ⊤ : Submodule R (J ⊗[R] M)) := by
  refine Submodule.smul_induction_on (p := fun j : J ↦ j ⊗ₜ[R] y ∈
      (I ^ m • ⊤ : Submodule R (J ⊗[R] M))) hj (fun r hr n _ ↦ ?_) (fun a b ha hb ↦ ?_)
  · rw [← smul_tmul']
    exact Submodule.smul_mem_smul hr trivial
  · rw [add_tmul]
    exact add_mem ha hb

section Reduction

variable (J : Ideal R) (n : ℕ)

/-- `J → J (R / Iⁿ)`. -/
def toMap : J →ₗ[R] (J.map (Ideal.Quotient.mk (I ^ n))) where
  toFun j := ⟨Ideal.Quotient.mk (I ^ n) j, Ideal.mem_map_of_mem _ j.2⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' r a := Subtype.ext (by simp [Algebra.smul_def])

lemma toMap_surjective : Function.Surjective (toMap I J n) := fun z ↦ by
  obtain ⟨j, hj, hz⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 z.2
  exact ⟨⟨j, hj⟩, Subtype.ext hz⟩

lemma mem_of_toMap_eq_zero {j : J} (hj : toMap I J n j = 0) :
    (j : R) ∈ I ^ n := by
  have := congrArg Subtype.val hj
  simpa [toMap, Ideal.Quotient.eq_zero_iff_mem] using this

end Reduction

variable [IsNoetherianRing R]

/-- **Key step of the local criterion**: an element of the kernel of `J ⊗ M → M` lies in
`Iᵐ (J ⊗ M)` for every `m`. -/
theorem mem_smul_top_of_rTensor_eq_zero
    (h : ∀ n, Module.Flat (R ⧸ I ^ n) ((R ⧸ I ^ n) ⊗[R] M)) (J : Ideal R) (x : J ⊗[R] M)
    (hx : LinearMap.rTensor M J.subtype x = 0) (m : ℕ) :
    x ∈ (I ^ m • ⊤ : Submodule R (J ⊗[R] M)) := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (M := R) J
  set n := m + k
  let B := R ⧸ I ^ n
  let JB : Ideal B := J.map (Ideal.Quotient.mk (I ^ n))
  let πJ := toMap I J n
  -- the kernel of `J → JB` lies in `Iᵐ J`
  have hK : ∀ j ∈ LinearMap.ker πJ, j ∈ (I ^ m • ⊤ : Submodule R J) := fun j hj ↦ by
    apply mem_smul_top_of_mem I J m j
    have h1 : (j : R) ∈ (I ^ n • ⊤ : Submodule R R) ⊓ J := by
      refine ⟨?_, j.2⟩
      rw [smul_eq_mul, Ideal.mul_top]
      exact mem_of_toMap_eq_zero I J n hj
    rw [hk n (by omega), show n - k = m by omega] at h1
    exact Submodule.smul_mono le_rfl inf_le_right h1
  let K := LinearMap.ker πJ
  let Q := (J ⊗[R] M) ⧸ (I ^ m • ⊤ : Submodule R (J ⊗[R] M))
  have hle : LinearMap.range (TensorProduct.map K.subtype (LinearMap.id : M →ₗ[R] M)) ≤
      (I ^ m • ⊤ : Submodule R (J ⊗[R] M)) := by
    rintro _ ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => exact tmul_mem_smul_top I J m (hK a.1 a.2) y
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  let e1 : (J ⧸ K) ≃ₗ[R] JB := πJ.quotKerEquivOfSurjective (toMap_surjective I J n)
  let δR : JB ⊗[R] M →ₗ[R] Q :=
    Submodule.factor hle ∘ₗ (quotientTensorEquiv M K).toLinearMap ∘ₗ
      (LinearEquiv.rTensor M e1.symm).toLinearMap
  let cb := AlgebraTensorModule.cancelBaseChange R B B JB M
  let cbB := AlgebraTensorModule.cancelBaseChange R B B B M
  -- `δR ∘ (πJ ⊗ M) = mkQ`
  have hδ : ∀ w : J ⊗[R] M, δR (LinearMap.rTensor M πJ w) =
      Submodule.Quotient.mk w := fun w ↦ by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      have he : e1.symm (πJ a) = Submodule.Quotient.mk a := by
        rw [LinearEquiv.symm_apply_eq]; rfl
      simp [δR, he]
      try rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]; rfl
  -- the square with the reduction of `J → R`
  have hsq : ∀ w : J ⊗[R] M,
      LinearMap.rTensor (B ⊗[R] M) JB.subtype (cb.symm (LinearMap.rTensor M πJ w)) =
        cbB.symm (LinearMap.rTensor M (Algebra.linearMap R B)
          (LinearMap.rTensor M J.subtype w)) := fun w ↦ by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [cb, cbB]; try rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have hinj := (Module.Flat.iff_rTensor_injective' (R := B) (M := B ⊗[R] M)).1 (h n) JB
  have h0 : cb.symm (LinearMap.rTensor M πJ x) = 0 := by
    apply hinj
    rw [hsq, hx]
    simp
  have h1 : Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R (J ⊗[R] M))) x = 0 := by
    rw [← hδ, ← cb.apply_symm_apply (LinearMap.rTensor M πJ x), h0]
    simp
  exact (Submodule.Quotient.mk_eq_zero _).1 h1

variable [Module.Finite R M]

/-- **The local criterion of flatness**: an element of the kernel of `J ⊗ M → M` is killed by an
element of `1 + I`. -/
theorem exists_mem_smul_eq_of_rTensor_eq_zero
    (h : ∀ n, Module.Flat (R ⧸ I ^ n) ((R ⧸ I ^ n) ⊗[R] M)) (J : Ideal R) (x : J ⊗[R] M)
    (hx : LinearMap.rTensor M J.subtype x = 0) : ∃ r ∈ I, r • x = x := by
  have hmem : x ∈ (⨅ i : ℕ, I ^ i • ⊤ : Submodule R (J ⊗[R] M)) :=
    Submodule.mem_iInf _ |>.2 fun m ↦ mem_smul_top_of_rTensor_eq_zero I h J x hx m
  obtain ⟨⟨r, hr⟩, hrx⟩ := (I.mem_iInf_smul_pow_eq_bot_iff x).1 hmem
  exact ⟨r, hr, hrx⟩

/-- **The local criterion of flatness** (adic form, cf. Stacks, Tag 00MK): if all reductions
`(R / Iⁿ) ⊗ M` are flat over `R / Iⁿ`, then `M` is flat at every prime containing `I`. -/
theorem flat_localizedModule (h : ∀ n, Module.Flat (R ⧸ I ^ n) ((R ⧸ I ^ n) ⊗[R] M))
    (p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    Module.Flat R (LocalizedModule p.primeCompl M) := by
  classical
  let S := p.primeCompl
  let g := LocalizedModule.mkLinearMap S M
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro z hz
  rw [LinearMap.mem_ker] at hz
  rw [Submodule.mem_bot]
  -- `M_p ⊗ J = (M ⊗ J)_p` and `M_p ⊗ R = (M ⊗ R)_p`
  let gJ := AlgebraTensorModule.rTensor R J g
  let gR := AlgebraTensorModule.rTensor R R g
  have hJ : IsLocalizedModule S gJ := IsLocalizedModule.rTensor (R := R) (A := R) S g
  have hR : IsLocalizedModule S gR := IsLocalizedModule.rTensor (R := R) (A := R) S g
  have hnat : ∀ w : M ⊗[R] J, LinearMap.lTensor _ J.subtype (gJ w) =
      gR (LinearMap.lTensor M J.subtype w) := fun w ↦ by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S gJ z
  have hx0 : gR (LinearMap.lTensor M J.subtype x) = gR 0 := by
    rw [← hnat, ← hs, map_zero]
    change LinearMap.lTensor _ J.subtype ((s : R) • z) = 0
    rw [map_smul, hz, smul_zero]
  obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := gR) hx0
  rw [smul_zero, Submonoid.smul_def, ← map_smul] at ht
  -- the local criterion, after swapping the factors
  have hc : LinearMap.rTensor M J.subtype (TensorProduct.comm R M J ((t : R) • x)) = 0 := by
    have : LinearMap.rTensor M J.subtype ∘ₗ (TensorProduct.comm R M J).toLinearMap =
        (TensorProduct.comm R M R).toLinearMap ∘ₗ LinearMap.lTensor M J.subtype := by
      apply TensorProduct.ext'
      intro a b
      simp
    have h2 := LinearMap.congr_fun this ((t : R) • x)
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at h2
    rw [h2, ht, map_zero]
  obtain ⟨r, hr, hrx⟩ := exists_mem_smul_eq_of_rTensor_eq_zero I h J _ hc
  rw [← map_smul, (TensorProduct.comm R M J).injective.eq_iff] at hrx
  have hu : (1 - r) * (t : R) ∈ S := by
    refine p.primeCompl.mul_mem (fun h1 ↦ ?_) t.2
    have : (1 : R) ∈ p := by simpa using p.add_mem h1 (hIp hr)
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 this)
  have hux : ((1 - r) * (t : R)) • x = 0 := by
    rw [mul_smul, sub_smul, one_smul, hrx, sub_self]
  have hgx : gJ x = 0 := by
    have hunit := IsLocalizedModule.map_units gJ ⟨_, hu⟩
    apply ((Module.End.isUnit_iff _).1 hunit).1
    rw [map_zero, Module.algebraMap_end_apply, ← map_smul]
    exact (congrArg gJ hux).trans (map_zero _)
  have hunit := IsLocalizedModule.map_units gJ s
  apply ((Module.End.isUnit_iff _).1 hunit).1
  rw [map_zero, Module.algebraMap_end_apply]
  exact hs.trans hgx

end LocalFlatness
