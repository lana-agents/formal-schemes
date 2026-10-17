/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleFlat
import FormalSchemes.LocalizedFlatTransport
import FormalSchemes.ProjectiveLineProper

/-!
# Global flatness of algebraizations on `ℙ¹_A`

Let `I ⊆ A` lie in the Jacobson radical. A chart module `M` on `ℙ¹_A` that is flat at every point
of the special fibre `V(I)` (on both charts) is flat on both charts:
`ProjectiveLine.ChartModule.flat_of_flat_special`. Every point of `ℙ¹_A` specializes into
`V(I)` (`ProjectiveLine.exists_prime_le_comap_toLaurentInv`), flatness at a point passes to its
generizations (`LocalFlatness.flat_localizedModule_of_le`), and flatness at a point of the overlap
`Spec A[T, T⁻¹]` does not depend on the chart through which it is computed
(`ProjectiveLine.ChartModule.flat_overlap_iff`, from `LocalFlatness.flat_localizedModule_iff`).
For a maximal ideal `m` of `A[X]` with `m + I·A[X] = A[X]` this gives flatness at `m` from
flatness at a point of `V(I)` in the chart `Spec A[Y]`.

Combined with the local criterion along the special fibre
(`ProjectiveLine.ChartModule.flat_x0_of_system`), an
algebraization of an adic system of flat chart modules is flat on `ℙ¹_A`:
`ProjectiveLine.ChartModule.flat_of_system`.
-/

universe u

open Polynomial TensorProduct
open scoped LaurentPolynomial
open LaurentPolynomial (T invert)

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A] (M : ChartModule A)

/-- The chart module with the two charts exchanged (`X ↔ Y`, `T ↦ T⁻¹`). -/
def swap : ChartModule A where
  M0 := M.M1
  M1 := M.M0
  M01 := M.M01
  x0 := M.x1
  x1 := M.x0
  t := M.t.symm
  r0 := M.r1
  r1 := M.r0
  r0_x0 := M.r1_x1
  r1_x1 m := by rw [LinearEquiv.symm_symm]; exact M.r0_x0 m
  exists_r0 := M.exists_r1
  ker_r0 := M.ker_r1
  exists_r1 z := by rw [LinearEquiv.symm_symm]; exact M.exists_r0 z
  ker_r1 := M.ker_r0

/-- The sections over the overlap `Spec A[T, T⁻¹]`, as an `A[T, T⁻¹]`-module through
`ProjectiveLine.ChartModule.lev`. -/
def Overlap : Type u := M.M01

instance : AddCommGroup M.Overlap := inferInstanceAs (AddCommGroup M.M01)

instance : Module A M.Overlap := inferInstanceAs (Module A M.M01)

noncomputable instance : Module A[T;T⁻¹] M.Overlap := Module.compHom M.M01 M.lev.toRingHom

lemma overlap_smul (l : A[T;T⁻¹]) (z : M.Overlap) : l • z = M.lev l z := rfl

lemma lev_C (a : A) (z : M.M01) : M.lev (LaurentPolynomial.C a) z = a • z := by
  simpa [LaurentPolynomial.T_zero] using M.lev_C_mul_T a 0 z

lemma lev_aeval (φ : A[X] →+* A[T;T⁻¹]) (hC : ∀ a, φ (Polynomial.C a) = LaurentPolynomial.C a)
    (τ : M.M01 ≃ₗ[A] M.M01) (hτ : ∀ z, M.lev (φ X) z = τ z) (p : A[X]) (z : M.M01) :
    M.lev (φ p) z = Polynomial.aeval (τ : M.M01 →ₗ[A] M.M01) p z := by
  have h : M.lev.toRingHom.comp φ = (Polynomial.aeval (τ : M.M01 →ₗ[A] M.M01)).toRingHom :=
    Polynomial.ringHom_ext (fun a ↦ by ext z; simp [hC, lev_C]) (by ext z; simp [hτ])
  exact congrArg (fun F : A[X] →+* Module.End A M.M01 ↦ F p z) h

/-- **Flatness at a point of the overlap, computed through a chart.** For a chart ring map
`φ : A[X] → A[T, T⁻¹]` which is a localization at `X`, `X` acting as `τ`, and a chart module
`(P₀, f)` with `r : P₀ → M₀₁` a localization at `X`: for a prime `P` of `A[T, T⁻¹]` over `p`,
`P₀` is flat at `p` iff the overlap sections are flat at `P`. -/
theorem flat_overlap_iff (φ : A[X] →+* A[T;T⁻¹])
    (hloc : letI := φ.toAlgebra; IsLocalization.Away (X : A[X]) A[T;T⁻¹])
    (hC : ∀ a, φ (Polynomial.C a) = LaurentPolynomial.C a)
    (τ : M.M01 ≃ₗ[A] M.M01) (hτ : ∀ z, M.lev (φ X) z = τ z)
    {P₀ : Type u} [AddCommGroup P₀] [Module A P₀] (f : P₀ →ₗ[A] P₀) (r : P₀ →ₗ[A] M.M01)
    (hr : ∀ p, r (f p) = τ (r p)) (hex : ∀ z, ∃ (p : P₀) (k : ℕ), (τ ^ k) z = r p)
    (hker : ∀ p, r p = 0 → ∃ k : ℕ, (f ^ k) p = 0)
    (P : Ideal A[T;T⁻¹]) [P.IsPrime] (p : Ideal A[X]) [p.IsPrime] (hp : P.comap φ = p) :
    Module.Flat A[X] (LocalizedModule p.primeCompl (Module.AEval' f)) ↔
      Module.Flat A[T;T⁻¹] (LocalizedModule P.primeCompl M.Overlap) := by
  subst hp
  letI : Algebra A[X] A[T;T⁻¹] := φ.toAlgebra
  letI : Module A[X] M.Overlap := Module.compHom _ φ
  haveI : IsScalarTower A[X] A[T;T⁻¹] M.Overlap :=
    ⟨fun x y z ↦ by
      change (φ x * y) • z = φ x • (y • z)
      exact mul_smul _ _ _⟩
  haveI := hloc
  let e : Module.AEval' (τ : M.M01 →ₗ[A] M.M01) ≃ₗ[A[X]] M.Overlap :=
    { toFun := fun z ↦ (Module.AEval'.of (τ : M.M01 →ₗ[A] M.M01)).symm z
      invFun := fun z ↦ Module.AEval'.of (τ : M.M01 →ₗ[A] M.M01) z
      map_add' := fun _ _ ↦ map_add _ _ _
      map_smul' := fun p z ↦ by
        change _ = M.lev (φ p) _
        rw [Module.AEval.of_symm_smul, M.lev_aeval φ hC τ hτ, Module.End.smul_def]
      left_inv := fun z ↦ by simp
      right_inv := fun z ↦ by simp }
  haveI := BTensor.isLocalizedModule_aevalMap hr hex hker
  haveI : IsLocalizedModule.Away (X : A[X])
      (e.toLinearMap ∘ₗ BTensor.aevalMap (f' := (τ : M.M01 →ₗ[A] M.M01)) r hr) :=
    IsLocalizedModule.of_linearEquiv _ _ e
  exact LocalFlatness.flat_localizedModule_iff (X : A[X])
    (e.toLinearMap ∘ₗ BTensor.aevalMap (f' := (τ : M.M01 →ₗ[A] M.M01)) r hr) P

lemma isLocalization_toLaurent :
    letI := (toLaurent : A[X] →+* A[T;T⁻¹]).toAlgebra
    IsLocalization.Away (X : A[X]) A[T;T⁻¹] :=
  LaurentPolynomial.isLocalization

lemma isLocalization_toLaurentInv :
    letI := (toLaurentInv : A[X] →+* A[T;T⁻¹]).toAlgebra
    IsLocalization.Away (X : A[X]) A[T;T⁻¹] :=
  (IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers (X : A[X]))
    (invert : A[T;T⁻¹] ≃ₐ[A] A[T;T⁻¹]).toRingEquiv).1 LaurentPolynomial.isLocalization

lemma lev_toLaurent_X (z : M.M01) : M.lev (toLaurent (X : A[X])) z = M.t z := by
  rw [Polynomial.toLaurent_X, M.lev_T, zpow_one]

lemma lev_toLaurentInv_X (z : M.M01) : M.lev (toLaurentInv (X : A[X])) z = M.t.symm z := by
  rw [toLaurentInv_apply, Polynomial.toLaurent_X, LaurentPolynomial.invert_T, M.lev_T,
    zpow_neg_one]
  rfl

/-- **Flatness spreads from the special fibre**, chart `Spec A[X]`: if `I` lies in the Jacobson
radical and `M` is flat at every point of `V(I)` on both charts, then `M₀` is flat over `A[X]`. -/
theorem flat_x0_of_flat_special (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (h0 : ∀ (p : Ideal A[X]) [p.IsPrime], I.map C ≤ p →
      Module.Flat A[X] (LocalizedModule p.primeCompl (Module.AEval' M.x0)))
    (h1 : ∀ (p : Ideal A[X]) [p.IsPrime], I.map C ≤ p →
      Module.Flat A[X] (LocalizedModule p.primeCompl (Module.AEval' M.x1))) :
    Module.Flat A[X] (Module.AEval' M.x0) := by
  refine Module.flat_of_localized_maximal _ fun m hm ↦ ?_
  haveI := hm.isPrime
  by_cases hIm : I.map C ≤ m
  · exact h0 m hIm
  have htop : I.map C ⊔ m = ⊤ := by
    by_contra hne
    exact hIm (le_sup_left.trans (hm.eq_of_le hne le_sup_right).symm.le)
  have hX := X_notMem_of_sup_eq_top hI m htop
  obtain ⟨q, hq, hle, hIq⟩ := exists_prime_le_comap_toLaurentInv hI m htop
  haveI := isPrime_map_toLaurent m hX
  have hflat1 : Module.Flat A[X] (LocalizedModule
      ((m.map (algebraMap A[X] A[T;T⁻¹])).comap toLaurentInv).primeCompl
        (Module.AEval' M.x1)) :=
    LocalFlatness.flat_localizedModule_of_le _ q hle (h1 q hIq)
  have hL := (M.flat_overlap_iff toLaurentInv isLocalization_toLaurentInv
    (fun a ↦ by rw [toLaurentInv_apply, Polynomial.toLaurent_C, LaurentPolynomial.invert_C])
    M.t.symm M.lev_toLaurentInv_X M.x1 M.r1 M.r1_x1 M.exists_r1 M.ker_r1 _ _ rfl).1 hflat1
  exact (M.flat_overlap_iff toLaurent isLocalization_toLaurent
    (fun a ↦ Polynomial.toLaurent_C a) M.t M.lev_toLaurent_X M.x0 M.r0 M.r0_x0 M.exists_r0
    M.ker_r0 _ m (comap_map_toLaurent m hX)).2 hL

/-- **Flatness spreads from the special fibre**: if `I` lies in the Jacobson radical and `M` is
flat at every point of `V(I)` on both charts, then `M` is flat on both charts of `ℙ¹_A`. -/
theorem flat_of_flat_special (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (h0 : ∀ (p : Ideal A[X]) [p.IsPrime], I.map C ≤ p →
      Module.Flat A[X] (LocalizedModule p.primeCompl (Module.AEval' M.x0)))
    (h1 : ∀ (p : Ideal A[X]) [p.IsPrime], I.map C ≤ p →
      Module.Flat A[X] (LocalizedModule p.primeCompl (Module.AEval' M.x1))) :
    Module.Flat A[X] (Module.AEval' M.x0) ∧ Module.Flat A[X] (Module.AEval' M.x1) :=
  ⟨M.flat_x0_of_flat_special I hI h0 h1, M.swap.flat_x0_of_flat_special I hI h1 h0⟩

/-- **Algebraizations of flat adic systems are flat** (on both charts of `ℙ¹_A`). Let `A` be
Noetherian and `I`-adically complete, `N` a coherent chart module with `α n : N → Mₙ` inducing
`N / Iⁿ N ≅ Mₙ` on both charts (as produced by
`ProjectiveLine.AdicChartSystem.exists_algebraization`). If every
`Mₙ` is flat over `ℙ¹_{A/Iⁿ}`, then `N₀` and `N₁` are flat over `A[X]` resp. `A[Y]`. -/
theorem flat_of_system [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] (N : ChartModule A)
    [Module.Finite A[X] (Module.AEval' N.x0)] [Module.Finite A[X] (Module.AEval' N.x1)]
    (Mn : ℕ → ChartModule A) (α : ∀ n, Hom N (Mn n))
    (hs0 : ∀ n, Function.Surjective (α n).f0) (hs1 : ∀ n, Function.Surjective (α n).f1)
    (hk0 : ∀ n, LinearMap.ker (α n).f0 = I ^ n • ⊤) (hk1 : ∀ n, LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hkill0 : ∀ n, I ^ n • (⊤ : Submodule A (Mn n).M0) = ⊥)
    (hkill1 : ∀ n, I ^ n • (⊤ : Submodule A (Mn n).M1) = ⊥)
    (hflat0 : ∀ n, Module.Flat (A[X] ⧸ I.map C ^ n)
      ((A[X] ⧸ I.map C ^ n) ⊗[A[X]] Module.AEval' (Mn n).x0))
    (hflat1 : ∀ n, Module.Flat (A[X] ⧸ I.map C ^ n)
      ((A[X] ⧸ I.map C ^ n) ⊗[A[X]] Module.AEval' (Mn n).x1)) :
    Module.Flat A[X] (Module.AEval' N.x0) ∧ Module.Flat A[X] (Module.AEval' N.x1) :=
  N.flat_of_flat_special I (IsAdicComplete.le_jacobson_bot I)
    (fun p _ hp ↦ flat_x0_of_system I N Mn α hs0 hk0 hkill0 hflat0 p hp)
    (fun p _ hp ↦ flat_x1_of_system I N Mn α hs1 hk1 hkill1 hflat1 p hp)

end ChartModule

end ProjectiveLine
