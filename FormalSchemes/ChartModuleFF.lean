/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleHom
import FormalSchemes.AdicSystemModule

/-!
# Full faithfulness of completion for coherent modules on `ℙ¹_A`

Let `A` be a Noetherian ring, complete with respect to an ideal `I`, and let `N`, `N'` be chart
modules of finite type (coherent modules on `ℙ¹_A`, `FormalSchemes.ChartModule`). Then a morphism
`N → N'` is the same as a compatible system of morphisms `N → N' / Iⁿ N'`
(`ChartModule.toHomSystem_bijective`); since a morphism `N → N' / Iⁿ N'` is the same as a morphism
`N / Iⁿ N → N' / Iⁿ N'`, this is the full faithfulness of the completion functor from coherent
modules on `ℙ¹_A` to compatible systems (Stacks, Lemma 30.24.1, Tag 0883, for `ℙ¹_A`).

The proof follows Stacks: present `N` as a quotient of `𝒪(-d)^ι`, whose morphisms are sections of
twists (`ChartModule.homFreeEquiv`), and use the theorem on formal functions for `H⁰`
(`ChartModule.formalFunctionsH0`) together with the completeness of finite `A`-modules.
-/

universe u

open Polynomial LaurentPolynomial

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A]

lemma finite_ker_free_x1 [IsNoetherianRing A] {M : ChartModule A} {ι : Type u} [Fintype ι]
    {n : ℕ} (φ : Hom (free (A := A) ι n) M) : Module.Finite A[X] (Module.AEval' φ.ker.x1) := by
  let F := free (A := A) ι n
  let e : Module.AEval' F.x1 ≃ₗ[A[X]] (ι → A[X]) :=
    LinearEquiv.ofAEval F.x1 (LinearEquiv.refl A (ι → A[X]) : F.M1 ≃ₗ[A] (ι → A[X]))
      fun _ ↦ rfl
  haveI : Module.Finite A[X] (Module.AEval' F.x1) := Module.Finite.equiv e.symm
  haveI : IsNoetherian A[X] (Module.AEval' F.x1) := inferInstance
  let j : Module.AEval' φ.ker.x1 →ₗ[A[X]] Module.AEval' F.x1 :=
    LinearMap.ofAEval _ ((Module.AEval'.of F.x1).toLinearMap ∘ₗ
      (LinearMap.ker φ.f1).subtype) fun m ↦ by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        rw [Module.AEval'.X_smul_of]
        rfl
  refine Module.Finite.of_injective j fun a b hab ↦ ?_
  have := congrArg (Module.AEval'.of F.x1).symm hab
  simp only [j, LinearMap.ofAEval, LinearMap.coe_mk] at this
  exact (Module.AEval'.of φ.ker.x1).symm.injective (Subtype.ext this)

/-- Twisting commutes with reduction, on sections. -/
lemma twist_quot_r1 (P : ChartModule A) (J : Ideal A) (d : ℕ) :
    ((P.quot J).twist d).r1 = ((P.twist d).quot J).r1 := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change ((P.quot J).t ^ (d : ℤ)) (Submodule.Quotient.mk (P.r1 x)) =
      Submodule.Quotient.mk ((P.t ^ (d : ℤ)) (P.r1 x))
    rw [zpow_natCast, zpow_natCast]
    exact quotEquiv_pow_mk _ P.t (map_smul_top_equiv J P.t) d _

lemma H0_twist_quot (P : ChartModule A) (J : Ideal A) (d : ℕ) :
    ((P.quot J).twist d).H0 = ((P.twist d).quot J).H0 := by
  change TwoCech.H0 _ ((P.quot J).twist d).r1 = TwoCech.H0 _ ((P.twist d).quot J).r1
  rw [twist_quot_r1]

lemma Hom.comp_assoc {M N P Q : ChartModule A} (χ : Hom P Q) (ψ : Hom N P) (φ : Hom M N) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := Hom.ext' rfl rfl rfl

section Evaluation

variable (P : ChartModule A) (I : Ideal A)

/-- The map `H⁰(P) → lim H⁰(P / Iⁿ P)`. -/
noncomputable def H0ToSystem : P.H0 →ₗ[A] P.H0System I :=
  P.toH0System I ∘ₗ AdicCompletion.of I P.H0

lemma H0ToSystem_apply (h : P.H0) (n : ℕ) :
    (P.H0ToSystem I h).1 n = (P.quotHom (I ^ n)).mapH0 h := rfl

theorem H0ToSystem_bijective [IsNoetherianRing A] [IsAdicComplete I A]
    [Module.Finite A[X] (Module.AEval' P.x0)] [Module.Finite A[X] (Module.AEval' P.x1)] :
    Function.Bijective (P.H0ToSystem I) := by
  haveI : Module.Finite A P.H0 := P.finite_H0
  haveI := AdicSystem.isAdicComplete_of_finite I P.H0
  exact (P.bijective_toH0System I).comp (AdicCompletion.of_bijective I P.H0)

end Evaluation

/-- The compatible systems of morphisms `N → N' / Iⁿ N'`. -/
def HomSystem (N N' : ChartModule A) (I : Ideal A) : Type u :=
  {f : ∀ n : ℕ, Hom N (N'.quot (I ^ n)) //
    ∀ (m n : ℕ) (h : m ≤ n), (N'.quotMap (Ideal.pow_le_pow_right h)).comp (f n) = f m}

/-- The reductions of a morphism. -/
noncomputable def toHomSystem {N N' : ChartModule A} (I : Ideal A) (ψ : Hom N N') :
    HomSystem N N' I :=
  ⟨fun n ↦ (N'.quotHom (I ^ n)).comp ψ, fun _ _ _ ↦ Hom.ext' rfl rfl rfl⟩

section Sections

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- Move a section across `H0_twist_quot`. -/
def castH0 (P : ChartModule A) (J : Ideal A) (d : ℕ) (x : ((P.quot J).twist d).H0) :
    ((P.twist d).quot J).H0 :=
  ⟨x.1, H0_twist_quot P J d ▸ x.2⟩

lemma castH0_injective (P : ChartModule A) (J : Ideal A) (d : ℕ) :
    Function.Injective (castH0 P J d) := fun x y h ↦ by
  have := congrArg Subtype.val h
  exact Subtype.ext this

lemma castH0_homFreeSections (P : ChartModule A) (J : Ideal A)
    (φ : Hom (free (A := A) ι d) P) (i : ι) :
    castH0 P J d (homFreeSections (P.quot J) ((P.quotHom J).comp φ) i) =
      ((P.twist d).quotHom J).mapH0 (homFreeSections P φ i) := rfl

end Sections

lemma sectionsHom_zero_f0 {P : ChartModule A} {ι : Type u} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (χ : Hom (free (A := A) ι d) P) (h : ∀ i, homFreeSections P χ i = 0)
    (p : (free (A := A) ι d).M0) : χ.f0 p = 0 := by
  have hχ : χ = (homFreeEquiv P).symm (homFreeEquiv P χ) := by simp
  have h' : homFreeEquiv P χ = 0 := funext h
  rw [hχ, h']
  exact Finset.sum_eq_zero fun i _ ↦ map_zero (Polynomial.aeval P.x0 (p i))

lemma sectionsHom_zero_f1 {P : ChartModule A} {ι : Type u} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (χ : Hom (free (A := A) ι d) P) (h : ∀ i, homFreeSections P χ i = 0)
    (p : (free (A := A) ι d).M1) : χ.f1 p = 0 := by
  have hχ : χ = (homFreeEquiv P).symm (homFreeEquiv P χ) := by simp
  have h' : homFreeEquiv P χ = 0 := funext h
  rw [hχ, h']
  exact Finset.sum_eq_zero fun i _ ↦ map_zero (Polynomial.aeval P.x1 (p i))

variable (I : Ideal A) (N N' : ChartModule A)

/-- **Full faithfulness of completion on `ℙ¹_A`** (Stacks, Lemma 30.24.1, Tag 0883, for `ℙ¹_A`):
over a Noetherian ring complete with respect to `I`, morphisms `N → N'` of coherent modules are
the compatible systems of morphisms `N → N' / Iⁿ N'`. -/
theorem toHomSystem_bijective [IsNoetherianRing A] [IsAdicComplete I A]
    [Module.Finite A[X] (Module.AEval' N.x0)] [Module.Finite A[X] (Module.AEval' N.x1)]
    [Module.Finite A[X] (Module.AEval' N'.x0)] [Module.Finite A[X] (Module.AEval' N'.x1)] :
    Function.Bijective (toHomSystem (N := N) (N' := N') I) := by
  classical
  obtain ⟨n₀, hn₀⟩ := N.exists_sectionsHom_surjective
  obtain ⟨ι, _, σ, hσ, h0, h1⟩ := hn₀ n₀ le_rfl
  let π := sectionsHom (n := n₀) N σ hσ
  have hev : ∀ e : ℕ, Function.Bijective ((N'.twist e).H0ToSystem I) := fun e ↦ by
    haveI : Module.Finite A[X] (Module.AEval' (N'.twist e).x0) :=
      inferInstanceAs (Module.Finite A[X] (Module.AEval' N'.x0))
    haveI : Module.Finite A[X] (Module.AEval' (N'.twist e).x1) :=
      inferInstanceAs (Module.Finite A[X] (Module.AEval' N'.x1))
    exact (N'.twist e).H0ToSystem_bijective I
  -- morphisms out of `𝒪(-n₀)^ι` are detected by their reductions
  have key : ∀ φ ψ : Hom (free (A := A) ι n₀) N',
      (∀ n, (N'.quotHom (I ^ n)).comp φ = (N'.quotHom (I ^ n)).comp ψ) → φ = ψ := by
    intro φ ψ h
    apply (homFreeEquiv N').injective
    funext i
    apply (hev n₀).1
    apply Subtype.ext
    funext n
    rw [H0ToSystem_apply, H0ToSystem_apply]
    change ((N'.twist n₀).quotHom (I ^ n)).mapH0 (homFreeSections N' φ i) =
      ((N'.twist n₀).quotHom (I ^ n)).mapH0 (homFreeSections N' ψ i)
    rw [← castH0_homFreeSections, ← castH0_homFreeSections, h n]
  constructor
  · intro ψ ψ' h
    apply π.comp_cancel h0 h1
    apply key
    intro n
    rw [← Hom.comp_assoc, ← Hom.comp_assoc]
    exact congrArg (fun χ ↦ Hom.comp χ π) (congrArg (fun F : HomSystem N N' I ↦ F.1 n) h)
  · intro f
    let σn : ∀ n, ι → ((N'.twist n₀).quot (I ^ n)).H0 := fun n i ↦
      castH0 N' (I ^ n) n₀ (homFreeSections _ ((f.1 n).comp π) i)
    have hcomp : ∀ i, (fun n ↦ σn n i) ∈ (N'.twist n₀).H0System I := fun i m n h ↦ by
      apply Subtype.ext
      simp only [σn]
      rw [← f.2 m n h]
      rfl
    choose s hs using fun i ↦ (hev n₀).2 ⟨_, hcomp i⟩
    let φ := (homFreeEquiv N').symm s
    have hφs : ∀ i, homFreeSections N' φ i = s i := fun i ↦
      congrFun ((homFreeEquiv N').apply_symm_apply s) i
    have hφ : ∀ n, (N'.quotHom (I ^ n)).comp φ = (f.1 n).comp π := by
      intro n
      apply (homFreeEquiv _).injective
      funext i
      apply castH0_injective N' (I ^ n) n₀
      change castH0 N' (I ^ n) n₀ (homFreeSections _ ((N'.quotHom _).comp φ) i) = σn n i
      rw [castH0_homFreeSections, hφs]
      have := congrArg (fun y : (N'.twist n₀).H0System I ↦ y.1 n) (hs i)
      simpa [H0ToSystem_apply] using this
    -- `φ` kills the kernel of `π`
    haveI := finite_ker_free π
    haveI := finite_ker_free_x1 π
    obtain ⟨e₀, he₀⟩ := π.ker.exists_sectionsHom_surjective
    obtain ⟨ι', _, τ, hτ, g0, g1⟩ := he₀ e₀ le_rfl
    let ρ := sectionsHom (n := e₀) π.ker τ hτ
    let χ := (φ.comp π.kerι).comp ρ
    have hχ : ∀ i, homFreeSections N' χ i = 0 := by
      intro i
      apply (hev e₀).1
      rw [map_zero]
      apply Subtype.ext
      funext n
      rw [H0ToSystem_apply]
      change ((N'.twist e₀).quotHom (I ^ n)).mapH0 (homFreeSections N' χ i) = 0
      rw [← castH0_homFreeSections]
      have : (N'.quotHom (I ^ n)).comp χ = (((f.1 n).comp π).comp π.kerι).comp ρ := by
        simp only [χ, ← Hom.comp_assoc, hφ n]
      rw [this]
      apply Subtype.ext
      apply Prod.ext
      · change (f.1 n).f0 (π.f0 ((π.kerι.f0 (ρ.f0 _)))) = 0
        rw [show π.f0 (π.kerι.f0 (ρ.f0 _)) = 0 from (ρ.f0 _).2, map_zero]
      · change (f.1 n).f1 (π.f1 ((π.kerι.f1 (ρ.f1 _)))) = 0
        rw [show π.f1 (π.kerι.f1 (ρ.f1 _)) = 0 from (ρ.f1 _).2, map_zero]
    have hk0 : LinearMap.ker π.f0 ≤ LinearMap.ker φ.f0 := by
      intro k hk
      obtain ⟨p, hp⟩ := g0 ⟨k, hk⟩
      have := sectionsHom_zero_f0 χ hχ p
      change φ.f0 (ρ.f0 p).1 = 0 at this
      have hp' : (ρ.f0 p).1 = k := congrArg Subtype.val hp
      rwa [hp'] at this
    have hk1 : LinearMap.ker π.f1 ≤ LinearMap.ker φ.f1 := by
      intro k hk
      obtain ⟨p, hp⟩ := g1 ⟨k, hk⟩
      have := sectionsHom_zero_f1 χ hχ p
      change φ.f1 (ρ.f1 p).1 = 0 at this
      have hp' : (ρ.f1 p).1 = k := congrArg Subtype.val hp
      rwa [hp'] at this
    refine ⟨π.descend h0 h1 φ hk0 hk1, Subtype.ext (funext fun n ↦ π.comp_cancel h0 h1 ?_)⟩
    change ((N'.quotHom (I ^ n)).comp (π.descend h0 h1 φ hk0 hk1)).comp π = (f.1 n).comp π
    rw [Hom.comp_assoc, Hom.descend_comp, hφ n]

end ChartModule

end ProjectiveLine
