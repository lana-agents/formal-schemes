/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleTensor
import FormalSchemes.ChartModuleExistence

/-!
# Grothendieck existence for coherent algebras on `ℙ¹_A`

A commutative algebra structure on a chart module `M` (a quasi-coherent `𝒪_{ℙ¹_A}`-algebra,
`ProjectiveLine.ChartModule.AlgStr`) is a multiplication `M ⊗ M → M` and a global section `1`,
associative, commutative and unital on both charts. An adic system of chart algebras
(`ProjectiveLine.AdicChartAlgSystem`) is an adic system of coherent chart modules
(`ProjectiveLine.AdicChartSystem`) with algebra structures respected by the transition maps.

**`AdicChartAlgSystem.exists_algebraization`** (Grothendieck existence for coherent algebras on
`ℙ¹_A`; cf. Stacks, Lemma 30.24.3, Tag 0885, and the proof of Lemma 30.28.2, Tag 09ZT, which
algebraizes the multiplications of the `f_{n,*}𝒪_{Y_n}` by full faithfulness, for `X = ℙ¹_A`):
over a Noetherian ring complete with respect to `I`, the algebraization `N` of the underlying
adic system of modules (`AdicChartSystem.exists_algebraization`) carries a compatible algebra
structure. The multiplication and the unit are obtained from
full faithfulness (`ChartModule.toHomSystem_bijective`, Tag 0883, applied to `N ⊗ N`, which is
coherent) and the theorem on formal functions for `H⁰` (`ChartModule.H0ToSystem_bijective`); the
algebra axioms hold because they hold modulo every `Iⁿ` and morphisms out of coherent modules
are detected modulo all `Iⁿ`.
-/

universe u

open Polynomial

namespace ProjectiveLine

namespace ChartModule

open BTensor

variable {A : Type u} [CommRing A]

/-- **A commutative algebra structure on a chart module.** -/
structure AlgStr (M : ChartModule A) where
  /-- the multiplication `M ⊗ M → M` -/
  mul : Hom (M.tensor M) M
  /-- the unit, a global section -/
  one : M.H0
  mul_assoc0 : ∀ a b c : M.M0,
    mul.f0 (tm _ _ (mul.f0 (tm _ _ a b)) c) = mul.f0 (tm _ _ a (mul.f0 (tm _ _ b c)))
  mul_assoc1 : ∀ a b c : M.M1,
    mul.f1 (tm _ _ (mul.f1 (tm _ _ a b)) c) = mul.f1 (tm _ _ a (mul.f1 (tm _ _ b c)))
  mul_comm0 : ∀ a b : M.M0, mul.f0 (tm _ _ a b) = mul.f0 (tm _ _ b a)
  mul_comm1 : ∀ a b : M.M1, mul.f1 (tm _ _ a b) = mul.f1 (tm _ _ b a)
  one_mul0 : ∀ a : M.M0, mul.f0 (tm _ _ one.1.1 a) = a
  one_mul1 : ∀ a : M.M1, mul.f1 (tm _ _ one.1.2 a) = a

variable {M N : ChartModule A}

/-- A morphism of chart modules is a **morphism of algebras** if it is compatible with the
multiplications and the units. -/
def AlgStr.IsHom (B : AlgStr M) (B' : AlgStr N) (φ : Hom M N) : Prop :=
  φ.comp B.mul = B'.mul.comp (φ.tensor φ) ∧ φ.mapH0 B.one = B'.one

lemma Hom.mapH0_comp {P : ChartModule A} (ψ : Hom N P) (φ : Hom M N) (x : M.H0) :
    (ψ.comp φ).mapH0 x = ψ.mapH0 (φ.mapH0 x) := rfl

lemma Hom.mapH0_id (x : M.H0) : (Hom.id M).mapH0 x = x := rfl

lemma Hom.f0_eq_of_eq {φ ψ : Hom M N} (h : φ = ψ) (x : M.M0) : φ.f0 x = ψ.f0 x := by rw [h]

lemma Hom.f1_eq_of_eq {φ ψ : Hom M N} (h : φ = ψ) (x : M.M1) : φ.f1 x = ψ.f1 x := by rw [h]

end ChartModule

open ChartModule BTensor

variable {A : Type u} [CommRing A]

/-- **An adic system of chart algebras**: an adic system of coherent chart modules whose levels
carry algebra structures respected by the transition maps. -/
structure AdicChartAlgSystem (I : Ideal A) extends AdicChartSystem I where
  /-- the algebra structure at level `n` -/
  alg : ∀ n, AlgStr (M n)
  isHom_tr : ∀ {m n : ℕ} (h : m ≤ n), (alg n).IsHom (alg m) (tr h)

namespace AdicChartAlgSystem

variable {I : Ideal A} [IsNoetherianRing A] [IsAdicComplete I A]

/-- **Grothendieck existence for coherent algebras on `ℙ¹_A`** (cf. Stacks, Lemma 30.24.3,
Tag 0885, and the proof of Lemma 30.28.2, Tag 09ZT, for `X = ℙ¹_A`): an adic system of coherent
chart algebras is the system of reductions of a coherent chart algebra. -/
theorem exists_algebraization (S : AdicChartAlgSystem I) :
    ∃ (N : ChartModule A) (_ : Module.Finite A[X] (Module.AEval' N.x0))
      (_ : Module.Finite A[X] (Module.AEval' N.x1)) (B : AlgStr N) (α : ∀ n, Hom N (S.M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α n).f1 = I ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m) ∧
      ∀ n, B.IsHom (S.alg n) (α n) := by
  obtain ⟨N, h0, h1, α, hα, hc⟩ := S.toAdicChartSystem.exists_algebraization
  -- `d n : S.M n ≅ N / Iⁿ N` and its inverse `e n`
  let d : ∀ n, Hom (S.M n) (N.quot (I ^ n)) := fun n ↦
    (α n).descend (hα n).1 (hα n).2.1 (N.quotHom (I ^ n))
      (by rw [(hα n).2.2.1]; exact (Submodule.ker_mkQ _).ge)
      (by rw [(hα n).2.2.2]; exact (Submodule.ker_mkQ _).ge)
  have hd : ∀ n, (d n).comp (α n) = N.quotHom (I ^ n) := fun n ↦ Hom.descend_comp _ _ _ _ _ _
  let e : ∀ n, Hom (N.quot (I ^ n)) (S.M n) := fun n ↦
    (N.quotHom (I ^ n)).descend (Submodule.mkQ_surjective _) (Submodule.mkQ_surjective _) (α n)
      (by
        change LinearMap.ker (Submodule.mkQ _) ≤ _
        rw [Submodule.ker_mkQ, (hα n).2.2.1])
      (by
        change LinearMap.ker (Submodule.mkQ _) ≤ _
        rw [Submodule.ker_mkQ, (hα n).2.2.2])
  have he : ∀ n, (e n).comp (N.quotHom (I ^ n)) = α n := fun n ↦ Hom.descend_comp _ _ _ _ _ _
  have hed : ∀ n, (e n).comp (d n) = Hom.id _ := fun n ↦ by
    refine Hom.comp_cancel (α n) (hα n).1 (hα n).2.1 ?_
    rw [Hom.comp_assoc, hd, he, Hom.id_comp]
  have hqd : ∀ m n (h : m ≤ n),
      (N.quotMap (Ideal.pow_le_pow_right h)).comp (d n) = (d m).comp (S.tr h) := by
    intro m n h
    refine Hom.comp_cancel (α n) (hα n).1 (hα n).2.1 ?_
    rw [Hom.comp_assoc, hd, Hom.comp_assoc, hc, hd]
    exact Hom.ext' rfl rfl rfl
  -- morphisms into `N` are detected by the `α n`
  have inj : ∀ {P : ChartModule A} [Module.Finite A[X] (Module.AEval' P.x0)]
      [Module.Finite A[X] (Module.AEval' P.x1)] (φ ψ : Hom P N),
      (∀ n, (α n).comp φ = (α n).comp ψ) → φ = ψ := by
    intro P _ _ φ ψ h
    refine (toHomSystem_bijective I P N).1 (Subtype.ext (funext fun n ↦ ?_))
    change (N.quotHom (I ^ n)).comp φ = (N.quotHom (I ^ n)).comp ψ
    rw [← hd, Hom.comp_assoc, Hom.comp_assoc, h]
  -- the multiplication
  let sys : ∀ n, Hom (N.tensor N) (N.quot (I ^ n)) := fun n ↦
    (d n).comp ((S.alg n).mul.comp ((α n).tensor (α n)))
  have hsys : ∀ m n (h : m ≤ n),
      (N.quotMap (Ideal.pow_le_pow_right h)).comp (sys n) = sys m := by
    intro m n h
    calc (N.quotMap (Ideal.pow_le_pow_right h)).comp (sys n)
        = ((N.quotMap (Ideal.pow_le_pow_right h)).comp (d n)).comp
            ((S.alg n).mul.comp ((α n).tensor (α n))) := rfl
      _ = (d m).comp (((S.tr h).comp (S.alg n).mul).comp ((α n).tensor (α n))) := by
          rw [hqd]; rfl
      _ = (d m).comp ((S.alg m).mul.comp (((S.tr h).comp (α n)).tensor ((S.tr h).comp (α n)))) := by
          rw [(S.isHom_tr h).1, Hom.tensor_comp]; rfl
      _ = sys m := by rw [hc]
  obtain ⟨μ, hμ⟩ := (toHomSystem_bijective I (N.tensor N) N).2 ⟨sys, hsys⟩
  have hμn : ∀ n, (N.quotHom (I ^ n)).comp μ = sys n := fun n ↦
    congrArg (fun s : HomSystem (N.tensor N) N I ↦ s.1 n) hμ
  have hαμ : ∀ n, (α n).comp μ = (S.alg n).mul.comp ((α n).tensor (α n)) := fun n ↦ by
    calc (α n).comp μ = ((e n).comp (N.quotHom (I ^ n))).comp μ := by rw [he]
      _ = (e n).comp (sys n) := by rw [Hom.comp_assoc, hμn]
      _ = ((e n).comp (d n)).comp ((S.alg n).mul.comp ((α n).tensor (α n))) := rfl
      _ = _ := by rw [hed, Hom.id_comp]
  have hαμ0 : ∀ n w, (α n).f0 (μ.f0 w) = (S.alg n).mul.f0 (((α n).tensor (α n)).f0 w) :=
    fun n w ↦ Hom.f0_eq_of_eq (hαμ n) w
  have hαμ1 : ∀ n w, (α n).f1 (μ.f1 w) = (S.alg n).mul.f1 (((α n).tensor (α n)).f1 w) :=
    fun n w ↦ Hom.f1_eq_of_eq (hαμ n) w
  -- the unit
  let oneSys : N.H0System I := ⟨fun n ↦ (d n).mapH0 (S.alg n).one, fun m n h ↦ by
    rw [← Hom.mapH0_comp, hqd m n h, Hom.mapH0_comp, (S.isHom_tr h).2]⟩
  obtain ⟨one, hone⟩ := (N.H0ToSystem_bijective I).2 oneSys
  have hαone : ∀ n, (α n).mapH0 one = (S.alg n).one := fun n ↦ by
    have h1 : (N.quotHom (I ^ n)).mapH0 one = (d n).mapH0 (S.alg n).one := by
      rw [← H0ToSystem_apply, hone]
    rw [← he, Hom.mapH0_comp, h1, ← Hom.mapH0_comp, hed, Hom.mapH0_id]
  have hαone0 : ∀ n, (α n).f0 one.1.1 = (S.alg n).one.1.1 := fun n ↦
    congrArg (fun x : (S.M n).H0 ↦ x.1.1) (hαone n)
  have hαone1 : ∀ n, (α n).f1 one.1.2 = (S.alg n).one.1.2 := fun n ↦
    congrArg (fun x : (S.M n).H0 ↦ x.1.2) (hαone n)
  -- the axioms
  have hαμ0' : ∀ n (a b : N.M0), (α n).f0 (μ.f0 (tm _ _ a b)) =
      (S.alg n).mul.f0 (tm _ _ ((α n).f0 a) ((α n).f0 b)) := fun n a b ↦ hαμ0 n _
  have hαμ1' : ∀ n (a b : N.M1), (α n).f1 (μ.f1 (tm _ _ a b)) =
      (S.alg n).mul.f1 (tm _ _ ((α n).f1 a) ((α n).f1 b)) := fun n a b ↦ hαμ1 n _
  have hassoc : μ.comp (μ.tensor (Hom.id N)) =
      μ.comp (((Hom.id N).tensor μ).comp (assoc N N N)) := by
    refine inj _ _ fun n ↦ Hom.ext_of_f0_f1 (ext3 fun a b c ↦ ?_) (ext3 fun a b c ↦ ?_)
    · change (α n).f0 (μ.f0 (tm _ _ (μ.f0 (tm _ _ a b)) c)) =
        (α n).f0 (μ.f0 (tm _ _ a (μ.f0 (tm _ _ b c))))
      rw [hαμ0', hαμ0', hαμ0', hαμ0']
      exact (S.alg n).mul_assoc0 _ _ _
    · change (α n).f1 (μ.f1 (tm _ _ (μ.f1 (tm _ _ a b)) c)) =
        (α n).f1 (μ.f1 (tm _ _ a (μ.f1 (tm _ _ b c))))
      rw [hαμ1', hαμ1', hαμ1', hαμ1']
      exact (S.alg n).mul_assoc1 _ _ _
  have hcomm : μ.comp (braid N N) = μ := by
    refine inj _ _ fun n ↦ Hom.ext_of_f0_f1 (BTensor.ext fun a b ↦ ?_) (BTensor.ext fun a b ↦ ?_)
    · change (α n).f0 (μ.f0 (tm _ _ b a)) = (α n).f0 (μ.f0 (tm _ _ a b))
      rw [hαμ0', hαμ0']
      exact (S.alg n).mul_comm0 _ _
    · change (α n).f1 (μ.f1 (tm _ _ b a)) = (α n).f1 (μ.f1 (tm _ _ a b))
      rw [hαμ1', hαμ1']
      exact (S.alg n).mul_comm1 _ _
  have hone_mul : μ.ofSection one = Hom.id N := by
    refine inj _ _ fun n ↦ Hom.ext_of_f0_f1 (LinearMap.ext fun a ↦ ?_) (LinearMap.ext fun a ↦ ?_)
    · change (α n).f0 (μ.f0 (tm _ _ one.1.1 a)) = (α n).f0 a
      rw [hαμ0', hαone0]
      exact (S.alg n).one_mul0 _
    · change (α n).f1 (μ.f1 (tm _ _ one.1.2 a)) = (α n).f1 a
      rw [hαμ1', hαone1]
      exact (S.alg n).one_mul1 _
  refine ⟨N, h0, h1,
    { mul := μ
      one := one
      mul_assoc0 := fun a b c ↦ Hom.f0_eq_of_eq hassoc (tm _ _ (tm _ _ a b) c)
      mul_assoc1 := fun a b c ↦ Hom.f1_eq_of_eq hassoc (tm _ _ (tm _ _ a b) c)
      mul_comm0 := fun a b ↦ (Hom.f0_eq_of_eq hcomm (tm _ _ b a))
      mul_comm1 := fun a b ↦ (Hom.f1_eq_of_eq hcomm (tm _ _ b a))
      one_mul0 := fun a ↦ Hom.f0_eq_of_eq hone_mul a
      one_mul1 := fun a ↦ Hom.f1_eq_of_eq hone_mul a },
    α, hα, hc, fun n ↦ ⟨hαμ n, hαone n⟩⟩

end AdicChartAlgSystem

end ProjectiveLine
