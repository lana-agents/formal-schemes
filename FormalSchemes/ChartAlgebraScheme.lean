/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleAlgebra
import FormalSchemes.ChartedSchemeDatumScheme

/-!
# The scheme of a chart algebra

A commutative chart algebra `B : ProjectiveLine.ChartModule.AlgStr M` (a quasi-coherent
`𝒪_{ℙ¹_A}`-algebra given on the two standard charts) has commutative rings of sections
`B.Ring0`, `B.Ring1` over `Spec A[X]`, `Spec A[Y]` and `B.Ring01` over the overlap, with ring maps
`B.r0Hom`, `B.r1Hom` which are the localizations at the images `B.X0`, `B.X1` of the chart
coordinates (`B.isLocalization_r0`, `B.isLocalization_r1`). Gluing `Spec B.Ring0` and
`Spec B.Ring1` along these localizations (`AlgebraicGeometry.ChartedSchemeDatum.ofTwoPatch`) gives
the scheme `B.scheme`, the relative spectrum of the algebra over `ℙ¹_A`, with its two affine charts
`B.schemeι`.

Together with `ProjectiveLine.AdicChartAlgSystem.exists_algebraization` this turns an adic system
of coherent algebras on `ℙ¹_{A/Iⁿ}` into a scheme over the algebraization.
-/

universe u

open Polynomial TensorProduct AlgebraicGeometry

namespace ProjectiveLine

namespace ChartModule

open BTensor

variable {A : Type u} [CommRing A]

section Generic

variable {P : Type u} [AddCommGroup P] [Module A P] (f : P →ₗ[A] P) (μ : BTensor f f →ₗ[A] P)
  (e : P)

/-- `P` with the multiplication `μ` and the unit `e`. -/
@[nolint unusedArguments]
def MulRing (_μ : BTensor f f →ₗ[A] P) (_e : P) : Type u := P

variable {f μ e}

/-- The commutative ring structure of `MulRing f μ e`. -/
noncomputable abbrev mulRingCommRing
    (hassoc : ∀ a b c, μ (tm f f (μ (tm f f a b)) c) = μ (tm f f a (μ (tm f f b c))))
    (hcomm : ∀ a b, μ (tm f f a b) = μ (tm f f b a)) (hone : ∀ a, μ (tm f f e a) = a) :
    CommRing (MulRing f μ e) :=
  { (inferInstance : AddCommGroup P) with
    mul := fun a b ↦ μ (tm f f a b)
    one := e
    mul_assoc := hassoc
    one_mul := hone
    mul_one := fun a ↦ (hcomm a e).trans (hone a)
    left_distrib := fun a b c ↦
      (congrArg μ (tm_add_right (f := f) (g := f) (p := a) (q := b) (q' := c))).trans
        (map_add μ _ _)
    right_distrib := fun a b c ↦
      (congrArg μ (tm_add_left (f := f) (g := f) (p := a) (p' := b) (q := c))).trans
        (map_add μ _ _)
    zero_mul := fun a ↦ by
      change μ (tm f f 0 a) = 0
      rw [tm_zero_left, map_zero]
    mul_zero := fun a ↦ by
      change μ (tm f f a 0) = 0
      rw [tm_zero_right, map_zero]
    mul_comm := hcomm }

end Generic

namespace AlgStr

variable {M : ChartModule A} (B : AlgStr M)

/-- The ring of sections over `Spec A[X]`. -/
abbrev Ring0 : Type u := MulRing M.x0 B.mul.f0 B.one.1.1

/-- The ring of sections over `Spec A[Y]`. -/
abbrev Ring1 : Type u := MulRing M.x1 B.mul.f1 B.one.1.2

/-- The ring of sections over the overlap. -/
abbrev Ring01 : Type u :=
  MulRing (M.t : M.M01 →ₗ[A] M.M01) B.mul.f01 (M.r0 B.one.1.1)

noncomputable instance : CommRing B.Ring0 :=
  mulRingCommRing B.mul_assoc0 B.mul_comm0 B.one_mul0

noncomputable instance : CommRing B.Ring1 :=
  mulRingCommRing B.mul_assoc1 B.mul_comm1 B.one_mul1

noncomputable instance : CommRing B.Ring01 :=
  mulRingCommRing B.mul_assoc01 B.mul_comm01 B.one_mul01

lemma mul0_def (a b : B.Ring0) : a * b = B.mul.f0 (tm M.x0 M.x0 a b) := rfl

lemma mul1_def (a b : B.Ring1) : a * b = B.mul.f1 (tm M.x1 M.x1 a b) := rfl

lemma mul01_def (a b : B.Ring01) :
    a * b = B.mul.f01 (tm (M.t : M.M01 →ₗ[A] M.M01) (M.t : M.M01 →ₗ[A] M.M01) a b) := rfl

lemma one0_def : (1 : B.Ring0) = B.one.1.1 := rfl

lemma one1_def : (1 : B.Ring1) = B.one.1.2 := rfl

lemma one01_def : (1 : B.Ring01) = M.r0 B.one.1.1 := rfl

/-- The restriction from `Spec A[X]` to the overlap, a ring map. -/
noncomputable def r0Hom : B.Ring0 →+* B.Ring01 where
  toFun := M.r0
  map_one' := rfl
  map_mul' a b := by
    rw [mul0_def, mul01_def, ← B.mul.comm_r0]
    erw [tensor_r0_tm]
  map_zero' := map_zero M.r0
  map_add' := map_add M.r0

/-- The restriction from `Spec A[Y]` to the overlap, a ring map. -/
noncomputable def r1Hom : B.Ring1 →+* B.Ring01 where
  toFun := M.r1
  map_one' := (TwoCech.mem_H0.1 B.one.2).symm
  map_mul' a b := by
    rw [mul1_def, mul01_def, ← B.mul.comm_r1]
    erw [tensor_r1_tm]
  map_zero' := map_zero M.r1
  map_add' := map_add M.r1

lemma r0Hom_apply (a : B.Ring0) : B.r0Hom a = M.r0 a := rfl

lemma r1Hom_apply (a : B.Ring1) : B.r1Hom a = M.r1 a := rfl

/-- The chart coordinate `X` in `B.Ring0`. -/
noncomputable def X0 : B.Ring0 := M.x0 B.one.1.1

/-- The chart coordinate `Y` in `B.Ring1`. -/
noncomputable def X1 : B.Ring1 := M.x1 B.one.1.2

/-- The coordinate `T` on the overlap. -/
noncomputable def T01 : B.Ring01 := M.t (M.r0 B.one.1.1)

/-- `T⁻¹` on the overlap. -/
noncomputable def Tinv : B.Ring01 := M.t.symm (M.r0 B.one.1.1)

lemma x0_eq_mul (a : B.Ring0) : M.x0 a = B.X0 * a := by
  rw [mul0_def, X0, ← xmul_tm]
  erw [B.mul.comm_x0]
  rw [← mul0_def, ← one0_def, one_mul]

lemma x1_eq_mul (a : B.Ring1) : M.x1 a = B.X1 * a := by
  rw [mul1_def, X1, ← xmul_tm]
  erw [B.mul.comm_x1]
  rw [← mul1_def, ← one1_def, one_mul]

lemma t_eq_mul (z : B.Ring01) : M.t z = B.T01 * z := by
  rw [mul01_def, T01]
  change _ = B.mul.f01 (tm _ _ ((M.t : M.M01 →ₗ[A] M.M01) (M.r0 B.one.1.1)) z)
  rw [← xmul_tm]
  erw [B.mul.comm_t]
  rw [← mul01_def, ← one01_def, one_mul]

lemma T01_mul_Tinv : B.T01 * B.Tinv = 1 := by
  rw [← t_eq_mul, Tinv, LinearEquiv.apply_symm_apply, one01_def]

lemma tsymm_eq_mul (z : B.Ring01) : M.t.symm z = B.Tinv * z := by
  apply M.t.injective
  rw [LinearEquiv.apply_symm_apply, t_eq_mul, ← mul_assoc, T01_mul_Tinv, one_mul]

lemma r0Hom_X0 : B.r0Hom B.X0 = B.T01 := by
  rw [r0Hom_apply, X0, M.r0_x0]
  rfl

lemma r1Hom_X1 : B.r1Hom B.X1 = B.Tinv := by
  rw [r1Hom_apply, X1, M.r1_x1, Tinv, ← one01_def, ← (TwoCech.mem_H0.1 B.one.2)]
  rfl

lemma isUnit_T01 : IsUnit B.T01 :=
  ⟨⟨B.T01, B.Tinv, B.T01_mul_Tinv, by rw [mul_comm]; exact B.T01_mul_Tinv⟩, rfl⟩

lemma isUnit_Tinv : IsUnit B.Tinv :=
  ⟨⟨B.Tinv, B.T01, by rw [mul_comm]; exact B.T01_mul_Tinv, B.T01_mul_Tinv⟩, rfl⟩

lemma x0_pow_eq_mul (k : ℕ) (a : B.Ring0) : (M.x0 ^ k) a = B.X0 ^ k * a := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, x0_eq_mul, pow_succ', mul_assoc]

lemma x1_pow_eq_mul (k : ℕ) (a : B.Ring1) : (M.x1 ^ k) a = B.X1 ^ k * a := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, x1_eq_mul, pow_succ', mul_assoc]

lemma t_pow_eq_mul (k : ℕ) (z : B.Ring01) : (M.t ^ k) z = B.T01 ^ k * z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, ih, t_eq_mul, pow_succ', mul_assoc]

lemma tsymm_pow_eq_mul (k : ℕ) (z : B.Ring01) : (M.t.symm ^ k) z = B.Tinv ^ k * z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, ih, tsymm_eq_mul, pow_succ', mul_assoc]

/-- **The overlap is the localization of the first chart at `X`.** -/
theorem isLocalization_r0 :
    letI := B.r0Hom.toAlgebra
    IsLocalization.Away B.X0 B.Ring01 := by
  letI := B.r0Hom.toAlgebra
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, fun z ↦ ?_, fun {x y} hxy ↦ ?_⟩
  · rintro ⟨_, k, rfl⟩
    change IsUnit (B.r0Hom (B.X0 ^ k))
    rw [map_pow, r0Hom_X0]
    exact B.isUnit_T01.pow k
  · obtain ⟨m, k, hk⟩ := M.exists_r0 z
    refine ⟨⟨m, ⟨B.X0 ^ k, k, rfl⟩⟩, ?_⟩
    change z * B.r0Hom (B.X0 ^ k) = B.r0Hom m
    rw [map_pow, r0Hom_X0, mul_comm, ← t_pow_eq_mul, hk]
    rfl
  · change B.r0Hom x = B.r0Hom y at hxy
    have h0 : B.r0Hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨k, hk⟩ := M.ker_r0 (x - y) h0
    refine ⟨⟨B.X0 ^ k, k, rfl⟩, ?_⟩
    change B.X0 ^ k * x = B.X0 ^ k * y
    rw [← sub_eq_zero, ← mul_sub, ← x0_pow_eq_mul]
    exact hk

/-- **The overlap is the localization of the second chart at `Y`.** -/
theorem isLocalization_r1 :
    letI := B.r1Hom.toAlgebra
    IsLocalization.Away B.X1 B.Ring01 := by
  letI := B.r1Hom.toAlgebra
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, fun z ↦ ?_, fun {x y} hxy ↦ ?_⟩
  · rintro ⟨_, k, rfl⟩
    change IsUnit (B.r1Hom (B.X1 ^ k))
    rw [map_pow, r1Hom_X1]
    exact B.isUnit_Tinv.pow k
  · obtain ⟨m, k, hk⟩ := M.exists_r1 z
    refine ⟨⟨m, ⟨B.X1 ^ k, k, rfl⟩⟩, ?_⟩
    change z * B.r1Hom (B.X1 ^ k) = B.r1Hom m
    rw [map_pow, r1Hom_X1, mul_comm, ← tsymm_pow_eq_mul, hk]
    rfl
  · change B.r1Hom x = B.r1Hom y at hxy
    have h0 : B.r1Hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨k, hk⟩ := M.ker_r1 (x - y) h0
    refine ⟨⟨B.X1 ^ k, k, rfl⟩, ?_⟩
    change B.X1 ^ k * x = B.X1 ^ k * y
    rw [← sub_eq_zero, ← mul_sub, ← x1_pow_eq_mul]
    exact hk

/-- The identification of the two presentations of the overlap,
`B₀[1/X] ≃ B₀₁ ≃ B₁[1/Y]`. -/
noncomputable def overlapEquiv : Localization.Away B.X0 ≃+* Localization.Away B.X1 :=
  letI := B.r0Hom.toAlgebra
  letI := B.r1Hom.toAlgebra
  haveI := B.isLocalization_r0
  haveI := B.isLocalization_r1
  (IsLocalization.algEquiv (Submonoid.powers B.X0) (Localization.Away B.X0)
      B.Ring01).toRingEquiv.trans
    (IsLocalization.algEquiv (Submonoid.powers B.X1) (Localization.Away B.X1)
      B.Ring01).toRingEquiv.symm

/-- The two-chart gluing datum of a chart algebra (the chart ideals are irrelevant here and taken
to be `⊤`). -/
noncomputable def datum : ChartedSchemeDatum.{u} :=
  ChartedSchemeDatum.ofTwoPatch (⊤ : Ideal B.Ring0) B.X0 (⊤ : Ideal B.Ring1) B.X1
    B.overlapEquiv (by simp [Ideal.map_top])

/-- **The scheme of a chart algebra**: `Spec B₀ ∪ Spec B₁`, glued along `Spec B₀[1/X] ≅
Spec B₁[1/Y]`. -/
noncomputable def scheme : Scheme.{u} := B.datum.specScheme

/-- The two affine charts of `B.scheme`. -/
noncomputable def schemeι (i : ULift.{u} Bool) :
    Spec (CommRingCat.of (B.datum.C i)) ⟶ B.scheme :=
  B.datum.specSchemeι i

instance (i : ULift.{u} Bool) : IsOpenImmersion (B.schemeι i) :=
  inferInstanceAs (IsOpenImmersion (B.datum.specSchemeι i))

end AlgStr

end ChartModule

end ProjectiveLine
