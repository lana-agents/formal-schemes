/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartAlgebraScheme

/-!
# Chart algebras from rings on the two charts

The converse direction of `ProjectiveLine.ChartModule.AlgStr.isLocalization_r0`: commutative
`A`-algebras `R₀`, `R₁` (sections over `Spec A[X]`, `Spec A[Y]` of a quasi-coherent algebra) with
elements `x`, `y` (the images of the chart coordinates), an `A`-algebra `R₀₁` with a unit `u` (the
image of `T`) and `A`-algebra maps `ρ₀ : R₀ → R₀₁`, `ρ₁ : R₁ → R₀₁` with `ρ₀ x = u`, `ρ₁ y = u⁻¹`,
which are the localizations at `x` and `y` (`ProjectiveLine.TwoChartRings`), define a chart
module (`TwoChartRings.chartModule`) with a commutative algebra structure
(`TwoChartRings.algStr`), whose rings of sections are `R₀`, `R₁`, `R₀₁`.

For an affine morphism `𝒴 → ℙ¹_A`, the rings of sections of `𝒴` over the preimages of the charts
and of their overlap form such a datum; this is the input format for the bridge from finite
coverings of a model `𝒳 → ℙ¹` to chart algebras.
-/

universe u

open Polynomial TensorProduct

namespace ProjectiveLine

open ChartModule BTensor

variable (A : Type u) [CommRing A]

/-- **Rings on the two charts of `ℙ¹_A`**, glued along the overlap. -/
structure TwoChartRings where
  /-- sections over `Spec A[X]` -/
  R0 : Type u
  /-- sections over `Spec A[Y]` -/
  R1 : Type u
  /-- sections over the overlap -/
  R01 : Type u
  [cR0 : CommRing R0]
  [cR1 : CommRing R1]
  [cR01 : CommRing R01]
  [aR0 : Algebra A R0]
  [aR1 : Algebra A R1]
  [aR01 : Algebra A R01]
  /-- the image of `X` -/
  x : R0
  /-- the image of `Y` -/
  y : R1
  /-- the image of `T` -/
  u : R01ˣ
  /-- restriction from `Spec A[X]` -/
  ρ0 : R0 →ₐ[A] R01
  /-- restriction from `Spec A[Y]` -/
  ρ1 : R1 →ₐ[A] R01
  ρ0_x : ρ0 x = u
  ρ1_y : ρ1 y = ↑u⁻¹
  exists0 : ∀ z, ∃ (m : R0) (k : ℕ), (u : R01) ^ k * z = ρ0 m
  ker0 : ∀ m, ρ0 m = 0 → ∃ k : ℕ, x ^ k * m = 0
  exists1 : ∀ z, ∃ (m : R1) (k : ℕ), (↑u⁻¹ : R01) ^ k * z = ρ1 m
  ker1 : ∀ m, ρ1 m = 0 → ∃ k : ℕ, y ^ k * m = 0

namespace TwoChartRings

attribute [instance] cR0 cR1 cR01 aR0 aR1 aR01

variable {A} (D : TwoChartRings A)

/-- Multiplication by the unit `u`, as an `A`-linear automorphism. -/
def mulU : D.R01 ≃ₗ[A] D.R01 where
  toLinearMap := LinearMap.mulLeft A (D.u : D.R01)
  invFun z := ↑D.u⁻¹ * z
  left_inv z := by simp
  right_inv z := by simp

lemma mulU_apply (z : D.R01) : D.mulU z = D.u * z := rfl

lemma mulU_symm_apply (z : D.R01) : D.mulU.symm z = ↑D.u⁻¹ * z := rfl

lemma mulU_pow_apply (k : ℕ) (z : D.R01) : (D.mulU ^ k) z = (D.u : D.R01) ^ k * z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, ih, mulU_apply, pow_succ', mul_assoc]

lemma mulU_symm_pow_apply (k : ℕ) (z : D.R01) :
    (D.mulU.symm ^ k) z = (↑D.u⁻¹ : D.R01) ^ k * z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, ih, mulU_symm_apply, pow_succ', mul_assoc]

lemma mulLeft_pow_apply {R : Type u} [CommRing R] [Algebra A R] (r : R) (k : ℕ) (m : R) :
    (LinearMap.mulLeft A r ^ k) m = r ^ k * m := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, LinearMap.mulLeft_apply, pow_succ', mul_assoc]

/-- **The chart module of `D`.** -/
noncomputable abbrev chartModule : ChartModule A where
  M0 := ModuleCat.of A D.R0
  M1 := ModuleCat.of A D.R1
  M01 := ModuleCat.of A D.R01
  x0 := LinearMap.mulLeft A D.x
  x1 := LinearMap.mulLeft A D.y
  t := D.mulU
  r0 := D.ρ0.toLinearMap
  r1 := D.ρ1.toLinearMap
  r0_x0 m := by
    change D.ρ0 (D.x * m) = D.u * D.ρ0 m
    rw [map_mul, D.ρ0_x]
  r1_x1 m := by
    change D.ρ1 (D.y * m) = ↑D.u⁻¹ * D.ρ1 m
    rw [map_mul, D.ρ1_y]
  exists_r0 z := by
    obtain ⟨m, k, h⟩ := D.exists0 z
    exact ⟨m, k, by rw [mulU_pow_apply]; exact h⟩
  ker_r0 m hm := by
    obtain ⟨k, h⟩ := D.ker0 m hm
    exact ⟨k, by rw [mulLeft_pow_apply]; exact h⟩
  exists_r1 z := by
    obtain ⟨m, k, h⟩ := D.exists1 z
    exact ⟨m, k, by rw [mulU_symm_pow_apply]; exact h⟩
  ker_r1 m hm := by
    obtain ⟨k, h⟩ := D.ker1 m hm
    exact ⟨k, by rw [mulLeft_pow_apply]; exact h⟩

variable (A) in
/-- The multiplication of a commutative algebra, as a map out of `BTensor` (the endomorphism being
multiplication by an element). -/
noncomputable def bmul {R : Type u} [CommRing R] [Algebra A R] (r : R) :
    BTensor (LinearMap.mulLeft A r) (LinearMap.mulLeft A r) →ₗ[A] R :=
  blift (LinearMap.mulLeft A r) (LinearMap.mul A R) (fun a b ↦ by simp [mul_assoc])
    (fun a b ↦ by simp [mul_left_comm])

variable (A) in
@[simp] lemma bmul_tm {R : Type u} [CommRing R] [Algebra A R] (r a b : R) :
    bmul A r (tm _ _ a b) = a * b := by
  simp [bmul]

variable (A) in
lemma bmul_xmul {R : Type u} [CommRing R] [Algebra A R] (r : R) (w) :
    bmul A r (xmul _ _ w) = r * bmul A r w :=
  blift_xmul _ _ _ _ w

/-- **The multiplication of `D`**, a morphism of chart modules. -/
noncomputable def mulHom : Hom (D.chartModule.tensor D.chartModule) D.chartModule where
  f0 := bmul A D.x
  f1 := bmul A D.y
  f01 := bmul A (D.u : D.R01)
  comm_x0 w := bmul_xmul A _ w
  comm_x1 w := bmul_xmul A _ w
  comm_t w := bmul_xmul A _ w
  comm_r0 w := by
    induction w using BTensor.induction_on with
    | h0 => simp
    | htm a b =>
      change bmul A (D.u : D.R01) (tm _ _ (D.ρ0 a) (D.ρ0 b)) =
        D.ρ0 (bmul A D.x (tm _ _ a b))
      simp
    | hadd w w' hw hw' => simp only [map_add, hw, hw']
  comm_r1 w := by
    induction w using BTensor.induction_on with
    | h0 => simp
    | htm a b =>
      change bmul A (D.u : D.R01) (tm _ _ (D.ρ1 a) (D.ρ1 b)) =
        D.ρ1 (bmul A D.y (tm _ _ a b))
      simp
    | hadd w w' hw hw' => simp only [map_add, hw, hw']

/-- The unit, a global section. -/
def one : D.chartModule.H0 :=
  ⟨((1 : D.R0), (1 : D.R1)), TwoCech.mem_H0.2 (by
    change D.ρ0 1 = D.ρ1 1
    rw [map_one, map_one])⟩

/-- **The commutative algebra structure of `D`.** -/
noncomputable def algStr : AlgStr D.chartModule where
  mul := D.mulHom
  one := D.one
  mul_assoc0 a b c := by
    change bmul A D.x (tm _ _ (bmul A D.x (tm _ _ a b)) c) =
      bmul A D.x (tm _ _ a (bmul A D.x (tm _ _ b c)))
    simp [mul_assoc]
  mul_assoc1 a b c := by
    change bmul A D.y (tm _ _ (bmul A D.y (tm _ _ a b)) c) =
      bmul A D.y (tm _ _ a (bmul A D.y (tm _ _ b c)))
    simp [mul_assoc]
  mul_comm0 a b := by
    change bmul A D.x (tm _ _ a b) = bmul A D.x (tm _ _ b a)
    simp [mul_comm]
  mul_comm1 a b := by
    change bmul A D.y (tm _ _ a b) = bmul A D.y (tm _ _ b a)
    simp [mul_comm]
  one_mul0 a := by
    change bmul A D.x (tm _ _ (1 : D.R0) a) = a
    simp
  one_mul1 a := by
    change bmul A D.y (tm _ _ (1 : D.R1) a) = a
    simp
  mul_assoc01 a b c := by
    change bmul A (D.u : D.R01) (tm _ _ (bmul A (D.u : D.R01) (tm _ _ a b)) c) =
      bmul A (D.u : D.R01) (tm _ _ a (bmul A (D.u : D.R01) (tm _ _ b c)))
    simp [mul_assoc]
  mul_comm01 a b := by
    change bmul A (D.u : D.R01) (tm _ _ a b) = bmul A (D.u : D.R01) (tm _ _ b a)
    simp [mul_comm]
  one_mul01 a := by
    change bmul A (D.u : D.R01) (tm _ _ (D.ρ0 1) a) = a
    simp

end TwoChartRings

end ProjectiveLine
