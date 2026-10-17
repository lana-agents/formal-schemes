/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartAlgebraOfRings
import FormalSchemes.ProjectiveLineGlue

/-!
# The chart rings of an affine morphism to `ℙ¹_A`

An affine morphism `f : Y ⟶ ℙ¹_A` gives two-chart rings (`ProjectiveLine.TwoChartRings`): the
rings of sections of `Y` over `f⁻¹ U₀`, `f⁻¹ U₁` and `f⁻¹ (U₀ ∩ U₁)`, with the pulled-back chart
coordinates and restriction maps (`ProjectiveLine.twoChartRingsOfAffine`). The localization axioms
hold because `U₀ ∩ U₁` is the basic open of the chart coordinate in `U₀` (and in `U₁`)
(`ProjectiveLine.basicOpen_coord_zero`), so its preimage is a basic open of the affine
`f⁻¹ U_k` (Mathlib, `AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen`). Composing
with `ProjectiveLine.TwoChartRings.algStr`, the pushforward `f_* 𝒪_Y` is a chart algebra on `ℙ¹_A`.
-/

universe u

open AlgebraicGeometry CategoryTheory Polynomial
open scoped LaurentPolynomial

namespace ProjectiveLine

variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ scheme A)

/-- The pullback of functions on the `k`-th chart, `A[X] → Γ(Y, f⁻¹ U_k)`. -/
noncomputable def chartPullback (k : Fin 2) : A[X] →+* Γ(Y, f ⁻¹ᵁ U A k) :=
  (f.app (U A k)).hom.comp (chartSections A k).symm.toRingHom

/-- The pullback of functions on the overlap, `A[T, T⁻¹] → Γ(Y, f⁻¹ (U₀ ∩ U₁))`. -/
noncomputable def overlapPullback : A[T;T⁻¹] →+* Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1)) :=
  (f.app (U A 0 ⊓ U A 1)).hom.comp (overlapSections A).symm.toRingHom

lemma preimage_inf_le (k : Fin 2) : f ⁻¹ᵁ (U A 0 ⊓ U A 1) ≤ f ⁻¹ᵁ U A k :=
  f.preimage_mono (by fin_cases k; exacts [inf_le_left, inf_le_right])

/-- The restriction `Γ(Y, f⁻¹ U_k) → Γ(Y, f⁻¹ (U₀ ∩ U₁))`. -/
noncomputable def preimageRes (k : Fin 2) : Γ(Y, f ⁻¹ᵁ U A k) →+* Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1)) :=
  (Y.presheaf.map (homOfLE (preimage_inf_le f k)).op).hom

lemma preimageRes_app (k : Fin 2) (s : Γ(scheme A, U A k)) :
    preimageRes f k (f.app (U A k) s) = f.app (U A 0 ⊓ U A 1) (ρ A k s) :=
  (ConcreteCategory.congr_hom (f.naturality (homOfLE (show U A 0 ⊓ U A 1 ≤ U A k by
    fin_cases k; exacts [inf_le_left, inf_le_right])).op) s).symm

lemma preimageRes_chartPullback_zero (p : A[X]) :
    preimageRes f 0 (chartPullback f 0 p) = overlapPullback f (toLaurent p) := by
  rw [chartPullback, RingHom.comp_apply, preimageRes_app, overlapPullback, RingHom.comp_apply]
  congr 1
  apply (overlapSections A).injective
  change overlapSections A ((scheme A).presheaf.map (homOfLE inf_le_left).op
    ((chartSections A 0).symm p)) = overlapSections A ((overlapSections A).symm (toLaurent p))
  rw [overlapSections_res_zero, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

lemma preimageRes_chartPullback_one (q : A[X]) :
    preimageRes f 1 (chartPullback f 1 q) =
      overlapPullback f (LaurentPolynomial.invert (toLaurent q)) := by
  rw [chartPullback, RingHom.comp_apply, preimageRes_app, overlapPullback, RingHom.comp_apply]
  congr 1
  apply (overlapSections A).injective
  change overlapSections A ((scheme A).presheaf.map (homOfLE inf_le_right).op
    ((chartSections A 1).symm q)) =
      overlapSections A ((overlapSections A).symm (LaurentPolynomial.invert (toLaurent q)))
  rw [overlapSections_res_one, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

lemma chartPullback_X (k : Fin 2) : chartPullback f k X = f.app (U A k) (coord A k) := by
  rw [chartPullback, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    ← chartSections_coord, RingEquiv.symm_apply_apply]

lemma preimage_inf_eq_basicOpen (k : Fin 2) [IsAffineHom f] :
    f ⁻¹ᵁ (U A 0 ⊓ U A 1) = Y.basicOpen (chartPullback f k X) := by
  rw [chartPullback_X, ← Scheme.preimage_basicOpen]
  fin_cases k
  · exact congrArg _ basicOpen_coord_zero.symm
  · exact congrArg _ basicOpen_coord_one.symm

lemma isLocalization_preimageRes (k : Fin 2) [IsAffineHom f] :
    letI := (preimageRes f k).toAlgebra
    IsLocalization.Away (chartPullback f k X) Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1)) :=
  ((isAffineOpen_U A k).preimage f).isLocalization_of_eq_basicOpen _
    (homOfLE (preimage_inf_le f k)) (preimage_inf_eq_basicOpen f k)

/-- The image of `T` on the overlap, a unit. -/
noncomputable def overlapUnit : Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1))ˣ :=
  Units.map (overlapPullback f : A[T;T⁻¹] →* _) (LaurentPolynomial.isUnit_T 1).unit

lemma overlapUnit_val : (overlapUnit f : Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1))) =
    overlapPullback f (LaurentPolynomial.T 1) := rfl

lemma overlapUnit_inv_val : (↑(overlapUnit f)⁻¹ : Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1))) =
    overlapPullback f (LaurentPolynomial.T (-1)) := by
  exact Units.inv_eq_of_mul_eq_one_right (by
    rw [overlapUnit_val, ← map_mul, ← LaurentPolynomial.T_add, add_neg_cancel,
      LaurentPolynomial.T_zero, map_one])

lemma preimageRes_zero_X : preimageRes f 0 (chartPullback f 0 X) = overlapUnit f := by
  rw [preimageRes_chartPullback_zero, Polynomial.toLaurent_X, overlapUnit_val]

lemma preimageRes_one_X : preimageRes f 1 (chartPullback f 1 X) = ↑(overlapUnit f)⁻¹ := by
  rw [preimageRes_chartPullback_one, Polynomial.toLaurent_X, LaurentPolynomial.invert_T,
    overlapUnit_inv_val]

lemma exists_preimageRes (k : Fin 2) [IsAffineHom f] (z : Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1))) :
    ∃ (m : Γ(Y, f ⁻¹ᵁ U A k)) (n : ℕ),
      preimageRes f k (chartPullback f k X) ^ n * z = preimageRes f k m := by
  letI := (preimageRes f k).toAlgebra
  haveI := isLocalization_preimageRes f k
  obtain ⟨⟨m, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (chartPullback f k X)) z
  refine ⟨m, n, ?_⟩
  rw [mul_comm, ← map_pow]
  exact h

lemma exists_pow_mul_eq_zero (k : Fin 2) [IsAffineHom f] (m : Γ(Y, f ⁻¹ᵁ U A k))
    (hm : preimageRes f k m = 0) : ∃ n : ℕ, chartPullback f k X ^ n * m = 0 := by
  letI := (preimageRes f k).toAlgebra
  haveI := isLocalization_preimageRes f k
  obtain ⟨⟨_, n, rfl⟩, h⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (chartPullback f k X)) _ m).1 hm
  exact ⟨n, h⟩

/-- **The two-chart rings of an affine morphism `f : Y ⟶ ℙ¹_A`**: sections of `Y` over the
preimages of the charts and of their overlap. -/
noncomputable def twoChartRingsOfAffine [IsAffineHom f] : TwoChartRings A :=
  letI : Algebra A Γ(Y, f ⁻¹ᵁ U A 0) := ((chartPullback f 0).comp C).toAlgebra
  letI : Algebra A Γ(Y, f ⁻¹ᵁ U A 1) := ((chartPullback f 1).comp C).toAlgebra
  letI : Algebra A Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1)) :=
    ((overlapPullback f).comp LaurentPolynomial.C).toAlgebra
  { R0 := Γ(Y, f ⁻¹ᵁ U A 0)
    R1 := Γ(Y, f ⁻¹ᵁ U A 1)
    R01 := Γ(Y, f ⁻¹ᵁ (U A 0 ⊓ U A 1))
    x := chartPullback f 0 X
    y := chartPullback f 1 X
    u := overlapUnit f
    ρ0 :=
      { preimageRes f 0 with
        commutes' := fun a ↦ by
          change preimageRes f 0 (chartPullback f 0 (C a)) = overlapPullback f _
          rw [preimageRes_chartPullback_zero, Polynomial.toLaurent_C] }
    ρ1 :=
      { preimageRes f 1 with
        commutes' := fun a ↦ by
          change preimageRes f 1 (chartPullback f 1 (C a)) = overlapPullback f _
          rw [preimageRes_chartPullback_one, Polynomial.toLaurent_C,
            LaurentPolynomial.invert_C] }
    ρ0_x := preimageRes_zero_X f
    ρ1_y := preimageRes_one_X f
    exists0 := fun z ↦ by
      obtain ⟨m, n, h⟩ := exists_preimageRes f 0 z
      exact ⟨m, n, by rw [← preimageRes_zero_X]; exact h⟩
    ker0 := exists_pow_mul_eq_zero f 0
    exists1 := fun z ↦ by
      obtain ⟨m, n, h⟩ := exists_preimageRes f 1 z
      exact ⟨m, n, by rw [← preimageRes_one_X]; exact h⟩
    ker1 := exists_pow_mul_eq_zero f 1 }

/-- **The pushforward of `𝒪_Y` along an affine `f : Y ⟶ ℙ¹_A`, as a chart algebra.** -/
noncomputable def algStrOfAffine [IsAffineHom f] :
    ChartModule.AlgStr (twoChartRingsOfAffine f).chartModule :=
  (twoChartRingsOfAffine f).algStr

end ProjectiveLine
