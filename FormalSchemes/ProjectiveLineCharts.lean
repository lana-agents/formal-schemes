/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.Laurent

/-!
# The affine charts of the projective line, algebraically

Let `A` be a commutative ring and `S = A[x₀, x₁]`, graded by total degree
(`ProjectiveLine.grading`). The projective line `ℙ¹_A = Proj S` is covered by the basic opens
`D₊(x₀)` and `D₊(x₁)`, whose rings of sections are the degree-zero parts `S_(x₀)` and `S_(x₁)` of
the homogeneous localizations, and their intersection is `D₊(x₀x₁)` with ring `S_(x₀x₁)`.
This file identifies these rings with polynomial and Laurent polynomial rings:

* `ProjectiveLine.chartEquiv A k : S_(x_k) ≃+* A[X]`, dehomogenizing at `x_k = 1`, so that
  `x_{1-k}/x_k ↦ X` (`ProjectiveLine.chartEquiv_mk_X`);
* `ProjectiveLine.overlapEquiv A : S_(x₀x₁) ≃+* A[T;T⁻¹]`, with `x₁/x₀ ↦ T`;
* `ProjectiveLine.overlapEquiv_awayMap_zero`, `ProjectiveLine.overlapEquiv_awayMap_one`: the
  restrictions `S_(x₀) → S_(x₀x₁)` and `S_(x₁) → S_(x₀x₁)` become `p ↦ p(T)` and
  `q ↦ q(T⁻¹)`.

The key identity is homogeneity: for `a` homogeneous of degree `n`,
`a(w v₀, w v₁) = wⁿ a(v₀, v₁)` (`ProjectiveLine.aeval_mul_of_isHomogeneous`); it shows that
`a / x_kⁿ` is the dehomogenization of `a` evaluated at `x_{1-k}/x_k`. This is the computation of
Stacks, Lemma 27.8.3, Tag 01MD (`D₊(f) ≅ Spec S_(f)`) made explicit for `ℙ¹`, as used in Stacks,
Section 30.8, Tag 01XS, for the cohomology of projective space.
-/

universe u

open HomogeneousLocalization

namespace ProjectiveLine

/-- Homogeneity: `a(w v) = wⁿ a(v)` for `a` homogeneous of degree `n`. -/
lemma eval₂_mul_of_isHomogeneous {σ R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) (w : S) (v : σ → S) :
    MvPolynomial.eval₂ f (fun i ↦ w * v i) p = w ^ n * MvPolynomial.eval₂ f v p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [MvPolynomial.eval₂_sum, Finset.mul_sum, MvPolynomial.eval₂_monomial]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdeg : (d.sum fun _ c ↦ c) = n := by
    have := hp (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply] using this
  rw [← hdeg, mul_left_comm]
  congr 1
  simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]

variable (A : Type u) [CommRing A]

/-- The homogeneous coordinate ring `A[x₀, x₁]` of `ℙ¹_A`, graded by total degree. -/
abbrev grading : ℕ → Submodule A (MvPolynomial (Fin 2) A) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) A

noncomputable instance : GradedAlgebra (grading A) := MvPolynomial.gradedAlgebra

variable {A}

lemma X_mem (i : Fin 2) : (MvPolynomial.X i : MvPolynomial (Fin 2) A) ∈ grading A 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X A i)

lemma X_mem' (i : Fin 2) :
    (MvPolynomial.X i : MvPolynomial (Fin 2) A) ∈ grading A (1 • 1) := by
  rw [smul_eq_mul, mul_one]; exact X_mem i

variable (A) in
/-- The constants `A → (A[x₀, x₁])₀`. -/
noncomputable def constZero : A →+* grading A 0 where
  toFun a := ⟨MvPolynomial.C a, (MvPolynomial.mem_homogeneousSubmodule _ _).2
    (MvPolynomial.isHomogeneous_C _ a)⟩
  map_one' := Subtype.ext MvPolynomial.C_1
  map_mul' _ _ := Subtype.ext MvPolynomial.C_mul
  map_zero' := Subtype.ext MvPolynomial.C_0
  map_add' _ _ := Subtype.ext MvPolynomial.C_add

/-- The chart `x_k = 1`: the point `(x_k, x_{1-k}) = (1, X)` of `A[X]`. -/
noncomputable def chartPt (k : Fin 2) : Fin 2 → Polynomial A :=
  fun i ↦ if i = k then 1 else Polynomial.X

/-- Dehomogenization `A[x₀, x₁] → A[X]` at `x_k = 1`, `x_{1-k} = X`. -/
noncomputable def dehom (k : Fin 2) : MvPolynomial (Fin 2) A →+* Polynomial A :=
  MvPolynomial.eval₂Hom Polynomial.C (chartPt k)

lemma dehom_X_self (k : Fin 2) : dehom k (MvPolynomial.X k : MvPolynomial (Fin 2) A) = 1 := by
  simp [dehom, chartPt]

lemma dehom_X_rev (k : Fin 2) :
    dehom k (MvPolynomial.X k.rev : MvPolynomial (Fin 2) A) = Polynomial.X := by
  fin_cases k <;> simp [dehom, chartPt]

/-- The map `S_(x_k) → A[X]`, `a / x_kⁿ ↦ a(1, X)` (dehomogenization). -/
noncomputable def chartToPoly (k : Fin 2) :
    Away (grading A) (MvPolynomial.X k) →+* Polynomial A :=
  (Localization.awayLift (dehom k) (MvPolynomial.X k) (by simp [dehom_X_self])).comp
    (algebraMap _ (Localization.Away (MvPolynomial.X k : MvPolynomial (Fin 2) A)))

/-- The affine coordinate `x_{1-k} / x_k` of the chart `D₊(x_k)`. -/
noncomputable def chartCoord (k : Fin 2) : Away (grading A) (MvPolynomial.X k) :=
  Away.mk (grading A) (X_mem k) 1 (MvPolynomial.X k.rev) (X_mem' k.rev)

/-- The map `A[X] → S_(x_k)`, `X ↦ x_{1-k}/x_k`. -/
noncomputable def polyToChart (k : Fin 2) :
    Polynomial A →+* Away (grading A) (MvPolynomial.X k) :=
  Polynomial.eval₂RingHom ((fromZeroRingHom (grading A) _).comp (constZero A)) (chartCoord k)

lemma val_fromZeroRingHom {x : Submonoid (MvPolynomial (Fin 2) A)} (c : grading A 0) :
    (fromZeroRingHom (grading A) x c).val =
      algebraMap (MvPolynomial (Fin 2) A) (Localization x) c := by
  rw [← Localization.mk_one_eq_algebraMap]
  rfl

lemma chartToPoly_fromZero (k : Fin 2) (a : A) :
    chartToPoly k (fromZeroRingHom (grading A) _ (constZero A a)) = Polynomial.C a := by
  simp only [chartToPoly, RingHom.coe_comp, Function.comp_apply, algebraMap_apply,
    val_fromZeroRingHom]
  erw [IsLocalization.Away.lift_eq]
  simp [dehom, constZero]

lemma chartToPoly_chartCoord (k : Fin 2) :
    chartToPoly k (chartCoord k : Away (grading A) _) = Polynomial.X := by
  simp only [chartToPoly, chartCoord, RingHom.coe_comp, Function.comp_apply, algebraMap_apply,
    Away.val_mk]
  rw [show (⟨MvPolynomial.X k ^ 1, 1, rfl⟩ : Submonoid.powers (MvPolynomial.X k)) =
    ⟨MvPolynomial.X k ^ 1, 1, rfl⟩ from rfl]
  rw [Localization.awayLift_mk (dehom k) (MvPolynomial.X k) _ 1 (by simp [dehom_X_self])]
  simp [dehom_X_rev]

lemma chartToPoly_polyToChart (k : Fin 2) (p : Polynomial A) :
    chartToPoly k (polyToChart k p) = p := by
  have : (chartToPoly k).comp (polyToChart k) = RingHom.id (Polynomial A) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [polyToChart, chartToPoly_fromZero]
    · simp [polyToChart, chartToPoly_chartCoord]
  exact congr($this p)

lemma rev_ne (k : Fin 2) : k.rev ≠ k := by
  fin_cases k <;> decide

lemma eq_rev_of_ne {i k : Fin 2} (h : i ≠ k) : i = k.rev := by
  fin_cases i <;> fin_cases k <;> simp_all

variable (A) in
/-- The localization `S_{x_k}` of `S = A[x₀, x₁]`. -/
abbrev Loc (k : Fin 2) := Localization.Away (MvPolynomial.X k : MvPolynomial (Fin 2) A)

/-- The constants `A → S → S_{x_k}`. -/
noncomputable abbrev locC (k : Fin 2) : A →+* Loc A k :=
  (algebraMap (MvPolynomial (Fin 2) A) (Loc A k)).comp MvPolynomial.C

lemma val_polyToChart (k : Fin 2) (p : Polynomial A) :
    (polyToChart k p).val = Polynomial.eval₂ (locC k) (chartCoord k).val p := by
  have : (algebraMap (Away (grading A) (MvPolynomial.X k)) (Loc A k)).comp (polyToChart k) =
      Polynomial.eval₂RingHom (locC k) (chartCoord k).val := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [polyToChart, val_fromZeroRingHom, constZero, locC]
    · simp [polyToChart]
  exact congr($this p)

lemma algebraMap_X_mul_chartCoord (k : Fin 2) :
    algebraMap (MvPolynomial (Fin 2) A) (Loc A k) (MvPolynomial.X k) *
      (chartCoord k : Away (grading A) _).val =
      algebraMap (MvPolynomial (Fin 2) A) (Loc A k) (MvPolynomial.X k.rev) := by
  rw [chartCoord, Away.val_mk, Localization.mk_eq_mk', mul_comm]
  convert IsLocalization.mk'_spec (Loc A k)
    (MvPolynomial.X k.rev)
    ⟨MvPolynomial.X k ^ 1, (Submonoid.mem_powers_iff _ _).mpr ⟨1, rfl⟩⟩ using 3
  simp

lemma chartToPoly_mk (k : Fin 2) (n : ℕ) (a : MvPolynomial (Fin 2) A) (ha) :
    chartToPoly k (Away.mk (grading A) (X_mem k) n a ha) = dehom k a := by
  simp only [chartToPoly, RingHom.coe_comp, Function.comp_apply, algebraMap_apply, Away.val_mk]
  rw [Localization.awayLift_mk (dehom k) (MvPolynomial.X k) a 1 (by simp [dehom_X_self]) n]
  simp

lemma polyToChart_chartToPoly (k : Fin 2) (x : Away (grading A) (MvPolynomial.X k)) :
    polyToChart k (chartToPoly k x) = x := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading A) (X_mem k) x
  apply val_injective
  rw [chartToPoly_mk, val_polyToChart, Away.val_mk]
  set y := (chartCoord k : Away (grading A) _).val
  set w := algebraMap (MvPolynomial (Fin 2) A) (Loc A k) (MvPolynomial.X k)
  let v : Fin 2 → Loc A k := fun i ↦ if i = k then 1 else y
  have h2 : (Polynomial.eval₂RingHom (locC k) y).comp (dehom k) =
      MvPolynomial.eval₂Hom (locC k) v := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [dehom]
    · intro i
      by_cases hi : i = k <;> simp [dehom, chartPt, v, hi]
  have h3 : algebraMap (MvPolynomial (Fin 2) A) (Loc A k) =
      MvPolynomial.eval₂Hom (locC k) (fun i ↦ w * v i) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i
      by_cases hi : i = k
      · subst hi; simp [v, w]
      · rw [eq_rev_of_ne hi]
        simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, v,
          if_neg (rev_ne k), ← algebraMap_X_mul_chartCoord, w, y]
  have hhom : a.IsHomogeneous n := by
    have := (MvPolynomial.mem_homogeneousSubmodule _ _).1 ha
    simpa using this
  have h4 := congr($h3 a)
  simp only [MvPolynomial.coe_eval₂Hom] at h4
  rw [eval₂_mul_of_isHomogeneous _ hhom] at h4
  have h5 : Polynomial.eval₂ (locC k) y (dehom k a) = MvPolynomial.eval₂ (locC k) v a :=
    congr($h2 a)
  rw [h5, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq, h4, mul_comm]
  simp [w]

/-- **The chart `D₊(x_k)` of `ℙ¹_A` is the affine line**: `S_(x_k) ≃ A[X]`, `x_{1-k}/x_k ↦ X`. -/
noncomputable def chartEquiv (k : Fin 2) : Away (grading A) (MvPolynomial.X k) ≃+* Polynomial A :=
  RingEquiv.ofRingHom (chartToPoly k) (polyToChart k)
    (RingHom.ext (chartToPoly_polyToChart k)) (RingHom.ext (polyToChart_chartToPoly k))

@[simp] lemma chartEquiv_apply (k : Fin 2) (x : Away (grading A) (MvPolynomial.X k)) :
    chartEquiv k x = chartToPoly k x := rfl

@[simp] lemma chartEquiv_symm_apply (k : Fin 2) (p) :
    (chartEquiv (A := A) k).symm p = polyToChart k p := rfl

lemma chartEquiv_chartCoord (k : Fin 2) :
    chartEquiv k (chartCoord k : Away (grading A) _) = Polynomial.X :=
  chartToPoly_chartCoord k

lemma chartEquiv_fromZero (k : Fin 2) (a : A) :
    chartEquiv k (fromZeroRingHom (grading A) _ (constZero A a)) = Polynomial.C a :=
  chartToPoly_fromZero k a

/-! ### The overlap `D₊(x₀x₁)` -/

lemma X01_eq : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) A) =
    MvPolynomial.X 0 * MvPolynomial.X 1 := rfl

lemma X01_eq' : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) A) =
    MvPolynomial.X 1 * MvPolynomial.X 0 := mul_comm _ _

variable (A) in
/-- The restriction `S_(x₀) → S_(x₀x₁)`. -/
noncomputable abbrev awayRes0 : Away (grading A) (MvPolynomial.X 0) →+*
    Away (grading A) (MvPolynomial.X 0 * MvPolynomial.X 1) :=
  awayMap (grading A) (X_mem 1) X01_eq

variable (A) in
/-- The restriction `S_(x₁) → S_(x₀x₁)`. -/
noncomputable abbrev awayRes1 : Away (grading A) (MvPolynomial.X 1) →+*
    Away (grading A) (MvPolynomial.X 0 * MvPolynomial.X 1) :=
  awayMap (grading A) (X_mem 0) X01_eq'

lemma isLocalizationElem_eq :
    Away.isLocalizationElem (X_mem (A := A) 0) (X_mem 1) = chartCoord 0 := by
  apply val_injective
  simp [chartCoord, Away.val_mk]

lemma isLocalization_awayRes0 :
    letI := (awayRes0 A).toAlgebra
    IsLocalization.Away (chartCoord 0 : Away (grading A) _)
      (Away (grading A) (MvPolynomial.X 0 * MvPolynomial.X 1)) := by
  rw [← isLocalizationElem_eq]
  exact Away.isLocalization_mul (X_mem 0) (X_mem 1) X01_eq one_ne_zero

/-- **The overlap of the two charts of `ℙ¹_A` is `Spec A[T, T⁻¹]`**: `S_(x₀x₁) ≃ A[T;T⁻¹]`,
`x₁/x₀ ↦ T`. -/
noncomputable def overlapEquiv :
    Away (grading A) (MvPolynomial.X 0 * MvPolynomial.X 1) ≃+* LaurentPolynomial A :=
  letI := (awayRes0 A).toAlgebra
  haveI := isLocalization_awayRes0 (A := A)
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (chartCoord 0))
    (T := Submonoid.powers (Polynomial.X : Polynomial A)) _ _ (chartEquiv 0) (by
      rw [Submonoid.map_powers]
      congr 1
      exact chartEquiv_chartCoord 0)

lemma overlapEquiv_awayRes0 (x : Away (grading A) (MvPolynomial.X 0)) :
    overlapEquiv (awayRes0 A x) = Polynomial.toLaurent (chartEquiv 0 x) := by
  letI := (awayRes0 A).toAlgebra
  haveI := isLocalization_awayRes0 (A := A)
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent]
  exact IsLocalization.ringEquivOfRingEquiv_eq _ x

lemma awayRes0_mul_awayRes1 :
    awayRes0 A (chartCoord 0) * awayRes1 A (chartCoord 1) = 1 := by
  apply val_injective
  simp only [chartCoord, val_mul, val_one, Away.val_mk, awayMap_mk, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, mul_one]
  rw [show (Fin.rev 0 : Fin 2) = 1 from rfl, show (Fin.rev 1 : Fin 2) = 0 from rfl]
  ring

lemma overlapEquiv_awayRes1_chartCoord :
    overlapEquiv (awayRes1 A (chartCoord 1)) = LaurentPolynomial.T (-1) := by
  have h := congr(overlapEquiv $(awayRes0_mul_awayRes1 (A := A)))
  rw [map_mul, map_one, overlapEquiv_awayRes0, chartEquiv_chartCoord, Polynomial.toLaurent_X] at h
  calc overlapEquiv (awayRes1 A (chartCoord 1))
      = LaurentPolynomial.T (-1) *
          (LaurentPolynomial.T 1 * overlapEquiv (awayRes1 A (chartCoord 1))) := by
        rw [← mul_assoc, ← LaurentPolynomial.T_add]; simp
    _ = LaurentPolynomial.T (-1) := by rw [h, mul_one]

lemma overlapEquiv_awayRes1 (x : Away (grading A) (MvPolynomial.X 1)) :
    overlapEquiv (awayRes1 A x) =
      LaurentPolynomial.invert (Polynomial.toLaurent (chartEquiv 1 x)) := by
  obtain ⟨p, rfl⟩ := (chartEquiv (A := A) 1).symm.surjective x
  rw [RingEquiv.apply_symm_apply]
  have key : ((overlapEquiv : _ ≃+* LaurentPolynomial A) : _ →+* _).comp
      ((awayRes1 A).comp (polyToChart 1)) =
      (LaurentPolynomial.invert (R := A)).toRingEquiv.toRingHom.comp
        Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext
    · intro a
      have h0 := overlapEquiv_awayRes0 (fromZeroRingHom (grading A) _ (constZero A a))
      rw [awayMap_fromZeroRingHom, chartEquiv_fromZero] at h0
      simp [polyToChart, awayMap_fromZeroRingHom, h0]
    · simp [polyToChart, overlapEquiv_awayRes1_chartCoord]
  simpa using congr($key p)

end ProjectiveLine
