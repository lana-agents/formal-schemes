import FormalSchemes.FormalGm

set_option linter.style.header false

/-!
# Coefficients of restricted Laurent series

`RestrictedLaurentSeries R I = R{X, X⁻¹}` is the `I`-adic completion of the Laurent polynomial
ring `R[T, T⁻¹]` (`FormalSchemes.FormalGm`). Its API so far consists of the variable `X`, its
unit-ness, and evaluation at units — nothing reads a single coefficient, and there is no
extensionality principle in those terms. This file supplies both, for a base ring that is
`I`-adically complete.

## The construction

`R[T, T⁻¹]` is `AddMonoidAlgebra R ℤ`, i.e. `ℤ →₀ R`, so `LaurentPolynomial.coeffₗ R n` — the
`n`-th coefficient as an `R`-linear map — is `Finsupp.lapply n` transported along
`AddMonoidAlgebra.coeffLinearEquiv`. It carries `K • ⊤` onto `K` in both directions
(`LaurentPolynomial.mem_smul_top_iff_coeffₗ_mem`), so it descends to every level of the
filtration, and the descended maps are compatible with the transition maps. `IsAdicComplete.lift`
then assembles them into `RestrictedLaurentSeries.coeff`.

The one wrinkle is that `RestrictedLaurentSeries R I` is the completion of `R[T, T⁻¹]` at an ideal
**of `R[T, T⁻¹]`**, whereas the coefficient is only `R`-linear. The bridge is
`Ideal.mem_map_pow_iff_mem_smul_top` (`FormalSchemes.RestrictedPowerSeries`): the two filtrations
`(I·R[T,T⁻¹])^m • ⊤` over `R[T,T⁻¹]` and `I^m • ⊤` over `R` have the same underlying set, and
`Submodule.Quotient.restrictScalarsEquiv` turns that into an `R`-linear identification of the two
quotients.

## Main results

* `LaurentPolynomial.coeffₗ`: the `n`-th coefficient of a Laurent polynomial, `R`-linearly, with
  `LaurentPolynomial.coeffₗ_T` and `LaurentPolynomial.coeffₗ_C` its values on the two generating
  families.
* `LaurentPolynomial.mem_smul_top_iff_coeffₗ_mem`: `p ∈ K • ⊤` exactly when every coefficient of
  `p` lies in `K`. Both directions are used — the forward one to descend the coefficient to the
  quotients, the backward one for extensionality.
* `RestrictedLaurentSeries.coeff`: **the `n`-th coefficient of a restricted Laurent series**, an
  `R`-linear map `R{X, X⁻¹} →ₗ[R] R`, for `[IsAdicComplete I R]`.
* `RestrictedLaurentSeries.coeff_X`, `RestrictedLaurentSeries.coeff_algebraMap`,
  `RestrictedLaurentSeries.coeff_one` and `RestrictedLaurentSeries.coeff_algebraMap_mul`: its
  values on `X R I k` and on the structural image of a scalar, and the fact that scalars pull
  out.
* `RestrictedLaurentSeries.coeff_mem_pow`: `coeff` is continuous — a coefficient of an element of
  the `m`-th step of the filtration lies in `I ^ m`. With
  `RestrictedLaurentSeries.exists_sub_mem_smul_top`, the density of `R[T, T⁻¹]`, this is what lets
  an identity between `R`-linear functionals be checked on Laurent polynomials alone.
* **`RestrictedLaurentSeries.ext_coeff`**: a restricted Laurent series is determined by its
  coefficients. With `RestrictedLaurentSeries.coeff_eq_zero_iff` this is the extensionality
  principle `FormalSchemes.FormalGm` lacks.

## What is *not* proved

**Nothing about the Tate curve.** The intended consumer is the coefficientwise comparison of the
two overlap legs of `FormalSchemes.TateInvGlobalProperness`, which needs in addition a
description of the image of `A = R{x, y}/(x·y − q)` in `R{X, X⁻¹}`; that is not attempted here.

**No multiplicativity.** `coeff` is `R`-linear and nothing more; the convolution formula for the
coefficients of a product is not proved and is not needed by the intended consumer.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §8.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.
-/

noncomputable section

open Ideal LaurentPolynomial Submodule

universe u

namespace LaurentPolynomial

variable (R : Type u) [CommRing R]

/-- The `n`-th coefficient of a Laurent polynomial, as an `R`-linear map. `R[T, T⁻¹]` is
`AddMonoidAlgebra R ℤ`, so this is `Finsupp.lapply` transported along
`AddMonoidAlgebra.coeffLinearEquiv`. -/
def coeffₗ (n : ℤ) : LaurentPolynomial R →ₗ[R] R :=
  Finsupp.lapply n ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R (S := R) (M := ℤ)).toLinearMap

@[simp]
theorem coeffₗ_apply (n : ℤ) (p : LaurentPolynomial R) : coeffₗ R n p = p.coeff n := rfl

@[simp]
theorem coeffₗ_T (n k : ℤ) :
    coeffₗ R n (T k : LaurentPolynomial R) = if n = k then 1 else 0 := by
  rw [show coeffₗ R n (T k : LaurentPolynomial R) = Finsupp.single k (1 : R) n from rfl,
    Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

@[simp]
theorem coeffₗ_C (n : ℤ) (r : R) :
    coeffₗ R n (C r : LaurentPolynomial R) = if n = 0 then r else 0 := by
  rw [show coeffₗ R n (C r : LaurentPolynomial R) = Finsupp.single (0 : ℤ) r n from rfl,
    Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

variable {R}

/-- A monomial is a scalar multiple of a power of the variable. -/
theorem single_eq_smul_T (r : R) (n : ℤ) :
    (AddMonoidAlgebra.single n r : LaurentPolynomial R) = r • T n := by
  rw [single_eq_C_mul_T, smul_eq_C_mul]

/-- Every coefficient of an element of `K • ⊤` lies in `K`. The submodule is generated by the
`r • p` with `r ∈ K`, and `coeffₗ` is `R`-linear, so this is `Submodule.smul_induction_on`. -/
theorem coeffₗ_mem_of_mem_smul_top {K : Ideal R} {p : LaurentPolynomial R}
    (hp : p ∈ (K • ⊤ : Submodule R (LaurentPolynomial R))) (n : ℤ) : coeffₗ R n p ∈ K := by
  refine Submodule.smul_induction_on hp ?_ ?_
  · intro r hr x _
    have hsmul : coeffₗ R n (r • x) = r * coeffₗ R n x := by rw [map_smul]; rfl
    rw [hsmul]
    exact K.mul_mem_right _ hr
  · intro x y hx hy
    rw [map_add]
    exact K.add_mem hx hy

/-- Conversely, a Laurent polynomial all of whose coefficients lie in `K` lies in `K • ⊤`: it is
the finite sum of its monomials, and `AddMonoidAlgebra.single n r` is `r • T n`. -/
theorem mem_smul_top_of_coeffₗ_mem {K : Ideal R} {p : LaurentPolynomial R}
    (h : ∀ n, coeffₗ R n p ∈ K) : p ∈ (K • ⊤ : Submodule R (LaurentPolynomial R)) := by
  have hsum : (p.coeff.sum AddMonoidAlgebra.single : LaurentPolynomial R) ∈
      (K • ⊤ : Submodule R (LaurentPolynomial R)) := by
    rw [Finsupp.sum]
    refine Submodule.sum_mem _ fun n _ => ?_
    rw [single_eq_smul_T]
    exact Submodule.smul_mem_smul (h n) Submodule.mem_top
  rwa [AddMonoidAlgebra.sum_coeff_single] at hsum

/-- **`K • ⊤` is cut out coefficientwise.** -/
theorem mem_smul_top_iff_coeffₗ_mem {K : Ideal R} {p : LaurentPolynomial R} :
    p ∈ (K • ⊤ : Submodule R (LaurentPolynomial R)) ↔ ∀ n, coeffₗ R n p ∈ K :=
  ⟨fun hp => coeffₗ_mem_of_mem_smul_top hp, mem_smul_top_of_coeffₗ_mem⟩

end LaurentPolynomial

namespace RestrictedLaurentSeries

variable {R : Type u} [CommRing R] (I : Ideal R)

/-! ### The coefficient at a single level of the filtration -/

/-- The `n`-th coefficient kills the `m`-th step of the filtration, modulo `I ^ m`. The two
filtrations agree by `Ideal.mem_map_pow_iff_mem_smul_top`. -/
theorem le_ker_coeffₗ (n : ℤ) (m : ℕ) :
    Submodule.restrictScalars R
        (((I.map (algebraMap R (LaurentPolynomial R))) ^ m • ⊤ :
          Submodule (LaurentPolynomial R) (LaurentPolynomial R))) ≤
      LinearMap.ker ((I ^ m • ⊤ : Submodule R R).mkQ ∘ₗ coeffₗ R n) := by
  intro p hp
  rw [Submodule.restrictScalars_mem, Ideal.mem_map_pow_iff_mem_smul_top] at hp
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  rw [Ideal.mem_smul_top_self_iff]
  exact LaurentPolynomial.coeffₗ_mem_of_mem_smul_top hp n

/-- The `n`-th coefficient at the `m`-th level of the filtration, as a map of quotients. -/
def coeffQuot (n : ℤ) (m : ℕ) :
    LaurentPolynomial R ⧸ ((I.map (algebraMap R (LaurentPolynomial R))) ^ m • ⊤ :
        Submodule (LaurentPolynomial R) (LaurentPolynomial R)) →ₗ[R]
      R ⧸ (I ^ m • ⊤ : Submodule R R) :=
  Submodule.liftQ _ ((I ^ m • ⊤ : Submodule R R).mkQ ∘ₗ coeffₗ R n) (le_ker_coeffₗ I n m) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R _).symm.toLinearMap

@[simp]
theorem coeffQuot_mk (n : ℤ) (m : ℕ) (p : LaurentPolynomial R) :
    coeffQuot I n m (Submodule.Quotient.mk p) = Submodule.Quotient.mk (coeffₗ R n p) := rfl

/-- The level maps commute with the transition maps of the two filtrations. -/
theorem coeffQuot_transitionMap (n : ℤ) {m k : ℕ} (hle : m ≤ k)
    (w : LaurentPolynomial R ⧸ ((I.map (algebraMap R (LaurentPolynomial R))) ^ k • ⊤ :
      Submodule (LaurentPolynomial R) (LaurentPolynomial R))) :
    coeffQuot I n m (AdicCompletion.transitionMap _ _ hle w) =
      Submodule.factorPow I R hle (coeffQuot I n k w) := by
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rfl

/-- The `n`-th coefficient of a restricted Laurent series, read modulo `I ^ m`. -/
def coeffLevel (n : ℤ) (m : ℕ) :
    RestrictedLaurentSeries R I →ₗ[R] R ⧸ (I ^ m • ⊤ : Submodule R R) :=
  coeffQuot I n m ∘ₗ
    (AdicCompletion.eval (I.map (algebraMap R (LaurentPolynomial R))) (LaurentPolynomial R)
      m).restrictScalars R

@[simp]
theorem coeffLevel_apply (n : ℤ) (m : ℕ) (z : RestrictedLaurentSeries R I) :
    coeffLevel I n m z = coeffQuot I n m (z.val m) := rfl

/-- The levels of the `n`-th coefficient form a compatible family, so they can be lifted. -/
theorem coeffLevel_compat (n : ℤ) {m k : ℕ} (hle : m ≤ k) :
    Submodule.factorPow I R hle ∘ₗ coeffLevel I n k = coeffLevel I n m :=
  LinearMap.ext fun z => by
    rw [LinearMap.comp_apply, coeffLevel_apply, coeffLevel_apply, ← z.property hle,
      coeffQuot_transitionMap]

/-- **The image of `R[T, T⁻¹]` is dense**: every restricted Laurent series agrees with a Laurent
polynomial modulo the `m`-th step of the filtration. This is `AdicCompletion.eval` being
surjective, read through `AdicCompletion.pow_smul_top_eq_ker_eval`. -/
theorem exists_sub_mem_smul_top (hI : I.FG) (m : ℕ) (z : RestrictedLaurentSeries R I) :
    ∃ p : LaurentPolynomial R,
      z - AdicCompletion.of (I.map (algebraMap R (LaurentPolynomial R))) (LaurentPolynomial R) p ∈
        ((I.map (algebraMap R (LaurentPolynomial R))) ^ m • ⊤ :
          Submodule (LaurentPolynomial R) (RestrictedLaurentSeries R I)) := by
  obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective _ (z.val m)
  refine ⟨p, ?_⟩
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (hI.map _), LinearMap.mem_ker, map_sub,
    AdicCompletion.eval_apply, AdicCompletion.eval_of, Submodule.mkQ_apply, ← hp, sub_self]

/-! ### The coefficient itself -/

variable [IsAdicComplete I R]

/-- **The `n`-th coefficient of a restricted Laurent series**, an `R`-linear map
`R{X, X⁻¹} →ₗ[R] R`, for a base ring that is `I`-adically complete. It is the lift of the
compatible family `coeffLevel` along the universal property of `IsAdicComplete`. -/
def coeff (n : ℤ) : RestrictedLaurentSeries R I →ₗ[R] R :=
  IsAdicComplete.lift I (coeffLevel I n) fun hle => coeffLevel_compat I n hle

@[simp]
theorem mk_coeff (n : ℤ) (m : ℕ) (z : RestrictedLaurentSeries R I) :
    (Submodule.Quotient.mk (coeff I n z) : R ⧸ (I ^ m • ⊤ : Submodule R R)) =
      coeffLevel I n m z :=
  IsAdicComplete.mk_lift I (fun hle => coeffLevel_compat I n hle) m z

/-- **The coefficient of the image of a Laurent polynomial is its coefficient.** -/
@[simp]
theorem coeff_of (n : ℤ) (p : LaurentPolynomial R) :
    coeff I n (AdicCompletion.of (I.map (algebraMap R (LaurentPolynomial R)))
      (LaurentPolynomial R) p) = coeffₗ R n p := by
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro m
  rw [SModEq.def, mk_coeff, coeffLevel_apply, AdicCompletion.of_apply, Submodule.mkQ_apply,
    coeffQuot_mk]

/-- **The coefficients of the variable.** -/
@[simp]
theorem coeff_X (n k : ℤ) : coeff I n (X R I k) = if n = k then 1 else 0 := by
  rw [X, coeff_of, coeffₗ_T]

/-- **The coefficients of a constant.** -/
@[simp]
theorem coeff_algebraMap (n : ℤ) (r : R) :
    coeff I n (algebraMap R (RestrictedLaurentSeries R I) r) = if n = 0 then r else 0 := by
  have hr : algebraMap R (RestrictedLaurentSeries R I) r =
      AdicCompletion.of (I.map (algebraMap R (LaurentPolynomial R))) (LaurentPolynomial R)
        (C r) := by
    rw [IsScalarTower.algebraMap_apply R (LaurentPolynomial R) (RestrictedLaurentSeries R I),
      AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, C_eq_algebraMap]
  rw [hr, coeff_of, coeffₗ_C]

/-- **A coefficient of an element of the `m`-th filtration step lies in `I ^ m`** — the
statement that `coeff` is continuous. -/
theorem coeff_mem_pow (hI : I.FG) (n : ℤ) (m : ℕ) {z : RestrictedLaurentSeries R I}
    (hz : z ∈ ((I.map (algebraMap R (LaurentPolynomial R))) ^ m • ⊤ :
      Submodule (LaurentPolynomial R) (RestrictedLaurentSeries R I))) :
    coeff I n z ∈ I ^ m := by
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (hI.map _), LinearMap.mem_ker,
    AdicCompletion.eval_apply] at hz
  have h0 : (Submodule.Quotient.mk (coeff I n z) : R ⧸ (I ^ m • ⊤ : Submodule R R)) = 0 := by
    rw [mk_coeff, coeffLevel_apply, hz, map_zero]
  rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_smul_top_self_iff] at h0
  exact h0

/-- **The coefficients of `1`.** -/
@[simp]
theorem coeff_one (n : ℤ) :
    coeff I n (1 : RestrictedLaurentSeries R I) = if n = 0 then 1 else 0 := by
  rw [← map_one (algebraMap R (RestrictedLaurentSeries R I)), coeff_algebraMap]

/-- **Scalars pull out of a coefficient.** Multiplication by the structural image of `r` is the
`R`-action, and `coeff` is `R`-linear. -/
theorem coeff_algebraMap_mul (n : ℤ) (r : R) (z : RestrictedLaurentSeries R I) :
    coeff I n (algebraMap R (RestrictedLaurentSeries R I) r * z) = r * coeff I n z := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-! ### Extensionality -/

/-- **A restricted Laurent series with all coefficients zero is zero.** At each level its
representative has every coefficient in `I ^ m`, hence lies in the `m`-th step of the filtration
by `LaurentPolynomial.mem_smul_top_of_coeffₗ_mem`. -/
theorem eq_zero_of_coeff_eq_zero {z : RestrictedLaurentSeries R I} (h : ∀ n, coeff I n z = 0) :
    z = 0 := by
  refine AdicCompletion.ext fun m => ?_
  obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective _ (z.val m)
  have hcoeff : ∀ n, coeffₗ R n p ∈ I ^ m := by
    intro n
    have h0 : (Submodule.Quotient.mk (coeff I n z) : R ⧸ (I ^ m • ⊤ : Submodule R R)) =
        Submodule.Quotient.mk (coeffₗ R n p) := by
      rw [mk_coeff, coeffLevel_apply, ← hp, coeffQuot_mk]
    rw [h n] at h0
    have hmem := (Submodule.Quotient.eq _).1 h0
    rw [zero_sub, Submodule.neg_mem_iff, Ideal.mem_smul_top_self_iff] at hmem
    exact hmem
  rw [← hp, AdicCompletion.val_zero_apply, Submodule.Quotient.mk_eq_zero,
    Ideal.mem_map_pow_iff_mem_smul_top I m p]
  exact LaurentPolynomial.mem_smul_top_of_coeffₗ_mem hcoeff

/-- **A restricted Laurent series is zero exactly when all its coefficients are.** -/
theorem coeff_eq_zero_iff {z : RestrictedLaurentSeries R I} :
    (∀ n, coeff I n z = 0) ↔ z = 0 :=
  ⟨eq_zero_of_coeff_eq_zero I, fun hz n => by rw [hz, map_zero]⟩

/-- **Extensionality: a restricted Laurent series is determined by its coefficients.** This is the
principle `FormalSchemes.FormalGm` lacks. -/
theorem ext_coeff {z w : RestrictedLaurentSeries R I} (h : ∀ n, coeff I n z = coeff I n w) :
    z = w := by
  rw [← sub_eq_zero]
  refine eq_zero_of_coeff_eq_zero I fun n => ?_
  rw [map_sub, h n, sub_self]

end RestrictedLaurentSeries
