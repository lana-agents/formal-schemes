import FormalSchemes.RestrictedPowerSeriesCoeff
import FormalSchemes.TateAnnulus

set_option linter.style.header false

/-!
# Coefficients on the Tate polydisc, and the recursion for division by `x·y − q`

`FormalSchemes.RestrictedPowerSeriesCoeff` reads coefficients off `R{X₁, …, Xₙ}`. The Tate
polydisc `annulusRing R I = R{x, y}` **is** `RestrictedPowerSeries R I 2` (it is an `abbrev`,
`FormalSchemes.TateAnnulus`), and `annulusX`/`annulusY` **are** the images of `MvPolynomial.X 0`
and `MvPolynomial.X 1`, so that API applies to it with no transport at all. This file records
what it says there.

## Why this file exists

The open half of the Tate normal form is a division: given `w ∈ R{x, y}` in the kernel of both
coordinate maps, write `w = (x·y − q) · v`. `AlgebraicGeometry.mem_span_X_mul_X_of_coord_eq_zero`
(`FormalSchemes.TateInvSeparatingBot`) does exactly that at `I = ⊥`, where `R{x, y}` is the
polynomial ring and the division is a statement about monomial ideals. At a general `I` there is
no such reduction, and what replaces it is a **recursion on coefficients**. This file states that
recursion:

`AlgebraicGeometry.coeff_annulusRel_mul` computes every coefficient of `(x·y − q) · z` from the
coefficients of `z`, as a shift by `(1, 1)` minus `q` times the coefficient at the same place.
Solving that recursion for `z` given the left-hand side is what a division algorithm is.

**No division is performed here.** This file computes; it does not invert.

## Main results

* `MvPolynomial.X_mul_X_eq_monomial`: `Xᵢ · Xⱼ` is the monomial at `single i 1 + single j 1`.
* `AlgebraicGeometry.coeff_annulusX`, `AlgebraicGeometry.coeff_annulusY`: the coefficients of the
  two coordinates.
* `AlgebraicGeometry.coeff_annulusX_mul`, `AlgebraicGeometry.coeff_annulusY_mul`: multiplying by a
  coordinate shifts the coefficients by one in that variable.
* `AlgebraicGeometry.coeff_annulusRel`: the coefficients of `x·y − q` itself — `1` at `(1, 1)`,
  `−q` at `(0, 0)`, and `0` elsewhere.
* **`AlgebraicGeometry.coeff_annulusRel_mul`**: the coefficients of `(x·y − q) · z`.

## What is *not* proved

**Nothing is divided.** `AlgebraicGeometry.IsTateInvCoordSeparating` is not discharged for any
base with `I ≠ ⊥`, no element of `annulusIdeal` is characterised by its coefficients, and no
statement below mentions `annulusAlgebra`, `annulusMk` or `AlgebraicGeometry.tateInvGlobalCoord`.
The two-variable analogue of `AlgebraicGeometry.mem_tateInvGlobalSubring_iff_coeff` is not
attempted.

**No converse to `coeff_annulusRel_mul`.** That an element all of whose coefficients satisfy the
recursion is a multiple of `x·y − q` — which is what a division would give — is exactly the open
question, and it is untouched. In particular nothing here says `annulusIdeal` is adically closed;
that remains the hypothesis `annulus_isAdicRing_of_kerClosed` takes.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.5.
-/

noncomputable section

open Ideal

universe u

namespace MvPolynomial

/-- A product of two variables is the monomial at the sum of their exponents. -/
theorem X_mul_X_eq_monomial {R : Type u} [CommRing R] {σ : Type*} (i j : σ) :
    (X i * X j : MvPolynomial σ R) =
      monomial (Finsupp.single i 1 + Finsupp.single j 1) 1 := by
  rw [show (X i : MvPolynomial σ R) = X i ^ 1 from (pow_one _).symm,
    show (X j : MvPolynomial σ R) = X j ^ 1 from (pow_one _).symm,
    X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, mul_one]

end MvPolynomial

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] (I : Ideal R) (q : R) [IsAdicComplete I R]

/-- **The coefficients of `x`.** -/
theorem coeff_annulusX (d : Fin 2 →₀ ℕ) :
    RestrictedPowerSeries.coeff I 2 d (annulusX R I) =
      if Finsupp.single 0 1 = d then 1 else 0 :=
  RestrictedPowerSeries.coeff_X I 2 d 0

/-- **The coefficients of `y`.** -/
theorem coeff_annulusY (d : Fin 2 →₀ ℕ) :
    RestrictedPowerSeries.coeff I 2 d (annulusY R I) =
      if Finsupp.single 1 1 = d then 1 else 0 :=
  RestrictedPowerSeries.coeff_X I 2 d 1

/-- **Multiplying by `x` shifts the coefficients by one in the first variable.** -/
theorem coeff_annulusX_mul (hI : I.FG) (d : Fin 2 →₀ ℕ) (z : annulusRing R I) :
    RestrictedPowerSeries.coeff I 2 d (annulusX R I * z) =
      if Finsupp.single 0 1 ≤ d then
        RestrictedPowerSeries.coeff I 2 (d - Finsupp.single 0 1) z else 0 := by
  have hX : annulusX R I = AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin 2) R)))
      (MvPolynomial (Fin 2) R) (MvPolynomial.monomial (Finsupp.single 0 1) (1 : R)) := by
    rw [← MvPolynomial.X_pow_eq_monomial, pow_one]
  rw [hX, RestrictedPowerSeries.coeff_monomial_mul I 2 hI]
  by_cases hle : Finsupp.single (0 : Fin 2) 1 ≤ d
  · rw [if_pos hle, if_pos hle, one_mul]
  · rw [if_neg hle, if_neg hle]

/-- **Multiplying by `y` shifts the coefficients by one in the second variable.** -/
theorem coeff_annulusY_mul (hI : I.FG) (d : Fin 2 →₀ ℕ) (z : annulusRing R I) :
    RestrictedPowerSeries.coeff I 2 d (annulusY R I * z) =
      if Finsupp.single 1 1 ≤ d then
        RestrictedPowerSeries.coeff I 2 (d - Finsupp.single 1 1) z else 0 := by
  have hY : annulusY R I = AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin 2) R)))
      (MvPolynomial (Fin 2) R) (MvPolynomial.monomial (Finsupp.single 1 1) (1 : R)) := by
    rw [← MvPolynomial.X_pow_eq_monomial, pow_one]
  rw [hY, RestrictedPowerSeries.coeff_monomial_mul I 2 hI]
  by_cases hle : Finsupp.single (1 : Fin 2) 1 ≤ d
  · rw [if_pos hle, if_pos hle, one_mul]
  · rw [if_neg hle, if_neg hle]

omit [IsAdicComplete I R] in
/-- `x · y` is the image of a single monomial. -/
theorem annulusX_mul_annulusY :
    annulusX R I * annulusY R I =
      AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin 2) R)))
        (MvPolynomial (Fin 2) R)
        (MvPolynomial.monomial (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1)
          (1 : R)) := by
  rw [RestrictedPowerSeries.of_mul_of, MvPolynomial.X_mul_X_eq_monomial]

/-- **The coefficients of the Tate relation `x·y − q`**: `1` at the exponent `(1, 1)`, `−q` at
`(0, 0)`, and `0` elsewhere. -/
theorem coeff_annulusRel (d : Fin 2 →₀ ℕ) :
    RestrictedPowerSeries.coeff I 2 d (annulusRel R I q) =
      (if Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 = d then 1 else 0) -
        (if 0 = d then q else 0) := by
  rw [show annulusRel R I q = annulusX R I * annulusY R I -
      algebraMap R (annulusRing R I) q from rfl, map_sub, annulusX_mul_annulusY,
    RestrictedPowerSeries.coeff_monomial, RestrictedPowerSeries.coeff_algebraMap]

/-- **The recursion for division by `x·y − q`.** Every coefficient of `(x·y − q) · z` is the
coefficient of `z` shifted by `(1, 1)`, minus `q` times the coefficient of `z` at the same place.

Reading this equation forwards computes; reading it backwards — solving for the coefficients of
`z` given those of the product — is a division algorithm, and **that is not done here**. See this
file's module docstring. -/
theorem coeff_annulusRel_mul (hI : I.FG) (d : Fin 2 →₀ ℕ) (z : annulusRing R I) :
    RestrictedPowerSeries.coeff I 2 d (annulusRel R I q * z) =
      (if Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 ≤ d then
        RestrictedPowerSeries.coeff I 2
          (d - (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1)) z
        else 0) - q * RestrictedPowerSeries.coeff I 2 d z := by
  rw [show annulusRel R I q = annulusX R I * annulusY R I -
      algebraMap R (annulusRing R I) q from rfl, sub_mul, map_sub, annulusX_mul_annulusY,
    RestrictedPowerSeries.coeff_monomial_mul I 2 hI,
    RestrictedPowerSeries.coeff_algebraMap_mul]
  by_cases hle : Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 ≤ d
  · rw [if_pos hle, if_pos hle, one_mul]
  · rw [if_neg hle, if_neg hle]

end AlgebraicGeometry
