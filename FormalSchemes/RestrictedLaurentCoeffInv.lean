import FormalSchemes.RestrictedLaurentCoeff
import FormalSchemes.TateOverlapInversion

set_option linter.style.header false

/-!
# `𝔾m`-inversion reverses the coefficients

`RestrictedLaurentSeries.rlsInv` (`FormalSchemes.TateOverlapInversion`) is the `𝔾m`-inversion
automorphism of `R{X, X⁻¹}`, `X n ↦ X (-n)`. On coefficients
(`FormalSchemes.RestrictedLaurentCoeff`) it is the reversal `n ↦ -n`, and this file proves that.

## Why it is not two lines

`rlsInv` is evaluation at the unit `(X 1)⁻¹`, so it is described by what it does to `X`, not by
what it does to a coefficient. The two `R`-linear functionals `coeff n ∘ rlsInv` and `coeff (-n)`
agree on the image of `R[T, T⁻¹]`, where `rlsInv` is `LaurentPolynomial.invert`
(`rlsInv_of`) and `LaurentPolynomial.invert_apply` is the reversal outright — but agreeing on a
dense subring does not by itself force two `R`-linear maps to agree. What closes the gap is that
both are *continuous*: `RestrictedLaurentSeries.coeff_mem_pow` sends the `m`-th step of the
filtration into `I ^ m`, `RestrictedLaurentSeries.isContinuousPoint_unitEvalAlgHom` keeps `rlsInv`
inside that step, and `RestrictedLaurentSeries.exists_sub_mem_smul_top` supplies the
approximation. The difference then lies in every `I ^ m`, and `R` is Hausdorff.

## Main results

* `RestrictedLaurentSeries.rlsInv_of`: `rlsInv` carries the image of a Laurent polynomial to the
  image of `LaurentPolynomial.invert` of it.
* **`RestrictedLaurentSeries.coeff_rlsInv`**: `coeff n (rlsInv z) = coeff (-n) z`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §8.
-/

noncomputable section

open Ideal LaurentPolynomial Submodule

universe u

namespace RestrictedLaurentSeries

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- **Inversion is exponent reversal on Laurent polynomials.** Both `rlsInv ∘ of` and
`of ∘ LaurentPolynomial.invert` are `R`-algebra homomorphisms out of `R[T, T⁻¹]` sending `T 1` to
`X (-1)`, and `RestrictedLaurentSeries.laurentAlgHom_ext` says that determines them. -/
theorem rlsInv_of (hI : I.FG) (p : LaurentPolynomial R) :
    rlsInv R I hI (AdicCompletion.of (I.map (algebraMap R (LaurentPolynomial R)))
        (LaurentPolynomial R) p) =
      AdicCompletion.of (I.map (algebraMap R (LaurentPolynomial R))) (LaurentPolynomial R)
        (LaurentPolynomial.invert p) := by
  have hext : (rlsInvAlg R I hI).comp (ofAlgHom R I) =
      (ofAlgHom R I).comp (LaurentPolynomial.invert (R := R)).toAlgHom := by
    refine laurentAlgHom_ext R ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, ← X_eq_ofAlgHom, rlsInvAlg_X]
    change _ = ofAlgHom R I (LaurentPolynomial.invert (T 1))
    rw [LaurentPolynomial.invert_T, ← X_eq_ofAlgHom]
  have h : rlsInvAlg R I hI (ofAlgHom R I p) =
      ofAlgHom R I (LaurentPolynomial.invert (R := R) p) :=
    congrArg (fun F : LaurentPolynomial R →ₐ[R] RestrictedLaurentSeries R I => F p) hext
  rw [ofAlgHom_apply, ofAlgHom_apply] at h
  rw [rlsInv_apply]
  exact h

variable {R I}

/-- **`𝔾m`-inversion reverses the coefficients**: `coeff n (rlsInv z) = coeff (-n) z`. Both sides
are continuous `R`-linear functionals agreeing on the dense image of `R[T, T⁻¹]`, so their
difference lies in every `I ^ m` and `R` is Hausdorff. -/
theorem coeff_rlsInv [IsAdicComplete I R] (hI : I.FG) (n : ℤ) (z : RestrictedLaurentSeries R I) :
    coeff I n (rlsInv R I hI z) = coeff I (-n) z := by
  haveI _hc : IsAdicComplete (idealOfDefinition R I) (RestrictedLaurentSeries R I) :=
    (isAdicRing R I hI).toIsAdicComplete
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) (M := R) inferInstance _ fun m => ?_
  rw [SModEq.zero]
  obtain ⟨p, hp⟩ := exists_sub_mem_smul_top I hI m z
  set u := AdicCompletion.of (I.map (algebraMap R (LaurentPolynomial R))) (LaurentPolynomial R) p
    with hu
  have hru : coeff I n (rlsInv R I hI u) = coeff I (-n) u := by
    rw [hu, rlsInv_of, coeff_of, coeff_of, LaurentPolynomial.coeffₗ_apply,
      LaurentPolynomial.coeffₗ_apply, LaurentPolynomial.invert_apply]
  have hcont : rlsInv R I hI (z - u) ∈
      ((I.map (algebraMap R (LaurentPolynomial R))) ^ m • ⊤ :
        Submodule (LaurentPolynomial R) (RestrictedLaurentSeries R I)) :=
    (mem_idealOfDefinition_pow_iff R I m _).mp
      (isContinuousPoint_unitEvalAlgHom R I (idealOfDefinition R I)
        (le_of_eq (idealOfDefinition_eq_map R I).symm) hI (isUnit_X R I 1).unit⁻¹ m (z - u) hp)
  have key : coeff I n (rlsInv R I hI z) - coeff I (-n) z =
      coeff I n (rlsInv R I hI (z - u)) - coeff I (-n) (z - u) := by
    rw [map_sub (rlsInv R I hI) z u, map_sub, map_sub, hru]
    ring
  rw [key, Ideal.mem_smul_top_self_iff]
  exact (I ^ m).sub_mem (coeff_mem_pow I hI n m hcont) (coeff_mem_pow I hI (-n) m hp)

end RestrictedLaurentSeries
