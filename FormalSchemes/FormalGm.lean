import FormalSchemes.RestrictedPowerSeries
import FormalSchemes.AdicExtend
import Mathlib.Algebra.Polynomial.Laurent

set_option linter.style.header false

/-!
# The formal multiplicative group

Over an adic ring `R` with ideal of definition `I`, the **formal multiplicative group** is
`Ĝm = Spf R{X, X⁻¹}`, where `R{X, X⁻¹}` is the `I`-adic completion of the Laurent polynomial
ring `R[T, T⁻¹]` (Bosch, *Lectures on Formal and Rigid Geometry*, §8). It is the ambient
formal group in which the period lattice `q^ℤ` of the Tate curve sits.

Following the design of `FormalSchemes/RestrictedPowerSeries.lean`, we define
`RestrictedLaurentSeries R I` directly as `AdicCompletion (I·R[T,T⁻¹]) R[T,T⁻¹]`; the general
completion machinery then makes it a complete adic ring for the extension of `I` (no
finiteness beyond `I.FG`, no closedness hypotheses), and `Ĝm` is the formal spectrum.

For the functor of points, the key construction is **evaluation at a unit**: a unit `u` of a
complete adic `R`-algebra `S` determines a continuous homomorphism `R{X,X⁻¹} →+* S` sending
`X ↦ u` (`RestrictedLaurentSeries.unitEval`), via Laurent-polynomial evaluation
`AddMonoidAlgebra.lift` at the group homomorphism `ℤ → Sˣ, n ↦ uⁿ`, extended to the completion
by `AdicCompletion.extendRingHom`. The inverse direction of the functor-of-points bijection
(every continuous point comes from the unit `image of X`) and the group-object structure
(comultiplication through the completed tensor product) are left to the follow-up parts of
this issue.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §8.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.
-/

noncomputable section

open Ideal LaurentPolynomial

universe u

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- The ring of **restricted Laurent series** `R{X, X⁻¹}`: the `I`-adic completion of the
Laurent polynomial ring. Its formal spectrum is the formal multiplicative group over `R`. -/
abbrev RestrictedLaurentSeries : Type u :=
  AdicCompletion (I.map (algebraMap R (LaurentPolynomial R))) (LaurentPolynomial R)

namespace RestrictedLaurentSeries

/-- The ideal of definition of `R{X, X⁻¹}`: the extension of `I·R[T,T⁻¹]` to the
completion. -/
abbrev idealOfDefinition : Ideal (RestrictedLaurentSeries R I) :=
  (I.map (algebraMap R (LaurentPolynomial R))).map
    (algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I))

/-- The ideal of definition of `R{X, X⁻¹}` is the extension of `I` itself. -/
theorem idealOfDefinition_eq_map :
    idealOfDefinition R I = I.map (algebraMap R (RestrictedLaurentSeries R I)) := by
  change (I.map (algebraMap R (LaurentPolynomial R))).map
    (algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I)) = _
  rw [Ideal.map_map]
  congr 1

/-- The restricted Laurent series ring is a complete adic ring (`I` finitely generated). -/
theorem isAdicRing (hI : I.FG) : IsAdicRing (idealOfDefinition R I) :=
  AdicCompletion.isAdicRing_map _ (hI.map _)

/-- The image of the Laurent variable `T ^ n` in the restricted Laurent series ring. -/
def X (n : ℤ) : RestrictedLaurentSeries R I :=
  AdicCompletion.of (I.map (algebraMap R (LaurentPolynomial R))) (LaurentPolynomial R) (T n)

/-- The variable of `R{X, X⁻¹}` is a unit (with inverse the image of `T⁻¹`). -/
theorem isUnit_X (n : ℤ) : IsUnit (X R I n) := by
  have h : X R I n =
      algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I) (T n) := by
    rw [X, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h]
  exact (isUnit_T n).map (algebraMap (LaurentPolynomial R) (RestrictedLaurentSeries R I))

end RestrictedLaurentSeries

/-- The **formal multiplicative group** `Ĝm = Spf R{X, X⁻¹}` over an adic ring `R` with
finitely generated ideal of definition `I`, as a formal scheme (Bosch, §8). -/
def formalGm (hI : I.FG) : AlgebraicGeometry.FormalScheme :=
  haveI := RestrictedLaurentSeries.isAdicRing R I hI
  AlgebraicGeometry.FormalScheme.Spf (RestrictedLaurentSeries.idealOfDefinition R I)

namespace RestrictedLaurentSeries

/-!
### Points of `Ĝm`: evaluation at units
-/

section Points

variable {S : Type u} [CommRing S] (L : Ideal S) [Algebra R S] [IsAdicComplete L S]
variable (hIL : I.map (algebraMap R S) ≤ L)

/-- Evaluation of Laurent polynomials at a unit `u`: the `R`-algebra homomorphism
`R[T, T⁻¹] →ₐ[R] S` sending `T ^ n ↦ uⁿ`. -/
def laurentEval (u : Sˣ) : LaurentPolynomial R →ₐ[R] S :=
  AddMonoidAlgebra.lift R S ℤ ((Units.coeHom S).comp (zpowersHom Sˣ u))

@[simp]
theorem laurentEval_T (u : Sˣ) (n : ℤ) : laurentEval R (u := u) (T n) = ((u ^ n : Sˣ) : S) := by
  simp only [laurentEval, T]
  rw [AddMonoidAlgebra.lift_single]
  simp

/-- **Evaluation of restricted Laurent series at a unit**: a unit of a complete adic
`R`-algebra determines a continuous homomorphism from `R{X, X⁻¹}` — a point of the formal
multiplicative group. -/
def unitEval (u : Sˣ) : RestrictedLaurentSeries R I →+* S :=
  AdicCompletion.extendRingHom (I.map (algebraMap R (LaurentPolynomial R))) L
    (laurentEval R (u := u)).toRingHom
    (Ideal.map_algebraMap_pow_le_comap I L hIL (laurentEval R (u := u)))

/-- The point attached to a unit `u` sends the variable `X` to `u`. -/
theorem unitEval_X (u : Sˣ) (n : ℤ) :
    unitEval R I L hIL u (X R I n) = ((u ^ n : Sˣ) : S) := by
  rw [unitEval, X, AdicCompletion.extendRingHom_of]
  exact laurentEval_T R u n

end Points

end RestrictedLaurentSeries
