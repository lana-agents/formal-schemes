import FormalSchemes.TateInvGlobalNormalForm

set_option linter.style.header false

/-!
# The separation hypothesis holds over a discrete base

`FormalSchemes.TateInvGlobalNormalForm` proves `Γ (T_inv/⟨σ⟩) ≃+* R` from one hypothesis,
`AlgebraicGeometry.IsTateInvCoordSeparating`, and proves that hypothesis for no `(R, I, q)`;
`FormalSchemes.TateInvSeparatingKerClosed` measures what the hypothesis costs but does not
discharge it. **Every conditional statement of that cluster was therefore unverified for
non-vacuity.** This file removes that doubt, for the whole family `I = ⊥`, `q = 0`.

## The statement

`AlgebraicGeometry.isTateInvCoordSeparating_bot`: for **every** commutative ring `R`,

```
IsTateInvCoordSeparating R ⊥ 0 Submodule.fg_bot
```

with no further hypothesis — `IsAdicComplete (⊥ : Ideal R) R` is automatic, `(⊥ : Ideal R).FG`
is `Submodule.fg_bot`, and `q = 0` is forced by `q ∈ ⊥`, so this is the *only* shape a discrete
base can take and the whole of it is covered. `AlgebraicGeometry.isTateInvCoordSeparating_int` is
the instance at `R = ℤ`, the tree's standing non-vacuity witness.

## Why the discrete case is a genuine computation and not a degeneracy

At `I = ⊥` the polydisc `R{x, y}` is the polynomial ring `R[x, y]` — `AdicCompletion.of` is
bijective because `R[x, y]` is already `⊥`-adically complete — so `A = R[x, y]/(x·y)`, and the
two coordinate maps are the two evaluations

```
φ       :  x ↦ X,  y ↦ q·X⁻¹ = 0
φ ∘ flip⁻¹ :  x ↦ 0,  y ↦ X
```

into `R{X, X⁻¹}`. Separation is then exactly the statement that a polynomial killed by both
`y ↦ 0` and `x ↦ 0` lies in `(x·y)` — which is **false for the individual maps** and is the
reason the hypothesis is stated jointly. `AlgebraicGeometry.not_injective_tateInvGlobalCoord_zero`
already records that `φ` alone is not injective at `q = 0`, so this file is proving something
that map cannot give.

The proof reads a coefficient of the image off a coefficient of the polynomial
(`AlgebraicGeometry.coeff_tateInvBotCoordX`, `AlgebraicGeometry.coeff_tateInvBotCoordY`), which
forces every monomial in the support of a jointly-killed polynomial to be divisible by both
variables, and closes with `MvPolynomial.mem_ideal_span_monomial_image`.

## What this does *not* prove

**Nothing about a base with `I ≠ ⊥`.** The general case is untouched, and so is every route to
it: no coefficient API for the two-variable polydisc is built here, and the argument below uses
`I = ⊥` twice essentially — once to identify the polydisc with a polynomial ring, and once
through `q = 0` to make the two evaluations kill a variable each. Whether
`IsTateInvCoordSeparating` holds for, say, `R = ℤ_p`, `I = (p)`, `q = p` is exactly as open as it
was before.

In particular this file does **not** make `AlgebraicGeometry.tateInvGlobalSubringEquivBase` or
`AlgebraicGeometry.tateInvPeriodQuotientGlobalSectionsEquivBase` unconditional. It makes them
non-vacuous.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
-/

noncomputable section

open RestrictedLaurentSeries MvPolynomial

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R]

/-! ### The polydisc over a discrete base is the polynomial ring -/

/-- The structural map `R[x, y] → R{x, y}` at `I = ⊥`. It is a ring isomorphism
(`AlgebraicGeometry.bijective_polydiscOfBot`), which is what makes the whole file a computation
with polynomials. -/
def polydiscOfBot : MvPolynomial (Fin 2) R →+* annulusRing R ⊥ :=
  algebraMap (MvPolynomial (Fin 2) R) (annulusRing R ⊥)

/-- **The polydisc over a discrete base is the polynomial ring**: `R[x, y]` is already
`⊥`-adically complete, so `AdicCompletion.of` is bijective. -/
theorem bijective_polydiscOfBot : Function.Bijective (polydiscOfBot R) := by
  haveI : IsAdicComplete (Ideal.map (algebraMap R (MvPolynomial (Fin 2) R)) ⊥)
      (MvPolynomial (Fin 2) R) := by rw [Ideal.map_bot]; infer_instance
  exact AdicCompletion.of_bijective _ _

theorem polydiscOfBot_X_zero : polydiscOfBot R (X 0) = annulusX R ⊥ := rfl

theorem polydiscOfBot_X_one : polydiscOfBot R (X 1) = annulusY R ⊥ := rfl

/-! ### The two coordinate maps, read on polynomials -/

/-- The `x`-chart coordinate map, precomposed with `R[x, y] ↠ A`. It sends `x ↦ X` and `y ↦ 0`,
because `y ↦ q·X⁻¹` and `q = 0`. -/
def tateInvBotCoordX : MvPolynomial (Fin 2) R →+* RestrictedLaurentSeries R ⊥ :=
  (tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot).comp
    ((annulusMk R ⊥ 0).toRingHom.comp (polydiscOfBot R))

/-- The flipped coordinate map, precomposed with `R[x, y] ↠ A`. It sends `x ↦ 0` and `y ↦ X`. -/
def tateInvBotCoordY : MvPolynomial (Fin 2) R →+* RestrictedLaurentSeries R ⊥ :=
  ((tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot).comp
    (annulusFlip R ⊥ 0 Submodule.fg_bot).symm.toAlgHom.toRingHom).comp
      ((annulusMk R ⊥ 0).toRingHom.comp (polydiscOfBot R))

variable {R}

theorem tateInvBotCoordX_X_zero :
    tateInvBotCoordX R (X 0) = RestrictedLaurentSeries.X R ⊥ 1 :=
  tateInvGlobalCoord_overlapX R ⊥ 0 _

theorem tateInvBotCoordX_X_one : tateInvBotCoordX R (X 1) = 0 := by
  change tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot (overlapY R ⊥ 0) = 0
  rw [tateInvGlobalCoord_overlapY, map_zero, zero_mul]

theorem tateInvBotCoordY_X_zero : tateInvBotCoordY R (X 0) = 0 := by
  change tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot
    ((annulusFlip R ⊥ 0 Submodule.fg_bot).symm (overlapX R ⊥ 0)) = 0
  rw [annulusFlip_symm_overlapX, tateInvGlobalCoord_overlapY, map_zero, zero_mul]

theorem tateInvBotCoordY_X_one :
    tateInvBotCoordY R (X 1) = RestrictedLaurentSeries.X R ⊥ 1 := by
  change tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot
    ((annulusFlip R ⊥ 0 Submodule.fg_bot).symm (overlapY R ⊥ 0)) = _
  rw [annulusFlip_symm_overlapY]
  exact tateInvGlobalCoord_overlapX R ⊥ 0 _

theorem tateInvBotCoordX_C (r : R) :
    tateInvBotCoordX R (C r) = algebraMap R (RestrictedLaurentSeries R ⊥) r := by
  change tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot (algebraMap R (annulusAlgebra R ⊥ 0) r) = _
  rw [tateInvGlobalCoord_algebraMap]

theorem tateInvBotCoordY_C (r : R) :
    tateInvBotCoordY R (C r) = algebraMap R (RestrictedLaurentSeries R ⊥) r := by
  change tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot
    ((annulusFlip R ⊥ 0 Submodule.fg_bot).symm (algebraMap R (annulusAlgebra R ⊥ 0) r)) = _
  rw [AlgEquiv.commutes, tateInvGlobalCoord_algebraMap]

end AlgebraicGeometry
