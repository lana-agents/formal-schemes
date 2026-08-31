import FormalSchemes.RestrictedPowerSeriesCoeff
import FormalSchemes.TateInvSeparatingDivision

set_option linter.style.header false

/-!
# A regular element of the base stays regular in the Tate annulus algebra

`A = annulusAlgebra R I q = R{x, y}/(x·y − q)` is the coordinate ring of the formal Tate
annulus (`FormalSchemes.TateAnnulus`). This file answers one question about it:

> is the structural image of `t : R` in `A` a non-zero-divisor?

**`AlgebraicGeometry.isLeftRegular_algebraMap_annulusAlgebra`: it is, exactly when `t` is a
non-zero-divisor in `R`**, for every `I`-adically complete Noetherian base and every `q`. The
`iff` is `AlgebraicGeometry.isLeftRegular_algebraMap_annulusAlgebra_iff`.

## Why this is the shape the node chart asked for

The node chart of the Tate curve's formal model is complete for its candidate ideal of definition
over a base with `I = (t)`, and the surviving hypotheses of those results are left-regularity
statements about the image of `t`. Reducing them to the single hypothesis
`IsLeftRegular (algebraMap R (annulusAlgebra R I q) t)` is issue 1284's obstruction (b); this file
is issue 1319, which asks whether that hypothesis ever holds. It holds whenever `t` is regular in
`R`, so at `R = ℤ⟦X⟧`, `I = (X)`, `q = X`, `t = X` — a base with `t ≠ 0`, `q ≠ 0` and `A`
nontrivial, recorded here as
`AlgebraicGeometry.isLeftRegular_algebraMap_annulusAlgebra_powerSeriesInt`.

## The route, and the two the issue proposed

Issue 1319 proposed two routes, both through the polydisc `P = R{x, y}`: write `q = t·c` and
reduce to "`x·y` is a non-zero-divisor mod `t` on `P`", then get that either by base change
(`P/t·P ≅ (R/t){x, y}`) or by a coefficient computation. **Neither is used here, and `q ∈ (t)` is
not assumed.** The route taken instead is the separation property of
`FormalSchemes.TateInvSeparatingDivision`:

* `AlgebraicGeometry.isTateInvCoordSeparating_of_noetherian` says the two `Ĝm` coordinate maps
  `AlgebraicGeometry.tateInvGlobalCoord` and its flip have zero common kernel over a Noetherian
  base — `A` embeds into `R{X, X⁻¹} × R{X, X⁻¹}`.
* `RestrictedLaurentSeries.isLeftRegular_algebraMap` says a regular `t` stays regular in
  `R{X, X⁻¹}`, which is one line of the coefficient API of
  `FormalSchemes.RestrictedLaurentCoeff` (`RestrictedLaurentSeries.coeff_algebraMap_mul` and
  `RestrictedLaurentSeries.ext_coeff`).
* Both coordinate maps are `R`-algebra maps up to the flip's `AlgEquiv.commutes`, so an equation
  `algebraMap t * a = 0` in `A` transports to both factors, and separation brings `a = 0` back.

## Main results

* `RestrictedLaurentSeries.isLeftRegular_algebraMap` and
  `RestrictedLaurentSeries.isLeftRegular_algebraMap_iff`: a base element is a non-zero-divisor in
  `R{X, X⁻¹}` exactly when it is one in `R`, for an `I`-adically complete base.
* `RestrictedPowerSeries.isLeftRegular_algebraMap` and
  `RestrictedPowerSeries.isLeftRegular_algebraMap_iff`: the same for the polydisc
  `R{X₁, …, Xₙ}`, by the same two lines in the coefficient API of
  `FormalSchemes.RestrictedPowerSeriesCoeff`. This is the first of the two inputs issue 1319's
  route needed (`t` is a non-zero-divisor on `P = R{x, y}`); it is not used below, and is
  recorded so that the claim "that input is free" is a theorem rather than a sentence.
* `AlgebraicGeometry.eq_zero_of_algebraMap_annulusAlgebra_mul_eq_zero`: the annihilator form of
  the main result, which is what the proof actually establishes.
* **`AlgebraicGeometry.isLeftRegular_algebraMap_annulusAlgebra`**: `IsLeftRegular t` implies
  `IsLeftRegular (algebraMap R (annulusAlgebra R I q) t)`, for `[IsAdicComplete I R]`,
  `[IsNoetherianRing R]` and `I.FG`. No hypothesis relates `t` to `q` or to `I`.
* `AlgebraicGeometry.algebraMap_annulusAlgebra_injective` and
  `AlgebraicGeometry.nontrivial_annulusAlgebra`: `R → A` is injective under the same hypotheses,
  so `A` is nontrivial whenever `R` is. This is what makes the main result a statement about a
  nonzero ring rather than about the zero ring.
* `AlgebraicGeometry.isLeftRegular_algebraMap_annulusAlgebra_iff`: the converse, from injectivity.
* `AlgebraicGeometry.isLeftRegular_algebraMap_annulusAlgebra_powerSeriesInt` and
  `AlgebraicGeometry.nontrivial_annulusAlgebra_powerSeriesInt`: the witness at `R = ℤ⟦X⟧`,
  `I = (X)`, `q = X`, `t = X`, where `I = Ideal.span {t}` and `q ∈ Ideal.span {t}` both hold.

## What is *not* proved here

No statement about the node chart, its ideal, or its completeness appears below; this file does
not import `FormalSchemes.TateInvNodeChartPrincipal` and proves nothing about it. Nothing here
weakens or restates the hypotheses of those results — it supplies an input to them.

Nothing is proved for a base that is not Noetherian: over such a base
`AlgebraicGeometry.isTateInvCoordSeparating_iff_adicKerClosed` shows separation is equivalent to
adic closedness of `(x·y − q)` in `R{x, y}`, and this file uses separation as a black box, so the
main result carries `[IsNoetherianRing R]` through `hsep` and nothing weaker was attempted.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
-/

noncomputable section

universe u

namespace RestrictedLaurentSeries

variable {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]

/-- **A non-zero-divisor of the base stays one in `R{X, X⁻¹}`.** Read off coefficientwise:
`RestrictedLaurentSeries.coeff_algebraMap_mul` pulls the scalar out of every coefficient, and
`RestrictedLaurentSeries.ext_coeff` puts the resulting equalities back together. -/
theorem isLeftRegular_algebraMap {t : R} (ht : IsLeftRegular t) :
    IsLeftRegular (algebraMap R (RestrictedLaurentSeries R I) t) := by
  intro z w h
  refine ext_coeff I fun n => ?_
  have h2 := congrArg (coeff I n) h
  rw [coeff_algebraMap_mul, coeff_algebraMap_mul] at h2
  exact ht h2

/-- **Regularity in `R{X, X⁻¹}` of a base element is regularity in the base.** The converse
direction is `RestrictedLaurentSeries.algebraMap_injective_of_isAdicComplete` applied to the
image of an equation `t · r = t · s`. -/
theorem isLeftRegular_algebraMap_iff {t : R} :
    IsLeftRegular (algebraMap R (RestrictedLaurentSeries R I) t) ↔ IsLeftRegular t := by
  refine ⟨fun h r s hrs => ?_, isLeftRegular_algebraMap I⟩
  refine algebraMap_injective_of_isAdicComplete I (h ?_)
  change algebraMap R (RestrictedLaurentSeries R I) t * algebraMap R _ r
    = algebraMap R (RestrictedLaurentSeries R I) t * algebraMap R _ s
  rw [← map_mul, ← map_mul]
  exact congrArg _ hrs

end RestrictedLaurentSeries

namespace RestrictedPowerSeries

variable {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) [IsAdicComplete I R]

/-- **A non-zero-divisor of the base stays one in the polydisc `R{X₁, …, Xₙ}`.** The
several-variable analogue of `RestrictedLaurentSeries.isLeftRegular_algebraMap`, read off with
`RestrictedPowerSeries.coeff_algebraMap_mul` and `RestrictedPowerSeries.ext_coeff`. -/
theorem isLeftRegular_algebraMap {t : R} (ht : IsLeftRegular t) :
    IsLeftRegular (algebraMap R (RestrictedPowerSeries R I n) t) := by
  intro z w h
  refine ext_coeff I n fun d => ?_
  have h2 := congrArg (coeff I n d) h
  rw [coeff_algebraMap_mul, coeff_algebraMap_mul] at h2
  exact ht h2

/-- **Regularity in the polydisc of a base element is regularity in the base.** The converse
direction is `RestrictedPowerSeries.algebraMap_injective`. -/
theorem isLeftRegular_algebraMap_iff {t : R} :
    IsLeftRegular (algebraMap R (RestrictedPowerSeries R I n) t) ↔ IsLeftRegular t := by
  refine ⟨fun h r s hrs => ?_, isLeftRegular_algebraMap I n⟩
  refine algebraMap_injective I n (h ?_)
  change algebraMap R (RestrictedPowerSeries R I n) t * algebraMap R _ r
    = algebraMap R (RestrictedPowerSeries R I n) t * algebraMap R _ s
  rw [← map_mul, ← map_mul]
  exact congrArg _ hrs

end RestrictedPowerSeries

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} (q : R)
variable [IsAdicComplete I R] [IsNoetherianRing R]

/-- **The annihilator form of the main result**: over a Noetherian complete base, the structural
image of a non-zero-divisor `t` of `R` kills nothing in `A = R{x, y}/(x·y − q)`.

Both `AlgebraicGeometry.tateInvGlobalCoord` and its composite with
`(annulusFlip _ _ _ _).symm` (root namespace) fix the base
(`AlgebraicGeometry.tateInvGlobalCoord_algebraMap` and `AlgEquiv.commutes`), so the hypothesis
transports to two equations in `R{X, X⁻¹}`; `RestrictedLaurentSeries.isLeftRegular_algebraMap`
clears `t` from both, and `AlgebraicGeometry.isTateInvCoordSeparating_of_noetherian` — the two
coordinate maps have zero common kernel — returns `c = 0`. -/
theorem eq_zero_of_algebraMap_annulusAlgebra_mul_eq_zero (hI : I.FG) {t : R}
    (ht : IsLeftRegular t) {c : annulusAlgebra R I q}
    (hc : algebraMap R (annulusAlgebra R I q) t * c = 0) : c = 0 := by
  refine isTateInvCoordSeparating_of_noetherian q hI c ?_ ?_
  · have h1 := congrArg (tateInvGlobalCoord R I q hI) hc
    rw [map_mul, map_zero, tateInvGlobalCoord_algebraMap] at h1
    exact RestrictedLaurentSeries.isLeftRegular_algebraMap I ht (by simpa using h1)
  · have h0 : (annulusFlip R I q hI).symm (algebraMap R (annulusAlgebra R I q) t * c) = 0 := by
      rw [hc, map_zero]
    rw [map_mul, AlgEquiv.commutes] at h0
    have h1 := congrArg (tateInvGlobalCoord R I q hI) h0
    rw [map_mul, map_zero, tateInvGlobalCoord_algebraMap] at h1
    exact RestrictedLaurentSeries.isLeftRegular_algebraMap I ht (by simpa using h1)

/-- **A non-zero-divisor of the base stays one in the Tate annulus algebra**, over every
`I`-adically complete Noetherian base, with no hypothesis relating `t` to `q` or to `I`.

This is the hypothesis carried by the principal-base completeness and finite-generation results
for the node chart's candidate ideal of definition, at `I = Ideal.span {t}`. -/
theorem isLeftRegular_algebraMap_annulusAlgebra (hI : I.FG) {t : R} (ht : IsLeftRegular t) :
    IsLeftRegular (algebraMap R (annulusAlgebra R I q) t) := by
  intro a b hab
  have hab' : algebraMap R (annulusAlgebra R I q) t * a
      = algebraMap R (annulusAlgebra R I q) t * b := hab
  refine sub_eq_zero.mp (eq_zero_of_algebraMap_annulusAlgebra_mul_eq_zero q hI ht ?_)
  rw [mul_sub, hab', sub_self]

omit [IsNoetherianRing R] in
/-- **`R → A` is injective** over a Noetherian complete base: the composite with
`AlgebraicGeometry.tateInvGlobalCoord` is `algebraMap R (RestrictedLaurentSeries R I)`, which is
injective by `RestrictedLaurentSeries.algebraMap_injective_of_isAdicComplete`. -/
theorem algebraMap_annulusAlgebra_injective (hI : I.FG) :
    Function.Injective (algebraMap R (annulusAlgebra R I q)) := by
  intro r s h
  refine RestrictedLaurentSeries.algebraMap_injective_of_isAdicComplete I ?_
  rw [← tateInvGlobalCoord_algebraMap R I q hI, ← tateInvGlobalCoord_algebraMap R I q hI, h]

omit [IsNoetherianRing R] in
/-- **The Tate annulus algebra is nontrivial whenever the base is.** Together with
`AlgebraicGeometry.isLeftRegular_algebraMap_annulusAlgebra` this says the regularity statement is
about a nonzero ring: in the zero ring every element is left-regular for trivial reasons. -/
theorem nontrivial_annulusAlgebra [Nontrivial R] (hI : I.FG) :
    Nontrivial (annulusAlgebra R I q) :=
  (algebraMap_annulusAlgebra_injective q hI).nontrivial

/-- **Regularity in `A` of a base element is regularity in the base.** -/
theorem isLeftRegular_algebraMap_annulusAlgebra_iff (hI : I.FG) {t : R} :
    IsLeftRegular (algebraMap R (annulusAlgebra R I q) t) ↔ IsLeftRegular t := by
  refine ⟨fun h r s hrs => ?_, isLeftRegular_algebraMap_annulusAlgebra q hI⟩
  refine algebraMap_annulusAlgebra_injective q hI (h ?_)
  change algebraMap R (annulusAlgebra R I q) t * algebraMap R _ r
    = algebraMap R (annulusAlgebra R I q) t * algebraMap R _ s
  rw [← map_mul, ← map_mul]
  exact congrArg _ hrs

/-! ### The witness at the universal Tate base -/

section Witness

/-- **The hypothesis of the principal-base node chart results is satisfiable at a base where
`t ≠ 0`**: `R = ℤ⟦X⟧`, `I = Ideal.span {X}`, `q = X`, `t = X`. Here `I = Ideal.span {t}` and
`q ∈ Ideal.span {t}` hold, `X ≠ 0` in `ℤ⟦X⟧`, and
`AlgebraicGeometry.nontrivial_annulusAlgebra_powerSeriesInt` records that the annulus algebra is
not the zero ring. -/
theorem isLeftRegular_algebraMap_annulusAlgebra_powerSeriesInt :
    IsLeftRegular (algebraMap (PowerSeries ℤ)
      (annulusAlgebra (PowerSeries ℤ) (Ideal.span {(PowerSeries.X : PowerSeries ℤ)})
        PowerSeries.X) PowerSeries.X) :=
  isLeftRegular_algebraMap_annulusAlgebra _ (Submodule.fg_span_singleton _)
    (IsRegular.of_ne_zero PowerSeries.X_ne_zero).left

/-- **The annulus algebra at the universal Tate base is not the zero ring.** -/
theorem nontrivial_annulusAlgebra_powerSeriesInt :
    Nontrivial (annulusAlgebra (PowerSeries ℤ)
      (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) PowerSeries.X) :=
  nontrivial_annulusAlgebra _ (Submodule.fg_span_singleton _)

end Witness

end AlgebraicGeometry
