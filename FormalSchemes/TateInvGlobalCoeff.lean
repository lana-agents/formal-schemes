import FormalSchemes.RestrictedLaurentCoeffInv
import FormalSchemes.TateInvGlobalProperness

set_option linter.style.header false

/-!
# `Γ (T_inv/⟨σ⟩)` as a single equalizer in `Ĝm` coordinates

`AlgebraicGeometry.tateInvGlobalSubring` (`FormalSchemes.TateInvGlobalSections`) cuts
`Γ (T_inv/⟨σ⟩)` out of `A = R{x, y}/(x·y − q)` by **two** equations, one for each of the two
overlap directions, between four ring maps landing in two different completions. This file reads
all four in the `Ĝm` coordinate `overlapEquiv : A[x⁻¹]^∧ ≃+* R{X, X⁻¹}` and finds that

* each of the two conditions is a single equation in `R{X, X⁻¹}` involving only the coordinate map
  `tateInvGlobalCoord` and the coordinate swap `annulusFlip`;
* **the two conditions are equivalent** — the backward one carries no information the forward one
  does not (`tateInvGlobalLegY_eq_legXY_iff_legX_eq_legYX`);
* so the subring is the equalizer of **one** pair of ring maps `A → R{X, X⁻¹}`
  (`tateInvGlobalSubring_eq_eqLocus`), and membership is a coefficientwise condition
  (`mem_tateInvGlobalSubring_iff_coeff`).

## The two coordinate maps

`tateInvGlobalCoord hI` is `a ↦ overlapEquiv (algebraMap A A[x⁻¹]^∧ a)`; it sends `x ↦ X` and
`y ↦ q·X⁻¹`. `tateInvGlobalCoordFlip hI` is `rlsInv ∘ tateInvGlobalCoord ∘ (annulusFlip hI).symm`;
it sends `x ↦ q·X` and `y ↦ X⁻¹`. So the two differ on `x` by the Tate parameter — which is
`AlgebraicGeometry.tateInvGlobalLegYX_overlapX` (`FormalSchemes.TateInvGlobalProperness`) read in
these coordinates, and is why the subring is proper.

Nothing here is new mathematics on top of `FormalSchemes.TateInvGlobalProperness`; it is that
file's computation, stated once for a general element instead of on the two coordinates, plus
`RestrictedLaurentSeries.coeff_rlsInv` and `RestrictedLaurentSeries.ext_coeff`
(`FormalSchemes.RestrictedLaurentCoeffInv`, `FormalSchemes.RestrictedLaurentCoeff`) to turn the
equation into a family of equations between elements of `R`.

## Main results

* `AlgebraicGeometry.tateInvGlobalCoord` and `AlgebraicGeometry.tateInvGlobalCoordFlip`, with
  their values on the two coordinates and on the base.
* `AlgebraicGeometry.tateInvGlobalLegX_eq_legYX_iff` and
  `AlgebraicGeometry.tateInvGlobalLegY_eq_legXY_iff`: each overlap condition, in coordinates.
* **`AlgebraicGeometry.tateInvGlobalLegY_eq_legXY_iff_legX_eq_legYX`**: the two are equivalent,
  because `RestrictedLaurentSeries.rlsInv` is an involution.
* **`AlgebraicGeometry.tateInvGlobalSubring_eq_eqLocus`**: the subring is
  `RingHom.eqLocus tateInvGlobalCoord tateInvGlobalCoordFlip` — a single equalizer of two ring
  maps into `R{X, X⁻¹}`.
* **`AlgebraicGeometry.mem_tateInvGlobalSubring_iff_coeff`**: membership is
  `∀ n, coeff n (tateInvGlobalCoord a) = coeff (-n) (tateInvGlobalCoord ((annulusFlip hI).symm a))`.

## What is *not* proved

**`Γ (T_inv/⟨σ⟩) ≃+* R` is not proved here**, and this file does not claim to have reduced the
remaining gap to nothing. The expected shape of the argument is that the condition forces every
coefficient of `tateInvGlobalCoord a` in nonzero degree to be killed by a unit `1 − qⁿ`, and what
is missing for that is a **normal form for `A = R{x, y}/(x·y − q)`** — a description of the image
of `tateInvGlobalCoord` in terms of coefficients, saying that `a` is `Σ aₙ xⁿ + Σ bₙ yⁿ` and that
`tateInvGlobalCoord a` has coefficients `aₙ` in degree `n ≥ 0` and `b₋ₙ q⁻ⁿ` in degree `n < 0`.
Nothing on the tree provides that, and it is not attempted here. The coefficientwise statement
above is the point at which the question stops being about formal schemes and becomes about that
normal form.

`1 − qⁿ` being a unit is *not* the obstruction: `Ideal.isUnit_of_sub_one_mem_jacobson_bot` fed by
`IsAdicComplete.le_jacobson_bot` gives it in four lines for any `q ∈ I`.

**Properness at a general open `S` is untouched.** This file is about `S = Set.univ`, where
`tateInvGlobalSubring` lives.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum RestrictedLaurentSeries LaurentPolynomial

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The two coordinate maps -/

/-- **The annulus in `Ĝm` coordinates**: `a ↦ overlapEquiv (algebraMap A A[x⁻¹]^∧ a)`, the
`x`-chart restriction read through the crux identification. It sends `x ↦ X` and `y ↦ q·X⁻¹`. -/
def tateInvGlobalCoord (hI : I.FG) : annulusAlgebra R I q →+* RestrictedLaurentSeries R I :=
  (overlapEquiv R I q hI).toRingHom.comp
    (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q))

theorem tateInvGlobalCoord_apply (hI : I.FG) (a : annulusAlgebra R I q) :
    tateInvGlobalCoord R I q hI a =
      overlapEquiv R I q hI (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) a) := rfl

/-- The coordinate map sends the coordinate `x` to the variable `X R I 1`. -/
theorem tateInvGlobalCoord_overlapX (hI : I.FG) :
    tateInvGlobalCoord R I q hI (overlapX R I q) = X R I 1 := by
  rw [tateInvGlobalCoord_apply, overlapEquiv_overlapX]

/-- The coordinate map sends `y` to `q·X⁻¹` — the Tate relation `x·y = q` once `x` is inverted. -/
theorem tateInvGlobalCoord_overlapY (hI : I.FG) :
    tateInvGlobalCoord R I q hI (overlapY R I q) =
      algebraMap R (RestrictedLaurentSeries R I) q * X R I (-1) := by
  rw [tateInvGlobalCoord_apply, overlapEquiv_algebraMap_overlapY]

/-- The coordinate map is the identity on the base. -/
theorem tateInvGlobalCoord_algebraMap (hI : I.FG) (r : R) :
    tateInvGlobalCoord R I q hI (algebraMap R (annulusAlgebra R I q) r) =
      algebraMap R (RestrictedLaurentSeries R I) r := by
  rw [tateInvGlobalCoord_apply, overlapEquiv_algebraMap_annulusAlgebra]

/-- **The second coordinate map**: the coordinate swap, then `tateInvGlobalCoord`, then
`𝔾m`-inversion. It sends `x ↦ q·X` and `y ↦ X⁻¹`. -/
def tateInvGlobalCoordFlip (hI : I.FG) :
    annulusAlgebra R I q →+* RestrictedLaurentSeries R I :=
  ((rlsInv R I hI).toRingHom.comp (tateInvGlobalCoord R I q hI)).comp
    (annulusFlip R I q hI).symm.toAlgHom.toRingHom

theorem tateInvGlobalCoordFlip_apply (hI : I.FG) (a : annulusAlgebra R I q) :
    tateInvGlobalCoordFlip R I q hI a =
      rlsInv R I hI (tateInvGlobalCoord R I q hI ((annulusFlip R I q hI).symm a)) := rfl

/-- The second coordinate map sends `x` to `q·X`: **the two coordinate maps differ on `x` by
exactly the Tate parameter**, which is why the subring is proper
(`AlgebraicGeometry.tateInvGlobalSubring_ne_top`). -/
theorem tateInvGlobalCoordFlip_overlapX (hI : I.FG) :
    tateInvGlobalCoordFlip R I q hI (overlapX R I q) =
      algebraMap R (RestrictedLaurentSeries R I) q * X R I 1 := by
  rw [tateInvGlobalCoordFlip_apply, annulusFlip_symm_overlapX, tateInvGlobalCoord_overlapY,
    map_mul, rlsInv_algebraMap, rlsInv_X_neg_one]

/-- The second coordinate map sends `y` to `X⁻¹`. -/
theorem tateInvGlobalCoordFlip_overlapY (hI : I.FG) :
    tateInvGlobalCoordFlip R I q hI (overlapY R I q) = X R I (-1) := by
  rw [tateInvGlobalCoordFlip_apply, annulusFlip_symm_overlapY, tateInvGlobalCoord_overlapX,
    rlsInv_X_one]

/-! ### The two overlap conditions, in coordinates -/

variable {R I q}

/-- **The forward overlap condition in `Ĝm` coordinates.** Both sides are transported by the
injective `annulusChartOverlapAlgX` and `overlapEquiv`, and
`AlgebraicGeometry.overlapEquiv_annulusOverlapInversion_symm_algebraMap`
(`FormalSchemes.TateInvGlobalProperness`) turns the inverse transition into
`RestrictedLaurentSeries.rlsInv` of the coordinate-swapped image. -/
theorem tateInvGlobalLegX_eq_legYX_iff (hI : I.FG) (a : annulusAlgebra R I q) :
    tateInvGlobalLegX (R := R) (I := I) (q := q) a =
        tateInvGlobalLegYX (R := R) (I := I) (q := q) hI a ↔
      tateInvGlobalCoord R I q hI a = tateInvGlobalCoordFlip R I q hI a := by
  rw [← (annulusChartOverlapAlgX R I q).injective.eq_iff,
    ← (overlapEquiv R I q hI).injective.eq_iff, annulusChartOverlapAlgX_tateInvGlobalLegX,
    annulusChartOverlapAlgX_tateInvGlobalLegYX,
    overlapEquiv_annulusOverlapInversion_symm_algebraMap]
  rfl

/-- **The backward overlap condition in `Ĝm` coordinates** — the mirror, read in the `y`-side
coordinate `AlgebraicGeometry.annulusOverlapEquivY`. -/
theorem tateInvGlobalLegY_eq_legXY_iff (hI : I.FG) (a : annulusAlgebra R I q) :
    tateInvGlobalLegY (R := R) (I := I) (q := q) a =
        tateInvGlobalLegXY (R := R) (I := I) (q := q) hI a ↔
      tateInvGlobalCoord R I q hI ((annulusFlip R I q hI).symm a) =
        rlsInv R I hI (tateInvGlobalCoord R I q hI a) := by
  rw [← (annulusChartOverlapAlgY R I q).injective.eq_iff,
    ← (annulusOverlapEquivY R I q hI).injective.eq_iff,
    annulusChartOverlapAlgY_tateInvGlobalLegY, tateInvGlobalLegXY_apply,
    annulusChartOverlapAlgY_annulusChartTransitionInvAlg,
    annulusChartOverlapAlgX_tateInvGlobalLegX, annulusOverlapEquivY_algebraMap,
    annulusOverlapEquivY_annulusOverlapInversion]
  rfl

/-- **The two overlap conditions are the same condition.** In coordinates the forward one reads
`φ a = rlsInv (φ (flip a))` and the backward one `φ (flip a) = rlsInv (φ a)`, and
`RestrictedLaurentSeries.rlsInv` is an
involution. So the backward condition carries no information the forward one does not — a
sharpening of `AlgebraicGeometry.tateInvGlobalLegY_ne_tateInvGlobalLegXY`, which says only that
each is *some* restriction. -/
theorem tateInvGlobalLegY_eq_legXY_iff_legX_eq_legYX (hI : I.FG) (a : annulusAlgebra R I q) :
    tateInvGlobalLegY (R := R) (I := I) (q := q) a =
        tateInvGlobalLegXY (R := R) (I := I) (q := q) hI a ↔
      tateInvGlobalLegX (R := R) (I := I) (q := q) a =
        tateInvGlobalLegYX (R := R) (I := I) (q := q) hI a := by
  rw [tateInvGlobalLegX_eq_legYX_iff, tateInvGlobalLegY_eq_legXY_iff, tateInvGlobalCoordFlip_apply]
  constructor <;> intro h <;> rw [h, rlsInv_rlsInv]

/-! ### The subring as a single equalizer -/

/-- **Membership in `Γ (T_inv/⟨σ⟩)` is one equation in `R{X, X⁻¹}`.** -/
theorem mem_tateInvGlobalSubring_iff_coord (hI : I.FG) (a : annulusAlgebra R I q) :
    a ∈ tateInvGlobalSubring (R := R) (I := I) (q := q) hI ↔
      tateInvGlobalCoord R I q hI a = tateInvGlobalCoordFlip R I q hI a := by
  rw [mem_tateInvGlobalSubring_iff, tateInvGlobalLegY_eq_legXY_iff_legX_eq_legYX, and_self,
    tateInvGlobalLegX_eq_legYX_iff]

/-- **`Γ (T_inv/⟨σ⟩)` is the equalizer of two ring maps `A → R{X, X⁻¹}`.**
`FormalSchemes.TateInvQuotientChartRing` cut it out by an `⨅` over `ℤ × ℤ` of glue-datum legs and
`FormalSchemes.TateInvChartAnnulusRing` reduced that to an infimum of two `RingHom.eqLocus`es;
this is one. -/
theorem tateInvGlobalSubring_eq_eqLocus (hI : I.FG) :
    tateInvGlobalSubring (R := R) (I := I) (q := q) hI =
      RingHom.eqLocus (tateInvGlobalCoord R I q hI) (tateInvGlobalCoordFlip R I q hI) :=
  Subring.ext fun a =>
    (mem_tateInvGlobalSubring_iff_coord hI a).trans (RingHom.mem_eqLocus).symm

/-! ### The condition coefficientwise -/

section Coefficients

variable [IsAdicComplete I R]

/-- **Membership is a coefficientwise condition.** `RestrictedLaurentSeries.ext_coeff` turns the
equation of `R{X, X⁻¹}` into a family of equations in `R`, and
`RestrictedLaurentSeries.coeff_rlsInv` reverses the degree on the flipped side. This is where the
question stops being about formal schemes: what remains is a normal form for `A`. -/
theorem mem_tateInvGlobalSubring_iff_coeff (hI : I.FG) (a : annulusAlgebra R I q) :
    a ∈ tateInvGlobalSubring (R := R) (I := I) (q := q) hI ↔
      ∀ n : ℤ, coeff I n (tateInvGlobalCoord R I q hI a) =
        coeff I (-n) (tateInvGlobalCoord R I q hI ((annulusFlip R I q hI).symm a)) := by
  rw [mem_tateInvGlobalSubring_iff_coord]
  constructor
  · intro h n
    rw [h, tateInvGlobalCoordFlip_apply, coeff_rlsInv]
  · intro h
    refine ext_coeff I fun n => ?_
    rw [tateInvGlobalCoordFlip_apply, coeff_rlsInv]
    exact h n

end Coefficients

end AlgebraicGeometry
