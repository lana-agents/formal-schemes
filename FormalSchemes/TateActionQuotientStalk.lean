import FormalSchemes.FreeActionQuotientFormalScheme
import FormalSchemes.TateActionQuotientFormalScheme

set_option linter.style.header false

/-!
# The Tate stalk hypothesis is a theorem

`FormalSchemes.TateActionQuotientFormalScheme` states `AlgebraicGeometry.TateStalkIsoHypothesis`
— that the stalk maps of the projection `T_inv ⟶ T_inv / q^{2ℤ}` are isomorphisms over a separating
open — as an *assumption*, and derives the Tate quotient formal scheme from it.
`FormalSchemes.FreeActionQuotientFormalScheme` proves the general statement it is an instance of, so
the assumption can be discharged. This file discharges it, and restates the consequences with no
hypothesis.

The one thing that is not immediate is the universe: the group is `Multiplicative ℤ`, in `Type 0`,
while `T_inv` lives in `LocallyRingedSpace.{u}`. That is exactly what the `Small.{u}` form of
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_of_isProperlyDiscontinuousOn` is for.

## Main results

* `AlgebraicGeometry.tateStalkIsoHypothesis`: the hypothesis holds.
* `AlgebraicGeometry.tateQuotientFormalScheme`: the Tate quotient as a formal scheme, produced by
  the general criterion with nothing assumed, and `…_toLocallyRingedSpace`, that it is the
  coequalizer.
* `AlgebraicGeometry.tateQuotientIsoTateCurveModel`: it is the hand-glued `𝔈_q`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- **The Tate stalk hypothesis is a theorem.** It is the general stalk lemma
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_ofRestrict_comp` at the coequalizer
projection of the `q^{2ℤ}`-action. -/
theorem tateStalkIsoHypothesis : TateStalkIsoHypothesis R I q hq hI := fun U hU y =>
  LocallyRingedSpace.isIso_stalkMap_ofRestrict_comp
    (isActionQuotient_actionQuotientπ (tateInvPeriodSqAction R I q hq hI)) U hU y

/-- **The Tate quotient `T_inv / q^{2ℤ}` as a formal scheme**, with nothing assumed. -/
def tateQuotientFormalScheme : FormalScheme.{u} :=
  tateActionQuotientFormalScheme R I q hq hI (tateStalkIsoHypothesis R I q hq hI)

/-- Its underlying locally ringed space is the coequalizer itself. -/
@[simp]
theorem tateQuotientFormalScheme_toLocallyRingedSpace :
    (tateQuotientFormalScheme R I q hq hI).toLocallyRingedSpace =
      actionQuotient (tateInvPeriodSqAction R I q hq hI) :=
  rfl

/-- **It is the hand-glued Tate curve formal model `𝔈_q`.** -/
def tateQuotientIsoTateCurveModel :
    (tateQuotientFormalScheme R I q hq hI).toLocallyRingedSpace ≅
      (tateCurveModel R I q hq hI).toLocallyRingedSpace :=
  tateActionQuotientIsoTateCurveModel R I q hq hI (tateStalkIsoHypothesis R I q hq hI)

end AlgebraicGeometry
