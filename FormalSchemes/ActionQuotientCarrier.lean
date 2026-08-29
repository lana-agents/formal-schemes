import FormalSchemes.ActionQuotientTop
import FormalSchemes.TateQuotientColimit

set_option linter.style.header false

/-!
# The underlying space of the quotient of a locally ringed space is the orbit space

`FormalSchemes.ActionQuotientColimit` builds the quotient of an object by a group action as a
coequalizer, and `FormalSchemes.TateQuotientColimit` observes that `LocallyRingedSpace` has all
small colimits, so the quotient of a locally ringed space by *any* action of a small group exists.
Neither says what its points are, and the answer is not obvious: Mathlib constructs the coequalizer
of locally ringed spaces through the `SheafedSpace` one, whose sections are an equalizer of
pushforwards and whose local-ring condition is proved by restricting to a basic open. There is no a
priori reason for the carrier of such an object to be the naive orbit space.

It is, and this file proves it. The mechanism is that the underlying-space functor factors as
`LocallyRingedSpace ⥤ SheafedSpace CommRingCat ⥤ TopCat`, and one more step lands in `Type`; each
of the three preserves the colimits a quotient is built from, so
`CategoryTheory.IsActionQuotient.map` carries the universal property down to `TopCat` and to
`Type`, where `FormalSchemes.ActionQuotientTop` and `FormalSchemes.ActionQuotientType` identify it
with the orbit space and the orbit set.

The statements are about an arbitrary `CategoryTheory.IsActionQuotient` and so apply both to the
generic coequalizer and to the hand-built Tate-curve quotient `π : T_inv ⟶ 𝔈_q`.

## What this settles, and what it does not

Issue 224's open item is whether a free, properly discontinuous action has a quotient that is again
a *formal scheme*. This file removes one possible obstruction to that: it was not clear that the
coequalizer's carrier is the orbit space rather than some larger sheaf-theoretic object, and if it
were not, the generic quotient would be about a different object than the hand-built `𝔈_q` and the
whole route would need restating. It is the orbit space, and **no** hypothesis on the action is
used — not freeness, not proper discontinuity, not finiteness of a fundamental domain.

Those hypotheses have to enter when one asks for the *structure sheaf* of the quotient to be
locally that of a formal scheme, i.e. for `actionQuotientπ` to be a local isomorphism onto its
image. This file says nothing about that; `FormalSchemes.ActionQuotientStalk` and
`FormalSchemes.FreeActionQuotientFormalScheme` do.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.forgetToTop` and
  `AlgebraicGeometry.LocallyRingedSpace.forgetToType`: the underlying-space and carrier functors
  `LocallyRingedSpace ⥤ TopCat ⥤ Type`, composites of forgetful functors each of which preserves
  all small colimits.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.base_surjective_of_isActionQuotient`: the projection of
  any action quotient is surjective on points.
* `AlgebraicGeometry.LocallyRingedSpace.base_eq_iff_of_isActionQuotient`: **the computation** — it
  identifies two points exactly when they lie in the same orbit. So the carrier of the quotient is
  the orbit set.
* `AlgebraicGeometry.LocallyRingedSpace.base_isQuotientMap_of_isActionQuotient`: and it carries the
  quotient topology. Together: the underlying space of the quotient *is* the orbit space.
* `AlgebraicGeometry.tateQuotientPi_base_surjective`,
  `AlgebraicGeometry.tateQuotientPi_base_isQuotientMap` and
  `AlgebraicGeometry.tateQuotientPi_base_eq_iff`: the same for the hand-built Tate-curve quotient
  `T_inv ⟶ 𝔈_q`, whose orbits are those of the `q^{2ℤ}`-shift.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

namespace LocallyRingedSpace

/-! ### The forgetful functors preserve the two colimits a quotient is built from

Mathlib's `AlgebraicGeometry.LocallyRingedSpace.forgetToTop` is a `def`, so instance search cannot
see that it is `forgetToSheafedSpace ⋙ SheafedSpace.forget _`. These two instances say so. Each
factor has the corresponding instance already — `preservesColimits_forgetToSheafedSpace` for the
first, and `SheafedSpace.forget`'s (from `CommRingCat` having limits) for the second — so both are
`inferInstanceAs`. -/

instance {ι : Type v} [Small.{u} ι] :
    PreservesColimitsOfShape (Discrete ι) forgetToTop.{u} :=
  inferInstanceAs (PreservesColimitsOfShape (Discrete ι)
    (forgetToSheafedSpace ⋙ SheafedSpace.forget _))

instance : PreservesColimitsOfShape Limits.WalkingParallelPair forgetToTop.{u} :=
  inferInstanceAs (PreservesColimitsOfShape Limits.WalkingParallelPair
    (forgetToSheafedSpace ⋙ SheafedSpace.forget _))

/-- **The carrier functor** `LocallyRingedSpace ⥤ Type`: `forgetToTop` followed by the forgetful
functor of `TopCat`, which preserves colimits of every size. -/
abbrev forgetToType : LocallyRingedSpace.{u} ⥤ Type u :=
  forgetToTop ⋙ CategoryTheory.forget TopCat

theorem forgetToType_map {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    forgetToType.map f = ↾(f.base) :=
  rfl

variable {G : Type v} [Group G] [Small.{u} G]
variable {X Q : LocallyRingedSpace.{u}} {a : G →* Aut X} {π : X ⟶ Q}

/-- **An action quotient of locally ringed spaces is a set-level action quotient on carriers.**
`CategoryTheory.IsActionQuotient.map` at the carrier functor. Its two preservation hypotheses are
found by instance search: `Small.{u} G` makes the coproduct `∐_{g : G} X` exist and be preserved by
each of the three factors, and the coequalizer is preserved by each of them too. -/
def isActionQuotient_forgetToType (h : IsActionQuotient a π) :
    IsActionQuotient (forgetToType.mapAction a) (forgetToType.map π) :=
  h.map forgetToType

/-- **The projection of an action quotient is surjective on points.** -/
theorem base_surjective_of_isActionQuotient (h : IsActionQuotient a π) :
    Function.Surjective π.base :=
  (isActionQuotient_forgetToType h).surjective

/-- **The points of the quotient are the orbits.** Two points of `X` have the same image exactly
when some `a g` carries one to the other. Together with surjectivity this says that the carrier of
`Q` is the orbit set of the action on the carrier of `X`. -/
theorem base_eq_iff_of_isActionQuotient (h : IsActionQuotient a π) (x y : X) :
    π.base x = π.base y ↔ ∃ g : G, (a g).hom.base x = y :=
  (isActionQuotient_forgetToType h).apply_eq_iff x y

/-- The same transport one step earlier, to `TopCat`, which remembers the topology. -/
def isActionQuotient_forgetToTop (h : IsActionQuotient a π) :
    IsActionQuotient (forgetToTop.mapAction a) (forgetToTop.map π) :=
  h.map forgetToTop

/-- **The quotient carries the quotient topology.** With `base_eq_iff_of_isActionQuotient` this is
the full statement that the underlying space of an action quotient is the orbit space: the points
are the orbits, and a subset is open exactly when its preimage in `X` is. -/
theorem base_isQuotientMap_of_isActionQuotient (h : IsActionQuotient a π) :
    Topology.IsQuotientMap π.base :=
  (isActionQuotient_forgetToTop h).isQuotientMap

end LocallyRingedSpace

/-! ### The Tate-curve quotient -/

section Tate

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- **`𝔈_q` has no points beyond the images of the chain's.** The hand-built quotient map
`π : T_inv ⟶ 𝔈_q` (`FormalSchemes.TateQuotientMap`) is surjective on points, because it satisfies
the universal property of the quotient by `tateInvPeriodSqAction`. -/
theorem tateQuotientPi_base_surjective :
    Function.Surjective (tateQuotientPi R I q hq hI).base :=
  LocallyRingedSpace.base_surjective_of_isActionQuotient
    (tateQuotientIsActionQuotient R I q hq hI)

/-- **`𝔈_q` carries the quotient topology of `T_inv`.** -/
theorem tateQuotientPi_base_isQuotientMap :
    Topology.IsQuotientMap (tateQuotientPi R I q hq hI).base :=
  LocallyRingedSpace.base_isQuotientMap_of_isActionQuotient
    (tateQuotientIsActionQuotient R I q hq hI)

/-- **The points of `𝔈_q` are the `q^{2ℤ}`-orbits of the points of `T_inv`.** The concrete content
of `tateQuotientIsActionQuotient` at the level of underlying sets. -/
theorem tateQuotientPi_base_eq_iff
    (x y : (tateChainInv R I q hq hI).toLocallyRingedSpace) :
    (tateQuotientPi R I q hq hI).base x = (tateQuotientPi R I q hq hI).base y ↔
      ∃ n : Multiplicative ℤ, (tateInvPeriodSqAction R I q hq hI n).hom.base x = y :=
  LocallyRingedSpace.base_eq_iff_of_isActionQuotient
    (tateQuotientIsActionQuotient R I q hq hI) x y

end Tate

end AlgebraicGeometry
