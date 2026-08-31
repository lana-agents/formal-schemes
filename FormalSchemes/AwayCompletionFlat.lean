import FormalSchemes.BasicOpenChart
import FormalSchemes.RestrictedPowerSeriesNoetherian
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Localization.Submodule

set_option linter.style.header false

/-!
# The completed localization of a Noetherian ring is Noetherian and flat over it

`FormalSpectrum.awayCompletion L f` is `AdicCompletion (L·A_f) A_f` for
`A_f = Localization.Away f` (`FormalSchemes.BasicOpenChart`). Over a Noetherian base both steps of
that construction are standard:

* `A_f` is Noetherian (`IsLocalization.isNoetherianRing`) and flat over `A`
  (`IsLocalization.flat`);
* the adic completion of a Noetherian ring along any ideal is Noetherian
  (`AdicCompletion.isNoetherianRing`, `FormalSchemes.RestrictedPowerSeriesNoetherian`, which is
  Atiyah–Macdonald 10.26) and flat over it (`AdicCompletion.flat_of_isNoetherian`).

Neither hypothesis needs the ideal to be finitely generated: over a Noetherian ring every ideal is,
so `IsNoetherian.noetherian` discharges `AdicCompletion.isNoetherianRing`'s `K.FG` argument.

## Main results

* `FormalSpectrum.instIsNoetherianRingAwayCompletion` — `A{1/f}` is Noetherian, as an instance, so
  the construction iterates: `A{1/f}{1/g}` is Noetherian and flat over `A{1/f}` with no further
  hypothesis.
* `FormalSpectrum.flat_awayCompletion` — `A{1/f}` is a flat `A`-module.
* `FormalSpectrum.isLeftRegular_awayCompletionHom` — **the consequence this file exists for**: a
  left-regular element of `A` stays left-regular in `A{1/f}`. This is `IsSMulRegular.of_flat`;
  `FormalSpectrum.awayCompletionHom L f` is the `A`-algebra structure map of `A{1/f}` on the nose,
  so no transport is needed between the two spellings.

`FormalSpectrum.isLeftRegular_of_ringEquiv` is the transport of left-regularity along a ring
isomorphism, which every consumer of the previous item on a *presheaf-section* spelling of `A{1/f}`
needs; it is a general fact about `RingEquiv` and has nothing to do with completion.

## What is *not* proved

* **Nothing about faithful flatness, injectivity of `awayCompletionHom`, or the converse.** A
  left-regular element of `A{1/f}` need not come from a left-regular element of `A` — indeed `f`
  itself becomes a unit — and none of that is used or claimed.
* **Nothing without `IsNoetherianRing A`.** Both halves of the tower use it, and adic completion of
  a non-Noetherian ring is not flat in general.

## References

* [Atiyah–Macdonald, *Introduction to Commutative Algebra*], Prop. 10.14, Prop. 10.26.
* [The Stacks Project, Tag 00MB](https://stacks.math.columbia.edu/tag/00MB) (completion is flat
  over a Noetherian ring).
-/

noncomputable section

universe u

namespace FormalSpectrum

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (L : Ideal A) (f : A)

/-- **`A{1/f}` is Noetherian when `A` is.** `Localization.Away f` is Noetherian, hence its ideal
`L · A_f` is finitely generated, and `AdicCompletion.isNoetherianRing` (Atiyah–Macdonald 10.26,
`FormalSchemes.RestrictedPowerSeriesNoetherian`) applies.

An `instance`, so that the two-step tower `A{1/f}{1/g}` is available with no extra hypothesis:
`FormalSpectrum.flat_awayCompletion` at the second step finds this at the first. -/
instance instIsNoetherianRingAwayCompletion : IsNoetherianRing (awayCompletion L f) :=
  AdicCompletion.isNoetherianRing _ (IsNoetherian.noetherian _)

/-- **`A{1/f}` is flat over `A`.** The composite of two flat extensions: `A → A_f` is flat because
it is a localization (`IsLocalization.flat`), and `A_f → AdicCompletion (L · A_f) A_f` is flat
because `A_f` is Noetherian (`AdicCompletion.flat_of_isNoetherian`).

Not an `instance`: the two `Module.Flat` witnesses it composes are not instances at these
arguments, and making this one would send instance search through `Module.Flat.trans` on every
`awayCompletion`. Consumers apply it by name. -/
theorem flat_awayCompletion : Module.Flat A (awayCompletion L f) :=
  haveI : Module.Flat A (Localization.Away f) := IsLocalization.flat _ (Submonoid.powers f)
  haveI : Module.Flat (Localization.Away f) (awayCompletion L f) :=
    AdicCompletion.flat_of_isNoetherian _
  Module.Flat.trans A (Localization.Away f) (awayCompletion L f)

/-- **A left-regular element of `A` stays left-regular in `A{1/f}`.** `IsSMulRegular.of_flat` at
`FormalSpectrum.flat_awayCompletion`.

`IsSMulRegular A a` and `IsLeftRegular a` are the same statement — multiplication by `a` on `A` is
injective — and `FormalSpectrum.awayCompletionHom L f` is `algebraMap A (awayCompletion L f)`, so
the transfer is `IsSMulRegular.of_flat` with no bridging. -/
theorem isLeftRegular_awayCompletionHom {a : A} (ha : IsLeftRegular a) :
    IsLeftRegular (awayCompletionHom L f a) :=
  haveI := flat_awayCompletion L f
  (IsSMulRegular.of_flat (S := awayCompletion L f) ha : IsSMulRegular _ _)

end FormalSpectrum

namespace FormalSpectrum

/-- **Left-regularity transports backwards along a ring isomorphism.** If `e x` is left-regular in
the target then `x` is left-regular in the source.

Stated in this direction because that is the one a presheaf-section consumer needs: the regularity
is proved in the completed-localization spelling and wanted in the section-ring spelling, and the
identification `FormalSpectrum.sectionsEquivOfEqBasicOpen` goes from sections to completion. -/
theorem isLeftRegular_of_ringEquiv {B C : Type u} [CommRing B] [CommRing C] (e : B ≃+* C) {x : B}
    (h : IsLeftRegular (e x)) : IsLeftRegular x := fun u v huv => by
  apply e.injective
  exact h (by simpa only [← map_mul] using congrArg e huv)

end FormalSpectrum
