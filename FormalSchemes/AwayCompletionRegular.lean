import FormalSchemes.BasicOpenChart
import FormalSchemes.RestrictedPowerSeriesNoetherian
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Submodule

set_option linter.style.header false

/-!
# Regularity rises to a completed localization

`FormalSpectrum.awayCompletion L f` is the `L`-adic completion of `A_f`. Over a **Noetherian** base
both of those steps are flat — a localization always is, and an adic completion of a Noetherian
ring is (`AdicCompletion.flat_of_isNoetherian`) — so a nonzerodivisor of `A` stays a nonzerodivisor
in `A{1/f}`.

That is the whole content of this file, and it is the tool that turns a regularity question about a
chart's target ring into a regularity question about the ring the chart was cut out of.

## Contents

* `FormalSpectrum.isNoetherianRing_awayCompletion` — `A{1/f}` is Noetherian when `A` is
  (`AdicCompletion.isNoetherianRing`, i.e. Atiyah–Macdonald 10.26, at the localization). This is
  what lets the previous item be **iterated**: `A{1/f}{1/g}` is again a completed localization of a
  Noetherian ring. It is an `instance`, so the second step of such a tower finds the first step's
  Noetherianity with nothing supplied by the caller.
* `FormalSpectrum.flat_awayCompletion` — `A{1/f}` is a flat `A`-module, the two flat steps composed
  by `Module.Flat.trans`. Deliberately **not** an instance: neither `Module.Flat` witness it
  composes is one at these arguments, and making it an instance would send instance search through
  `Module.Flat.trans` at every `awayCompletion`.
* `FormalSpectrum.isLeftRegular_algebraMap_awayCompletion` — left-regularity rises along
  `algebraMap A (awayCompletion L f)`.

## What this does *not* say

Nothing in the other direction. An element can perfectly well become regular in `A{1/f}` without
being regular in `A` — the localization kills `f`-power torsion — so these are one-way statements
and a consumer that wants an `iff` needs a different argument.
-/

noncomputable section

universe u

namespace FormalSpectrum

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (L : Ideal A) (f : A)

/-- **A completed localization of a Noetherian ring is Noetherian.** The localization `A_f` is
Noetherian (`IsLocalization`'s instance), every ideal of it is then finitely generated, and
`AdicCompletion.isNoetherianRing` (Atiyah–Macdonald 10.26,
`FormalSchemes.RestrictedPowerSeriesNoetherian`) applies.

An `instance` because `isLeftRegular_algebraMap_awayCompletion` has to be applied **twice** in a
row at a nested chart, and the second application needs the first ring's Noetherianity. As an
instance it is found there automatically; `L` and `f` are both determined by the goal
`IsNoetherianRing (awayCompletion L f)`, so there is nothing for instance search to guess. -/
instance isNoetherianRing_awayCompletion : IsNoetherianRing (awayCompletion L f) :=
  AdicCompletion.isNoetherianRing _ (IsNoetherian.noetherian _)

/-- **`A{1/f}` is flat over `A`.** The composite of two flat extensions: `A → A_f` is flat because
it is a localization (`IsLocalization.flat`), and `A_f → awayCompletion L f` is flat because `A_f`
is Noetherian (`AdicCompletion.flat_of_isNoetherian`, which is an instance and picks up the
Noetherianity of `A_f` from `IsLocalization`'s own instance).

Not an instance, for the reason in this file's module docstring.
`isLeftRegular_algebraMap_awayCompletion` is the one consumer here and applies it by name. -/
theorem flat_awayCompletion : Module.Flat A (awayCompletion L f) :=
  haveI : Module.Flat A (Localization.Away f) := IsLocalization.flat _ (Submonoid.powers f)
  haveI : Module.Flat (Localization.Away f) (awayCompletion L f) :=
    AdicCompletion.flat_of_isNoetherian _
  Module.Flat.trans A (Localization.Away f) (awayCompletion L f)

/-- **Left-regularity rises to a completed localization**, over a Noetherian base.

`IsSMulRegular.of_flat` at `flat_awayCompletion`, in one step. The two-step form — regularity into
`A_f` by `IsSMulRegular.of_isLocalization`, then into the completion by `IsSMulRegular.of_flat`,
recomposed with `IsScalarTower.algebraMap_apply` — proves the same thing and is what this file
originally did; going through the named flatness of the composite is shorter and keeps the reason
in one place.

`IsLeftRegular a` and `IsSMulRegular A a` are the same statement — `a • ·` and `a * ·` are the same
function on `A` — which is why `ha` is passed to a lemma about the latter with no conversion, and
why the result needs only a type ascription to come back. -/
theorem isLeftRegular_algebraMap_awayCompletion {a : A} (ha : IsLeftRegular a) :
    IsLeftRegular (algebraMap A (awayCompletion L f) a) :=
  haveI := flat_awayCompletion L f
  (IsSMulRegular.of_flat (S := awayCompletion L f) ha : IsSMulRegular _ _)

end FormalSpectrum
