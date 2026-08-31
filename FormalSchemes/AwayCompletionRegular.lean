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
  Noetherian ring.
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

Stated because `isLeftRegular_algebraMap_awayCompletion` has to be applied **twice** in a row at a
nested chart, and the second application needs the first ring's Noetherianity. -/
theorem isNoetherianRing_awayCompletion : IsNoetherianRing (awayCompletion L f) :=
  AdicCompletion.isNoetherianRing _ (IsNoetherian.noetherian _)

/-- **Left-regularity rises to a completed localization**, over a Noetherian base.

`a` regular in `A` gives `algebraMap A A_f a` regular in `A_f` because a localization is flat
(`IsSMulRegular.of_isLocalization`), and that in turn gives the image in the completion because an
adic completion of a Noetherian ring is flat over it (`AdicCompletion.flat_of_isNoetherian`, fed to
`IsSMulRegular.of_flat`). `IsScalarTower.algebraMap_apply` composes the two structural maps into
`algebraMap A (awayCompletion L f)`.

`IsLeftRegular a` and `IsSMulRegular A a` are the same statement — `a • ·` and `a * ·` are the same
function on `A` — which is why `ha` is passed to a lemma about the latter with no conversion. -/
theorem isLeftRegular_algebraMap_awayCompletion {a : A} (ha : IsLeftRegular a) :
    IsLeftRegular (algebraMap A (awayCompletion L f) a) := by
  have h1 : IsSMulRegular (Localization.Away f) (algebraMap A (Localization.Away f) a) :=
    IsSMulRegular.of_isLocalization (S := Localization.Away f) (p := Submonoid.powers f) ha
  have h2 := h1.of_flat (S := awayCompletion L f)
  rw [← IsScalarTower.algebraMap_apply] at h2
  exact h2

end FormalSpectrum
