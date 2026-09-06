import Mathlib.Data.Countable.Basic
import Mathlib.RingTheory.Localization.FractionRing

set_option linter.style.header false

/-!
# A localization of a countable ring is countable

Every element of a localization is `IsLocalization.mk'` applied to a numerator in `R` and a
denominator in the submonoid `S` being inverted (`IsLocalization.mk'_surjective`), so a
localization is a surjective image of `R × S`. When `R` is countable so is `R × S`, and a
surjective image of a countable type is countable (`Function.Surjective.countable`).

Mathlib does not have this. `Mathlib.Data.Countable.Basic` closes `Countable` under products,
sums, subtypes and quotients, but nothing under `Mathlib.RingTheory.Localization` carries a
`Countable` instance, and `Countable (FractionRing ℤ)` fails to synthesize with `Countable ℤ` in
scope — checked by trying to produce it, and separately at `Localization (nonZeroDivisors ℤ)`,
since `FractionRing` is an `abbrev` for the latter and the two could in principle have been found
by different paths. Neither is.

The consumer is `FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, where
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` is stated under
`[Countable (FractionRing R)]` — the hypothesis is on the fraction field, because that is what the
proof there uses. This file is what discharges it from a hypothesis on `R` itself, which is the
form a consumer at a concrete ring has.

## Main results

* `IsLocalization.countable`: any `A` exhibited as a localization of a countable `R` is countable.
  Not an instance — the submonoid occurs in the hypotheses and not in the conclusion, so instance
  search would have nothing to unify it against.
* `Localization.instCountable`: the instance form, at the canonical model. It fires at
  `FractionRing R` as well, that being an `abbrev` for `Localization (nonZeroDivisors R)`.
-/

namespace IsLocalization

/-- **A localization of a countable ring is countable.** Every element is `IsLocalization.mk'` of
a numerator and a denominator (`IsLocalization.mk'_surjective`), so `A` is a surjective image of
`R × S`, and both factors are countable — the second by `Subtype.countable`, which has to be
supplied by hand because instance search does not unfold the `SetLike` coercion of a `Submonoid`
to reach it.

Stated for an arbitrary model `A` rather than for `Localization S`, so that it applies to
`FractionRing`, to `Localization.Away` and to any ring a consumer has already exhibited as a
localization. **Not an instance**: `S` appears in the hypotheses and not in the conclusion, so a
search for `Countable A` has nothing to unify it against. The instance is
`Localization.instCountable` below, at the canonical model. -/
theorem countable {R : Type*} [CommSemiring R] (S : Submonoid R) (A : Type*) [CommSemiring A]
    [Algebra R A] [IsLocalization S A] [Countable R] : Countable A := by
  haveI : Countable S := Subtype.countable
  refine Function.Surjective.countable
    (f := fun p : R × S => IsLocalization.mk' A p.1 p.2) fun z => ?_
  obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective S z
  exact ⟨(x, y), rfl⟩

end IsLocalization

namespace Localization

/-- **The canonical localization of a countable ring is countable**, as an instance.

The head symbol of the conclusion is `Localization`, so this fires only where a localization is
already written down, and it cannot loop, its own hypothesis being about a different type. It
reaches `FractionRing R` too, that being an `abbrev` for `Localization (nonZeroDivisors R)`. -/
instance instCountable {R : Type*} [CommSemiring R] (S : Submonoid R) [Countable R] :
    Countable (Localization S) :=
  IsLocalization.countable S _

end Localization

/-- `Localization.instCountable` fires at a concrete ring: the rationals, presented as the
fraction field of the integers, are countable. -/
example : Countable (FractionRing ℤ) := inferInstance
