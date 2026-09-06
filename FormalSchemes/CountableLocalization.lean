import Mathlib.Data.Countable.Basic
import Mathlib.RingTheory.Localization.FractionRing

set_option linter.style.header false

/-!
# A localization of a countable ring is countable

Every element of `Localization M` is `Localization.mk r s` for a numerator `r` and a denominator
`s : M`, so `Localization M` is a surjective image of `A × M`. When `A` is countable so is
`A × M`, and a surjective image of a countable type is countable
(`Function.Surjective.countable`).

**The statement is not new and is not restated here.**
`Localization.countable_of_countable` was proved in
`FormalSchemes.CompletionToSpecNotClosedImmersion`, where the uncountability of a power series
ring is played off against the countability of a stalk. It is **moved** here — same name, same
type, same proof — because it has acquired a second consumer that cannot reach its old home: that
file has forward closure 25 and is not in the closure of
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, nor that of it. The statement
mentions no formal scheme, no ideal of definition and no power series, so a Mathlib-only leaf is
where it belongs and both consumers reach it from there.

The one change is `theorem` to **`instance`**. That is what
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` needs: it is stated under
`[Countable (FractionRing R)]` — the hypothesis is on the fraction field, because that is what its
proof uses — and a consumer at a concrete ring has `[Countable R]` instead. Adding a *second*
declaration for the instance form was the alternative and was rejected: it would be a
project-internal duplicate of exactly the kind
`scripts/symm_duplicate_statement_scan.lean` exists to catch, two names for one type under one set
of binders. The existing consumer passes the submonoid explicitly through a `haveI` and is
unaffected by the promotion.

Mathlib does not have the statement in any form. `Mathlib/Data/Countable/Basic.lean` closes
`Countable` under products, sums, subtypes and quotients, but no file under Mathlib's
localization directory carries a `Countable` instance: `Countable (FractionRing ℤ)`
fails to synthesize with `Countable ℤ` in scope, and so does
`Countable (Localization (nonZeroDivisors ℤ))` — checked separately, since `FractionRing` is an
`abbrev` for the latter and the two could in principle have been found by different paths.

## Main results

* `Localization.countable_of_countable`: **a localization of a countable ring is countable**, as
  an instance. It fires at `FractionRing A` too, that being an `abbrev` for
  `Localization (nonZeroDivisors A)`.
-/

universe u

namespace Localization

/-- **A localization of a countable ring is countable**: every element is `Localization.mk r s`,
so `R × M` surjects onto it.

An `instance` rather than a `theorem`: the head symbol of the conclusion is `Localization`, so it
fires only where a localization is already written down, and it cannot loop, its own hypothesis
being about a different type. `FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` is
what wants it found by search rather than supplied by hand, at `FractionRing R`. -/
instance countable_of_countable {A : Type u} [CommRing A] [Countable A] (M : Submonoid A) :
    Countable (Localization M) := by
  refine Function.Surjective.countable (f := fun q : A × M => Localization.mk q.1 q.2) ?_
  intro z
  induction z using Localization.ind with
  | _ q => exact ⟨(q.1, q.2), rfl⟩

end Localization

/-- The instance fires at a concrete ring: the rationals, presented as the fraction field of the
integers, are countable. -/
example : Countable (FractionRing ℤ) := inferInstance
