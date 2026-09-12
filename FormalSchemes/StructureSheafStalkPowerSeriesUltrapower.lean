import FormalSchemes.StructureSheafStalkPowerSeriesCounterexample
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot

set_option linter.style.header false

/-!
# The denominator condition without a common denominator: an ultrapower of `ℤ`

`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` names the condition
`FormalSpectrum.HasBoundedDenominators` — every `ℕ`-indexed family in `Frac R` is cleared into `R`
by the powers of a single `m ≠ 0` — proves that it is what the surjectivity half of
`FormalSpectrum.IsStalkLimit` at the generic point of `Spf (R⟦X⟧, (X))` amounts to, and proves that
over a **countable** fraction field it collapses onto the much stronger condition that some single
`R[1/m]` is already `Frac R` (`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective`). About
that hypothesis it says, in its module docstring:

> Whether `FormalSpectrum.HasBoundedDenominators` is equivalent to *some `R[1/m]` is already
> `Frac R`* at an arbitrary domain is **not settled here in either direction** […] The hypothesis
> is not known to be removable and is not known to be needed.

**This file settles it: the hypothesis is needed.** The witness is an ultrapower of `ℤ`.

> `FormalSpectrum.hasBoundedDenominators_and_not_exists_surjective_intUltrapower`: for a
> non-principal ultrafilter `φ` on `ℕ`, the ultrapower `FormalSpectrum.IntUltrapower φ` satisfies
> the denominator condition and **no** single `m ≠ 0` makes `R[1/m] → Frac R` surjective.

The mechanism is the one the counterexample file's docstring names as the obstruction to removing
the hypothesis, realised: the condition only ever sees **countable** families, and in an ultrapower
every countable family of nonzero elements divides a single element while no element is divisible
by everything.

## The two halves, and where each comes from

* **The condition holds** (`FormalSpectrum.exists_forall_dvd_intUltrapower`). Countably many nonzero
  germs `d n` have representatives `f n : ℕ → ℤ`; each may be replaced by the nowhere-zero
  `e n i = if f n i = 0 then 1 else f n i`, which has the same germ because `d n ≠ 0` puts
  `{i | f n i ≠ 0}` in the ultrafilter. The **diagonal product**
  `m i = ∏ n ∈ Finset.range (i + 1), e n i` is then divisible by `e n i` at every `i ≥ n`, and
  `{i | n ≤ i}` is in the ultrafilter because it is non-principal. So `d n ∣ m` — with exponent
  `1`, not merely up to powers.
* **No single denominator works** (`FormalSpectrum.exists_forall_not_dvd_pow_intUltrapower`). Given
  `m ≠ 0` with representative `M`, a prime `p i > (M i).natAbs` at each `i` gives a nonzero germ
  dividing no power of `m`: on the large set where `M i ≠ 0`, `p i ∣ M i ^ k` would force
  `p i ∣ M i` and hence `p i ≤ |M i|`.

Neither half needs saturation, transfer, or any model theory: the first is one
`Finset.dvd_prod_of_mem` under a `filter_upwards`, and the second is `Nat.exists_infinite_primes`
with `Prime.dvd_of_dvd_pow`.

## Why the two refuting criteria on the tree do not apply

A reader who knows `FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` will reach for one
of them at once, and both fail on their hypotheses rather than on their conclusions.

The family that answers both is the same one:
`FormalSpectrum.exists_prime_family_not_associated_intUltrapower` gives infinitely many pairwise
non-associated primes, the germs of `2, 3, 5, …`. The two criteria differ precisely in which of
their hypotheses the ultrapower falsifies, and that pair of answers is complete.

* `FormalSpectrum.not_hasBoundedDenominators_of_primes` asks for a family of primes that **no**
  single `m ≠ 0` is divisible by, with no `[UniqueFactorizationMonoid R]` anywhere. In an
  ultrapower that hypothesis is unsatisfiable, and `FormalSpectrum.exists_forall_dvd_intUltrapower`
  is exactly the statement that it is: *every* countable family of nonzero elements, primes or not,
  is divisible into a single element — applied to the family above, it produces the very `m` the
  criterion asks not to exist.
* `FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated` and the classification
  `FormalSpectrum.hasBoundedDenominators_iff_finite_primes` both assume
  `[UniqueFactorizationMonoid R]`, and `FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower`
  says the ultrapower does not satisfy it — so both are inapplicable by a theorem and not merely by
  an instance nobody has supplied. For **both** the ultrapower says more than *inapplicable*. It
  satisfies the criterion's other two hypotheses, by the family above, and satisfies the
  denominator condition anyway
  (`FormalSpectrum.hasBoundedDenominators_and_exists_primes_not_associated_intUltrapower`); and it
  satisfies the classification's left-hand side while falsifying its right-hand side, by that same
  family read at `Associates`
  (`FormalSpectrum.hasBoundedDenominators_and_infinite_primes_intUltrapower`). So
  `[UniqueFactorizationMonoid R]` is **needed** in each and not merely absent here
  (`FormalSpectrum.not_forall_primes_not_associated_imp_not_hasBoundedDenominators`,
  `FormalSpectrum.not_forall_hasBoundedDenominators_iff_finite_primes`). What the classification's
  refutation reaches is its **forward** direction only; that finitely many prime classes force the
  condition without unique factorisation is refuted at a **different** ring, in the last section of
  this file, and the ultrapower bears on it not at all.

None of this contradicts `FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower`: a domain may
have infinitely many pairwise non-associated primes and fail to be a unique factorisation domain,
because the primes need not generate, and nothing below says these do.

## What this buys the stalk half

`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators` carries no
hypothesis beyond `[IsDomain R]`, so the condition transfers and
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_intUltrapower` is a **new positive value of
the predicate**. It is of a kind the tree did not have: at a field, at a discrete valuation ring and
at the closed point of a local ring the predicate holds because one localization already does all of
the work, and here it holds while **no** localization at a single element is the fraction field
(`FormalSpectrum.isStalkLimit_and_not_exists_surjective_intUltrapower`).

## What the ring is not, and why that is cheap

Three properties of the ultrapower follow from the two halves with nothing added:

* **uncountable** — were `Frac R` countable then
  `FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` would *apply* and produce the very
  `m` the second half refutes, so the collapse theorem is used here as a tool rather than as a
  target;
* **not a unique factorisation domain** — at a unique factorisation domain the condition forces
  finitely many primes up to associates and hence a single clearing `m`
  (`FormalSpectrum.exists_forall_dvd_pow_of_hasBoundedDenominators`), and again there is none;
* **not Noetherian** — the single `m` clearing `c, c², c³, …` for `c` the germ of the constant `2`
  lies in `⋂ᵢ (c)ⁱ`, which Krull intersection makes `⊥` in a Noetherian domain.

Each is a contradiction from a classification already on the tree. **None of them develops any
factorisation theory of the ring, and none computes a cardinal**; see *What is not proved here*.

## The primes of the ultrapower, and the two hypotheses they measure

One positive arithmetic fact is proved as well, and it does not belong under the heading above.
The germs of the constant sequences at `2, 3, 5, …` are primes of the ultrapower and are pairwise
non-associated (`FormalSpectrum.exists_prime_family_not_associated_intUltrapower`): primality
transfers pointwise because `p ∣ ab` is an eventual pointwise divisibility and
`Ultrafilter.eventually_or` chooses a side of the resulting disjunction globally, and
non-associatedness comes back down because both divisibilities are eventual and a set of an
ultrafilter is nonempty.

**It is proved because hypotheses need measuring, and not for its own sake**, and it measures the
same instance on two different theorems.
`FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated` concludes
`¬ HasBoundedDenominators R` from such a family *plus* `[UniqueFactorizationMonoid R]`. The
ultrapower supplies the family and satisfies the denominator condition anyway, so that hypothesis
is **needed** and not merely unavailable here. The classification
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes` carries the same instance, and the same
family read at `Associates` — where non-associatedness is injectivity of `n ↦ Associates.mk (p n)`
— makes `{a : Associates R | Prime a}` infinite
(`FormalSpectrum.infinite_setOf_prime_associates_intUltrapower`), so the ultrapower satisfies that
theorem's left-hand side and falsifies its right-hand side, and its instance is needed too. Both
are the shape of `FormalSpectrum.not_forall_hasBoundedDenominators_imp_exists_surjective`, a
hypothesis shown needed by a witness rather than shown absent at one ring. What this family
measures is the classification's **forward** direction; its backward direction is out of the
ultrapower's reach and is measured in the last section of this file, at a different ring.

## A second witness, and why it is in a file named for the ultrapower

The last section of this file is about a **different ring**, and the file's name is the ultrapower's
rather than that ring's. The subject the name abbreviates is not one ring but one question — which
hypotheses of the passages from the denominator condition to a single clearing `m` can be deleted —
and every `not_forall_…` refutation on this tree is here. Two of those passages have hypotheses
**the ultrapower provably cannot measure**, `FormalSpectrum.forall_dvd_pow_prod` and
`FormalSpectrum.exists_forall_dvd_pow_of_finite_primes`: each wants finitely many prime associate
classes and the ultrapower has infinitely many. The witness that measures both is the ring of all
algebraic integers, which has **no** prime elements at all — so the first is refuted at the empty
`Finset`, and the second at a ring where its hypothesis holds vacuously and its conclusion fails
for every candidate.

It is one `abbrev` and ten theorems, one of them `private`, none of which develops any theory of
that ring, and it is in this file rather than in a new module because the sentences it falsifies
are in this file's docstring and beside the two theorems in
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` that it measures. A reader who wants
only the ultrapower can stop at *The value of the predicate at the ultrapower*; nothing above the
last section mentions the second ring except to say which question it answers.

## Main results

* `FormalSpectrum.hasBoundedDenominators_iff_forall_exists_dvd_pow`: **the denominator condition is
  a divisibility statement in `R`** — every countable family of nonzero elements divides powers of a
  single element — at an **arbitrary** domain and with no countability hypothesis. The
  arbitrary-domain companion of `FormalSpectrum.hasBoundedDenominators_iff_forall_dvd_pow`, which
  quantifies over all of `R` and needs `[Countable (FractionRing R)]`.
* `FormalSpectrum.hasBoundedDenominators_of_forall_exists_dvd`: the same as a sufficient criterion
  with the exponent fixed at `1`.
* `FormalSpectrum.IntUltrapower`, and its `NoZeroDivisors` and `IsDomain` instances.
* `FormalSpectrum.exists_forall_dvd_intUltrapower`,
  `FormalSpectrum.hasBoundedDenominators_intUltrapower`: **the condition holds in the ultrapower.**
* `FormalSpectrum.exists_forall_not_dvd_pow_intUltrapower`,
  `FormalSpectrum.not_exists_surjective_awayToFractionRing_intUltrapower`: **and no single `R[1/m]`
  is its fraction field.**
* `FormalSpectrum.exists_forall_dvd_pow_of_hasBoundedDenominators`: at a **unique factorisation
  domain** the collapse holds with no countability at all, the finitely many primes having a
  product that clears everything. **Its instance is needed too**, by the entry three below.
* `FormalSpectrum.not_exists_denominator_intUltrapower`,
  `FormalSpectrum.not_exists_forall_dvd_pow_intUltrapower`,
  `FormalSpectrum.not_exists_isField_away_intUltrapower`: **the other three spellings of the
  collapse fail at the ultrapower too**, each refuted on the right-hand side its own `↔` states.
* `FormalSpectrum.hasBoundedDenominators_and_not_exists_surjective_intUltrapower`,
  `FormalSpectrum.hasBoundedDenominators_and_no_collapse_intUltrapower`,
  `FormalSpectrum.not_forall_hasBoundedDenominators_imp_exists_surjective`: **the countability
  hypothesis of the collapse is needed**, in each of its four spellings, stated at the ultrapower
  and as the refutation of the quantified implication.
* `FormalSpectrum.hasBoundedDenominators_and_not_exists_forall_dvd_pow_intUltrapower`,
  `FormalSpectrum.not_forall_hasBoundedDenominators_imp_exists_forall_dvd_pow`: **the
  `[UniqueFactorizationMonoid R]` of
  `FormalSpectrum.exists_forall_dvd_pow_of_hasBoundedDenominators` is needed**, at the
  ultrapower — it satisfies that implication's hypothesis and falsifies its conclusion, which is
  `FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower`'s proof read the other way round.
  **The forward passage only**; `FormalSpectrum.exists_forall_dvd_pow_of_finite_primes` and
  `FormalSpectrum.forall_dvd_pow_prod` are measured at a different ring, in the last two entries
  below.
* `FormalSpectrum.eventually_dvd_of_coe_dvd_coe_intUltrapower`,
  `FormalSpectrum.coe_dvd_coe_iff_eventually_dvd_intUltrapower`: **divisibility of germs is eventual
  pointwise divisibility**, the converse of the direction this file already had.
* `FormalSpectrum.prime_coe_intUltrapower`, `FormalSpectrum.not_isUnit_coe_intUltrapower`,
  `FormalSpectrum.exists_prime_family_not_associated_intUltrapower`: **a pointwise prime is prime,
  and the ultrapower has infinitely many pairwise non-associated primes** — the germs of
  `2, 3, 5, …`, enumerated from `Nat.exists_infinite_primes` rather than from Mathlib's nth-prime
  function, whose module is outside this project's Mathlib closure.
* `FormalSpectrum.hasBoundedDenominators_and_exists_primes_not_associated_intUltrapower`,
  `FormalSpectrum.not_forall_primes_not_associated_imp_not_hasBoundedDenominators`: **the
  `[UniqueFactorizationMonoid R]` of
  `FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated` is needed**, again at the
  ultrapower and not merely unavailable there — its other two hypotheses hold and its conclusion
  fails.
* `FormalSpectrum.infinite_setOf_prime_associates_intUltrapower`,
  `FormalSpectrum.hasBoundedDenominators_and_infinite_primes_intUltrapower`,
  `FormalSpectrum.not_forall_hasBoundedDenominators_imp_finite_primes`,
  `FormalSpectrum.not_forall_hasBoundedDenominators_iff_finite_primes`: **the same instance is
  needed in the classification `FormalSpectrum.hasBoundedDenominators_iff_finite_primes` too**, and
  at the ultrapower again —
  the same family read at `Associates` makes the prime classes infinite while the condition holds,
  which refutes the classification's forward direction with the instance deleted, and the `↔` with
  it. **Only the forward direction**; the backward one is out of the ultrapower's reach and is
  refuted at a different ring, in the last entry below.
* `FormalSpectrum.not_countable_intUltrapower`,
  `FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower`,
  `FormalSpectrum.not_isNoetherianRing_intUltrapower`: **the ultrapower is uncountable, is not a
  unique factorisation domain and is not Noetherian** — each from the two halves above, with no
  factorisation theory, no cardinal arithmetic and no model theory.
* `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_intUltrapower`,
  `FormalSpectrum.isStalkLimit_and_not_exists_surjective_intUltrapower`: **the geometric value**,
  and that no single localization explains it.
* `FormalSpectrum.AlgInt`, `FormalSpectrum.exists_sq_eq_algInt`,
  `FormalSpectrum.not_prime_algInt`, `FormalSpectrum.not_isUnit_two_algInt`,
  `FormalSpectrum.not_forall_forall_dvd_pow_prod`: **the `[UniqueFactorizationMonoid R]` of
  `FormalSpectrum.forall_dvd_pow_prod` is needed too** — and **not** at the ultrapower, which
  cannot measure it, but at the ring of all algebraic integers, which has **no** prime elements and
  a nonzero non-unit. The refutation is the empty `Finset`, where that theorem says every nonzero
  element is a unit.
* `FormalSpectrum.finite_setOf_prime_associates_algInt`,
  `FormalSpectrum.exists_int_ne_zero_dvd_algInt`,
  `FormalSpectrum.dvd_of_intCast_dvd_intCast_algInt`,
  `FormalSpectrum.exists_ne_zero_forall_not_dvd_pow_algInt`,
  `FormalSpectrum.not_forall_exists_forall_dvd_pow_of_finite_primes`: **the
  `[UniqueFactorizationMonoid R]` of
  `FormalSpectrum.exists_forall_dvd_pow_of_finite_primes` is needed too**, at the same ring, which
  is where the classification's backward direction is settled. Both halves are total rather than
  sampled: the hypothesis holds because that ring has **no** prime associate classes, and the
  conclusion fails because **no** nonzero element of it is a clearing element. The argument is
  three elementary steps and **no valuation** — a nonzero rational integer that the candidate
  divides, the descent of a divisibility of rational integers back to `ℤ`, and a rational prime
  larger than that integer.

## What is *not* proved here

**No hypothesis is removed from anything.** This file proves that
`[Countable (FractionRing R)]` **cannot** be removed from
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` or from anything derived from it,
which is the opposite operation; every statement in
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` is consumed exactly as it stands. The
*other* direction of that equivalence, `FormalSpectrum.hasBoundedDenominators_of_surjective`, holds
at every domain and is untouched.

**Nothing here is a statement about `FormalSpectrum.IsStalkLimit` in general, and nothing here
repairs EGA I 10.8's stalk half.** One further positive value is added, at one point of one formal
spectrum, and which hypothesis makes the stalk half true is no better determined than before.

**The ring's negative properties are proved, and one positive arithmetic fact with them; its
factorisation theory is not.** That `FormalSpectrum.IntUltrapower φ` is uncountable, is not a
unique factorisation domain and is not Noetherian are the section *What the ring is not*, and each
is read off the two halves above rather than developed. The germs of `2, 3, 5, …` **are** primes of
it, pairwise non-associated, and that is now the section *The primes of the ultrapower* rather than
a sentence here; it is proved because
`FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated` and
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes` each have an instance that needs
measuring, and not for its own sake. **No factorisation of any element is exhibited**, no claim is
made that these are all the primes or that they generate anything, no prime is counted, and no
cardinal is computed — `FormalSpectrum.not_countable_intUltrapower` is a negation of `Countable`
and supplies no lower bound.

In particular the paragraph above about the refuting criteria still argues from their
**hypotheses** and not from any factorisation theory: one asks for a family no element is divisible
by, which `FormalSpectrum.exists_forall_dvd_intUltrapower` refutes outright, and the other asks for
unique factorisation, which is *needed* rather than merely absent —
`FormalSpectrum.hasBoundedDenominators_and_exists_primes_not_associated_intUltrapower` supplies its
other two hypotheses and the denominator condition together, so
`FormalSpectrum.not_forall_primes_not_associated_imp_not_hasBoundedDenominators` refutes it with
`[UniqueFactorizationMonoid R]` deleted. The classification
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes` is refuted the same way and from the same
family (`FormalSpectrum.not_forall_hasBoundedDenominators_iff_finite_primes`), and both are
strictly stronger than `FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower`, which says
only that they do not apply here. **Neither refutation is a factorisation of anything**, and
**neither reaches the classification's backward direction, which the ultrapower cannot reach at
all**: *finitely many prime classes ⇒ the denominator condition* is
`FormalSpectrum.exists_forall_dvd_pow_of_finite_primes`, whose hypothesis fails at a ring with
infinitely many prime classes. That instance is measured in the last section of this file, at the
ring of all algebraic integers, where the hypothesis holds vacuously
(`FormalSpectrum.not_forall_exists_forall_dvd_pow_of_finite_primes`).

**Nothing is proved about the ring of all algebraic integers beyond seven facts**, and they are
`FormalSpectrum.exists_sq_eq_algInt`, `FormalSpectrum.not_prime_algInt`,
`FormalSpectrum.not_isUnit_two_algInt`, `FormalSpectrum.finite_setOf_prime_associates_algInt`,
`FormalSpectrum.exists_int_ne_zero_dvd_algInt`,
`FormalSpectrum.dvd_of_intCast_dvd_intCast_algInt` and
`FormalSpectrum.exists_ne_zero_forall_not_dvd_pow_algInt`. It is **not** claimed to be, or not to
be, a `UniqueFactorizationMonoid` — that is a statement in the shape of
`FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower` and it is not made here — nor a
Bézout, Dedekind or principal ideal ring; no factorisation is exhibited, no class group is
computed, no ideal of it is mentioned, and `2` is still the only element of it this file names.
**No valuation, no number field and no prime of that ring appears anywhere**: it has no primes, and
the last two theorems reach `ℤ` instead, where a prime is available. The rational primes they use
are produced by `Nat.exists_infinite_primes` and not chosen.

**The ultrafilter hypothesis is not analysed.** `Ultrafilter.eventually_or` is what makes the
ring a domain and `(φ : Filter ℕ) ≤ Filter.atTop` is what makes the diagonal product work; that the
second is equivalent to `φ` being non-principal is not proved, and no ultrafilter other than
`Filter.hyperfilter ℕ` is exhibited.

**No cardinal arithmetic, no saturation and no transfer principle.** The word *ultrapower* names the
construction and nothing below appeals to any model-theoretic property of it. In particular the
`ℵ₁`-saturation that would give the first half at once is neither used nor stated, and
`FormalSpectrum.not_countable_intUltrapower` is proved from the collapse theorem rather than by
counting anything.

## Implementation notes

`FormalSpectrum.coe_dvd_coe_of_eventually_dvd_intUltrapower` produces its cofactor as the pointwise
integer quotient `fun i => b i / a i`, which is a total function and equal to the wanted cofactor
where the divisibility holds; that is why no choice over the large set is made. `Int.ediv` is used
for nothing else.

**`CommRing ℤ` has to be in scope for `CommRing (Filter.Germ ↑φ ℤ)` to be synthesized**, and a file
importing only `Mathlib/Order/Filter/Germ/Basic.lean` reports *failed to synthesize `CommRing
(l.Germ ℤ)`* while finding `AddCommMonoid` — the missing instance is the one on `ℤ`, and the error
names the germ ring instead. Any project import supplies it, so nothing has to be done about it
here; it is recorded because the error message points at the wrong object.

## Placement

A leaf over `FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, which holds the condition,
its criteria and the identification of the geometric half with it: forward closure **53** project
modules besides itself, reverse closure **0**, counted by walking every `^import FormalSchemes.`
line over the 562 modules under `FormalSchemes/` (a module is not counted in its own closure; the
aggregator at the repository root is outside the walk).

`FormalSchemes.StructureSheafStalkPowerSeriesDedekind` and
`FormalSchemes.StructureSheafStalkPowerSeriesLocal` are **not** imported: their refuting criteria
are the ones this file argues do not apply, and importing them would be four modules for
statements that are only discussed.

**This leaf adds exactly one module to the project's Mathlib closure**,
`Mathlib/Order/Filter/Germ/Basic.lean`: **2649** modules at base and **2650** at head. An absolute
pair here is worth nothing without the walk that produced it, so the walk is written down. It
starts from every `import Mathlib…` line under `FormalSchemes/`, reads the header of each Mathlib
source with its nested block comments stripped, accepts all five import spellings this Mathlib
uses — `import`, `public import`, `meta import`, `public meta import` and `import all` — and
allows a trailing `--` comment after the module name, which 118 of Mathlib's import lines carry.
The two figures are then Lean's own: `Lean.Environment.allImportedModuleNames`, filtered to the
names beginning with Mathlib, gives 2650 for the aggregator at the repository root and 2649 for
the same tree with this file's line deleted. Two nearby conventions do not reproduce that —
accepting only `import` and `public import` gives 2630 and 2631, and rejecting the trailing
comment gives 2615 and 2616 — and under all three the **delta is 1**, which is what this
paragraph is claiming.
`Mathlib/Order/Filter/Ultrafilter/Basic.lean` (for `Filter.hyperfilter` and
`Ultrafilter.eventually_or`) and `Mathlib/Data/Nat/Prime/Infinite.lean` (for
`Nat.exists_infinite_primes`) are already in it and are reached through the import above.
`Mathlib/Order/Filter/FilterProduct.lean`, the ultraproduct file, is **not** imported: it supplies
the field structure of an ultrapower of a field, and neither half below needs it.

**The second witness costs one `import` line and no module at all.**
`Mathlib/RingTheory/Polynomial/RationalRoot.lean` is imported for the one instance
`IsIntegrallyClosed ℤ`, and that import is spent once and consumed twice: both
`FormalSpectrum.not_isUnit_two_algInt` and `FormalSpectrum.dvd_of_intCast_dvd_intCast_algInt` end
in `IsIntegrallyClosed.isIntegral_iff` at `ℤ`, and the second spends no import the first has not
already spent. That module is **already** in this project's Mathlib closure — three other files
reach it, the shortest chain being three steps from `Mathlib/NumberTheory/NumberField/Basic.lean`
through `Mathlib/RingTheory/DedekindDomain/Basic.lean` — so the sentence above stays exact: this
leaf still adds exactly one module to that closure, and the line here adds none.

To **this file's own** closure it adds three, and the two other modules a reader would expect sit
on opposite sides of that difference. `Mathlib/FieldTheory/IsAlgClosed/AlgebraicClosure.lean` was
already reachable from here **before** this line was written: with the two imports above and
nothing else, `AlgebraicClosure` and `integralClosure` both elaborate.
`Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean` was **not** — with those same two
imports `IsIntegrallyClosed` is not an identifier in scope at all. It arrives here *with*
`Mathlib/RingTheory/Polynomial/RationalRoot.lean`, which imports it, and brings
`Mathlib/RingTheory/Localization/NumDen.lean` with it. So neither line needs to be written, but
not for the same reason, and the difference is load-bearing: a successor who reproves **both**
consumers of `IsIntegrallyClosed ℤ` and deletes that import line keeps `AlgebraicClosure` and
loses `IsIntegrallyClosed`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX).
-/

noncomputable section

universe u

open Filter

namespace FormalSpectrum

/-! ### The denominator condition as divisibility in `R` -/

section Domain

variable (R : Type u) [CommRing R] [IsDomain R]

/-- **The denominator condition is a statement about divisibility in `R`**: it holds exactly when
every countable family of nonzero elements of `R` divides powers of a single `m ≠ 0`.

`FormalSpectrum.HasBoundedDenominators` quantifies over families in `Frac R`, and this says that
only the denominators of such a family matter. Forwards, apply the condition to the family of
inverses and clear denominators with `IsFractionRing.injective`; backwards, write each member as
`IsLocalization.mk'` of a numerator over a nonzero denominator and feed the denominators in.

This is the arbitrary-domain companion of
`FormalSpectrum.hasBoundedDenominators_iff_forall_dvd_pow`, whose right-hand side quantifies over
**all** nonzero elements of `R` at once and which needs `[Countable (FractionRing R)]` for exactly
that reason. Here the family is still countable and no countability hypothesis appears; what the
two spellings differ by is the quantifier order, which is the whole subject of
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective`. -/
theorem hasBoundedDenominators_iff_forall_exists_dvd_pow :
    HasBoundedDenominators R ↔
      ∀ d : ℕ → R, (∀ n, d n ≠ 0) → ∃ m : R, m ≠ 0 ∧ ∀ n, ∃ k : ℕ, d n ∣ m ^ k := by
  constructor
  · intro h d hd
    obtain ⟨m, hm, hall⟩ := h fun n => (algebraMap R (FractionRing R) (d n))⁻¹
    refine ⟨m, hm, fun n => ?_⟩
    obtain ⟨k, r, hr⟩ := hall n
    refine ⟨k, r, ?_⟩
    have hdn : algebraMap R (FractionRing R) (d n) ≠ 0 := by simpa using hd n
    have hfrac : algebraMap R (FractionRing R) (m ^ k) =
        algebraMap R (FractionRing R) r * algebraMap R (FractionRing R) (d n) := by
      field_simp at hr
      rw [← hr]
    rw [← map_mul, mul_comm] at hfrac
    exact IsFractionRing.injective R (FractionRing R) hfrac
  · intro h x
    choose ab hab using fun n => IsLocalization.mk'_surjective (nonZeroDivisors R) (x n)
    obtain ⟨m, hm, hall⟩ := h (fun n => ((ab n).2 : R)) fun n => nonZeroDivisors.coe_ne_zero _
    refine ⟨m, hm, fun n => ?_⟩
    obtain ⟨k, c, hc⟩ := hall n
    refine ⟨k, c * (ab n).1, ?_⟩
    have hx : algebraMap R (FractionRing R) ((ab n).2 : R) * x n =
        algebraMap R (FractionRing R) (ab n).1 := by
      rw [← hab n]
      exact IsLocalization.mk'_spec' _ _ _
    have hkey : algebraMap R (FractionRing R) (m ^ k) * x n
        = algebraMap R (FractionRing R) (c * (ab n).1) := by
      rw [hc, map_mul, mul_comm (algebraMap R (FractionRing R) ((ab n).2 : R)), mul_assoc, hx,
        ← map_mul]
    exact hkey.symm

/-- **The same as a sufficient criterion with the exponent fixed at `1`.** A ring in which every
countable family of nonzero elements divides a single element satisfies the denominator condition.

`FormalSpectrum.hasBoundedDenominators_iff_forall_exists_dvd_pow` with `k = 1` supplied. It is
shipped separately because that is the shape a construction produces — a single element divisible by
the whole family — and it keeps the existential over exponents out of the caller. -/
theorem hasBoundedDenominators_of_forall_exists_dvd
    (h : ∀ d : ℕ → R, (∀ n, d n ≠ 0) → ∃ m : R, m ≠ 0 ∧ ∀ n, d n ∣ m) :
    HasBoundedDenominators R :=
  (hasBoundedDenominators_iff_forall_exists_dvd_pow R).mpr fun d hd => by
    obtain ⟨m, hm, hall⟩ := h d hd
    exact ⟨m, hm, fun n => ⟨1, by simpa using hall n⟩⟩

/-- **At a unique factorisation domain the collapse holds with no countability at all.** The
denominator condition produces a single `m ≠ 0` whose powers clear every nonzero element of `R`.

`FormalSpectrum.hasBoundedDenominators_iff_finite_primes` carries `[UniqueFactorizationMonoid R]`
and **no** `[Countable (FractionRing R)]`, so the condition already forces finitely many primes up
to associates there; their product is the `m`
(`FormalSpectrum.exists_forall_dvd_pow_of_finite_primes`).

This is what `FormalSpectrum.hasBoundedDenominators_iff_forall_dvd_pow` says under
`[Countable (FractionRing R)]` at an arbitrary domain, and the two hypotheses are incomparable:
neither unique factorisation nor a countable fraction field implies the other. Read
contrapositively it is the tool of
`FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower` below. -/
theorem exists_forall_dvd_pow_of_hasBoundedDenominators [UniqueFactorizationMonoid R]
    (h : HasBoundedDenominators R) :
    ∃ m : R, m ≠ 0 ∧ ∀ s : R, s ≠ 0 → ∃ k : ℕ, s ∣ m ^ k :=
  exists_forall_dvd_pow_of_finite_primes R ((hasBoundedDenominators_iff_finite_primes R).mp h)

end Domain

/-! ### The ultrapower of `ℤ` -/

/-- **The ultrapower of `ℤ` along an ultrafilter on `ℕ`**: sequences of integers modulo agreement on
a set of the ultrafilter. -/
abbrev IntUltrapower (φ : Ultrafilter ℕ) : Type := Germ (↑φ : Filter ℕ) ℤ

variable (φ : Ultrafilter ℕ)

/-- A sequence has germ `0` exactly when it vanishes on a set of the filter. `Filter.Germ.coe_eq`
against the zero function. -/
theorem coe_eq_zero_iff_intUltrapower (f : ℕ → ℤ) :
    ((f : IntUltrapower φ) = 0) ↔ ∀ᶠ i in (φ : Filter ℕ), f i = 0 := by
  rw [← Germ.coe_zero, Germ.coe_eq]
  rfl

/-- A nowhere-vanishing sequence has nonzero germ. The filter is not `⊥`, so a set of it is
nonempty. -/
theorem coe_ne_zero_intUltrapower {f : ℕ → ℤ} (hf : ∀ i, f i ≠ 0) :
    (f : IntUltrapower φ) ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := ((coe_eq_zero_iff_intUltrapower φ f).mp h).exists
  exact hf i hi

/-- **A nonzero germ is nonzero on a set of the ultrafilter.** This is the first of the three
places where the filter has to be an ultrafilter: `Ultrafilter.eventually_not` turns the *failure*
of eventual vanishing into eventual non-vanishing, which is false at a general filter. -/
theorem eventually_ne_zero_intUltrapower {f : ℕ → ℤ} (hf : (f : IntUltrapower φ) ≠ 0) :
    ∀ᶠ i in (φ : Filter ℕ), f i ≠ 0 :=
  Ultrafilter.eventually_not.mpr fun h => hf ((coe_eq_zero_iff_intUltrapower φ f).mpr h)

/-- **The ultrapower has no zero divisors**, which is the second of the three places the ultrafilter
is used for its own sake: `Ultrafilter.eventually_or` splits *eventually one of the two factors
vanishes* into *one of the two vanishes eventually*. Over a filter that is not an ultrafilter the
germ ring has zero divisors and nothing in this file survives. The third is
`FormalSpectrum.prime_coe_intUltrapower`, which splits the same disjunction for divisibility. -/
instance : NoZeroDivisors (IntUltrapower φ) where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} := by
    induction x, y using Germ.inductionOn₂ with
    | h f g =>
      intro hxy
      rw [← Germ.coe_mul, coe_eq_zero_iff_intUltrapower] at hxy
      have h2 : ∀ᶠ i in (φ : Filter ℕ), f i = 0 ∨ g i = 0 :=
        hxy.mono fun i hi => by simpa using mul_eq_zero.mp hi
      rcases Ultrafilter.eventually_or.mp h2 with h3 | h3
      · exact Or.inl ((coe_eq_zero_iff_intUltrapower φ f).mpr h3)
      · exact Or.inr ((coe_eq_zero_iff_intUltrapower φ g).mpr h3)

instance : IsDomain (IntUltrapower φ) := NoZeroDivisors.to_isDomain _

/-- **Eventual divisibility gives divisibility of germs.** The cofactor is the pointwise integer
quotient, a total function that is the wanted cofactor wherever the hypothesis holds
(`Int.mul_ediv_cancel'`); no choice over the large set is needed and none is made. -/
theorem coe_dvd_coe_of_eventually_dvd_intUltrapower {a b : ℕ → ℤ}
    (h : ∀ᶠ i in (φ : Filter ℕ), a i ∣ b i) : (a : IntUltrapower φ) ∣ (b : IntUltrapower φ) :=
  ⟨((fun i => b i / a i : ℕ → ℤ) : IntUltrapower φ), by
    rw [← Germ.coe_mul, Germ.coe_eq]
    exact h.mono fun i hi => (Int.mul_ediv_cancel' hi).symm⟩

/-- **Divisibility of germs is eventual divisibility**, the converse of
`FormalSpectrum.coe_dvd_coe_of_eventually_dvd_intUltrapower`: a cofactor germ has a representative,
and the defining equation of the product is an eventual pointwise equation.

This is the file's third instance of the same phenomenon —
`FormalSpectrum.coe_eq_zero_iff_intUltrapower` for equality, the `NoZeroDivisors` instance for
products, and now divisibility — and each is one `filter_upwards` or one
`Ultrafilter.eventually_or`. That is why none of this needs Łoś's theorem: the statements being
transferred are all of the shape the ultrafilter settles by itself. -/
theorem eventually_dvd_of_coe_dvd_coe_intUltrapower {a b : ℕ → ℤ}
    (h : (a : IntUltrapower φ) ∣ (b : IntUltrapower φ)) :
    ∀ᶠ i in (φ : Filter ℕ), a i ∣ b i := by
  obtain ⟨c, hc⟩ := h
  induction c using Germ.inductionOn with
  | h g =>
    rw [← Germ.coe_mul, Germ.coe_eq] at hc
    filter_upwards [hc] with i hi
    exact ⟨g i, hi⟩

/-- **Divisibility of germs of sequences is eventual pointwise divisibility**, both directions
together. -/
theorem coe_dvd_coe_iff_eventually_dvd_intUltrapower {a b : ℕ → ℤ} :
    (a : IntUltrapower φ) ∣ (b : IntUltrapower φ) ↔ ∀ᶠ i in (φ : Filter ℕ), a i ∣ b i :=
  ⟨eventually_dvd_of_coe_dvd_coe_intUltrapower φ,
    coe_dvd_coe_of_eventually_dvd_intUltrapower φ⟩

/-! ### The denominator condition holds in the ultrapower -/

/-- **Every countable family of nonzero elements of the ultrapower divides a single element**, with
no power taken.

Representatives `f n` of the `d n` are replaced by `e n i = if f n i = 0 then 1 else f n i`, which
is nowhere zero and has the same germ, since `d n ≠ 0` puts `{i | f n i ≠ 0}` in the ultrafilter.
The witness is the **diagonal product** `m i = ∏ n ∈ Finset.range (i + 1), e n i`: it is nowhere
zero because each factor is, and for `i ≥ n` the factor `e n i` occurs in it, so
`FormalSpectrum.coe_dvd_coe_of_eventually_dvd_intUltrapower` applies over `{i | n ≤ i}`.

**The hypothesis `(φ : Filter ℕ) ≤ Filter.atTop` is exactly what makes `{i | n ≤ i}` large**, and it
is the only property of `φ` used here beyond its being an ultrafilter. That it says `φ` is
non-principal is not proved. -/
theorem exists_forall_dvd_intUltrapower (hφ : (φ : Filter ℕ) ≤ atTop) (d : ℕ → IntUltrapower φ)
    (hd : ∀ n, d n ≠ 0) : ∃ m : IntUltrapower φ, m ≠ 0 ∧ ∀ n, d n ∣ m := by
  classical
  choose f hf using fun n : ℕ =>
    Germ.inductionOn (d n) (p := fun x => ∃ g : ℕ → ℤ, ((g : IntUltrapower φ) = x))
      fun g => ⟨g, rfl⟩
  set e : ℕ → ℕ → ℤ := fun n i => if f n i = 0 then 1 else f n i with he
  have he_ne : ∀ n i, e n i ≠ 0 := by
    intro n i
    simp only [he]
    split
    · exact one_ne_zero
    · assumption
  have he_coe : ∀ n, ((e n : ℕ → ℤ) : IntUltrapower φ) = d n := by
    intro n
    rw [← hf n, Germ.coe_eq]
    have hne := eventually_ne_zero_intUltrapower φ (f := f n) (by rw [hf n]; exact hd n)
    exact hne.mono fun i hi => by simp only [he, if_neg hi]
  refine ⟨((fun i => ∏ n ∈ Finset.range (i + 1), e n i : ℕ → ℤ) : IntUltrapower φ), ?_, ?_⟩
  · exact coe_ne_zero_intUltrapower φ fun i => Finset.prod_ne_zero_iff.mpr fun n _ => he_ne n i
  · intro n
    rw [← he_coe n]
    refine coe_dvd_coe_of_eventually_dvd_intUltrapower φ ?_
    have hmem : {i | n ≤ i} ∈ (φ : Filter ℕ) := hφ (mem_atTop n)
    filter_upwards [hmem] with i hi
    exact Finset.dvd_prod_of_mem (fun k => e k i) (Finset.mem_range.mpr (by omega))

/-- **The ultrapower satisfies the denominator condition.**
`FormalSpectrum.hasBoundedDenominators_of_forall_exists_dvd` at
`FormalSpectrum.exists_forall_dvd_intUltrapower`. -/
theorem hasBoundedDenominators_intUltrapower (hφ : (φ : Filter ℕ) ≤ atTop) :
    HasBoundedDenominators (IntUltrapower φ) :=
  hasBoundedDenominators_of_forall_exists_dvd _ (exists_forall_dvd_intUltrapower φ hφ)

/-! ### No single denominator serves the whole ultrapower -/

/-- **For every `m ≠ 0` there is a nonzero element dividing no power of `m`.**

A prime `p i` larger than `(M i).natAbs` at each index, for `M` a representative of `m`. On the
set where `M i ≠ 0` — which is large because `m ≠ 0` — `p i ∣ M i ^ k` gives `p i ∣ M i` by
primality and then `p i ≤ |M i|`, against the choice of `p i`. The ultrafilter enters only through
`FormalSpectrum.eventually_ne_zero_intUltrapower`, and no hypothesis on `φ` beyond that is
used. -/
theorem exists_forall_not_dvd_pow_intUltrapower (m : IntUltrapower φ) (hm : m ≠ 0) :
    ∃ s : IntUltrapower φ, s ≠ 0 ∧ ∀ k : ℕ, ¬ s ∣ m ^ k := by
  classical
  induction m using Germ.inductionOn with
  | h M =>
    choose p hple hp using fun i : ℕ => Nat.exists_infinite_primes ((M i).natAbs + 1)
    refine ⟨((fun i => (p i : ℤ)) : IntUltrapower φ), coe_ne_zero_intUltrapower φ ?_, ?_⟩
    · intro i
      exact_mod_cast (hp i).ne_zero
    · rintro k ⟨c, hc⟩
      induction c using Germ.inductionOn with
      | h C =>
        rw [← Germ.coe_pow, ← Germ.coe_mul, Germ.coe_eq] at hc
        have hne := eventually_ne_zero_intUltrapower φ (f := M) hm
        obtain ⟨i, hci, hMi⟩ := (hc.and hne).exists
        have hdvd : ((p i : ℤ)) ∣ M i ^ k := ⟨C i, by simpa using hci⟩
        have hpi : Prime ((p i : ℤ)) := Nat.prime_iff_prime_int.mp (hp i)
        have hdvd' : ((p i : ℤ)) ∣ M i := hpi.dvd_of_dvd_pow hdvd
        have hle : ((p i : ℤ)) ≤ |M i| :=
          Int.le_of_dvd (abs_pos.mpr hMi) ((dvd_abs _ _).mpr hdvd')
        rw [Int.abs_eq_natAbs] at hle
        have := hple i
        omega

/-- **No localization of the ultrapower at a single element is its fraction field.**

`FormalSpectrum.surjective_awayToFractionRing_iff_forall_dvd_pow` — which holds at an arbitrary
domain and carries no countability hypothesis — against
`FormalSpectrum.exists_forall_not_dvd_pow_intUltrapower`. -/
theorem not_exists_surjective_awayToFractionRing_intUltrapower :
    ¬ ∃ (m : IntUltrapower φ) (hm : m ≠ 0),
        Function.Surjective (awayToFractionRing (IntUltrapower φ) m hm) := by
  rintro ⟨m, hm, hs⟩
  obtain ⟨s, hs0, hsm⟩ := exists_forall_not_dvd_pow_intUltrapower φ m hm
  obtain ⟨k, hk⟩ :=
    (surjective_awayToFractionRing_iff_forall_dvd_pow (IntUltrapower φ) hm).mp hs s hs0
  exact hsm k hk

/-- **No single `m` clears every element of the fraction field**, which is the same statement with
the localization removed.

`FormalSpectrum.mem_range_awayToFractionRing_iff` at each element — a per-`m` bridge stated at an
arbitrary domain with no countability — against
`FormalSpectrum.not_exists_surjective_awayToFractionRing_intUltrapower`. The right-hand side here
is, character for character, the one
`FormalSpectrum.hasBoundedDenominators_iff_exists_denominator` puts on the other side of its `↔`
under `[Countable (FractionRing R)]`. -/
theorem not_exists_denominator_intUltrapower :
    ¬ ∃ m : IntUltrapower φ, m ≠ 0 ∧ ∀ y : FractionRing (IntUltrapower φ), ∃ k : ℕ,
        algebraMap (IntUltrapower φ) (FractionRing (IntUltrapower φ)) (m ^ k) * y ∈
          Set.range (algebraMap (IntUltrapower φ) (FractionRing (IntUltrapower φ))) := by
  rintro ⟨m, hm, h⟩
  exact not_exists_surjective_awayToFractionRing_intUltrapower φ
    ⟨m, hm, fun y => (mem_range_awayToFractionRing_iff (IntUltrapower φ) m hm y).mpr (h y)⟩

/-- **No single `m` has every nonzero element dividing a power of it**: the same statement again
with no fraction field and no localization left in it, which is
`FormalSpectrum.hasBoundedDenominators_iff_forall_dvd_pow`'s right-hand side.

Immediate from `FormalSpectrum.exists_forall_not_dvd_pow_intUltrapower`, which is exactly the
negation of the inner quantifier at each `m`. Beside
`FormalSpectrum.exists_forall_dvd_intUltrapower` it is the whole content of this file in two
lines: **every countable family of nonzero elements divides one element, and the family of all of
them does not.** -/
theorem not_exists_forall_dvd_pow_intUltrapower :
    ¬ ∃ m : IntUltrapower φ, m ≠ 0 ∧ ∀ s : IntUltrapower φ, s ≠ 0 → ∃ k : ℕ, s ∣ m ^ k := by
  rintro ⟨m, hm, h⟩
  obtain ⟨s, hs0, hsm⟩ := exists_forall_not_dvd_pow_intUltrapower φ m hm
  obtain ⟨k, hk⟩ := h s hs0
  exact hsm k hk

/-- **No localization of the ultrapower at a single element is a field.**

`FormalSpectrum.surjective_awayToFractionRing_iff_isField`, the per-`m` bridge that holds at an
arbitrary domain, against
`FormalSpectrum.not_exists_surjective_awayToFractionRing_intUltrapower`. This is the right-hand
side of `FormalSpectrum.hasBoundedDenominators_iff_exists_isField`. -/
theorem not_exists_isField_away_intUltrapower :
    ¬ ∃ m : IntUltrapower φ, m ≠ 0 ∧ IsField (Localization.Away m) := by
  rintro ⟨m, hm, hf⟩
  exact not_exists_surjective_awayToFractionRing_intUltrapower φ
    ⟨m, hm, (surjective_awayToFractionRing_iff_isField (IntUltrapower φ) hm).mpr hf⟩

/-! ### The countability hypothesis of the collapse is needed -/

/-- **The denominator condition does not imply that some `R[1/m]` is already `Frac R`.** Both halves
hold in one ring, which is what
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` asserts cannot happen over a
**countable** fraction field.

So the hypothesis `[Countable (FractionRing R)]` of that equivalence, and of
`FormalSpectrum.hasBoundedDenominators_iff_exists_denominator`,
`FormalSpectrum.hasBoundedDenominators_iff_forall_dvd_pow` and
`FormalSpectrum.hasBoundedDenominators_iff_exists_isField` with it, **is needed and cannot be
dropped**. The converse direction, `FormalSpectrum.hasBoundedDenominators_of_surjective`, holds at
every domain and is untouched by this. -/
theorem hasBoundedDenominators_and_not_exists_surjective_intUltrapower
    (hφ : (φ : Filter ℕ) ≤ atTop) :
    HasBoundedDenominators (IntUltrapower φ) ∧
      ¬ ∃ (m : IntUltrapower φ) (hm : m ≠ 0),
          Function.Surjective (awayToFractionRing (IntUltrapower φ) m hm) :=
  ⟨hasBoundedDenominators_intUltrapower φ hφ,
    not_exists_surjective_awayToFractionRing_intUltrapower φ⟩

/-- **The countability hypothesis is needed in every spelling of the collapse.** One ring satisfies
the denominator condition and falsifies all four right-hand sides at once.

The four are `FormalSpectrum.hasBoundedDenominators_iff_exists_surjective`,
`FormalSpectrum.hasBoundedDenominators_iff_exists_denominator`,
`FormalSpectrum.hasBoundedDenominators_iff_forall_dvd_pow` and
`FormalSpectrum.hasBoundedDenominators_iff_exists_isField`, and each conjunct below is that
theorem's own right-hand side negated, not a paraphrase of it.

`FormalSpectrum.hasBoundedDenominators_iff_finite_primes` is **not** on the list: it assumes
`[UniqueFactorizationMonoid R]` rather than `[Countable (FractionRing R)]`, and its right-hand side
is none of the four. The ultrapower does have something to say about it, but a different thing and
about a different instance — that its `[UniqueFactorizationMonoid R]` cannot be dropped either,
which is `FormalSpectrum.not_forall_hasBoundedDenominators_iff_finite_primes` below and no part of
the conjunction here. -/
theorem hasBoundedDenominators_and_no_collapse_intUltrapower (hφ : (φ : Filter ℕ) ≤ atTop) :
    HasBoundedDenominators (IntUltrapower φ) ∧
      (¬ ∃ (m : IntUltrapower φ) (hm : m ≠ 0),
          Function.Surjective (awayToFractionRing (IntUltrapower φ) m hm)) ∧
      (¬ ∃ m : IntUltrapower φ, m ≠ 0 ∧ ∀ y : FractionRing (IntUltrapower φ), ∃ k : ℕ,
          algebraMap (IntUltrapower φ) (FractionRing (IntUltrapower φ)) (m ^ k) * y ∈
            Set.range (algebraMap (IntUltrapower φ) (FractionRing (IntUltrapower φ)))) ∧
      (¬ ∃ m : IntUltrapower φ, m ≠ 0 ∧ ∀ s : IntUltrapower φ, s ≠ 0 → ∃ k : ℕ, s ∣ m ^ k) ∧
      (¬ ∃ m : IntUltrapower φ, m ≠ 0 ∧ IsField (Localization.Away m)) :=
  ⟨hasBoundedDenominators_intUltrapower φ hφ,
    not_exists_surjective_awayToFractionRing_intUltrapower φ,
    not_exists_denominator_intUltrapower φ,
    not_exists_forall_dvd_pow_intUltrapower φ,
    not_exists_isField_away_intUltrapower φ⟩

/-- **The quantified form: the implication is false at an arbitrary domain.**

`FormalSpectrum.hasBoundedDenominators_and_not_exists_surjective_intUltrapower` at
`Filter.hyperfilter ℕ`, whose `Nat.hyperfilter_le_atTop` supplies the hypothesis. This is the
sentence the counterexample file's *"not known to be removable and is not known to be needed"* was
about, with the second half of it now answered. -/
theorem not_forall_hasBoundedDenominators_imp_exists_surjective :
    ¬ ∀ (R : Type) [CommRing R] [IsDomain R], HasBoundedDenominators R →
        ∃ (m : R) (hm : m ≠ 0), Function.Surjective (awayToFractionRing R m hm) := by
  intro h
  obtain ⟨hbd, hns⟩ :=
    hasBoundedDenominators_and_not_exists_surjective_intUltrapower (hyperfilter ℕ)
      Nat.hyperfilter_le_atTop
  exact hns (h (IntUltrapower (hyperfilter ℕ)) hbd)

/-! ### The unique-factorisation hypothesis of the collapse is needed

`FormalSpectrum.exists_forall_dvd_pow_of_hasBoundedDenominators` is the *other* passage from the
denominator condition to a single clearing `m`: not through a countable fraction field but through
unique factorisation. Its instance cannot be deleted either, and the witness is the ring already
above — no prime family, no `Associates` and nothing from the section that follows.

**The refutation is `FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower`'s own proof read
the other way round.** That proof discharges `[UniqueFactorizationMonoid R]` against the **ring**
and concludes that the ring is not a unique factorisation domain; discharge the same instance
against the **quantified statement** and the same three facts —
`FormalSpectrum.hasBoundedDenominators_intUltrapower`,
`FormalSpectrum.not_exists_forall_dvd_pow_intUltrapower` and the theorem itself — conclude that the
instance cannot be dropped from it. One ring, one pair of facts, two readings, and *the instance is
unavailable here* is the weaker of them.

**Only the forward passage is reached, and only by this ring.**
`FormalSpectrum.exists_forall_dvd_pow_of_hasBoundedDenominators` factors through
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes` and
`FormalSpectrum.exists_forall_dvd_pow_of_finite_primes`, and the ultrapower bears on neither of the
last two as it bears on the first: refuting the second would need a domain with **finitely** many
prime associate classes and no clearing `m`, and this ring has infinitely many
(`FormalSpectrum.infinite_setOf_prime_associates_intUltrapower`), and the third quantifies over a
`Finset` meeting every prime class, which for the same reason has no instance here. Both are
reached at a **different** ring — the section *A second witness: the ring of all algebraic
integers* at the end of this file, where the instance of each of the last two is shown **needed**.
-/

/-- **The ultrapower satisfies the denominator condition and has no single clearing `m`.**

The two sides of the implication
`FormalSpectrum.exists_forall_dvd_pow_of_hasBoundedDenominators` at one ring, the hypothesis true
and the conclusion false. The second conjunct is that theorem's own conclusion negated and nothing
else; it is already named, `FormalSpectrum.not_exists_forall_dvd_pow_intUltrapower`, and carries no
`hφ`, so no projection out of
`FormalSpectrum.hasBoundedDenominators_and_no_collapse_intUltrapower` is needed to reach it.

The pairing is what carries no content and is stated anyway, because
`FormalSpectrum.hasBoundedDenominators_and_exists_primes_not_associated_intUltrapower` and
`FormalSpectrum.hasBoundedDenominators_and_infinite_primes_intUltrapower` are the same shape for
the two *needed* results below, and a reader meeting the third should meet it in the shape of the
first two. -/
theorem hasBoundedDenominators_and_not_exists_forall_dvd_pow_intUltrapower
    (hφ : (φ : Filter ℕ) ≤ atTop) :
    HasBoundedDenominators (IntUltrapower φ) ∧
      ¬ ∃ m : IntUltrapower φ, m ≠ 0 ∧ ∀ s : IntUltrapower φ, s ≠ 0 → ∃ k : ℕ, s ∣ m ^ k :=
  ⟨hasBoundedDenominators_intUltrapower φ hφ, not_exists_forall_dvd_pow_intUltrapower φ⟩

/-- **The quantified form: the collapse at a unique factorisation domain is false without that
instance.**

The statement is `FormalSpectrum.exists_forall_dvd_pow_of_hasBoundedDenominators`'s own, with
`[UniqueFactorizationMonoid R]` deleted and nothing else changed — the universe restricted to
`Type` as in `FormalSpectrum.not_forall_hasBoundedDenominators_imp_exists_surjective`, the
neighbouring statement of the same shape, which `IntUltrapower φ` meets.

**There is no `↔` companion**, unlike the pair
`FormalSpectrum.not_forall_hasBoundedDenominators_imp_finite_primes` /
`FormalSpectrum.not_forall_hasBoundedDenominators_iff_finite_primes` below: the theorem refuted
here is an implication and not a classification, so this `→` form already is its negation. -/
theorem not_forall_hasBoundedDenominators_imp_exists_forall_dvd_pow :
    ¬ ∀ (R : Type) [CommRing R] [IsDomain R],
        HasBoundedDenominators R → ∃ m : R, m ≠ 0 ∧ ∀ s : R, s ≠ 0 → ∃ k : ℕ, s ∣ m ^ k := by
  intro h
  obtain ⟨hbd, hno⟩ :=
    hasBoundedDenominators_and_not_exists_forall_dvd_pow_intUltrapower (hyperfilter ℕ)
      Nat.hyperfilter_le_atTop
  exact hno (h (IntUltrapower (hyperfilter ℕ)) hbd)

/-! ### The primes of the ultrapower

The one *positive* arithmetic fact this file proves, and it is here rather than under *What the
ring is not* for that reason. It is not decoration, and it is not read once: the same family
measures `[UniqueFactorizationMonoid R]` on **two** theorems. Read against
`FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated` it says that criterion's
instance is **needed** and not merely unavailable. Read at `Associates`, where the
pairwise-non-associatedness becomes injectivity, it says the same of the classification
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`, whose **forward** direction it refutes
with that instance deleted. The two readings are one fact in two spellings, and the second is the
inverse of the translation that classification's own proof performs.

Nothing below exhibits a factorisation of any element, claims that these are all the primes, or
claims that they generate anything, and nothing below bears on the classification's **backward**
direction, which needs unique factorisation for a reason no witness here touches. -/

/-- **A pointwise non-unit is a non-unit.** An inverse germ has a representative, and the defining
equation holds at some index because a set of the filter is nonempty.

The general form of `FormalSpectrum.not_isUnit_coe_two_intUltrapower`, which is now one line of
it. -/
theorem not_isUnit_coe_intUltrapower {f : ℕ → ℤ} (hf : ∀ i, ¬ IsUnit (f i)) :
    ¬ IsUnit ((f : IntUltrapower φ)) := by
  rw [isUnit_iff_exists_inv]
  rintro ⟨v, hv⟩
  induction v using Germ.inductionOn with
  | h g =>
    rw [← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq] at hv
    obtain ⟨i, hi⟩ := hv.exists
    exact hf i (isUnit_iff_exists_inv.mpr ⟨g i, hi⟩)

/-- **A pointwise prime is prime**, and the ultrafilter is what does the work: `p ∣ ab` is eventual
by `FormalSpectrum.eventually_dvd_of_coe_dvd_coe_intUltrapower`, `Prime (f i)` splits it at each
index, and `Ultrafilter.eventually_or` chooses the side globally.

Together with the `NoZeroDivisors` instance this is the second and last place in the file where a
*disjunction* has to be resolved on a large set, and it is the same move; counting
`FormalSpectrum.eventually_ne_zero_intUltrapower` it is the third and last place where the filter
has to be an ultrafilter. -/
theorem prime_coe_intUltrapower {f : ℕ → ℤ} (hf : ∀ i, Prime (f i)) :
    Prime ((f : IntUltrapower φ)) := by
  refine ⟨coe_ne_zero_intUltrapower φ fun i => (hf i).ne_zero,
    not_isUnit_coe_intUltrapower φ fun i => (hf i).not_unit, ?_⟩
  intro x y hxy
  induction x, y using Germ.inductionOn₂ with
  | h a b =>
    rw [← Germ.coe_mul] at hxy
    have h := eventually_dvd_of_coe_dvd_coe_intUltrapower φ hxy
    have h' : ∀ᶠ i in (φ : Filter ℕ), f i ∣ a i ∨ f i ∣ b i := by
      filter_upwards [h] with i hi using (hf i).dvd_or_dvd hi
    rcases Ultrafilter.eventually_or.mp h' with h1 | h1
    · exact Or.inl (coe_dvd_coe_of_eventually_dvd_intUltrapower φ h1)
    · exact Or.inr (coe_dvd_coe_of_eventually_dvd_intUltrapower φ h1)

/-- **The germ of a constant rational prime is prime.** -/
theorem prime_coe_const_intUltrapower {p : ℤ} (hp : Prime p) :
    Prime (((fun _ => p) : ℕ → ℤ) : IntUltrapower φ) :=
  prime_coe_intUltrapower φ fun _ => hp

/-- **Associated constant germs come from associated integers.** Both divisibilities are eventual,
and a set of an ultrafilter is nonempty, so one index settles it. -/
theorem associated_of_associated_coe_const_intUltrapower {p q : ℤ}
    (h : Associated (((fun _ => p) : ℕ → ℤ) : IntUltrapower φ)
      (((fun _ => q) : ℕ → ℤ) : IntUltrapower φ)) : Associated p q := by
  obtain ⟨_, h1⟩ := (eventually_dvd_of_coe_dvd_coe_intUltrapower φ h.dvd).exists
  obtain ⟨_, h2⟩ := (eventually_dvd_of_coe_dvd_coe_intUltrapower φ h.symm.dvd).exists
  exact associated_of_dvd_dvd h1 h2

/-- **The ultrapower has infinitely many primes, pairwise non-associated**: the germs of the
constant sequences at a strictly increasing sequence of rational primes.

The enumeration is built by recursion from `Nat.exists_infinite_primes`, which this file already
uses in `FormalSpectrum.exists_forall_not_dvd_pow_intUltrapower`, rather than from Mathlib's
nth-prime function: `Mathlib/Data/Nat/Nth.lean` is **not** in this project's Mathlib closure, its
enumerator does not elaborate from this file, and importing it would be the whole cost of this
section. -/
theorem exists_prime_family_not_associated_intUltrapower :
    ∃ p : ℕ → IntUltrapower φ, (∀ n, Prime (p n)) ∧
      ∀ i j : ℕ, Associated (p i) (p j) → i = j := by
  choose f hle hfp using fun n : ℕ => Nat.exists_infinite_primes (n + 1)
  set q : ℕ → ℕ := fun n => Nat.rec (f 0) (fun _ ih => f ih) n with hq
  have hqp : ∀ n, (q n).Prime := by
    intro n
    cases n with
    | zero => exact hfp 0
    | succ k => exact hfp _
  have hmono : StrictMono q := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    have : q n + 1 ≤ f (q n) := hle (q n)
    simpa [hq] using this
  refine ⟨fun n => (((fun _ => ((q n : ℤ))) : ℕ → ℤ) : IntUltrapower φ),
    fun n => prime_coe_const_intUltrapower φ (Nat.prime_iff_prime_int.mp (hqp n)), ?_⟩
  intro i j hij
  have hass := associated_of_associated_coe_const_intUltrapower φ hij
  rw [Int.associated_iff] at hass
  have hqi : 0 < q i := (hqp i).pos
  have hqj : 0 < q j := (hqp j).pos
  rcases hass with h | h
  · exact hmono.injective (by exact_mod_cast h)
  · omega

/-- **The ultrapower satisfies the denominator condition *and* has infinitely many pairwise
non-associated primes.**

Read against `FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated`, which concludes
`¬ HasBoundedDenominators R` from exactly the second half of this conjunction *plus*
`[UniqueFactorizationMonoid R]`, this says that hypothesis is **needed** and not merely
unavailable here. `FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower` says only that the
criterion does not apply; this says it would be false without the hypothesis. -/
theorem hasBoundedDenominators_and_exists_primes_not_associated_intUltrapower
    (hφ : (φ : Filter ℕ) ≤ atTop) :
    HasBoundedDenominators (IntUltrapower φ) ∧
      ∃ p : ℕ → IntUltrapower φ, (∀ n, Prime (p n)) ∧
        ∀ i j : ℕ, Associated (p i) (p j) → i = j :=
  ⟨hasBoundedDenominators_intUltrapower φ hφ,
    exists_prime_family_not_associated_intUltrapower φ⟩

/-- **The quantified form: the criterion is false without unique factorisation.**

The statement is `FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated`'s own, with
`[UniqueFactorizationMonoid R]` deleted and nothing else changed — the universe restricted to
`Type` as in `FormalSpectrum.not_forall_hasBoundedDenominators_imp_exists_surjective`, the
neighbouring statement of the same shape, which `IntUltrapower φ` meets. -/
theorem not_forall_primes_not_associated_imp_not_hasBoundedDenominators :
    ¬ ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ → R), (∀ n, Prime (p n)) →
        (∀ i j, Associated (p i) (p j) → i = j) → ¬ HasBoundedDenominators R := by
  intro h
  obtain ⟨hbd, p, hp, hpa⟩ :=
    hasBoundedDenominators_and_exists_primes_not_associated_intUltrapower (hyperfilter ℕ)
      Nat.hyperfilter_le_atTop
  exact h (IntUltrapower (hyperfilter ℕ)) p hp hpa hbd

/-- **The prime associate classes of the ultrapower are infinite.**

`FormalSpectrum.exists_prime_family_not_associated_intUltrapower` read at `Associates`:
`Associates.mk_eq_mk_iff_associated` is exactly the pairwise-non-associated hypothesis read as
injectivity of `n ↦ Associates.mk (p n)`, and `Associates.prime_mk` is primality read at the class.
`Set.infinite_of_injective_forall_mem` then makes the set infinite, `ℕ` supplying the `Infinite`
instance on the source.

This is the **inverse** of the translation the forward direction of
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes` performs, which turns an infinite set of
classes into a family through `Set.Infinite.natEmbedding` and `Associates.mk_surjective`; a reader
who has seen both has seen one fact in two spellings and not two facts. -/
theorem infinite_setOf_prime_associates_intUltrapower :
    {a : Associates (IntUltrapower φ) | Prime a}.Infinite := by
  obtain ⟨p, hp, hne⟩ := exists_prime_family_not_associated_intUltrapower φ
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => Associates.mk (p n)) ?_ ?_
  · intro i j hij
    exact hne i j (Associates.mk_eq_mk_iff_associated.mp hij)
  · intro n
    exact Associates.prime_mk.mpr (hp n)

/-- **The ultrapower satisfies the denominator condition *and* has infinitely many prime associate
classes.**

The two sides of `FormalSpectrum.hasBoundedDenominators_iff_finite_primes` at one ring, the left
one true and the right one false. Read against that classification this says its
`[UniqueFactorizationMonoid R]` is **needed** and not merely unavailable here — the same reading
`FormalSpectrum.hasBoundedDenominators_and_exists_primes_not_associated_intUltrapower` gives of the
refuting criterion, from the same family. -/
theorem hasBoundedDenominators_and_infinite_primes_intUltrapower
    (hφ : (φ : Filter ℕ) ≤ atTop) :
    HasBoundedDenominators (IntUltrapower φ) ∧
      {a : Associates (IntUltrapower φ) | Prime a}.Infinite :=
  ⟨hasBoundedDenominators_intUltrapower φ hφ, infinite_setOf_prime_associates_intUltrapower φ⟩

/-- **The quantified form: the classification's forward direction is false without unique
factorisation.**

The statement is the forward direction of
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`, with `[UniqueFactorizationMonoid R]`
deleted and nothing else changed — the universe restricted to `Type` as in
`FormalSpectrum.not_forall_primes_not_associated_imp_not_hasBoundedDenominators`, the neighbouring
statement of the same shape, which `IntUltrapower φ` meets.

**The backward direction is untouched.** Nothing here says that finitely many prime classes force
the denominator condition without unique factorisation;
`FormalSpectrum.exists_forall_dvd_pow_of_finite_primes` uses that instance for more than
bookkeeping, and whether it can be dropped there is not decided anywhere on this tree. -/
theorem not_forall_hasBoundedDenominators_imp_finite_primes :
    ¬ ∀ (R : Type) [CommRing R] [IsDomain R],
        HasBoundedDenominators R → {a : Associates R | Prime a}.Finite := by
  intro h
  obtain ⟨hbd, hinf⟩ :=
    hasBoundedDenominators_and_infinite_primes_intUltrapower (hyperfilter ℕ)
      Nat.hyperfilter_le_atTop
  exact hinf (h (IntUltrapower (hyperfilter ℕ)) hbd)

/-- **The classification itself is false without unique factorisation**, which is the literal
negation of `FormalSpectrum.hasBoundedDenominators_iff_finite_primes` with its instance deleted.

One line from
`FormalSpectrum.not_forall_hasBoundedDenominators_imp_finite_primes`, which is the sharper of the
two because it names the direction that fails; this one is the shape that matches the theorem on
the tree. They are stated together and derived from one another so that they cannot drift apart. -/
theorem not_forall_hasBoundedDenominators_iff_finite_primes :
    ¬ ∀ (R : Type) [CommRing R] [IsDomain R],
        HasBoundedDenominators R ↔ {a : Associates R | Prime a}.Finite :=
  fun h => not_forall_hasBoundedDenominators_imp_finite_primes fun R _ _ => (h R).mp

/-! ### What the ring is not

Three properties the ultrapower does not have, each read off the two halves above and none of them
needing any factorisation theory, cardinal arithmetic or model theory. They are here because the
first version of this file asserted all three in prose as true-but-unproved, and an assertion no
declaration states is the thing this tree tries hardest not to leave lying about. -/

/-- **The fraction field of the ultrapower is uncountable.**

The collapse used as a tool rather than as a target: if `Frac R` were countable then
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` would *apply*, and it would produce
from `FormalSpectrum.hasBoundedDenominators_intUltrapower` the single `m` that
`FormalSpectrum.exists_forall_not_dvd_pow_intUltrapower` refutes.

Nothing here computes a cardinal. What is proved is a negation of `Countable`, and no lower bound
on the size of the ring is available from it. -/
theorem not_countable_fractionRing_intUltrapower (hφ : (φ : Filter ℕ) ≤ atTop) :
    ¬ Countable (FractionRing (IntUltrapower φ)) := by
  intro _hc
  exact not_exists_surjective_awayToFractionRing_intUltrapower φ
    ((hasBoundedDenominators_iff_exists_surjective (IntUltrapower φ)).mp
      (hasBoundedDenominators_intUltrapower φ hφ))

/-- **The ultrapower itself is uncountable.**

`Localization.countable_of_countable` in `FormalSchemes.CountableLocalization` is an `instance`, and
`FractionRing` is an `abbrev` for `Localization (nonZeroDivisors R)`, so a countable ring would have
a countable fraction field by instance search alone — which is why `inferInstance` is the whole
step down from
`FormalSpectrum.not_countable_fractionRing_intUltrapower`. -/
theorem not_countable_intUltrapower (hφ : (φ : Filter ℕ) ≤ atTop) :
    ¬ Countable (IntUltrapower φ) := fun _hc =>
  not_countable_fractionRing_intUltrapower φ hφ inferInstance

/-- **The ultrapower is not a unique factorisation domain.**

`FormalSpectrum.exists_forall_dvd_pow_of_hasBoundedDenominators` says that at a unique
factorisation domain the denominator condition produces a single `m` whose powers clear everything;
`FormalSpectrum.not_exists_forall_dvd_pow_intUltrapower` says there is no such `m` here, and
`FormalSpectrum.hasBoundedDenominators_intUltrapower` says the condition holds.

**This is a proof by contradiction from a classification and not a piece of factorisation theory.**
It exhibits no irreducible-but-not-prime element, counts no primes, and does not show the ring has
a prime element at all. What it does settle is that
`FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated`,
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes` and the
`FormalSpectrum.exists_forall_dvd_pow_of_hasBoundedDenominators` the line below invokes are
inapplicable here as a **theorem** rather than as an observation about an instance that happens not
to be available. That is the weakest thing this ring says about the three of them. The stronger
thing, said of each, is that the instance is **needed** — by
`FormalSpectrum.not_forall_primes_not_associated_imp_not_hasBoundedDenominators`, by
`FormalSpectrum.not_forall_hasBoundedDenominators_imp_finite_primes` and by
`FormalSpectrum.not_forall_hasBoundedDenominators_imp_exists_forall_dvd_pow`, each of which refutes
its statement with `[UniqueFactorizationMonoid R]` deleted. *Inapplicable here* is what this
theorem says; *needed there* is what those three say, and a hypothesis unavailable at one ring is
never on its own a reason that it cannot be dropped.

**The third of the three is this proof read the other way round**, and that is why it is the one
worth pausing on. The line below discharges `[UniqueFactorizationMonoid (IntUltrapower φ)]` against
the **ring** and combines three facts — the theorem,
`FormalSpectrum.hasBoundedDenominators_intUltrapower` and
`FormalSpectrum.not_exists_forall_dvd_pow_intUltrapower` — to conclude that the ring is not a
unique factorisation domain. Discharge the same instance against the **quantified statement**
instead, and the same three facts conclude that it cannot be deleted from the theorem. One ring,
one pair of facts, two readings; the section *The unique-factorisation hypothesis of the collapse
is needed* above is the second of them, and this theorem is the first. -/
theorem not_uniqueFactorizationMonoid_intUltrapower (hφ : (φ : Filter ℕ) ≤ atTop) :
    ¬ UniqueFactorizationMonoid (IntUltrapower φ) := fun _ =>
  not_exists_forall_dvd_pow_intUltrapower φ
    (exists_forall_dvd_pow_of_hasBoundedDenominators (IntUltrapower φ)
      (hasBoundedDenominators_intUltrapower φ hφ))

/-- The germ of the constant sequence `2` is not a unit: an inverse would have `2 * g i = 1` in `ℤ`
at some index, since a set of the filter is nonempty.

Nothing about `2` matters beyond its being a nonzero non-unit of `ℤ`, and it is written as a
coercion rather than given a name because a `def` would need its equation lemma supplied before
the rewrites below fire. The statement is unchanged; the argument it used to run inline is now
`FormalSpectrum.not_isUnit_coe_intUltrapower`, which the primes section needs at an arbitrary
pointwise non-unit, and `Int.isUnit_iff` reduces the pointwise obligation to `omega`. -/
theorem not_isUnit_coe_two_intUltrapower :
    ¬ IsUnit ((((fun _ => (2 : ℤ)) : ℕ → ℤ) : IntUltrapower φ)) :=
  not_isUnit_coe_intUltrapower φ fun _ => by rw [Int.isUnit_iff]; omega

/-- **The ultrapower is not Noetherian**, by Krull intersection against the diagonal product.

Let `c` be the germ of the constant `2`, a nonzero non-unit. The countable family `c, c², c³, …` is
cleared by a single `m ≠ 0` (`FormalSpectrum.exists_forall_dvd_intUltrapower`), and such an `m` lies
in `⋂ᵢ (c)ⁱ`, which `Ideal.iInf_pow_eq_bot_of_isDomain` forces to be `⊥` in a Noetherian domain at
a proper ideal.

**The `i = 0` case is not decoration**: `(c)⁰` is `⊤` and the family is indexed so that the
hypothesis supplies `c ^ (j + 1) ∣ m`, which is the successor case exactly. The statement needs no
import that this file did not already have. -/
theorem not_isNoetherianRing_intUltrapower (hφ : (φ : Filter ℕ) ≤ atTop) :
    ¬ IsNoetherianRing (IntUltrapower φ) := by
  intro hN
  set c : IntUltrapower φ := (((fun _ => (2 : ℤ)) : ℕ → ℤ) : IntUltrapower φ) with hcdef
  have hc0 : c ≠ 0 := coe_ne_zero_intUltrapower φ (by norm_num)
  obtain ⟨m, hm, hall⟩ :=
    exists_forall_dvd_intUltrapower φ hφ (fun n => c ^ (n + 1)) fun n => pow_ne_zero _ hc0
  have hne : Ideal.span ({c} : Set (IntUltrapower φ)) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact not_isUnit_coe_two_intUltrapower φ
  have hmem : m ∈ ⨅ i : ℕ, (Ideal.span ({c} : Set (IntUltrapower φ))) ^ i := by
    refine Ideal.mem_iInf.mpr fun i => ?_
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    cases i with
    | zero => simp
    | succ j => exact hall j
  rw [Ideal.iInf_pow_eq_bot_of_isDomain _ hne, Ideal.mem_bot] at hmem
  exact hm hmem

/-! ### The value of the predicate at the ultrapower -/

/-- **`FormalSpectrum.IsStalkLimit` holds at `(X) ⊆ R⟦X⟧` at the generic point, for `R` an
ultrapower of `ℤ`.**

`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`, which needs only
`[IsDomain R]`, at `FormalSpectrum.hasBoundedDenominators_intUltrapower`. -/
theorem isStalkLimit_powerSeriesXGenericPoint_intUltrapower (hφ : (φ : Filter ℕ) ≤ atTop) :
    IsStalkLimit (powerSeriesXIdeal (IntUltrapower φ))
      (powerSeriesXGenericPoint (IntUltrapower φ)) :=
  (isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators (IntUltrapower φ)).mpr
    (hasBoundedDenominators_intUltrapower φ hφ)

/-- **A positive value of the predicate that no single localization explains.**

At a field, at a discrete valuation ring and at the closed point of a local ring the predicate holds
because one `R[1/m]` already does all of the work. Here it holds and no `R[1/m]` is the fraction
field, so the mechanism behind the earlier values is not the mechanism behind this one.

This is a statement about one point of one formal spectrum and about nothing else; in particular it
is not a statement about `FormalSpectrum.IsStalkLimit` at any other point of the same space, where
nothing below applies. -/
theorem isStalkLimit_and_not_exists_surjective_intUltrapower (hφ : (φ : Filter ℕ) ≤ atTop) :
    IsStalkLimit (powerSeriesXIdeal (IntUltrapower φ))
        (powerSeriesXGenericPoint (IntUltrapower φ)) ∧
      ¬ ∃ (m : IntUltrapower φ) (hm : m ≠ 0),
          Function.Surjective (awayToFractionRing (IntUltrapower φ) m hm) :=
  ⟨isStalkLimit_powerSeriesXGenericPoint_intUltrapower φ hφ,
    not_exists_surjective_awayToFractionRing_intUltrapower φ⟩

/-! ### A second witness: the ring of all algebraic integers

`FormalSpectrum.forall_dvd_pow_prod` — the step inside
`FormalSpectrum.exists_forall_dvd_pow_of_finite_primes` that turns a finite set of primes covering
every associate class into a denominator for the whole ring — carries
`[UniqueFactorizationMonoid R]` too, and **the ultrapower cannot measure it**. Its hypothesis asks
for a `Finset R` meeting every prime associate class, and the ultrapower has infinitely many of
them (`FormalSpectrum.infinite_setOf_prime_associates_intUltrapower`), so no finite set satisfies
that hypothesis there and no instantiation at the ring above says anything. A second witness is
needed, and the one that works sits at the opposite extreme: a ring with **no** prime elements.

**The refutation is the empty set.** `FormalSpectrum.forall_dvd_pow_prod` carries `[CommRing R]`
and the instance and — unlike every theorem above — **no** `[IsDomain R]`, so deleting the instance
leaves a statement about an arbitrary commutative ring; and it is quantified over a `Finset R`. At
the empty set its hypothesis reads *there are no prime elements* and its conclusion reads *every
`s ≠ 0` divides `1`*. So what refutes it is a ring with no primes and one nonzero non-unit, and no
divisibility argument, no fraction field and no denominator condition enter at all. That reduction
is why this section is short; it is not a second development of anything above.

The ring of all algebraic integers is such a ring. Every element is a square, because the ambient
field is algebraically closed and a square root of an algebraic integer is again one; an element
that is a square of a non-unit is not irreducible and hence not prime, and here the square root is
a non-unit whenever the element is. And `2` is not a unit, because a rational algebraic integer is
a rational integer. **That the witness is an integral closure in an algebraically closed field, and
not the ring of integers of a number field, is what makes the first half true** — a ring of
integers is not closed under square roots, which is why
`FormalSchemes.StructureSheafStalkPowerSeriesNumberField` cannot supply this witness even though it
is the file about integral closures of `ℤ`.

**The same ring measures `FormalSpectrum.exists_forall_dvd_pow_of_finite_primes` as well**, which
`FormalSpectrum.forall_dvd_pow_prod` is the inside of, and there the reduction is different: the
hypothesis holds vacuously and the conclusion has to fail at *every* candidate `m`, not at one
chosen `Finset`. That half needs one arithmetic fact this ring's non-factorisation properties do
not supply — that a nonzero element of it divides a nonzero rational integer — and it is proved
below, with the two steps that turn it into the refutation.
-/

/-- **The ring of all algebraic integers**: the integral closure of `ℤ` in an algebraic closure of
`ℚ`.

It is an `abbrev` so that its `CommRing` instance and its coercion to `AlgebraicClosure` are found
without unfolding, as `FormalSpectrum.IntUltrapower` above is. Nothing here develops its
factorisation theory: the only facts proved about it are the five below, and in particular it is
**not** claimed to be or not to be a `UniqueFactorizationMonoid`, a Bézout ring or a Dedekind
domain, and no class group is mentioned. -/
abbrev AlgInt := integralClosure ℤ (AlgebraicClosure ℚ)

/-- **Every algebraic integer is a square.** `IsAlgClosed.exists_pow_nat_eq` produces a square root
in `AlgebraicClosure ℚ` and `isIntegral_trans`, against the monic `X ^ 2 - C p`, puts it back in
the integral closure.

**This is the step that fixes the witness.** The second half of the argument runs the square root
back through the coercion, which is an injection of a subring, so no choice of root matters. A ring
of integers of a number field is not closed under square roots and would fail here at once. -/
theorem exists_sq_eq_algInt (p : AlgInt) : ∃ r : AlgInt, r * r = p := by
  obtain ⟨r, hr⟩ :=
    IsAlgClosed.exists_pow_nat_eq (p : AlgebraicClosure ℚ) (n := 2) (by norm_num)
  have hint : IsIntegral ℤ r :=
    isIntegral_trans (A := AlgInt) r
      ⟨Polynomial.X ^ 2 - Polynomial.C p, Polynomial.monic_X_pow_sub_C _ two_ne_zero, by simp [hr]⟩
  exact ⟨⟨r, hint⟩, Subtype.ext (by push_cast; rw [← hr]; ring)⟩

/-- **The ring of all algebraic integers has no prime elements at all.**

`Prime.irreducible` against `p = r * r`: `Irreducible.isUnit_or_isUnit` makes `r` a unit on
whichever side it is read, so `p` is a product of two units and `Prime.not_unit` is contradicted.
No factorisation is exhibited and no irreducible element is produced — there are none of those
either, and only the prime statement is needed below. -/
theorem not_prime_algInt (p : AlgInt) : ¬ Prime p := by
  intro hp
  obtain ⟨r, hr⟩ := exists_sq_eq_algInt p
  rcases hp.irreducible.isUnit_or_isUnit hr.symm with h | h <;> exact hp.not_unit (hr ▸ h.mul h)

/-- **`2` is not a unit of the ring of all algebraic integers**, which is the classical *a rational
algebraic integer is a rational integer*.

A right inverse `u` of `2` satisfies `2 * u = 1` in `AlgebraicClosure` and so is the image of
`1 / 2`; `isIntegral_algebraMap_iff` pushes its integrality down to `(1 / 2 : ℚ)` along the
injection of `ℚ`, and `IsIntegrallyClosed.isIntegral_iff` at `ℤ` produces an integer `y` with
`2 * y = 1`.

**This is where the section's one Mathlib import is spent**: `IsIntegrallyClosed ℤ` is
declared in `Mathlib/RingTheory/Polynomial/RationalRoot.lean`, and everything else here was already
reachable. It is spent once and consumed twice; the second consumer is
`FormalSpectrum.dvd_of_intCast_dvd_intCast_algInt`, which adds no import of its own. Nothing
distinguishes `2` beyond its being a nonzero non-unit; it is used rather than named because the
two theorems that consume it want an element and not a definition. -/
theorem not_isUnit_two_algInt : ¬ IsUnit (2 : AlgInt) := by
  intro h
  obtain ⟨u, hu⟩ := h.exists_right_inv
  have hval : (2 : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ) = 1 := by
    have := congrArg (Subtype.val) hu; push_cast at this; exact this
  have hcast : (algebraMap ℚ (AlgebraicClosure ℚ)) (1 / 2) = (u : AlgebraicClosure ℚ) := by
    rw [map_div₀, map_one, map_ofNat, div_eq_iff (two_ne_zero (α := AlgebraicClosure ℚ))]
    linear_combination -hval
  have h3 : IsIntegral ℤ (1 / 2 : ℚ) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mp (hcast ▸ u.2)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h3
  have hq : (y : ℚ) = 1 / 2 := by simpa using hy
  have : (2 * y : ℤ) = 1 := by
    have : ((2 * y : ℤ) : ℚ) = 1 := by push_cast [hq]; norm_num
    exact_mod_cast this
  omega

/-- **The quantified form: `FormalSpectrum.forall_dvd_pow_prod` is false without unique
factorisation.**

The statement is that theorem's own, with `[UniqueFactorizationMonoid R]` deleted and nothing else
changed — the universe restricted to `Type` as in
`FormalSpectrum.not_forall_hasBoundedDenominators_imp_exists_forall_dvd_pow` above, the neighbouring
statement of the same shape, which the witness meets.

**There is no conjunction beside it**, unlike each of the three refutations above. Those pair a
hypothesis and a failed conclusion at one ring because each destructures a two-part fact about that
ring; this one destructures nothing. It applies the quantified statement at the empty set, where
the hypothesis is `FormalSpectrum.not_prime_algInt` and the conclusion is refuted by
`FormalSpectrum.not_isUnit_two_algInt`, so a conjunction of those two would be a name for an
anonymous constructor and for nothing else. -/
theorem not_forall_forall_dvd_pow_prod :
    ¬ ∀ (R : Type) [CommRing R] (t : Finset R),
        (∀ p : R, Prime p → ∃ q ∈ t, Associated p q) →
          ∀ s : R, s ≠ 0 → ∃ k : ℕ, s ∣ t.prod id ^ k := by
  intro h
  obtain ⟨k, hk⟩ := h AlgInt ∅ (fun p hp => absurd hp (not_prime_algInt p)) 2 two_ne_zero
  simp only [Finset.prod_empty, one_pow] at hk
  exact not_isUnit_two_algInt (isUnit_of_dvd_one hk)

/-! ### The same witness settles the sibling question too, and no valuation is needed

`FormalSpectrum.exists_forall_dvd_pow_of_finite_primes` is the theorem
`FormalSpectrum.forall_dvd_pow_prod` is the inside of, and it carries the same instance. **That
instance is needed too**, at the same ring and for a stronger reason than the shape of the question
suggests: the ring of all algebraic integers satisfies that theorem's hypothesis, having no prime
associate classes at all, and **no** element of it is a clearing element — not the units, and not
the non-units either.

**The argument does not go through valuations, and that is the point.** Producing a prime of this
ring above a rational prime outside the support of `m` would need every element to lie in a number
field and would need the primes of that field's ring of integers; this ring has no primes at all,
so that route does not exist here. What replaces it is three elementary steps, all inside what
this file already imports:

* every nonzero element divides a nonzero rational integer
  (`FormalSpectrum.exists_int_ne_zero_dvd_algInt`), by stripping the factors of `X` off any monic
  integer polynomial that kills it until the constant coefficient is nonzero, at which point that
  coefficient is the multiple;
* a divisibility between two rational integers descends from this ring to `ℤ`
  (`FormalSpectrum.dvd_of_intCast_dvd_intCast_algInt`), because the quotient is a rational number
  and is integral over `ℤ`. This is `FormalSpectrum.not_isUnit_two_algInt`'s own proof generalised
  from `1 / 2` to `b / a`, and it is what the single Mathlib import of this section already paid
  for;
* so a rational prime larger than that multiple divides no power of the element
  (`FormalSpectrum.exists_ne_zero_forall_not_dvd_pow_algInt`), since a divisibility of powers would
  descend to a divisibility in `ℤ` that primality forbids.

The unit case is the special case `m` a unit, where the multiple can be taken to be `1`; it is no
longer stated separately.
-/

/-- **The ring of all algebraic integers has finitely many prime associate classes: none.**

`Associates.mk_surjective` and `Associates.prime_mk` off `FormalSpectrum.not_prime_algInt`, so the
set is empty rather than merely finite. This is the hypothesis of
`FormalSpectrum.exists_forall_dvd_pow_of_finite_primes` at this ring, and it is the reason that
theorem's instance is measured here rather than at the ultrapower, whose prime classes are infinite
(`FormalSpectrum.infinite_setOf_prime_associates_intUltrapower`). -/
theorem finite_setOf_prime_associates_algInt : {a : Associates AlgInt | Prime a}.Finite := by
  convert Set.finite_empty
  ext a
  obtain ⟨p, rfl⟩ := Associates.mk_surjective a
  simpa using fun hp => not_prime_algInt p (Associates.prime_mk.mp hp)

/-- The degree induction inside `FormalSpectrum.exists_int_ne_zero_dvd_algInt`, which is the only
place it is used and is where its statement is explained. It is separate only because the induction
has to be run with the polynomial generalised. -/
private theorem exists_int_ne_zero_dvd_of_aeval_eq_zero (m : AlgInt) (hm : m ≠ 0) :
    ∀ (n : ℕ) (p : Polynomial ℤ), p.natDegree ≤ n → p ≠ 0 → Polynomial.aeval m p = 0 →
      ∃ N : ℤ, N ≠ 0 ∧ m ∣ (N : AlgInt) := by
  intro n
  induction n with
  | zero =>
      intro p hdeg hp0 heval
      have hc : p.coeff 0 ≠ 0 := fun h =>
        hp0 (by rw [Polynomial.eq_C_of_natDegree_le_zero hdeg, h, map_zero])
      refine ⟨p.coeff 0, hc, ?_⟩
      have hz : ((p.coeff 0 : ℤ) : AlgInt) = 0 := by
        have h2 := heval
        rw [Polynomial.eq_C_of_natDegree_le_zero hdeg] at h2
        simpa using h2
      rw [hz]
      exact dvd_zero m
  | succ n ih =>
      intro p hdeg hp0 heval
      by_cases hc : p.coeff 0 = 0
      · have hpx : p.divX * Polynomial.X = p := by
          have h3 := Polynomial.divX_mul_X_add p
          rw [hc, map_zero, add_zero] at h3
          exact h3
        have hdvx : p.divX ≠ 0 := fun h => hp0 (by rw [← hpx, h, zero_mul])
        have heval' : Polynomial.aeval m p.divX = 0 := by
          have h4 : Polynomial.aeval m p.divX * m = 0 := by
            have h5 := congrArg (Polynomial.aeval m) hpx
            simpa using h5.trans heval
          rcases mul_eq_zero.mp h4 with h | h
          · exact h
          · exact absurd h hm
        refine ih p.divX ?_ hdvx heval'
        have h6 : p.divX.natDegree = p.natDegree - 1 :=
          Polynomial.natDegree_divX_eq_natDegree_tsub_one
        have h7 : p.natDegree ≠ 0 := fun h =>
          hp0 (by rw [Polynomial.eq_C_of_natDegree_le_zero h.le, hc, map_zero])
        omega
      · refine ⟨p.coeff 0, hc, ?_⟩
        have key := congrArg (Polynomial.aeval m) (Polynomial.divX_mul_X_add p)
        rw [heval] at key
        simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at key
        refine ⟨-(Polynomial.aeval m p.divX), ?_⟩
        have hcast : ((p.coeff 0 : ℤ) : AlgInt) = algebraMap ℤ AlgInt (p.coeff 0) := by norm_cast
        rw [hcast]
        linear_combination key

/-- **Every nonzero algebraic integer divides a nonzero rational integer.**

Any monic integer polynomial killing `m` will do, and no minimal one is needed: if its constant
coefficient is nonzero then `Polynomial.divX_mul_X_add` exhibits `m` as a factor of that
coefficient, and if it vanishes the polynomial is its own `Polynomial.divX` times `Polynomial.X`,
so `m ≠ 0` in a domain leaves that quotient killing `m` with one degree less. **No `minpoly`, no
norm and no number field.**
`minpoly.coeff_zero_ne_zero`, which is what this looks like it wants, is stated over a *field* and
so says nothing about `minpoly ℤ`; routing through `minpoly ℚ` instead would cost a Mathlib module
this file does not have, and the induction costs none. -/
theorem exists_int_ne_zero_dvd_algInt (m : AlgInt) (hm : m ≠ 0) :
    ∃ N : ℤ, N ≠ 0 ∧ m ∣ (N : AlgInt) := by
  obtain ⟨p, hpm, hp⟩ := integralClosure.isIntegral m
  refine exists_int_ne_zero_dvd_of_aeval_eq_zero m hm p.natDegree p le_rfl hpm.ne_zero ?_
  simpa [Polynomial.aeval_def] using hp

/-- **A divisibility between rational integers descends from the ring of all algebraic integers to
`ℤ`.** The witness is the rational number `b / a`, and it is integral over `ℤ`.

This is `FormalSpectrum.not_isUnit_two_algInt`'s proof at `b / a` instead of `1 / 2`, on the same
three steps — `isIntegral_algebraMap_iff` down the injection of `ℚ`, the membership that defines
the integral closure, and `IsIntegrallyClosed.isIntegral_iff` at `ℤ`. It spends no import that
theorem has not already spent. The converse is `Int.cast` being a ring homomorphism and is not
stated, because nothing here wants it. -/
theorem dvd_of_intCast_dvd_intCast_algInt {a b : ℤ} (h : (a : AlgInt) ∣ (b : AlgInt))
    (ha : a ≠ 0) : a ∣ b := by
  obtain ⟨w, hw⟩ := h
  have hval : (b : AlgebraicClosure ℚ) = (a : AlgebraicClosure ℚ) * (w : AlgebraicClosure ℚ) := by
    have := congrArg (Subtype.val) hw
    push_cast at this
    exact this
  have hane : (a : AlgebraicClosure ℚ) ≠ 0 := by
    exact_mod_cast (by exact_mod_cast ha : (a : ℚ) ≠ 0)
  have hcast : (algebraMap ℚ (AlgebraicClosure ℚ)) ((b : ℚ) / (a : ℚ))
      = (w : AlgebraicClosure ℚ) := by
    rw [map_div₀]
    simp only [map_intCast]
    rw [div_eq_iff hane]
    linear_combination hval
  have hint : IsIntegral ℤ ((b : ℚ) / (a : ℚ)) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mp (hcast ▸ w.2)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hq : (y : ℚ) = (b : ℚ) / (a : ℚ) := by simpa using hy
  refine ⟨y, ?_⟩
  have : ((b : ℚ)) = (a : ℚ) * (y : ℚ) := by rw [hq]; field_simp
  exact_mod_cast this

/-- **No element of the ring of all algebraic integers is a clearing element**: for every `m ≠ 0`
there is a nonzero `s` dividing no power of `m`, and `s` can be taken to be a rational prime.

Take a nonzero rational integer `N` that `m` divides
(`FormalSpectrum.exists_int_ne_zero_dvd_algInt`) and a rational prime `q` exceeding its absolute
value (`Nat.exists_infinite_primes`, the same source as the ultrapower's primes above). Then
`q ∣ m ^ k` would give `q ∣ N ^ k` in this ring, hence in `ℤ`
(`FormalSpectrum.dvd_of_intCast_dvd_intCast_algInt`), hence `q ∣ N`, which `q > |N| ≠ 0` forbids.

**The units are not a separate case.** A unit `m` divides `1`, so the prime produced is any prime
at all, and the statement below covers it; that is why no unit-only form of it is stated. -/
theorem exists_ne_zero_forall_not_dvd_pow_algInt (m : AlgInt) (hm : m ≠ 0) :
    ∃ s : AlgInt, s ≠ 0 ∧ ∀ k : ℕ, ¬ s ∣ m ^ k := by
  obtain ⟨N, hN, hmN⟩ := exists_int_ne_zero_dvd_algInt m hm
  obtain ⟨q, hqge, hqp⟩ := Nat.exists_infinite_primes (N.natAbs + 1)
  have hqz : ((q : ℤ)) ≠ 0 := by exact_mod_cast hqp.ne_zero
  refine ⟨((q : ℤ) : AlgInt), by exact_mod_cast hqz, ?_⟩
  intro k hk
  have hpow : ((q : ℤ) : AlgInt) ∣ ((N ^ k : ℤ) : AlgInt) := by
    refine hk.trans ?_
    push_cast
    exact pow_dvd_pow_of_dvd hmN k
  have hdvd : (q : ℤ) ∣ N ^ k := dvd_of_intCast_dvd_intCast_algInt hpow hqz
  have hqN : (q : ℤ) ∣ N := (Nat.prime_iff_prime_int.mp hqp).dvd_of_dvd_pow hdvd
  have habs : q ∣ N.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hqN
    simpa using this
  have hle : q ≤ N.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hN) habs
  omega

/-- **`FormalSpectrum.exists_forall_dvd_pow_of_finite_primes` is false without unique
factorisation.**

The statement is that theorem's own, with `[UniqueFactorizationMonoid R]` deleted and nothing else
changed — the universe restricted to `Type` as in
`FormalSpectrum.not_forall_forall_dvd_pow_prod` above, the neighbouring statement of the same shape,
which the same witness meets.

**Both halves are total rather than sampled**, which is what distinguishes this from the three
refutations above and from the unit-only statement this replaces: the hypothesis holds at the ring
of all algebraic integers because it has *no* prime associate classes
(`FormalSpectrum.finite_setOf_prime_associates_algInt`), and the conclusion fails there because
*no* nonzero element is a clearing element
(`FormalSpectrum.exists_ne_zero_forall_not_dvd_pow_algInt`). Nothing is chosen but the ring. -/
theorem not_forall_exists_forall_dvd_pow_of_finite_primes :
    ¬ ∀ (R : Type) [CommRing R] [IsDomain R], {a : Associates R | Prime a}.Finite →
        ∃ m : R, m ≠ 0 ∧ ∀ s : R, s ≠ 0 → ∃ k : ℕ, s ∣ m ^ k := by
  intro h
  obtain ⟨m, hm, hall⟩ := h AlgInt finite_setOf_prime_associates_algInt
  obtain ⟨s, hs, hns⟩ := exists_ne_zero_forall_not_dvd_pow_algInt m hm
  obtain ⟨k, hk⟩ := hall s hs
  exact hns k hk

end FormalSpectrum

end
