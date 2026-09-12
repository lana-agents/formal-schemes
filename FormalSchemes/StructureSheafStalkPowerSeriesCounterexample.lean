import FormalSchemes.CountableLocalization
import FormalSchemes.StructureSheafStalkPowerSeriesGeneric
import Mathlib.Data.Nat.Prime.Int

set_option linter.style.header false

/-!
# The criterion at `(X) ⊆ R⟦X⟧`: the two rings, two generic points, and the half characterised

`FormalSpectrum.IsStalkLimit` — the stalk half of EGA I 10.8, *the stalk of the completion is the
completion of the stalk* — had three values when this file was started, all positive and all at a
point where the colimit over basic opens has nothing to do: `FormalSpectrum.isStalkLimit_bot`,
`FormalSpectrum.isStalkLimit_of_isNilpotent`, and `FormalSpectrum.isStalkLimit_powerSeriesX_field`
at `(X) ⊆ k⟦X⟧` for `k` a field. `FormalSchemes.StructureSheafStalkPowerSeriesGeneric` took the
first target where the colimit does move — `(X) ⊆ ℤ⟦X⟧` at the generic point of `Spec ℤ` — proved
that the difficulty is neither at a single level of the stalk tower nor before completing
(`FormalSpectrum.exists_awayToAtPrimeLevel_eq`), and stopped, recording that finishing needs two
ring identifications that were not on the tree.

This file proves those two identifications and finishes.
**`FormalSpectrum.not_isStalkLimit_powerSeriesXIntGenericPoint`: `FormalSpectrum.IsStalkLimit` is
false at `(X) ⊆ ℤ⟦X⟧` at the generic point.** It is the first negative value of the predicate
anywhere.

**And the refutation is sharp.** The predicate is a conjunction, and a conjunction can be false
for a boring reason — both halves failing. Here the injectivity half **holds**, at this point and
indeed at the generic point of every domain
(`FormalSpectrum.exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint`), so
`FormalSpectrum.IsStalkLimit` fails at `(X) ⊆ ℤ⟦X⟧` for exactly one reason, recorded as
`FormalSpectrum.injective_and_not_surjective_powerSeriesXIntGenericPoint`. The same two
identifications give both: read through them the comparison map is `PowerSeries.map` of
`ℤ[1/m] → ℚ`, which is injective coefficient by coefficient and misses `1 / p` for every prime
`p > |m|`.

**And the predicate is not positive only where it is idle.** The same two identifications, run in
the other direction over a discrete valuation ring, give
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint`: at `(X) ⊆ R⟦X⟧` at the generic point of a
discrete valuation ring `FormalSpectrum.IsStalkLimit` **holds**, and it holds at a point that is
not closed and where a witness really is produced
(`FormalSpectrum.isStalkLimit_and_not_isClosed_powerSeriesXGenericPoint`, and at `ℚ⟦T⟧` with no
hypothesis at all in
`FormalSpectrum.isStalkLimit_and_not_isClosed_powerSeriesXRatSeriesGenericPoint`). So the standing
picture
is not "positive exactly when the colimit has nothing to do": the predicate takes both values at
points where the colimit moves, and what separates `ℤ` from a discrete valuation ring is how many
primes have to be inverted at once. Inverting one uniformizer already gives the whole fraction
field; no single `m` does that over `ℤ`.

## The two identifications

* `FormalSpectrum.awayCompletionEquivPowerSeriesAway`: **`R⟦X⟧{1/f} ≃+* R[1/m]⟦X⟧`**, where `m` is
  the constant term of `f`, at every commutative ring and every `f`. Completing `R⟦X⟧[1/f]`
  `X`-adically both inverts `m` — which the localization itself need not do — and supplies the
  unbounded denominators no localization of `R⟦X⟧` contains.
* `FormalSpectrum.atPrimeCompletionEquivFractionPowerSeries`: **the target at the generic point is
  `(Frac R)⟦X⟧`**, at every domain. Over `ℤ` it is `ℚ⟦X⟧`.
* `FormalSpectrum.atPrimeCompletionEquiv_awayToAtPrimeCompletion`: under those two, the comparison
  map `FormalSpectrum.awayToAtPrimeCompletion` **is** `PowerSeries.map` of `R[1/m] → Frac R`.

Read through them, the surjectivity half of
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff` at `R = ℤ` says: *every element of
`ℚ⟦X⟧` has all of its coefficients in a single `ℤ[1/m]`.* The series with coefficients `1/(n + 1)`
(`FormalSpectrum.unitFractionSeries`) refutes it, because a prime `p > |m|` divides no power of
`m`.

**That reading is a theorem, not a gloss.**
`FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff` says the half
holds at the generic point of a domain `R` **iff** every `ℕ`-indexed family in `Frac R` lies in a
single `R[1/m]` with `m ≠ 0`, and
`FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators`
restates that with no localization in it: every such family has a common denominator up to powers
of one element. Both values of the half in this file are corollaries of it, and both proofs are
shorter for going through it. It characterises **one conjunct**, and at this one point that
conjunct turns out to be the whole predicate: the other one holds at the generic point of every
domain, so the conjunction collapses onto it
(`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`, below). At any
other point, and at any other ideal of definition, it still says nothing about
`FormalSpectrum.IsStalkLimit`.

**And the condition has a name.** `FormalSpectrum.HasBoundedDenominators` is that right-hand side:
every `ℕ`-indexed family in `Frac R` has a single denominator up to powers. It is a condition on
`R` alone — no completion, no localization of `R⟦X⟧`, no power series — and equivalently a
condition on countable *subsets* of `Frac R`
(`FormalSpectrum.hasBoundedDenominators_iff_countable`). Each value of the half in this file is
now a value of it: **a field satisfies it** with `m = 1`, **a discrete valuation ring** with a
uniformizer, and **`ℤ` does not**, because a prime larger than `|m|` divides no power of `m`. So
the shape of the answer is that the half is about how many primes have to be inverted at once, and
the geometric statements are that arithmetic read through the two identifications.

**And at a unique factorisation domain the condition is decided.**
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`: it holds **iff** there are finitely many
primes up to associates. That is the cardinality the sentence above calls *how many*, and it makes
the three values three cases of one theorem — the empty set, a singleton, and Euclid. Two criteria
hold at an *arbitrary* domain and are what the classification glues: a single `m ≠ 0` whose powers
clear every denominator gives the condition
(`FormalSpectrum.hasBoundedDenominators_of_forall_dvd_pow`), and a family of primes divisible into
no single element refutes it (`FormalSpectrum.not_hasBoundedDenominators_of_primes`).

**And at this point the condition is the predicate.** The criterion is a conjunction whose
injectivity half holds at the generic point of every domain, so nothing but the surjectivity half
is ever at stake there and the conjunction collapses:
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators` says
`FormalSpectrum.IsStalkLimit` holds at `(X) ⊆ R⟦X⟧` at the generic point **iff** `R` satisfies the
denominator condition, at every domain and under no further hypothesis. Composed with the
classification that is a cardinality:
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_finite_primes` — **at a unique
factorisation domain the stalk of the completion is the completion of the stalk at the generic
point of `R⟦X⟧` exactly when `R` has finitely many primes up to associates.** Those two are
statements about the predicate itself rather than about one of its halves, and they are made at
this one point and at no other.

**Away from that hypothesis nothing here decides which rings satisfy the condition**, and the
criteria on their own still do not meet: **the sufficient one is not necessary at a general
domain**, and the obstruction is the one this file names — the condition only ever sees *countable*
families, so a domain whose fraction field needs uncountably many denominator types satisfies it
with no single `m` serving every element. Such a domain exists and is exhibited in
`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`, an ultrapower of `ℤ`; nothing below bears
on it in either direction. None of the obvious guesses about semilocal, Prüfer or valuation domains
is checked anywhere below. A Dedekind domain is not a corollary of the classification either — it
is a statement about **ideals**, and a nonprincipal maximal ideal contributes no prime element at
all — and that is exactly why it takes a *second* refuting criterion, stated at prime ideals, which
`FormalSchemes.StructureSheafStalkPowerSeriesDedekind` supplies:
`FormalSpectrum.hasBoundedDenominators_iff_finite_primeIdeals` decides the condition there and
nothing in this file does.

**Under a second hypothesis the two criteria meet again, and this one is that same obstruction
removed rather than got round.** When `Frac R` is **countable** there is no room for uncountably
many denominator types, so the condition may be applied to the whole of `Frac R` at once, and
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` makes the sufficient criterion
necessary as well: the condition holds exactly when a single `R[1/m]` is already the whole
fraction field. **Unlike the classification this decides no ring** — it trades one condition for a
more elementary one, which a consumer can check by hand at a given ring, and which rings satisfy
*that* is not determined here either. Its sharpest consequences are arithmetic with no geometry
left in them at all: `FormalSpectrum.not_exists_surjective_awayToFractionRing_int` says **no single
`ℤ[1/m]` is `ℚ`**, and `FormalSpectrum.not_exists_isField_localizationAway_int` says **no single
`ℤ[1/m]` is a field**.

**The condition has three further spellings and the last of them names no map.** At a fixed
`m ≠ 0` at an arbitrary domain, `R[1/m] → Frac R` being surjective, every nonzero element of `R`
dividing a power of `m`, and `R[1/m]` being a field are the same hypothesis
(`FormalSpectrum.surjective_awayToFractionRing_iff_forall_dvd_pow`,
`FormalSpectrum.surjective_awayToFractionRing_iff_isField`), and
`FormalSpectrum.surjective_awayToFractionRing_iff_isField` is Mathlib's
`IsFractionRing.surjective_iff_isField` read at `R[1/m]`. Under `[Countable (FractionRing R)]` the
quantifier over `m` may be put back in front of any of the three, and the resulting statement of
the condition is respectively
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective`,
`FormalSpectrum.hasBoundedDenominators_iff_forall_dvd_pow` — which mentions no fraction field and
no localization at all — and `FormalSpectrum.hasBoundedDenominators_iff_exists_isField`: **the
denominator condition is *some `R[1/m]` is already a field*.** None of the three decides a ring;
they say what the condition is, not which rings have it.

**The two hypotheses are incomparable and neither result subsumes the other.** Unique
factorisation does not imply a countable fraction field (`ℂ[X]`) and a countable fraction field
does not imply unique factorisation (an order in a number field with class number greater than
one). Where they overlap the two statements agree, and that agreement is checked below as an
`example` rather than asserted.

## The tool that was missing, and why the one on the tree does not do it

`AdicCompletion.bijective_mapCompletion` (`FormalSchemes.StructureSheafStalkPowerSeries`) makes the
completion of a **bijection** a bijection. That is useless here: `R⟦X⟧[1/f] → R[1/m]⟦X⟧` is not
injective and not surjective, and only becomes bijective after quotienting by a power of `(X)`.
`AdicCompletion.bijective_mapCompletion_of_bijective_quotientMap` is the statement actually needed
— *bijective at every level implies bijective on completions* — and it holds at every pair of
finitely generated ideals with no reference to power series. Its proof constructs no element of the
source ring: injectivity is `AdicCompletion.ext_evalₐ`, and surjectivity assembles levelwise
preimages inside the completion, which is complete.

## What is *not* proved here

**`FormalSpectrum.IsStalkLimit` is not false in general, and this file must not be read as saying
so.** It is refuted at one point of one ring. The three positive values that predate this file are
untouched, and each is still exactly as general as it was; in particular
`FormalSpectrum.isStalkLimit_powerSeriesX_field` holds at `(X) ⊆ k⟦X⟧` for every field `k`, so the
predicate genuinely depends on the ring and not only on the ideal of definition. This file adds a
fourth positive value, at the generic point of a discrete valuation ring, and it is equally not a
statement about the predicate in general.

**Nothing about EGA I 10.8's own statement is contradicted.** `FormalSpectrum.IsStalkLimit` is this
tree's bijectivity assertion for `FormalSpectrum.stalkToAdicCompletion` at a single point, carrying
none of EGA's standing hypotheses — no Noetherian hypothesis, no adic-ring hypothesis on the base,
no finiteness on the point. `ℤ⟦X⟧` *is* Noetherian, so the counterexample is not "a non-Noetherian
pathology"; what it shows is that the naked statement, at an arbitrary point of an arbitrary
`Spf`, is false, and that any true form of the stalk half needs a hypothesis this tree's predicate
does not carry. **Which hypothesis is not determined here** and no repair is proposed.

**Nothing about the injectivity half away from the generic point.** The half is proved below, at
the generic point of every domain, and that is the whole of what is claimed for it: it is
attempted at no other point, at no other ideal of definition, and in no generality that would
bear on EGA I 10.8's own statement. The counterexample proper still says nothing about it —
`FormalSpectrum.not_isStalkLimit_powerSeriesXIntGenericPoint` refutes the conjunction by refuting
surjectivity alone, and the two halves are established by separate arguments below.

**No general statement about `IsStalkLimit` at a non-closed point — one non-closed point only.**
The refutation at `ℤ` uses `FormalSpectrum.unitFractionSeries` and the infinitude of the primes,
and the two identifications, though they hold much more generally — the first at every commutative
ring, the second at every domain — are identifications at the **generic point of `R⟦X⟧`** and
nowhere else. At that one point the predicate is characterised, in both directions and with no
hypothesis beyond `IsDomain R`
(`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`), and at a
unique factorisation domain the characterisation is a cardinality
(`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_finite_primes`). **That is the whole of
what is claimed about the predicate.** The statement *`IsStalkLimit` holds at `(X) ⊆ R⟦X⟧` for
exactly these `R`* is proved **here** and at **this** point; no statement of that form is proved at
any other point, and the surjectivity half on its own is still all that
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes` decides.

**What is still open, which is what a successor needs.** Three things were named here as open,
none of them touched below, and **the first has since been closed elsewhere on the tree**: the
predicate at a point of `Spf (R⟦X⟧, (X))` **other than the generic one** is settled at every point
of every domain by `FormalSchemes.StructureSheafStalkPowerSeriesPoint`, in
`FormalSpectrum.isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt`. The other two are
still open: the predicate at an **ideal of definition of `R⟦X⟧` other than `(X)`**, and the
predicate at a formal spectrum whose ring is **not a power series ring** at all. Nothing below
bears on any of the three, and nothing below is even stated at another point: both inputs to the
characterisation — the injectivity half and the identification of the surjectivity half with the
condition — name `FormalSpectrum.powerSeriesXGenericPoint` in their statements, so moving the
point means restating them. That restatement was the whole of the cost, and it turned out to be
small: `FormalSpectrum.awayCompletionEquivPowerSeriesAway` was already at every commutative ring,
and `FormalSpectrum.atPrimeCompletionEquivFractionPowerSeries` was reproved at every ring and
every point as `FormalSpectrum.atPrimeCompletionEquivLocalizationPowerSeries`, its domain
hypothesis doing no work at all — the one step that looks as though it needs a fraction field is a
common-denominator argument inside the prime complement `Ideal.primeCompl`. **Moving the ideal is
what remains untested.** What is on the tree elsewhere is not surveyed here beyond that; in
particular this says nothing about which of the general criteria in
`FormalSchemes.StructureSheafStalkPowerSeries` do or do not apply at some other point.

**The collapse is not claimed without countability.** Whether
`FormalSpectrum.HasBoundedDenominators` is equivalent to *some `R[1/m]` is already `Frac R`* at an
arbitrary domain is **settled by no argument in this file**: no proof is given, no counterexample
is exhibited below, and nothing below should be read as evidence for either answer. What is proved
here is the implication that holds at every domain
(`FormalSpectrum.hasBoundedDenominators_of_surjective`) and its converse under
`[Countable (FractionRing R)]` (`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective`).
**The hypothesis is needed**, which is proved one module downstream in
`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`: an ultrapower of `ℤ` satisfies the
condition while no single `R[1/m]` is its fraction field, so the converse is false without it.
That removes nothing from anything below, which is consumed exactly as it stands.

**And the collapse is not a classification.** It replaces one condition on `R` by a more
elementary one; **which countable domains satisfy either is not determined here**, and no
Dedekind, semilocal, Prüfer or valuation ring is decided by it. In particular nothing below
computes the set of `m` that work at any ring other than a field, a discrete valuation ring, and
`ℤ` — where the answer is that none does
(`FormalSpectrum.not_exists_surjective_awayToFractionRing_int`).

**Nothing under a Noetherian hypothesis**, and nothing that uses one.

**No comparison with `Spec`.** `FormalSchemes.SpfDiscrete` is not imported; measured at **42**
modules besides itself on top of this file's closure, 43 including it, and nothing here needs it.

## Implementation notes

The five `AdicCompletion` lemmas at the top of the file mention no formal geometry and would sit
naturally in `FormalSchemes.Completion`, whose reverse closure is 448 of the project's 561 modules
against this file's 5. They are kept here on the disposition
`FormalSchemes.StructureSheafStalkPowerSeries` recorded for
`AdicCompletion.bijective_mapCompletion` — which is the same shape and is still in that file — and
because every consumer is in this file. **If a second file needs
`AdicCompletion.bijective_mapCompletion_of_bijective_quotientMap`, the two belong together and the
move should be made for both at once.**

`PowerSeries.constantCoeff_map` is a `_root_` lemma: Mathlib has the `MvPowerSeries` form and not
the `PowerSeries` one. It is stated here rather than in a Mathlib mirror because it is one
`PowerSeries.coeff_map` away and has one consumer.

The whole file is arranged so that no element of an `AdicCompletion` is ever written down except
through `AdicCompletion.mapCompletion` and `algebraMap`. The counterexample's witness is a
`PowerSeries`, and it reaches the completion only through the inverse of
`FormalSpectrum.atPrimeCompletionEquivFractionPowerSeries`.

## Placement

Over `FormalSchemes.StructureSheafStalkPowerSeriesGeneric` and
`FormalSchemes.CountableLocalization`: forward closure **52** project modules besides itself (53
counted with itself), reverse closure **5** —
`FormalSchemes.StructureSheafStalkPowerSeriesDedekind`, which carries the classification at prime
ideals, and over it both
`FormalSchemes.StructureSheafStalkPowerSeriesNumberField`, which instantiates the refuting
criterion at a ring of integers, and `FormalSchemes.StructureSheafStalkPowerSeriesLocal`, which
instantiates it at `ℤ[X]` localized at `(2, X)`;
`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`, which settles the collapse without
countability at an ultrapower of `ℤ`; and
`FormalSchemes.StructureSheafStalkPowerSeriesPoint`, which decides the predicate at an arbitrary
point — counted by walking every `^import` line over the
561 modules under `FormalSchemes/` (a module is not counted in its own closure, and the aggregator
at the repository root is outside the walk).

**Every closure figure in this docstring comes from that one walk and they go stale together** —
the `FormalSchemes.SpfDiscrete` comparison in `## What is *not* proved here`, the two in
`## Implementation notes`, this one, and the Mathlib-only leaf's below. A forward closure moves
only when this file's own imports move, so any diff that changes one shows it; a reverse closure is
invalidated by a module added anywhere above this file, by a branch that need not touch this file
and cannot be asked to find every figure it moved. Nothing sees such a figure go wrong — not the
build, not the by-name signature diff, not the stripped code-line diff, not
`scripts/citation_audit.py`, since every name in the sentence still resolves and only the number is
stale. **Re-measure all of them at one walk rather than adjusting one**, and say which walk.

The classification section keeps the criteria it glues in one file rather than putting them one
module apart: both of its directions are theorems above it, all three of its cases are theorems
below it, and the prose it makes stale is this docstring's. The collapse section is placed on the
same ground, one section further down.

The second import is the one the collapse section adds, and it is the **Mathlib-only leaf**
`FormalSchemes.CountableLocalization`, whose forward closure is 0 and whose reverse closure is 7 —
holding one statement that was already on the tree:
`Localization.countable_of_countable`, moved out of
`FormalSchemes.CompletionToSpecNotClosedImmersion` and promoted to an instance. That file has
forward closure 25, is not in this file's closure and does not have this file in its own, so
neither could import the other; the statement mentions no formal scheme, no ideal of definition
and no power series, and 25 of the 558 modules are already leaves of exactly that kind. Restating
it here instead of moving it would have been a project-internal duplicate, which is what
`scripts/symm_duplicate_statement_scan.lean` exists to catch; putting it in an existing
Mathlib-only leaf would have turned a file about one localization identity
(`FormalSchemes.LocalizationQuotient`) or about regularity (`FormalSchemes.RegularMulEquiv`) into
a grab bag. It costs one module, one build job, and no Mathlib import that this file's closure did
not already reach.
`Mathlib/RingTheory/AdicCompletion/Completeness.lean`, which carries the
`IsAdicComplete (.span {X}) (PowerSeries R)` instance, is already reached. The discrete-valuation
section adds no Mathlib import either: `IsDiscreteValuationRing`,
`IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible` and `PowerSeries.map_surjective`
are all in this closure already.

**One Mathlib import is not reached and is taken: `Mathlib/Data/Nat/Prime/Int.lean`**, for
`Nat.prime_iff_prime_int` in the consistency check that reads `ℤ` off the refuting criterion. It
costs one build job — everything it imports was already reached — and it is the only Mathlib
import in the file that is not needed by a theorem. The criteria themselves add none:
`IsFractionRing.div_surjective`, `Prime.dvd_of_dvd_pow`, `UniqueFactorizationMonoid.factors`,
`UniqueFactorizationMonoid.exists_mem_factors_of_dvd` and `Set.infinite_range_of_injective` are
all in this closure already, and so is everything the classification adds — `Associates`,
`Associates.mk_surjective`, `UniqueFactorizationMonoid.factors_prod`,
`Multiset.prod_dvd_prod_of_dvd`, `Set.Infinite.natEmbedding` and
`IsDiscreteValuationRing.associated_of_irreducible`.

## Main definitions and results

* `AdicCompletion.bijective_mapCompletion_of_bijective_quotientMap`: **bijective at every level
  implies bijective on completions.**
* `FormalSpectrum.awayCompletionEquivPowerSeriesAway`: **`R⟦X⟧{1/f} ≃+* R[1/m]⟦X⟧`.**
* `FormalSpectrum.atPrimeCompletionEquivFractionPowerSeries`: **the target at the generic point is
  `(Frac R)⟦X⟧`.**
* `FormalSpectrum.atPrimeCompletionEquiv_awayToAtPrimeCompletion`: the comparison map is
  `PowerSeries.map` under those two identifications.
* `FormalSpectrum.isUnit_mk_algebraMap_C_constantCoeff`: the constant term of `f` is a unit modulo
  every power of `(X)`, though not in `R⟦X⟧[1/f]`.
* `FormalSpectrum.unitFractionSeries`, `FormalSpectrum.unitFractionSeries_notMem_range`: the
  witness and the arithmetic that defeats every `m`.
* `FormalSpectrum.injective_awayToFractionRing`: `R[1/m] → Frac R` is injective for `m ≠ 0` in a
  domain.
* `FormalSpectrum.injective_awayToAtPrimeCompletion_powerSeriesXGenericPoint`: **the comparison
  map at the generic point is injective**, at every domain and every `f` with `constantCoeff f ≠
  0`.
* `FormalSpectrum.exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint`: **the
  injectivity half holds** at the generic point of every domain.
* `FormalSpectrum.not_isStalkLimit_powerSeriesXIntGenericPoint`: **`FormalSpectrum.IsStalkLimit` is
  false at `(X) ⊆ ℤ⟦X⟧` at the generic point.**
* `FormalSpectrum.not_surjective_powerSeriesXIntGenericPoint`: **the surjectivity half fails** at
  `ℤ`, which is the whole of the previous statement.
* `FormalSpectrum.injective_and_not_surjective_powerSeriesXIntGenericPoint`: **the refutation is
  sharp** — the injectivity half holds and the surjectivity half fails.
* `FormalSpectrum.surjective_awayToFractionRing_of_irreducible`,
  `FormalSpectrum.isField_localizationAway_of_irreducible`: `R[1/ϖ] → Frac R` is **surjective**
  at a uniformizer of a discrete valuation ring, which is what `ℤ` cannot do at any `m`, and so
  **`R[1/ϖ]` is a field** there — `FormalSpectrum.isField_localizationAway_of_irreducible` is
  `FormalSpectrum.surjective_awayToFractionRing_of_irreducible` read through
  `FormalSpectrum.surjective_awayToFractionRing_iff_isField`, with no countability.
* `FormalSpectrum.exists_isField_localizationAway_of_isDiscreteValuationRing`: the existential
  form of `FormalSpectrum.isField_localizationAway_of_irreducible`, and the **exact negation** of
  `FormalSpectrum.not_exists_isField_localizationAway_int` at the same strength: `ℤ` has no
  `m ≠ 0` with `ℤ[1/m]` a field, a discrete valuation ring has one, and neither statement carries
  a countability hypothesis.
* `FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint`: **the surjectivity
  half holds** at the generic point of a discrete valuation ring, with one `f` for every element.
* `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint`: **`FormalSpectrum.IsStalkLimit` is true at
  `(X) ⊆ R⟦X⟧` at the generic point of a discrete valuation ring.**
* `FormalSpectrum.isStalkLimit_and_not_isClosed_powerSeriesXGenericPoint`: **and it is true at a
  point that is not closed** — the predicate is not positive only where the colimit is idle.
* `FormalSpectrum.isStalkLimit_and_not_isClosed_powerSeriesXRatSeriesGenericPoint`: the same at
  `ℚ⟦T⟧`, so the two theorems above are not conditional on an instance the tree cannot exhibit.
* `PowerSeries.exists_map_eq_iff_forall_coeff_mem_range`: a series is hit by `PowerSeries.map g`
  iff each of its coefficients is hit by `g` — the non-surjective companion of
  `PowerSeries.map_surjective`.
* `FormalSpectrum.mem_range_awayToFractionRing_iff`: membership in the image of `R[1/m] → Frac R`,
  as *some power of `m` clears it into `R`*.
* `FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff`: **the
  surjectivity half at the generic point of a domain is exactly the statement that every
  `ℕ`-indexed family in `Frac R` lies in a single `R[1/m]`.**
* `FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators`:
  the same with the condition named — a common denominator up to powers of one element.
* `FormalSpectrum.HasBoundedDenominators`: **the condition**, as a `def` on a domain: every
  `ℕ`-indexed family in `Frac R` has a single denominator up to powers.
* `FormalSpectrum.hasBoundedDenominators_iff_range`: the same as *lies inside a single `R[1/m]`*.
* `FormalSpectrum.hasBoundedDenominators_iff_countable`: `ℕ`-indexed families and countable
  subsets of `Frac R` give the same condition.
* `FormalSpectrum.surjective_awayToFractionRing_of_forall_dvd_pow`,
  `FormalSpectrum.hasBoundedDenominators_of_surjective`,
  `FormalSpectrum.hasBoundedDenominators_of_forall_dvd_pow`: **the sufficient criterion at an
  arbitrary domain**, in its two halves and composed — one `m ≠ 0` whose powers clear every
  denominator gives the condition. Both values below are instances.
* `FormalSpectrum.forall_dvd_pow_of_surjective_awayToFractionRing`,
  `FormalSpectrum.surjective_awayToFractionRing_iff_forall_dvd_pow`: **the first of those halves
  is an `↔`** — at a fixed `m ≠ 0` at any domain, `R[1/m] → Frac R` is surjective exactly when
  every nonzero element of `R` divides a power of `m`. So the divisibility spelling and the
  localized spelling of the sufficient criterion are one hypothesis, and choosing between them is
  a matter of what a consumer holds. It is a statement about **one** `m` and decides no ring.
* `FormalSpectrum.surjective_awayToFractionRing_iff_isField`: **and it is a statement about the
  ring `R[1/m]` alone** — that surjection exists exactly when `R[1/m]` is a field. This is
  Mathlib's `IsFractionRing.surjective_iff_isField` read at `R[1/m]`, which is not immediate only
  because the `IsFractionRing (Localization.Away m) (FractionRing R)` instance is absent on this
  tree; the proof supplies the algebra structure and cites it. Also about **one** `m`.
* `FormalSpectrum.hasBoundedDenominators_of_isField`: **the sufficient criterion in that third
  spelling** — one `m ≠ 0` with `R[1/m]` a field gives the condition, at every domain and with no
  countability. It is `FormalSpectrum.surjective_awayToFractionRing_iff_isField` composed with
  `FormalSpectrum.hasBoundedDenominators_of_surjective`, and it is the direction of
  `FormalSpectrum.hasBoundedDenominators_iff_exists_isField` below that the countability
  hypothesis does *not* buy.
* `FormalSpectrum.not_hasBoundedDenominators_of_primes`,
  `FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated`: **the refuting criterion**
  — a family of primes divisible into no single element refutes the condition — and the form it
  takes at a unique factorisation domain, where *pairwise non-associated* suffices. Neither
  criterion implies the other and neither is a classification on its own. The second one's
  `[UniqueFactorizationMonoid R]` is **needed**, by
  `FormalSpectrum.not_forall_primes_not_associated_imp_not_hasBoundedDenominators` in
  `FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`, which refutes it with that instance
  deleted; the ultrapower witnessing it falsifies the *first* criterion's divisibility hypothesis
  instead.
* `FormalSpectrum.forall_dvd_pow_prod`: at a unique factorisation domain, **the product of a finite
  set meeting every prime associate class is a denominator for the whole ring**, and
  `FormalSpectrum.exists_forall_dvd_pow_of_finite_primes`: **finitely many primes up to associates
  therefore give such a denominator**, which is the construction inside the classification below
  and is named so that its forward composite can be stated elsewhere rather than copied. The
  first's `[UniqueFactorizationMonoid R]` is **needed**, by
  `FormalSpectrum.not_forall_forall_dvd_pow_prod` in
  `FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`, at the ring of all algebraic integers
  and the empty set. The second's is **not** measured anywhere: that same ring reaches its
  hypothesis and fails only the unit case of its conclusion.
* `FormalSpectrum.hasBoundedDenominators_iff_finite_primes`: **the classification at a unique
  factorisation domain** — the condition holds **iff** `{a : Associates R | Prime a}` is finite.
  Its two directions are `FormalSpectrum.exists_forall_dvd_pow_of_finite_primes` above, at the
  product of a set of representatives of the prime associate classes, and
  `FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated`. Its
  `[UniqueFactorizationMonoid R]` is **needed** for the **forward** direction, by
  `FormalSpectrum.not_forall_hasBoundedDenominators_imp_finite_primes` in
  `FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`, which refutes that direction with the
  instance deleted; `FormalSpectrum.not_forall_hasBoundedDenominators_iff_finite_primes` beside it
  refutes the `↔` itself, and the backward direction with the instance deleted is refuted nowhere.
  The three values below are its empty, singleton and infinite cases. It is the only hypothesis
  under which anything **in this file** decides the condition; semilocal, Prüfer and valuation
  rings are untouched, and the Dedekind case is a separate theorem in a separate module, because it
  is a statement about ideals — `FormalSpectrum.hasBoundedDenominators_iff_finite_primeIdeals`
  (`FormalSchemes.StructureSheafStalkPowerSeriesDedekind`).
* `FormalSpectrum.hasBoundedDenominators_iff_exists_surjective`,
  `FormalSpectrum.hasBoundedDenominators_iff_exists_denominator`,
  `FormalSpectrum.hasBoundedDenominators_iff_forall_dvd_pow`,
  `FormalSpectrum.hasBoundedDenominators_iff_exists_isField`: **the collapse over a countable
  fraction field** — under `[Countable (FractionRing R)]` the condition holds **iff** a single
  `R[1/m]` is already the whole of `Frac R`, so the sufficient criterion above is necessary too.
  Four spellings, and what changes between them is which objects a consumer has to have in hand:
  a surjection onto `Frac R`; a range inside `Frac R`; **pure divisibility in `R`**, with no
  fraction field and no localization in the statement at all; and **`R[1/m]` being a field**, which
  is a property of that ring alone and is the most compact of the four. This hypothesis is
  incomparable with unique factorisation, and unlike the classification it **decides no ring**: it
  replaces the condition by a more elementary one and nothing here says which rings meet it.
* `FormalSpectrum.not_exists_surjective_awayToFractionRing_int`: **no single `ℤ[1/m]` is `ℚ`** —
  the whole refutation with the power series, the completions and the localizations of `ℤ⟦X⟧`
  stripped off. A corollary of `FormalSpectrum.not_hasBoundedDenominators_int`, needing no
  countability hypothesis, since that direction holds at every domain.
* `FormalSpectrum.not_exists_isField_localizationAway_int`: **and no single `ℤ[1/m]` is a field** —
  the same refutation with the map to `ℚ` stripped off as well, so that nothing but the rings
  `ℤ[1/m]` is named. Needs no countability either: it is the bullet above read through
  `FormalSpectrum.surjective_awayToFractionRing_iff_isField` at a fixed `m`.
* `FormalSpectrum.hasBoundedDenominators_of_field`: **a field satisfies it**, with `m = 1`. This
  is a value of the condition and not of `FormalSpectrum.IsStalkLimit`; the latter at a field is
  `FormalSpectrum.isStalkLimit_powerSeriesX_field`, by a different route.
* `FormalSpectrum.not_hasBoundedDenominators_int`: **`ℤ` does not**, which is the whole of the
  refutation with no formal geometry in it.
* `FormalSpectrum.hasBoundedDenominators_of_isDiscreteValuationRing`: **a discrete valuation ring
  does**, with a uniformizer as the denominator.
* `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`: **the
  predicate itself, at the generic point of `R⟦X⟧`, is exactly the denominator condition**, at
  every domain. The criterion's injectivity half holds there for every domain, so the conjunction
  collapses onto its surjectivity half.
* `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_finite_primes`: **and at a unique
  factorisation domain it is a cardinality** — the stalk of the completion is the completion of the
  stalk at that point exactly when `R` has finitely many primes up to associates.

Each of the field, `ℤ` and discrete-valuation-ring values above is checked a second time below, as
an anonymous `example` reading it off
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`. **None of the three proofs is
replaced**: each carries something the classification does not — the field value needs no
factorisation, the discrete-valuation-ring value exhibits the uniformizer, and
`FormalSpectrum.not_hasBoundedDenominators_int` exhibits an explicit family in `Frac ℤ` that
defeats every `m`.

The two values of the predicate are checked the same way, as anonymous `example`s reading them off
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators` rather than off
the classification, and neither of those proofs is replaced either.

Three further anonymous `example`s sit beside the collapse and are consistency checks of the same
kind: that the classification and the collapse agree at a domain satisfying both hypotheses, and
that the collapse's forward direction has a value, at a countable discrete valuation ring — which
also exhibits `Localization.countable_of_countable` discharging the hypothesis from
`[Countable R]` — read once as a surjection and once as
`IsField (Localization.Away m)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX).
-/

noncomputable section

universe u

open PowerSeries

/-! ### Bijectivity of a completed ring map, level by level -/

namespace AdicCompletion

variable {R S : Type u} [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}

/-- The continuity bound at every level that `I.map f ≤ J` already contains: `Ideal.map_pow` turns
the hypothesis into `(I ^ n).map f ≤ J ^ n`, which is the `Ideal.comap` form
`AdicCompletion.evalₐ_mapCompletion` and `Ideal.quotientMap` ask for. Stated separately because the
criterion below quantifies over the proof. -/
theorem pow_le_comap_of_map_le (f : R →+* S) (hf : I.map f ≤ J) (n : ℕ) :
    I ^ n ≤ (J ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono hf n

/-- **Congruence modulo the `n`-th filtration step of `R^` is equality of level-`n` evaluations.**
`FormalSpectrum`'s tower vocabulary is `AdicCompletion.evalₐ`; `IsPrecomplete.prec`'s is `SModEq`
for the module filtration `I ^ n • ⊤`. This is the translation, and it is
`AdicCompletion.ker_evalₐ` (`FormalSchemes.Completion`) together with
`AdicCompletion.mem_idealOfDefinition_pow_iff`, which is where the finite generation is spent. -/
theorem smodEq_iff_evalₐ_eq (hI : I.FG) (n : ℕ) (x y : AdicCompletion I R) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R (AdicCompletion I R))] ↔ evalₐ I n x = evalₐ I n y := by
  rw [SModEq.sub_mem, ← mem_idealOfDefinition_pow_iff, ← ker_evalₐ I hI n, RingHom.mem_ker]
  change evalₐ I n (x - y) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- **A criterion for `Ideal.quotientMap` to be bijective**, in the two element-level forms the
identifications below actually produce: every element of the target is congruent to something in
the image, and nothing outside `I` maps into `J`. Both directions of the quotient statement are
`Ideal.Quotient.mk_surjective` away from these. -/
theorem bijective_quotientMap_of (f : R →+* S) (hc : I ≤ J.comap f)
    (hsurj : ∀ t : S, ∃ r : R, t - f r ∈ J)
    (hinj : ∀ r : R, f r ∈ J → r ∈ I) :
    Function.Bijective (Ideal.quotientMap J f hc) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hinj r hz)
  · intro w
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨r, hr⟩ := hsurj t
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simpa [neg_sub] using (Ideal.neg_mem_iff J).mpr hr

/-- **The completion of a ring map that is bijective at every level is bijective.**

This is the tool the two identifications below need and that the tree did not have.
`AdicCompletion.bijective_mapCompletion`
(`FormalSchemes.StructureSheafStalkPowerSeries`) asks for a bijection of *rings*, which is far too
strong here: `R⟦X⟧[1/f] → R[1/m]⟦X⟧` is very far from bijective, and only becomes so after taking
quotients by the powers of `(X)`.

Injectivity is `AdicCompletion.ext_evalₐ` applied to `AdicCompletion.evalₐ_mapCompletion`.
Surjectivity chooses a level-`n` preimage for every `n`, checks the choices are Cauchy — that is
the `Ideal.Quotient.factorPow` square, which commutes because both maps are induced by `f` — and
takes the limit inside `R^` itself, which is complete by `AdicCompletion.isAdicComplete`. No
element of the source ring is constructed anywhere, which is exactly why the criterion applies to
a map with no reasonable inverse.

The hypothesis quantifies over the continuity bound rather than fixing one, so a caller may supply
whichever proof term is in hand. -/
theorem bijective_mapCompletion_of_bijective_quotientMap (f : R →+* S) (hf : I.map f ≤ J)
    (hI : I.FG) (hJ : J.FG)
    (hlev : ∀ (n : ℕ) (hc : I ^ n ≤ (J ^ n).comap f),
      Function.Bijective (Ideal.quotientMap (J ^ n) f hc)) :
    Function.Bijective (mapCompletion f hf hJ) := by
  have hc : ∀ n, I ^ n ≤ (J ^ n).comap f := pow_le_comap_of_map_le f hf
  have hsq : ∀ {m n : ℕ} (hmn : m ≤ n) (z : R ⧸ I ^ n),
      Ideal.Quotient.factorPow J hmn (Ideal.quotientMap (J ^ n) f (hc n) z) =
        Ideal.quotientMap (J ^ m) f (hc m) (Ideal.Quotient.factorPow I hmn z) := by
    intro m n hmn z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp [Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]
  constructor
  · intro x y hxy
    refine ext_evalₐ fun n => ?_
    have h := congrArg (evalₐ J n) hxy
    rw [evalₐ_mapCompletion f hf hJ hI n (hc n) x,
      evalₐ_mapCompletion f hf hJ hI n (hc n) y] at h
    exact (hlev n (hc n)).1 h
  · intro y
    choose c hcy using fun n => (hlev n (hc n)).2 (evalₐ J n y)
    choose a hay using fun n => surjective_evalₐ I n (c n)
    have hcompat : ∀ {m n : ℕ}, m ≤ n → evalₐ I m (a m) = evalₐ I m (a n) := by
      intro m n hmn
      refine (hlev m (hc m)).1 ?_
      have h1 : Ideal.quotientMap (J ^ m) f (hc m) (evalₐ I m (a n)) = evalₐ J m y := by
        rw [← factorPow_evalₐ I hmn (a n), ← hsq hmn, hay n, hcy n, factorPow_evalₐ]
      have h2 : Ideal.quotientMap (J ^ m) f (hc m) (evalₐ I m (a m)) = evalₐ J m y := by
        rw [hay m, hcy m]
      rw [h1, h2]
    obtain ⟨L, hL⟩ := (AdicCompletion.isAdicComplete hI).toIsPrecomplete.prec
      (f := a) (fun {m n} hmn => (smodEq_iff_evalₐ_eq hI m (a m) (a n)).mpr (hcompat hmn))
    refine ⟨L, ext_evalₐ fun n => ?_⟩
    rw [evalₐ_mapCompletion f hf hJ hI n (hc n) L,
      ← (smodEq_iff_evalₐ_eq hI n (a n) L).mp (hL n), hay n, hcy n]

/-- **A complete ring is its own completion**, in ring-map form: `algebraMap A (AdicCompletion K A)`
is bijective. This is `AdicCompletion.of_bijective` read through
`AdicCompletion.algebraMap_apply`, which is definitional at `S = A`. It is what turns the
bijectivity statements below into ring isomorphisms with `PowerSeries` itself, through Mathlib's
`IsAdicComplete (.span {X}) (PowerSeries R)` instance. -/
theorem bijective_algebraMap_of_isAdicComplete {A : Type u} [CommRing A] (K : Ideal A)
    [IsAdicComplete K A] : Function.Bijective (algebraMap A (AdicCompletion K A)) := by
  have h := AdicCompletion.of_bijective K A
  have hfun : ⇑(algebraMap A (AdicCompletion K A)) = ⇑(AdicCompletion.of K A) := rfl
  rw [hfun]
  exact h

end AdicCompletion

/-! ### `PowerSeries.map` on constant terms, and which series it hits -/

/-- `PowerSeries.constantCoeff` commutes with `PowerSeries.map`. Mathlib has this for
`MvPowerSeries` (`MvPowerSeries.constantCoeff_map`) and not for `PowerSeries`; it is
`PowerSeries.coeff_map` at `0`. -/
theorem PowerSeries.constantCoeff_map {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S)
    (φ : PowerSeries R) : constantCoeff (PowerSeries.map g φ) = g (constantCoeff φ) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply (PowerSeries.map g φ),
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- **A power series is hit by `PowerSeries.map g` exactly when each of its coefficients is hit by
`g`.** Both directions are `PowerSeries.coeff_map`: forwards read off a coefficient, backwards
choose a preimage in each degree and assemble them with `PowerSeries.mk`.

Mathlib's `PowerSeries.map_surjective` is the special case where `g` is surjective, so that every
coefficient qualifies and the choice is unconstrained. This is the form needed when `g` is *not*
surjective and the question is which series happen to be in the image, which is the question the
surjectivity half of `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff` turns into. -/
theorem PowerSeries.exists_map_eq_iff_forall_coeff_mem_range {R S : Type u} [CommRing R]
    [CommRing S] (g : R →+* S) (b : PowerSeries S) :
    (∃ φ, PowerSeries.map g φ = b) ↔ ∀ n, PowerSeries.coeff n b ∈ Set.range g := by
  constructor
  · rintro ⟨φ, rfl⟩ n
    exact ⟨PowerSeries.coeff n φ, (PowerSeries.coeff_map _ _ _).symm⟩
  · intro h
    choose c hc using h
    exact ⟨PowerSeries.mk c, PowerSeries.ext fun n => by
      rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hc]⟩

namespace FormalSpectrum

/-- `PowerSeries.map` carries `(X)` onto `(X)`. -/
theorem map_powerSeriesXIdeal_map {S T : Type u} [CommRing S] [CommRing T] (φ : S →+* T) :
    (powerSeriesXIdeal S).map (PowerSeries.map φ) = powerSeriesXIdeal T := by
  rw [Ideal.map_span, Set.image_singleton, PowerSeries.map_X]

/-! ### `R⟦X⟧{1/f}` is `R[1/m]⟦X⟧` -/

section Away

variable {R : Type u} [CommRing R] (f : PowerSeries R)

/-- The constant term of `f` is a unit in `R[1/m]`, `m` being that constant term. -/
theorem isUnit_algebraMap_awayConstantCoeff :
    IsUnit (algebraMap R (Localization.Away (constantCoeff f)) (constantCoeff f)) :=
  IsLocalization.map_units _ (⟨constantCoeff f, Submonoid.mem_powers _⟩ :
    Submonoid.powers (constantCoeff f))

/-- **A power series with the same constant term as `f` is a unit of `R[1/m]⟦X⟧`.** A power series
over any commutative ring is a unit exactly when its constant term is
(`PowerSeries.isUnit_iff_constantCoeff`), and `m` is inverted in `R[1/m]` by construction.

This is the whole reason `FormalSpectrum.awayToPowerSeriesAway` exists. Note that **`f` need not be
a unit of `R⟦X⟧[1/m]`**: over `ℤ` with `f = 2 + X` the inverse is `∑ (-1) ^ n X ^ n / 2 ^ (n + 1)`,
whose denominators are unbounded, so it lies in `ℤ[1/2]⟦X⟧` and in no localization of `ℤ⟦X⟧`. The
two rings `Localization.Away f` and `Localization.Away (PowerSeries.C m)` are genuinely different;
they agree only after quotienting by a power of `(X)`. -/
theorem isUnit_map_awayConstantCoeff (g : PowerSeries R)
    (hg : constantCoeff g = constantCoeff f) :
    IsUnit (PowerSeries.map (algebraMap R (Localization.Away (constantCoeff f))) g) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_map, hg]
  exact isUnit_algebraMap_awayConstantCoeff f

/-- **The comparison `R⟦X⟧[1/f] →+* R[1/m]⟦X⟧`**, `m` the constant term of `f`, obtained from the
universal property of the localization away from `f` at
`FormalSpectrum.isUnit_map_awayConstantCoeff`. Its completion is an isomorphism
(`FormalSpectrum.awayCompletionEquivPowerSeriesAway`); it is very far from being one itself. -/
def awayToPowerSeriesAway :
    Localization.Away f →+* PowerSeries (Localization.Away (constantCoeff f)) :=
  IsLocalization.Away.lift f (isUnit_map_awayConstantCoeff f f rfl)

/-- `FormalSpectrum.awayToPowerSeriesAway` is a map under `R⟦X⟧`, and on `R⟦X⟧` it is
`PowerSeries.map` of the localization map. -/
theorem awayToPowerSeriesAway_algebraMap (g : PowerSeries R) :
    awayToPowerSeriesAway f (algebraMap (PowerSeries R) (Localization.Away f) g) =
      PowerSeries.map (algebraMap R (Localization.Away (constantCoeff f))) g :=
  IsLocalization.Away.lift_eq f (isUnit_map_awayConstantCoeff f f rfl) g

/-- **The comparison `R⟦X⟧[1/C m] →+* R[1/m]⟦X⟧`.** The source is a *different* ring from
`Localization.Away f` — see `FormalSpectrum.isUnit_map_awayConstantCoeff` — and it is the one in
which `PowerSeries.C m` is invertible outright, which is what makes the surjectivity induction
below go through. -/
def awayConstToPowerSeriesAway :
    Localization.Away (PowerSeries.C (constantCoeff f)) →+*
      PowerSeries (Localization.Away (constantCoeff f)) :=
  IsLocalization.Away.lift (PowerSeries.C (constantCoeff f))
    (isUnit_map_awayConstantCoeff f _ (by simp))

/-- `FormalSpectrum.awayConstToPowerSeriesAway` is a map under `R⟦X⟧` too, with the same value on
`R⟦X⟧` as `FormalSpectrum.awayToPowerSeriesAway`. -/
theorem awayConstToPowerSeriesAway_algebraMap (g : PowerSeries R) :
    awayConstToPowerSeriesAway f
        (algebraMap (PowerSeries R) (Localization.Away (PowerSeries.C (constantCoeff f))) g) =
      PowerSeries.map (algebraMap R (Localization.Away (constantCoeff f))) g :=
  IsLocalization.Away.lift_eq _ (isUnit_map_awayConstantCoeff f _ (by simp)) g

/-- **`FormalSpectrum.awayToPowerSeriesAway` carries the ideal of definition onto the ideal of
definition**: the extension of `(X)` to `R⟦X⟧[1/f]` maps onto `(X) ⊆ R[1/m]⟦X⟧`. An equality, not
merely a containment, because both are `Ideal.map` of `(X)` along a map under `R⟦X⟧` and `X` is
sent to `X`. This is what `AdicCompletion.mapCompletion` consumes. -/
theorem map_awayToPowerSeriesAway :
    ((powerSeriesXIdeal R).map (algebraMap (PowerSeries R) (Localization.Away f))).map
        (awayToPowerSeriesAway f) =
      powerSeriesXIdeal (Localization.Away (constantCoeff f)) := by
  rw [Ideal.map_map, Ideal.map_span, Set.image_singleton]
  congr 1
  rw [RingHom.comp_apply, awayToPowerSeriesAway_algebraMap, PowerSeries.map_X]

/-- The image of the `n`-th power of the ideal of definition is inside the `n`-th power of the ideal
of definition, which is `FormalSpectrum.map_awayToPowerSeriesAway` and `Ideal.map_pow`. -/
theorem awayToPowerSeriesAway_mem_pow (n : ℕ) (x : Localization.Away f)
    (hx : x ∈ ((powerSeriesXIdeal R).map
      (algebraMap (PowerSeries R) (Localization.Away f))) ^ n) :
    awayToPowerSeriesAway f x ∈
      powerSeriesXIdeal (Localization.Away (constantCoeff f)) ^ n := by
  have h := Ideal.mem_map_of_mem (awayToPowerSeriesAway f) hx
  rwa [Ideal.map_pow, map_awayToPowerSeriesAway] at h

/-- An element of `(X) ^ n ⊆ R⟦X⟧` has its image in the `n`-th power of the extended ideal. -/
theorem algebraMap_mem_map_pow (n : ℕ) (x : PowerSeries R)
    (hx : x ∈ powerSeriesXIdeal R ^ n) :
    algebraMap (PowerSeries R) (Localization.Away f) x ∈
      ((powerSeriesXIdeal R).map (algebraMap (PowerSeries R) (Localization.Away f))) ^ n := by
  have h := Ideal.mem_map_of_mem (algebraMap (PowerSeries R) (Localization.Away f)) hx
  rwa [Ideal.map_pow] at h

/-- **The constant term of `f` becomes a unit in `R⟦X⟧[1/f] ⧸ (X) ^ n`**, though not in
`R⟦X⟧[1/f]` itself.

This single fact is what makes both halves of the level identification work. `PowerSeries.C m - f`
has zero constant term, so it lies in `(X)`, so its image is nilpotent in the quotient; `f` itself
is a unit of `R⟦X⟧[1/f]`; and a unit plus a nilpotent is a unit
(`IsNilpotent.isUnit_add_left_of_commute`).

Concretely at `R = ℤ`, `f = 2 + X`: the element `2` is **not** invertible in `ℤ⟦X⟧[1/(2 + X)]` —
compare top coefficients in `2a = (2 + X) ^ k` — but it is invertible modulo every power of
`(X)`. -/
theorem isUnit_mk_algebraMap_C_constantCoeff (n : ℕ) :
    IsUnit (Ideal.Quotient.mk (((powerSeriesXIdeal R).map
          (algebraMap (PowerSeries R) (Localization.Away f))) ^ n)
      (algebraMap (PowerSeries R) (Localization.Away f) (PowerSeries.C (constantCoeff f)))) := by
  have hmem : PowerSeries.C (constantCoeff f) - f ∈ powerSeriesXIdeal R := by
    rw [powerSeriesXIdeal, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simp
  have hnil : IsNilpotent (Ideal.Quotient.mk (((powerSeriesXIdeal R).map
      (algebraMap (PowerSeries R) (Localization.Away f))) ^ n)
      (algebraMap (PowerSeries R) (Localization.Away f)
        (PowerSeries.C (constantCoeff f) - f))) := by
    refine ⟨n, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow
      (Ideal.mem_map_of_mem (algebraMap (PowerSeries R) (Localization.Away f)) hmem) n
  have hunit : IsUnit (Ideal.Quotient.mk (((powerSeriesXIdeal R).map
      (algebraMap (PowerSeries R) (Localization.Away f))) ^ n)
      (algebraMap (PowerSeries R) (Localization.Away f) f)) :=
    IsUnit.map (Ideal.Quotient.mk _)
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f)
  have hsum : (algebraMap (PowerSeries R) (Localization.Away f))
        (PowerSeries.C (constantCoeff f)) =
      (algebraMap (PowerSeries R) (Localization.Away f)) f +
      (algebraMap (PowerSeries R) (Localization.Away f))
        (PowerSeries.C (constantCoeff f) - f) := by
    rw [← map_add]; ring_nf
  rw [hsum, map_add]
  exact hnil.isUnit_add_left_of_commute hunit (Commute.all _ _)

/-- **`R⟦X⟧[1/C m] → R[1/m]⟦X⟧ ⧸ (X) ^ n` is surjective**, by induction on `n`: given an
approximation modulo `X ^ n`, the error is `X ^ n * u`, and the constant term of `u` is
`r / m ^ k` for some `r` and `k`, so `(C r * X ^ n) / (C m) ^ k` improves the approximation to
`X ^ (n + 1)`. The source is the localization at `PowerSeries.C m` precisely so that this
denominator is available in the ring. -/
theorem exists_sub_awayConstToPowerSeriesAway_mem (n : ℕ)
    (t : PowerSeries (Localization.Away (constantCoeff f))) :
    ∃ z : Localization.Away (PowerSeries.C (constantCoeff f)),
      t - awayConstToPowerSeriesAway f z ∈
        powerSeriesXIdeal (Localization.Away (constantCoeff f)) ^ n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    rw [show (powerSeriesXIdeal (Localization.Away (constantCoeff f)) ^ n) =
        Ideal.span {(X : PowerSeries (Localization.Away (constantCoeff f))) ^ n} from
        Ideal.span_singleton_pow _ _, Ideal.mem_span_singleton] at hz
    obtain ⟨u, hu⟩ := hz
    obtain ⟨⟨r, d⟩, hrd⟩ := IsLocalization.mk'_surjective
      (Submonoid.powers (constantCoeff f)) (constantCoeff u)
    obtain ⟨k, hk⟩ := d.2
    have hspec : algebraMap R (Localization.Away (constantCoeff f)) (d : R) * constantCoeff u =
        algebraMap R (Localization.Away (constantCoeff f)) r := by
      rw [← hrd]; exact IsLocalization.mk'_spec' _ r d
    set y : Submonoid.powers (PowerSeries.C (constantCoeff f)) :=
      ⟨PowerSeries.C (constantCoeff f) ^ k, ⟨k, rfl⟩⟩ with hy
    refine ⟨z + IsLocalization.mk' _ (PowerSeries.C r * (X : PowerSeries R) ^ n) y, ?_⟩
    have hyval : (y : PowerSeries R) = PowerSeries.C (constantCoeff f) ^ k := rfl
    have hunit : IsUnit (PowerSeries.map
        (algebraMap R (Localization.Away (constantCoeff f))) (y : PowerSeries R)) := by
      rw [hyval, map_pow]
      exact (isUnit_map_awayConstantCoeff f _ (by simp)).pow k
    have hkey : awayConstToPowerSeriesAway f (IsLocalization.mk' _
        (PowerSeries.C r * (X : PowerSeries R) ^ n) y) =
        (X : PowerSeries (Localization.Away (constantCoeff f))) ^ n *
          PowerSeries.C (constantCoeff u) := by
      refine hunit.mul_left_cancel ?_
      have h1 : PowerSeries.map (algebraMap R (Localization.Away (constantCoeff f)))
            (y : PowerSeries R) *
          awayConstToPowerSeriesAway f (IsLocalization.mk' _
            (PowerSeries.C r * (X : PowerSeries R) ^ n) y) =
          PowerSeries.map (algebraMap R (Localization.Away (constantCoeff f)))
            (PowerSeries.C r * (X : PowerSeries R) ^ n) := by
        rw [← awayConstToPowerSeriesAway_algebraMap f (y : PowerSeries R), ← map_mul,
          IsLocalization.mk'_spec', awayConstToPowerSeriesAway_algebraMap]
      have hdk : (constantCoeff f) ^ k = (d : R) := hk
      have h2 : PowerSeries.map (algebraMap R (Localization.Away (constantCoeff f)))
          (y : PowerSeries R) =
          PowerSeries.C (algebraMap R (Localization.Away (constantCoeff f)) (d : R)) := by
        rw [hyval, map_pow, PowerSeries.map_C, ← hdk, map_pow, map_pow]
      rw [h1, h2, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, ← hspec, map_mul]
      ring
    rw [map_add, hkey]
    rw [show (powerSeriesXIdeal (Localization.Away (constantCoeff f)) ^ (n + 1)) =
        Ideal.span {(X : PowerSeries (Localization.Away (constantCoeff f))) ^ (n + 1)} from
        Ideal.span_singleton_pow _ _, Ideal.mem_span_singleton]
    have hdvd : (X : PowerSeries (Localization.Away (constantCoeff f))) ∣
        (u - PowerSeries.C (constantCoeff u)) := by
      rw [PowerSeries.X_dvd_iff]; simp
    obtain ⟨w, hw⟩ := hdvd
    refine ⟨w, ?_⟩
    have hrw : t - (awayConstToPowerSeriesAway f z +
        (X : PowerSeries (Localization.Away (constantCoeff f))) ^ n *
          PowerSeries.C (constantCoeff u)) =
        (X : PowerSeries (Localization.Away (constantCoeff f))) ^ n *
          (u - PowerSeries.C (constantCoeff u)) := by
      rw [mul_sub, ← hu]; ring
    rw [hrw, hw]; ring

/-- **`R⟦X⟧[1/f] → R[1/m]⟦X⟧ ⧸ (X) ^ n` is surjective.** The previous lemma does it for
`R⟦X⟧[1/C m]`, whose denominators `(C m) ^ k` are not available in `R⟦X⟧[1/f]`; they are available
*modulo `(X) ^ n`* by `FormalSpectrum.isUnit_mk_algebraMap_C_constantCoeff`, and this transfers the
statement across by replacing each `(C m) ^ (-k)` by the `k`-th power of an approximate inverse.
All the arithmetic happens in `R[1/m]⟦X⟧ ⧸ (X) ^ n`, where the approximate inverse is an
inverse. -/
theorem exists_sub_awayToPowerSeriesAway_mem (n : ℕ)
    (t : PowerSeries (Localization.Away (constantCoeff f))) :
    ∃ s : Localization.Away f, t - awayToPowerSeriesAway f s ∈
      powerSeriesXIdeal (Localization.Away (constantCoeff f)) ^ n := by
  obtain ⟨z, hz⟩ := exists_sub_awayConstToPowerSeriesAway_mem f n t
  obtain ⟨⟨a, y⟩, hy⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (PowerSeries.C (constantCoeff f))) z
  obtain ⟨k, hk⟩ := y.2
  obtain ⟨u, hu⟩ := isUnit_mk_algebraMap_C_constantCoeff f n
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (I := ((powerSeriesXIdeal R).map
    (algebraMap (PowerSeries R) (Localization.Away f))) ^ n) (↑u⁻¹)
  refine ⟨algebraMap (PowerSeries R) (Localization.Away f) a * w ^ k, ?_⟩
  -- the approximate inverse of `C m` in `R⟦X⟧[1/f]`
  have hinv : algebraMap (PowerSeries R) (Localization.Away f)
        (PowerSeries.C (constantCoeff f)) * w - 1 ∈ ((powerSeriesXIdeal R).map
      (algebraMap (PowerSeries R) (Localization.Away f))) ^ n := by
    rw [← Ideal.Quotient.eq, map_mul, map_one, hw, ← hu, Units.mul_inv]
  have hPw : awayToPowerSeriesAway f (algebraMap (PowerSeries R) (Localization.Away f)
        (PowerSeries.C (constantCoeff f))) * awayToPowerSeriesAway f w - 1 ∈
      powerSeriesXIdeal (Localization.Away (constantCoeff f)) ^ n := by
    have h := awayToPowerSeriesAway_mem_pow f n _ hinv
    rwa [map_sub, map_mul, map_one] at h
  set P : PowerSeries (Localization.Away (constantCoeff f)) :=
    PowerSeries.map (algebraMap R (Localization.Away (constantCoeff f)))
      (PowerSeries.C (constantCoeff f)) with hP
  set K : Ideal (PowerSeries (Localization.Away (constantCoeff f))) :=
    powerSeriesXIdeal (Localization.Away (constantCoeff f)) ^ n with hK
  have hPeq : awayToPowerSeriesAway f (algebraMap (PowerSeries R) (Localization.Away f)
      (PowerSeries.C (constantCoeff f))) = P := awayToPowerSeriesAway_algebraMap f _
  have h1 : Ideal.Quotient.mk K P *
      Ideal.Quotient.mk K (awayToPowerSeriesAway f w) = 1 := by
    have h := (Ideal.Quotient.eq (I := K)).mpr hPw
    rwa [map_mul, map_one, hPeq] at h
  have hunitP : IsUnit (Ideal.Quotient.mk K P) :=
    ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hyval : (y : PowerSeries R) = PowerSeries.C (constantCoeff f) ^ k := hk.symm
  have h2 : P ^ k * awayConstToPowerSeriesAway f z =
      PowerSeries.map (algebraMap R (Localization.Away (constantCoeff f))) a := by
    have hspec := IsLocalization.mk'_spec'
      (Localization.Away (PowerSeries.C (constantCoeff f))) a y
    rw [show IsLocalization.mk' (Localization.Away (PowerSeries.C (constantCoeff f))) a y = z
      from hy] at hspec
    have h := congrArg (awayConstToPowerSeriesAway f) hspec
    rwa [map_mul, awayConstToPowerSeriesAway_algebraMap,
      awayConstToPowerSeriesAway_algebraMap, hyval, map_pow] at h
  rw [← Ideal.Quotient.eq (I := K)]
  refine (hunitP.pow k).mul_left_cancel ?_
  rw [(Ideal.Quotient.eq (I := K)).mpr hz, ← map_pow, ← map_mul, h2, map_mul,
    awayToPowerSeriesAway_algebraMap, map_mul, map_pow, ← mul_assoc,
    mul_comm (Ideal.Quotient.mk K P ^ k), mul_assoc]
  rw [show (Ideal.Quotient.mk K) ((awayToPowerSeriesAway f) (w ^ k)) =
      (Ideal.Quotient.mk K) ((awayToPowerSeriesAway f) w) ^ k from by rw [map_pow, map_pow],
    ← mul_pow, h1, one_pow, mul_one]

/-- **If the first `n` coefficients of `a` die in `R[1/m]`, then `X ^ n` divides `C m ^ k * a` for
some single `k`.**

The point is the uniformity of `k`: each coefficient separately is killed by *some* power of `m`,
and the induction takes one new power per coefficient rather than a maximum over
`Finset.range n`. The step reads the `n`-th coefficient of `C m ^ k * a = X ^ n * c` as the
constant term of `c` (`PowerSeries.coeff_X_pow_mul`), kills it with one further power of `m`
(`IsLocalization.map_eq_zero_iff`), and gains one factor of `X` from
`PowerSeries.X_dvd_iff`. -/
theorem exists_pow_C_mul_X_pow_dvd (a : PowerSeries R) (n : ℕ)
    (ha : ∀ i < n, algebraMap R (Localization.Away (constantCoeff f)) (coeff i a) = 0) :
    ∃ k : ℕ, (X : PowerSeries R) ^ n ∣ PowerSeries.C (constantCoeff f) ^ k * a := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨k, c, hc⟩ := ih fun i hi => ha i (Nat.lt_succ_of_lt hi)
    have hcoeff : algebraMap R (Localization.Away (constantCoeff f)) (coeff 0 c) = 0 := by
      have h1 : coeff n (PowerSeries.C (constantCoeff f) ^ k * a) = coeff 0 c := by
        rw [hc]; simpa using PowerSeries.coeff_X_pow_mul c n 0
      have h2 : coeff n (PowerSeries.C (constantCoeff f) ^ k * a) =
          constantCoeff f ^ k * coeff n a := by
        rw [← map_pow, PowerSeries.coeff_C_mul]
      rw [← h1, h2, map_mul, ha n (Nat.lt_succ_self n), mul_zero]
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (constantCoeff f)) _ _).mp hcoeff
    obtain ⟨k', hk'⟩ := t.2
    refine ⟨k + k', ?_⟩
    have hdvd : (X : PowerSeries R) ∣ PowerSeries.C (constantCoeff f) ^ k' * c := by
      rw [PowerSeries.X_dvd_iff, ← map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simpa [hk'] using ht
    obtain ⟨w, hw⟩ := hdvd
    refine ⟨w, ?_⟩
    calc PowerSeries.C (constantCoeff f) ^ (k + k') * a
        = PowerSeries.C (constantCoeff f) ^ k' *
          (PowerSeries.C (constantCoeff f) ^ k * a) := by ring
      _ = (X : PowerSeries R) ^ n * (PowerSeries.C (constantCoeff f) ^ k' * c) := by
          rw [hc]; ring
      _ = (X : PowerSeries R) ^ (n + 1) * w := by rw [hw]; ring

/-- **`R⟦X⟧[1/f] → R[1/m]⟦X⟧ ⧸ (X) ^ n` is injective.** Writing the element as `a / f ^ j` and
using that `f` is a unit, the hypothesis says the first `n` coefficients of `a` die in `R[1/m]`;
`FormalSpectrum.exists_pow_C_mul_X_pow_dvd` then puts `C m ^ k * a` into `(X) ^ n`, and
`FormalSpectrum.isUnit_mk_algebraMap_C_constantCoeff` cancels the `C m ^ k` in the quotient. -/
theorem mem_pow_of_awayToPowerSeriesAway_mem (n : ℕ) (s : Localization.Away f)
    (hs : awayToPowerSeriesAway f s ∈
      powerSeriesXIdeal (Localization.Away (constantCoeff f)) ^ n) :
    s ∈ ((powerSeriesXIdeal R).map
      (algebraMap (PowerSeries R) (Localization.Away f))) ^ n := by
  obtain ⟨⟨a, y⟩, hy⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) s
  have hspec : algebraMap (PowerSeries R) (Localization.Away f) (y : PowerSeries R) * s =
      algebraMap (PowerSeries R) (Localization.Away f) a := by
    rw [← show IsLocalization.mk' (Localization.Away f) a y = s from hy]
    exact IsLocalization.mk'_spec' _ a y
  have hmapa : PowerSeries.map (algebraMap R (Localization.Away (constantCoeff f))) a ∈
      powerSeriesXIdeal (Localization.Away (constantCoeff f)) ^ n := by
    rw [← awayToPowerSeriesAway_algebraMap f a, ← hspec, map_mul]
    exact Ideal.mul_mem_left _ _ hs
  have hcoeff : ∀ i < n,
      algebraMap R (Localization.Away (constantCoeff f)) (coeff i a) = 0 := by
    rw [show (powerSeriesXIdeal (Localization.Away (constantCoeff f)) ^ n) =
        Ideal.span {(X : PowerSeries (Localization.Away (constantCoeff f))) ^ n} from
        Ideal.span_singleton_pow _ _, Ideal.mem_span_singleton,
      PowerSeries.X_pow_dvd_iff] at hmapa
    intro i hi
    have h := hmapa i hi
    rwa [PowerSeries.coeff_map] at h
  obtain ⟨k, c, hc⟩ := exists_pow_C_mul_X_pow_dvd f a n hcoeff
  obtain ⟨u, hu⟩ := isUnit_mk_algebraMap_C_constantCoeff f n
  have hmem : algebraMap (PowerSeries R) (Localization.Away f)
      (PowerSeries.C (constantCoeff f) ^ k * a) ∈ ((powerSeriesXIdeal R).map
        (algebraMap (PowerSeries R) (Localization.Away f))) ^ n := by
    refine algebraMap_mem_map_pow f n _ ?_
    rw [hc, show (powerSeriesXIdeal R ^ n) = Ideal.span {(X : PowerSeries R) ^ n} from
      Ideal.span_singleton_pow _ _, Ideal.mem_span_singleton]
    exact ⟨c, rfl⟩
  have hzero : Ideal.Quotient.mk (((powerSeriesXIdeal R).map
      (algebraMap (PowerSeries R) (Localization.Away f))) ^ n)
      (algebraMap (PowerSeries R) (Localization.Away f) a) = 0 := by
    have h0 : Ideal.Quotient.mk (((powerSeriesXIdeal R).map
        (algebraMap (PowerSeries R) (Localization.Away f))) ^ n)
        (algebraMap (PowerSeries R) (Localization.Away f)
          (PowerSeries.C (constantCoeff f) ^ k * a)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [map_mul, map_mul, map_pow, map_pow, ← hu] at h0
    exact (IsUnit.mul_right_eq_zero (u ^ k).isUnit).mp (by simpa using h0)
  have hain : algebraMap (PowerSeries R) (Localization.Away f) a ∈
      ((powerSeriesXIdeal R).map
        (algebraMap (PowerSeries R) (Localization.Away f))) ^ n :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  obtain ⟨v, hv⟩ := IsLocalization.map_units (Localization.Away f) y
  have hsv : s = ↑v⁻¹ * algebraMap (PowerSeries R) (Localization.Away f) a := by
    rw [← hspec, ← hv, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hsv]
  exact Ideal.mul_mem_left _ _ hain

/-- The completion of `FormalSpectrum.awayToPowerSeriesAway` is bijective: the levelwise criterion
`AdicCompletion.bijective_mapCompletion_of_bijective_quotientMap` at the two previous lemmas. -/
theorem bijective_mapCompletion_awayToPowerSeriesAway :
    Function.Bijective (AdicCompletion.mapCompletion (awayToPowerSeriesAway f)
      (map_awayToPowerSeriesAway f).le (fg_powerSeriesXIdeal _)) := by
  refine AdicCompletion.bijective_mapCompletion_of_bijective_quotientMap _ _
    ((fg_powerSeriesXIdeal R).map _) (fg_powerSeriesXIdeal _) fun n hc => ?_
  refine AdicCompletion.bijective_quotientMap_of _ hc
    (fun t => exists_sub_awayToPowerSeriesAway_mem f n t)
    (fun s hs => mem_pow_of_awayToPowerSeriesAway_mem f n s hs)

/-- **`R⟦X⟧{1/f} ≃+* R[1/m]⟦X⟧`, `m` the constant term of `f`** — the first of the two ring
identifications the `ℤ⟦X⟧` counterexample needs, at every commutative ring and with no hypothesis
on `f` at all.

`FormalSpectrum.awayCompletion (X) f` is by definition the `(X)`-adic completion of
`R⟦X⟧[1/f]`, so this says: completing the localization `X`-adically both inverts the constant term
of `f` and restores the unbounded denominators that `R⟦X⟧[1/f]` does not contain. Over `ℤ` with
`f = C m` this is `ℤ[1/m]⟦X⟧`, and it is strictly bigger than `ℤ⟦X⟧[1/m]`.

It is `AdicCompletion.mapCompletion` of `FormalSpectrum.awayToPowerSeriesAway`, bijective by the
levelwise criterion, composed with the inverse of `algebraMap` into the completion of
`R[1/m]⟦X⟧` — bijective because `R[1/m]⟦X⟧` is `(X)`-adically complete, which is Mathlib's
`IsAdicComplete (.span {X}) (PowerSeries R)`. -/
def awayCompletionEquivPowerSeriesAway :
    awayCompletion (powerSeriesXIdeal R) f ≃+*
      PowerSeries (Localization.Away (constantCoeff f)) :=
  (RingEquiv.ofBijective _ (bijective_mapCompletion_awayToPowerSeriesAway f)).trans
    (RingEquiv.ofBijective _
      (AdicCompletion.bijective_algebraMap_of_isAdicComplete
        (powerSeriesXIdeal (Localization.Away (constantCoeff f))))).symm

/-- `FormalSpectrum.awayCompletionEquivPowerSeriesAway` read as an equation between ring maps into
the completion of `R[1/m]⟦X⟧`, which is the form the compatibility square below consumes. -/
theorem algebraMap_awayCompletionEquivPowerSeriesAway (a : awayCompletion (powerSeriesXIdeal R) f) :
    algebraMap (PowerSeries (Localization.Away (constantCoeff f)))
        (AdicCompletion (powerSeriesXIdeal (Localization.Away (constantCoeff f)))
          (PowerSeries (Localization.Away (constantCoeff f))))
        (awayCompletionEquivPowerSeriesAway f a) =
      AdicCompletion.mapCompletion (awayToPowerSeriesAway f)
        (map_awayToPowerSeriesAway f).le (fg_powerSeriesXIdeal _) a :=
  (RingEquiv.ofBijective _ (AdicCompletion.bijective_algebraMap_of_isAdicComplete
    (powerSeriesXIdeal (Localization.Away (constantCoeff f))))).apply_symm_apply _

end Away

/-! ### The target at the generic point is `(Frac R)⟦X⟧` -/

section Generic

variable (R : Type u) [CommRing R] [IsDomain R]

/-- Being outside the prime under the generic point is having a nonzero constant term — the
complement form of `FormalSpectrum.mem_basicOpen_powerSeriesXGenericPoint_iff`, used to feed the
prime complement into `IsLocalization.lift`. -/
theorem notMem_pointPrime_powerSeriesXGenericPoint_iff (g : PowerSeries R) :
    g ∉ pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) ↔ constantCoeff g ≠ 0 := by
  rw [pointPrime_powerSeriesXGenericPoint, powerSeriesXIdeal_eq_ker, RingHom.mem_ker]

/-- **A power series with nonzero constant term becomes a unit of `K⟦X⟧`, `K = Frac R`.** Over a
domain the constant term stays nonzero in the fraction field, where it is invertible. Unlike the
`Localization.Away` case there is no nilpotence and no approximation here: this is why the target
at the generic point is the easier of the two identifications. -/
theorem isUnit_map_fractionRing (g : PowerSeries R) (hg : constantCoeff g ≠ 0) :
    IsUnit (PowerSeries.map (algebraMap R (FractionRing R)) g) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  refine isUnit_iff_ne_zero.mpr fun h => hg ?_
  exact (map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mp h

/-- **The comparison `R⟦X⟧_{(X)} →+* K⟦X⟧`, `K = Frac R`**, from the universal property of the
localization at the prime complement. `FormalSpectrum.pointPrime_powerSeriesXGenericPoint` says
the prime under the generic point is `(X)` itself, so the source is exactly the ring whose
completion is the target of the stalk comparison there. -/
def atPrimeToFractionPowerSeries :
    Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)) →+*
      PowerSeries (FractionRing R) :=
  IsLocalization.lift (M := (pointPrime (powerSeriesXIdeal R)
      (powerSeriesXGenericPoint R)).primeCompl)
    (g := PowerSeries.map (algebraMap R (FractionRing R)))
    (fun y => isUnit_map_fractionRing R y.1
      ((notMem_pointPrime_powerSeriesXGenericPoint_iff R y.1).mp y.2))

/-- `FormalSpectrum.atPrimeToFractionPowerSeries` is a map under `R⟦X⟧`. -/
theorem atPrimeToFractionPowerSeries_algebraMap (g : PowerSeries R) :
    atPrimeToFractionPowerSeries R (algebraMap (PowerSeries R) _ g) =
      PowerSeries.map (algebraMap R (FractionRing R)) g :=
  IsLocalization.lift_eq _ g

/-- The powers of the ideal of definition of the stalk's local ring are the principal ideals
generated by the powers of `X`. -/
theorem pointIdeal_powerSeriesXGenericPoint_pow_eq_span (n : ℕ) :
    pointIdeal (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) ^ n =
      Ideal.span {algebraMap (PowerSeries R)
        (Localization.AtPrime (pointPrime (powerSeriesXIdeal R)
          (powerSeriesXGenericPoint R))) ((X : PowerSeries R) ^ n)} := by
  rw [pointIdeal, Ideal.map_span, Set.image_singleton, map_pow, Ideal.span_singleton_pow]

/-- `FormalSpectrum.atPrimeToFractionPowerSeries` carries the ideal of definition onto `(X) ⊆
K⟦X⟧`; an equality, for the same reason as in the `Localization.Away` case. -/
theorem map_pointIdeal_atPrimeToFractionPowerSeries :
    (pointIdeal (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)).map
        (atPrimeToFractionPowerSeries R) = powerSeriesXIdeal (FractionRing R) := by
  rw [pointIdeal, Ideal.map_map, Ideal.map_span, Set.image_singleton]
  congr 1
  rw [RingHom.comp_apply, atPrimeToFractionPowerSeries_algebraMap, PowerSeries.map_X]

/-- **`R⟦X⟧_{(X)} → K⟦X⟧ ⧸ (X) ^ n` is injective.** Writing the element as `a / d` with `d` outside
`(X)`, the hypothesis says the first `n` coefficients of `a` vanish in `K`, hence in `R`, since
`R` is a domain; so `X ^ n` divides `a` already in `R⟦X⟧`. No denominators have to be cleared,
which is what distinguishes this from the `Localization.Away` case. -/
theorem mem_pointIdeal_pow_of_map_mem (n : ℕ)
    (s : Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)))
    (hs : atPrimeToFractionPowerSeries R s ∈ powerSeriesXIdeal (FractionRing R) ^ n) :
    s ∈ pointIdeal (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) ^ n := by
  obtain ⟨⟨a, y⟩, hy⟩ := IsLocalization.mk'_surjective
    (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)).primeCompl s
  have hspec : algebraMap (PowerSeries R) _ y.1 * s = algebraMap (PowerSeries R) _ a := by
    rw [← hy]; exact IsLocalization.mk'_spec' _ a y
  have h1 : PowerSeries.map (algebraMap R (FractionRing R)) a ∈
      powerSeriesXIdeal (FractionRing R) ^ n := by
    rw [← atPrimeToFractionPowerSeries_algebraMap, ← hspec, map_mul]
    exact Ideal.mul_mem_left _ _ hs
  rw [show (powerSeriesXIdeal (FractionRing R) ^ n) =
      Ideal.span {(X : PowerSeries (FractionRing R)) ^ n} from Ideal.span_singleton_pow _ _,
    Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at h1
  have h2 : (X : PowerSeries R) ^ n ∣ a := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    have := h1 m hm
    rw [PowerSeries.coeff_map] at this
    exact (map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mp this
  obtain ⟨b, hb⟩ := h2
  obtain ⟨u, hu⟩ := IsLocalization.map_units
    (Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R))) y
  have hs' : s = ↑u⁻¹ * algebraMap (PowerSeries R) _ a := by
    rw [← hspec, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hs', pointIdeal_powerSeriesXGenericPoint_pow_eq_span]
  refine Ideal.mul_mem_left _ _ ?_
  rw [hb, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- **`R⟦X⟧_{(X)} → K⟦X⟧ ⧸ (X) ^ n` is surjective**, by the same induction as in the
`Localization.Away` case
and with the same shape: the error is `X ^ n * u`, the constant term of `u` is `r / d` with
`d ≠ 0`, and `PowerSeries.C d` is outside `(X)`, hence already invertible in the source. -/
theorem exists_sub_atPrimeToFractionPowerSeries_mem (n : ℕ) (t : PowerSeries (FractionRing R)) :
    ∃ s : Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)),
      t - atPrimeToFractionPowerSeries R s ∈ powerSeriesXIdeal (FractionRing R) ^ n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    rw [show (powerSeriesXIdeal (FractionRing R) ^ n) =
        Ideal.span {(X : PowerSeries (FractionRing R)) ^ n} from Ideal.span_singleton_pow _ _,
      Ideal.mem_span_singleton] at hs
    obtain ⟨u, hu⟩ := hs
    obtain ⟨⟨r, d⟩, hrd⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R)
      (constantCoeff (R := FractionRing R) u)
    have hd0 : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.2
    have hy : (PowerSeries.C (d : R)) ∈
        (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)).primeCompl := by
      exact (notMem_pointPrime_powerSeriesXGenericPoint_iff R _).mpr (by simp [hd0])
    refine ⟨s + IsLocalization.mk' _ (PowerSeries.C r * (X : PowerSeries R) ^ n)
      ⟨PowerSeries.C (d : R), hy⟩, ?_⟩
    have hkey : atPrimeToFractionPowerSeries R (IsLocalization.mk' _
        (PowerSeries.C r * (X : PowerSeries R) ^ n) ⟨PowerSeries.C (d : R), hy⟩) =
        (X : PowerSeries (FractionRing R)) ^ n *
          PowerSeries.C (constantCoeff (R := FractionRing R) u) := by
      have hb : (algebraMap R (FractionRing R)) (d : R) *
          constantCoeff (R := FractionRing R) u = algebraMap R (FractionRing R) r := by
        rw [← hrd]; exact IsLocalization.mk'_spec' _ r d
      rw [atPrimeToFractionPowerSeries, IsLocalization.lift_mk'_spec, map_mul, map_pow,
        PowerSeries.map_C, PowerSeries.map_X]
      change PowerSeries.C (algebraMap R (FractionRing R) r) *
          (X : PowerSeries (FractionRing R)) ^ n
        = PowerSeries.map (algebraMap R (FractionRing R)) (PowerSeries.C (d : R)) *
          ((X : PowerSeries (FractionRing R)) ^ n *
            PowerSeries.C (constantCoeff (R := FractionRing R) u))
      rw [PowerSeries.map_C, ← hb, map_mul]
      ring
    rw [map_add, hkey]
    rw [show (powerSeriesXIdeal (FractionRing R) ^ (n + 1)) =
        Ideal.span {(X : PowerSeries (FractionRing R)) ^ (n + 1)} from
        Ideal.span_singleton_pow _ _, Ideal.mem_span_singleton]
    have hdvd : (X : PowerSeries (FractionRing R)) ∣
        (u - PowerSeries.C (constantCoeff (R := FractionRing R) u)) := by
      rw [PowerSeries.X_dvd_iff]
      simp
    obtain ⟨w, hw⟩ := hdvd
    refine ⟨w, ?_⟩
    have : t - (atPrimeToFractionPowerSeries R s +
        (X : PowerSeries (FractionRing R)) ^ n *
          PowerSeries.C (constantCoeff (R := FractionRing R) u)) =
        (X : PowerSeries (FractionRing R)) ^ n *
          (u - PowerSeries.C (constantCoeff (R := FractionRing R) u)) := by
      rw [mul_sub, ← hu]; ring
    rw [this, hw]; ring

/-- The completion of `FormalSpectrum.atPrimeToFractionPowerSeries` is bijective, by the levelwise
criterion at the two previous lemmas. -/
theorem bijective_mapCompletion_atPrimeToFractionPowerSeries :
    Function.Bijective (AdicCompletion.mapCompletion (atPrimeToFractionPowerSeries R)
      (map_pointIdeal_atPrimeToFractionPowerSeries R).le (fg_powerSeriesXIdeal _)) := by
  refine AdicCompletion.bijective_mapCompletion_of_bijective_quotientMap _ _
    ((fg_powerSeriesXIdeal R).map _) (fg_powerSeriesXIdeal _) fun n hc => ?_
  refine AdicCompletion.bijective_quotientMap_of _ hc ?_ ?_
  · intro t
    obtain ⟨s, hs⟩ := exists_sub_atPrimeToFractionPowerSeries_mem R n t
    exact ⟨s, hs⟩
  · exact fun s hs => mem_pointIdeal_pow_of_map_mem R n s hs

/-- **The target of the stalk comparison at the generic point is `K⟦X⟧`, `K = Frac R`** — the
second of the two ring identifications, at every domain.

Over `ℤ` this says the target is `ℚ⟦X⟧`. Together with
`FormalSpectrum.awayCompletionEquivPowerSeriesAway` it turns the surjectivity half of
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff` into the assertion that every element of
`ℚ⟦X⟧` has all of its coefficients in a single `ℤ[1/m]`, which
`FormalSpectrum.not_isStalkLimit_powerSeriesXIntGenericPoint` refutes. -/
def atPrimeCompletionEquivFractionPowerSeries :
    AdicCompletion (pointIdeal (powerSeriesXIdeal R) (powerSeriesXGenericPoint R))
        (Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)))
      ≃+* PowerSeries (FractionRing R) :=
  (RingEquiv.ofBijective _ (bijective_mapCompletion_atPrimeToFractionPowerSeries R)).trans
    (RingEquiv.ofBijective _
      (AdicCompletion.bijective_algebraMap_of_isAdicComplete
        (powerSeriesXIdeal (FractionRing R)))).symm

/-- `FormalSpectrum.atPrimeCompletionEquivFractionPowerSeries` as an equation between ring maps into
the completion of `K⟦X⟧`. -/
theorem algebraMap_atPrimeCompletionEquivFractionPowerSeries
    (b : AdicCompletion (pointIdeal (powerSeriesXIdeal R) (powerSeriesXGenericPoint R))
      (Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)))) :
    algebraMap (PowerSeries (FractionRing R))
        (AdicCompletion (powerSeriesXIdeal (FractionRing R))
          (PowerSeries (FractionRing R)))
        (atPrimeCompletionEquivFractionPowerSeries R b) =
      AdicCompletion.mapCompletion (atPrimeToFractionPowerSeries R)
        (map_pointIdeal_atPrimeToFractionPowerSeries R).le (fg_powerSeriesXIdeal _) b :=
  (RingEquiv.ofBijective _ (AdicCompletion.bijective_algebraMap_of_isAdicComplete
    (powerSeriesXIdeal (FractionRing R)))).apply_symm_apply _

/-- The map `R[1/m] →+* Frac R` for `m ≠ 0` in a domain: everything inverted on the left is already
invertible on the right. This is the map the counterexample is about — its image is the subring of
fractions whose denominators are powers of `m`. -/
def awayToFractionRing (m : R) (hm : m ≠ 0) :
    Localization.Away m →+* FractionRing R :=
  IsLocalization.lift (M := Submonoid.powers m) (g := algebraMap R (FractionRing R))
    (fun y => by
      obtain ⟨k, hk⟩ := y.2
      refine isUnit_iff_ne_zero.mpr fun h => ?_
      have h0 : (y : R) = 0 := (map_eq_zero_iff _ (IsFractionRing.injective R
        (FractionRing R))).mp h
      rw [← hk] at h0
      exact hm (pow_eq_zero_iff'.mp h0).1)

/-- `FormalSpectrum.awayToFractionRing` is a map under `R`. -/
theorem awayToFractionRing_algebraMap (m : R) (hm : m ≠ 0) (r : R) :
    awayToFractionRing R m hm (algebraMap R (Localization.Away m) r) =
      algebraMap R (FractionRing R) r :=
  IsLocalization.lift_eq _ r

/-- **The square, before completing.** The localization map `R⟦X⟧[1/f] → R⟦X⟧_{(X)}` followed by
the identification of the target with `K⟦X⟧` is `PowerSeries.map` of `R[1/m] → K` followed by the
identification of the source with `R[1/m]⟦X⟧`.

Both sides are ring maps out of a localization of `R⟦X⟧`, so `IsLocalization.ringHom_ext` reduces
this to their values on `R⟦X⟧`, where both are `PowerSeries.map (algebraMap R K)`. No continuity
and no completeness is used: this is the whole content of the compatibility, and the completed
statement follows from it by functoriality alone. -/
theorem atPrimeToFractionPowerSeries_comp_awayToAtPrime (f : PowerSeries R)
    (hf : powerSeriesXGenericPoint R ∈ basicOpen (powerSeriesXIdeal R) f)
    (hm : constantCoeff f ≠ 0) :
    (atPrimeToFractionPowerSeries R).comp
        (awayToAtPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) hf) =
      (PowerSeries.map (awayToFractionRing R (constantCoeff f) hm)).comp
        (awayToPowerSeriesAway f) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun g => ?_)
  have hcomp : (awayToFractionRing R (constantCoeff f) hm).comp
        (algebraMap R (Localization.Away (constantCoeff f))) =
      algebraMap R (FractionRing R) :=
    RingHom.ext fun r => awayToFractionRing_algebraMap R (constantCoeff f) hm r
  simp only [RingHom.coe_comp, Function.comp_apply, awayToAtPrime_algebraMap,
    atPrimeToFractionPowerSeries_algebraMap, awayToPowerSeriesAway_algebraMap]
  rw [show PowerSeries.map (awayToFractionRing R (constantCoeff f) hm)
        (PowerSeries.map (algebraMap R (Localization.Away (constantCoeff f))) g) =
      PowerSeries.map ((awayToFractionRing R (constantCoeff f) hm).comp
        (algebraMap R (Localization.Away (constantCoeff f)))) g from by
      rw [PowerSeries.map_comp]; rfl, hcomp]

/-- **The two identifications are compatible with the stalk comparison.** Under
`FormalSpectrum.awayCompletionEquivPowerSeriesAway` on the source and
`FormalSpectrum.atPrimeCompletionEquivFractionPowerSeries` on the target, the comparison map
`FormalSpectrum.awayToAtPrimeCompletion` at the generic point **is** `PowerSeries.map` of
`R[1/m] → Frac R`, coefficient by coefficient.

This is the previous lemma pushed through `AdicCompletion.mapCompletion_comp` twice, with
`AdicCompletion.mapCompletion_algebraMap` recognising the two `algebraMap`s and one local step
rewriting the ring-level square inside the completion functor. That step is
`AdicCompletion.mapCompletion_congr` (`FormalSchemes.CompletionNestedBasicOpenMap`), which is
**not** imported: its module adds fourteen to this file's forward closure, measured, and the step
is two lines. It is what makes the counterexample a statement about denominators of rational
numbers. -/
theorem atPrimeCompletionEquiv_awayToAtPrimeCompletion (f : PowerSeries R)
    (hf : powerSeriesXGenericPoint R ∈ basicOpen (powerSeriesXIdeal R) f)
    (hm : constantCoeff f ≠ 0) (a : awayCompletion (powerSeriesXIdeal R) f) :
    atPrimeCompletionEquivFractionPowerSeries R
        (awayToAtPrimeCompletion (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)
          (fg_powerSeriesXIdeal R) hf a) =
      PowerSeries.map (awayToFractionRing R (constantCoeff f) hm)
        (awayCompletionEquivPowerSeriesAway f a) := by
  have hFG : (((powerSeriesXIdeal R).map
      (algebraMap (PowerSeries R) (Localization.Away f)))).FG := (fg_powerSeriesXIdeal R).map _
  -- `AdicCompletion.mapCompletion` depends on its ring map only through its value; the two
  -- containment proofs are propositions. `AdicCompletion.mapCompletion_congr`
  -- (`FormalSchemes.CompletionNestedBasicOpenMap`) is this statement, but that module is not in
  -- this file's closure and adds fourteen, so it is used here as a local step rather than imported.
  have hcongr : ∀ (φ₁ φ₂ : Localization.Away f →+* PowerSeries (FractionRing R))
      (h₁ : ((powerSeriesXIdeal R).map
        (algebraMap (PowerSeries R) (Localization.Away f))).map φ₁ ≤
          powerSeriesXIdeal (FractionRing R))
      (h₂ : ((powerSeriesXIdeal R).map
        (algebraMap (PowerSeries R) (Localization.Away f))).map φ₂ ≤
          powerSeriesXIdeal (FractionRing R))
      (hJ : (powerSeriesXIdeal (FractionRing R)).FG), φ₁ = φ₂ →
      AdicCompletion.mapCompletion φ₁ h₁ hJ = AdicCompletion.mapCompletion φ₂ h₂ hJ := by
    rintro φ₁ φ₂ h₁ h₂ hJ rfl
    rfl
  refine (AdicCompletion.bijective_algebraMap_of_isAdicComplete
    (powerSeriesXIdeal (FractionRing R))).1 ?_
  rw [algebraMap_atPrimeCompletionEquivFractionPowerSeries, awayToAtPrimeCompletion,
    ← RingHom.comp_apply, AdicCompletion.mapCompletion_comp _ _ _ _ _ _ hFG,
    hcongr _ _ _ _ _ (atPrimeToFractionPowerSeries_comp_awayToAtPrime R f hf hm),
    ← AdicCompletion.mapCompletion_comp (awayToPowerSeriesAway f)
      (PowerSeries.map (awayToFractionRing R (constantCoeff f) hm))
      (map_awayToPowerSeriesAway f).le (map_powerSeriesXIdeal_map _).le
      (fg_powerSeriesXIdeal _) (fg_powerSeriesXIdeal _) hFG,
    RingHom.comp_apply, ← algebraMap_awayCompletionEquivPowerSeriesAway f a,
    AdicCompletion.mapCompletion_algebraMap]
  rw [← Ideal.map_map, map_awayToPowerSeriesAway]
  exact (map_powerSeriesXIdeal_map _).le

/-! ### The injectivity half at the generic point

The refutation above kills a conjunction, and this section is what stops it from being a boring
one: the injectivity half of `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff` holds at
the generic point of every domain, so at `(X) ⊆ ℤ⟦X⟧` the predicate fails in the surjectivity
half only.
-/

/-- **`FormalSpectrum.awayToFractionRing` is injective** for `m ≠ 0` in a domain: `R[1/m]` really
does sit inside `Frac R`, as the fractions whose denominators are powers of `m`.

`IsLocalization.injective_iff_map_algebraMap_eq` reduces injectivity of a ring map out of a
localization to a statement about the structural map alone, and there both sides say `x = y`: the
source by `IsLocalization.injective` at `Submonoid.powers m ≤ nonZeroDivisors R`, the target by
`IsFractionRing.injective`. -/
theorem injective_awayToFractionRing (m : R) (hm : m ≠ 0) :
    Function.Injective (awayToFractionRing R m hm) := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq (M := Submonoid.powers m)]
  intro x y
  rw [awayToFractionRing_algebraMap, awayToFractionRing_algebraMap]
  refine ⟨fun h => congrArg _ (IsLocalization.injective (Localization.Away m)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hm) h),
    fun h => congrArg _ (IsFractionRing.injective R (FractionRing R) h)⟩

/-- **The comparison map at the generic point is injective**, at every domain and every `f` with
`constantCoeff f ≠ 0`. This is more than the injectivity half asks for: the half is content with
a section that dies after restriction to a smaller basic open, and this says the section is
already `0`.

It is `FormalSpectrum.atPrimeCompletionEquiv_awayToAtPrimeCompletion` read as a statement about
maps rather than about elements. That lemma is an equation between *applications*, and the step
from it to injectivity of the comparison is the only place this argument could go wrong quietly:
it goes through because `FormalSpectrum.awayCompletionEquivPowerSeriesAway` and
`FormalSpectrum.atPrimeCompletionEquivFractionPowerSeries` are `RingEquiv`s, hence injective, and
because `PowerSeries.map` of an injective ring map is injective (`PowerSeries.map_injective`, in
Mathlib). -/
theorem injective_awayToAtPrimeCompletion_powerSeriesXGenericPoint (f : PowerSeries R)
    (hf : powerSeriesXGenericPoint R ∈ basicOpen (powerSeriesXIdeal R) f)
    (hm : constantCoeff f ≠ 0) :
    Function.Injective (awayToAtPrimeCompletion (powerSeriesXIdeal R)
      (powerSeriesXGenericPoint R) (fg_powerSeriesXIdeal R) hf) := by
  intro a b hab
  refine (awayCompletionEquivPowerSeriesAway f).injective
    (PowerSeries.map_injective _ (injective_awayToFractionRing R (constantCoeff f) hm) ?_)
  rw [← atPrimeCompletionEquiv_awayToAtPrimeCompletion R f hf hm a,
    ← atPrimeCompletionEquiv_awayToAtPrimeCompletion R f hf hm b, hab]

/-- **The injectivity half of `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff` holds**,
at the generic point of every domain.

The half asks for *some* smaller basic open on which the section already vanishes; the previous
lemma gives that the section is `0` outright, so `e = f` and `le_rfl` serve. All that is used of
`FormalSpectrum.awayCompletionRestrict` here is that it is a ring homomorphism and therefore
sends `0` to `0`; in particular nothing below claims that restriction along `le_rfl` is the
identity, which is a separate question about `FormalSchemes.AwayCompletionRestrict`. -/
theorem exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint (f : PowerSeries R)
    (hf : constantCoeff f ≠ 0) (a : awayCompletion (powerSeriesXIdeal R) f)
    (ha : awayToAtPrimeCompletion (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)
      (fg_powerSeriesXIdeal R) ((mem_basicOpen_powerSeriesXGenericPoint_iff R f).mpr hf) a = 0) :
    ∃ e, ∃ (_ : constantCoeff e ≠ 0)
      (hle : basicOpen (powerSeriesXIdeal R) e ≤ basicOpen (powerSeriesXIdeal R) f),
      awayCompletionRestrict (powerSeriesXIdeal R) f e (fg_powerSeriesXIdeal R) hle a = 0 :=
  have ha0 : a = 0 :=
    injective_awayToAtPrimeCompletion_powerSeriesXGenericPoint R f _ hf (by rw [ha, map_zero])
  ⟨f, hf, le_rfl, by rw [ha0, map_zero]⟩

/-! ### The surjectivity half, characterised

The two identifications turn the half at the generic point into a statement with no completion, no
localization of `R⟦X⟧` and no formal geometry in it at all: a question about denominators in
`Frac R`. Both values of the half become corollaries of it — `ℤ` fails it because a prime larger
than `|m|` divides no power of `m`, and a discrete valuation ring satisfies it because inverting
one uniformizer already gives the whole fraction field.
-/

/-- **Membership in the image of `R[1/m] → Frac R`, with no localization in the statement.** An
element of `Frac R` is a fraction whose denominator is a power of `m` exactly when some power of
`m` clears it into `R`.

Forwards, `IsLocalization.mk'_surjective` writes the preimage as `r / m ^ k` and
`IsLocalization.mk'_spec'` clears the denominator. Backwards, `IsLocalization.lift_mk'_spec` turns
the cleared equation into a value of the lift; `FormalSpectrum.awayToFractionRing` is a `def`
wrapping `IsLocalization.lift`, so that lemma has to be pointed at it explicitly before it
fires. -/
theorem mem_range_awayToFractionRing_iff (m : R) (hm : m ≠ 0) (x : FractionRing R) :
    x ∈ Set.range (awayToFractionRing R m hm) ↔
      ∃ k : ℕ, algebraMap R (FractionRing R) (m ^ k) * x ∈
        Set.range (algebraMap R (FractionRing R)) := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.mk'_surjective (Submonoid.powers m) y
    obtain ⟨k, hk⟩ := s.2
    refine ⟨k, r, ?_⟩
    have hspec : algebraMap R (Localization.Away m) (s : R) * y =
        algebraMap R (Localization.Away m) r := by
      rw [← show IsLocalization.mk' (Localization.Away m) r s = y from hy]
      exact IsLocalization.mk'_spec' _ r s
    have hs : (s : R) = m ^ k := hk.symm
    have hmap := congrArg (awayToFractionRing R m hm) hspec
    rw [map_mul, awayToFractionRing_algebraMap, awayToFractionRing_algebraMap, hs] at hmap
    exact hmap.symm
  · rintro ⟨k, r, hr⟩
    refine ⟨IsLocalization.mk' (Localization.Away m) r
      (⟨m ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers m), ?_⟩
    rw [show awayToFractionRing R m hm = IsLocalization.lift
      (M := Submonoid.powers m) (g := algebraMap R (FractionRing R)) _ from rfl,
      IsLocalization.lift_mk'_spec]
    change algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (m ^ k) * x
    exact hr

/-- **The surjectivity half at the generic point, characterised.** At a domain `R` the half holds
exactly when every `ℕ`-indexed family in `Frac R` lies inside a single `R[1/m]` with `m ≠ 0`.

Read through `FormalSpectrum.awayCompletionEquivPowerSeriesAway` and
`FormalSpectrum.atPrimeCompletionEquivFractionPowerSeries`, tied together by
`FormalSpectrum.atPrimeCompletionEquiv_awayToAtPrimeCompletion`, the comparison map is
`PowerSeries.map` of `FormalSpectrum.awayToFractionRing R m`, and a power series over `Frac R` is
an `ℕ`-indexed family in `Frac R`. `PowerSeries.exists_map_eq_iff_forall_coeff_mem_range` is what
turns *hit by `PowerSeries.map`* into a condition on coefficients. Backwards the `f` is
`PowerSeries.C m`, whose constant term is `m` definitionally, so no transport is needed for the
dependent type `PowerSeries (Localization.Away (constantCoeff f))`.

**The quantifier order is the whole content.** `∀ x, ∃ m` is the statement, and the `m` is allowed
to depend on the family. `∃ m, ∀ x` is stronger and is false at `ℤ`, since it implies this one, and
it is **strictly stronger** — the two come apart at an ultrapower of `ℤ`
(`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`) — while over a countable fraction field
it is not:
`FormalSpectrum.hasBoundedDenominators_iff_exists_denominator` puts a single `m` serving every
element of `Frac R` at once, hence every family, on the other side of an `↔`.
`∀ x, ∀ n, ∃ m` is strictly weaker and holds at every domain, because a single element
of `Frac R` is a fraction and its own denominator serves; a characterisation with that order would
be vacuous. -/
theorem exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff :
    (∀ b : AdicCompletion (pointIdeal (powerSeriesXIdeal R) (powerSeriesXGenericPoint R))
        (Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R))),
      ∃ f, ∃ (hf : constantCoeff f ≠ 0),
        ∃ a, awayToAtPrimeCompletion (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)
          (fg_powerSeriesXIdeal R)
          ((mem_basicOpen_powerSeriesXGenericPoint_iff R f).mpr hf) a = b) ↔
      ∀ x : ℕ → FractionRing R, ∃ m : R, ∃ hm : m ≠ 0,
        ∀ n, x n ∈ Set.range (awayToFractionRing R m hm) := by
  constructor
  · intro h x
    obtain ⟨f, hf, a, ha⟩ := h
      ((atPrimeCompletionEquivFractionPowerSeries R).symm (PowerSeries.mk x))
    have key : PowerSeries.map (awayToFractionRing R (constantCoeff f) hf)
        (awayCompletionEquivPowerSeriesAway f a) = PowerSeries.mk x := by
      rw [← atPrimeCompletionEquiv_awayToAtPrimeCompletion R f
        ((mem_basicOpen_powerSeriesXGenericPoint_iff R f).mpr hf) hf a, ha,
        RingEquiv.apply_symm_apply]
    exact ⟨constantCoeff f, hf, fun n =>
      ⟨PowerSeries.coeff n (awayCompletionEquivPowerSeriesAway f a), by
        rw [← PowerSeries.coeff_map, key, PowerSeries.coeff_mk]⟩⟩
  · intro h b
    obtain ⟨m, hm, hall⟩ := h fun n =>
      PowerSeries.coeff n (atPrimeCompletionEquivFractionPowerSeries R b)
    have hcc : constantCoeff (PowerSeries.C m) ≠ 0 := by
      rw [constantCoeff_C]
      exact hm
    obtain ⟨z, hz⟩ := (PowerSeries.exists_map_eq_iff_forall_coeff_mem_range
      (awayToFractionRing R m hm) (atPrimeCompletionEquivFractionPowerSeries R b)).mpr hall
    refine ⟨PowerSeries.C m, hcc,
      (awayCompletionEquivPowerSeriesAway (PowerSeries.C m)).symm z, ?_⟩
    apply (atPrimeCompletionEquivFractionPowerSeries R).injective
    rw [atPrimeCompletionEquiv_awayToAtPrimeCompletion R (PowerSeries.C m) _ hcc,
      RingEquiv.apply_symm_apply]
    exact hz

/-! ### The denominator condition, named

The right-hand side of the characterisation is a condition on `R` alone: no completion, no
localization of `R⟦X⟧`, no power series. Until it has a name nothing can be proved *about* it, and
the three values in this file read as three unrelated computations rather than as three values of
one condition.
-/

/-- **The denominator condition.** Every `ℕ`-indexed family in `Frac R` has a single denominator up
to powers: one `m ≠ 0` such that every member of the family is cleared into `R` by some power of
`m`.

Equivalently every such family lies inside a single `R[1/m]`
(`FormalSpectrum.hasBoundedDenominators_iff_range`), and it makes no difference whether the
families are indexed by `ℕ` or are countable subsets of `Frac R`
(`FormalSpectrum.hasBoundedDenominators_iff_countable`).

**The quantifier order is the content.** The `m` is uniform in the family and the exponent `k` is
not: each member may need its own power of the same `m`. Weakening to `∀ x, ∀ n, ∃ m` holds at
every domain, because a single element of `Frac R` is a fraction and its own denominator serves;
strengthening to `∃ m, ∀ x` implies this one and so is false at `ℤ`. That strengthening is
*strictly* stronger at a general domain — an ultrapower of `ℤ` satisfies this condition and no
single `m` serves it (`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`) — while over a
**countable** fraction field it is not, the two being equivalent by
`FormalSpectrum.hasBoundedDenominators_iff_exists_denominator`.

This is exactly the surjectivity half of
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff` at the generic point of `R`, by
`FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators`. It
is **one conjunct**, but the other one holds at the generic point of every domain
(`FormalSpectrum.exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint`), so at **this**
point the two coincide and the condition is `FormalSpectrum.IsStalkLimit` itself
(`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`). It is not the
predicate at any other point, nor at any other ideal of definition. Naming it
decided nothing on its own; what decides it is
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`, and only at a **unique factorisation
domain**, where the condition is exactly *finitely many primes up to associates*. Two criteria at
an arbitrary domain are proved below
(`FormalSpectrum.hasBoundedDenominators_of_forall_dvd_pow` and
`FormalSpectrum.not_hasBoundedDenominators_of_primes`); away from that hypothesis they still do not
meet, and the sufficient one is not necessary at a general domain
(`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`). Over a **countable**
fraction field it is necessary, and the condition collapses to a single `R[1/m]` being the whole of
`Frac R` (`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective`) — a second hypothesis,
incomparable with the first, under which the criteria meet without deciding any ring.

A `def` rather than a `class`: the condition occurs on the right of an `↔`, where instance search
has nothing to do, and one of its three values is a *negation*, which no instance can carry. The
class variant does elaborate — a field and a discrete valuation ring both give firing instances —
and was rejected for those two reasons, not because it fails.

The binders are written out rather than taken from the section: `IsDomain R` is not used by the
body, so it would be dropped from the signature, and the condition is only the intended one at a
domain — over a ring with zero divisors `m ≠ 0` does not make `m` a denominator. -/
def HasBoundedDenominators (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ x : ℕ → FractionRing R, ∃ m : R, m ≠ 0 ∧ ∀ n, ∃ k : ℕ,
    algebraMap R (FractionRing R) (m ^ k) * x n ∈ Set.range (algebraMap R (FractionRing R))

/-- **The condition, with the localization back in.** A family has a single denominator up to
powers exactly when it lies inside a single `R[1/m]`.

`FormalSpectrum.mem_range_awayToFractionRing_iff` at each member. The two forms are used in
different places: the definition is elementary arithmetic in `R` and `Frac R`, and this one is
what the characterisation and the value at a discrete valuation ring are stated with. -/
theorem hasBoundedDenominators_iff_range :
    HasBoundedDenominators R ↔ ∀ x : ℕ → FractionRing R, ∃ m : R, ∃ hm : m ≠ 0,
      ∀ n, x n ∈ Set.range (awayToFractionRing R m hm) := by
  constructor
  · intro h x
    obtain ⟨m, hm, hall⟩ := h x
    exact ⟨m, hm, fun n => (mem_range_awayToFractionRing_iff R m hm (x n)).mpr (hall n)⟩
  · intro h x
    obtain ⟨m, hm, hall⟩ := h x
    exact ⟨m, hm, fun n => (mem_range_awayToFractionRing_iff R m hm (x n)).mp (hall n)⟩

/-- **`ℕ`-indexed families and countable subsets give the same condition.** The half needs the
`ℕ`-indexed form, because a power series is an `ℕ`-indexed family; this says nothing is lost or
gained by asking it of every countable subset of `Frac R` instead.

Forwards, a nonempty countable set is a range (`Set.Countable.exists_eq_range`) and the empty set
is served by `m = 1` — the one place the two quantifier problems differ. Backwards, the range of a
family is countable. -/
theorem hasBoundedDenominators_iff_countable :
    HasBoundedDenominators R ↔ ∀ s : Set (FractionRing R), s.Countable →
      ∃ m : R, m ≠ 0 ∧ ∀ y ∈ s, ∃ k : ℕ,
        algebraMap R (FractionRing R) (m ^ k) * y ∈
          Set.range (algebraMap R (FractionRing R)) := by
  constructor
  · intro h s hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_ne_zero, by simp⟩
    · obtain ⟨f, rfl⟩ := hs.exists_eq_range hne
      obtain ⟨m, hm, hall⟩ := h f
      exact ⟨m, hm, by rintro _ ⟨n, rfl⟩; exact hall n⟩
  · intro h x
    obtain ⟨m, hm, hall⟩ := h (Set.range x) (Set.countable_range x)
    exact ⟨m, hm, fun n => hall _ ⟨n, rfl⟩⟩

/-- **The same characterisation with the condition named.** The half at the generic point of a
domain holds exactly when `FormalSpectrum.HasBoundedDenominators` holds of `R`: every `ℕ`-indexed
family in `Frac R` has a common denominator up to powers, a single `m ≠ 0` such that every member
is cleared into `R` by some power of `m`.

`FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff` read through
`FormalSpectrum.hasBoundedDenominators_iff_range`. This is the form a consumer wants: its
right-hand side is elementary arithmetic in `R` and `Frac R` and names neither `Localization.Away`
nor any completion. The right-hand side is the definition unfolded and the statement is the one
this theorem had before the condition was named; only the spelling of that side changed. -/
theorem exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators :
    (∀ b : AdicCompletion (pointIdeal (powerSeriesXIdeal R) (powerSeriesXGenericPoint R))
        (Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R))),
      ∃ f, ∃ (hf : constantCoeff f ≠ 0),
        ∃ a, awayToAtPrimeCompletion (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)
          (fg_powerSeriesXIdeal R)
          ((mem_basicOpen_powerSeriesXGenericPoint_iff R f).mpr hf) a = b) ↔
      HasBoundedDenominators R :=
  (exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff R).trans
    (hasBoundedDenominators_iff_range R).symm

/-! ### Two criteria at an arbitrary domain

Three values are three rings. The two criteria below are what holds at an arbitrary domain: one
**sufficient** — a single `m ≠ 0` whose powers clear every denominator — and one that **refutes**
— a family of primes that no single element is divisible by. Both values above and below are
instances of the first, and `ℤ` is an instance of the second.

**The sufficient criterion has two faces and they are one criterion.** *Every nonzero `s` divides
a power of `m`* and *`R[1/m]` is already the whole of `Frac R`* are equivalent at a fixed `m ≠ 0`
at any domain (`FormalSpectrum.surjective_awayToFractionRing_iff_forall_dvd_pow`), so which one a
statement below is written in is a matter of what its consumer holds and not a difference in
strength. That equivalence is about **one** `m`; it says nothing about the quantifier over `m`,
which is where every open question in this section lives.

**Neither is a classification on its own, and at a general domain the two together are not one
either.** The sufficient criterion is not necessary there
(`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`), and the refuting one is not known to be
the only way the condition can fail. The obstruction is that
`FormalSpectrum.HasBoundedDenominators` only ever sees **countable** families
(`FormalSpectrum.hasBoundedDenominators_iff_countable`), so a domain whose fraction field needs
uncountably many denominator types is not ruled out by anything here — and an ultrapower of `ℤ` is
such a domain.

**Two hypotheses make them meet, and they meet in different ways.** At a unique factorisation
domain the section below glues them into
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`, and that hypothesis is what makes the
passage from *every prime divides `m`* to *every element divides a power of `m`* available; that
one **decides** the condition, as a cardinality. Over a countable fraction field the section after
it turns the sufficient criterion into
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` by removing the obstruction rather
than getting round it — the condition may then be applied to the whole of `Frac R` at once — and
that one **decides nothing**, it only makes the condition elementary. The two hypotheses are
incomparable. Nothing below decides Dedekind, semilocal, Prüfer or valuation rings, and nothing
below is attempted at a non-domain.
-/

/-- **The sufficient criterion, first half**: if a single `m ≠ 0` is such that every nonzero
`s : R` divides some power of `m`, then `R[1/m]` is already the whole fraction field.

`FormalSpectrum.mem_range_awayToFractionRing_iff` at `x = r / s`: an equation `s * t = m ^ k`
clears the denominator into `R`, and `r * t` is then the numerator of `x` over `m ^ k`. The
content is that **one** `m` serves every `s`; for each `s` separately its own denominator serves,
at every domain.

`FormalSpectrum.surjective_awayToFractionRing_of_irreducible` is the same conclusion at a
uniformizer of a discrete valuation ring, proved from the valuation rather than from
divisibility. -/
theorem surjective_awayToFractionRing_of_forall_dvd_pow {m : R} (hm : m ≠ 0)
    (h : ∀ s : R, s ≠ 0 → ∃ k : ℕ, s ∣ m ^ k) :
    Function.Surjective (awayToFractionRing R m hm) := by
  intro x
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := R) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨k, t, ht⟩ := h s hs0
  rw [← Set.mem_range, mem_range_awayToFractionRing_iff]
  refine ⟨k, r * t, ?_⟩
  have hsne : algebraMap R (FractionRing R) s ≠ 0 := fun hz =>
    hs0 (IsFractionRing.injective R (FractionRing R) (by rw [hz, map_zero]))
  rw [← hrs, ht, map_mul, map_mul]
  field_simp

/-- **The converse of the first half**: if `R[1/m]` is already the whole fraction field then every
nonzero `s : R` divides a power of `m`. At an arbitrary domain, with no factorisation and no
countability hypothesis.

**The divisibility condition is Mathlib's description of what it means for `s` to become a unit in
`R[1/m]`**: `IsLocalization.Away.algebraMap_isUnit_iff` says `IsUnit (algebraMap R R[1/m] s)` is
`∃ n, s ∣ m ^ n`, at any commutative ring. So the only thing to prove is that surjectivity makes
every nonzero `s` a unit there, and that is where the hypotheses are spent: `s ≠ 0` gives an
inverse in `Frac R`, surjectivity pulls it back to some `y : R[1/m]`, and
`FormalSpectrum.injective_awayToFractionRing` — which needs `m ≠ 0` and `IsDomain R` — is what
promotes `y * s = 1` from `Frac R` to `R[1/m]`.

Injectivity is the step that cannot be dropped: a surjection alone would only say the two rings
have the same image, and `y * s` and `1` could differ in the kernel. -/
theorem forall_dvd_pow_of_surjective_awayToFractionRing {m : R} (hm : m ≠ 0)
    (hs : Function.Surjective (awayToFractionRing R m hm)) (s : R) (hs0 : s ≠ 0) :
    ∃ k : ℕ, s ∣ m ^ k := by
  rw [← IsLocalization.Away.algebraMap_isUnit_iff (S := Localization.Away m) (x := m)]
  obtain ⟨y, hy⟩ := hs (algebraMap R (FractionRing R) s)⁻¹
  refine isUnit_iff_exists_inv.mpr ⟨y, injective_awayToFractionRing R m hm ?_⟩
  rw [map_mul, hy, map_one, awayToFractionRing_algebraMap]
  exact mul_inv_cancel₀ fun h => hs0 (IsFractionRing.injective R (FractionRing R)
    (by rw [h, map_zero]))

/-- **The two forms of the sufficient criterion are one criterion.** For a fixed `m ≠ 0` at an
arbitrary domain, `R[1/m] → Frac R` is surjective **iff** every nonzero element of `R` divides a
power of `m`.

The backward direction is `FormalSpectrum.surjective_awayToFractionRing_of_forall_dvd_pow`, which
was already on the tree; only the forward direction is new. Their relation is exactly that of
`FormalSpectrum.hasBoundedDenominators_iff_range` to
`FormalSpectrum.HasBoundedDenominators` — one statement in a localized spelling and an arithmetic
one, with nothing between them.

**This decides no ring.** It is a statement about one fixed `m`, and it says nothing new about
`FormalSpectrum.HasBoundedDenominators`, which quantifies over `m`. In particular it does **not**
remove the countability hypothesis from
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` or the unique-factorisation
hypothesis from `FormalSpectrum.hasBoundedDenominators_iff_finite_primes`: both of those are about
the quantifier over `m`, which this leaves exactly where it was. Nothing here bears on Dedekind,
semilocal, Prüfer or valuation rings either.

The quantified consequence, where the `m` is bound, is
`FormalSpectrum.hasBoundedDenominators_iff_forall_dvd_pow` below; it gets the quantifier from
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` and its countability hypothesis, not
from this. -/
theorem surjective_awayToFractionRing_iff_forall_dvd_pow {m : R} (hm : m ≠ 0) :
    Function.Surjective (awayToFractionRing R m hm) ↔ ∀ s : R, s ≠ 0 → ∃ k : ℕ, s ∣ m ^ k :=
  ⟨fun hs s hs0 => forall_dvd_pow_of_surjective_awayToFractionRing R hm hs s hs0,
    surjective_awayToFractionRing_of_forall_dvd_pow R hm⟩

/-- **The sufficient criterion is a statement about the ring `R[1/m]` alone**: for a fixed `m ≠ 0`
at an arbitrary domain, `R[1/m] → Frac R` is surjective **iff** `R[1/m]` is already a field.

This is Mathlib's `IsFractionRing.surjective_iff_isField` — *a domain surjects onto its fraction
field exactly when it is a field* — read at `R[1/m]` in place of `R`. What separates the two is an
instance gap and nothing more: `Algebra (Localization.Away m) (FractionRing R)` is **not**
synthesised on this tree, so the `IsFractionRing` hypothesis that lemma needs cannot even be stated
until the algebra structure is supplied. The proof supplies it from
`FormalSpectrum.awayToFractionRing` itself, so that `algebraMap` on the nose *is*
`FormalSpectrum.awayToFractionRing`, and the three steps in between are
`IsLocalization.isDomain_localization`, `IsScalarTower.of_algebraMap_eq` at
`FormalSpectrum.awayToFractionRing_algebraMap`, and
`IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`.

**The hand-rolled route was measured and rejected**, and a reader should know it exists. Proving
the two directions directly — the forward one from `RingEquiv.ofBijective` and `MulEquiv.isField`,
the backward one by clearing a denominator through `IsField.mul_inv_cancel` — elaborates, in about
thirty lines, and its forward direction is `IsFractionRing.surjective_iff_isField`'s own proof
copied out. Supplying the instance is shorter and leaves the citation visible.

**This decides no ring**, exactly as
`FormalSpectrum.surjective_awayToFractionRing_iff_forall_dvd_pow` does not. It is a statement about
one fixed `m`, and the quantifier over `m` in `FormalSpectrum.HasBoundedDenominators` is untouched
by it; the quantified consequence is
`FormalSpectrum.hasBoundedDenominators_iff_exists_isField` below, and it needs
`[Countable (FractionRing R)]` to get there, from
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` and not from this. -/
theorem surjective_awayToFractionRing_iff_isField {m : R} (hm : m ≠ 0) :
    Function.Surjective (awayToFractionRing R m hm) ↔ IsField (Localization.Away m) := by
  haveI : IsDomain (Localization.Away m) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hm)
  letI : Algebra (Localization.Away m) (FractionRing R) := (awayToFractionRing R m hm).toAlgebra
  haveI : IsScalarTower R (Localization.Away m) (FractionRing R) :=
    IsScalarTower.of_algebraMap_eq fun r => (awayToFractionRing_algebraMap R m hm r).symm
  haveI : IsFractionRing (Localization.Away m) (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers m)
      (Localization.Away m) (FractionRing R)
  exact IsFractionRing.surjective_iff_isField (K := FractionRing R)

/-- **The sufficient criterion, second half**: one surjective localization already gives the
condition. If `R[1/m] → Frac R` is surjective for a single `m ≠ 0`, every family in `Frac R` lies
in that one `R[1/m]`, and the denominator the condition asks for is chosen before the family is.

`FormalSpectrum.hasBoundedDenominators_iff_range` and nothing else.

Kept separate from `FormalSpectrum.hasBoundedDenominators_of_forall_dvd_pow` because the two have
different consumers: the value at a discrete valuation ring arrives with the surjection already in
hand (`FormalSpectrum.surjective_awayToFractionRing_of_irreducible`) and has no divisibility
hypothesis to offer, while the value at a field has only divisibility. -/
theorem hasBoundedDenominators_of_surjective {m : R} (hm : m ≠ 0)
    (hs : Function.Surjective (awayToFractionRing R m hm)) : HasBoundedDenominators R :=
  (hasBoundedDenominators_iff_range R).mpr fun x => ⟨m, hm, fun n => hs (x n)⟩

/-- **The sufficient criterion.** One `m ≠ 0` whose powers clear every nonzero denominator makes
the denominator condition hold.

The two halves composed. Both values in this file are instances: a field is `m = 1`, where every
nonzero element divides `1 ^ 0` because it is a unit, and a discrete valuation ring is a
uniformizer — though that one is shorter through
`FormalSpectrum.hasBoundedDenominators_of_surjective`, whose hypothesis it already has.

**Not known to be necessary at a general domain**, and this file does not claim it is; see the
section heading above for the obstruction. At a unique factorisation domain it **is** necessary,
and that is `FormalSpectrum.hasBoundedDenominators_iff_finite_primes`, whose backward direction is
this criterion at the product of a set of representatives of the prime associate classes and whose
forward direction is `FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated`
answering from the other side.

**Over a countable fraction field a criterion of this shape is necessary too, and it is this
one — as a theorem and no longer as a reading.**
`FormalSpectrum.hasBoundedDenominators_iff_forall_dvd_pow` is this criterion with its `m` bound and
turned into an `↔`: the condition holds there **iff** some `m ≠ 0` has the hypothesis of this
theorem. The two steps are `FormalSpectrum.hasBoundedDenominators_iff_exists_surjective`, which is
where the countability is spent, and
`FormalSpectrum.surjective_awayToFractionRing_iff_forall_dvd_pow`, which identifies the
surjectivity form with this divisibility form at a fixed `m` at every domain with no countability
at all. -/
theorem hasBoundedDenominators_of_forall_dvd_pow {m : R} (hm : m ≠ 0)
    (h : ∀ s : R, s ≠ 0 → ∃ k : ℕ, s ∣ m ^ k) : HasBoundedDenominators R :=
  hasBoundedDenominators_of_surjective R hm (surjective_awayToFractionRing_of_forall_dvd_pow R hm h)

/-- **The sufficient criterion in the third spelling**: for a single `m ≠ 0`, `R[1/m]` being a
field gives the denominator condition — at an arbitrary domain and with no countability.

`FormalSpectrum.hasBoundedDenominators_of_surjective` after
`FormalSpectrum.surjective_awayToFractionRing_iff_isField`, and that composition is the whole of
it.

**Named because the file already asserts it.**
`FormalSpectrum.hasBoundedDenominators_iff_exists_isField` below carries
`[Countable (FractionRing R)]`, and its docstring says that only *necessity* needs that hypothesis
while sufficiency holds at every domain. That was true, but the tree held it only as a composition
a reader had to perform; this is the composition, and the `↔` points here for it.

**It decides no ring**, exactly as its two companions above do not. It is a statement at one fixed
`m`, and the quantifier over `m` in `FormalSpectrum.HasBoundedDenominators` is untouched by it.
What separates the three is only what a consumer has to have in hand: a surjection onto `Frac R`
(`FormalSpectrum.hasBoundedDenominators_of_surjective`), a divisibility in `R`
(`FormalSpectrum.hasBoundedDenominators_of_forall_dvd_pow`), or a property of the ring `R[1/m]` on
its own, which is this one. -/
theorem hasBoundedDenominators_of_isField {m : R} (hm : m ≠ 0)
    (hf : IsField (Localization.Away m)) : HasBoundedDenominators R :=
  hasBoundedDenominators_of_surjective R hm
    ((surjective_awayToFractionRing_iff_isField R hm).mpr hf)

/-- **The refuting criterion.** A family of primes that no single `m ≠ 0` is divisible by refutes
the denominator condition.

Apply the condition to the family of inverses `n ↦ (p n)⁻¹`. A common denominator `m` and an
exponent `k` give `m ^ k = r * p n` back in `R`, so `p n ∣ m ^ k`, and `Prime.dvd_of_dvd_pow`
turns that into `p n ∣ m` — which is what the hypothesis forbids at some `n`. The family is
`ℕ`-indexed because that is what the condition quantifies over; no injectivity is asked of it.

**`Prime` does not weaken to `Irreducible` here.** The hypothesis is used only through
`Prime.dvd_of_dvd_pow` and `Prime.ne_zero`, and at a general domain an irreducible element need
not divide a factor of a power it divides, and exact? finds no `Irreducible` form of it. At
a unique factorisation domain the two hypotheses do agree
(`UniqueFactorizationMonoid.irreducible_iff_prime`), which is where
`FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated` lives.

**What the ultrapower falsifies here is the divisibility hypothesis and nothing else.** It has a
family of primes (`FormalSpectrum.exists_prime_family_not_associated_intUltrapower`), so the
primality hypothesis is met, but `FormalSpectrum.exists_forall_dvd_intUltrapower` applied to that
very family produces an `m ≠ 0` divisible by every member. The two criteria therefore fail at that
ring for different reasons — this one on its divisibility hypothesis, the companion below on
`[UniqueFactorizationMonoid R]`, which the same family shows is **needed** rather than merely
absent. -/
theorem not_hasBoundedDenominators_of_primes (p : ℕ → R) (hp : ∀ n, Prime (p n))
    (hdvd : ∀ m : R, m ≠ 0 → ∃ n, ¬ p n ∣ m) : ¬ HasBoundedDenominators R := by
  intro h
  obtain ⟨m, hm, hall⟩ := h fun n => (algebraMap R (FractionRing R) (p n))⁻¹
  obtain ⟨n, hn⟩ := hdvd m hm
  obtain ⟨k, r, hr⟩ := hall n
  apply hn
  have hpn0 : algebraMap R (FractionRing R) (p n) ≠ 0 := by simpa using (hp n).ne_zero
  have hfrac : algebraMap R (FractionRing R) (m ^ k) =
      algebraMap R (FractionRing R) r * algebraMap R (FractionRing R) (p n) := by
    field_simp at hr
    rw [← hr]
  rw [← map_mul] at hfrac
  have hmk : m ^ k = r * p n := IsFractionRing.injective R (FractionRing R) hfrac
  exact (hp n).dvd_of_dvd_pow (n := k) ⟨r, by rw [hmk, mul_comm]⟩

/-- **The refuting criterion in the form a caller has it**: at a unique factorisation domain a
family of pairwise non-associated primes refutes the denominator condition.

`FormalSpectrum.not_hasBoundedDenominators_of_primes` asks that no single `m` be divisible by the
whole family, which is what its proof consumes; this asks that the family be pairwise
non-associated, which is what a caller can check. If some `m ≠ 0` were divisible by every `p n`
then each `p n` is associated to a member of `UniqueFactorizationMonoid.factors m`, the resulting
map `ℕ → R` is injective because the family is pairwise non-associated, and a multiset of factors
is finite.

Both forms are shipped rather than one: the general one's hypothesis is strictly weaker — it needs
no factorisation and no pairwise condition — and this one is the only one that a family of primes
satisfies without any arithmetic being done first.

**`[UniqueFactorizationMonoid R]` is needed here, and not merely convenient**, by a witness rather
than by an argument:
`FormalSpectrum.not_forall_primes_not_associated_imp_not_hasBoundedDenominators`
(`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`) refutes this statement with that
instance deleted and nothing else changed. The witness is an ultrapower of `ℤ`, which has
infinitely many pairwise non-associated primes — the germs of the constant sequences at `2, 3, 5, …`
(`FormalSpectrum.exists_prime_family_not_associated_intUltrapower`) — and satisfies
`FormalSpectrum.HasBoundedDenominators` anyway
(`FormalSpectrum.hasBoundedDenominators_and_exists_primes_not_associated_intUltrapower`). That is
strictly more than `FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower`, which says only
that this criterion does not apply at that ring. -/
theorem not_hasBoundedDenominators_of_primes_not_associated [UniqueFactorizationMonoid R]
    (p : ℕ → R) (hp : ∀ n, Prime (p n))
    (hne : ∀ i j, Associated (p i) (p j) → i = j) : ¬ HasBoundedDenominators R := by
  classical
  refine not_hasBoundedDenominators_of_primes R p hp fun m hm => ?_
  by_contra hcon
  have hdvd : ∀ n, p n ∣ m := fun n => not_not.mp fun hnd => hcon ⟨n, hnd⟩
  choose f hf hfa using fun n =>
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd hm (hp n).irreducible (hdvd n)
  have hinj : Function.Injective f := fun i j hij =>
    hne i j ((hfa i).trans (hij ▸ (hfa j).symm))
  have hsub : Set.range f ⊆ (UniqueFactorizationMonoid.factors m).toFinset := by
    rintro _ ⟨n, rfl⟩
    exact Multiset.mem_toFinset.mpr (hf n)
  exact Set.infinite_range_of_injective hinj
    (((UniqueFactorizationMonoid.factors m).toFinset.finite_toSet).subset hsub)

/-! ### The classification at a unique factorisation domain

The two criteria above do not meet at a general domain. At a unique factorisation domain they do,
and the answer is a cardinality: **the denominator condition holds exactly when there are finitely
many primes up to associates.** That makes the three values below three cases of one theorem — a
field is the empty case, a discrete valuation ring the singleton case, and `ℤ` fails by Euclid —
and it is what the sentence *"the half is about how many primes have to be inverted at once"* says
once *how many* is read as a cardinality.

`Associates R` is the quotient of `R` by the associate relation, so `{a : Associates R | Prime a}`
says *up to associates* with no choice of representatives in the statement. Choice enters in both
directions of the proof, and only there.

**The hypothesis is not removable, and the forward direction says so by a witness.** An ultrapower
of `ℤ` satisfies the condition and has infinitely many prime associate classes, so the `↔` with
`[UniqueFactorizationMonoid R]` deleted is false —
`FormalSpectrum.not_forall_hasBoundedDenominators_iff_finite_primes` in
`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`, and
`FormalSpectrum.not_forall_hasBoundedDenominators_imp_finite_primes` for the direction that
actually fails. Nothing refutes the **backward** direction without the hypothesis, and outside a
unique factorisation domain it has no reason to hold either: it goes from *every prime divides `m`*
to *every element divides a power of `m`*, and that passage is factorisation. **A Dedekind domain
is still not a corollary of this** — it is a statement about ideals, not elements, and a
nonprincipal maximal ideal contributes no prime element at all — but there the passage is available
for a reason rather than by hypothesis, since finitely many prime ideals forces principality. That
is `FormalSpectrum.hasBoundedDenominators_iff_finite_primeIdeals`
(`FormalSchemes.StructureSheafStalkPowerSeriesDedekind`), which **derives** the factorisation
instead of removing this hypothesis. Nothing below bears on semilocal, Prüfer or valuation rings,
and the general domain remains open for the reason the section above gives.
-/

omit [IsDomain R] in
/-- **Every nonzero element divides a power of the product of a covering set of primes.** If a
finite set `t` meets every associate class of primes of a unique factorisation domain, then
`∏ t` is a denominator for the whole ring in the sense
`FormalSpectrum.surjective_awayToFractionRing_of_forall_dvd_pow` asks for.

`UniqueFactorizationMonoid.factors s` is a multiset of primes whose product is associated to `s`,
each of its members is associated to a member of `t` and therefore divides `∏ t`, and a product of
`Multiset.card` many elements, each dividing `∏ t`, divides that many-th power of `∏ t`. That last
step is Mathlib's
`Multiset.prod_dvd_prod_of_dvd` at the constant function; the specialised form
`s.prod ∣ m ^ Multiset.card s` is **not** in Mathlib — exact? on that goal fails — but it is one
simpa away from the lemma that is, so it is used inline rather than given a name of its own.

**No primality is asked of the members of `t`**, only that they cover. Primality enters on the
side of `UniqueFactorizationMonoid.factors`, and again where the product of `t` has to be shown
nonzero — which happens inside `FormalSpectrum.hasBoundedDenominators_iff_finite_primes` and not
here.

**`[UniqueFactorizationMonoid R]` is needed here, and not merely convenient**, by a witness rather
than by an argument: `FormalSpectrum.not_forall_forall_dvd_pow_prod`
(`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`) refutes this statement with that
instance deleted and nothing else changed. **The refuting `t` is the empty one.** This theorem
carries no `[IsDomain R]`, so with the instance gone it speaks about an arbitrary commutative ring,
and at `t = ∅` it says *a ring with no prime elements has every nonzero element a unit*. The ring
of all algebraic integers has no prime elements — every element is a square — and `2` is not a unit
of it. So no divisibility argument is involved in the refutation, and the witness is neither the
ultrapower, which has infinitely many prime classes and therefore satisfies no instance of the
hypothesis, nor a ring of integers of a number field, which is not closed under square roots. -/
theorem forall_dvd_pow_prod [UniqueFactorizationMonoid R] (t : Finset R)
    (hcov : ∀ p : R, Prime p → ∃ q ∈ t, Associated p q) :
    ∀ s : R, s ≠ 0 → ∃ k : ℕ, s ∣ (t.prod id) ^ k := by
  intro s hs
  refine ⟨Multiset.card (UniqueFactorizationMonoid.factors s), ?_⟩
  refine ((UniqueFactorizationMonoid.factors_prod hs).symm.dvd).trans ?_
  have hdvd : ∀ x ∈ UniqueFactorizationMonoid.factors s, id x ∣ (fun _ : R => t.prod id) x := by
    intro x hx
    obtain ⟨q, hq, hassoc⟩ := hcov x (UniqueFactorizationMonoid.prime_of_factor x hx)
    exact hassoc.dvd.trans (Finset.dvd_prod_of_mem id hq)
  simpa using Multiset.prod_dvd_prod_of_dvd (S := UniqueFactorizationMonoid.factors s) id
    (fun _ => t.prod id) hdvd

/-- **Finitely many primes up to associates give a single element that every nonzero element
divides a power of**: their product, through `FormalSpectrum.forall_dvd_pow_prod`.

This is the construction inside the backward direction of
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`, which is its one consumer here. It is
named because the *forward* composite is wanted too — at a unique factorisation domain the
denominator condition produces such an `m`, with **no countability hypothesis**, which is
`FormalSpectrum.exists_forall_dvd_pow_of_hasBoundedDenominators` in
`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower` — and a second consumer of a proof body
is a project-internal duplicate rather than a second consumer of a theorem.

The `m` is not canonical: it is a product of one chosen representative of each prime class, and
any associate of it, or any multiple, serves equally. Nothing downstream depends on the choice. -/
theorem exists_forall_dvd_pow_of_finite_primes [UniqueFactorizationMonoid R]
    (hfin : {a : Associates R | Prime a}.Finite) :
    ∃ m : R, m ≠ 0 ∧ ∀ s : R, s ≠ 0 → ∃ k : ℕ, s ∣ m ^ k := by
  classical
  choose rep hrep using fun a : Associates R => Associates.mk_surjective a
  set t : Finset R := hfin.toFinset.image rep with ht
  have hcov : ∀ p : R, Prime p → ∃ q ∈ t, Associated p q := by
    intro p hpp
    refine ⟨rep (Associates.mk p), Finset.mem_image_of_mem _ ?_, ?_⟩
    · exact (Set.Finite.mem_toFinset hfin).mpr (Associates.prime_mk.mpr hpp)
    · exact Associates.mk_eq_mk_iff_associated.mp (hrep (Associates.mk p)).symm
  have htne : t.prod id ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    have hpa : Prime a := (Set.Finite.mem_toFinset hfin).mp ha
    have hpr : Prime (Associates.mk (rep a)) := by rw [hrep a]; exact hpa
    exact (Associates.prime_mk.mp hpr).ne_zero
  exact ⟨t.prod id, htne, forall_dvd_pow_prod R t hcov⟩

/-- **The denominator condition at a unique factorisation domain is exactly "finitely many primes
up to associates".** This is where the two criteria of the section above meet, and it is the only
hypothesis under which anything on this tree makes them meet.

**The forward direction is the refuting criterion**, at a family extracted from an infinite set:
`Set.Infinite.natEmbedding` turns infinitely many prime associate classes into an injective
`ℕ`-indexed family of them, `Associates.mk_surjective` lifts each to a representative in `R`, and
injectivity of the embedding is exactly the *pairwise non-associated* hypothesis of
`FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated`.

**The backward direction is the sufficient criterion**, at the product of a set of representatives.
That whole construction is `FormalSpectrum.exists_forall_dvd_pow_of_finite_primes` above, which is
where `FormalSpectrum.forall_dvd_pow_prod` discharges the divisibility hypothesis and the product
is shown nonzero; what is left here is to pass through both spellings of the criterion —
divisibility, then surjectivity, then the condition — and the middle step costs nothing, since the
two spellings are one hypothesis at a fixed `m`
(`FormalSpectrum.surjective_awayToFractionRing_iff_forall_dvd_pow`).

`Associates.out` is not available in either — it needs
`[NormalizationMonoid R]`, which a bare unique factorisation domain does not carry — so the
representatives come from a choose on `Associates.mk_surjective`, in
`FormalSpectrum.exists_forall_dvd_pow_of_finite_primes`.

**`[UniqueFactorizationMonoid R]` is needed here, by a witness and not merely by the absence of a
proof without it.** An ultrapower of `ℤ` satisfies the condition and has infinitely many prime
associate classes, so this `↔` with the instance deleted is false:
`FormalSpectrum.not_forall_hasBoundedDenominators_iff_finite_primes` in
`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`, and
`FormalSpectrum.not_forall_hasBoundedDenominators_imp_finite_primes` for the sharper statement that
it is the **forward** direction that fails there. The witness is the same family that measures the
instance of `FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated`, read at
`Associates`; that the forward direction below turns an infinite set of classes back into such a
family is the inverse translation. **The backward direction is refuted too, and at a different
ring**: `FormalSpectrum.exists_forall_dvd_pow_of_finite_primes` does not survive without unique
factorisation, by `FormalSpectrum.not_forall_exists_forall_dvd_pow_of_finite_primes` in
`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`. The ultrapower cannot supply that one —
its prime classes are infinite and the hypothesis is that they are finite — so the witness there is
the ring of all algebraic integers, which has no prime elements at all
(`FormalSpectrum.finite_setOf_prime_associates_algInt`) and in which no nonzero element is a
clearing element (`FormalSpectrum.exists_ne_zero_forall_not_dvd_pow_algInt`). **The two directions
are refuted separately, at two different rings, and neither refutation bears on the other.**

The three values in this file are the three cases: a field is the empty set, a discrete valuation
ring the singleton, and `ℤ` the infinite one. Each is checked below as an `example` beside the
theorem it reproduces; **none of those proofs is replaced**, because each carries something this
does not — the field value needs no factorisation, the discrete-valuation-ring value exhibits the
uniformizer as the denominator, and `FormalSpectrum.not_hasBoundedDenominators_int` exhibits an
explicit family in `Frac ℤ` that defeats every `m`.

**On its own this is one conjunct**, exactly as `FormalSpectrum.HasBoundedDenominators` is:
through `FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators`
it decides the surjectivity half at the generic point of `R⟦X⟧` for every unique factorisation
domain. The other conjunct is
`FormalSpectrum.exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint`, which holds at that
point for every domain, so the two compose into a statement about the predicate itself there:
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_finite_primes`. **The predicate at any
other point is a different statement and is decided nowhere.** -/
theorem hasBoundedDenominators_iff_finite_primes [UniqueFactorizationMonoid R] :
    HasBoundedDenominators R ↔ {a : Associates R | Prime a}.Finite := by
  classical
  constructor
  · intro h
    by_contra hinf
    rw [Set.not_finite] at hinf
    let e : ℕ ↪ {a : Associates R | Prime a} := hinf.natEmbedding
    choose p hp using fun n : ℕ => Associates.mk_surjective (e n : Associates R)
    refine not_hasBoundedDenominators_of_primes_not_associated R p (fun n => ?_)
      (fun i j hij => ?_) h
    · exact Associates.prime_mk.mp (hp n ▸ (e n).2)
    · have hee : (e i : Associates R) = e j := by
        rw [← hp i, ← hp j]
        exact Associates.mk_eq_mk_iff_associated.mpr hij
      exact e.injective (Subtype.ext hee)
  · intro hfin
    obtain ⟨m, hm, hall⟩ := exists_forall_dvd_pow_of_finite_primes R hfin
    exact hasBoundedDenominators_of_surjective R hm
      (surjective_awayToFractionRing_of_forall_dvd_pow R hm hall)

/-! ### The collapse over a countable fraction field

The sufficient criterion above is not necessary at a general domain — an ultrapower of `ℤ`
satisfies the condition and no single `R[1/m]` is its fraction field
(`FormalSpectrum.hasBoundedDenominators_and_no_collapse_intUltrapower`, which refutes the
right-hand side of every theorem in this section at once) — and the reason
the section heading gives is a cardinality: `FormalSpectrum.HasBoundedDenominators` only ever sees
*countable* families (`FormalSpectrum.hasBoundedDenominators_iff_countable`), so a domain whose
fraction field needs uncountably many denominator types is not excluded by it. **That reason is
also the proof of this section.** When `Frac R` is itself countable there is no room for
uncountably many denominator types: the condition may be applied to the whole of `Frac R` at once,
and the criterion is then necessary as well as sufficient. So the countability hypothesis is not
incidental — it is exactly what the general case is missing, and the two sections locate the
difficulty in the same place.

**This decides no ring.** It trades one condition for a more elementary one — a single `m ≠ 0`
with `R[1/m]` already the whole fraction field — which a consumer can check by hand at a given
ring. Which rings satisfy *that* is still not determined here.

The hypothesis is on `Frac R` and not on `R`, because that is what the proof uses and it is the
weaker of the two. `Localization.countable_of_countable`, in `FormalSchemes.CountableLocalization`,
discharges it from `[Countable R]`, which is the form a consumer at a concrete ring has.
-/

/-- **Over a countable fraction field the sufficient criterion is necessary too**: the denominator
condition holds exactly when one `R[1/m]` is already the whole of `Frac R`.

Forwards is the only new content, and it is
`FormalSpectrum.hasBoundedDenominators_iff_countable` applied at `Set.univ`: the whole of `Frac R`
is a countable set, so a single `m` serves all of it, and
`FormalSpectrum.mem_range_awayToFractionRing_iff` turns *cleared by a power of `m`* into
*in the image of `R[1/m]`*, which is surjectivity. Backwards is
`FormalSpectrum.hasBoundedDenominators_of_surjective` and nothing else.

**The right-hand side has a localization-free reading too.** At a fixed `m` the surjection is the
same hypothesis as *every nonzero element of `R` divides a power of `m`*
(`FormalSpectrum.surjective_awayToFractionRing_iff_forall_dvd_pow`), at every domain and with no
countability, so a consumer may check whichever is easier at the ring in hand. That does not
weaken this theorem's hypothesis: what `[Countable (FractionRing R)]` buys is the quantifier over
`m`, not the form of the condition at one `m`.

**Necessity is what the hypothesis buys.** Sufficiency holds at every domain and is proved above;
this direction is **false** at a general domain, and the counterexample is a theorem rather than a
remark: `FormalSpectrum.hasBoundedDenominators_and_not_exists_surjective_intUltrapower` in
`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower` asserts this theorem's left-hand side and
the negation of its right-hand side at an ultrapower of `ℤ`. The obstruction named there — that the
condition only ever sees countable families — is precisely what `[Countable (FractionRing R)]`
removes.

The hypothesis is on the fraction field rather than on `R`: it is the weaker assumption, and it is
what the proof uses. At a concrete ring it comes from `[Countable R]` through
`Localization.countable_of_countable`. -/
theorem hasBoundedDenominators_iff_exists_surjective [Countable (FractionRing R)] :
    HasBoundedDenominators R ↔
      ∃ m : R, ∃ hm : m ≠ 0, Function.Surjective (awayToFractionRing R m hm) := by
  constructor
  · intro h
    obtain ⟨m, hm, hall⟩ := (hasBoundedDenominators_iff_countable R).mp h Set.univ
      Set.countable_univ
    exact ⟨m, hm, fun y => (mem_range_awayToFractionRing_iff R m hm y).mpr
      (hall y (Set.mem_univ y))⟩
  · rintro ⟨m, hm, hs⟩
    exact hasBoundedDenominators_of_surjective R hm hs

/-- **The same collapse with the localization removed**, matching the spelling of the definition:
over a countable fraction field one `m ≠ 0` clears *every* element of `Frac R`, not merely every
countable family.

`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` read through
`FormalSpectrum.mem_range_awayToFractionRing_iff` at each element, exactly as
`FormalSpectrum.hasBoundedDenominators_iff_range` is the localized reading of the definition.

Both spellings are shipped because they are wanted in different places. The localized one is the
form the criteria above are stated in, and is what composes with
`FormalSpectrum.hasBoundedDenominators_of_surjective`. This one is elementary arithmetic in `R`
and `Frac R`, names no localization, and is the one that says what the collapse *is*: the
quantifier order of `FormalSpectrum.HasBoundedDenominators` stops mattering, because the `m` may
be chosen before the family.

**The hypothesis is needed here too**, and in this spelling:
`FormalSpectrum.not_exists_denominator_intUltrapower` in
`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower` refutes exactly the right-hand side below
at a ring where the left-hand side holds. -/
theorem hasBoundedDenominators_iff_exists_denominator [Countable (FractionRing R)] :
    HasBoundedDenominators R ↔
      ∃ m : R, m ≠ 0 ∧ ∀ y : FractionRing R, ∃ k : ℕ,
        algebraMap R (FractionRing R) (m ^ k) * y ∈
          Set.range (algebraMap R (FractionRing R)) := by
  rw [hasBoundedDenominators_iff_exists_surjective R]
  constructor
  · rintro ⟨m, hm, hs⟩
    exact ⟨m, hm, fun y => (mem_range_awayToFractionRing_iff R m hm y).mp (hs y)⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨m, hm, fun y => (mem_range_awayToFractionRing_iff R m hm y).mpr (h y)⟩

/-- **The collapse with no localization and no fraction field left in the statement**: over a
countable fraction field the denominator condition is pure divisibility in `R`. Some `m ≠ 0` is
such that every nonzero `s : R` divides a power of it.

`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` read through
`FormalSpectrum.surjective_awayToFractionRing_iff_forall_dvd_pow` at the `m` it produces, in both
directions.

**A third spelling of the collapse, and this is what it is for.**
`FormalSpectrum.hasBoundedDenominators_iff_exists_denominator` is already the arithmetic reading,
but its right-hand side still quantifies over `Frac R` and still names
`Set.range (algebraMap R (FractionRing R))`. This one names no fraction field, no localization, no
surjection and no range: it is four quantifiers over `R` and `ℕ`, an inequation and a divisibility,
and it can be checked at a ring by hand. It is also the form the values in this file actually
instantiate — `FormalSpectrum.hasBoundedDenominators_of_field` is `m = 1` and `k = 0`, and
`FormalSpectrum.hasBoundedDenominators_of_isDiscreteValuationRing` is a uniformizer — so the
sufficient criterion `FormalSpectrum.hasBoundedDenominators_of_forall_dvd_pow` and the condition
are, under this hypothesis, literally the same words.

Shipped for the reason
`FormalSpectrum.hasBoundedDenominators_iff_exists_denominator` is shipped beside
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective`: the spellings are wanted in
different places, and what changes between them is which objects a consumer has to have in hand.

**The countability is spent on the quantifier over `m` and on nothing else.** At a fixed `m` the
divisibility form and the surjectivity form are the same hypothesis at every domain
(`FormalSpectrum.surjective_awayToFractionRing_iff_forall_dvd_pow`); it is
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` that needs
`[Countable (FractionRing R)]`, and this inherits it from there — including the fact that it
cannot be dropped, `FormalSpectrum.not_exists_forall_dvd_pow_intUltrapower` refuting the right-hand
side below at a ring satisfying the condition.

**A different hypothesis buys the same conclusion.** At a unique factorisation domain, with no
countability whatever, `FormalSpectrum.exists_forall_dvd_pow_of_hasBoundedDenominators` produces
the same `m` from `FormalSpectrum.exists_forall_dvd_pow_of_finite_primes` above. The two
hypotheses are incomparable and neither is necessary for the `m`, each theorem reaching it without
the other's. Neither can be **dropped** from the theorem that carries it, which is a different
statement and now known of both: the paragraph above says it of the countability here, and
`FormalSpectrum.not_forall_hasBoundedDenominators_imp_exists_forall_dvd_pow`
(`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`) says it of the unique factorisation
there, refuting that implication with `[UniqueFactorizationMonoid R]` deleted. Neither bears on
`FormalSpectrum.exists_forall_dvd_pow_of_finite_primes`, whose instance is measured separately and
at a different ring by `FormalSpectrum.not_forall_exists_forall_dvd_pow_of_finite_primes` in that
same file, and is **needed** there too. -/
theorem hasBoundedDenominators_iff_forall_dvd_pow [Countable (FractionRing R)] :
    HasBoundedDenominators R ↔
      ∃ m : R, m ≠ 0 ∧ ∀ s : R, s ≠ 0 → ∃ k : ℕ, s ∣ m ^ k := by
  rw [hasBoundedDenominators_iff_exists_surjective R]
  constructor
  · rintro ⟨m, hm, hs⟩
    exact ⟨m, hm, (surjective_awayToFractionRing_iff_forall_dvd_pow R hm).mp hs⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨m, hm, (surjective_awayToFractionRing_iff_forall_dvd_pow R hm).mpr h⟩

/-- **The denominator condition is *some `R[1/m]` is already a field*.** Over a countable fraction
field that is the whole of it, and it is the most compact statement of the condition in this file.

`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` read through
`FormalSpectrum.surjective_awayToFractionRing_iff_isField` at the `m` it produces. Composed with
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators` below it says
that, at a domain with a countable fraction field, `FormalSpectrum.IsStalkLimit` holds at
`(X) ⊆ R⟦X⟧` at the generic point exactly when some single-element localization of `R` is a field.

The right-hand side mentions neither `Frac R` nor any map out of `R[1/m]`: it is a property of the
ring `R[1/m]` on its own. That is what distinguishes it from the two spellings above, which name a
surjection onto `Frac R` and a range inside `Frac R` respectively.

**It decides no ring, and it is not a classification.** It trades the condition for another one
and says nothing about which domains meet that one. What decides rings is elsewhere: the values at
a field, at `ℤ` and at a discrete valuation ring, and — read through this `↔` — the classification
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`, which at a countable unique
factorisation domain turns *some `R[1/m]` is a field* into *finitely many primes up to associates*.

**Only one of the two directions needs the hypothesis**, exactly as for
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective`, from which this inherits it.
Sufficiency holds at every domain with no countability and has a name of its own,
`FormalSpectrum.hasBoundedDenominators_of_isField`; necessity is what
`[Countable (FractionRing R)]` buys and is false without it, by
`FormalSpectrum.not_exists_isField_away_intUltrapower` in
`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`, which refutes the right-hand side below
at a ring where the left-hand side holds. -/
theorem hasBoundedDenominators_iff_exists_isField [Countable (FractionRing R)] :
    HasBoundedDenominators R ↔ ∃ m : R, m ≠ 0 ∧ IsField (Localization.Away m) := by
  rw [hasBoundedDenominators_iff_exists_surjective R]
  constructor
  · rintro ⟨m, hm, hs⟩
    exact ⟨m, hm, (surjective_awayToFractionRing_iff_isField R hm).mp hs⟩
  · rintro ⟨m, hm, hf⟩
    exact ⟨m, hm, (surjective_awayToFractionRing_iff_isField R hm).mpr hf⟩

/-- **Where the classification and the collapse overlap they agree**, and this checks it rather
than asserting it: at a domain that is both a unique factorisation domain and has a countable
fraction field, *finitely many primes up to associates* and *some `R[1/m]` is already `Frac R`*
are equivalent, both being `FormalSpectrum.HasBoundedDenominators`.

**A consistency check on two independently derived statements, and it is deliberately not a named
theorem.** The two hypotheses are incomparable — `ℂ[X]` is a unique factorisation domain with an
uncountable fraction field, and an order in a number field of class number greater than one has a
countable fraction field and is not factorial — so neither of the two results above subsumes the
other, and their composite is a statement about the intersection that belongs to neither. It is an
`example` for the same reason the three values of the classification are: it proves nothing that
does not already have a name, and its whole content is that the two names fit together.

Nothing here computes which countable unique factorisation domains satisfy either side. -/
example [UniqueFactorizationMonoid R] [Countable (FractionRing R)] :
    {a : Associates R | Prime a}.Finite ↔
      ∃ m : R, ∃ hm : m ≠ 0, Function.Surjective (awayToFractionRing R m hm) :=
  (hasBoundedDenominators_iff_finite_primes R).symm.trans
    (hasBoundedDenominators_iff_exists_surjective R)

/-! ### The value at a field -/

/-- **A field satisfies the denominator condition**, with `m = 1` and `k = 0`: nothing needs a
denominator, because `K → Frac K` is already surjective.

This is a value of the *condition*, hence of the surjectivity half at the generic point of
`K⟦X⟧`. It is **not** `FormalSpectrum.isStalkLimit_powerSeriesX_field`, which is a value of the
whole predicate `FormalSpectrum.IsStalkLimit` at every point of `Spf (k⟦X⟧, (X))` and is proved by
a different route: over a field that space has one point, every `g` outside
`FormalSpectrum.pointPrime` is a unit, and no witness is produced. The two do agree where they
meet — the condition at a field also follows from that theorem through
`FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators`, and
the proof below uses none of it.

`FormalSpectrum.hasBoundedDenominators_of_forall_dvd_pow` at `m = 1`, where the divisibility
hypothesis is `s ∣ 1 ^ 0` and holds because a nonzero element of a field is a unit. The statement
is unchanged; the earlier proof produced the same `m = 1` and `k = 0` by writing out the quotient
`r / s` by hand. -/
theorem hasBoundedDenominators_of_field (K : Type u) [Field K] : HasBoundedDenominators K :=
  hasBoundedDenominators_of_forall_dvd_pow K (one_ne_zero (α := K))
    fun _ hs => ⟨0, (isUnit_iff_ne_zero.mpr hs).dvd⟩

/-- A field is the **empty** case of `FormalSpectrum.hasBoundedDenominators_iff_finite_primes`:
every nonzero element is a unit, so there is no prime at all and the set of prime associate
classes is empty.

**A consistency check on the classification, not a replacement for the theorem above.** The proof
above needs no factorisation — a field is a unique factorisation monoid, but nothing about the
value uses it — and it produces the denominator `m = 1` explicitly, where this produces it from a
finite set of representatives of an empty set. It is an `example` because it proves a statement
that already has a name. -/
example (K : Type u) [Field K] : HasBoundedDenominators K := by
  refine (hasBoundedDenominators_iff_finite_primes K).mpr ?_
  convert Set.finite_empty
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro ha
  obtain ⟨x, rfl⟩ := Associates.mk_surjective a
  exact (Associates.prime_mk.mp ha).not_unit
    (isUnit_iff_ne_zero.mpr (Associates.prime_mk.mp ha).ne_zero)

/-! ### The predicate itself, at the generic point

Everything above is about `FormalSpectrum.HasBoundedDenominators`, which is **one conjunct** of
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff`. At this one point that qualification
can be dropped, and the reason is not a new argument: the other conjunct was proved not at one ring
but at the generic point of *every* domain
(`FormalSpectrum.exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint`), so wherever the
criterion applies at all it is already discharged and the conjunction collapses onto the condition.
The two statements below are that composition, and their whole content is that it is legitimate.
-/

/-- **`FormalSpectrum.IsStalkLimit` at the generic point of `R⟦X⟧` is exactly the denominator
condition**, at every domain — no factorisation, no countability, no Noetherian hypothesis — and
with neither a completion nor a power series left on the right-hand side.

**What makes the collapse possible is not a new argument.**
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff` is a plain conjunction, and its two
conjuncts are settled in the same generality:

* the **injectivity** half is
  `FormalSpectrum.exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint`, a theorem at the
  generic point of *every* domain rather than at one ring (issue 1759, PR #589), so it is free
  wherever the criterion can be stated at all;
* the **surjectivity** half is `FormalSpectrum.HasBoundedDenominators` on the nose, by
  `FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators`
  (issue 1776, PR #595), whose left-hand side is literally the second conjunct of the criterion.

Had the injectivity half been proved only at `ℤ`, or only at a discrete valuation ring, this would
not be available at a general domain and there would be a second thing to prove.

**One point.** This says nothing at any other point of `Spf (R⟦X⟧, (X))`, nothing at any other
ideal of definition, and nothing at a formal spectrum whose ring is not a power series ring; see
the module docstring. -/
theorem isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators :
    IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) ↔
      HasBoundedDenominators R :=
  (isStalkLimit_powerSeriesXGenericPoint_iff R).trans
    ⟨fun h =>
      (exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators R).mp h.2,
     fun h =>
      ⟨exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint R,
        (exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators R).mpr h⟩⟩

/-- **At a unique factorisation domain, the stalk of the completion is the completion of the stalk
at the generic point of `R⟦X⟧` exactly when `R` has finitely many primes up to associates.**

`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators` composed with
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`. It is the classification of the
condition read as a statement about the predicate, and the three values in this file are its three
cases: a field is the empty set, a discrete valuation ring the singleton, and `ℤ` the infinite one.

The factorisation hypothesis is spent entirely by the classification — the theorem above carries
none of it — so away from a unique factorisation domain **this** cardinality form is simply not
available. Nothing here decides semilocal, Prüfer or valuation rings.

**A Dedekind domain has a cardinality form of its own, and it is a different one for exactly the
reason this file used to give for having none**: a Dedekind domain is a statement about **ideals**,
and a nonprincipal maximal ideal contributes no prime element at all, so what decides it is
`{I : Ideal R | I.IsPrime}` and not the primes up to associates. That is
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_finite_primeIdeals`
(`FormalSchemes.StructureSheafStalkPowerSeriesDedekind`), this theorem's twin at that hypothesis.
It is **not** derived from this one and does not derive this one: `[UniqueFactorizationMonoid R]`
and `[IsDedekindDomain R]` neither contains the other, and where both hold the two counts still
differ by `⊥`. -/
theorem isStalkLimit_powerSeriesXGenericPoint_iff_finite_primes
    [UniqueFactorizationMonoid R] :
    IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) ↔
      {a : Associates R | Prime a}.Finite :=
  (isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators R).trans
    (hasBoundedDenominators_iff_finite_primes R)

end Generic

/-! ### The counterexample at `ℤ` -/

section Int

/-- **The witness**: the power series over `Frac ℤ` whose `n`-th coefficient is `1 / (n + 1)`.

Any element whose coefficients need infinitely many primes in their denominators would do — the
older docstrings on this cluster propose `∑ X ^ n / p n` for `p n` the `n`-th prime — but
`1 / (n + 1)` needs no enumeration of the primes: to defeat a given `m` one reads the coefficient
in degree `p - 1` for a prime `p` larger than `|m|`. -/
def unitFractionSeries : PowerSeries (FractionRing ℤ) :=
  PowerSeries.mk fun n => IsLocalization.mk' (FractionRing ℤ) 1
    ⟨(n : ℤ) + 1, mem_nonZeroDivisors_of_ne_zero (by positivity)⟩

/-- **`FormalSpectrum.unitFractionSeries` is not `PowerSeries.map (R[1/m] → Frac ℤ)` of anything**,
for any `m ≠ 0`.

Pick a prime `p > |m|` (`Nat.exists_infinite_primes`) and look at the coefficient in degree
`p - 1`, which is `1 / p`. If it were `r / m ^ k` then `m ^ k = p * r` in `ℤ`, so `p` divides `m`
and `p ≤ |m|`. This is the arithmetic the whole file exists to reach: the image of `ℤ[1/m]` in `ℚ`
misses `1 / p` for all but finitely many primes, so no single basic open `D(m)` can carry a
section whose germ is this one. -/
theorem unitFractionSeries_notMem_range (m : ℤ) (hm : m ≠ 0)
    (g : PowerSeries (Localization.Away m)) :
    PowerSeries.map (awayToFractionRing ℤ m hm) g ≠ unitFractionSeries := by
  intro h
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (m.natAbs + 1)
  have hcast : ((p - 1 : ℕ) : ℤ) + 1 = (p : ℤ) := by
    have h1 := hp.two_le
    omega
  have hcoeff := congrArg (PowerSeries.coeff (p - 1)) h
  rw [PowerSeries.coeff_map, unitFractionSeries, PowerSeries.coeff_mk] at hcoeff
  obtain ⟨⟨r, y⟩, hy⟩ := IsLocalization.mk'_surjective (Submonoid.powers m)
    (PowerSeries.coeff (p - 1) g)
  obtain ⟨k, hk⟩ := y.2
  have hspec : algebraMap ℤ (Localization.Away m) (y : ℤ) *
      PowerSeries.coeff (p - 1) g = algebraMap ℤ (Localization.Away m) r := by
    rw [← show IsLocalization.mk' (Localization.Away m) r y = PowerSeries.coeff (p - 1) g from hy]
    exact IsLocalization.mk'_spec' _ r y
  have himg := congrArg (awayToFractionRing ℤ m hm) hspec
  rw [map_mul, awayToFractionRing_algebraMap, awayToFractionRing_algebraMap, hcoeff] at himg
  set P : ℤ := ((p - 1 : ℕ) : ℤ) + 1 with hPdef
  set hP : P ∈ nonZeroDivisors ℤ := mem_nonZeroDivisors_of_ne_zero (by positivity) with _hPmem
  set mu : FractionRing ℤ := IsLocalization.mk' (FractionRing ℤ) 1 ⟨P, hP⟩ with hmu
  have hpspec : algebraMap ℤ (FractionRing ℤ) P * mu = 1 := by
    have h1 := IsLocalization.mk'_spec' (FractionRing ℤ) (1 : ℤ) (⟨P, hP⟩ : nonZeroDivisors ℤ)
    rw [map_one] at h1
    exact h1
  have hyPr : (y : ℤ) = P * r := by
    refine IsFractionRing.injective ℤ (FractionRing ℤ) ?_
    rw [map_mul]
    calc algebraMap ℤ (FractionRing ℤ) (y : ℤ)
        = algebraMap ℤ (FractionRing ℤ) (y : ℤ) *
            (algebraMap ℤ (FractionRing ℤ) P * mu) := by rw [hpspec, mul_one]
      _ = algebraMap ℤ (FractionRing ℤ) P *
            (algebraMap ℤ (FractionRing ℤ) (y : ℤ) * mu) := by ring
      _ = algebraMap ℤ (FractionRing ℤ) P * algebraMap ℤ (FractionRing ℤ) r := by rw [himg]
  have hpdvd : (p : ℤ) ∣ m ^ k :=
    ⟨r, by rw [show m ^ k = (y : ℤ) from hk, hyPr, hcast]⟩
  have hdvdNat : p ∣ m.natAbs ^ k := by
    have h1 := Int.natAbs_dvd_natAbs.mpr hpdvd
    simpa [Int.natAbs_pow] using h1
  have hle : p ≤ m.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hm) (hp.dvd_of_dvd_pow hdvdNat)
  omega

/-- **`ℤ` does not satisfy the denominator condition.** The coefficients of
`FormalSpectrum.unitFractionSeries` are `1 / (n + 1)`, and no single `m ≠ 0` clears all of them:
a prime `p > |m|` divides no power of `m`.

This is the arithmetic of `FormalSpectrum.unitFractionSeries_notMem_range` carried from
coefficients back to a series by
`PowerSeries.exists_map_eq_iff_forall_coeff_mem_range`, and it mentions no completion, no
localization of `ℤ⟦X⟧` and no formal geometry. The geometric refutation below is this statement
read through
`FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators`. -/
theorem not_hasBoundedDenominators_int : ¬ HasBoundedDenominators ℤ := by
  intro h
  obtain ⟨m, hm, hall⟩ := (hasBoundedDenominators_iff_range ℤ).mp h
    fun n => PowerSeries.coeff n unitFractionSeries
  obtain ⟨g, hg⟩ := (PowerSeries.exists_map_eq_iff_forall_coeff_mem_range
    (awayToFractionRing ℤ m hm) unitFractionSeries).mpr hall
  exact unitFractionSeries_notMem_range m hm g hg

/-- `ℤ` is an instance of `FormalSpectrum.not_hasBoundedDenominators_of_primes`: a family of
primes with `p n > n` is divisible by no single `m`, since a divisor of `m ≠ 0` is at most `|m|`.

**A consistency check on the criterion, not a replacement for the theorem above.** The proof above
is kept, and is the only place on this tree where an element of `Frac ℤ⟦X⟧` that defeats every `m`
is written down: `FormalSpectrum.unitFractionSeries` is a witness, and this is an application of a
criterion whose own witness is `Nat.exists_infinite_primes`. Deleting either for the other would
lose something. It is an `example` because it proves a statement that already has a name.

`Nat.exists_infinite_primes` is the whole of the arithmetic, and it is Euclid's theorem — the same
fact the docstring above states as *"a prime `p > |m|` divides no power of `m`"*. -/
example : ¬ HasBoundedDenominators ℤ := by
  classical
  choose p hle hp using fun n : ℕ => Nat.exists_infinite_primes (n + 1)
  refine not_hasBoundedDenominators_of_primes ℤ (fun n => (p n : ℤ))
    (fun n => Nat.prime_iff_prime_int.mp (hp n)) fun m hm => ⟨m.natAbs, fun hdvd => ?_⟩
  have hle' : (p m.natAbs : ℤ) ≤ |m| :=
    Int.le_of_dvd (abs_pos.mpr hm) ((dvd_abs _ _).mpr hdvd)
  have hgt : (m.natAbs : ℤ) < (p m.natAbs : ℤ) := by
    exact_mod_cast Nat.lt_of_succ_le (hle m.natAbs)
  rw [← Int.natCast_natAbs] at hle'
  omega

/-- `ℤ` is the **infinite** case of
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`: read through the classification, the
theorem above says exactly that `ℤ` has infinitely many primes up to associates, which is Euclid's
theorem.

**A consistency check, and the arrow runs the other way from the two above.** The field and
discrete-valuation-ring cases compute the set of prime associate classes and read the condition
off it; here the condition is already refuted, with an explicit witness in `Frac ℤ`, and the
classification turns that refutation into the cardinality statement. It is one of **four**
accounts of `ℤ` in this file and all four are kept: `FormalSpectrum.unitFractionSeries` is the
witness, the `example` above is Euclid used as an instance of the refuting criterion, this is
Euclid recovered from the witness, and
`FormalSpectrum.not_exists_surjective_awayToFractionRing_int` below is the same refutation with
the power series stripped off. -/
example : ¬ {a : Associates ℤ | Prime a}.Finite :=
  fun h => not_hasBoundedDenominators_int ((hasBoundedDenominators_iff_finite_primes ℤ).mpr h)

/-- **No single `ℤ[1/m]` is `ℚ`.** For every `m ≠ 0` the map `ℤ[1/m] → ℚ` misses something, so
there is no one integer whose inversion produces the whole of the rationals.

This is the arithmetic content of the whole refutation with every trace of formal geometry
removed: no power series, no completion, no localization of `ℤ⟦X⟧`, no adic ring. It is a
**corollary of `FormalSpectrum.not_hasBoundedDenominators_int`** and not an independent proof —
the arithmetic is all there, in `FormalSpectrum.unitFractionSeries`, and this only reads it off.

It is the reverse half of `FormalSpectrum.hasBoundedDenominators_iff_exists_surjective`
contraposed, and it is stated with **no countability hypothesis**, because that half is
`FormalSpectrum.hasBoundedDenominators_of_surjective` and holds at every domain. `ℤ` does satisfy
the hypothesis — `Countable (FractionRing ℤ)` by `Localization.countable_of_countable` — so this
is a corollary of the `↔` as well; the direct route is taken because it assumes less.

This is the **fourth** account of `ℤ` in this file and none of the four replaces another.
`FormalSpectrum.not_hasBoundedDenominators_int` is the theorem, with an explicit family in
`Frac ℤ` that defeats every `m`; the first `example` above is Euclid used as an instance of the
refuting criterion `FormalSpectrum.not_hasBoundedDenominators_of_primes`; the second is Euclid
recovered from that witness through the classification; and this is the same refutation with the
power series stripped off, which is the form an arithmetic reader recognises. -/
theorem not_exists_surjective_awayToFractionRing_int :
    ¬ ∃ m : ℤ, ∃ hm : m ≠ 0, Function.Surjective (awayToFractionRing ℤ m hm) :=
  fun ⟨_, hm, hs⟩ =>
    not_hasBoundedDenominators_int (hasBoundedDenominators_of_surjective ℤ hm hs)

/-- **No localization of `ℤ` at the powers of a single nonzero element is a field.** Not `ℤ[1/2]`,
not `ℤ[1/6]`, not `ℤ[1/n]` for any `n ≠ 0`: some prime is always left uninverted.

`FormalSpectrum.not_exists_surjective_awayToFractionRing_int` read through
`FormalSpectrum.surjective_awayToFractionRing_iff_isField` at the `m` the existential supplies. All
of the arithmetic is in `FormalSpectrum.unitFractionSeries`, as it is for the three accounts of `ℤ`
above; this reads it off and adds nothing to it.

**This is a named theorem rather than an `example`, and the reason is the theorem one paragraph
above.** `FormalSpectrum.not_exists_surjective_awayToFractionRing_int` has exactly this status —
a corollary of `FormalSpectrum.not_hasBoundedDenominators_int` with the formal geometry stripped
off — and is named. This one strips off one thing more: its statement mentions no map at all, so it
is a statement about the rings `ℤ[1/m]` themselves, and it is the form in which the fact is
recognisable without any of this file's definitions. Naming it is what makes it greppable from
outside the `FormalSpectrum` namespace.

**Like the theorem above, this needs no countability**, and the proof is chosen so that it does
not. `FormalSpectrum.hasBoundedDenominators_iff_exists_isField` would also prove it in one line,
and the `[Countable (FractionRing ℤ)]` instance it needs is found without help, from
`Localization.countable_of_countable`; but that route assumes strictly more, so it is not taken.
`FormalSpectrum.surjective_awayToFractionRing_iff_isField` being stated at one **fixed** `m` is
what makes the cheap route work rather than what would block it: instantiate it at the `m` the
existential hands over, and the two existentials match term for term. So this statement and
`FormalSpectrum.not_exists_surjective_awayToFractionRing_int` stand on the same footing: each is
`FormalSpectrum.not_hasBoundedDenominators_int` with one more layer stripped off, and neither
spends the countability of `ℚ` to get there. -/
theorem not_exists_isField_localizationAway_int :
    ¬ ∃ m : ℤ, m ≠ 0 ∧ IsField (Localization.Away m) :=
  fun ⟨m, hm, hf⟩ =>
    not_exists_surjective_awayToFractionRing_int
      ⟨m, hm, (surjective_awayToFractionRing_iff_isField ℤ hm).mpr hf⟩

/-- **The surjectivity half of `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff` fails at
`ℤ`.**

It fails exactly where `FormalSchemes.StructureSheafStalkPowerSeriesGeneric` isolated the
difficulty: not at any one level of the stalk tower, where
`FormalSpectrum.exists_awayToAtPrimeLevel_eq` says there is never an obstruction, but in the
passage to the limit, where one `f` must serve every level at once. Read through the two
identifications the half says every element of `ℚ⟦X⟧` lies in `ℤ[1/m]⟦X⟧` for a single `m ≠ 0`,
and `FormalSpectrum.unitFractionSeries` does not. That reading is a theorem —
`FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators` —
and this proof is that theorem at `FormalSpectrum.not_hasBoundedDenominators_int`, which carries
all of the arithmetic.

This is stated separately from
`FormalSpectrum.not_isStalkLimit_powerSeriesXIntGenericPoint` because it is strictly more
informative: it names the half that fails, and the other half holds
(`FormalSpectrum.exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint`). -/
theorem not_surjective_powerSeriesXIntGenericPoint :
    ¬ ∀ b : AdicCompletion (pointIdeal (powerSeriesXIdeal ℤ) (powerSeriesXGenericPoint ℤ))
        (Localization.AtPrime (pointPrime (powerSeriesXIdeal ℤ) (powerSeriesXGenericPoint ℤ))),
      ∃ f, ∃ (hf : constantCoeff f ≠ 0),
        ∃ a, awayToAtPrimeCompletion (powerSeriesXIdeal ℤ) (powerSeriesXGenericPoint ℤ)
          (fg_powerSeriesXIdeal ℤ)
          ((mem_basicOpen_powerSeriesXGenericPoint_iff ℤ f).mpr hf) a = b := fun hsurj =>
  not_hasBoundedDenominators_int
    ((exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators ℤ).mp hsurj)

/-- **`FormalSpectrum.IsStalkLimit` is false at `(X) ⊆ ℤ⟦X⟧` at the generic point.**

This is the first negative value of the predicate anywhere: the three values that predate this file
— `FormalSpectrum.isStalkLimit_bot`, `FormalSpectrum.isStalkLimit_of_isNilpotent` and
`FormalSpectrum.isStalkLimit_powerSeriesX_field` — are all positive, and all at points where the
colimit over basic opens does not move. It is **not** the case that the predicate is negative
wherever the colimit moves: `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint`, below, is
positive at the generic point of a discrete valuation ring.

The whole of the failure is the surjectivity half
(`FormalSpectrum.not_surjective_powerSeriesXIntGenericPoint`), which is all this proof uses.

**What this does not say.** It does not say `FormalSpectrum.IsStalkLimit` is false — the positive
values stand, one of them below, and this is one point of one ring. It says nothing about EGA I
10.8, whose hypotheses this tree's predicate does not carry; see the module docstring. -/
theorem not_isStalkLimit_powerSeriesXIntGenericPoint :
    ¬ IsStalkLimit (powerSeriesXIdeal ℤ) (powerSeriesXGenericPoint ℤ) := fun h =>
  not_surjective_powerSeriesXIntGenericPoint
    ((isStalkLimit_powerSeriesXGenericPoint_iff ℤ).mp h).2

/-- The same value read off
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`, as a
**consistency check** on that characterisation.

**The proof above is not replaced and must not be.** It refutes the predicate by refuting the
surjectivity half, and that refutation exhibits `FormalSpectrum.unitFractionSeries`, an explicit
element of the completion that defeats every `m`; a corollary of a characterisation exhibits
nothing. This is an `example` for that reason, and because it proves a statement that already has
a name. -/
example : ¬ IsStalkLimit (powerSeriesXIdeal ℤ) (powerSeriesXGenericPoint ℤ) := fun h =>
  not_hasBoundedDenominators_int
    ((isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators ℤ).mp h)

/-- **The refutation is sharp: `FormalSpectrum.IsStalkLimit` fails at `(X) ⊆ ℤ⟦X⟧` in the
surjectivity half only.** The two conjuncts below are, verbatim, the two components of
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff` at `R = ℤ`: the first holds and the
second does not.

A conjunction can be false for a boring reason, and this says that is not what happened. The
injectivity half is not merely true here by accident of the point: it holds at the generic point
of every domain, by
`FormalSpectrum.exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint`, and what defeats
the predicate is that `ℚ⟦X⟧` is not the union of the `ℤ[1/m]⟦X⟧`. -/
theorem injective_and_not_surjective_powerSeriesXIntGenericPoint :
    (∀ (f : PowerSeries ℤ) (hf : constantCoeff f ≠ 0)
        (a : awayCompletion (powerSeriesXIdeal ℤ) f),
        awayToAtPrimeCompletion (powerSeriesXIdeal ℤ) (powerSeriesXGenericPoint ℤ)
            (fg_powerSeriesXIdeal ℤ)
            ((mem_basicOpen_powerSeriesXGenericPoint_iff ℤ f).mpr hf) a = 0 →
          ∃ e, ∃ (_ : constantCoeff e ≠ 0)
            (hle : basicOpen (powerSeriesXIdeal ℤ) e ≤ basicOpen (powerSeriesXIdeal ℤ) f),
            awayCompletionRestrict (powerSeriesXIdeal ℤ) f e (fg_powerSeriesXIdeal ℤ) hle a = 0) ∧
      ¬ ∀ b : AdicCompletion (pointIdeal (powerSeriesXIdeal ℤ) (powerSeriesXGenericPoint ℤ))
          (Localization.AtPrime (pointPrime (powerSeriesXIdeal ℤ) (powerSeriesXGenericPoint ℤ))),
        ∃ f, ∃ (hf : constantCoeff f ≠ 0),
          ∃ a, awayToAtPrimeCompletion (powerSeriesXIdeal ℤ) (powerSeriesXGenericPoint ℤ)
            (fg_powerSeriesXIdeal ℤ)
            ((mem_basicOpen_powerSeriesXGenericPoint_iff ℤ f).mpr hf) a = b :=
  ⟨exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint ℤ,
    not_surjective_powerSeriesXIntGenericPoint⟩

end Int

/-! ### The positive value at a discrete valuation ring

The refutation above needs infinitely many primes. Read through the two identifications the
surjectivity half asks that every element of `(Frac R)⟦X⟧` have all of its coefficients in a
single `R[1/m]`, and `FormalSpectrum.unitFractionSeries` defeats every `m` because `ℤ` has
infinitely many primes to put in a denominator. **A discrete valuation ring has one**, and there
the half is not merely true but trivially so, uniformly in the element: for a uniformizer `ϖ` the
ring `R[1/ϖ]` is already all of `Frac R`.

So this section puts a *positive* value in a file named for a counterexample. That is deliberate
and not an accident of where the work landed: both values are read through the same two
identifications and through the same
`FormalSpectrum.atPrimeCompletionEquiv_awayToAtPrimeCompletion`, run in opposite directions, and
the contrast is the finding. Splitting them into two files would put the one statement that needs
both of them in neither.
-/

section DiscreteValuationRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **`FormalSpectrum.awayToFractionRing` is surjective at a uniformizer**: inverting `ϖ` alone
already gives the whole fraction field.

This is the discrete-valuation-ring statement and it is where the contrast with `ℤ` lives. The
valuation is `ℤ`-valued and `ϖ` generates the value group, so every nonzero `x : Frac R` is
`u • algebraMap ϖ ^ n` for a unit `u : Rˣ` and an `n : ℤ`
(`IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible`); for `n ≥ 0` the preimage is
the image of `u * ϖ ^ n` and for `n < 0` it is `IsLocalization.mk' u ϖ ^ (-n)`. Over `ℤ` no single
`m` can do this — that is `FormalSpectrum.unitFractionSeries_notMem_range` — and the difference is
that `ℤ` has infinitely many primes and a discrete valuation ring has one.

Stated at an arbitrary `Irreducible ϖ` rather than at `IsDiscreteValuationRing.exists_irreducible`'s
choice, so the caller picks the uniformizer. -/
theorem surjective_awayToFractionRing_of_irreducible {ϖ : R} (hϖ : Irreducible ϖ) :
    Function.Surjective (awayToFractionRing R ϖ hϖ.ne_zero) := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, map_zero _⟩
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (K := FractionRing R) hϖ hx
  have hϖ' : algebraMap R (FractionRing R) ϖ ≠ 0 := by
    simpa using hϖ.ne_zero
  obtain ⟨k, rfl | rfl⟩ : ∃ k : ℕ, n = (k : ℤ) ∨ n = -(k : ℤ) := by
    rcases n with k | k
    · exact ⟨k, Or.inl rfl⟩
    · exact ⟨k + 1, Or.inr (by simp [Int.negSucc_eq])⟩
  · refine ⟨algebraMap R (Localization.Away ϖ) ((u : R) * ϖ ^ k), ?_⟩
    rw [awayToFractionRing_algebraMap]
    simp [Units.smul_def, Algebra.smul_def, map_mul, map_pow, zpow_natCast]
  · refine ⟨IsLocalization.mk' (Localization.Away ϖ) (u : R)
      (⟨ϖ ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers ϖ), ?_⟩
    rw [show awayToFractionRing R ϖ hϖ.ne_zero = IsLocalization.lift
      (M := Submonoid.powers ϖ) (g := algebraMap R (FractionRing R)) _ from rfl,
      IsLocalization.lift_mk'_spec]
    simp only [Units.smul_def, Algebra.smul_def, zpow_neg, zpow_natCast]
    field_simp
    rw [map_pow]

/-- **A discrete valuation ring satisfies the denominator condition**, and the denominator is a
uniformizer, chosen before the family is.

`FormalSpectrum.surjective_awayToFractionRing_of_irreducible` at
`IsDiscreteValuationRing.exists_irreducible`: inverting `ϖ` alone gives the whole fraction field,
so every family lies in `R[1/ϖ]` and no member needs a denominator of its own. Over `ℤ` this fails
at every `m` (`FormalSpectrum.not_hasBoundedDenominators_int`), and the difference is that `ℤ` has
infinitely many primes to put in a denominator and a discrete valuation ring has one.

`FormalSpectrum.hasBoundedDenominators_of_surjective` at a uniformizer: the surjection is the
theorem above, and the criterion needs nothing else. The statement is unchanged. -/
theorem hasBoundedDenominators_of_isDiscreteValuationRing : HasBoundedDenominators R :=
  (IsDiscreteValuationRing.exists_irreducible R).elim fun _ hϖ =>
    hasBoundedDenominators_of_surjective R hϖ.ne_zero
      (surjective_awayToFractionRing_of_irreducible R hϖ)

/-- **`R[1/ϖ]` is a field at a discrete valuation ring**, at every irreducible `ϖ`, with no
countability hypothesis anywhere.

`FormalSpectrum.surjective_awayToFractionRing_of_irreducible` into
`FormalSpectrum.surjective_awayToFractionRing_iff_isField`: inverting a uniformizer already gives
the whole of `Frac R`, and a domain that surjects onto its fraction field is a field.

**This is the statement the last `example` of this section recorded as absent**, and what made it
absent was the route and not the mathematics. Those `example`s reach the `IsField` form through
`FormalSpectrum.hasBoundedDenominators_iff_exists_isField`, which carries
`[Countable (FractionRing R)]`, so they cannot state it unconditionally; they still go that way
round, because exhibiting the collapse is what they are for, and the fact itself lives here.

Stated at an arbitrary `Irreducible ϖ` rather than at `IsDiscreteValuationRing.exists_irreducible`'s
choice, matching `FormalSpectrum.surjective_awayToFractionRing_of_irreducible`, so the caller picks
the uniformizer. The existential form is
`FormalSpectrum.exists_isField_localizationAway_of_isDiscreteValuationRing` below. -/
theorem isField_localizationAway_of_irreducible {ϖ : R} (hϖ : Irreducible ϖ) :
    IsField (Localization.Away ϖ) :=
  (surjective_awayToFractionRing_iff_isField R hϖ.ne_zero).mp
    (surjective_awayToFractionRing_of_irreducible R hϖ)

/-- **A discrete valuation ring has a single-element localization that is a field**, with no
countability hypothesis.

`FormalSpectrum.isField_localizationAway_of_irreducible` at
`IsDiscreteValuationRing.exists_irreducible`, and nothing else.

**This is the exact negation of `FormalSpectrum.not_exists_isField_localizationAway_int` at the
same strength**, and the pair is the sharpest contrast this file's `IsField` material draws: `ℤ`
has no `m ≠ 0` with `ℤ[1/m]` a field, a discrete valuation ring has one, and **neither statement
carries a countability hypothesis**. Both name no map, no power series ring and none of this
file's own definitions; they are statements about the rings `R[1/m]` themselves.

Named for the reason `FormalSpectrum.not_exists_isField_localizationAway_int` is named — it is the
form in which the fact is recognisable, and greppable, from outside the `FormalSpectrum` namespace
— and not because it adds anything to `FormalSpectrum.isField_localizationAway_of_irreducible`
above, which is stronger and exhibits the uniformizer. -/
theorem exists_isField_localizationAway_of_isDiscreteValuationRing :
    ∃ m : R, m ≠ 0 ∧ IsField (Localization.Away m) :=
  (IsDiscreteValuationRing.exists_irreducible R).elim fun _ hϖ =>
    ⟨_, hϖ.ne_zero, isField_localizationAway_of_irreducible R hϖ⟩

/-- A discrete valuation ring is the **singleton** case of
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`: all its irreducible elements are
associated (`IsDiscreteValuationRing.associated_of_irreducible`), so there is exactly one prime
associate class.

**A consistency check on the classification, not a replacement for the theorem above.** The proof
above exhibits the uniformizer as the denominator and goes through the surjection
`FormalSpectrum.surjective_awayToFractionRing_of_irreducible`, which is proved from the valuation;
this one produces the same denominator only as the product of a one-element set of
representatives, and it is the classification's cardinality that does the work. It is an `example`
because it proves a statement that already has a name. -/
example : HasBoundedDenominators R := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine (hasBoundedDenominators_iff_finite_primes R).mpr
    (Set.Finite.subset (Set.finite_singleton (Associates.mk ϖ)) fun a ha => ?_)
  obtain ⟨x, rfl⟩ := Associates.mk_surjective a
  exact Associates.mk_eq_mk_iff_associated.mpr
    (IsDiscreteValuationRing.associated_of_irreducible R
      (Associates.prime_mk.mp ha).irreducible hϖ)

/-- The forward direction of `FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` is not
vacuous: at a **countable** discrete valuation ring it produces an `m` whose inversion gives the
whole fraction field.

**Two things are being exhibited, and neither is a new mathematical statement.** First,
`Localization.countable_of_countable` fires: the hypothesis of the collapse is on `Frac R`, and
here only `[Countable R]` is assumed, so the instance is what supplies it. Second, the direction
that the countability hypothesis buys — the one that is *not* available at a general domain — has
a value, so the ℤ corollary is not an artefact of a right-hand side nothing satisfies.

The conclusion is already `FormalSpectrum.surjective_awayToFractionRing_of_irreducible` at a
uniformizer, and by a shorter route that needs no countability; this deliberately goes the long
way round, through the collapse, because that is what is being exhibited. It is an `example`. -/
example [Countable R] :
    ∃ m : R, ∃ hm : m ≠ 0, Function.Surjective (awayToFractionRing R m hm) :=
  (hasBoundedDenominators_iff_exists_surjective R).mp
    (hasBoundedDenominators_of_isDiscreteValuationRing R)

/-- The same forward direction read through
`FormalSpectrum.hasBoundedDenominators_iff_exists_isField`: at a **countable** discrete valuation
ring some single-element localization is a field, which is the positive counterpart of
`FormalSpectrum.not_exists_isField_localizationAway_int`.

**Strictly weaker than what this tree knows about discrete valuation rings, and that is the point
of writing it down.** `FormalSpectrum.hasBoundedDenominators_of_isDiscreteValuationRing` holds at
*every* discrete valuation ring, and `FormalSpectrum.surjective_awayToFractionRing_of_irreducible`
exhibits `R[1/ϖ] → Frac R` as surjective there with no countability at all. Only the passage to
`IsField` goes through the `↔`, which carries `[Countable (FractionRing R)]`, so the hypothesis
here is an artefact of the route and not of the fact. **The unconditional statement is
`FormalSpectrum.isField_localizationAway_of_irreducible` above**, which is that same composition —
`FormalSpectrum.surjective_awayToFractionRing_of_irreducible` into
`FormalSpectrum.surjective_awayToFractionRing_iff_isField` — with no countability anywhere, and
`FormalSpectrum.exists_isField_localizationAway_of_isDiscreteValuationRing` is this `example`'s own
statement with the hypothesis dropped. The `example` still goes the long way round, because that
composition does not go through the collapse and the `example`s in this section are here to exhibit
the collapse.

It is an `example` for the same reason the two beside it are: it proves nothing that does not
already have a name. -/
example [Countable R] : ∃ m : R, m ≠ 0 ∧ IsField (Localization.Away m) :=
  (hasBoundedDenominators_iff_exists_isField R).mp
    (hasBoundedDenominators_of_isDiscreteValuationRing R)

/-- **The surjectivity half of `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff` holds**
at the generic point of a discrete valuation ring — and one `f` serves every element at once,
namely `PowerSeries.C ϖ` for a uniformizer `ϖ`.

That is exactly what fails over `ℤ`, where the half cannot fail at any single level of the stalk
tower (`FormalSpectrum.exists_awayToAtPrimeLevel_eq`) but no single `f` serves the limit. Here the
non-uniformity has nowhere to hide, because one `f` is chosen before the element is.

`FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators`
reduces this to `FormalSpectrum.hasBoundedDenominators_of_isDiscreteValuationRing`, where the
uniformizer is obtained from `IsDiscreteValuationRing.exists_irreducible` **before** the family is
introduced — which is what the paragraph above is about. The statement here does not express that,
since its `∃ f` sits under the `∀ b` the criterion puts there. -/
theorem exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint
    (b : AdicCompletion (pointIdeal (powerSeriesXIdeal R) (powerSeriesXGenericPoint R))
      (Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)))) :
    ∃ f, ∃ (hf : constantCoeff f ≠ 0),
      ∃ a, awayToAtPrimeCompletion (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)
        (fg_powerSeriesXIdeal R)
        ((mem_basicOpen_powerSeriesXGenericPoint_iff R f).mpr hf) a = b :=
  (exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators R).mpr
    (hasBoundedDenominators_of_isDiscreteValuationRing R) b

/-- **`FormalSpectrum.IsStalkLimit` holds at `(X) ⊆ R⟦X⟧` at the generic point of a discrete
valuation ring.**

Both halves of `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff`, and neither is proved
here. The injectivity half is
`FormalSpectrum.exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint`, which holds at the
generic point of **every** domain and so needs no hypothesis on `R` at all; the surjectivity half
is the theorem above, and it is the only place the valuation is used.

At the `p`-adic integers this holds and at `ℤ` it fails
(`FormalSpectrum.not_isStalkLimit_powerSeriesXIntGenericPoint`), and the two differ only in how
many primes have to be inverted at once. -/
theorem isStalkLimit_powerSeriesXGenericPoint :
    IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) :=
  (isStalkLimit_powerSeriesXGenericPoint_iff R).mpr
    ⟨exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint R,
      exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint R⟩

/-- The same value read off
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`, as a
**consistency check** on that characterisation.

**The proof above is not replaced and must not be.** It goes through
`FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint`, where the uniformizer
is exhibited as the denominator and the `f` serving a given element is produced; this route hides
both halves behind a single `↔`. It is an `example` because it proves a statement that already has
a name. -/
example : IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) :=
  (isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators R).mpr
    (hasBoundedDenominators_of_isDiscreteValuationRing R)

/-- **`FormalSpectrum.IsStalkLimit` is positive at a point where the colimit over basic opens
genuinely moves**, which is what this section exists to record.

Before this, every positive value was at a point where the question is idle: at `⊥` and at a
nilpotent ideal of definition the two completions collapse, and
`FormalSpectrum.isStalkLimit_powerSeriesX_field` is reached through
`FormalSpectrum.isStalkLimit_of_isUnit_notMem_pointPrime`, at the closed point of a local ring,
where every `f` with `x ∈ D(f)` is a unit and no witness is ever produced. A reader could have
concluded that the predicate is positive exactly when it is vacuous. **It is not**: here the point
is not closed, a witness is produced, and the value is positive.

The criterion behind the value over a field also does not apply — a discrete valuation ring is not
a field (`IsDiscreteValuationRing.not_isField`), so
`FormalSpectrum.exists_notMem_pointPrime_not_isUnit_powerSeriesXGenericPoint` supplies an element
outside `FormalSpectrum.pointPrime` that is not a unit. This is not
`FormalSpectrum.isStalkLimit_powerSeriesX_field` in disguise. -/
theorem isStalkLimit_and_not_isClosed_powerSeriesXGenericPoint :
    IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) ∧
      ¬ IsClosed ({powerSeriesXGenericPoint R} :
        Set (FormalSpectrum (powerSeriesXIdeal R))) :=
  ⟨isStalkLimit_powerSeriesXGenericPoint R,
    not_isClosed_powerSeriesXGenericPoint R (IsDiscreteValuationRing.not_isField R)⟩

/-- **The value above is not vacuous**, and the witness needs no import this file does not have:
`ℚ⟦T⟧` is a discrete valuation ring, so `FormalSpectrum.IsStalkLimit` holds at
`(X) ⊆ ℚ⟦T⟧⟦X⟧` at the generic point, and that point is not closed.

A statement under `[IsDiscreteValuationRing R]` is only as good as the instances in scope, and
this is what stops the two theorems above from being conditional on something the tree cannot
exhibit. It also gives the contrast in fully closed form: this holds, and
`FormalSpectrum.not_isStalkLimit_powerSeriesXIntGenericPoint` fails, with no hypothesis on either
side. -/
theorem isStalkLimit_and_not_isClosed_powerSeriesXRatSeriesGenericPoint :
    IsStalkLimit (powerSeriesXIdeal (PowerSeries ℚ))
        (powerSeriesXGenericPoint (PowerSeries ℚ)) ∧
      ¬ IsClosed ({powerSeriesXGenericPoint (PowerSeries ℚ)} :
        Set (FormalSpectrum (powerSeriesXIdeal (PowerSeries ℚ)))) :=
  isStalkLimit_and_not_isClosed_powerSeriesXGenericPoint _

end DiscreteValuationRing

end FormalSpectrum
