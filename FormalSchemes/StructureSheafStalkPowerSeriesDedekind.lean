import FormalSchemes.StructureSheafStalkPowerSeriesPoint
import FormalSchemes.StructureSheafStalkPowerSeriesCounterexample
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.DedekindDomain.PID

set_option linter.style.header false

/-!
# The denominator condition at a Dedekind domain: finitely many prime ideals

`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` classifies
`FormalSpectrum.HasBoundedDenominators` at a **unique factorisation domain**: it holds exactly when
there are finitely many primes up to associates
(`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`). It also says, in two places, that
nothing there bears on Dedekind domains, and gives the same reason both times — *a Dedekind domain
is a statement about **ideals**, and a nonprincipal maximal ideal contributes no prime element at
all.*

**That reason is correct and it is what tells you what is missing: a refuting criterion stated at
prime ideals rather than at prime elements.** This file supplies it and reads off the
classification:

> `FormalSpectrum.hasBoundedDenominators_iff_finite_primeIdeals`: at a Dedekind domain the
> denominator condition holds **iff** `{I : Ideal R | I.IsPrime}` is finite.

and its corollary, which is the sharper sentence:

> `FormalSpectrum.isPrincipalIdealRing_of_hasBoundedDenominators`: a Dedekind domain satisfying the
> denominator condition is a **principal ideal ring**.

Both are then read at `FormalSpectrum.IsStalkLimit` rather than left for the reader to compose,
because that predicate is what EGA I 10.8's stalk half is:

> `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_finite_primeIdeals`: at a Dedekind
> domain the stalk half **holds** at the generic point of `R⟦X⟧` **iff** `{I : Ideal R | I.IsPrime}`
> is finite;

> `FormalSpectrum.isPrincipalIdealRing_of_isStalkLimit_powerSeriesXGenericPoint`: so it **fails**
> at every Dedekind domain that is not a principal ideal ring.

The reading goes through
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`, which is in
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` and rests in turn on
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff`
(`FormalSchemes.StructureSheafStalkPowerSeriesGeneric`), where the predicate at this point is set
up. So the half fails over every Dedekind domain with infinitely many primes, and over every
Dedekind domain whose class number is greater than one.

**None of that is confined to the generic point.**
`FormalSchemes.StructureSheafStalkPowerSeriesPoint` decides `FormalSpectrum.IsStalkLimit` at an
**arbitrary** point of `Spf (R⟦X⟧, (X))`, as `FormalSpectrum.HasBoundedDenominatorsAt` at the
corresponding prime of `R`, so the refuting criteria above have a form there too and this file
carries them to it:

> `FormalSpectrum.not_isStalkLimit_powerSeriesX_of_infinite_primeIdeals`: over a Noetherian domain
> of dimension at most one with infinitely many nonzero primes the stalk half fails at **every**
> point of `Spf (R⟦X⟧, (X))`, and not only at the generic one.

That is `FormalSpectrum.not_isStalkLimit_powerSeriesX_int` with `ℤ` replaced by the hypotheses it
was using — the `example` in `section Int` below recovers the `ℤ` statement from it, and
`FormalSchemes.StructureSheafStalkPowerSeriesNumberField` reads it at every ring of integers. **It
costs one project import and no Mathlib import**; see `## Placement`.

Two steps of that passage are not transcriptions of the generic-point argument, and both are where
a shorter-looking version goes wrong. **The descent back to `R` is where `[IsDomain R]` is spent**,
through `Ideal.primeCompl_le_nonZeroDivisors` rather than through `IsFractionRing.injective`; and
**the family of primes cannot be indexed by the nonzero primes**, because `p` is one of them and
the elements the criterion needs have to avoid `p`. Cutting the family down to the primes other
than `p` is what makes maximality — `Ideal.IsPrime.isMaximal`, which is the `Ring.DimensionLEOne`
hypothesis — do work that it does not do at the generic point.

## Where the element criterion stops and the ideal criterion goes on

The two refuting criteria share everything but their last step. Both apply the condition to the
family of inverses `n ↦ (s n)⁻¹` and land on `m ^ k = r * s n` back in `R`. Then

* `FormalSpectrum.not_hasBoundedDenominators_of_primes` reads that as `p n ∣ m ^ k` and finishes
  with `Prime.dvd_of_dvd_pow`, which needs `p n` to be a prime **element**;
* `FormalSpectrum.not_hasBoundedDenominators_of_primeIdeals` reads it as `m ^ k ∈ P n`, by
  `Ideal.mul_mem_left` from `s n ∈ P n`, and finishes with `Ideal.IsPrime.mem_of_pow_mem`.

**That is the step a nonprincipal maximal ideal makes impossible in the element version and trivial
here**, and it is the whole content of the generalisation. **The implication between the two
criteria therefore runs one way, and it is the way the word says.** The ideal criterion gives the
element one back, at `P n := Ideal.span {p n}` with `s n := p n`: `Ideal.span_singleton_prime`
makes the span prime, `p n` is its own nonzero witness, and `Ideal.mem_span_singleton` turns *no
`m` is divisible by the whole family* into *no `m` lies in every `P n`*. That derivation is
written out as an `example` beside that criterion rather than asserted here, at the same
generality and with no extra hypothesis. **The converse fails for the reason this file exists**:
a nonprincipal maximal ideal is not the span of a prime element, so a family containing one is out
of the element criterion's reach.

`FormalSpectrum.not_hasBoundedDenominators_of_primes` is kept as it stands and is not restated as
a corollary, on the precedent its own neighbour sets — *both forms are shipped rather than one* —
because a caller holding prime elements should not have to build spans to use them.

**The refutation uses no integral closedness.**
`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals` assumes only
`[IsNoetherianRing R]` and `[Ring.DimensionLEOne R]`, so it refutes the condition at
**orders in number fields**, which are not Dedekind, as well as at Dedekind domains. Only the
converse direction of the classification uses the full hypothesis.

## What the classification does *not* do to the one it generalises

**It does not remove the unique-factorisation hypothesis from
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`; it derives it.** Finitely many primes at
a Dedekind domain forces principality — Mathlib's `IsPrincipalIdealRing.of_finite_primes` — and a
principal ideal domain is a unique factorisation domain, so the backward direction here is that
theorem applied after `FormalSpectrum.finite_prime_associates_of_finite_primeIdeals` supplies its
hypothesis. The counterexample file's sentence about that direction — *"it goes from every prime
divides `m` to every element divides a power of `m`, and that passage is factorisation"* — stays
exactly true: the factorisation arrives through `IsPrincipalIdealRing.of_finite_primes` instead
of being assumed.

**There is no countability hypothesis anywhere here and none is removed from anything.** Like the
unique-factorisation classification, the refuting direction constructs **one** explicit
`ℕ`-indexed family rather than quantifying over the whole of `Frac R`, which is what
`[Countable (FractionRing R)]` is needed for elsewhere;
`FormalSpectrum.hasBoundedDenominators_iff_exists_surjective` and the three spellings beside it keep
their hypothesis and nothing below bears on it.

**The two classifications are incomparable, and that is this subject's standing shape.** A unique
factorisation domain of dimension greater than one — `ℂ[X, Y]` — is decided by the element version
and not by this one; a Dedekind domain of class number greater than one is decided by this one and
not by the element version, since its nonprincipal maximal ideals contribute no prime element. Where
both apply, at a principal ideal domain, they agree.

## Main results

* `FormalSpectrum.not_hasBoundedDenominators_of_primeIdeals`: **the refuting criterion at prime
  ideals** — a family of nonzero prime ideals lying in no single `m ≠ 0` refutes the condition, at
  an arbitrary domain, with no factorisation, no Noetherian and no dimension hypothesis.
* `FormalSpectrum.finite_setOf_isPrime_mem`: at a Noetherian ring of dimension at most one, **only
  finitely many nonzero primes contain a fixed `m ≠ 0`**, because each of them is minimal over
  `(m)`.
* `FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals`: **infinitely many nonzero
  primes refutes the condition**, at a Noetherian domain of dimension at most one.
* `FormalSpectrum.finite_prime_associates_of_finite_primeIdeals`: at an arbitrary domain, finitely
  many prime **ideals** gives finitely many prime **associate classes**.
* `FormalSpectrum.not_hasBoundedDenominatorsAt_of_primeIdeals`: **the refuting criterion at an
  arbitrary prime** — the criterion at the head of this list with the fraction field replaced by
  the local ring, at an arbitrary domain and with the same three hypotheses absent.
* `FormalSpectrum.not_hasBoundedDenominatorsAt_of_infinite_primeIdeals`: **infinitely many nonzero
  primes refutes the condition at every prime**, at a Noetherian domain of dimension at most one.
* `FormalSpectrum.not_isStalkLimit_powerSeriesX_of_infinite_primeIdeals`: **and so the stalk half
  fails at every point of `Spf (R⟦X⟧, (X))`** over such a ring, not only at the generic point.
* `FormalSpectrum.hasBoundedDenominators_iff_finite_primeIdeals`: **the classification at a Dedekind
  domain** — the condition holds **iff** `{I : Ideal R | I.IsPrime}` is finite.
* `FormalSpectrum.isPrincipalIdealRing_of_hasBoundedDenominators`: **and a Dedekind domain
  satisfying it is a principal ideal ring**, so no Dedekind domain of class number greater than one
  satisfies it.
* `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_finite_primeIdeals`: **the same
  classification read at the predicate** — at a Dedekind domain `FormalSpectrum.IsStalkLimit` holds
  at the generic point of `R⟦X⟧` **iff** `{I : Ideal R | I.IsPrime}` is finite.
* `FormalSpectrum.isPrincipalIdealRing_of_isStalkLimit_powerSeriesXGenericPoint`: **and the
  corollary at the predicate** — the stalk half of EGA I 10.8 fails at that point over every
  Dedekind domain that is not a principal ideal ring.
* `FormalSpectrum.infinite_setOf_isPrime_int`: **`ℤ` has infinitely many nonzero prime ideals**,
  built from `Nat.infinite_setOf_prime` so that the everywhere-failure above is checked at `ℤ`
  rather than asserted of it.

## What is *not* proved here

**Nothing here repairs EGA I 10.8's stalk half.** It refutes that half over a larger class of rings
than `ℤ`, and at every point of `Spf (R⟦X⟧, (X))` rather than at the generic point alone; which
hypothesis makes the general statement true is undetermined and nothing below bears on it. **No
criterion for when the predicate *holds* at a general prime is given either**, at any generality;
the one general positive value on the tree is
`FormalSpectrum.hasBoundedDenominatorsAt_maximalIdeal`, which is proved elsewhere and is not
touched here.

**Nothing here says `FormalSpectrum.IsStalkLimit` varies across a single formal spectrum**, and no
ring below can be made to say it. That needs a **local** domain failing the denominator condition; a
Dedekind domain with infinitely many primes is not local, and neither is one of class number greater
than one. **The obstruction is in the hypotheses rather than in the choice of ring**:
`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals` assumes `Ring.DimensionLEOne`,
and a local Noetherian domain of dimension at most one has exactly one nonzero prime, so locality
and that criterion's hypothesis exclude each other. A witness therefore has to come from
`FormalSpectrum.not_hasBoundedDenominators_of_primeIdeals`, the arbitrary-domain criterion above,
and one does: `FormalSchemes.StructureSheafStalkPowerSeriesLocal` builds it at `ℤ[X]` localized at
`(2, X)`. **The criterion at an arbitrary point sharpens that exclusion rather than weakening it**:
`FormalSpectrum.not_isStalkLimit_powerSeriesX_of_infinite_primeIdeals` decides every point of
`Spf (R⟦X⟧, (X))` the same way, so no ring meeting its hypotheses can be the witness either.

**No ring is instantiated here except `ℤ`, and the reason is import cost rather than
difficulty.** Reading the theorems above at a ring of integers needs the infinitude of the primes of
`𝓞 K`, which is not in Mathlib as a `Set.Infinite` statement and has to be built from
`Ideal.exists_ideal_over_prime_of_isIntegral` and `Nat.infinite_setOf_prime`; that drags a
number-theory import in, and it is paid one module further out instead, on the leaf
`FormalSchemes.StructureSheafStalkPowerSeriesNumberField`, whose whole purpose is to keep
`Mathlib/NumberTheory/NumberField/Basic.lean` out of this module's closure.

**What that leaf finds is stronger than the reading this paragraph used to name.** It is not the
class number that decides the question at a ring of integers:
`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals` above asks only for infinitely
many nonzero primes, and every `𝓞 K` has them, so the condition fails at `𝓞 K` for **every** number
field `K` — `FormalSpectrum.not_hasBoundedDenominators_ringOfIntegers`. `ℤ` remains the only ring
instantiated *here*.

**Nothing here bears on semilocal domains in general.** The classification decides the condition at
a **semilocal Dedekind** domain, positively, because that is a Dedekind domain with finitely many
primes; a semilocal domain that is not Dedekind is untouched, as are Prüfer and valuation rings and
the general domain.

**No hypothesis is removed from anything on the tree.** Neither `[Countable (FractionRing R)]` from
the collapse, nor `[UniqueFactorizationMonoid R]` from the classification this generalises, nor
`[IsDomain R]` from the condition itself.

## Placement

Over `FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, which holds
`FormalSpectrum.HasBoundedDenominators`, both refuting criteria and the element classification:
forward closure **54** project modules besides itself, reverse closure **2** — the leaves
`FormalSchemes.StructureSheafStalkPowerSeriesNumberField`, which instantiates the refuting criterion
at a ring of integers, and `FormalSchemes.StructureSheafStalkPowerSeriesLocal`, which instantiates
it at `ℤ[X]` localized at `(2, X)` — counted by walking every `^import FormalSchemes.` line over
the 560 modules under `FormalSchemes/` (a module is not counted in its own closure; the aggregator
at the repository root is outside the walk). The forward count includes
`FormalSchemes.StructureSheafStalkPowerSeriesPoint`, which holds the predicate at an arbitrary
point, is itself over that same module, and is what the arbitrary-point material below is stated
in; it is the one edge this branch adds.

Appending to that file was the alternative and is cheaper by a module. It is not taken for two
reasons, and the second is the load-bearing one. It is **3012** lines with **94** declarations —
`theorem`, `lemma`, `def`, `instance` or `class` at the start of a line, `example`s not counted and
there are **nine** of those — and is the most edited file on this board, at **26** commits touching
it against **12** for the runner-up, so a leaf keeps two concurrent rows off one file; and **the two
Mathlib imports this material needs would otherwise be paid by a module that does not need them.**
That file's own discrete-valuation-ring section advertises that it *"adds no Mathlib import
either"*, so the imports are a cost worth isolating, and they are not avoidable: without
`Mathlib/RingTheory/DedekindDomain/PID.lean` the constant `Ring.DimensionLEOne` does not exist, and
without `Mathlib/RingTheory/Ideal/MinimalPrime/Noetherian.lean` the finiteness above has nothing to
cite.

**Only one of the two is new to the project's Mathlib closure, and it is worth saying which**, since
the import line and the build cost are different things: walking `import` and `public import` over
Mathlib's sources from every `import Mathlib…` line under `FormalSchemes/`, the project's Mathlib
closure is **exactly two modules larger** than it would be without
`Mathlib/RingTheory/DedekindDomain/PID.lean`, the two being that module and its own
`Mathlib/RingTheory/PrincipalIdealDomainOfPrime.lean`.
`Mathlib/RingTheory/Ideal/MinimalPrime/Noetherian.lean` was **already** reached by this project, so
naming it here costs a line and no build.

The **delta** is the figure quoted, not the absolute, and the reason is the one
`FormalSchemes.StructureSheafStalkPowerSeriesNumberField` records at greater length: the absolute
depends on the walk's convention — restricting to `Mathlib.*` gives 2727 where following the other
packages as well gives 2985 — and it drifts upwards with every `import Mathlib…` line any row adds
anywhere under `FormalSchemes/`, so it is stale the moment it is written. The delta is stable under
both conventions and is what a reader deciding where to put material needs.

**The arbitrary-point material is appended here rather than paid on a leaf, which is the opposite
of the choice the two paragraphs above defend, and the reason is that neither of their arguments
reaches it.** It needs **no** Mathlib import — `Ring.DimensionLEOne` and the Noetherian finiteness
it spends are already in this file's closure — so the cost it would isolate does not exist; and its
one new edge is the project import
`FormalSchemes.StructureSheafStalkPowerSeriesPoint`, without which
`FormalSpectrum.HasBoundedDenominatorsAt` cannot be named at all. The concurrency argument is real
and is paid: this file is longer for it.

**What a leaf would cost instead is prose, and the bill is not small.** A 561st module changes how
many project modules every module above it reaches, and this tree states those counts in prose.
The three routes were measured with `scripts/closure_audit.py --tree` in a scratch worktree, and
the numbers are these. A stub leaf importing this file, the point module and the
number-field one sends **42** attributed figures in **23** files to MISMATCH; the route taken
here sends **5** in **4**; putting the material in the point module instead — that module importing
this one, and the number-field leaf importing it — sends the same **5** in **3**.

**The mathematical fit is what decides between the two cheap routes.** The criterion below is
`FormalSpectrum.not_hasBoundedDenominators_of_primeIdeals` with the fraction field replaced by the
local ring, and `FormalSpectrum.finite_setOf_isPrime_mem`, which its covering hypothesis spends, is
a couple of hundred lines above it; neither fact is about a point of a formal spectrum, and the
point module would be importing a Dedekind-domain classification it makes no use of.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX).
-/

noncomputable section

universe u

namespace FormalSpectrum

section Domain

variable (R : Type u) [CommRing R] [IsDomain R]

omit [IsDomain R] in
/-- **At a Noetherian ring of dimension at most one, only finitely many nonzero primes contain a
fixed `m ≠ 0`.**

Every such prime is **minimal** over `(m)`: a prime `Q` with `(m) ≤ Q ≤ P` contains `m ≠ 0`, so
`Q ≠ ⊥`, so `Ideal.IsPrime.isMaximal` — which is what `Ring.DimensionLEOne` gives — makes `Q`
maximal, and `Q ≤ P` with `P` prime hence not `⊤` forces `Q = P`. The finiteness is then Mathlib's
`Ideal.finite_minimalPrimes_of_isNoetherianRing` and nothing else.

`Ideal.IsMinimalPrime I p` unfolds to `Minimal (fun q ↦ q.IsPrime ∧ I ≤ q) p`, so the two goals
after the anonymous constructor are *`(m)` is contained in `P`* and *`P` is below every prime above
`(m)` that is below it*; there is no membership lemma to reach for.

**This is a statement about the ring and not about the denominator condition**, and it is where the
dimension hypothesis is spent. -/
theorem finite_setOf_isPrime_mem [IsNoetherianRing R] [Ring.DimensionLEOne R] {m : R} (hm : m ≠ 0) :
    {P : Ideal R | P.IsPrime ∧ P ≠ ⊥ ∧ m ∈ P}.Finite := by
  refine (Ideal.span {m}).finite_minimalPrimes_of_isNoetherianRing.subset ?_
  rintro P ⟨hp, hne, hmem⟩
  refine ⟨⟨hp, ?_⟩, ?_⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  · rintro Q ⟨hq, hQle⟩ hQP
    have hm' : m ∈ Q := hQle (Ideal.mem_span_singleton_self m)
    have hQne : Q ≠ ⊥ := fun h => hm (by simpa [h] using hm')
    exact (hq.isMaximal hQne).eq_of_le hp.ne_top hQP ▸ le_refl _

/-- **The refuting criterion at prime ideals.** A family of prime ideals, each carrying a nonzero
element, such that no single `m ≠ 0` lies in all of them, refutes the denominator condition.

This is `FormalSpectrum.not_hasBoundedDenominators_of_primes` with its last step replaced, and the
replacement is the point of this file. Both proofs apply the condition to the family of inverses
`n ↦ (s n)⁻¹`, obtain a common denominator `m` and an exponent `k`, and clear denominators to
`m ^ k = r * s n` in `R`. The element version reads that as `p n ∣ m ^ k` and finishes with
`Prime.dvd_of_dvd_pow`, which needs a prime **element**; this one reads it as `m ^ k ∈ P n`, by
`Ideal.mul_mem_left` from `s n ∈ P n`, and finishes with `Ideal.IsPrime.mem_of_pow_mem`. **A
nonprincipal maximal ideal makes the first step impossible and leaves the second untouched.**

The covering hypothesis is the analogue of the element version's *no single `m` is divisible by
the whole family*: no single `m` lies in every `P n`. The elements `s n` are hypotheses rather than
choices, so that the criterion is usable at a family a caller already has;
`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals` below makes them by choice.

**No factorisation, no Noetherian hypothesis and no dimension hypothesis** — an arbitrary domain,
exactly like the criterion it generalises. -/
theorem not_hasBoundedDenominators_of_primeIdeals (P : ℕ → Ideal R) (hP : ∀ n, (P n).IsPrime)
    (s : ℕ → R) (hs : ∀ n, s n ∈ P n) (hs0 : ∀ n, s n ≠ 0)
    (hcov : ∀ m : R, m ≠ 0 → ∃ n, m ∉ P n) : ¬ HasBoundedDenominators R := by
  intro h
  obtain ⟨m, hm, hall⟩ := h fun n => (algebraMap R (FractionRing R) (s n))⁻¹
  obtain ⟨n, hn⟩ := hcov m hm
  obtain ⟨k, r, hr⟩ := hall n
  apply hn
  have hsn0 : algebraMap R (FractionRing R) (s n) ≠ 0 := by simpa using (hs0 n)
  have hfrac : algebraMap R (FractionRing R) (m ^ k) =
      algebraMap R (FractionRing R) r * algebraMap R (FractionRing R) (s n) := by
    field_simp at hr
    rw [← hr]
  rw [← map_mul] at hfrac
  have hmk : m ^ k = r * s n := IsFractionRing.injective R (FractionRing R) hfrac
  exact (hP n).mem_of_pow_mem k (hmk ▸ Ideal.mul_mem_left _ r (hs n))

/-- **The ideal criterion gives the element one back**, which is what makes the word
*generalisation* above a checked statement rather than an assertion.

`Ideal.span {p n}` is prime by `Ideal.span_singleton_prime`, `p n` is a nonzero element of it by
`Ideal.mem_span_singleton_self` and `Prime.ne_zero`, and `Ideal.mem_span_singleton` turns the
element version's *no `m` is divisible by the whole family* into the covering hypothesis. Same
generality, no extra hypothesis.

An `example` rather than a theorem: `FormalSpectrum.not_hasBoundedDenominators_of_primes` is on
the tree already and stays there, for the reason its own neighbour gives — both forms are wanted
in different places, and a caller holding prime elements should not have to build spans. The
converse implication fails, and fails for the reason this file exists: a nonprincipal maximal
ideal is not the span of a prime element. -/
example (p : ℕ → R) (hp : ∀ n, Prime (p n)) (hdvd : ∀ m : R, m ≠ 0 → ∃ n, ¬ p n ∣ m) :
    ¬ HasBoundedDenominators R :=
  not_hasBoundedDenominators_of_primeIdeals R (fun n => Ideal.span {p n})
    (fun n => (Ideal.span_singleton_prime (hp n).ne_zero).mpr (hp n))
    p (fun _ => Ideal.mem_span_singleton_self _) (fun n => (hp n).ne_zero)
    (fun m hm => (hdvd m hm).imp fun _ hn => fun hmem => hn (Ideal.mem_span_singleton.mp hmem))

/-- **Infinitely many nonzero primes refutes the denominator condition**, at a Noetherian domain of
dimension at most one.

`Set.Infinite.natEmbedding` turns the infinite set of nonzero primes into an injective `ℕ`-indexed
family of them, `Submodule.exists_mem_ne_zero_of_ne_bot` supplies a nonzero element of each, and
`FormalSpectrum.not_hasBoundedDenominators_of_primeIdeals` consumes both.

**The covering hypothesis is where `FormalSpectrum.finite_setOf_isPrime_mem` is spent, and it is not
"pick a prime avoiding `m`".** The prime that lemma produces need not lie in the range of the
embedding. The argument is the one
`FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated` already uses at prime elements:
if every member of the family contained `m` then an **injective** `ℕ`-indexed family would land
inside a **finite** set, which `Set.infinite_range_of_injective` refutes.

**No integral closedness is used**, so this applies to orders in number fields and to every other
Noetherian domain of dimension at most one, not only to Dedekind domains. -/
theorem not_hasBoundedDenominators_of_infinite_primeIdeals [IsNoetherianRing R]
    [Ring.DimensionLEOne R] (hinf : {P : Ideal R | P.IsPrime ∧ P ≠ ⊥}.Infinite) :
    ¬ HasBoundedDenominators R := by
  classical
  let e : ℕ ↪ {P : Ideal R // P ∈ {P : Ideal R | P.IsPrime ∧ P ≠ ⊥}} := hinf.natEmbedding
  have hprime : ∀ n, ((e n : Ideal R)).IsPrime := fun n => (e n).2.1
  have hne : ∀ n, (e n : Ideal R) ≠ ⊥ := fun n => (e n).2.2
  choose s hs hs0 using fun n : ℕ => Submodule.exists_mem_ne_zero_of_ne_bot (hne n)
  refine not_hasBoundedDenominators_of_primeIdeals R (fun n => (e n : Ideal R)) hprime s hs hs0 ?_
  intro m hm
  by_contra hcon
  have hmem : ∀ n, m ∈ (e n : Ideal R) := fun n => not_not.mp fun h => hcon ⟨n, h⟩
  have hinj : Function.Injective (fun n => (e n : Ideal R)) := fun i j hij =>
    e.injective (Subtype.ext hij)
  refine Set.infinite_range_of_injective hinj ((finite_setOf_isPrime_mem R hm).subset ?_)
  rintro _ ⟨n, rfl⟩
  exact ⟨hprime n, hne n, hmem n⟩

/-- **Finitely many prime ideals gives finitely many prime associate classes**, at an arbitrary
domain.

The map is *prime element up to associates* ↦ *the ideal it generates*. It lands among the prime
ideals by `Ideal.span_singleton_prime`, and it is injective on primes by
`Ideal.span_singleton_eq_span_singleton`, which needs `[IsDomain]` and nothing else.

The representatives are chosen through `Associates.mk_surjective` and **not** through
`Associates.out`, for the reason `FormalSpectrum.hasBoundedDenominators_iff_finite_primes`'s
docstring already gives: `Associates.out` needs `[NormalizationMonoid R]`, which a bare domain does
not carry.

**This direction needs neither factorisation nor principality**, which is why it is stated here
rather than inside `FormalSpectrum.hasBoundedDenominators_iff_finite_primeIdeals` below: what the
Dedekind hypothesis buys there is principality, and that is used on the other side of this map. -/
theorem finite_prime_associates_of_finite_primeIdeals (hfin : {I : Ideal R | I.IsPrime}.Finite) :
    {a : Associates R | Prime a}.Finite := by
  classical
  choose rep hrep using fun a : Associates R => Associates.mk_surjective a
  have hprime : ∀ a : Associates R, Prime a → Prime (rep a) := by
    intro a ha
    rw [← Associates.prime_mk, hrep a]; exact ha
  refine Set.Finite.of_finite_image (f := fun a => Ideal.span {rep a}) (hfin.subset ?_) ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact (Ideal.span_singleton_prime (hprime a ha).ne_zero).mpr (hprime a ha)
  · intro a ha b hb hab
    have hassoc : Associated (rep a) (rep b) := Ideal.span_singleton_eq_span_singleton.mp hab
    rw [← hrep a, ← hrep b]
    exact Associates.mk_eq_mk_iff_associated.mpr hassoc

end Domain

section DimOnePoint

variable (R : Type u) [CommRing R] [IsDomain R]

/-- **The refuting criterion at an arbitrary prime**: a family of prime ideals, each of them
carrying an element outside `p`, and no single `m` outside `p` lying in all of them, refutes
`FormalSpectrum.HasBoundedDenominatorsAt` at `p`.

This is `FormalSpectrum.not_hasBoundedDenominators_of_primeIdeals` with the fraction field replaced
by the local ring at `p` and `m ≠ 0` by `m ∉ p` — exactly the relation
`FormalSpectrum.HasBoundedDenominatorsAt` bears to `FormalSpectrum.HasBoundedDenominators` — and
the four steps are the same ones: feed the condition the family `n ↦ 1 / s n`, get a common
denominator `m ∉ p`, land back in `R` on `m ^ k = r * s n`, and read that as `m ^ k ∈ P n` by
`Ideal.mul_mem_left` and then as `m ∈ P n` by `Ideal.IsPrime.mem_of_pow_mem`.

**The descent back to `R` is where the two versions differ, and it is the only use `[IsDomain R]`
gets here.** The generic-point version returns from `Frac R` by `IsFractionRing.injective`; the map
to `Localization.AtPrime p` is injective for the neighbouring reason, that the prime complement of
a prime of a domain consists of nonzero divisors — `Ideal.primeCompl_le_nonZeroDivisors` and
`IsLocalization.injective`. Nothing else below asks for a domain.

**`s n ∉ p` is a hypothesis and not bookkeeping.** It is what makes `1 / s n` an element of the
local ring at all, and it is why the family cannot simply be indexed by the nonzero primes: at
`P n = p` it is unsatisfiable. `FormalSpectrum.not_hasBoundedDenominatorsAt_of_infinite_primeIdeals`
below is where that is dealt with.

**No factorisation, no Noetherian hypothesis and no dimension hypothesis** — an arbitrary domain and
an arbitrary prime of it, like the criterion this generalises. -/
theorem not_hasBoundedDenominatorsAt_of_primeIdeals (p : Ideal R) [p.IsPrime] (P : ℕ → Ideal R)
    (hP : ∀ n, (P n).IsPrime) (s : ℕ → R) (hs : ∀ n, s n ∈ P n) (hsp : ∀ n, s n ∉ p)
    (hcov : ∀ m : R, m ∉ p → ∃ n, m ∉ P n) : ¬ HasBoundedDenominatorsAt R p := by
  intro h
  obtain ⟨m, hm, hall⟩ := h fun n =>
    IsLocalization.mk' (M := p.primeCompl) _ (1 : R) ⟨s n, hsp n⟩
  obtain ⟨n, hn⟩ := hcov m hm
  obtain ⟨k, r, hr⟩ := hall n
  have hmul := congrArg (· * algebraMap R (Localization.AtPrime p) (s n)) hr
  simp only [mul_assoc] at hmul
  rw [IsLocalization.mk'_spec, map_one, mul_one, ← map_mul] at hmul
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime p)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors p)
  have heq : r * s n = m ^ k := hinj hmul
  exact hn ((hP n).mem_of_pow_mem k (heq ▸ Ideal.mul_mem_left _ r (hs n)))

variable [IsNoetherianRing R] [Ring.DimensionLEOne R]

/-- **Infinitely many nonzero primes refutes the denominator condition at every prime**, at a
Noetherian domain of dimension at most one.

`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals` is the case `p = ⊥` of this,
read through `FormalSpectrum.hasBoundedDenominatorsAt_bot_iff`; the `example` below checks that
rather than leaving it asserted.

**The family that version builds cannot be reused, and cutting it down is the work.** Its members
have to avoid `p`, and `p` is itself one of the infinitely many nonzero primes, so the set is
first replaced by `{P | P.IsPrime ∧ P ≠ ⊥ ∧ P ≠ p}` — still infinite, being an infinite set less
one element — and only then embedded by `Set.Infinite.natEmbedding`.

**That cut is also what produces the elements, and it is the step with nothing to match at the
generic point.** A nonzero prime `P ≠ p` of a Noetherian domain of dimension at most one is
**maximal** — `Ideal.IsPrime.isMaximal`, which is what `Ring.DimensionLEOne` gives — so `P ≤ p`
would force `P = p`, since `p` is prime and hence not `⊤`; `SetLike.not_le_iff_exists` then hands
over an element of `P` outside `p`. At the generic point the elements are whatever
`Submodule.exists_mem_ne_zero_of_ne_bot` returns and no maximality is needed.

**The covering hypothesis is discharged exactly as that version discharges its own**, and it is not
"pick a prime avoiding `m`": if every member of an injective `ℕ`-indexed family contained `m` then
that family would sit inside the finite set `FormalSpectrum.finite_setOf_isPrime_mem` produces,
which `Set.infinite_range_of_injective` refutes. The `m ≠ 0` that lemma asks for is read off
`m ∉ p` rather than assumed. -/
theorem not_hasBoundedDenominatorsAt_of_infinite_primeIdeals (p : Ideal R) [p.IsPrime]
    (hinf : {P : Ideal R | P.IsPrime ∧ P ≠ ⊥}.Infinite) :
    ¬ HasBoundedDenominatorsAt R p := by
  classical
  have hinf' : {P : Ideal R | P.IsPrime ∧ P ≠ ⊥ ∧ P ≠ p}.Infinite := by
    refine Set.Infinite.mono ?_ (hinf.sdiff (Set.finite_singleton p))
    rintro P ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, by simpa using h3⟩
  let e : ℕ ↪ {P : Ideal R // P ∈ {P : Ideal R | P.IsPrime ∧ P ≠ ⊥ ∧ P ≠ p}} := hinf'.natEmbedding
  have hprime : ∀ n, ((e n : Ideal R)).IsPrime := fun n => (e n).2.1
  have hne : ∀ n, (e n : Ideal R) ≠ ⊥ := fun n => (e n).2.2.1
  have hnotle : ∀ n, ¬ ((e n : Ideal R) ≤ p) := fun n hle =>
    (e n).2.2.2 (((hprime n).isMaximal (hne n)).eq_of_le (Ideal.IsPrime.ne_top ‹p.IsPrime›) hle)
  choose s hs hsp using fun n => SetLike.not_le_iff_exists.mp (hnotle n)
  refine not_hasBoundedDenominatorsAt_of_primeIdeals R p (fun n => (e n : Ideal R)) hprime s hs
    hsp ?_
  intro m hm
  have hm0 : m ≠ 0 := fun h => hm (h ▸ p.zero_mem)
  by_contra hcon
  have hmem : ∀ n, m ∈ (e n : Ideal R) := fun n => not_not.mp fun h => hcon ⟨n, h⟩
  have hinj : Function.Injective (fun n => (e n : Ideal R)) := fun i j hij =>
    e.injective (Subtype.ext hij)
  refine Set.infinite_range_of_injective hinj ((finite_setOf_isPrime_mem R hm0).subset ?_)
  rintro _ ⟨n, rfl⟩
  exact ⟨hprime n, hne n, hmem n⟩

/-- **The stalk half of EGA I 10.8 fails at every point of `Spf (R⟦X⟧, (X))`**, over every
Noetherian domain of dimension at most one with infinitely many nonzero prime ideals.

`FormalSpectrum.eq_powerSeriesXPoint` says every point of that space is a
`FormalSpectrum.powerSeriesXPoint`, and
`FormalSpectrum.isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt` turns the predicate
there into the denominator condition at the corresponding prime of `R`, which the theorem above
refutes at every prime at once. Both live in
`FormalSchemes.StructureSheafStalkPowerSeriesPoint` and are the whole reason this file imports it.

**This is `FormalSpectrum.not_isStalkLimit_powerSeriesX_int` with `ℤ` replaced by the hypotheses it
was using.** That theorem's argument is *the ring has infinitely many primes and every candidate
denominator misses one of them*, and `ℤ` entered it only through `Int.natAbs` bookkeeping and
through the two-branch case split that a principal ideal ring makes possible. Here the bookkeeping
is the cut-down family above, there is one branch, and the ring is arbitrary; the `example` in
`section Int` below recovers the `ℤ` statement.

**It gives no criterion for when the predicate holds** at a general prime — one direction is proved
and `FormalSpectrum.hasBoundedDenominatorsAt_maximalIdeal` already shows the behaviour is not
universal — and **it refutes no theorem.** EGA I 10.8 asks for a Noetherian adic hypothesis on a
scheme; what fails here is the stalk half at a formal spectrum whose ideal of definition is
`FormalSpectrum.powerSeriesXIdeal`, and no hypothesis of that theorem is claimed to hold. -/
theorem not_isStalkLimit_powerSeriesX_of_infinite_primeIdeals
    (hinf : {P : Ideal R | P.IsPrime ∧ P ≠ ⊥}.Infinite)
    (x : FormalSpectrum (powerSeriesXIdeal R)) : ¬ IsStalkLimit (powerSeriesXIdeal R) x := by
  rw [eq_powerSeriesXPoint R x, isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt]
  exact not_hasBoundedDenominatorsAt_of_infinite_primeIdeals R _ hinf

/-- **The generic-point criterion is the case `p = ⊥`**, which is what makes the word
*generalisation* above a checked statement rather than an assertion.
`FormalSpectrum.hasBoundedDenominatorsAt_bot_iff` is the comparison and there is nothing else in
the step.

An `example` rather than a theorem, on the convention the `example` under
`FormalSpectrum.not_hasBoundedDenominators_of_primeIdeals` already follows here:
`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals` is on the tree already, is
stated in the `FormalSpectrum.HasBoundedDenominators` idiom its consumers use, and stays. -/
example (hinf : {P : Ideal R | P.IsPrime ∧ P ≠ ⊥}.Infinite) : ¬ HasBoundedDenominators R := by
  rw [← hasBoundedDenominatorsAt_bot_iff]
  exact not_hasBoundedDenominatorsAt_of_infinite_primeIdeals R ⊥ hinf

end DimOnePoint

section Dedekind

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- **The classification at a Dedekind domain: the denominator condition holds exactly when there
are finitely many prime ideals.**

This is `FormalSpectrum.hasBoundedDenominators_iff_finite_primes` with *primes up to associates*
replaced by *prime ideals*, and it is not a corollary of it — a nonprincipal maximal ideal
contributes no prime element, so neither statement implies the other. What replaces the element
criterion is `FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals`, which is where the
work is.

**The backward direction is where the Dedekind hypothesis is used, and it derives unique
factorisation rather than dispensing with it.** Finitely many primes at a Dedekind domain forces
principality, by Mathlib's `IsPrincipalIdealRing.of_finite_primes`; a principal ideal domain is a
unique factorisation domain; and
`FormalSpectrum.finite_prime_associates_of_finite_primeIdeals` supplies the element
classification's hypothesis from the ideal one. So the counterexample file's sentence about that
direction — *that passage is factorisation* — is still exactly right.

**The forward direction assumes strictly less than Dedekind**: it is
`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals`, which needs only Noetherian
and dimension at most one, and the set of nonzero primes is the set of primes with `⊥` removed.

`{I : Ideal R | I.IsPrime}` rather than the nonzero primes, because that is the spelling
`IsPrincipalIdealRing.of_finite_primes` takes and the two differ by the single element `⊥`, which
is prime here since `R` is a domain.

**No countability hypothesis**, and none is removed from anything: the refuting direction exhibits
one `ℕ`-indexed family rather than quantifying over `Frac R`. -/
theorem hasBoundedDenominators_iff_finite_primeIdeals :
    HasBoundedDenominators R ↔ {I : Ideal R | I.IsPrime}.Finite := by
  constructor
  · intro h
    by_contra hinf
    rw [Set.not_finite] at hinf
    refine not_hasBoundedDenominators_of_infinite_primeIdeals R ?_ h
    refine (hinf.sdiff (Set.finite_singleton (⊥ : Ideal R))).mono ?_
    rintro P ⟨hp, hne⟩
    exact ⟨hp, hne⟩
  · intro hfin
    haveI : IsPrincipalIdealRing R := IsPrincipalIdealRing.of_finite_primes hfin
    exact (hasBoundedDenominators_iff_finite_primes R).mpr
      (finite_prime_associates_of_finite_primeIdeals R hfin)

/-- **A Dedekind domain satisfying the denominator condition is a principal ideal ring**, so no
Dedekind domain of class number greater than one satisfies it.

The classification above into `IsPrincipalIdealRing.of_finite_primes`. Read through
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators` this is a
statement about the stalk half of EGA I 10.8 at the generic point of `R⟦X⟧`: **the half fails at
every Dedekind domain that is not a principal ideal ring** — a class of rings about which the
element classification says nothing at all, since none of them is a unique factorisation domain.

**At a ring of integers this theorem is vacuous, and the class number is not what decides the
question there.** `FormalSpectrum.not_hasBoundedDenominators_ringOfIntegers`
(`FormalSchemes.StructureSheafStalkPowerSeriesNumberField`) refutes the condition at `𝓞 K` for
every number field `K`, class number one or not, because
`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals` above asks only for infinitely
many nonzero primes. That is a fact about rings of integers and **not** a defect in this theorem,
which has content wherever the condition does hold — at a discrete valuation ring and at a
semilocal Dedekind domain, both of which are principal ideal rings.

**No ring is exhibited here**, and the reason is import cost rather than difficulty; see this
file's *What is not proved here*. The statement above is not conditional on exhibiting one: it is a
theorem about every Dedekind domain, and `ℤ` is a Dedekind domain, which the `example` in the
`Int` section below uses in the other direction. -/
theorem isPrincipalIdealRing_of_hasBoundedDenominators (h : HasBoundedDenominators R) :
    IsPrincipalIdealRing R :=
  IsPrincipalIdealRing.of_finite_primes ((hasBoundedDenominators_iff_finite_primeIdeals R).mp h)

/-- **The classification read at the predicate: at a Dedekind domain the stalk of the completion is
the completion of the stalk at the generic point of `R⟦X⟧` exactly when `R` has finitely many prime
ideals.**

`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators` composed with the
classification above. It is the Dedekind twin of
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_finite_primes`, which is the same
composition at a unique factorisation domain with the element classification in place of this one,
and it exists for the reason that one does: **a classification of the condition is not yet a
statement about EGA I 10.8 until it is read at the predicate.**

**The two are incomparable, and neither is an instance of the other in either direction.**
`[UniqueFactorizationMonoid R]` and `[IsDedekindDomain R]` neither contains the other — `ℂ[X, Y]`
is the first and not the second, a Dedekind domain of class number greater than one is the second
and not the first — so there is no substitution that turns one statement into the other. That is
the incomparability the module docstring records for the two classifications, transported along a
`↔` that carries no hypothesis of its own. **Where both apply, at a principal ideal domain, they
agree**, and that is checked immediately below as an `example` rather than asserted here.

**The two counts differ by `⊥` even where both apply**, and a reader comparing the two `↔`s will
meet it first. `{I : Ideal R | I.IsPrime}` contains `⊥`, which is prime because `R` is a domain and
which is the span of no prime element; `{a : Associates R | Prime a}` does not. At each of the
three values the counterexample file records — all three of which are principal ideal domains — the
ideal side is the associate side with `⊥` adjoined: at a field `{⊥}` against `∅`, at a discrete
valuation ring `{⊥, 𝔪}` against the singleton, and at `ℤ` both are infinite. Finiteness is
insensitive to one element, which is why the `↔`s agree while the cardinalities do not.

**One point, and not a repair.** This is EGA I 10.8's stalk half at the generic point of `R⟦X⟧` and
at no other point, at the ideal of definition `(X)` and no other, and over a power series ring and
nothing else; it enlarges the class of rings over which the half is known to fail and settles
nothing about which hypothesis would make the general statement true. -/
theorem isStalkLimit_powerSeriesXGenericPoint_iff_finite_primeIdeals :
    IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) ↔
      {I : Ideal R | I.IsPrime}.Finite :=
  (isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators R).trans
    (hasBoundedDenominators_iff_finite_primeIdeals R)

/-- **Where both classifications apply they agree.** A principal ideal domain is both a Dedekind
domain and a unique factorisation domain, and there the two right-hand sides are equivalent —
because each of them is equivalent to the same predicate at the same point.

The proof is the two `↔`s and nothing else, which is the whole point of writing it: it is a check on
the **pair**, not on either one, and it is the direction the module docstring's *"where both apply,
at a principal ideal domain, they agree"* asserts. The forward implication is already a theorem at
an arbitrary domain
(`FormalSpectrum.finite_prime_associates_of_finite_primeIdeals`), so what is new here is the
converse — and the converse is not proved by counting anything.

An `example`, because it is the agreement of two named theorems rather than a statement of this
file's, and because a claim about the relation between two theorems is worth putting where the
build checks it rather than leaving in a docstring. -/
example [IsPrincipalIdealRing R] :
    {I : Ideal R | I.IsPrime}.Finite ↔ {a : Associates R | Prime a}.Finite :=
  (isStalkLimit_powerSeriesXGenericPoint_iff_finite_primeIdeals R).symm.trans
    (isStalkLimit_powerSeriesXGenericPoint_iff_finite_primes R)

/-- **The stalk half of EGA I 10.8 fails at the generic point of `R⟦X⟧` over every Dedekind domain
that is not a principal ideal ring**, stated at the predicate.

`FormalSpectrum.isPrincipalIdealRing_of_hasBoundedDenominators` with the predicate turned into the
condition by `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`.

**It is the contrapositive that is the sentence worth having**, and it is the sentence this cluster
is for: a Dedekind domain whose class group is nontrivial is a ring where the stalk of the
completion is *not* the completion of the stalk, at a point of a formal spectrum, and that is a
statement about EGA I 10.8 rather than about denominators in a fraction field. It earns a name for
the same reason `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_finite_primes` does,
one file down: it is one composition away from theorems that are already named, and it is the form
in which the fact is recognisable to a reader who has not read
`FormalSpectrum.HasBoundedDenominators`.

**At a ring of integers it is vacuous, for the reason the theorem it composes is** — the hypothesis
is never met there, since `FormalSpectrum.not_hasBoundedDenominators_ringOfIntegers`
(`FormalSchemes.StructureSheafStalkPowerSeriesNumberField`) refutes the condition at every `𝓞 K`.
Where it has content is where the condition holds and principality is not free: see the fences on
`FormalSpectrum.isPrincipalIdealRing_of_hasBoundedDenominators` above.

**It does not say the predicate varies across a single formal spectrum.** That needs a **local**
domain failing the condition and none is on this tree; this is one point of one spectrum, and a
Dedekind domain that is not a principal ideal ring is not local. -/
theorem isPrincipalIdealRing_of_isStalkLimit_powerSeriesXGenericPoint
    (h : IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)) :
    IsPrincipalIdealRing R :=
  isPrincipalIdealRing_of_hasBoundedDenominators R
    ((isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators R).mp h)

end Dedekind

section Int

/-- **The classification is not vacuous, and at `ℤ` it is read in the direction that is new.**
`FormalSpectrum.not_hasBoundedDenominators_int` is built from an explicit family in `Frac ℤ`
(`FormalSpectrum.unitFractionSeries`), and
`FormalSpectrum.hasBoundedDenominators_iff_finite_primeIdeals` turns that family into a cardinality
of `Spec ℤ`: **`ℤ` has infinitely many prime ideals.**

The fact is Euclid's and the transport is the point — nothing on this tree could previously carry a
statement about denominators in `Frac ℤ` over to a statement about the ideals of `ℤ`.
`IsDedekindDomain ℤ` is found by instance synthesis with no help.

An `example`, because it proves a statement of Mathlib's and not one of this file's. -/
example : {I : Ideal ℤ | I.IsPrime}.Infinite := fun hfin =>
  not_hasBoundedDenominators_int ((hasBoundedDenominators_iff_finite_primeIdeals ℤ).mpr hfin)

/-- **`ℤ` has infinitely many nonzero prime ideals**, built from Euclid rather than read off the
classification.

The `example` above gets the same count out of
`FormalSpectrum.hasBoundedDenominators_iff_finite_primeIdeals`, and for that reason cannot be used
to **feed** a criterion that refutes the denominator condition: the transport there runs from
denominators to ideals, and what is wanted here is the other direction. This one runs
`Nat.infinite_setOf_prime` through `Ideal.span_singleton_prime` — the span of a rational prime is
prime and nonzero — and the map `q ↦ (q)` is injective because `(a) = (b)` gives `a ∣ b` through
`Ideal.mem_span_singleton`, and two positive primes dividing each other are equal
(`Nat.prime_dvd_prime_iff_eq`).

It exists so that *`ℤ` satisfies the hypotheses of
`FormalSpectrum.not_isStalkLimit_powerSeriesX_of_infinite_primeIdeals`* is a checked statement
rather than an assertion; the `example` below is that check. -/
theorem infinite_setOf_isPrime_int : {P : Ideal ℤ | P.IsPrime ∧ P ≠ ⊥}.Infinite := by
  classical
  haveI : Infinite {q : ℕ // q ∈ {q : ℕ | q.Prime}} := Nat.infinite_setOf_prime.to_subtype
  have hinj : Function.Injective
      (fun q : {q : ℕ // q ∈ {q : ℕ | q.Prime}} => Ideal.span {((q : ℕ) : ℤ)}) := by
    intro a b hab
    have hdvd : ((a : ℕ) : ℤ) ∣ ((b : ℕ) : ℤ) := by
      have hmem : ((b : ℕ) : ℤ) ∈ Ideal.span {((a : ℕ) : ℤ)} := by
        simp only at hab
        rw [hab]
        exact Ideal.mem_span_singleton_self _
      exact Ideal.mem_span_singleton.mp hmem
    exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq a.2 b.2).mp (by exact_mod_cast hdvd))
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hinj)
  rintro _ ⟨a, rfl⟩
  have hp : Prime ((a : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp a.2
  exact ⟨(Ideal.span_singleton_prime hp.ne_zero).mpr hp,
    fun h => hp.ne_zero (Ideal.span_singleton_eq_bot.mp h)⟩

/-- **`FormalSpectrum.not_isStalkLimit_powerSeriesX_int` is the case `R = ℤ`**, which is what makes
*the everywhere-failure at `Spf (ℤ⟦X⟧, (X))` is not about `ℤ`* a checked statement rather than an
assertion.

An `example`: the statement belongs to `FormalSchemes.StructureSheafStalkPowerSeriesPoint` and
stays there, where its proof splits `Spec ℤ` into the generic point and the closed points and
treats each with its own argument — the split a principal ideal ring makes possible and the general
theorem does not need. -/
example (x : FormalSpectrum (powerSeriesXIdeal ℤ)) : ¬ IsStalkLimit (powerSeriesXIdeal ℤ) x :=
  not_isStalkLimit_powerSeriesX_of_infinite_primeIdeals ℤ infinite_setOf_isPrime_int x

end Int

end FormalSpectrum

end
