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

Through `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`
(`FormalSchemes.StructureSheafStalkPowerSeriesGeneric`) both are statements about the stalk half of
EGA I 10.8 at the generic point of `R⟦X⟧`: it fails over every Dedekind domain with infinitely many
primes, and over every Dedekind domain whose class number is greater than one.

## Where the element criterion stops and the ideal criterion goes on

The two refuting criteria share everything but their last step. Both apply the condition to the
family of inverses `n ↦ (s n)⁻¹` and land on `m ^ k = r * s n` back in `R`. Then

* `FormalSpectrum.not_hasBoundedDenominators_of_primes` reads that as `p n ∣ m ^ k` and finishes
  with `Prime.dvd_of_dvd_pow`, which needs `p n` to be a prime **element**;
* `FormalSpectrum.not_hasBoundedDenominators_of_primeIdeals` reads it as `m ^ k ∈ P n`, by
  `Ideal.mul_mem_left` from `s n ∈ P n`, and finishes with `Ideal.IsPrime.mem_of_pow_mem`.

**That is the step a nonprincipal maximal ideal makes impossible in the element version and trivial
here**, and it is the whole content of the generalisation. Neither criterion implies the other: the
element version's hypothesis is about divisibility by a single `m` and asks for no witnesses, while
this one asks for a nonzero element of each ideal and no arithmetic at all.

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
* `FormalSpectrum.hasBoundedDenominators_iff_finite_primeIdeals`: **the classification at a Dedekind
  domain** — the condition holds **iff** `{I : Ideal R | I.IsPrime}` is finite.
* `FormalSpectrum.isPrincipalIdealRing_of_hasBoundedDenominators`: **and a Dedekind domain
  satisfying it is a principal ideal ring**, so no Dedekind domain of class number greater than one
  satisfies it.

## What is *not* proved here

**Nothing here repairs EGA I 10.8's stalk half.** It refutes the stalk half at the generic point of
`R⟦X⟧` over a larger class of rings than `ℤ`; which hypothesis makes the general statement true is
undetermined and nothing below bears on it.

**Nothing here says `FormalSpectrum.IsStalkLimit` varies across a single formal spectrum.** That
would need a **local** domain failing the denominator condition, and none is on this tree; a
Dedekind domain with infinitely many primes is not local, and neither is one of class number greater
than one.

**No ring is instantiated except `ℤ`.** The sharp reading of
`FormalSpectrum.isPrincipalIdealRing_of_hasBoundedDenominators` is at a ring of integers of class
number greater than one, where the element classification says nothing at all. That is deliberately
not written down: it needs the infinitude of the primes of `𝓞 K`, which is not in Mathlib as a
`Set.Infinite` statement and would have to be built from
`Ideal.exists_ideal_over_prime_of_isIntegral` and `Nat.exists_infinite_primes`, and it would drag a
number-theory import into a formal-schemes file. **The consequence is stated in prose and
instantiated nowhere.**

**Nothing here bears on semilocal domains in general.** The classification decides the condition at
a **semilocal Dedekind** domain, positively, because that is a Dedekind domain with finitely many
primes; a semilocal domain that is not Dedekind is untouched, as are Prüfer and valuation rings and
the general domain.

**No hypothesis is removed from anything on the tree.** Neither `[Countable (FractionRing R)]` from
the collapse, nor `[UniqueFactorizationMonoid R]` from the classification this generalises, nor
`[IsDomain R]` from the condition itself.

## Placement

A leaf over `FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, which holds
`FormalSpectrum.HasBoundedDenominators`, both refuting criteria and the element classification:
forward closure **53** project modules besides itself, reverse closure **0**, counted by walking
every `^import FormalSchemes.` line over the 555 modules under `FormalSchemes/` (a module is not
counted in its own closure; the aggregator at the repository root is outside the walk).

Appending to that file was the alternative and is cheaper by a module. It is not taken for two
reasons, and the second is the load-bearing one. It is 2523 lines with 80 declarations and is the
most edited file on this board, so a leaf keeps two concurrent rows off one file; and **the two
Mathlib imports this material needs would otherwise be paid by a module that does not need them.**
That file's own discrete-valuation-ring section advertises that it *"adds no Mathlib import
either"*, so the imports are a cost worth isolating, and they are not avoidable: without
`Mathlib/RingTheory/DedekindDomain/PID.lean` the constant `Ring.DimensionLEOne` does not exist and
without `Mathlib/RingTheory/Ideal/MinimalPrime/Noetherian.lean` the finiteness above has nothing to
cite.

**Only one of the two is new to the project's Mathlib closure, and it is worth saying which**, since
the import line and the build cost are different things: walking the `import` graph over Mathlib's
sources from every `import Mathlib` line in `FormalSchemes/`, the closure grows from **2910** to
**2912** modules, the additions being `Mathlib/RingTheory/DedekindDomain/PID.lean` and its own
`Mathlib/RingTheory/PrincipalIdealDomainOfPrime.lean`.
`Mathlib/RingTheory/Ideal/MinimalPrime/Noetherian.lean` was **already** reached by this project, so
naming it here costs a line and no build.

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

/-- **Infinitely many nonzero primes refutes the denominator condition**, at a Noetherian domain of
dimension at most one.

`Set.Infinite.natEmbedding` turns the infinite set of nonzero primes into an injective `ℕ`-indexed
family of them, `Submodule.exists_mem_ne_zero_of_ne_bot` supplies a nonzero element of each, and the
criterion above consumes both.

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
rather than inside the classification below: what the Dedekind hypothesis buys there is
principality, and that is used on the other side of this map. -/
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
every Dedekind domain that is not a principal ideal ring**, and in particular at every ring of
integers of class number greater than one — a class of rings about which the element classification
says nothing at all, since none of them is a unique factorisation domain.

**No such ring is exhibited here**, and the reason is import cost rather than difficulty; see this
file's *What is not proved here*. The statement above is not conditional on exhibiting one: it is a
theorem about every Dedekind domain, and `ℤ` is a Dedekind domain, which the `example` below uses
in the other direction. -/
theorem isPrincipalIdealRing_of_hasBoundedDenominators (h : HasBoundedDenominators R) :
    IsPrincipalIdealRing R :=
  IsPrincipalIdealRing.of_finite_primes ((hasBoundedDenominators_iff_finite_primeIdeals R).mp h)

end Dedekind

section Int

/-- **The classification is not vacuous, and at `ℤ` it is read in the direction that is new.**
`FormalSpectrum.not_hasBoundedDenominators_int` is built from an explicit family in `Frac ℤ`
(`FormalSpectrum.unitFractionSeries`), and the `↔` above turns that family into a cardinality of
`Spec ℤ`: **`ℤ` has infinitely many prime ideals.**

The fact is Euclid's and the transport is the point — nothing on this tree could previously carry a
statement about denominators in `Frac ℤ` over to a statement about the ideals of `ℤ`.
`IsDedekindDomain ℤ` is found by instance synthesis with no help.

An `example`, because it proves a statement of Mathlib's and not one of this file's. -/
example : {I : Ideal ℤ | I.IsPrime}.Infinite := fun hfin =>
  not_hasBoundedDenominators_int ((hasBoundedDenominators_iff_finite_primeIdeals ℤ).mpr hfin)

end Int

end FormalSpectrum

end
