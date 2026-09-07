import FormalSchemes.StructureSheafStalkPowerSeriesDedekind
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.GoingUp

set_option linter.style.header false

/-!
# The denominator condition fails at the ring of integers of every number field

`FormalSchemes.StructureSheafStalkPowerSeriesDedekind` classifies
`FormalSpectrum.HasBoundedDenominators` at a Dedekind domain — it holds exactly when there are
finitely many prime ideals — and refutes it, through
`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals`, at every Noetherian domain of
dimension at most one with infinitely many nonzero primes. It instantiates that at no ring but `ℤ`,
and says why: the infinitude of the primes of `𝓞 K` is not in Mathlib, and building it drags a
number-theory import in.

**This file is that import, paid on a leaf**, and what it buys is not one ring but a family:

> `FormalSpectrum.not_hasBoundedDenominators_ringOfIntegers`: the denominator condition **fails at
> `𝓞 K` for every number field `K`**.

and therefore

> `FormalSpectrum.not_isStalkLimit_powerSeriesXRingOfIntegersGenericPoint`: the stalk half of
> EGA I 10.8 **fails at the generic point of `(𝓞 K)⟦X⟧`, for every number field `K`**.

## The class number does not enter, and that is the point

The reading a reader reaches for first is
`FormalSpectrum.isPrincipalIdealRing_of_hasBoundedDenominators` at a ring of integers of class
number greater than one: the element classification of
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` says nothing there, since no such ring
is a unique factorisation domain. **That is correct about the element classification and much too
weak about the ideal one**, and the theorem to read through is the refuting criterion rather than
the corollary. `FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals` asks for
Noetherian, dimension at most one, and infinitely many nonzero primes — and every ring of integers
of every number field has all three, class number one or not.

Two consequences worth stating in those terms.

* **The refutation is unconditional.** `FormalSpectrum.not_hasBoundedDenominators_ringOfIntegers`
  carries no class-number hypothesis, no unique-factorisation hypothesis and no countability
  hypothesis.
* **`FormalSpectrum.isPrincipalIdealRing_of_hasBoundedDenominators` is vacuous at a ring of
  integers**: its hypothesis is never met there. That is a statement about rings of integers and
  **not** a defect in that theorem, which is not vacuous in general — a discrete valuation ring and
  a semilocal Dedekind domain both satisfy the denominator condition and are principal ideal rings,
  and they are where it has content.

For the same reason **no class-number theorem is stated here.** Mathlib states class number one as
principality of the ring of integers (`Mathlib/NumberTheory/NumberField/ClassNumber.lean`), so that
statement composes with the two facts above — and the composite is vacuous. A name for it would
suggest the class number decides something here, and it decides nothing.

## Where the infinitude comes from

Euclid, transported along `ℤ → 𝓞 K`. For each rational prime `p` the ideal `(p)` is prime in `ℤ`,
so going-up (`Ideal.exists_ideal_over_prime_of_isIntegral`) produces a prime `Q` of `𝓞 K` with
`Q.comap (algebraMap ℤ (𝓞 K)) = (p)`, and `Nat.infinite_setOf_prime` supplies infinitely many `p`.

Two steps of that are not free and are worth naming, because both are where a shorter-looking
argument goes wrong.

* **`Q ≠ ⊥` is not part of what going-up gives.** It comes from `Ideal.comap_bot_of_injective`:
  the contraction of `⊥` along an injective `algebraMap` is `⊥`, and `(p) ≠ ⊥`.
* **The family is injective through the contractions and not through the ideals.** There is a choice
  of `Q` at each `p`, and at a split prime that choice is real, so nothing about the `Q` themselves
  is canonical. Their contractions are, and `(p) = (q)` in `ℤ` forces `p = q` for positive primes.

## Main results

* `FormalSpectrum.exists_isPrime_comap_span_singleton_natCast`: **lying over a rational prime** —
  every `(p)` with `p` prime is the contraction of a nonzero prime ideal of `𝓞 K`.
* `FormalSpectrum.infinite_setOf_isPrime_ringOfIntegers`: **`𝓞 K` has infinitely many nonzero prime
  ideals**, for every number field `K`.
* `FormalSpectrum.not_hasBoundedDenominators_ringOfIntegers`: **the denominator condition fails at
  `𝓞 K`**, with no class-number, factorisation or countability hypothesis.
* `FormalSpectrum.not_isStalkLimit_powerSeriesXRingOfIntegersGenericPoint`: **and so
  `FormalSpectrum.IsStalkLimit` is false at `(X) ⊆ (𝓞 K)⟦X⟧` at the generic point.**

The last is the second family of negative values of `FormalSpectrum.IsStalkLimit` on this tree,
after `FormalSpectrum.not_isStalkLimit_powerSeriesXIntGenericPoint`, and the first that is a family
rather than a single ring. The two are worth reading as a pair: the refutation at `ℤ` is built by
hand from an explicit series, `FormalSpectrum.unitFractionSeries`, whose coefficients are arranged
to defeat every `m`; this one names no element of any fraction field at all and runs entirely
through the count of prime ideals.

## What is *not* proved here

**Nothing here repairs EGA I 10.8's stalk half.** It enlarges the class of rings over which that
half is known to fail. Which hypothesis makes the general statement true is undetermined and nothing
below bears on it.

**Nothing here says `FormalSpectrum.IsStalkLimit` varies across a single formal spectrum.** That
needs a **local** domain failing the denominator condition, and no ring of integers of a number
field is local. One is built on the sibling leaf
`FormalSchemes.StructureSheafStalkPowerSeriesLocal`, out of the same arbitrary-domain criterion and
over a ring nothing here reaches.

**No individual number field is instantiated, and none is wanted.**
`FormalSpectrum.not_hasBoundedDenominators_ringOfIntegers` is a statement about every `K` and needs
no witness; a specific field would buy nothing and cost a heavier import. The `example` below is at
`ℚ`, where `NumberField ℚ` is already an instance, and it is a non-vacuity check rather than a
sharper reading.

**Nothing here bears on orders in number fields**, though
`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals` would apply to them: they are
Noetherian of dimension at most one, and only the integral closedness is missing. Mathlib carries no
`Set.Infinite` statement about the primes of an order, and neither does this file.

**No hypothesis is removed from anything on the tree.** Not `[Countable (FractionRing R)]` from the
collapse, not `[UniqueFactorizationMonoid R]` from the element classification, not
`[IsDedekindDomain R]` from the ideal classification.

## Placement

A leaf over `FormalSchemes.StructureSheafStalkPowerSeriesDedekind`, which holds the refuting
criterion this file instantiates: forward closure **54** project modules besides itself, reverse
closure **0**, counted by walking every `^import FormalSchemes.` line over the 559 modules under
`FormalSchemes/` (a module is not counted in its own closure; the aggregator at the repository root
is outside the walk).

**The leaf exists to isolate a Mathlib import, which is the reason the Dedekind module gave for not
doing this work itself.** Appending here would push
`Mathlib/NumberTheory/NumberField/Basic.lean` under everything that ever imports the Dedekind
classification, and that classification is general
commutative algebra with no number theory in it. The chain is three modules each one hypothesis
narrower — arbitrary domain, Dedekind domain, ring of integers — and the imports get heavier in the
same direction. The price of the leaf is a forward pointer from the Dedekind module's
`## What is *not* proved here`, which this branch pays.

**Only one of the two Mathlib imports costs a build, and the cost is 22 modules.** Walking
`import` and `public import` over Mathlib's sources from every `import Mathlib…` line under
`FormalSchemes/`, the project's Mathlib closure grows from **2699** to **2721**;
`Mathlib/NumberTheory/NumberField/Basic.lean` brings all 22 with it, and
`Mathlib/RingTheory/Ideal/GoingUp.lean` was **already** reached, so naming it costs a line and no
build. That is an order of magnitude more than the two modules
`FormalSchemes.StructureSheafStalkPowerSeriesDedekind` paid, and it is the whole reason this is a
leaf rather than an appendix to that file.

Two cautions for whoever re-measures. **Mathlib writes `public import`**; a walk matching only
`^import ` returns a closure two orders of magnitude too small. And the absolute figure depends on
the convention — restricting to names matching `^import <Name>$` and to `Mathlib.*` gives 2699,
while admitting the `import Mathlib…` lines that occur inside docstrings gives 2704 and following
non-Mathlib packages as well gives 2954. **The delta is 22 under all three**, which is why the
delta and not the absolute is the figure quoted here; the same caution applies to the 2910 quoted
by `FormalSchemes.StructureSheafStalkPowerSeriesDedekind`, whose delta of 2 reproduces exactly.

**The `lake build` job count goes 3455 to 3479, and the walk accounts for 23 of those 24** — the 22
Mathlib modules and this leaf. The twenty-fourth is not a source module in any package the project
depends on; the same walk accounted for that file's `+3` exactly, so the discrepancy is recorded
here rather than explained away.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX).
-/

noncomputable section

universe u

namespace FormalSpectrum

open NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- **Lying over a rational prime.** For every prime `p : ℕ` there is a nonzero prime ideal of
`𝓞 K` whose contraction along `ℤ → 𝓞 K` is `(p)`.

`Ideal.exists_ideal_over_prime_of_isIntegral` at `(p)`, which is prime in `ℤ` by
`Ideal.span_singleton_prime`; `Algebra.IsIntegral ℤ (𝓞 K)` is found by instance synthesis, and the
side condition on the kernel is `FaithfulSMul.ker_algebraMap_eq_bot`.

**`Q ≠ ⊥` is not part of what going-up gives** and is proved separately: the contraction of `⊥`
along an injective `algebraMap` is `⊥` (`Ideal.comap_bot_of_injective`), so a `Q` with contraction
`(p) ≠ ⊥` cannot be `⊥`. It is stated here rather than derived at the call site because
`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals` asks for nonzero primes.

**The contraction is what makes the family below injective**, and it is why it appears in the
statement at all. The ideal `Q` is not canonical — at a prime that splits there is a genuine choice,
and this statement makes it — but the contraction is, so distinct rational primes give distinct
`Q`. -/
theorem exists_isPrime_comap_span_singleton_natCast {p : ℕ} (hp : p.Prime) :
    ∃ Q : Ideal (𝓞 K), Q.IsPrime ∧ Q ≠ ⊥ ∧
      Q.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : ℤ)} := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hp
  have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {(p : ℤ)} := by
    rw [FaithfulSMul.ker_algebraMap_eq_bot ℤ (𝓞 K)]
    exact bot_le
  obtain ⟨Q, -, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := 𝓞 K) (Ideal.span {(p : ℤ)}) ⊥ (by simpa [← RingHom.ker_eq_comap_bot] using hker)
  refine ⟨Q, hQp, ?_, hQc⟩
  rintro rfl
  rw [Ideal.comap_bot_of_injective _ (RingHom.injective_int (algebraMap ℤ (𝓞 K)))] at hQc
  have hmem : ((p : ℤ)) ∈ (⊥ : Ideal ℤ) := by
    rw [hQc]; exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_bot] at hmem
  exact hp.ne_zero (by exact_mod_cast hmem)

/-- **The ring of integers of a number field has infinitely many nonzero prime ideals.**

Euclid's theorem transported along `ℤ → 𝓞 K`: `Nat.infinite_setOf_prime` supplies infinitely many
rational primes, the lemma above lies a nonzero prime of `𝓞 K` over each, and the resulting family
is injective because its contractions are distinct — `(p) = (q)` in `ℤ` gives `p ∣ q`, and two
positive primes dividing each other are equal.

The shape is `Set.infinite_range_of_injective` and then `Set.Infinite.mono`, which is the shape
`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals` uses in the opposite direction:
there an injective `ℕ`-indexed family is shown *not* to fit inside a finite set, here one is built
to exhibit an infinite one. The two are worth reading as a pair, since this lemma exists only to
feed that one.

**No class number and no integral closedness.** Nothing above uses that `𝓞 K` is a Dedekind domain;
integrality of `ℤ → 𝓞 K` and injectivity are the whole hypothesis. -/
theorem infinite_setOf_isPrime_ringOfIntegers :
    {P : Ideal (𝓞 K) | P.IsPrime ∧ P ≠ ⊥}.Infinite := by
  classical
  haveI : Infinite {p : ℕ // p ∈ {p : ℕ | p.Prime}} := Nat.infinite_setOf_prime.to_subtype
  choose F hFp hFne hFc using fun p : {p : ℕ // p ∈ {p : ℕ | p.Prime}} =>
    exists_isPrime_comap_span_singleton_natCast K p.2
  have hinj : Function.Injective F := by
    intro a b hab
    have h : Ideal.span {((a : ℕ) : ℤ)} = Ideal.span {((b : ℕ) : ℤ)} := by
      rw [← hFc a, ← hFc b, hab]
    have hdvd : ((a : ℕ) : ℤ) ∣ ((b : ℕ) : ℤ) := by
      rw [← Ideal.mem_span_singleton, h]; exact Ideal.mem_span_singleton_self _
    exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq a.2 b.2).mp (by exact_mod_cast hdvd))
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hinj)
  rintro _ ⟨a, rfl⟩
  exact ⟨hFp a, hFne a⟩

/-- **The denominator condition fails at the ring of integers of every number field.**

`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals` at the infinitude above.
`IsDedekindDomain (𝓞 K)` is found by instance synthesis and supplies the three hypotheses that
criterion needs — `IsDomain`, `IsNoetherianRing` and `Ring.DimensionLEOne` — so the only content
here is the count of prime ideals.

**No class number, and that is the whole point of the statement.** The condition fails at
`𝓞 K` whether or not `𝓞 K` is a principal ideal ring, so
`FormalSpectrum.isPrincipalIdealRing_of_hasBoundedDenominators` is **vacuous** at every ring of
integers — a fact about rings of integers and not a defect in that theorem, which is not vacuous in
general: a discrete valuation ring and a semilocal Dedekind domain satisfy the condition and are
principal ideal rings. What is true at a ring of integers of class number greater than one is the
weaker thing, that `FormalSpectrum.hasBoundedDenominators_iff_finite_primes` says nothing there
since no such ring is a unique factorisation domain; that is a statement about the *element*
classification and it is not what refutes the condition.

**No countability hypothesis either**, for the reason the ideal classification has none: the
refutation exhibits one `ℕ`-indexed family rather than quantifying over the whole of
`Frac (𝓞 K)`. -/
theorem not_hasBoundedDenominators_ringOfIntegers : ¬ HasBoundedDenominators (𝓞 K) :=
  not_hasBoundedDenominators_of_infinite_primeIdeals (𝓞 K)
    (infinite_setOf_isPrime_ringOfIntegers K)

/-- **`FormalSpectrum.IsStalkLimit` is false at `(X) ⊆ (𝓞 K)⟦X⟧` at the generic point**, for every
number field `K`.

The theorem above read through
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`.

**The second family of negative values of the predicate on this tree**, after
`FormalSpectrum.not_isStalkLimit_powerSeriesXIntGenericPoint`, and the first that is a family rather
than a single ring. The two refutations are built in opposite ways and the contrast is the reason to
have both: the one at `ℤ` exhibits `FormalSpectrum.unitFractionSeries`, a series in `ℚ⟦X⟧` whose
coefficients are arranged so that no single `m` clears them all, and this one names no element of
any fraction field — it counts prime ideals.

**This does not repair EGA I 10.8's stalk half and does not claim to.** It enlarges the class of
rings over which that half is known to fail. Nor does it say the predicate varies across a single
formal spectrum: that needs a **local** domain failing the denominator condition, and `𝓞 K` is not
local. -/
theorem not_isStalkLimit_powerSeriesXRingOfIntegersGenericPoint :
    ¬ IsStalkLimit (powerSeriesXIdeal (𝓞 K)) (powerSeriesXGenericPoint (𝓞 K)) := fun h =>
  not_hasBoundedDenominators_ringOfIntegers K
    ((isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators (𝓞 K)).mp h)

/-- **The statements above are not vacuous**: `NumberField ℚ` is an instance, so `ℚ` is a value of
every one of them.

Read at `ℚ` this says that `𝓞 ℚ` has infinitely many prime ideals and that the denominator
condition fails there. **It is not `FormalSpectrum.not_hasBoundedDenominators_int`**, and must not
be read as it: `𝓞 ℚ` is isomorphic to `ℤ` but not definitionally equal to it, and nothing here
transports along that isomorphism. What it checks is that the hypotheses above are satisfiable, not
that they recover a theorem the tree already has.

An `example`, because it proves no statement that does not already have a name. -/
example : ¬ HasBoundedDenominators (𝓞 ℚ) := not_hasBoundedDenominators_ringOfIntegers ℚ

end FormalSpectrum

end
