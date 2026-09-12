import FormalSchemes.StructureSheafStalkPowerSeriesCounterexample

set_option linter.style.header false

/-!
# `IsStalkLimit` at an arbitrary point of `Spf (R⟦X⟧, (X))`

`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` decides
`FormalSpectrum.IsStalkLimit` — the stalk half of EGA I 10.8, *the stalk of the completion is the
completion of the stalk* — at the **generic** point of `Spf (R⟦X⟧, (X))` for every domain, and
`FormalSchemes.StructureSheafStalkPowerSeries` decides it at the **closed** point of that space for
every local ring. Those are two points, and that file's own `## What is *not* proved here` names
the gap first among the three things it says a successor needs: *the predicate at a point of
`Spf (R⟦X⟧, (X))` other than the generic one*.

**This file closes that one.** The space is `Spec R`
(`FormalSpectrum.powerSeriesXHomeo`), so its points are the primes of `R`; they are named here as
`FormalSpectrum.powerSeriesXPoint`, and

> `FormalSpectrum.isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt`: at **every** point
> of `Spf (R⟦X⟧, (X))` over a domain `R`, `FormalSpectrum.IsStalkLimit` holds exactly when every
> `ℕ`-indexed family in the local ring of `R` at that prime has a single denominator, up to powers,
> that is itself outside the prime.

The two known values are the two ends of that family and are *not* generalisations of anything:
`FormalSpectrum.powerSeriesXPoint_bot` and `FormalSpectrum.powerSeriesXPoint_maximalIdeal` say the
point over `⊥` and the point over the maximal ideal of a local ring are the existing generic and
closed points, and both are `rfl`.

And the predicate genuinely takes a new kind of value:

> `FormalSpectrum.isClosed_and_not_isStalkLimit_powerSeriesXPoint_intTwo`: at `(X) ⊆ ℤ⟦X⟧`, at the
> point over `(2)`, the singleton is **closed** and `FormalSpectrum.IsStalkLimit` is **false**.

Every negative value of the predicate that predates this file is at a **generic** point. That
closed point turns out to be an illustration rather than an exception:

> `FormalSpectrum.not_isStalkLimit_powerSeriesX_int`: at **every** point of `Spf (ℤ⟦X⟧, (X))` —
> the generic point and every closed point, none left over — `FormalSpectrum.IsStalkLimit` is
> **false**.

That is the first formal spectrum on this tree decided everywhere in the **negative**, and it is
no longer the only one: `FormalSpectrum.not_isStalkLimit_powerSeriesX_of_infinite_primeIdeals`
(`FormalSchemes.StructureSheafStalkPowerSeriesDedekind`) is that theorem with `ℤ` replaced by the
hypotheses its proof uses — a Noetherian domain of dimension at most one with infinitely many
nonzero primes — and `FormalSpectrum.not_isStalkLimit_powerSeriesXRingOfIntegers` reads it at the
ring of integers of every number field. It is not the first decided everywhere:
`FormalSpectrum.isStalkLimit_bot` decides `Spf (R, ⊥)` at every point of every commutative ring,
`FormalSpectrum.isStalkLimit_of_isNilpotent` does the same at every finitely generated nilpotent
ideal of definition, and
`FormalSpectrum.isStalkLimit_powerSeriesX_field` decides `Spf (k⟦X⟧, (X))` over a field — and all
three of those are positive. **It is not a claim that `ℤ⟦X⟧` is a pathological ring and it
refutes nothing** — see `## What is *not* proved here` below.

## What it costs, and what it does not

**The identification of the target is freed of both of its hypotheses, and the domain hypothesis
was never doing any work.** Of the three identifications that decide the generic point, one —
`FormalSpectrum.awayCompletionEquivPowerSeriesAway`, which is
`R⟦X⟧{1/f} ≃+* R[1/m]⟦X⟧` — is already stated at every commutative ring and every `f`, and is
reused here unchanged. The other two are stated at the generic point of a domain, and the domain
enters `FormalSpectrum.atPrimeCompletionEquivFractionPowerSeries`'s proof at three places, and none
of the three survives to a general prime as an obligation. Two are bookkeeping — that a nonzero
constant term is invertible in the fraction field, and that a nonzero denominator is a nonzero
divisor — and at a general prime each is read off membership in the prime complement instead. The
third is the argument: a vanishing coefficient is pushed from the fraction field back to `R` along
an injection. At a general prime that becomes a common-denominator argument, because a coefficient
that dies in the local ring is killed by *some* element outside the prime and finitely many such
elements multiply to one element outside it. So

* `FormalSpectrum.atPrimeCompletionEquivLocalizationPowerSeries` holds at **every** commutative
  ring and **every** point, with the target `(Localization.AtPrime p)⟦X⟧`, and
* `FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXPoint_iff` — the **surjectivity**
  half of the criterion, characterised — carries no hypothesis on `R` either.

`[IsDomain R]` is spent on the **injectivity** half alone, where it is used to see that
`R[1/m]` really does sit inside the local ring at `p`, and that is the only place it appears in
the main theorem's proof.

## What is *not* proved here

**The other two questions that paragraph names are untouched.** Nothing here is stated at an ideal
of definition of `R⟦X⟧` other than `(X)`, and nothing at a formal spectrum whose ring is not a
power series ring. Every statement below names `FormalSpectrum.powerSeriesXIdeal`.

**The generic-point theorem *is* recovered as a corollary, and the corollary is one line.**
`FormalSpectrum.powerSeriesXPoint_bot` says the *point* is the same one and is `rfl`, so the main
theorem below is about the same object as
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`. The two
*conditions* are still not literally the same statement — that one is about `FractionRing R` and
this one about `Localization.AtPrime` at `⊥` — and identifying those two models of the same
localization is `FormalSpectrum.hasBoundedDenominatorsAt_bot_iff`. Composing the two gives the
generic-point theorem back, which is what the `example` under
`### The two known points, as values of the criterion` records. It is an `example` and not a
theorem because the statement is already proved elsewhere on this tree and is **not** reproved
here.

**`FormalSpectrum.HasBoundedDenominatorsAt` is classified at a unique factorisation domain and
nowhere else.** `FormalSpectrum.hasBoundedDenominatorsAt_iff_finite_primes` says that at such a
ring, and at **every** prime `p`, the condition holds exactly when finitely many primes up to
associates lie outside `p`; monotonicity in the prime
(`FormalSpectrum.hasBoundedDenominatorsAt_of_le`) and *the denominator condition implies the
condition at every prime* (`FormalSpectrum.hasBoundedDenominatorsAt_of_hasBoundedDenominators`)
are read off the right-hand side. **At a general domain nothing here is claimed and nothing is
guessed at**: `⊥` is one of the primes that `↔` quantifies over, so the ultrapower of `ℤ` that
refutes the classification at the generic point
(`FormalSpectrum.not_forall_hasBoundedDenominators_imp_finite_primes`, in
`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`) refutes this one with the same instance
deleted. **The converse of monotonicity is left open here and is false elsewhere on this tree**, at
`ℤ[X]` localized at `(2, X)`; that ring lives in a module *downstream* of this one, which this
file cannot reach, so the statement is prose here and not a theorem. The one value proved here
that needs no factorisation at all is still at the maximal ideal of a local ring
(`FormalSpectrum.hasBoundedDenominatorsAt_maximalIdeal`), where nothing has to be inverted, and it
is strictly more general than the case of the classification that recovers it.

**The closed point is not decided in general, and neither is the everywhere-failure.** `ℤ` is now
decided at every one of its primes, and `Spf (ℤ⟦X⟧, (X))` was the first space on this tree decided
everywhere in the *negative*; it is not the only one, because
`FormalSpectrum.not_isStalkLimit_powerSeriesX_of_infinite_primeIdeals`
(`FormalSchemes.StructureSheafStalkPowerSeriesDedekind`) decides every point of `Spf (R⟦X⟧, (X))`
the same way over every Noetherian domain of dimension at most one with infinitely many nonzero
primes. `FormalSpectrum.not_isStalkLimit_powerSeriesX_int` **here** is about `ℤ` and about nothing
else, while `FormalSpectrum.isStalkLimit_powerSeriesX_field` decides every prime of a field the
other way. **Two conditions for behaving like `ℤ` are now on this tree and neither of them is at a
general domain.** That theorem is a *sufficient* one and is not a classification, and it is not
given here. `FormalSpectrum.isStalkLimit_powerSeriesXPoint_iff_finite_primes` **below** is a
classification, in both directions, at a unique factorisation domain: the count of prime classes
outside the point's own prime. At a general domain none is given and none is guessed at, and
`FormalSpectrum.hasBoundedDenominatorsAt_maximalIdeal` shows the behaviour is not universal — at a
local ring the condition holds at the maximal ideal.

Neither `FormalSpectrum.isClosed_and_not_isStalkLimit_powerSeriesXPoint_intTwo` nor
`FormalSpectrum.not_isStalkLimit_powerSeriesX_int` refutes a theorem on this tree:
`FormalSpectrum.powerSeriesXClosedPoint` is *defined* only at a local ring, so
`FormalSpectrum.isStalkLimit_powerSeriesXClosedPoint`'s `[IsLocalRing R]` cannot be deleted from a
statement that would not typecheck without it. What they refute is the reading that closed points
are the points where the colimit has nothing to do — over `ℤ` the basic opens through the point
over `(2)` are a genuinely filtered system and the colimit misses `1 / q` for every prime `q`
larger than the denominator on offer.

**Nothing about the Dedekind or Noetherian hypotheses, and nothing consumed from the three modules
that carry this material further.** No statement below carries either of those, and no declaration
of `FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`,
`FormalSchemes.StructureSheafStalkPowerSeriesDedekind` or
`FormalSchemes.StructureSheafStalkPowerSeriesNumberField` is consumed or contradicted — none of
the three is in this file's import closure and none could be. **For two of them the traffic runs
the other way**: the Dedekind module imports this one and carries the criterion below to a
Noetherian domain of dimension at most one, the number-field module imports that, and so a
hypothesis of that shape is where the generalisations of anything here are to be looked for, and
not in this file. The ultrapower module is a genuine sibling — neither file reaches the other.
`[UniqueFactorizationMonoid R]` is the one hypothesis of that list that does appear below, on the
classification at a general prime and its corollaries; what it needs from
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` is
`FormalSpectrum.HasBoundedDenominators` and nothing about factorisation, so the
unique-factorisation lemmas there are named in prose and mirrored rather than reused. **In
particular `FormalSpectrum.hasBoundedDenominators_iff_finite_primes` is recovered as an `example`
below and is not reproved.**

## Placement

Over `FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, which holds the two
identifications at the generic point and the levelwise completion criterion the target
identification below reuses: forward closure **53** project modules besides itself, reverse closure
**3** — `FormalSchemes.StructureSheafStalkPowerSeriesDedekind`, which generalises the criterion
below away from `ℤ`, and the two modules over it,
`FormalSchemes.StructureSheafStalkPowerSeriesNumberField` and
`FormalSchemes.StructureSheafStalkPowerSeriesLocal` — counted by walking every
`^import FormalSchemes.` line over the 562 modules under
`FormalSchemes/` (a module is not counted in its own closure; the aggregator at the repository root
is outside the walk). It adds no Mathlib import.

`FormalSpectrum.awayCompletionEquivPowerSeriesAway` lives there too, is already stated at every
commutative ring, and is reused below unchanged.

**This module was a leaf when it was written and is one no longer.** What made it stop being one is
that `FormalSpectrum.HasBoundedDenominatorsAt` and the criterion at an arbitrary point below are
what a general everywhere-failure has to be stated in, so the Dedekind module imports this one
rather than the other way about; nothing here was moved and nothing here changed to make that
possible.

**One instance was moved down to make room for this file and has now come back up into it.**
`FormalSpectrum.isPrime_span_singleton_two` — `(2)` is prime in `ℤ` — was declared in
`FormalSchemes.StructureSheafStalkPowerSeriesLocal`, which **was** a sibling leaf when this file
was written: neither could reach the other, so the closed point below would have needed a second
copy of it and the instance went down to
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, which both of them reach. That is no
longer symmetric. `FormalSchemes.StructureSheafStalkPowerSeriesLocal` now reaches this module
through `FormalSchemes.StructureSheafStalkPowerSeriesDedekind` and is one of the three modules the
count at the head of this section names; this module still cannot reach it, now because that edge
would be a cycle rather than because the two are unrelated. **So a consumer can host it, and this
file is the one that can**: the instance is declared here, once, and the local module picks it up
through the Dedekind one. `Int.span_two_isMaximal` (`FormalSchemes.TwoAdicDegeneracy`) is the same
fact about maximality and does **not** move with it: it is in neither module's closure, it has a
consumer where it is, and the one use of maximality below is a term rather than a named theorem.

**A new module is not free here and the alternative was measured.** Appending to
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` would cost the rebuild of its reverse
closure and would put an arbitrary-point theory inside a file whose subject is one point; appending
to `FormalSchemes.StructureSheafStalkPowerSeriesLocal`, the leaf whose subject is closest, would
cost nothing at all in figures, because a leaf added to a leaf moves no closure. What a new module
costs instead is prose: the module count and every reverse closure through
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` move by one, which is thirty-seven
figures in twenty-three files, all of them numerals — measured by adding a scratch leaf over that
module in a throwaway worktree and re-running the tree audit, so a later reader can re-derive it
instead of trusting the words. At the tree this file was added to the same construction gave
thirty-six figures in twenty-two files, and those twenty-two are exactly the files whose prose the
commit that added this one had to touch. That cost is paid in the same commit and is the reason the
diff is wider than the mathematics.

## Main results

* `FormalSpectrum.powerSeriesXPoint`: **the point of `Spf (R⟦X⟧, (X))` over a prime of `R`**, with
  its prime (`FormalSpectrum.pointPrime_powerSeriesXPoint`), the basic opens through it
  (`FormalSpectrum.mem_basicOpen_powerSeriesXPoint_iff`: the constant terms outside the prime),
  the fact that every point is one of these (`FormalSpectrum.eq_powerSeriesXPoint`), and when it
  is closed (`FormalSpectrum.isClosed_singleton_powerSeriesXPoint_iff`: exactly at a maximal
  ideal).
* `FormalSpectrum.atPrimeCompletionEquivLocalizationPowerSeries`: **the target of the stalk
  comparison at that point is `(R_p)⟦X⟧`**, at every commutative ring and every point — the second
  ring identification with both of its restrictions removed.
* `FormalSpectrum.atPrimeCompletionEquivLocalization_awayToAtPrimeCompletion`: **the two
  identifications are compatible with the comparison map**, which through them is
  `PowerSeries.map` of `FormalSpectrum.awayToLocalizationAtPrime`.
* `FormalSpectrum.HasBoundedDenominatorsAt` and
  `FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXPoint_iff`: **the surjectivity
  half at that point is exactly that condition**, at every commutative ring.
* `FormalSpectrum.exists_awayCompletionRestrict_eq_zero_powerSeriesXPoint`: **the injectivity half
  holds at every point of every domain** — more than the half asks, since the section is already
  `0`.
* `FormalSpectrum.isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt`: **the predicate at
  every point of every domain**, with neither a completion nor a power series left on the right.
* `FormalSpectrum.hasBoundedDenominatorsAt_bot_iff`: **the condition at `⊥` is the denominator
  condition**, at every domain — the identification of the two models that makes the criterion
  above subsume
  `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators` and carries
  its classification onto the predicate at `⊥`.
* `FormalSpectrum.hasBoundedDenominatorsAt_maximalIdeal`: **the condition holds at the maximal
  ideal of every local ring**, with no domain hypothesis — the predicate's first value that is not
  a negation at a single ring.
* `FormalSpectrum.not_isStalkLimit_powerSeriesX_int`: **the predicate fails at every point of
  `Spf (ℤ⟦X⟧, (X))`**, the first formal spectrum here on which it is identically false. It goes
  through `FormalSpectrum.not_hasBoundedDenominatorsAt_int`, whose nonzero-prime branch is
  `FormalSpectrum.not_hasBoundedDenominatorsAt_intSpan` and whose branch at `⊥` is the existing
  refutation read through `FormalSpectrum.hasBoundedDenominatorsAt_bot_iff`.
* `FormalSpectrum.isClosed_and_not_isStalkLimit_powerSeriesXPoint_intTwo`: **a closed point at
  which the predicate fails**, at `(X) ⊆ ℤ⟦X⟧` over `(2)` — the illustration of the theorem
  above, its failure half now a corollary and only its closedness half about `(2)`.
* `FormalSpectrum.dvd_pow_of_mem_range_algebraMap`: **the descent from the local ring back to the
  ring** — clearing `1 / s` by `m ^ k` says `s ∣ m ^ k` in `R` — the single step both refutations
  of the condition take, and one of the places a proof here spends `[IsDomain R]`; they are
  enumerated on `FormalSpectrum.injective_awayToLocalizationAtPrime`.
* `FormalSpectrum.hasBoundedDenominatorsAt_iff_finite_primes`: **the condition at a unique
  factorisation domain is a cardinality at every prime**, namely the number of primes up to
  associates lying outside that prime — the analogue at a general prime of
  `FormalSpectrum.hasBoundedDenominators_iff_finite_primes`, with the sufficient half
  (`FormalSpectrum.hasBoundedDenominatorsAt_of_forall_dvd_pow`) carrying no hypothesis on `R` at
  all.
* `FormalSpectrum.hasBoundedDenominatorsAt_of_le` and
  `FormalSpectrum.hasBoundedDenominatorsAt_of_hasBoundedDenominators`: **the condition is monotone
  in the prime** at such a ring, and **the denominator condition implies it at every prime**. The
  converse of each is false, at a ring this file cannot reach.
* `FormalSpectrum.isStalkLimit_powerSeriesXPoint_iff_finite_primes`: **the predicate at every
  point of `Spf (R⟦X⟧, (X))` over a unique factorisation domain, in both directions** — the first
  statement here that decides a whole space and can come out either way.
-/

noncomputable section

universe u

namespace FormalSpectrum

open PowerSeries

/-! ### The point over an arbitrary prime -/

section Point

variable (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]

/-- **The point of `Spf (R⟦X⟧, (X))` over a prime `p` of `R`.** The space is `Spec R` by
`FormalSpectrum.powerSeriesXHomeo`, so a prime of `R` names a point of it and every point is so
named (`FormalSpectrum.eq_powerSeriesXPoint`).

`FormalSpectrum.powerSeriesXGenericPoint` and `FormalSpectrum.powerSeriesXClosedPoint` are the
values of this at `⊥` and at the maximal ideal of a local ring, and they are equal to them by
`rfl`; this definition generalises no theorem about either, it only lets the two be stated in one
family. -/
def powerSeriesXPoint : FormalSpectrum (powerSeriesXIdeal R) :=
  (powerSeriesXHomeo R).symm ⟨p, inferInstance⟩

/-- `FormalSpectrum.powerSeriesXPoint` sits over `p` under `FormalSpectrum.powerSeriesXHomeo`, by
construction. -/
theorem powerSeriesXHomeo_powerSeriesXPoint :
    powerSeriesXHomeo R (powerSeriesXPoint R p) = ⟨p, inferInstance⟩ :=
  (powerSeriesXHomeo R).apply_symm_apply _

/-- **The prime of `R⟦X⟧` under the point over `p` is the `PowerSeries.constantCoeff` preimage of
`p`.** This is `FormalSpectrum.pointPrime_powerSeriesX`, which is already stated at an arbitrary
point, read at this one. -/
theorem pointPrime_powerSeriesXPoint :
    pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p) =
      Ideal.comap (constantCoeff (R := R)) p := by
  rw [pointPrime_powerSeriesX, powerSeriesXHomeo_powerSeriesXPoint]

/-- Being outside the prime under the point over `p` is having a constant term outside `p` — the
complement form of `FormalSpectrum.mem_basicOpen_powerSeriesXPoint_iff`, used to feed the prime
complement into `IsLocalization.lift`. -/
theorem notMem_pointPrime_powerSeriesXPoint_iff (g : PowerSeries R) :
    g ∉ pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p) ↔ constantCoeff g ∉ p := by
  rw [pointPrime_powerSeriesXPoint, Ideal.mem_comap]

/-- **The basic opens through the point over `p` are the constant terms outside `p`.** So the
quantifier `∀ f, x ∈ D(f) → …` in both halves of `FormalSpectrum.isStalkLimit_powerSeriesX_iff`
ranges over the basic opens of `Spec R` through `p` and over nothing else. -/
theorem mem_basicOpen_powerSeriesXPoint_iff (g : PowerSeries R) :
    powerSeriesXPoint R p ∈ basicOpen (powerSeriesXIdeal R) g ↔ constantCoeff g ∉ p := by
  rw [mem_basicOpen_powerSeriesX_iff, notMem_pointPrime_powerSeriesXPoint_iff]
  simp

/-- **Every point of `Spf (R⟦X⟧, (X))` is the point over a prime of `R`**, namely over the prime it
maps to under `FormalSpectrum.powerSeriesXHomeo`. So the statements below leave no point out. -/
theorem eq_powerSeriesXPoint (x : FormalSpectrum (powerSeriesXIdeal R)) :
    x = powerSeriesXPoint R (powerSeriesXHomeo R x).asIdeal :=
  ((powerSeriesXHomeo R).symm_apply_apply x).symm

/-- **The point over `p` is closed exactly when `p` is maximal.** Transported along
`FormalSpectrum.powerSeriesXHomeo` the singleton is `{p} ⊆ Spec R`, and
`PrimeSpectrum.isClosed_singleton_iff_isMaximal` is the statement there.

`FormalSpectrum.not_isClosed_powerSeriesXGenericPoint` is the `p = ⊥` half of this at a domain
that is not a field; it is not reproved here and does not follow from this without
`Ring.isField_iff_maximal_bot`. -/
theorem isClosed_singleton_powerSeriesXPoint_iff :
    IsClosed ({powerSeriesXPoint R p} : Set (FormalSpectrum (powerSeriesXIdeal R))) ↔
      p.IsMaximal := by
  have h := (powerSeriesXHomeo R).isClosed_image (s := {powerSeriesXPoint R p})
  rw [Set.image_singleton, powerSeriesXHomeo_powerSeriesXPoint] at h
  rw [← h, PrimeSpectrum.isClosed_singleton_iff_isMaximal]

end Point

/-- **The generic point is the point over `⊥`.** Both sides are
`FormalSpectrum.powerSeriesXHomeo`'s inverse at the same prime spectrum point, and the two
`Ideal.IsPrime` proofs are propositions, so this is `rfl`. -/
theorem powerSeriesXPoint_bot (R : Type u) [CommRing R] [IsDomain R] :
    powerSeriesXPoint R ⊥ = powerSeriesXGenericPoint R := rfl

/-- **The closed point of a local ring is the point over its maximal ideal.** `rfl`, for the same
reason as `FormalSpectrum.powerSeriesXPoint_bot`.

Together the two say that this file introduces no new point: it names the family both existing
points already belong to. -/
theorem powerSeriesXPoint_maximalIdeal (R : Type u) [CommRing R] [IsLocalRing R] :
    powerSeriesXPoint R (IsLocalRing.maximalIdeal R) = powerSeriesXClosedPoint R := rfl

/-! ### The target at that point is `(R_p)⟦X⟧` -/

section Target

variable (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]

/-- **A power series whose constant term is outside `p` becomes a unit of `(R_p)⟦X⟧`.** Its
constant term lands in the prime complement, hence in the units of the localization, and a power
series is a unit exactly when its constant term is
(`PowerSeries.isUnit_iff_constantCoeff`).

This is the analogue of `FormalSpectrum.isUnit_map_fractionRing`, and it is where the domain
hypothesis of that lemma disappears: there the constant term had to be seen to stay nonzero in the
fraction field, and here it is inverted by the very submonoid it lies in. -/
theorem isUnit_map_localizationAtPrime (g : PowerSeries R) (hg : constantCoeff g ∉ p) :
    IsUnit (PowerSeries.map (algebraMap R (Localization.AtPrime p)) g) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_map]
  exact IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p) ⟨_, hg⟩

/-- **The comparison `R⟦X⟧_P →+* (R_p)⟦X⟧`**, `P` the prime under the point over `p`, from the
universal property of the localization at the prime complement.
`FormalSpectrum.pointPrime_powerSeriesXPoint` says `P` is the `PowerSeries.constantCoeff` preimage
of `p`, so the source is exactly the ring whose completion is the target of the stalk comparison
there. -/
def atPrimeToLocalizationPowerSeries :
    Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p)) →+*
      PowerSeries (Localization.AtPrime p) :=
  IsLocalization.lift
    (M := (pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p)).primeCompl)
    (g := PowerSeries.map (algebraMap R (Localization.AtPrime p)))
    (fun y => isUnit_map_localizationAtPrime R p y.1
      ((notMem_pointPrime_powerSeriesXPoint_iff R p y.1).mp y.2))

/-- `FormalSpectrum.atPrimeToLocalizationPowerSeries` is a map under `R⟦X⟧`. -/
theorem atPrimeToLocalizationPowerSeries_algebraMap (g : PowerSeries R) :
    atPrimeToLocalizationPowerSeries R p (algebraMap (PowerSeries R) _ g) =
      PowerSeries.map (algebraMap R (Localization.AtPrime p)) g :=
  IsLocalization.lift_eq _ g

/-- `FormalSpectrum.atPrimeToLocalizationPowerSeries` carries the ideal of definition onto
`(X) ⊆ (R_p)⟦X⟧`; an equality, both sides being the span of the image of `X`. -/
theorem map_pointIdeal_atPrimeToLocalizationPowerSeries :
    (pointIdeal (powerSeriesXIdeal R) (powerSeriesXPoint R p)).map
        (atPrimeToLocalizationPowerSeries R p) =
      powerSeriesXIdeal (Localization.AtPrime p) := by
  rw [pointIdeal, Ideal.map_map, Ideal.map_span, Set.image_singleton]
  congr 1
  rw [RingHom.comp_apply, atPrimeToLocalizationPowerSeries_algebraMap, PowerSeries.map_X]

/-- **Finitely many coefficients that die in the local ring at `p` are killed by a single element
outside `p`.** The prime complement is a submonoid, so the product of the `n` witnesses supplied by
`IsLocalization.map_eq_zero_iff` is again outside `p`.

This is the step that replaces the domain hypothesis of
`FormalSpectrum.mem_pointIdeal_pow_of_map_mem`, whose argument pushes a vanishing coefficient back
along an injection that a general localization does not have. It is `private` because it is the
induction inside the next theorem and has no other consumer; the statement is about a power series
only through `PowerSeries.coeff`, so a caller wanting it for a general finite family would want a
different statement rather than this one. -/
private theorem exists_mem_primeCompl_mul_coeff_eq_zero (n : ℕ) (a : PowerSeries R)
    (h : ∀ i < n, algebraMap R (Localization.AtPrime p) (PowerSeries.coeff i a) = 0) :
    ∃ t ∈ p.primeCompl, ∀ i < n, t * PowerSeries.coeff i a = 0 := by
  induction n with
  | zero => exact ⟨1, p.primeCompl.one_mem, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
      obtain ⟨t, ht, htall⟩ := ih fun i hi => h i (by omega)
      obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) _).mp
        (h n (by omega))
      refine ⟨t * (u : R), mul_mem ht u.2, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · calc t * (u : R) * PowerSeries.coeff i a
            = (u : R) * (t * PowerSeries.coeff i a) := by ring
          _ = 0 := by rw [htall i hlt, mul_zero]
      · calc t * (u : R) * PowerSeries.coeff i a
            = t * ((u : R) * PowerSeries.coeff i a) := by ring
          _ = 0 := by rw [hu, mul_zero]

/-- The powers of the ideal of definition of the stalk's local ring are the principal ideals
generated by the powers of `X`. -/
theorem pointIdeal_powerSeriesXPoint_pow_eq_span (n : ℕ) :
    pointIdeal (powerSeriesXIdeal R) (powerSeriesXPoint R p) ^ n =
      Ideal.span {algebraMap (PowerSeries R)
        (Localization.AtPrime (pointPrime (powerSeriesXIdeal R)
          (powerSeriesXPoint R p))) ((X : PowerSeries R) ^ n)} := by
  rw [pointIdeal, Ideal.map_span, Set.image_singleton, map_pow, Ideal.span_singleton_pow]

/-- **`R⟦X⟧_P → (R_p)⟦X⟧ ⧸ (X) ^ n` is injective.** Writing the element as `a / y` with `y` outside
`P`, the hypothesis says the first `n` coefficients of `a` die in `Localization.AtPrime p`; a
single `t` outside `p` kills all of them at once, so `X ^ n` divides the constant multiple
`C t * a` in `R⟦X⟧`, and `C t * y` is again outside `P`, which is what turns that back into a
statement about `a / y`.

No injectivity of any structural map is used, which is why this holds at every commutative ring
and `FormalSpectrum.mem_pointIdeal_pow_of_map_mem`, the same statement at the generic point, is
stated at a domain. -/
theorem mem_pointIdeal_pow_of_map_mem_powerSeriesXPoint (n : ℕ)
    (s : Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p)))
    (hs : atPrimeToLocalizationPowerSeries R p s ∈
      powerSeriesXIdeal (Localization.AtPrime p) ^ n) :
    s ∈ pointIdeal (powerSeriesXIdeal R) (powerSeriesXPoint R p) ^ n := by
  obtain ⟨⟨a, y⟩, hy⟩ := IsLocalization.mk'_surjective
    (pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p)).primeCompl s
  have hspec : algebraMap (PowerSeries R) _ y.1 * s = algebraMap (PowerSeries R) _ a := by
    rw [← hy]; exact IsLocalization.mk'_spec' _ a y
  have h1 : PowerSeries.map (algebraMap R (Localization.AtPrime p)) a ∈
      powerSeriesXIdeal (Localization.AtPrime p) ^ n := by
    rw [← atPrimeToLocalizationPowerSeries_algebraMap, ← hspec, map_mul]
    exact Ideal.mul_mem_left _ _ hs
  rw [show (powerSeriesXIdeal (Localization.AtPrime p) ^ n) =
      Ideal.span {(X : PowerSeries (Localization.AtPrime p)) ^ n} from
      Ideal.span_singleton_pow _ _,
    Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at h1
  have h1' : ∀ i < n, algebraMap R (Localization.AtPrime p) (PowerSeries.coeff i a) = 0 := by
    intro i hi
    have hc := h1 i hi
    rwa [PowerSeries.coeff_map] at hc
  obtain ⟨t, ht, htall⟩ := exists_mem_primeCompl_mul_coeff_eq_zero R p n a h1'
  obtain ⟨b, hb⟩ : (X : PowerSeries R) ^ n ∣ PowerSeries.C t * a := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [PowerSeries.coeff_C_mul]
    exact htall m hm
  have hCt : PowerSeries.C t ∉ pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p) :=
    (notMem_pointPrime_powerSeriesXPoint_iff R p _).mpr (by simpa using ht)
  obtain ⟨u, hu⟩ := IsLocalization.map_units
    (Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p)))
    (⟨PowerSeries.C t * y.1, mul_mem hCt y.2⟩ :
      (pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p)).primeCompl)
  have hspec2 : algebraMap (PowerSeries R) _ (PowerSeries.C t * y.1) * s =
      algebraMap (PowerSeries R) _ (PowerSeries.C t * a) := by
    rw [map_mul, map_mul, mul_assoc, hspec]
  have hs' : s = ↑u⁻¹ * algebraMap (PowerSeries R) _ (PowerSeries.C t * a) := by
    rw [← hspec2, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hs', pointIdeal_powerSeriesXPoint_pow_eq_span]
  refine Ideal.mul_mem_left _ _ ?_
  rw [hb, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- **`R⟦X⟧_P → (R_p)⟦X⟧ ⧸ (X) ^ n` is surjective**, by the induction the generic-point case uses
and with the same shape: the error is `X ^ n * u`, the constant term of `u` is `r / d` with `d`
outside `p`, and `PowerSeries.C d` is then outside `P`, hence already invertible in the source. -/
theorem exists_sub_atPrimeToLocalizationPowerSeries_mem (n : ℕ)
    (w : PowerSeries (Localization.AtPrime p)) :
    ∃ s : Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p)),
      w - atPrimeToLocalizationPowerSeries R p s ∈
        powerSeriesXIdeal (Localization.AtPrime p) ^ n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    rw [show (powerSeriesXIdeal (Localization.AtPrime p) ^ n) =
        Ideal.span {(X : PowerSeries (Localization.AtPrime p)) ^ n} from
        Ideal.span_singleton_pow _ _,
      Ideal.mem_span_singleton] at hs
    obtain ⟨u, hu⟩ := hs
    obtain ⟨⟨r, d⟩, hrd⟩ := IsLocalization.mk'_surjective p.primeCompl
      (constantCoeff (R := Localization.AtPrime p) u)
    have hy : (PowerSeries.C (d : R)) ∈
        (pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p)).primeCompl :=
      (notMem_pointPrime_powerSeriesXPoint_iff R p _).mpr
        (by rw [PowerSeries.constantCoeff_C]; exact d.2)
    refine ⟨s + IsLocalization.mk' _ (PowerSeries.C r * (X : PowerSeries R) ^ n)
      ⟨PowerSeries.C (d : R), hy⟩, ?_⟩
    have hkey : atPrimeToLocalizationPowerSeries R p (IsLocalization.mk' _
        (PowerSeries.C r * (X : PowerSeries R) ^ n) ⟨PowerSeries.C (d : R), hy⟩) =
        (X : PowerSeries (Localization.AtPrime p)) ^ n *
          PowerSeries.C (constantCoeff (R := Localization.AtPrime p) u) := by
      have hb : (algebraMap R (Localization.AtPrime p)) (d : R) *
          constantCoeff (R := Localization.AtPrime p) u =
            algebraMap R (Localization.AtPrime p) r := by
        rw [← hrd]; exact IsLocalization.mk'_spec' _ r d
      rw [atPrimeToLocalizationPowerSeries, IsLocalization.lift_mk'_spec, map_mul, map_pow,
        PowerSeries.map_C, PowerSeries.map_X]
      change PowerSeries.C (algebraMap R (Localization.AtPrime p) r) *
          (X : PowerSeries (Localization.AtPrime p)) ^ n
        = PowerSeries.map (algebraMap R (Localization.AtPrime p)) (PowerSeries.C (d : R)) *
          ((X : PowerSeries (Localization.AtPrime p)) ^ n *
            PowerSeries.C (constantCoeff (R := Localization.AtPrime p) u))
      rw [PowerSeries.map_C, ← hb, map_mul]
      ring
    rw [map_add, hkey]
    rw [show (powerSeriesXIdeal (Localization.AtPrime p) ^ (n + 1)) =
        Ideal.span {(X : PowerSeries (Localization.AtPrime p)) ^ (n + 1)} from
        Ideal.span_singleton_pow _ _, Ideal.mem_span_singleton]
    obtain ⟨v, hv⟩ : (X : PowerSeries (Localization.AtPrime p)) ∣
        (u - PowerSeries.C (constantCoeff (R := Localization.AtPrime p) u)) := by
      rw [PowerSeries.X_dvd_iff]
      simp
    refine ⟨v, ?_⟩
    have hrw : w - (atPrimeToLocalizationPowerSeries R p s +
        (X : PowerSeries (Localization.AtPrime p)) ^ n *
          PowerSeries.C (constantCoeff (R := Localization.AtPrime p) u)) =
        (X : PowerSeries (Localization.AtPrime p)) ^ n *
          (u - PowerSeries.C (constantCoeff (R := Localization.AtPrime p) u)) := by
      rw [mul_sub, ← hu]; ring
    rw [hrw, hv]; ring

/-- The completion of `FormalSpectrum.atPrimeToLocalizationPowerSeries` is bijective, by the
levelwise criterion `AdicCompletion.bijective_mapCompletion_of_bijective_quotientMap` at the two
previous theorems. -/
theorem bijective_mapCompletion_atPrimeToLocalizationPowerSeries :
    Function.Bijective (AdicCompletion.mapCompletion (atPrimeToLocalizationPowerSeries R p)
      (map_pointIdeal_atPrimeToLocalizationPowerSeries R p).le (fg_powerSeriesXIdeal _)) := by
  refine AdicCompletion.bijective_mapCompletion_of_bijective_quotientMap _ _
    ((fg_powerSeriesXIdeal R).map _) (fg_powerSeriesXIdeal _) fun n hc => ?_
  refine AdicCompletion.bijective_quotientMap_of _ hc ?_ ?_
  · intro w
    obtain ⟨s, hs⟩ := exists_sub_atPrimeToLocalizationPowerSeries_mem R p n w
    exact ⟨s, hs⟩
  · exact fun s hs => mem_pointIdeal_pow_of_map_mem_powerSeriesXPoint R p n s hs

/-- **The target of the stalk comparison at the point over `p` is `(R_p)⟦X⟧`**, at every
commutative ring and every point.

This is `FormalSpectrum.atPrimeCompletionEquivFractionPowerSeries` with both of its restrictions
removed: that one is stated at the generic point of a domain, and the domain enters its proof at
one step only, which
`FormalSpectrum.mem_pointIdeal_pow_of_map_mem_powerSeriesXPoint` replaces by a common-denominator
argument inside the prime complement. Neither theorem is derived from the other and the earlier
one is not reproved; the two targets are `FractionRing R` and `Localization.AtPrime` at `⊥`.
Those two *coefficient* rings are identified further down, by
`FormalSpectrum.localizationAtPrimeBotEquiv`, but that identification is never transported through
`PowerSeries.map`, so the two completions above are still not compared and the first sentence
stands. -/
def atPrimeCompletionEquivLocalizationPowerSeries :
    AdicCompletion (pointIdeal (powerSeriesXIdeal R) (powerSeriesXPoint R p))
        (Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p)))
      ≃+* PowerSeries (Localization.AtPrime p) :=
  (RingEquiv.ofBijective _ (bijective_mapCompletion_atPrimeToLocalizationPowerSeries R p)).trans
    (RingEquiv.ofBijective _
      (AdicCompletion.bijective_algebraMap_of_isAdicComplete
        (powerSeriesXIdeal (Localization.AtPrime p)))).symm

/-- `FormalSpectrum.atPrimeCompletionEquivLocalizationPowerSeries` as an equation between ring maps
into the completion of `(R_p)⟦X⟧`, which is the form the compatibility square below consumes. -/
theorem algebraMap_atPrimeCompletionEquivLocalizationPowerSeries
    (b : AdicCompletion (pointIdeal (powerSeriesXIdeal R) (powerSeriesXPoint R p))
      (Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p)))) :
    algebraMap (PowerSeries (Localization.AtPrime p))
        (AdicCompletion (powerSeriesXIdeal (Localization.AtPrime p))
          (PowerSeries (Localization.AtPrime p)))
        (atPrimeCompletionEquivLocalizationPowerSeries R p b) =
      AdicCompletion.mapCompletion (atPrimeToLocalizationPowerSeries R p)
        (map_pointIdeal_atPrimeToLocalizationPowerSeries R p).le (fg_powerSeriesXIdeal _) b :=
  (RingEquiv.ofBijective _ (AdicCompletion.bijective_algebraMap_of_isAdicComplete
    (powerSeriesXIdeal (Localization.AtPrime p)))).apply_symm_apply _

end Target

/-! ### The comparison map through the two identifications -/

section Comparison

variable (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]

/-- **The map `R[1/m] →+* R_p` for `m` outside `p`**: everything inverted on the left is already
invertible on the right, because `m` lies in the prime complement.

This is `FormalSpectrum.awayToFractionRing` at a general prime, and again with no domain
hypothesis: there the powers of `m` had to be seen to be nonzero, and here they are units of the
localization outright. -/
def awayToLocalizationAtPrime (m : R) (hm : m ∉ p) :
    Localization.Away m →+* Localization.AtPrime p :=
  IsLocalization.lift (M := Submonoid.powers m) (g := algebraMap R (Localization.AtPrime p))
    (fun y => by
      obtain ⟨k, hk⟩ := y.2
      rw [← hk, map_pow]
      exact (IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p) ⟨m, hm⟩).pow k)

/-- `FormalSpectrum.awayToLocalizationAtPrime` is a map under `R`. -/
theorem awayToLocalizationAtPrime_algebraMap (m : R) (hm : m ∉ p) (r : R) :
    awayToLocalizationAtPrime R p m hm (algebraMap R (Localization.Away m) r) =
      algebraMap R (Localization.AtPrime p) r :=
  IsLocalization.lift_eq _ r

/-- **The square, before completing.** The localization map `R⟦X⟧[1/f] → R⟦X⟧_P` followed by the
identification of the target with `(R_p)⟦X⟧` is `PowerSeries.map` of `R[1/m] → R_p` followed by the
identification of the source with `R[1/m]⟦X⟧`.

Both sides are ring maps out of a localization of `R⟦X⟧`, so `IsLocalization.ringHom_ext` reduces
this to their values on `R⟦X⟧`, where both are `PowerSeries.map` of the structural map into the
local ring. No continuity and no completeness is used. -/
theorem atPrimeToLocalizationPowerSeries_comp_awayToAtPrime (f : PowerSeries R)
    (hf : powerSeriesXPoint R p ∈ basicOpen (powerSeriesXIdeal R) f)
    (hm : constantCoeff f ∉ p) :
    (atPrimeToLocalizationPowerSeries R p).comp
        (awayToAtPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p) hf) =
      (PowerSeries.map (awayToLocalizationAtPrime R p (constantCoeff f) hm)).comp
        (awayToPowerSeriesAway f) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun g => ?_)
  have hcomp : (awayToLocalizationAtPrime R p (constantCoeff f) hm).comp
        (algebraMap R (Localization.Away (constantCoeff f))) =
      algebraMap R (Localization.AtPrime p) :=
    RingHom.ext fun r => awayToLocalizationAtPrime_algebraMap R p (constantCoeff f) hm r
  simp only [RingHom.coe_comp, Function.comp_apply, awayToAtPrime_algebraMap,
    atPrimeToLocalizationPowerSeries_algebraMap, awayToPowerSeriesAway_algebraMap]
  rw [show PowerSeries.map (awayToLocalizationAtPrime R p (constantCoeff f) hm)
        (PowerSeries.map (algebraMap R (Localization.Away (constantCoeff f))) g) =
      PowerSeries.map ((awayToLocalizationAtPrime R p (constantCoeff f) hm).comp
        (algebraMap R (Localization.Away (constantCoeff f)))) g from by
      rw [PowerSeries.map_comp]; rfl, hcomp]

/-- **The two identifications are compatible with the stalk comparison.** Under
`FormalSpectrum.awayCompletionEquivPowerSeriesAway` on the source and
`FormalSpectrum.atPrimeCompletionEquivLocalizationPowerSeries` on the target, the comparison map
`FormalSpectrum.awayToAtPrimeCompletion` at the point over `p` **is** `PowerSeries.map` of
`R[1/m] → R_p`, coefficient by coefficient.

This is the previous theorem pushed through `AdicCompletion.mapCompletion_comp` twice, with
`AdicCompletion.mapCompletion_algebraMap` recognising the two structural maps and one local step
rewriting the ring-level square inside the completion functor. That step is
`AdicCompletion.mapCompletion_congr` (`FormalSchemes.CompletionNestedBasicOpenMap`), which is
**not** imported here for the same reason it is not imported by
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`: the module is outside this file's
closure and the step is two lines. -/
theorem atPrimeCompletionEquivLocalization_awayToAtPrimeCompletion (f : PowerSeries R)
    (hf : powerSeriesXPoint R p ∈ basicOpen (powerSeriesXIdeal R) f)
    (hm : constantCoeff f ∉ p) (a : awayCompletion (powerSeriesXIdeal R) f) :
    atPrimeCompletionEquivLocalizationPowerSeries R p
        (awayToAtPrimeCompletion (powerSeriesXIdeal R) (powerSeriesXPoint R p)
          (fg_powerSeriesXIdeal R) hf a) =
      PowerSeries.map (awayToLocalizationAtPrime R p (constantCoeff f) hm)
        (awayCompletionEquivPowerSeriesAway f a) := by
  have hFG : (((powerSeriesXIdeal R).map
      (algebraMap (PowerSeries R) (Localization.Away f)))).FG := (fg_powerSeriesXIdeal R).map _
  -- `AdicCompletion.mapCompletion` depends on its ring map only through its value, and the two
  -- containment proofs are propositions.
  have hcongr : ∀ (φ₁ φ₂ : Localization.Away f →+* PowerSeries (Localization.AtPrime p))
      (h₁ : ((powerSeriesXIdeal R).map
        (algebraMap (PowerSeries R) (Localization.Away f))).map φ₁ ≤
          powerSeriesXIdeal (Localization.AtPrime p))
      (h₂ : ((powerSeriesXIdeal R).map
        (algebraMap (PowerSeries R) (Localization.Away f))).map φ₂ ≤
          powerSeriesXIdeal (Localization.AtPrime p))
      (hJ : (powerSeriesXIdeal (Localization.AtPrime p)).FG), φ₁ = φ₂ →
      AdicCompletion.mapCompletion φ₁ h₁ hJ = AdicCompletion.mapCompletion φ₂ h₂ hJ := by
    rintro φ₁ φ₂ h₁ h₂ hJ rfl
    rfl
  refine (AdicCompletion.bijective_algebraMap_of_isAdicComplete
    (powerSeriesXIdeal (Localization.AtPrime p))).1 ?_
  rw [algebraMap_atPrimeCompletionEquivLocalizationPowerSeries, awayToAtPrimeCompletion,
    ← RingHom.comp_apply, AdicCompletion.mapCompletion_comp _ _ _ _ _ _ hFG,
    hcongr _ _ _ _ _ (atPrimeToLocalizationPowerSeries_comp_awayToAtPrime R p f hf hm),
    ← AdicCompletion.mapCompletion_comp (awayToPowerSeriesAway f)
      (PowerSeries.map (awayToLocalizationAtPrime R p (constantCoeff f) hm))
      (map_awayToPowerSeriesAway f).le (map_powerSeriesXIdeal_map _).le
      (fg_powerSeriesXIdeal _) (fg_powerSeriesXIdeal _) hFG,
    RingHom.comp_apply, ← algebraMap_awayCompletionEquivPowerSeriesAway f a,
    AdicCompletion.mapCompletion_algebraMap]
  rw [← Ideal.map_map, map_awayToPowerSeriesAway]
  exact (map_powerSeriesXIdeal_map _).le

end Comparison

/-! ### The criterion at that point, and the condition the surjectivity half is -/

section Criterion

variable (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]

/-- **The criterion at the point over `p`, with the basic opens written out.**
`FormalSpectrum.isStalkLimit_powerSeriesX_iff` is already stated at an arbitrary point; all this
does is replace the two occurrences of `x ∈ D(f)` by the condition on constant terms that
`FormalSpectrum.mem_basicOpen_powerSeriesXPoint_iff` computes. -/
theorem isStalkLimit_powerSeriesXPoint_iff :
    IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXPoint R p) ↔
      (∀ (f : PowerSeries R) (hf : constantCoeff f ∉ p)
          (a : awayCompletion (powerSeriesXIdeal R) f),
          awayToAtPrimeCompletion (powerSeriesXIdeal R) (powerSeriesXPoint R p)
              (fg_powerSeriesXIdeal R)
              ((mem_basicOpen_powerSeriesXPoint_iff R p f).mpr hf) a = 0 →
            ∃ e, ∃ (_ : constantCoeff e ∉ p)
              (hle : basicOpen (powerSeriesXIdeal R) e ≤ basicOpen (powerSeriesXIdeal R) f),
              awayCompletionRestrict (powerSeriesXIdeal R) f e (fg_powerSeriesXIdeal R) hle a = 0) ∧
        ∀ b : AdicCompletion (pointIdeal (powerSeriesXIdeal R) (powerSeriesXPoint R p))
            (Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p))),
          ∃ f, ∃ (hf : constantCoeff f ∉ p),
            ∃ a, awayToAtPrimeCompletion (powerSeriesXIdeal R) (powerSeriesXPoint R p)
              (fg_powerSeriesXIdeal R)
              ((mem_basicOpen_powerSeriesXPoint_iff R p f).mpr hf) a = b := by
  rw [isStalkLimit_powerSeriesX_iff]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun f hf a ha => ?_, fun b => ?_⟩
    · obtain ⟨e, he, hle, hres⟩ := hinj f _ a ha
      exact ⟨e, (mem_basicOpen_powerSeriesXPoint_iff R p e).mp he, hle, hres⟩
    · obtain ⟨f, hf, a, ha⟩ := hsurj b
      exact ⟨f, (mem_basicOpen_powerSeriesXPoint_iff R p f).mp hf, a, ha⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun f hf a ha => ?_, fun b => ?_⟩
    · obtain ⟨e, he, hle, hres⟩ :=
        hinj f ((mem_basicOpen_powerSeriesXPoint_iff R p f).mp hf) a ha
      exact ⟨e, (mem_basicOpen_powerSeriesXPoint_iff R p e).mpr he, hle, hres⟩
    · obtain ⟨f, hf, a, ha⟩ := hsurj b
      exact ⟨f, (mem_basicOpen_powerSeriesXPoint_iff R p f).mpr hf, a, ha⟩

/-- **The denominator condition at a prime.** Every `ℕ`-indexed family in `Localization.AtPrime p`
has a single denominator up to powers, and the denominator is itself outside `p`.

The definition is `FormalSpectrum.HasBoundedDenominators`'s with `m ≠ 0` replaced by `m ∉ p` and
the fraction field replaced by the local ring, and it is stated in the same of the two equivalent
forms — denominators rather than localizations, the other being
`FormalSpectrum.hasBoundedDenominatorsAt_iff_range`.

**What is proved about it, all of it below.**
`FormalSpectrum.hasBoundedDenominatorsAt_bot_iff` identifies it at `⊥` with
`FormalSpectrum.HasBoundedDenominators`; `FormalSpectrum.hasBoundedDenominatorsAt_of_surjective`
is a sufficient criterion, and `FormalSpectrum.hasBoundedDenominatorsAt_maximalIdeal` the one
general value it yields; `FormalSpectrum.not_hasBoundedDenominatorsAt_int` refutes it at every
prime of `ℤ`. What it is *for* is that the surjectivity half of the criterion at the point
over `p` is literally it
(`FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXPoint_iff`). -/
def HasBoundedDenominatorsAt (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] : Prop :=
  ∀ x : ℕ → Localization.AtPrime p, ∃ m : R, m ∉ p ∧ ∀ n, ∃ k : ℕ,
    algebraMap R (Localization.AtPrime p) (m ^ k) * x n ∈
      Set.range (algebraMap R (Localization.AtPrime p))

/-- **What `FormalSpectrum.awayToLocalizationAtPrime` hits.** An element of
`Localization.AtPrime p` is the image of something in `R[1/m]` exactly when a power of `m` clears it
into `R`.

`FormalSpectrum.mem_range_awayToFractionRing_iff` is the same statement at the generic point of a
domain, and this proof is that one with the prime complement in place of the nonzero divisors. -/
theorem mem_range_awayToLocalizationAtPrime_iff (m : R) (hm : m ∉ p)
    (x : Localization.AtPrime p) :
    x ∈ Set.range (awayToLocalizationAtPrime R p m hm) ↔
      ∃ k : ℕ, algebraMap R (Localization.AtPrime p) (m ^ k) * x ∈
        Set.range (algebraMap R (Localization.AtPrime p)) := by
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
    have hmap := congrArg (awayToLocalizationAtPrime R p m hm) hspec
    rw [map_mul, awayToLocalizationAtPrime_algebraMap, awayToLocalizationAtPrime_algebraMap,
      hs] at hmap
    exact hmap.symm
  · rintro ⟨k, r, hr⟩
    refine ⟨IsLocalization.mk' (Localization.Away m) r
      (⟨m ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers m), ?_⟩
    rw [show awayToLocalizationAtPrime R p m hm = IsLocalization.lift
      (M := Submonoid.powers m) (g := algebraMap R (Localization.AtPrime p)) _ from rfl,
      IsLocalization.lift_mk'_spec]
    change algebraMap R (Localization.AtPrime p) r =
      algebraMap R (Localization.AtPrime p) (m ^ k) * x
    exact hr

/-- **The condition with the localization back in.** A family has a single denominator up to powers
exactly when it lies inside a single `R[1/m]` with `m` outside `p`.

`FormalSpectrum.mem_range_awayToLocalizationAtPrime_iff` at each member. This is the form the
surjectivity half produces and the definition is the form that mentions no localization; the two
are stated together so that neither has to be restated at a use site. -/
theorem hasBoundedDenominatorsAt_iff_range :
    HasBoundedDenominatorsAt R p ↔
      ∀ x : ℕ → Localization.AtPrime p, ∃ m : R, ∃ hm : m ∉ p,
        ∀ n, x n ∈ Set.range (awayToLocalizationAtPrime R p m hm) := by
  constructor
  · intro h x
    obtain ⟨m, hm, hall⟩ := h x
    exact ⟨m, hm, fun n => (mem_range_awayToLocalizationAtPrime_iff R p m hm _).mpr (hall n)⟩
  · intro h x
    obtain ⟨m, hm, hall⟩ := h x
    exact ⟨m, hm, fun n => (mem_range_awayToLocalizationAtPrime_iff R p m hm _).mp (hall n)⟩

/-- **The surjectivity half at the point over `p`, characterised**, at every commutative ring: it
holds exactly when every `ℕ`-indexed family in `Localization.AtPrime p` lies inside a single
`R[1/m]` with `m` outside `p`.

Read through `FormalSpectrum.awayCompletionEquivPowerSeriesAway` and
`FormalSpectrum.atPrimeCompletionEquivLocalizationPowerSeries`, tied together by
`FormalSpectrum.atPrimeCompletionEquivLocalization_awayToAtPrimeCompletion`, the comparison map is
`PowerSeries.map` of `FormalSpectrum.awayToLocalizationAtPrime`, and a power series over
`Localization.AtPrime p` is an `ℕ`-indexed family in it.
`PowerSeries.exists_map_eq_iff_forall_coeff_mem_range` turns *hit by `PowerSeries.map`* into a
condition on coefficients. Backwards the `f` is `PowerSeries.C m`,
whose constant term is `m` definitionally, so no transport is needed for the dependent type.

**The quantifier order is the content**, exactly as at the generic point: the `m` is uniform in the
family and the exponent is not. -/
theorem exists_awayToAtPrimeCompletion_eq_powerSeriesXPoint_iff :
    (∀ b : AdicCompletion (pointIdeal (powerSeriesXIdeal R) (powerSeriesXPoint R p))
        (Localization.AtPrime (pointPrime (powerSeriesXIdeal R) (powerSeriesXPoint R p))),
      ∃ f, ∃ (hf : constantCoeff f ∉ p),
        ∃ a, awayToAtPrimeCompletion (powerSeriesXIdeal R) (powerSeriesXPoint R p)
          (fg_powerSeriesXIdeal R)
          ((mem_basicOpen_powerSeriesXPoint_iff R p f).mpr hf) a = b) ↔
      HasBoundedDenominatorsAt R p := by
  rw [hasBoundedDenominatorsAt_iff_range]
  constructor
  · intro h x
    obtain ⟨f, hf, a, ha⟩ := h
      ((atPrimeCompletionEquivLocalizationPowerSeries R p).symm (PowerSeries.mk x))
    have key : PowerSeries.map (awayToLocalizationAtPrime R p (constantCoeff f) hf)
        (awayCompletionEquivPowerSeriesAway f a) = PowerSeries.mk x := by
      rw [← atPrimeCompletionEquivLocalization_awayToAtPrimeCompletion R p f
        ((mem_basicOpen_powerSeriesXPoint_iff R p f).mpr hf) hf a, ha,
        RingEquiv.apply_symm_apply]
    exact ⟨constantCoeff f, hf, fun n =>
      ⟨PowerSeries.coeff n (awayCompletionEquivPowerSeriesAway f a), by
        rw [← PowerSeries.coeff_map, key, PowerSeries.coeff_mk]⟩⟩
  · intro h b
    obtain ⟨m, hm, hall⟩ := h fun n =>
      PowerSeries.coeff n (atPrimeCompletionEquivLocalizationPowerSeries R p b)
    have hcc : constantCoeff (PowerSeries.C m) ∉ p := by
      rw [constantCoeff_C]
      exact hm
    obtain ⟨z, hz⟩ := (PowerSeries.exists_map_eq_iff_forall_coeff_mem_range
      (awayToLocalizationAtPrime R p m hm)
      (atPrimeCompletionEquivLocalizationPowerSeries R p b)).mpr hall
    refine ⟨PowerSeries.C m, hcc,
      (awayCompletionEquivPowerSeriesAway (PowerSeries.C m)).symm z, ?_⟩
    apply (atPrimeCompletionEquivLocalizationPowerSeries R p).injective
    rw [atPrimeCompletionEquivLocalization_awayToAtPrimeCompletion R p (PowerSeries.C m) _ hcc,
      RingEquiv.apply_symm_apply]
    exact hz

end Criterion

/-! ### The injectivity half at a domain, and the predicate -/

section Domain

variable (R : Type u) [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]

/-- **`FormalSpectrum.awayToLocalizationAtPrime` is injective** for `m` outside `p` in a domain:
`R[1/m]` really does sit inside `Localization.AtPrime p`, both being subrings of the fraction field.

`IsLocalization.injective_iff_map_algebraMap_eq` reduces injectivity of a ring map out of a
localization to a statement about the structural map alone, and there both sides say `x = y`: the
source because the powers of a nonzero element are nonzero divisors, the target because the prime
complement is (`Ideal.primeCompl_le_nonZeroDivisors`). **This is one of exactly three places a
proof in this file spends `[IsDomain R]`.** The second is
`FormalSpectrum.dvd_pow_of_mem_range_algebraMap`, which spends the very same fact to push an
equation in `Localization.AtPrime p` back down to `R`; the third is
`FormalSpectrum.isFractionRing_localizationAtPrimeBot`, which spends a different one,
`Ideal.primeCompl_bot`, and whose statement does not elaborate without the binder either. That is
why the main theorem below carries the instance while the surjectivity half does not. Every other
occurrence of the binder either consumes one of the three or is there only so that a statement
elaborates — `FormalSpectrum.powerSeriesXPoint_bot`, where
`FormalSpectrum.powerSeriesXGenericPoint` is defined only at a domain, and the
unique-factorisation section at the end of the file, where `[UniqueFactorizationMonoid R]` does
not elaborate without it. -/
theorem injective_awayToLocalizationAtPrime (m : R) (hm : m ∉ p) :
    Function.Injective (awayToLocalizationAtPrime R p m hm) := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ p.zero_mem)
  rw [IsLocalization.injective_iff_map_algebraMap_eq (M := Submonoid.powers m)]
  intro x y
  rw [awayToLocalizationAtPrime_algebraMap, awayToLocalizationAtPrime_algebraMap]
  refine ⟨fun h => congrArg _ (IsLocalization.injective (Localization.Away m)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hm0) h),
    fun h => congrArg _ (IsLocalization.injective (Localization.AtPrime p)
      (Ideal.primeCompl_le_nonZeroDivisors p) h)⟩

/-- **The comparison map at the point over `p` is injective**, at every domain and every `f` whose
constant term is outside `p`. This is more than the injectivity half asks for: the half is content
with a section that dies after restriction to a smaller basic open, and this says the section is
already `0`.

It is `FormalSpectrum.atPrimeCompletionEquivLocalization_awayToAtPrimeCompletion` read as a
statement about maps rather than about elements, through the two `RingEquiv`s and
`PowerSeries.map_injective`. -/
theorem injective_awayToAtPrimeCompletion_powerSeriesXPoint (f : PowerSeries R)
    (hf : powerSeriesXPoint R p ∈ basicOpen (powerSeriesXIdeal R) f)
    (hm : constantCoeff f ∉ p) :
    Function.Injective (awayToAtPrimeCompletion (powerSeriesXIdeal R)
      (powerSeriesXPoint R p) (fg_powerSeriesXIdeal R) hf) := by
  intro a b hab
  refine (awayCompletionEquivPowerSeriesAway f).injective
    (PowerSeries.map_injective _ (injective_awayToLocalizationAtPrime R p (constantCoeff f) hm) ?_)
  rw [← atPrimeCompletionEquivLocalization_awayToAtPrimeCompletion R p f hf hm a,
    ← atPrimeCompletionEquivLocalization_awayToAtPrimeCompletion R p f hf hm b, hab]

/-- **The injectivity half of `FormalSpectrum.isStalkLimit_powerSeriesXPoint_iff` holds**, at every
point of every domain.

The half asks for *some* smaller basic open on which the section already vanishes; the previous
theorem gives that the section is `0` outright, so `e = f` and `le_rfl` serve. All that is used of
`FormalSpectrum.awayCompletionRestrict` is that it is a ring homomorphism and therefore sends `0`
to `0`. -/
theorem exists_awayCompletionRestrict_eq_zero_powerSeriesXPoint (f : PowerSeries R)
    (hf : constantCoeff f ∉ p) (a : awayCompletion (powerSeriesXIdeal R) f)
    (ha : awayToAtPrimeCompletion (powerSeriesXIdeal R) (powerSeriesXPoint R p)
      (fg_powerSeriesXIdeal R) ((mem_basicOpen_powerSeriesXPoint_iff R p f).mpr hf) a = 0) :
    ∃ e, ∃ (_ : constantCoeff e ∉ p)
      (hle : basicOpen (powerSeriesXIdeal R) e ≤ basicOpen (powerSeriesXIdeal R) f),
      awayCompletionRestrict (powerSeriesXIdeal R) f e (fg_powerSeriesXIdeal R) hle a = 0 :=
  have ha0 : a = 0 :=
    injective_awayToAtPrimeCompletion_powerSeriesXPoint R p f _ hf (by rw [ha, map_zero])
  ⟨f, hf, le_rfl, by rw [ha0, map_zero]⟩

/-- **`FormalSpectrum.IsStalkLimit` at an arbitrary point of `Spf (R⟦X⟧, (X))` is exactly the
denominator condition at the prime under it**, at every domain — no factorisation, no countability,
no Noetherian hypothesis, and no restriction on the point — and with neither a completion nor a
power series left on the right-hand side.

The collapse is the same one the generic point enjoys and for the same reason:
`FormalSpectrum.isStalkLimit_powerSeriesXPoint_iff` is a plain conjunction whose injectivity half
holds at *every* point of every domain
(`FormalSpectrum.exists_awayCompletionRestrict_eq_zero_powerSeriesXPoint`), so nothing but the
surjectivity half is ever at stake and that half is
`FormalSpectrum.HasBoundedDenominatorsAt` on the nose.

**This does not restate or reprove
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`**, and *restate
or reprove* is the whole of what it does not do. By `FormalSpectrum.powerSeriesXPoint_bot` the two
are about the same point when `p = ⊥`, and their right-hand sides are conditions on two different
models of the same localization which `FormalSpectrum.hasBoundedDenominatorsAt_bot_iff` identifies.
Composing the two **does** derive the generic-point theorem from this one; that derivation ships
below as an `example` rather than as a theorem, so no second declaration of that statement exists
on the tree. -/
theorem isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt :
    IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXPoint R p) ↔
      HasBoundedDenominatorsAt R p :=
  (isStalkLimit_powerSeriesXPoint_iff R p).trans
    ⟨fun h => (exists_awayToAtPrimeCompletion_eq_powerSeriesXPoint_iff R p).mp h.2,
     fun h =>
      ⟨exists_awayCompletionRestrict_eq_zero_powerSeriesXPoint R p,
        (exists_awayToAtPrimeCompletion_eq_powerSeriesXPoint_iff R p).mpr h⟩⟩

end Domain

/-! ### Comparison with the condition at the generic point -/

section BotComparison

variable (R : Type u) [CommRing R] [IsDomain R]

/-- **The local ring at `⊥` is a fraction field.** `Ideal.primeCompl_bot` says that in a domain
the prime complement of `⊥` *is* the non-zero divisors, so a localization at `⊥` is a localization
at the non-zero divisors, and that is what `IsFractionRing` asks for.

**This is an instance and it is seen outside this file**, which is a change: three modules reach
this one, as the `## Placement` section above records, so the justification this paragraph used to
give — that nothing imports this file, and therefore nobody sees the instance — went stale when the
Dedekind module began importing it. What makes the instance safe is not scope but the head of its
statement: it is a candidate only for an `IsFractionRing` goal whose second argument unifies with
`Localization.AtPrime (⊥ : Ideal R)`, and none of the three localizes at `⊥` — the primes they
localize at are a fixed prime of `ℤ[X]` and a bound variable of the arbitrary-point criterion. The
`IsFractionRing` goals that *do* occur downstream are at `FractionRing R`, which does not unify
with it, and over the deepest of the three that goal still resolves to Mathlib's
`Localization.isLocalization` — so nothing standard is shadowed. **That pair of `#synth` goals is
the check to re-run**, not a count of what imports this file: the count is what one new import
falsifies, and it already has.

`FormalSpectrum.localizationAtPrimeBotEquiv` needs it as an instance rather than as a hypothesis,
because `IsLocalization.algEquiv` takes both localization facts by instance search. -/
instance isFractionRing_localizationAtPrimeBot :
    IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) := by
  rw [IsFractionRing, ← Ideal.primeCompl_bot (α := R)]
  infer_instance

/-- **The two models of that localization, identified.** Both `FractionRing R` and
`Localization.AtPrime (⊥ : Ideal R)` localize `R` at its non-zero divisors, so
`IsLocalization.algEquiv` gives the unique `R`-algebra isomorphism between them.

The `R`-algebra structure is what the transport below runs on, not the ring structure: it needs
the isomorphism to commute with the two structural maps out of `R` (`AlgEquiv.commutes`), and a
bare ring isomorphism of the two would not carry that. -/
def localizationAtPrimeBotEquiv :
    Localization.AtPrime (⊥ : Ideal R) ≃ₐ[R] FractionRing R :=
  IsLocalization.algEquiv (nonZeroDivisors R) _ _

/-- **The condition at `⊥` is the denominator condition.** At every domain,
`FormalSpectrum.HasBoundedDenominatorsAt` at the zero ideal and
`FormalSpectrum.HasBoundedDenominators` are the same condition.

The two differ in three places and all three are settled by
`FormalSpectrum.localizationAtPrimeBotEquiv`: a family indexed by one model transports to a family
indexed by the other, `m ∉ (⊥ : Ideal R)` is `m ≠ 0` by `Ideal.mem_bot`, and membership in the
range of a structural map transports because the isomorphism commutes with both of them. The
quantifiers are untouched, which is the point — the `m` stays uniform in the family and the
exponent stays local to each member.

**This is what the module header used to say was not done.** With
`FormalSpectrum.powerSeriesXPoint_bot`, which is `rfl`, it makes
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators` a corollary of
`FormalSpectrum.isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt`, and it carries the
whole classification of the denominator condition — at a unique factorisation domain, at a
Dedekind domain, over a countable fraction field, and the ultrapower's refutation of sufficiency —
onto the predicate at `⊥`. None of that is restated in code here; the `↔` is the transport. -/
theorem hasBoundedDenominatorsAt_bot_iff :
    HasBoundedDenominatorsAt R (⊥ : Ideal R) ↔ HasBoundedDenominators R := by
  set e := localizationAtPrimeBotEquiv R with he
  constructor
  · intro h x
    obtain ⟨m, hm, hall⟩ := h fun n => e.symm (x n)
    refine ⟨m, by simpa using hm, fun n => ?_⟩
    obtain ⟨k, r, hr⟩ := hall n
    refine ⟨k, r, ?_⟩
    have h2 := congrArg e hr
    rwa [map_mul, e.commutes, e.apply_symm_apply, e.commutes] at h2
  · intro h x
    obtain ⟨m, hm, hall⟩ := h fun n => e (x n)
    refine ⟨m, by simpa [Ideal.mem_bot] using hm, fun n => ?_⟩
    obtain ⟨k, r, hr⟩ := hall n
    refine ⟨k, r, ?_⟩
    have h2 := congrArg e.symm hr
    rwa [map_mul, e.symm.commutes, e.symm_apply_apply, e.symm.commutes] at h2

end BotComparison

/-! ### A point at which the condition holds -/

section Surjective

variable (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]

/-- **The condition holds wherever nothing has to be inverted.** If every element of
`Localization.AtPrime p` is already the image of an element of `R`, then `m = 1` and `k = 0` serve
for every family at once.

`1 ∉ p` is `Ideal.ne_top_iff_one` at a prime, and it is the only thing the *proof* needs primeness
for. The instance is doing something else as well, which is making the statement elaborate at all:
`Ideal.primeCompl`, `Localization.AtPrime` and `FormalSpectrum.HasBoundedDenominatorsAt` each take
it as an instance argument. -/
theorem hasBoundedDenominatorsAt_of_surjective
    (hsurj : Function.Surjective (algebraMap R (Localization.AtPrime p))) :
    HasBoundedDenominatorsAt R p :=
  fun x => ⟨1, (Ideal.ne_top_iff_one p).mp (‹p.IsPrime›).ne_top, fun n => ⟨0, by
    simpa using hsurj (x n)⟩⟩

end Surjective

section LocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- **A local ring is its own local ring at its maximal ideal.** Everything outside the maximal
ideal is a unit (`IsLocalRing.notMem_maximalIdeal`), so the prime complement lands in
`IsUnit.submonoid` and `IsLocalization.atUnits` makes the structural map an isomorphism; only its
surjectivity is wanted below. -/
theorem surjective_algebraMap_localizationAtPrime_maximalIdeal :
    Function.Surjective (algebraMap R (Localization.AtPrime (IsLocalRing.maximalIdeal R))) :=
  (IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl
    (fun _ hx => IsLocalRing.notMem_maximalIdeal.mp hx)).surjective

/-- **The condition holds at the maximal ideal of every local ring**, with no domain hypothesis
and no hypothesis on the ring at all beyond locality.

This is the only value of `FormalSpectrum.HasBoundedDenominatorsAt` on this tree that is not a
negation: `FormalSpectrum.not_hasBoundedDenominatorsAt_int` below refutes it at *every* prime of
`ℤ`, and everything the condition at the generic point is known to satisfy is a theorem about
`FormalSpectrum.HasBoundedDenominators`, which reaches the predicate only at `⊥` and only through
`FormalSpectrum.hasBoundedDenominatorsAt_bot_iff`. -/
theorem hasBoundedDenominatorsAt_maximalIdeal :
    HasBoundedDenominatorsAt R (IsLocalRing.maximalIdeal R) :=
  hasBoundedDenominatorsAt_of_surjective R _
    (surjective_algebraMap_localizationAtPrime_maximalIdeal R)

end LocalRing

/-! ### The two known points, as values of the criterion

The two `example`s below are **checks and not results**: each restates a theorem this tree already
has, and each is derived here from the criterion at an arbitrary point. They are what shows the
comparison above is the missing edge and not a restatement, and they are `example`s precisely so
that neither becomes a second declaration of a statement already proved elsewhere.
-/

/-- The generic point: the criterion at an arbitrary point, at `⊥`, composed with the comparison.
That `FormalSpectrum.powerSeriesXGenericPoint` may be written where the criterion says
`FormalSpectrum.powerSeriesXPoint` at `⊥` is `FormalSpectrum.powerSeriesXPoint_bot`, which is
`rfl`, so the elaborator needs no rewriting on the point and the whole derivation is the `↔`. -/
example (R : Type u) [CommRing R] [IsDomain R] :
    IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) ↔
      HasBoundedDenominators R :=
  (isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt R ⊥).trans
    (hasBoundedDenominatorsAt_bot_iff R)

/-- The closed point of a local domain, from
`FormalSpectrum.hasBoundedDenominatorsAt_maximalIdeal` through the same criterion.
`FormalSpectrum.isStalkLimit_powerSeriesXClosedPoint` proves this at every local ring and is not
weakened by it; the domain hypothesis here is the criterion's, not the statement's. -/
example (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] :
    IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXClosedPoint R) :=
  (isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt R
    (IsLocalRing.maximalIdeal R)).mpr (hasBoundedDenominatorsAt_maximalIdeal R)

/-! ### The descent from the local ring back to the ring -/

section Descent

variable (R : Type u) [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]

/-- **A denominator that clears a reciprocal divides that power of itself.** If `m ^ k` carries
`1 / s` into the image of `R`, for an `s` outside `p`, then `s ∣ m ^ k` in `R`.

This is the step every refutation of `FormalSpectrum.HasBoundedDenominatorsAt` below has to take,
and the only thing any of them does with the hypothesis at a single index: it says nothing about
how `s` was chosen, and the two consumers differ only in what they know about `s` afterwards.

Multiplying the hypothesis by `algebraMap s` collapses the reciprocal (`IsLocalization.mk'_spec`)
and leaves an equation between two images of `R`. **The domain hypothesis is spent on pushing that
equation back down**, the prime complement of a prime of a domain consisting of nonzero divisors
(`Ideal.primeCompl_le_nonZeroDivisors`, through `IsLocalization.injective`); that is the same fact
`FormalSpectrum.injective_awayToLocalizationAtPrime` spends, while
`FormalSpectrum.isFractionRing_localizationAtPrimeBot` spends a different one.
`FormalSpectrum.injective_awayToLocalizationAtPrime`'s docstring enumerates every place in this
file where a proof spends the binder. -/
theorem dvd_pow_of_mem_range_algebraMap (m : R) {s : R} (hs : s ∉ p) {k : ℕ}
    (h : algebraMap R (Localization.AtPrime p) (m ^ k) *
        IsLocalization.mk' (M := p.primeCompl) _ (1 : R) ⟨s, hs⟩ ∈
      Set.range (algebraMap R (Localization.AtPrime p))) :
    s ∣ m ^ k := by
  obtain ⟨r, hr⟩ := h
  have hmul := congrArg (· * algebraMap R (Localization.AtPrime p) s) hr
  simp only [mul_assoc] at hmul
  rw [IsLocalization.mk'_spec, map_one, mul_one, ← map_mul] at hmul
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime p)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors p)
  exact ⟨r, by rw [← hinj hmul]; ring⟩

end Descent

/-! ### A formal spectrum at which the predicate fails everywhere -/

section Int

/-- **A prime larger than a given integer and a given bound.** `Nat.exists_infinite_primes` is the
same source the `ℤ` refutation at the generic point draws its primes from. The bound is
`g.natAbs + n + 3` and each summand earns its place: the absolute value (`Int.natAbs`) is what
makes the prime miss `g`, the index is what makes the family below unbounded, and the constant is
what makes the bound *strictly* exceed that absolute value, which is what
`FormalSpectrum.bigPrimeAvoiding_notMem` needs when the index is zero. Any positive constant would
serve; three is carried over from the `(2)` version this generalises, where it also had to push
the prime past `2`. -/
def bigPrimeAvoiding (g : ℤ) (n : ℕ) : ℕ :=
  (Nat.exists_infinite_primes (g.natAbs + n + 3)).choose

theorem bigPrimeAvoiding_prime (g : ℤ) (n : ℕ) : (bigPrimeAvoiding g n).Prime :=
  (Nat.exists_infinite_primes (g.natAbs + n + 3)).choose_spec.2

theorem le_bigPrimeAvoiding (g : ℤ) (n : ℕ) : g.natAbs + n + 3 ≤ bigPrimeAvoiding g n :=
  (Nat.exists_infinite_primes (g.natAbs + n + 3)).choose_spec.1

/-- **The prime misses the ideal because it is larger than the generator**, and for no other
reason. There is no coprimality argument here and none is available: membership in the span says
that `g` divides the prime, and a prime is divisible only by one and itself, so `Int.natAbs` of
the generator is either `1` or the prime — `Prime.not_unit` rules out the first, and
`FormalSpectrum.le_bigPrimeAvoiding`, which puts the prime strictly above that absolute value,
rules out the second. -/
theorem bigPrimeAvoiding_notMem {g : ℤ} (hg : Prime g) (n : ℕ) :
    ((bigPrimeAvoiding g n : ℕ) : ℤ) ∉ Ideal.span {g} := by
  rw [Ideal.mem_span_singleton]
  intro hdvd
  have hnat : g.natAbs ∣ bigPrimeAvoiding g n := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  rcases (bigPrimeAvoiding_prime g n).eq_one_or_self_of_dvd _ hnat with h | h
  · exact hg.not_unit (Int.isUnit_iff.mpr (Int.natAbs_eq_iff.mp h |>.imp id id))
  · have := le_bigPrimeAvoiding g n
    omega

/-- **The family that refutes the condition at a nonzero prime of `ℤ`**: the reciprocals of an
infinite set of primes, each of them a legitimate element of the local ring because its
denominator is larger than the generator and so lies outside the prime.

The `ℤ` refutation at the generic point uses `FormalSpectrum.unitFractionSeries`, the reciprocals
of *all* the positive integers; that family is not available here, because the reciprocal of the
generator is not in the local ring at the ideal it generates. -/
def intPrimeFamily {g : ℤ} (hg : Prime g) [(Ideal.span {g}).IsPrime] (n : ℕ) :
    Localization.AtPrime (Ideal.span {g}) :=
  IsLocalization.mk' (M := (Ideal.span {g}).primeCompl) _ (1 : ℤ)
    ⟨((bigPrimeAvoiding g n : ℕ) : ℤ), bigPrimeAvoiding_notMem hg n⟩

/-- **The denominator condition fails at every nonzero prime of `ℤ`.** For any candidate
denominator `m`, a prime `q` exceeding `|m|` divides no power of `m`, so the reciprocal of `q` is
not cleared into `ℤ` by any power of `m` — and the family above contains such a `q` for every `m`,
because it contains a prime past every bound.

**Nothing in the argument is about the generator beyond
`FormalSpectrum.bigPrimeAvoiding_notMem`**, which is why the same dozen lines decide every prime
at once rather than one of them; `2` never played a role in it.

The step that makes the descent legal — that `ℤ → ℤ_(g)` is injective, the prime complement of a
prime of a domain consisting of nonzero divisors — is
`FormalSpectrum.dvd_pow_of_mem_range_algebraMap`, and what is left here once it is applied is
arithmetic about `Int.natAbs`. The primeness of `g` is taken here as a hypothesis and the instance
on its span as an instance binder, so that the statement elaborates at all; both are supplied
once, in `FormalSpectrum.not_hasBoundedDenominatorsAt_int`. -/
theorem not_hasBoundedDenominatorsAt_intSpan {g : ℤ} (hg : Prime g)
    [(Ideal.span {g}).IsPrime] :
    ¬ HasBoundedDenominatorsAt ℤ (Ideal.span {g}) := by
  intro h
  obtain ⟨m, hm, hall⟩ := h (intPrimeFamily hg)
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ Ideal.zero_mem _)
  obtain ⟨k, hk⟩ := hall m.natAbs
  have hdvd : ((bigPrimeAvoiding g m.natAbs : ℕ) : ℤ) ∣ m ^ k :=
    dvd_pow_of_mem_range_algebraMap ℤ (Ideal.span {g}) m
      (bigPrimeAvoiding_notMem hg m.natAbs) hk
  have hqp : Prime ((bigPrimeAvoiding g m.natAbs : ℕ) : ℤ) :=
    Nat.prime_iff_prime_int.mp (bigPrimeAvoiding_prime g m.natAbs)
  have hqm : ((bigPrimeAvoiding g m.natAbs : ℕ) : ℤ) ∣ m := hqp.dvd_of_dvd_pow hdvd
  have hnat : bigPrimeAvoiding g m.natAbs ∣ m.natAbs := by
    have hd := Int.natAbs_dvd_natAbs.mpr hqm
    simpa using hd
  have hle : bigPrimeAvoiding g m.natAbs ≤ m.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hm0) hnat
  have := le_bigPrimeAvoiding g m.natAbs
  omega

/-- **The denominator condition fails at every prime of `ℤ`, the zero ideal included.**

**Two arguments, not one, and the generic point is not a special case of the other.** At a nonzero
prime it is `FormalSpectrum.not_hasBoundedDenominatorsAt_intSpan`. At `⊥` there is no generator
that is a prime element, so `FormalSpectrum.intPrimeFamily` does not typecheck there at all, and
the branch instead reads the existing `FormalSpectrum.not_hasBoundedDenominators_int` through
`FormalSpectrum.hasBoundedDenominatorsAt_bot_iff` — which is the whole use this file makes of that
comparison outside its own consistency checks.

What lets the two branches exhaust the primes is that `ℤ` is a principal ideal ring:
`Ideal.span_singleton_generator` writes any ideal as a span, and `Ideal.span_singleton_prime`
reads `Prime g` back off the ambient `Ideal.IsPrime` once the generator is known nonzero. -/
theorem not_hasBoundedDenominatorsAt_int (p : Ideal ℤ) [p.IsPrime] :
    ¬ HasBoundedDenominatorsAt ℤ p := by
  rcases eq_or_ne p ⊥ with rfl | hp0
  · rw [hasBoundedDenominatorsAt_bot_iff]
    exact not_hasBoundedDenominators_int
  · obtain ⟨g, rfl⟩ : ∃ g : ℤ, p = Ideal.span {g} :=
      ⟨_, (Ideal.span_singleton_generator p).symm⟩
    have hgne : g ≠ 0 := fun h0 => hp0 (by rw [h0, Ideal.span_singleton_eq_bot.mpr rfl])
    exact not_hasBoundedDenominatorsAt_intSpan ((Ideal.span_singleton_prime hgne).mp ‹_›)

/-- **`FormalSpectrum.IsStalkLimit` fails at every point of `Spf (ℤ⟦X⟧, (X))`** — at the generic
point, at every closed point, with no point left over. This is the first formal spectrum on this
tree decided everywhere in the **negative** and it is no longer the only one —
`FormalSpectrum.not_isStalkLimit_powerSeriesX_of_infinite_primeIdeals` is this theorem with `ℤ`
replaced by the hypotheses the proof uses, and it is what to cite for any other ring. It is not the
first decided everywhere, since
`FormalSpectrum.isStalkLimit_bot`, `FormalSpectrum.isStalkLimit_of_isNilpotent` and
`FormalSpectrum.isStalkLimit_powerSeriesX_field` each decide a space at every one of its points,
and each of those three is positive.

The proof is the criterion at an arbitrary point applied to an arbitrary point:
`FormalSpectrum.eq_powerSeriesXPoint` says every point is a
`FormalSpectrum.powerSeriesXPoint`, and after that there is nothing left but
`FormalSpectrum.not_hasBoundedDenominatorsAt_int`.

**This is not a statement about `ℤ⟦X⟧` being a pathological ring and it refutes no theorem.** EGA
I 10.8 asks for a Noetherian adic hypothesis on a scheme; what is at stake here is the stalk half
at a formal spectrum whose ideal of definition is `FormalSpectrum.powerSeriesXIdeal`, and no
hypothesis of that theorem is claimed to hold here. -/
theorem not_isStalkLimit_powerSeriesX_int (x : FormalSpectrum (powerSeriesXIdeal ℤ)) :
    ¬ IsStalkLimit (powerSeriesXIdeal ℤ) x := by
  rw [eq_powerSeriesXPoint ℤ x, isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt]
  exact not_hasBoundedDenominatorsAt_int _

/-- **`(2)` is prime in `ℤ`.** Stated as an instance so that a prime of `ℤ[X]` above it, or a point
of a formal spectrum over it, is prime by synthesis.

It sits with a consumer rather than below both of them. The other consumer is
`FormalSchemes.StructureSheafStalkPowerSeriesLocal`, where it makes `FormalSpectrum.polyIntTwoX`
prime; that module reaches this one through
`FormalSchemes.StructureSheafStalkPowerSeriesDedekind`, so one declaration still serves both, and
nothing that consumed the instance in its old home has lost it. It was declared in
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, below both consumers, for as long as
neither of them could reach the other and so neither could host it — a placement resting on the
**absence** of an edge, which any module added above either consumer can end, and one did. The
placement here rests on that edge instead, which is a claim about the graph that the graph can
only strengthen.

**The general statement is a hypothesis and not an instance.** The results above take
`[p.IsPrime]` on an arbitrary `p`, and at a span it is `Ideal.span_singleton_prime` in one rewrite,
which is this proof. What a global instance buys is the places where the ideal is written out and
no such hypothesis is in scope: the three theorems below, and the primality of
`FormalSpectrum.polyIntTwoX` in the local module, which is `Ideal.comap_isPrime` of this one. -/
instance isPrime_span_singleton_two : (Ideal.span {(2 : ℤ)}).IsPrime := by
  rw [Ideal.span_singleton_prime two_ne_zero]
  exact Int.prime_two

/-- **The denominator condition fails at `(2) ⊆ ℤ`.** The case of
`FormalSpectrum.not_hasBoundedDenominatorsAt_int` at the prime `(2)`, kept as a name because it is
what the closed point below is about. -/
theorem not_hasBoundedDenominatorsAt_intTwo :
    ¬ HasBoundedDenominatorsAt ℤ (Ideal.span {(2 : ℤ)}) :=
  not_hasBoundedDenominatorsAt_int _

/-- **`FormalSpectrum.IsStalkLimit` fails at the point of `Spf (ℤ⟦X⟧, (X))` over `(2)`.** -/
theorem not_isStalkLimit_powerSeriesXPoint_intTwo :
    ¬ IsStalkLimit (powerSeriesXIdeal ℤ) (powerSeriesXPoint ℤ (Ideal.span {(2 : ℤ)})) :=
  not_isStalkLimit_powerSeriesX_int _

/-- **A closed point at which `FormalSpectrum.IsStalkLimit` fails.**

Every negative value of the predicate that predates this file is at a **generic** point — of
`ℤ⟦X⟧`, of the local domain in `FormalSchemes.StructureSheafStalkPowerSeriesLocal`, and of the ring
of integers of a number field in
`FormalSchemes.StructureSheafStalkPowerSeriesNumberField` — and every positive value at a closed
point carries `[IsLocalRing R]`.

**Only the closedness half is about `(2)`.** The failure half is the case of
`FormalSpectrum.not_isStalkLimit_powerSeriesX_int` at this point and says nothing about `2` that
it does not say about every prime; what is genuinely about `(2)` is that it is maximal, which is
what makes the singleton closed.

**This refutes no theorem on this tree.** `FormalSpectrum.powerSeriesXClosedPoint` is defined only
at a local ring, so the instance in `FormalSpectrum.isStalkLimit_powerSeriesXClosedPoint` cannot be
deleted from a statement that would not typecheck without it. What it refutes is the reading that a
closed point is one where the colimit over basic opens has nothing to do: `ℤ` is not local, the
basic opens through this point are a genuinely filtered system, and the colimit misses `1 / q` for
every odd prime `q` past the denominator on offer. -/
theorem isClosed_and_not_isStalkLimit_powerSeriesXPoint_intTwo :
    IsClosed ({powerSeriesXPoint ℤ (Ideal.span {(2 : ℤ)})} :
        Set (FormalSpectrum (powerSeriesXIdeal ℤ))) ∧
      ¬ IsStalkLimit (powerSeriesXIdeal ℤ) (powerSeriesXPoint ℤ (Ideal.span {(2 : ℤ)})) :=
  ⟨(isClosed_singleton_powerSeriesXPoint_iff ℤ (Ideal.span {(2 : ℤ)})).mpr
      (PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible),
    not_isStalkLimit_powerSeriesXPoint_intTwo⟩

end Int

/-! ### The classification at a unique factorisation domain, at every prime

At `⊥` the denominator condition is a cardinality:
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes` says it holds at a unique factorisation
domain exactly when there are finitely many primes up to associates. **The same is true at every
prime, with the primes counted outside it.** Both directions are that proof with *nonzero*
replaced by *outside `p`*, and neither replacement is free: the forward one has to descend from
`Localization.AtPrime p` rather than from a fraction field, and the backward one has to know that
the factors of an element outside `p` are themselves outside `p`, which is closure of a *prime*
ideal downwards along divisibility rather than the corresponding triviality about being nonzero.

**Nothing here weakens `[UniqueFactorizationMonoid R]`, and the forward direction is refuted
without it.** An ultrapower of `ℤ` satisfies the denominator condition and has infinitely many
prime associate classes (`FormalSpectrum.not_forall_hasBoundedDenominators_imp_finite_primes`, in
`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`); `⊥` is one of the primes below, so that
witness refutes the `↔` below as it stands. **This is a statement about prime elements and not
about prime ideals**, so `FormalSpectrum.hasBoundedDenominators_iff_finite_primeIdeals` is not a
corollary of it and does not become one — a non-principal maximal ideal contributes no prime
element at all.
-/

section UniqueFactorization

variable (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]

/-- **A single denominator for everything outside `p` gives the condition**, with no hypothesis on
`R` whatever: if every `s ∉ p` divides a power of `m` and `m ∉ p`, then that one `m` serves every
family at once.

Each member of a family is `IsLocalization.mk' r s` with `s ∉ p`
(`IsLocalization.mk'_surjective` at the prime complement), and `m ^ k = s * t` turns clearing by
`m ^ k` into clearing by `s`, which is `IsLocalization.mk'_spec'`. The exponent depends on the
member and the denominator does not, which is exactly the shape
`FormalSpectrum.HasBoundedDenominatorsAt` asks for.

**This is the sufficient half of the classification below and is strictly more general than it**:
it carries neither `[IsDomain R]` nor `[UniqueFactorizationMonoid R]`, and a consumer at a
concrete ring may find the divisibility easier to check than the condition. -/
theorem hasBoundedDenominatorsAt_of_forall_dvd_pow {m : R} (hm : m ∉ p)
    (hall : ∀ s : R, s ∉ p → ∃ k : ℕ, s ∣ m ^ k) :
    HasBoundedDenominatorsAt R p := by
  intro x
  refine ⟨m, hm, fun n => ?_⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective p.primeCompl (x n)
  obtain ⟨k, t, ht⟩ := hall (s : R) s.2
  have hspec : algebraMap R (Localization.AtPrime p) (s : R) *
      IsLocalization.mk' (Localization.AtPrime p) r s =
      algebraMap R (Localization.AtPrime p) r := IsLocalization.mk'_spec' _ r s
  refine ⟨k, t * r, ?_⟩
  rw [← hrs, ht, map_mul, map_mul,
    mul_comm (algebraMap R (Localization.AtPrime p) (s : R)),
    mul_assoc, hspec]

/-- **Infinitely many pairwise non-associated primes outside `p` refute the condition.** This is
`FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated` at an arbitrary prime, and
the family that defeats every candidate denominator is the same one: the reciprocals of the given
primes, each of them an element of `Localization.AtPrime p` because its denominator is outside
`p`.

`FormalSpectrum.dvd_pow_of_mem_range_algebraMap` turns the clearing of `1 / q n` into
`q n ∣ m ^ k`, primeness of `q n` into `q n ∣ m`, and then unique factorisation finishes: the
chosen primes inject into `UniqueFactorizationMonoid.factors m`, which is a finite multiset.
**`m ≠ 0` is not a hypothesis and is not proved** — `0 ∈ p`, so `m ∉ p` already says it, and that
is one place where a general prime is cheaper than the generic point rather than dearer. -/
theorem not_hasBoundedDenominatorsAt_of_primes_notMem [IsDomain R]
    [UniqueFactorizationMonoid R] (q : ℕ → R) (hq : ∀ n, Prime (q n)) (hqp : ∀ n, q n ∉ p)
    (hne : ∀ i j, Associated (q i) (q j) → i = j) : ¬ HasBoundedDenominatorsAt R p := by
  classical
  intro h
  obtain ⟨m, hm, hall⟩ :=
    h fun n => IsLocalization.mk' (M := p.primeCompl) _ (1 : R) ⟨q n, hqp n⟩
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ Ideal.zero_mem p)
  have hdvd : ∀ n, q n ∣ m := by
    intro n
    obtain ⟨k, hk⟩ := hall n
    exact (hq n).dvd_of_dvd_pow (dvd_pow_of_mem_range_algebraMap R p m (hqp n) hk)
  choose f hf hfa using fun n =>
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd hm0 (hq n).irreducible (hdvd n)
  have hinj : Function.Injective f := fun i j hij =>
    hne i j ((hfa i).trans (hij ▸ (hfa j).symm))
  have hsub : Set.range f ⊆ (UniqueFactorizationMonoid.factors m).toFinset := by
    rintro _ ⟨n, rfl⟩
    exact Multiset.mem_toFinset.mpr (hf n)
  exact Set.infinite_range_of_injective hinj
    (((UniqueFactorizationMonoid.factors m).toFinset.finite_toSet).subset hsub)

omit [p.IsPrime] in
/-- **Everything outside `p` divides a power of the product of a covering set of primes.** The
analogue of `FormalSpectrum.forall_dvd_pow_prod`, where the set has to cover only the primes
outside `p` and the conclusion is only about elements outside `p`.

**That weaker covering hypothesis is enough for the stronger-looking conclusion because a prime
ideal is closed downwards along divisibility**: a factor of `s` lying in `p` would put `s` in `p`
(`Ideal.mem_of_dvd`), so every member of `UniqueFactorizationMonoid.factors s` is one of the
primes the hypothesis covers. That step has no counterpart in the proof at the generic point,
where *nonzero* is closed under divisors for nothing. After it the argument is the same:
each factor divides the product, and a product of `Multiset.card` many divisors of one element
divides that many-th power of it (`Multiset.prod_dvd_prod_of_dvd` at the constant function).

`s ≠ 0` is not a hypothesis here either: `0 ∈ p`. -/
theorem forall_dvd_pow_prod_notMem [IsDomain R] [UniqueFactorizationMonoid R] (t : Finset R)
    (hcov : ∀ q : R, Prime q → q ∉ p → ∃ w ∈ t, Associated q w) :
    ∀ s : R, s ∉ p → ∃ k : ℕ, s ∣ (t.prod id) ^ k := by
  intro s hs
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ Ideal.zero_mem p)
  refine ⟨Multiset.card (UniqueFactorizationMonoid.factors s), ?_⟩
  refine ((UniqueFactorizationMonoid.factors_prod hs0).symm.dvd).trans ?_
  have hdvd : ∀ x ∈ UniqueFactorizationMonoid.factors s, id x ∣ (fun _ : R => t.prod id) x := by
    intro x hx
    have hxp : Prime x := UniqueFactorizationMonoid.prime_of_factor x hx
    have hxs : x ∣ s := UniqueFactorizationMonoid.dvd_of_mem_factors hx
    have hxnp : x ∉ p := fun hmem => hs (p.mem_of_dvd hxs hmem)
    obtain ⟨w, hw, hassoc⟩ := hcov x hxp hxnp
    exact hassoc.dvd.trans (Finset.dvd_prod_of_mem id hw)
  simpa using Multiset.prod_dvd_prod_of_dvd (S := UniqueFactorizationMonoid.factors s) id
    (fun _ => t.prod id) hdvd

/-- **Finitely many prime classes outside `p` give a single denominator outside `p`**: the product
of one representative of each, through `FormalSpectrum.forall_dvd_pow_prod_notMem`. The analogue
of `FormalSpectrum.exists_forall_dvd_pow_of_finite_primes`, and the backward direction of the
classification below is this composed with
`FormalSpectrum.hasBoundedDenominatorsAt_of_forall_dvd_pow`.

**That the product is itself outside `p` is where primeness is spent a second time**, through
`Ideal.IsPrime.prod_mem_iff`; at the generic point the corresponding step is that a product of
nonzero elements of a domain is nonzero, which is a different fact about a different hypothesis.

The representatives are chosen by a total function with a junk value off the set, rather than on
the subtype, because `Associates.out` needs `[NormalizationMonoid R]` and a bare unique
factorisation domain does not carry it — the same reason
`FormalSpectrum.exists_forall_dvd_pow_of_finite_primes` chooses on `Associates.mk_surjective`. The
`m` is not canonical and nothing below depends on the choice. -/
theorem exists_forall_dvd_pow_notMem_of_finite [IsDomain R] [UniqueFactorizationMonoid R]
    (hfin : {a : Associates R | Prime a ∧ ∃ r : R, Associates.mk r = a ∧ r ∉ p}.Finite) :
    ∃ m : R, m ∉ p ∧ ∀ s : R, s ∉ p → ∃ k : ℕ, s ∣ m ^ k := by
  classical
  have hex : ∀ a : Associates R, ∃ r : R,
      a ∈ {a : Associates R | Prime a ∧ ∃ r : R, Associates.mk r = a ∧ r ∉ p} →
        Associates.mk r = a ∧ r ∉ p := by
    intro a
    by_cases ha : a ∈ {a : Associates R | Prime a ∧ ∃ r : R, Associates.mk r = a ∧ r ∉ p}
    · obtain ⟨r, hr1, hr2⟩ := ha.2
      exact ⟨r, fun _ => ⟨hr1, hr2⟩⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose rep hrep using hex
  refine ⟨(hfin.toFinset.image rep).prod id, ?_, ?_⟩
  · intro hmem
    obtain ⟨w, hw, hwp⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
    exact (hrep a ((Set.Finite.mem_toFinset hfin).mp ha)).2 hwp
  · refine forall_dvd_pow_prod_notMem R p _ ?_
    intro q hq hqp
    refine ⟨rep (Associates.mk q), Finset.mem_image_of_mem _ ?_, ?_⟩
    · exact (Set.Finite.mem_toFinset hfin).mpr ⟨Associates.prime_mk.mpr hq, q, rfl, hqp⟩
    · exact Associates.mk_eq_mk_iff_associated.mp
        (hrep _ ⟨Associates.prime_mk.mpr hq, q, rfl, hqp⟩).1.symm

/-- **The condition at a unique factorisation domain is a cardinality at every prime, not only at
`⊥`**: it holds at `p` exactly when finitely many primes up to associates lie outside `p`.

`Associates R` is the quotient by the associate relation, so the set says *up to associates* with
no choice of representatives in the statement; the extra clause asks that the class have **some**
representative outside `p`, which is the same as asking it of every one, since `p` is an ideal.
Choice enters in both directions of the proof and only there.

Forwards is `FormalSpectrum.not_hasBoundedDenominatorsAt_of_primes_notMem` at a family extracted
from an infinite set by `Set.Infinite.natEmbedding`, the injectivity of the embedding being
exactly the *pairwise non-associated* hypothesis. Backwards is
`FormalSpectrum.exists_forall_dvd_pow_notMem_of_finite` into
`FormalSpectrum.hasBoundedDenominatorsAt_of_forall_dvd_pow`.

**This is the analogue at a general prime that the module header above said was missing**, and
with `FormalSpectrum.isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt` it decides
`FormalSpectrum.IsStalkLimit` at every point of `Spf (R⟦X⟧, (X))` over a unique factorisation
domain, in both directions. It says nothing at a general domain: `⊥` is one of its primes, so the
ultrapower that refutes the classification there refutes this one too. -/
theorem hasBoundedDenominatorsAt_iff_finite_primes [IsDomain R] [UniqueFactorizationMonoid R] :
    HasBoundedDenominatorsAt R p ↔
      {a : Associates R | Prime a ∧ ∃ r : R, Associates.mk r = a ∧ r ∉ p}.Finite := by
  classical
  constructor
  · intro h
    by_contra hinf
    rw [Set.not_finite] at hinf
    let e : ℕ ↪ {a : Associates R //
      a ∈ {a : Associates R | Prime a ∧ ∃ r : R, Associates.mk r = a ∧ r ∉ p}} :=
      hinf.natEmbedding
    choose q hq hqp using fun n : ℕ => (e n).2.2
    refine not_hasBoundedDenominatorsAt_of_primes_notMem R p q (fun n => ?_) hqp
      (fun i j hij => ?_) h
    · exact Associates.prime_mk.mp (hq n ▸ (e n).2.1)
    · have hee : (e i : Associates R) = e j := by
        rw [← hq i, ← hq j]
        exact Associates.mk_eq_mk_iff_associated.mpr hij
      exact e.injective (Subtype.ext hee)
  · intro hfin
    obtain ⟨m, hm, hall⟩ := exists_forall_dvd_pow_notMem_of_finite R p hfin
    exact hasBoundedDenominatorsAt_of_forall_dvd_pow R p hm hall

end UniqueFactorization

/-! ### What the classification answers about the condition itself

The right-hand side above shrinks as the prime grows, so the condition is **monotone in the
prime** at a unique factorisation domain, and *the condition at `⊥`* — which is the denominator
condition, by `FormalSpectrum.hasBoundedDenominatorsAt_bot_iff` — implies it everywhere. Those are
two of the three questions the module header lists as open about
`FormalSpectrum.HasBoundedDenominatorsAt`, and the theorem above is the third.

**The converse of monotonicity is false, and the witness is already on this tree.** `ℤ[X]`
localized at `(2, X)` is a local unique factorisation domain, so the condition holds at its
maximal ideal (`FormalSpectrum.hasBoundedDenominatorsAt_maximalIdeal`) and fails at `⊥`, where
`FormalSchemes.StructureSheafStalkPowerSeriesLocal` refutes it. That is stated here in prose
rather than proved, because that module is **downstream** of this one:
`FormalSchemes.StructureSheafStalkPowerSeriesLocal` imports
`FormalSchemes.StructureSheafStalkPowerSeriesDedekind`, which imports this file, so the witness
cannot be named from here at all. It could be named *there*, at no module cost, and that is the
successor row rather than this one.
-/

section UniqueFactorizationCorollaries

variable (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

omit [IsDomain R] [UniqueFactorizationMonoid R] in
/-- **At `⊥` the primes outside the prime are all the primes.** The clause that cuts the count
down is vacuous at the zero ideal, because `Ideal.mem_bot` reads *outside `⊥`* as *nonzero* and a
prime class has a nonzero representative — every representative, in fact.

This is what makes `FormalSpectrum.hasBoundedDenominatorsAt_iff_finite_primes` a generalisation of
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes` rather than a statement beside it, and
it is used only for the `example` below that checks exactly that. It needs neither instance of the
section. -/
theorem setOf_prime_notMem_bot :
    {a : Associates R | Prime a ∧ ∃ r : R, Associates.mk r = a ∧ r ∉ (⊥ : Ideal R)} =
      {a : Associates R | Prime a} := by
  ext a
  refine ⟨fun h => h.1, fun ha => ⟨ha, ?_⟩⟩
  obtain ⟨r, rfl⟩ := Associates.mk_surjective a
  exact ⟨r, rfl, fun h0 => (Associates.prime_mk.mp ha).ne_zero (Ideal.mem_bot.mp h0)⟩

/-- **The condition is monotone in the prime** at a unique factorisation domain: it passes from a
prime to any larger one. The larger prime swallows more prime elements, so fewer classes are left
outside it, and `Set.Finite.subset` is the whole proof.

**The converse is false**, by the witness the section heading above names, and this is one of the
three questions the module header lists as open about
`FormalSpectrum.HasBoundedDenominatorsAt`. -/
theorem hasBoundedDenominatorsAt_of_le (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q)
    (h : HasBoundedDenominatorsAt R p) : HasBoundedDenominatorsAt R q :=
  (hasBoundedDenominatorsAt_iff_finite_primes R q).mpr
    (((hasBoundedDenominatorsAt_iff_finite_primes R p).mp h).subset
      fun _ ha => ⟨ha.1, ha.2.choose, ha.2.choose_spec.1,
        fun hmem => ha.2.choose_spec.2 (hpq hmem)⟩)

/-- **The denominator condition implies the condition at every prime**, at a unique factorisation
domain: the case `p = ⊥` of monotonicity above, read through
`FormalSpectrum.hasBoundedDenominatorsAt_bot_iff`.

This is the second of the three questions the module header lists as open, and it is the direction
that is true: the condition at a prime does **not** imply it at `⊥`, by the same witness. -/
theorem hasBoundedDenominatorsAt_of_hasBoundedDenominators (h : HasBoundedDenominators R)
    (p : Ideal R) [p.IsPrime] : HasBoundedDenominatorsAt R p :=
  hasBoundedDenominatorsAt_of_le R ⊥ p bot_le ((hasBoundedDenominatorsAt_bot_iff R).mpr h)

/-- **`FormalSpectrum.IsStalkLimit` at every point of `Spf (R⟦X⟧, (X))` over a unique
factorisation domain, in both directions**: the criterion at an arbitrary point composed with the
classification above.

Every earlier value of the predicate on this tree is either at one distinguished point, or at one
ring, or negative; this is the first statement that decides it everywhere on a space and can come
out either way, the answer depending on how many primes lie outside the point's own. -/
theorem isStalkLimit_powerSeriesXPoint_iff_finite_primes (p : Ideal R) [p.IsPrime] :
    IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXPoint R p) ↔
      {a : Associates R | Prime a ∧ ∃ r : R, Associates.mk r = a ∧ r ∉ p}.Finite :=
  (isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt R p).trans
    (hasBoundedDenominatorsAt_iff_finite_primes R p)

/-! ### The classification against what the tree already knows

The three `example`s below are **checks and not results**, exactly as the pair under
`### The two known points, as values of the criterion` is: each restates something this tree
already proves and derives it from the classification above, and each is an `example` so that no
statement gets a second declaration.
-/

/-- The classification at `⊥` is the classification at the generic point:
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes`, recovered through
`FormalSpectrum.hasBoundedDenominatorsAt_bot_iff` and `FormalSpectrum.setOf_prime_notMem_bot`.
This is what makes *generalisation* a checked word here rather than an assertion. -/
example : HasBoundedDenominators R ↔ {a : Associates R | Prime a}.Finite := by
  rw [← hasBoundedDenominatorsAt_bot_iff, hasBoundedDenominatorsAt_iff_finite_primes,
    setOf_prime_notMem_bot]

/-- The value at the maximal ideal of a local ring, at a local unique factorisation domain: the
set is empty, because a prime element is a nonunit and every nonunit of a local ring lies in the
maximal ideal. `FormalSpectrum.hasBoundedDenominatorsAt_maximalIdeal` proves this at **every**
local ring, with no factorisation and no domain hypothesis, and is not weakened by it. -/
example [IsLocalRing R] : HasBoundedDenominatorsAt R (IsLocalRing.maximalIdeal R) := by
  refine (hasBoundedDenominatorsAt_iff_finite_primes R _).mpr ?_
  convert Set.finite_empty
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ha ⟨r, rfl, hr⟩
  exact (Associates.prime_mk.mp ha).not_unit (IsLocalRing.notMem_maximalIdeal.mp hr)

/-- `FormalSpectrum.not_hasBoundedDenominatorsAt_int` read through the classification: it becomes
*`ℤ` has infinitely many prime classes outside every one of its primes*, which is Euclid with one
prime removed. This is the only one of the three checks that exercises the **forward** direction,
and it is stated at `ℤ` rather than at the section's `R` because that is the ring the refutation
is about. -/
example (p : Ideal ℤ) [p.IsPrime] :
    ¬ {a : Associates ℤ | Prime a ∧ ∃ r : ℤ, Associates.mk r = a ∧ r ∉ p}.Finite :=
  fun hfin => not_hasBoundedDenominatorsAt_int p
    ((hasBoundedDenominatorsAt_iff_finite_primes ℤ p).mpr hfin)

end UniqueFactorizationCorollaries

end FormalSpectrum

end
