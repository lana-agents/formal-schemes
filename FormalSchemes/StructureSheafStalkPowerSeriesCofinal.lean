import FormalSchemes.CofinalStalkLimit
import FormalSchemes.StructureSheafStalkPowerSeriesDedekind
import FormalSchemes.CofinalAdicRing
import Mathlib.RingTheory.PowerSeries.Ideal

set_option linter.style.header false

/-!
# The `R⟦X⟧` stalk-limit values, at every other ideal of definition

`FormalSchemes.CofinalStalkLimit` proves that `FormalSpectrum.IsStalkLimit` does not depend on the
ideal of definition: for two ideals of definition `I`, `J` of one adic ring it holds at a point of
`Spf_I R` exactly when it holds at the partner point of `Spf_J R`. This file reads that theorem at
the one adic ring this tree has decided values at — `R⟦X⟧` with its `(X)`-adic topology — and so
carries the values of the `FormalSchemes.StructureSheafStalkPowerSeries*` cluster off `(X)`.

## What the hypothesis on the second ideal is, and why no topology appears below

An ideal of definition of `R⟦X⟧` *for the `(X)`-adic topology* is exactly an ideal cofinal with
`(X)` in the sense of `Ideal.IsCofinal` (`FormalSchemes.CofinalIdeal`): `Ideal.IsCofinal.isAdic`
turns a cofinality into the equality of topologies that `IsAdic` unfolds to, and `IsAdic.isCofinal`
turns it back. So every value below takes the topology-free hypothesis
`Ideal.IsCofinal (powerSeriesXIdeal R) J`, and **`IsAdicRing J` is derived rather than assumed**,
by `IsAdicRing.of_isCofinal` (`FormalSchemes.CofinalAdicRing`) at the `(X)`-adic topology — for
which `(X)` is an ideal of definition by `isAdicRing_adicTopology`
(`FormalSchemes.StructureSheafStalkNilpotent`) together with Mathlib's `IsAdicComplete` instance
for `(X) ⊆ R⟦X⟧`. As in `FormalSchemes.StructureSheafStalkPowerSeries`, the topology is supplied
inside each proof and **the statements carry none**.

**`Ideal.FG` of `J` is a second hypothesis, it is not free in general, and it is free at every ring
the values below are stated at.** `FormalSpectrum.isStalkLimit_congr` takes `Ideal.FG` of both
ideals — `FormalSpectrum.awayToAtPrimeCompletion`, `FormalSpectrum.awayCompletionRestrict` and
`AdicCompletion.mapCompletion` each take it — and on the `(X)` side
`FormalSpectrum.fg_powerSeriesXIdeal` discharges it, while on the `J` side nothing does in general.
An ideal cofinal with a finitely generated ideal need not be finitely generated, and this tree
carries no lemma producing `Ideal.FG` from an ideal of definition:
`FormalSchemes.LargestIdealOfDefinition` and `FormalSchemes.IdealsOfDefinition` were both read for
a statement of that shape and neither has one. **So the general statements here keep the
hypothesis and say so.**

What removes it in every case this file decides is that `R⟦X⟧` is Noetherian as soon as `R` is —
Mathlib's instance in `Mathlib/RingTheory/PowerSeries/Ideal.lean`, which is this file's one new
Mathlib import — and all three values are at a Noetherian ring: `ℤ`, a field, and a Noetherian
domain of dimension at most one. `FormalSpectrum.fg_powerSeriesIdeal_of_isNoetherianRing` is the
one step, so **the three transported values carry no finiteness hypothesis at all**: they are about
*every* ideal of definition of their power series ring, not merely every finitely generated one.
That is stronger than the umbrella promised, and it is why the qualification is absent from their
statements rather than hidden in them.

## What is transported, and what is not

Three values, chosen so that both answers appear and neither needs a name for a point:

* the everywhere-negative one at `ℤ`, `FormalSpectrum.not_isStalkLimit_powerSeriesX_int`
  (`FormalSchemes.StructureSheafStalkPowerSeriesPoint`);
* its generalisation `FormalSpectrum.not_isStalkLimit_powerSeriesX_of_infinite_primeIdeals`
  (`FormalSchemes.StructureSheafStalkPowerSeriesDedekind`);
* the everywhere-positive one at a field, `FormalSpectrum.isStalkLimit_powerSeriesX_field`
  (`FormalSchemes.StructureSheafStalkPowerSeries`).

All three quantify over the points of their own formal spectrum, so the transported statement needs
no name for the points of `Spf_J R`: that is why these three, and why they all factor through the
single bridge `FormalSpectrum.exists_isStalkLimit_powerSeriesX_iff_of_isCofinal` below. All three
are also at a Noetherian ring, which is what lets them drop `Ideal.FG`.

The **pointwise** classifications are *not* transported.
`FormalSpectrum.isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt` and
`FormalSpectrum.isStalkLimit_powerSeriesXPoint_iff_finite_primes` are stated at
`FormalSpectrum.powerSeriesXPoint R p`, a point named by a prime of `R`; the partner of that point
is `FormalSpectrum.cofinalPoint (powerSeriesXIdeal R) J (powerSeriesXPoint R p)`, which is correct
and tells a reader nothing, because the resulting `J`-side statement is not indexed by a prime of
`R` in any way that can be used. Giving the points of `Spf_J R` their own name over
`PrimeSpectrum R` would buy that indexing, at the price of a definition, its two computation
lemmas and the homeomorphism argument identifying it with
`FormalSpectrum.powerSeriesXHomeo`. It is not done here and nothing below needs it.

`FormalSpectrum.not_isStalkLimit_powerSeriesXRingOfIntegers`
(`FormalSchemes.StructureSheafStalkPowerSeriesNumberField`) is not restated either: it is
`FormalSpectrum.not_isStalkLimit_powerSeriesX_of_infinite_primeIdeals` at the ring of integers of a
number field, so the transported form of that theorem already covers it once a caller supplies the
four instances, and importing that module to say so again would cost one more module in this
file's import cone for no new content.

## The family is not empty

`FormalSpectrum.powerSeriesXIdeal_pow_ne` says `(X) ^ k ≠ (X)` for `k ≥ 2` over a nontrivial ring,
and `Ideal.IsCofinal.pow` (`FormalSchemes.CofinalIdeal`) says `(X) ^ k` is cofinal with `(X)` for
every `k ≠ 0`. So `FormalSpectrum.not_isStalkLimit_powerSeriesXIdealPow_int` is a decision at a
formal spectrum of `ℤ⟦X⟧` whose ideal of definition genuinely **is not** `(X)`, and the transport
is not a claim about a family with one member in it.
`FormalSpectrum.exists_isCofinal_ne_powerSeriesXIdeal_not_isStalkLimit_int` is that sentence as a
theorem, cofinality conjunct and all, which is what makes it checkable rather than prose: without
that conjunct the statement would quantify over every ideal of `ℤ⟦X⟧` and `⊤`, whose formal
spectrum is empty, would satisfy it.

## What is *not* proved here

**Nothing that produces `Ideal.FG` from cofinality.** The general transport,
`FormalSpectrum.isStalkLimit_powerSeriesX_congr`, and the bridge below both keep the hypothesis,
and no lemma removing it is proved or used. What the three values use instead is the Noetherianness
their own base ring already carries, which is a different argument and reaches no further than it.

**Nothing at a formal spectrum whose ring is not a power series ring.** Cofinal invariance moves
the ideal of definition and not the ring, so the second of the two questions
`FormalSchemes.StructureSheafStalkPowerSeriesPoint` names as open is as untouched here as it is
there.

**No new stalk-limit fact at `(X)`.** Every value below is a theorem already on this tree read
through `FormalSpectrum.isStalkLimit_congr`; nothing about
`FormalSpectrum.HasBoundedDenominatorsAt` is stated, used or strengthened.

## Main results

* `FormalSpectrum.isStalkLimit_powerSeriesX_congr`: at a finitely generated ideal of definition `J`
  of `R⟦X⟧` the predicate is the predicate at `(X)`, at the partner point.
* `FormalSpectrum.not_isStalkLimit_powerSeriesXCofinal_int`: **false** at every point of every
  ideal of definition of `ℤ⟦X⟧`, with no finiteness hypothesis.
* `FormalSpectrum.isStalkLimit_powerSeriesXCofinal_field`: **true** at every point of every ideal
  of definition of `k⟦X⟧`, for `k` a field.
* `FormalSpectrum.not_isStalkLimit_powerSeriesXCofinal_of_infinite_primeIdeals`: the negative value
  at a Noetherian domain of dimension at most one with infinitely many nonzero primes.
* `FormalSpectrum.fg_powerSeriesIdeal_of_isNoetherianRing`: what removes the finiteness hypothesis
  from the three of them.
* `FormalSpectrum.exists_isCofinal_ne_powerSeriesXIdeal_not_isStalkLimit_int`: **there is an ideal
  of definition of `ℤ⟦X⟧` other than `(X)`** at which the predicate is false at every point — the
  ideal-of-definition clause being the statement's own cofinality conjunct — so none of this is a
  restatement of what was already there.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.3 and §10.8.
-/

noncomputable section

universe u

open PowerSeries

namespace FormalSpectrum

section Ambient

variable {R : Type u} [CommRing R] [TopologicalSpace (PowerSeries R)]
  [IsAdicRing (powerSeriesXIdeal R)] (J : Ideal (PowerSeries R)) [IsAdicRing J]

/-- **The stalk-limit predicate at an ideal of definition of `R⟦X⟧` is the predicate at `(X)`.**
This is `FormalSpectrum.isStalkLimit_congr` (`FormalSchemes.CofinalStalkLimit`) with the second
ideal taken to be `FormalSpectrum.powerSeriesXIdeal`, whose `Ideal.FG` hypothesis is discharged by
`FormalSpectrum.fg_powerSeriesXIdeal`. Nothing else happens in the proof.

The ambient topology is one for which `(X)` is an ideal of definition, and there is only one such:
`IsAdicRing.isAdic` unfolds to the assertion that the topology *is* `Ideal.adicTopology (X)`. It is
a hypothesis here rather than a choice so that the statement composes with anything else stated in
an adic ring; the values below fix it and carry no topology at all. -/
theorem isStalkLimit_powerSeriesX_congr (hJ : J.FG) (y : FormalSpectrum J) :
    IsStalkLimit J y ↔
      IsStalkLimit (powerSeriesXIdeal R) (cofinalPoint J (powerSeriesXIdeal R) y) :=
  isStalkLimit_congr J (powerSeriesXIdeal R) hJ (fg_powerSeriesXIdeal R) y

end Ambient

section Values

variable {R : Type u} [CommRing R]

/-- **The bridge every value below crosses**: a point of `Spf_J R⟦X⟧`, for `J` a finitely generated
ideal of definition of `R⟦X⟧`, has a point of `Spf ((X) ⊆ R⟦X⟧)` at which the stalk-limit predicate
takes the same value.

Stated as an existential because naming the point is `FormalSpectrum.cofinalPoint`, which takes the
topology and the two `IsAdicRing` instances that this statement exists to hide;
`FormalSpectrum.isStalkLimit_powerSeriesX_congr` above is the precise form and says which point it
is. An existential is enough for every value transported below, because each of them holds at
*every* point of `Spf ((X) ⊆ R⟦X⟧)`.

The hypothesis is topology-free and is what "ideal of definition of `R⟦X⟧`" means here: the
`(X)`-adic topology is chosen inside the proof, `(X)` is an ideal of definition for it by
`isAdicRing_adicTopology` (`FormalSchemes.StructureSheafStalkNilpotent`), and `J` is one by
`IsAdicRing.of_isCofinal` (`FormalSchemes.CofinalAdicRing`). -/
theorem exists_isStalkLimit_powerSeriesX_iff_of_isCofinal {J : Ideal (PowerSeries R)}
    (h : Ideal.IsCofinal (powerSeriesXIdeal R) J) (hJ : J.FG) (y : FormalSpectrum J) :
    ∃ x : FormalSpectrum (powerSeriesXIdeal R),
      (IsStalkLimit J y ↔ IsStalkLimit (powerSeriesXIdeal R) x) := by
  letI : TopologicalSpace (PowerSeries R) := (powerSeriesXIdeal R).adicTopology
  haveI : IsAdicRing (powerSeriesXIdeal R) := isAdicRing_adicTopology (powerSeriesXIdeal R)
  haveI : IsAdicRing J := IsAdicRing.of_isCofinal h
  exact ⟨cofinalPoint J (powerSeriesXIdeal R) y, isStalkLimit_powerSeriesX_congr J hJ y⟩

/-- **Over a Noetherian base every ideal of `R⟦X⟧` is finitely generated**, so the `Ideal.FG`
hypothesis of `FormalSpectrum.exists_isStalkLimit_powerSeriesX_iff_of_isCofinal` costs nothing at
any of the three rings this file decides. `R⟦X⟧` is Noetherian when `R` is, by Mathlib's instance
in `Mathlib/RingTheory/PowerSeries/Ideal.lean`, and `isNoetherianRing_iff_ideal_fg` is the rest.

The hypothesis is **not** free in general and the two statements above keep it; this is why the
three values below do not. -/
theorem fg_powerSeriesIdeal_of_isNoetherianRing [IsNoetherianRing R] (J : Ideal (PowerSeries R)) :
    J.FG :=
  (isNoetherianRing_iff_ideal_fg _).mp inferInstance J

/-- **`(X) ^ k` is not `(X)`** once `k ≥ 2` and `R` is nontrivial: `X` itself is in the second and
not in the first, because `X ^ k ∣ X` would force the coefficient of `X` in `X` to vanish
(`PowerSeries.X_pow_dvd_iff`).

It is here so that `FormalSpectrum.not_isStalkLimit_powerSeriesXIdealPow_int` is a statement about
an ideal of definition other than `(X)` rather than possibly about `(X)` again. -/
theorem powerSeriesXIdeal_pow_ne [Nontrivial R] {k : ℕ} (hk : 2 ≤ k) :
    powerSeriesXIdeal R ^ k ≠ powerSeriesXIdeal R := by
  intro hEq
  have hmem : (X : PowerSeries R) ∈ powerSeriesXIdeal R ^ k := by
    rw [hEq]
    exact Ideal.subset_span rfl
  rw [powerSeriesXIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  have h1 : (PowerSeries.coeff 1 (X : PowerSeries R)) = 0 :=
    (PowerSeries.X_pow_dvd_iff.mp hmem) 1 (by omega)
  rw [PowerSeries.coeff_one_X] at h1
  exact one_ne_zero h1

end Values

section Int

/-- **`FormalSpectrum.IsStalkLimit` is false at every point of `Spf (ℤ⟦X⟧, J)`, for every finitely
generated ideal of definition `J` of `ℤ⟦X⟧`.**

`FormalSpectrum.not_isStalkLimit_powerSeriesX_int`
(`FormalSchemes.StructureSheafStalkPowerSeriesPoint`) is this at `J = (X)`, and it decides every
point there; `FormalSpectrum.exists_isStalkLimit_powerSeriesX_iff_of_isCofinal` carries the
decision to `J`. **No finiteness hypothesis on `J`**: `ℤ⟦X⟧` is Noetherian, so
`FormalSpectrum.fg_powerSeriesIdeal_of_isNoetherianRing` supplies the one the bridge takes. -/
theorem not_isStalkLimit_powerSeriesXCofinal_int {J : Ideal (PowerSeries ℤ)}
    (h : Ideal.IsCofinal (powerSeriesXIdeal ℤ) J) (y : FormalSpectrum J) :
    ¬ IsStalkLimit J y := by
  obtain ⟨x, hx⟩ := exists_isStalkLimit_powerSeriesX_iff_of_isCofinal h
    (fg_powerSeriesIdeal_of_isNoetherianRing J) y
  exact fun hy => not_isStalkLimit_powerSeriesX_int x (hx.mp hy)

/-- **The decision at an ideal of definition of `ℤ⟦X⟧` that is not `(X)`**: `(X) ^ k` for `k ≥ 2`.
It is cofinal with `(X)` by `Ideal.IsCofinal.pow` (`FormalSchemes.CofinalIdeal`) and distinct from
`(X)` by `FormalSpectrum.powerSeriesXIdeal_pow_ne`.

This is the witness that `FormalSpectrum.not_isStalkLimit_powerSeriesXCofinal_int` is not a
statement about `(X)` under another name. The hypothesis `2 ≤ k` is what makes the ideal different;
at `k = 1` the statement is the one already on the tree. -/
theorem not_isStalkLimit_powerSeriesXIdealPow_int {k : ℕ} (hk : 2 ≤ k)
    (y : FormalSpectrum (powerSeriesXIdeal ℤ ^ k)) :
    ¬ IsStalkLimit (powerSeriesXIdeal ℤ ^ k) y :=
  not_isStalkLimit_powerSeriesXCofinal_int (Ideal.IsCofinal.pow _ (by omega)) y

/-- **The sentence this file's prose repair turns on, as a theorem**: there is an ideal of
definition of `ℤ⟦X⟧` **other than** `(X)` at which `FormalSpectrum.IsStalkLimit` is false at every
point. The witness is `(X) ^ 2`.

*Ideal of definition* is the first conjunct and not a hypothesis left to the reader: by the opening
section above, an ideal of `ℤ⟦X⟧` is an ideal of definition for the `(X)`-adic topology exactly
when it is cofinal with `(X)`, so the three conjuncts are the three clauses of the sentence.

The cofinality is also what keeps the statement from being satisfied by an ideal at which there is
nothing to decide. `FormalSpectrum J` is `PrimeSpectrum (ℤ⟦X⟧ ⧸ J)`, so at `J = ⊤` it is empty and
the universal clause holds for want of a point; `⊤ ≠ (X)` as well, so the last two conjuncts on
their own are satisfiable by a witness that decides nothing. `Ideal.IsCofinal (X) ⊤` is false — it
asks for `⊤ ^ n ≤ (X)`, and `⊤ ^ n` is `⊤` at every `n` — so the first conjunct rules that witness
out. Nonemptiness of `FormalSpectrum J` is not stated here and is not needed for that: cofinality
gives `J ^ n ≤ (X)` with `(X)` prime, hence `J ≤ (X)` and `J` proper, but nothing below asks for a
point and this file adds no declaration to supply one.

Without it the claim that anything here is stated away from `(X)` would rest on prose; with it the
two repaired docstrings in `FormalSchemes.StructureSheafStalkPowerSeriesPoint` and
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` assert something the tree proves. It
is the counterpart of `FormalSpectrum.exists_isStalkLimit_powerSeriesX_field`, which records the
same kind of non-vacuity one file down — there by exhibiting a point, here by constraining the
ideal. -/
theorem exists_isCofinal_ne_powerSeriesXIdeal_not_isStalkLimit_int :
    ∃ J : Ideal (PowerSeries ℤ), Ideal.IsCofinal (powerSeriesXIdeal ℤ) J ∧
      J ≠ powerSeriesXIdeal ℤ ∧ ∀ y : FormalSpectrum J, ¬ IsStalkLimit J y :=
  ⟨powerSeriesXIdeal ℤ ^ 2, Ideal.IsCofinal.pow _ two_ne_zero,
    powerSeriesXIdeal_pow_ne le_rfl, not_isStalkLimit_powerSeriesXIdealPow_int le_rfl⟩

end Int

section Field

variable (k : Type u) [Field k]

/-- **`FormalSpectrum.IsStalkLimit` holds at every point of `Spf (k⟦X⟧, J)` for `k` a field and `J`
a finitely generated ideal of definition of `k⟦X⟧`.**

`FormalSpectrum.isStalkLimit_powerSeriesX_field` (`FormalSchemes.StructureSheafStalkPowerSeries`)
is this at `J = (X)`. Together with
`FormalSpectrum.not_isStalkLimit_powerSeriesXCofinal_int` it shows the transport is not vacuous in
either direction: both values of the predicate are attained away from `(X)`. A field is Noetherian,
so there is no finiteness hypothesis here either. -/
theorem isStalkLimit_powerSeriesXCofinal_field {J : Ideal (PowerSeries k)}
    (h : Ideal.IsCofinal (powerSeriesXIdeal k) J) (y : FormalSpectrum J) :
    IsStalkLimit J y := by
  obtain ⟨x, hx⟩ := exists_isStalkLimit_powerSeriesX_iff_of_isCofinal h
    (fg_powerSeriesIdeal_of_isNoetherianRing J) y
  exact hx.mpr (isStalkLimit_powerSeriesX_field k x)

end Field

section DimOne

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.DimensionLEOne R]

/-- **The negative value at every finitely generated ideal of definition, over a Noetherian domain
of dimension at most one with infinitely many nonzero primes.**
`FormalSpectrum.not_isStalkLimit_powerSeriesX_of_infinite_primeIdeals`
(`FormalSchemes.StructureSheafStalkPowerSeriesDedekind`) is this at `J = (X)`, and
`FormalSpectrum.not_isStalkLimit_powerSeriesXCofinal_int` is this at `R = ℤ`, where the hypothesis
on the primes is `FormalSpectrum.infinite_setOf_isPrime_int`.

`FormalSpectrum.not_isStalkLimit_powerSeriesXRingOfIntegers`
(`FormalSchemes.StructureSheafStalkPowerSeriesNumberField`) is the `(X)`-side statement at the ring
of integers of a number field; its transported form is this theorem at that ring and is not
restated, since restating it would cost one more module in this file's import cone and add
nothing. The hypothesis `[IsNoetherianRing R]` is already here, so this statement too carries no
finiteness hypothesis on `J`. -/
theorem not_isStalkLimit_powerSeriesXCofinal_of_infinite_primeIdeals
    (hinf : {P : Ideal R | P.IsPrime ∧ P ≠ ⊥}.Infinite) {J : Ideal (PowerSeries R)}
    (h : Ideal.IsCofinal (powerSeriesXIdeal R) J) (y : FormalSpectrum J) :
    ¬ IsStalkLimit J y := by
  obtain ⟨x, hx⟩ := exists_isStalkLimit_powerSeriesX_iff_of_isCofinal h
    (fg_powerSeriesIdeal_of_isNoetherianRing J) y
  exact fun hy => not_isStalkLimit_powerSeriesX_of_infinite_primeIdeals R hinf x (hx.mp hy)

end DimOne

end FormalSpectrum

end
