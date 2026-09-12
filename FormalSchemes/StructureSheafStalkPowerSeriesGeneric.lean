import FormalSchemes.StructureSheafStalkPowerSeries

set_option linter.style.header false

/-!
# `FormalSpectrum.IsStalkLimit` at a point that is not closed: `(X) ⊆ ℤ⟦X⟧` at the generic point

`FormalSpectrum.IsStalkLimit` — the stalk half of EGA I 10.8 — had three values when this file was
written, and all three were at a point where the colimit over basic opens has nothing to do:
`FormalSpectrum.isStalkLimit_bot` at `I = ⊥`, `FormalSpectrum.isStalkLimit_of_isNilpotent` at every
finitely generated nilpotent ideal of definition, and
`FormalSpectrum.isStalkLimit_powerSeriesX_field` at `(X) ⊆ k⟦X⟧` for `k` a field. **That is no
longer a description of the predicate**: `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint`
(`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`) is positive at the generic point of
a discrete valuation ring, where the colimit does move. The third of the three broke the
nilpotency barrier — `FormalSpectrum.not_isNilpotent_powerSeriesXIdeal` is proved — but it is a
value at the **closed point of a local ring**, reached through
`FormalSpectrum.isStalkLimit_of_isUnit_notMem_pointPrime`, where every `f` with `x ∈ D(f)` is a
unit and no witness is ever produced. `FormalSchemes.StructureSheafStalkPowerSeries` says so in its
own `## What is *not* proved here`.

This file takes the target that file names: `R⟦X⟧` for `R` an integral domain, at the point of
`Spf (R⟦X⟧, (X))` lying over the generic point of `Spec R`, with `R = ℤ` as the case where the
point is not closed. **It does not decide `FormalSpectrum.IsStalkLimit` there, in either
direction.**

## What the point is, and that it is a new one

`FormalSpectrum.powerSeriesXHomeo` makes the space of `Spf (R⟦X⟧, (X))` into `Spec R`, so for `R` a
domain the generic point of `Spec R` names a point `FormalSpectrum.powerSeriesXGenericPoint`. Four
facts about it are proved below rather than asserted:

* `FormalSpectrum.pointPrime_powerSeriesXGenericPoint`: the prime under it is `(X)` itself, so the
  target of the comparison is the `(X)`-adic completion of the localization of `R⟦X⟧` at `(X)`. The
  argument is not the one used over a field, which reads maximality of `(X)` off the residue field:
  `(X)` is **not** maximal here (`FormalSpectrum.not_isMaximal_powerSeriesXIdeal`, proved for every
  `R` that is not a field). It is the transport of `⊥` along
  `FormalSpectrum.powerSeriesXQuotientEquiv` instead.
* `FormalSpectrum.mem_basicOpen_powerSeriesXGenericPoint_iff`: `x ∈ D(f)` is exactly
  `PowerSeries.constantCoeff f ≠ 0`. So the quantifier `∀ f, x ∈ D(f) → …` in both halves of the
  criterion ranges over the power series with nonzero constant term, and over nothing else.
* `FormalSpectrum.exists_notMem_pointPrime_not_isUnit_powerSeriesXGenericPoint`: as soon as `R` is
  not a field there is a non-unit outside that prime, so
  `FormalSpectrum.isStalkLimit_of_isUnit_notMem_pointPrime` — the criterion behind the value over a
  field — **does not apply**. At `R = ℤ` the witness is `PowerSeries.C 2`
  (`FormalSpectrum.C_two_notMem_pointPrime_powerSeriesXIntGenericPoint`,
  `FormalSpectrum.not_isUnit_C_two_powerSeries`). This is the check that this row is not the
  previous one.
* `FormalSpectrum.not_isClosed_powerSeriesXGenericPoint`: the point is **not closed**, again as
  soon as `R` is not a field. Over a field there is no such point, so this is the first target of
  its kind for the predicate.

The filtration does not collapse on the local ring either:
`FormalSpectrum.pow_pointIdeal_powerSeriesXGenericPoint_ne_bot` says no power of the ideal of
definition of the stalk's local ring is `⊥`, which is the statement one level down from
`FormalSpectrum.pow_powerSeriesXIdeal_ne_bot` and is where the levels of the stalk tower live.

## What is landed about the question itself

`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff` is the sheaf-free criterion at this
point with the basic-open quantifier replaced by the condition on constant terms. It is
`FormalSpectrum.isStalkLimit_powerSeriesX_iff` (which already carries no topology and no
`IsAdicRing`) with that one substitution, and **nothing more is claimed for it**; see the
implementation notes for exactly which packaging is still in the statement.

Three general statements say where the difficulty is **not**:

* `FormalSpectrum.exists_awayToAtPrime_eq`: **before completing, the surjectivity is free.** Every
  element of `Localization.AtPrime (pointPrime I x)` is `FormalSpectrum.awayToAtPrime` of an
  element of some `Localization.Away f` with `x ∈ D(f)` — at every ideal of definition, every ring
  and every point, with no hypothesis. It is the localization written as what it is, a filtered
  union.
* `FormalSpectrum.exists_mk_awayToAtPrime_eq`: the same modulo any power of
  `FormalSpectrum.pointIdeal`, hence at **every level of the stalk tower**, those levels being
  `Localization.AtPrime (pointPrime I x) ⧸ pointIdeal I x ^ (n + 1)` by
  `FormalSpectrum.stalkTowerLevelEquiv`.
* `FormalSpectrum.exists_awayToAtPrimeLevel_eq`: the same statement about the map the tower
  actually compares with, `FormalSpectrum.awayToAtPrimeLevel`. The two agree definitionally, and
  this is the declaration that says so, so that "the surjectivity half cannot fail at any one
  level" is carried by a theorem about the level map rather than by a step left to the reader.

So the surjectivity half of `FormalSpectrum.IsStalkLimit` cannot fail at any single level, and
cannot fail before completion: whatever fails, fails in the passage to the limit, where one `f`
must serve every level at once. That is exactly the non-uniformity
`FormalSchemes.StructureSheafStalkComparison` records in prose, and these two statements are the
first time it has been isolated as a theorem rather than described.

## What is *not* proved here

**Nothing below decides `FormalSpectrum.IsStalkLimit` at `(X) ⊆ ℤ⟦X⟧` at the generic point**, in
either direction: the surjectivity half is attempted here and does **not** close, and no
counterexample is constructed below. It is decided elsewhere, and negatively:
`FormalSpectrum.not_isStalkLimit_powerSeriesXIntGenericPoint`
(`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`) refutes it, using the two ring
identifications the paragraph below asks for. **That does not make the predicate false in
general** — the positive values stand, and one of them
(`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint`) is at the generic point of a discrete
valuation ring, so the predicate is not negative wherever the colimit moves — and nothing in this
file is evidence in either direction.

**The two general statements above are not evidence that the half holds.** They say the obstruction
is concentrated in the limit; they say nothing about whether it is surmountable there. A reader
must not read `FormalSpectrum.exists_mk_awayToAtPrime_eq` as levelwise progress towards the
surjectivity half — the half quantifies over elements of the completion, and no element of the
completion is constructed below.

**Where the attempt below stopped, and what it took.** The expected counterexample is the one
`FormalSchemes.StructureSheafStalkPowerSeries` records: over `ℤ`, an element of the target whose
coefficients have denominators involving infinitely many primes lies in no single
`FormalSpectrum.awayCompletion (X) f`. Carrying it out needs two ring identifications that are
**not proved below**: that the target is `ℚ⟦X⟧`, and that `FormalSpectrum.awayCompletion (X) f` is
`ℤ[1/m]⟦X⟧` for `m` the constant term of `f`. Both are now on the tree, as
`FormalSpectrum.atPrimeCompletionEquivFractionPowerSeries` and
`FormalSpectrum.awayCompletionEquivPowerSeriesAway` in
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, which is where the counterexample is
assembled. **No declaration below asserts either of them.**

**Nothing under a Noetherian hypothesis.** `Ideal.FG` of the ideal of definition is the only
finiteness assumption anywhere below, and it is `FormalSpectrum.fg_powerSeriesXIdeal`. `ℤ⟦X⟧` is
Noetherian and no statement below uses it.

**Nothing about the injectivity half.** It is not attempted below, at this point or any other. It
is settled elsewhere, and positively:
`FormalSpectrum.exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint`
(`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`) proves it at the generic point of
every domain, which is what makes the refutation named above sharp. No declaration below is
evidence for it.

**No comparison with `Spec`.** `FormalSchemes.SpfDiscrete` is not imported — measured at **42**
modules besides itself on top of this file's closure, 43 including it — and nothing here needs it.

## Implementation notes

`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff` replaces the two occurrences of
`x ∈ FormalSpectrum.basicOpen (X) f` by `PowerSeries.constantCoeff f ≠ 0` and **does not** remove
the rest of the packaging: `FormalSpectrum.awayCompletion`,
`FormalSpectrum.awayToAtPrimeCompletion`, `FormalSpectrum.awayCompletionRestrict`,
`FormalSpectrum.pointIdeal` and `FormalSpectrum.pointPrime` all still occur, and so does one
`FormalSpectrum.basicOpen ≤ FormalSpectrum.basicOpen`, which is the containment of basic opens the
injectivity half restricts along. Two of those are unavoidable — the comparison map is what the
question is about — and `FormalSpectrum.pointPrime` appears inside a **type**, so trading it for
`(X)` along `FormalSpectrum.pointPrime_powerSeriesXGenericPoint` is a transport and not a rewrite;
the equation is supplied separately instead. `FormalSpectrum.awayCompletion` is an `abbrev` for
`AdicCompletion (I.map (algebraMap R (Localization.Away f))) (Localization.Away f)`, so the
statement is already in terms of the `X`-adic filtration on localizations of `R⟦X⟧`, whatever it
prints as.

`FormalSpectrum.exists_awayToAtPrime_eq` and `FormalSpectrum.exists_mk_awayToAtPrime_eq` mention no
power series and would sit as naturally in `FormalSchemes.StructureSheafStalkComparison`, whose
`## What is *not* proved here` is what they sharpen and whose reverse closure is **11** of the
project's 561 modules (forward closure 36 with itself, against this file's 51). They are kept here
anyway, on two grounds: each has exactly one consumer, both in this file, which is the disposition
`FormalSchemes.StructureSheafStalkNilpotent` and `FormalSchemes.StructureSheafStalkPowerSeries`
both recorded for a general statement with a single consumer; and moving them would edit a file
this row is scoped not to touch. **The move was re-costed when the level bridge was added and
declined**, not on the closure numbers but because it is blocked:
`FormalSpectrum.exists_awayToAtPrime_eq` consumes
`FormalSpectrum.mem_basicOpen_of_notMem_pointPrime`, which lives in
`FormalSchemes.StructureSheafStalkBot` — *downstream* of
`FormalSchemes.StructureSheafStalkComparison` — so the move would have to drag one of that file's
five general-`I` lemmas upstream as well, or replace a named citation by the definitional
coincidence that the two statements are the same proposition. Neither is worth it, and the three
statements stay together here.

## Placement

Over `FormalSchemes.StructureSheafStalkPowerSeries`: forward closure **50** project modules
besides itself (51 counted with itself), reverse closure **6** —
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` and the five modules above it. It adds
no Mathlib import.

## Main definitions and results

* `FormalSpectrum.exists_awayToAtPrime_eq`, `FormalSpectrum.exists_mk_awayToAtPrime_eq`,
  `FormalSpectrum.exists_awayToAtPrimeLevel_eq`: the uncompleted surjectivity, the same modulo any
  power of the ideal of definition, and the same through the stalk tower's own level map, at every
  ideal of definition and point.
* `FormalSpectrum.powerSeriesXGenericPoint`: the point of `Spf (R⟦X⟧, (X))` over the generic point
  of `Spec R`, for `R` a domain.
* `FormalSpectrum.pointPrime_powerSeriesXGenericPoint`,
  `FormalSpectrum.mem_basicOpen_powerSeriesXGenericPoint_iff`: the prime under it is `(X)`, and its
  basic opens are the constant terms that are nonzero.
* `FormalSpectrum.not_isMaximal_powerSeriesXIdeal`: `(X)` is maximal only over a field, so the
  route used there is unavailable.
* `FormalSpectrum.not_isClosed_powerSeriesXGenericPoint`,
  `FormalSpectrum.exists_notMem_pointPrime_not_isUnit_powerSeriesXGenericPoint`: over a ring that
  is not a field the point is not closed and the criterion behind the value over a field does not
  apply.
* `FormalSpectrum.pow_pointIdeal_powerSeriesXGenericPoint_ne_bot`: the filtration does not collapse
  on the stalk's local ring either.
* `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff`: **the criterion at this point**, with
  the basic-open quantifier written out.
* `FormalSpectrum.not_isUnit_C_two_powerSeries`,
  `FormalSpectrum.C_two_notMem_pointPrime_powerSeriesXIntGenericPoint`,
  `FormalSpectrum.not_isClosed_powerSeriesXIntGenericPoint`,
  `FormalSpectrum.not_isNilpotent_powerSeriesXIdealInt`: the four checks at `R = ℤ`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX).
-/

noncomputable section

universe u

open PowerSeries

namespace FormalSpectrum

/-! ### Before completing, the surjectivity is free -/

section Uncompleted

variable {R : Type u} [CommRing R] (I : Ideal R) (x : FormalSpectrum I)

/-- **Every element of the local ring at a point of `Spf R` comes from a basic open through it.**
`Localization.AtPrime (pointPrime I x)` is a localization at a prime complement, so each of its
elements is `IsLocalization.mk' r s` with `s ∉ pointPrime I x`; then `x ∈ D(s)` by
`FormalSpectrum.mem_basicOpen_of_notMem_pointPrime`, and the corresponding element of
`Localization.Away s` maps to it because `FormalSpectrum.awayToAtPrime` is a map under `R` and the
image of `s` is a unit downstairs.

**This is the surjectivity half of `FormalSpectrum.IsStalkLimit` before completing**, and it holds
at every ideal of definition, every commutative ring and every point, with no hypothesis. The
witness `f` depends on the element, which is the whole point: the surjectivity half asks for one
`f` serving a compatible sequence, and this says nothing about that. -/
theorem exists_awayToAtPrime_eq (c : Localization.AtPrime (pointPrime I x)) :
    ∃ (f : R) (hf : x ∈ basicOpen I f) (a : Localization.Away f),
      awayToAtPrime I x hf a = c := by
  obtain ⟨⟨r, s, hs⟩, hrs⟩ := IsLocalization.mk'_surjective (pointPrime I x).primeCompl c
  have hf : x ∈ basicOpen I s := mem_basicOpen_of_notMem_pointPrime I x hs
  refine ⟨s, hf, IsLocalization.mk' (Localization.Away s) r ⟨s, Submonoid.mem_powers s⟩, ?_⟩
  have hu : IsUnit (algebraMap R (Localization.AtPrime (pointPrime I x)) s) :=
    isUnit_algebraMap_atPrime_of_mem_basicOpen I x hf
  refine hu.mul_left_cancel ?_
  have h1 : algebraMap R (Localization.Away s) s *
      IsLocalization.mk' (Localization.Away s) r ⟨s, Submonoid.mem_powers s⟩ =
      algebraMap R (Localization.Away s) r :=
    IsLocalization.mk'_spec' (Localization.Away s) r ⟨s, Submonoid.mem_powers s⟩
  calc algebraMap R (Localization.AtPrime (pointPrime I x)) s *
        awayToAtPrime I x hf (IsLocalization.mk' (Localization.Away s) r
          ⟨s, Submonoid.mem_powers s⟩)
      = awayToAtPrime I x hf (algebraMap R (Localization.Away s) s *
          IsLocalization.mk' (Localization.Away s) r ⟨s, Submonoid.mem_powers s⟩) := by
        rw [map_mul, awayToAtPrime_algebraMap]
    _ = algebraMap R (Localization.AtPrime (pointPrime I x)) r := by
        rw [h1, awayToAtPrime_algebraMap]
    _ = algebraMap R (Localization.AtPrime (pointPrime I x)) s * c := by
        rw [← hrs]
        exact (IsLocalization.mk'_spec' (Localization.AtPrime (pointPrime I x)) r ⟨s, hs⟩).symm

/-- **The same at every level of the stalk tower.** `FormalSpectrum.stalkTowerLevelEquiv`
identifies level `n` with `Localization.AtPrime (pointPrime I x) ⧸ pointIdeal I x ^ (n + 1)`, and
this says every element of any such quotient — indeed of the quotient by any power — is hit from
some basic open through the point. `Ideal.Quotient.mk_surjective` lifts, and
`FormalSpectrum.exists_awayToAtPrime_eq` does the rest.

**So the surjectivity half cannot fail at any one level.** Whatever fails in it fails in the
passage to the limit, where a single `f` must serve every level at once; that non-uniformity is the
obstruction `FormalSchemes.StructureSheafStalkComparison` records, and nothing here surmounts it. -/
theorem exists_mk_awayToAtPrime_eq (n : ℕ)
    (c : Localization.AtPrime (pointPrime I x) ⧸ pointIdeal I x ^ n) :
    ∃ (f : R) (hf : x ∈ basicOpen I f) (a : Localization.Away f),
      Ideal.Quotient.mk (pointIdeal I x ^ n) (awayToAtPrime I x hf a) = c := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨f, hf, a, ha⟩ := exists_awayToAtPrime_eq I x b
  exact ⟨f, hf, a, by rw [ha]⟩

/-- **The same at every level of the stalk tower, through the tower's own comparison map.**
`FormalSpectrum.exists_mk_awayToAtPrime_eq` is stated about `Ideal.Quotient.mk` composed with
`FormalSpectrum.awayToAtPrime`; the map the stalk tower compares with at level `n` is
`FormalSpectrum.awayToAtPrimeLevel`, which is `Ideal.quotientMap` of that same ring map. The two
agree definitionally, and this is the declaration that says so — so that the reading "the
surjectivity half cannot fail at any one level" is carried by a theorem about the level map itself
and not by a step left to the reader.

The indexing is `FormalSpectrum.stalkTowerLevelEquiv`'s: level `n` is the quotient by the
`(n + 1)`-st power. -/
theorem exists_awayToAtPrimeLevel_eq (n : ℕ)
    (c : Localization.AtPrime (pointPrime I x) ⧸ pointIdeal I x ^ (n + 1)) :
    ∃ (f : R) (hf : x ∈ basicOpen I f)
      (a : Localization.Away f ⧸ (I.map (algebraMap R (Localization.Away f))) ^ (n + 1)),
      awayToAtPrimeLevel I x hf n a = c := by
  obtain ⟨f, hf, a, ha⟩ := exists_mk_awayToAtPrime_eq I x (n + 1) c
  exact ⟨f, hf, Ideal.Quotient.mk _ a, ha⟩

end Uncompleted

/-! ### The generic point of `Spf (R⟦X⟧, (X))` for a domain `R` -/

section Generic

variable (R : Type u) [CommRing R] [IsDomain R]

/-- **The point of `Spf (R⟦X⟧, (X))` over the generic point of `Spec R`.** The space is `Spec R` by
`FormalSpectrum.powerSeriesXHomeo`, so `⊥` names a point as soon as `⊥` is prime, i.e. as soon as
`R` is a domain. Over a field this is the unique point and it is closed; over `ℤ` it is one point
among infinitely many and it is not closed
(`FormalSpectrum.not_isClosed_powerSeriesXGenericPoint`). -/
def powerSeriesXGenericPoint : FormalSpectrum (powerSeriesXIdeal R) :=
  (powerSeriesXHomeo R).symm ⟨⊥, Ideal.isPrime_bot⟩

/-- The prime of `R⟦X⟧ ⧸ (X)` at the generic point is `⊥`: it is the contraction of `⊥` along the
injection `FormalSpectrum.powerSeriesXQuotientEquiv`. -/
theorem asIdeal_powerSeriesXGenericPoint : (powerSeriesXGenericPoint R).asIdeal = ⊥ := by
  rw [powerSeriesXGenericPoint, powerSeriesXHomeo]
  exact Ideal.comap_bot_of_injective _ (powerSeriesXQuotientEquiv R).injective

omit [IsDomain R] in
/-- **`(X) ⊆ R⟦X⟧` is not maximal unless `R` is a field.** `R⟦X⟧ ⧸ (X)` is `R`
(`FormalSpectrum.powerSeriesXQuotientEquiv`), and an ideal is maximal exactly when the quotient by
it is a field.

This is why `FormalSpectrum.pointPrime_powerSeriesXIdeal`'s argument does not run at the generic
point: over a field it identifies the prime under a point with `(X)` from maximality, and over `ℤ`
there is no maximality to use. -/
theorem not_isMaximal_powerSeriesXIdeal (hR : ¬ IsField R) : ¬ (powerSeriesXIdeal R).IsMaximal := by
  intro hmax
  refine hR ?_
  have h : IsField (PowerSeries R ⧸ powerSeriesXIdeal R) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax
  exact (powerSeriesXQuotientEquiv R).symm.toMulEquiv.isField h

/-- **The prime of `R⟦X⟧` under the generic point is the ideal of definition itself.** So the
target of the comparison at this point — `AdicCompletion (pointIdeal (X) x) (Localization.AtPrime
…)` — is the `(X)`-adic completion of the localization of `R⟦X⟧` at `(X)`.

The proof is *not* `FormalSpectrum.pointPrime_powerSeriesXIdeal`'s: that one uses maximality of
`(X)`, which fails here — over `ℤ` the ideal `(2, X)` is strictly larger. It is the contraction of
`⊥` along `Ideal.Quotient.mk`, which is `Ideal.mk_ker`. -/
theorem pointPrime_powerSeriesXGenericPoint :
    pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) = powerSeriesXIdeal R := by
  have hdef : pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) =
      ((powerSeriesXGenericPoint R).asIdeal).comap (Ideal.Quotient.mk (powerSeriesXIdeal R)) := rfl
  rw [hdef, asIdeal_powerSeriesXGenericPoint, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

/-- **The basic opens through the generic point are the nonzero constant terms.** So the quantifier
`∀ f, x ∈ D(f) → …` in both halves of `FormalSpectrum.isStalkLimit_powerSeriesX_iff` ranges over
the power series with `PowerSeries.constantCoeff f ≠ 0` and over nothing else — over `ℤ`, over the
basic opens `D(m)` of `Spec ℤ` for `m ≠ 0`. -/
theorem mem_basicOpen_powerSeriesXGenericPoint_iff (f : PowerSeries R) :
    powerSeriesXGenericPoint R ∈ basicOpen (powerSeriesXIdeal R) f ↔ constantCoeff f ≠ 0 := by
  rw [mem_basicOpen_powerSeriesX_iff, pointPrime_powerSeriesXGenericPoint,
    powerSeriesXIdeal_eq_ker, RingHom.mem_ker, constantCoeff_C]

/-- The generic point sits over `⊥` under `FormalSpectrum.powerSeriesXHomeo`, by construction. -/
theorem powerSeriesXHomeo_powerSeriesXGenericPoint :
    powerSeriesXHomeo R (powerSeriesXGenericPoint R) = ⟨⊥, Ideal.isPrime_bot⟩ :=
  (powerSeriesXHomeo R).apply_symm_apply _

/-- **The generic point is not closed**, as soon as `R` is not a field. Transported along
`FormalSpectrum.powerSeriesXHomeo` the singleton is `{⊥} ⊆ Spec R`, whose closedness is maximality
of `⊥` (`PrimeSpectrum.isClosed_singleton_iff_isMaximal`), which is `R` being a field
(`Ring.isField_iff_maximal_bot`).

**This is what makes the point a new target for `FormalSpectrum.IsStalkLimit`.** The three values
that predate this file are at points around which the basic opens are not a genuinely filtered
system: at `⊥` and at a nilpotent ideal of definition the two completions collapse, and at
`(X) ⊆ k⟦X⟧` the point is the closed point of a local ring. The predicate is now decided at this
kind of point in both directions — negatively at `(X) ⊆ ℤ⟦X⟧` and positively at the generic point
of a discrete valuation ring — so a value here is not settled by the point being of this kind. -/
theorem not_isClosed_powerSeriesXGenericPoint (hR : ¬ IsField R) :
    ¬ IsClosed ({powerSeriesXGenericPoint R} : Set (FormalSpectrum (powerSeriesXIdeal R))) := by
  intro hc
  refine hR ?_
  rw [Ring.isField_iff_maximal_bot]
  have h := (powerSeriesXHomeo R).isClosed_image (s := {powerSeriesXGenericPoint R})
  rw [Set.image_singleton, powerSeriesXHomeo_powerSeriesXGenericPoint] at h
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal ⟨⊥, Ideal.isPrime_bot⟩).mp (h.mpr hc)

/-- The structural map of `R⟦X⟧` into the local ring at the generic point is injective: `R⟦X⟧` is a
domain and the prime complement misses `0`. Used to see that the filtration on that local ring does
not collapse. -/
theorem injective_algebraMap_atPrime_powerSeriesXGenericPoint :
    Function.Injective (algebraMap (PowerSeries R)
      (Localization.AtPrime
        (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)))) := by
  refine IsLocalization.injective
    (M := (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)).primeCompl) _
    (fun s hs => ?_)
  refine mem_nonZeroDivisors_of_ne_zero (fun h => hs ?_)
  exact h ▸ (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)).zero_mem

/-- **No power of the ideal of definition of the stalk's local ring is `⊥`.** This is
`FormalSpectrum.pow_powerSeriesXIdeal_ne_bot` one level down, at the ring where the levels of the
stalk tower actually live (`FormalSpectrum.stalkTowerLevelEquiv`): the image of `X ^ n` is nonzero
because `R⟦X⟧` is a domain and the localization map is injective.

So the degeneracy that makes `FormalSchemes.StructureSheafStalkNilpotent`'s argument run — the
tower being constant from some level on — is absent here for the same reason at both levels. It
does **not** follow that the tower's levels are pairwise distinct, and that is not proved. -/
theorem pow_pointIdeal_powerSeriesXGenericPoint_ne_bot (n : ℕ) :
    pointIdeal (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) ^ n ≠ ⊥ := by
  intro h
  have hx : (algebraMap (PowerSeries R) (Localization.AtPrime
      (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)))) ((X : PowerSeries R) ^ n) ∈
      pointIdeal (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) ^ n := by
    have hmem : (X : PowerSeries R) ^ n ∈ Ideal.span {(X : PowerSeries R)} ^ n := by
      rw [Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    rw [pointIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hmem
  rw [h, Ideal.mem_bot] at hx
  have hxz : (X : PowerSeries R) ^ n = 0 :=
    injective_algebraMap_atPrime_powerSeriesXGenericPoint R (by rw [hx, map_zero])
  have hone : (PowerSeries.coeff n) ((X : PowerSeries R) ^ n) = 1 := by simp
  rw [hxz] at hone
  simp at hone

/-- **The criterion behind the value over a field does not apply at the generic point**, as soon as
`R` is not a field: `FormalSpectrum.isStalkLimit_of_isUnit_notMem_pointPrime` asks that everything
outside the prime under the point be a unit, and a non-unit `a ≠ 0` of `R` gives the constant power
series `PowerSeries.C a`, which is outside `(X)` and is not a unit because
`PowerSeries.constantCoeff` would carry a unit to one.

This is the check that this target is not `FormalSpectrum.isStalkLimit_powerSeriesX_field`'s in
disguise. It refutes the applicability of one criterion and **says nothing about
`FormalSpectrum.IsStalkLimit` itself**. -/
theorem exists_notMem_pointPrime_not_isUnit_powerSeriesXGenericPoint (hR : ¬ IsField R) :
    ∃ g : PowerSeries R,
      g ∉ pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) ∧ ¬ IsUnit g := by
  obtain ⟨a, ha0, hau⟩ := Ring.exists_not_isUnit_of_not_isField hR
  refine ⟨PowerSeries.C a, ?_, fun h => hau ?_⟩
  · rw [pointPrime_powerSeriesXGenericPoint, powerSeriesXIdeal_eq_ker, RingHom.mem_ker,
      constantCoeff_C]
    exact ha0
  · have hu : IsUnit ((constantCoeff (R := R)) (PowerSeries.C a)) := h.map _
    rwa [constantCoeff_C] at hu

/-- **The sheaf-free criterion at the generic point, with the basic-open quantifier written out.**
`FormalSpectrum.isStalkLimit_powerSeriesX_iff` already carries no topology and no `IsAdicRing`;
this is that statement at `FormalSpectrum.powerSeriesXGenericPoint`, with `x ∈ D(f)` replaced by
`PowerSeries.constantCoeff f ≠ 0` on both halves by
`FormalSpectrum.mem_basicOpen_powerSeriesXGenericPoint_iff`. Over `ℤ` the two halves therefore
quantify over the basic opens `D(m)`, `m ≠ 0`, of `Spec ℤ`.

**What is still in it, and is not claimed to be gone.** The comparison maps
`FormalSpectrum.awayToAtPrimeCompletion` and `FormalSpectrum.awayCompletionRestrict` remain — they
are what the question is about — as do `FormalSpectrum.pointIdeal` and `FormalSpectrum.pointPrime`,
which occur inside a type and can therefore only be traded along
`FormalSpectrum.pointPrime_powerSeriesXGenericPoint` by transport, and one containment of basic
opens in the injectivity half. `FormalSpectrum.awayCompletion` is an `abbrev` for an
`AdicCompletion` of a localization, so no unfolding is needed to read the source as a completed
localization of `R⟦X⟧`.

**Neither side is decided below**, that is, nowhere in this file. Both are decided downstream, in
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, and so is the conjunction: the
injectivity half holds at the generic point of every domain, the surjectivity half is shown there
to be equivalent to a condition on `R` alone which fails at `R = ℤ` and holds at a discrete
valuation ring, and the two compose into an `↔` between `FormalSpectrum.IsStalkLimit` at this point
and that condition — a cardinality, once `R` is a unique factorisation domain. None of that is
available here; see that module's docstring. -/
theorem isStalkLimit_powerSeriesXGenericPoint_iff :
    IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) ↔
      (∀ (f : PowerSeries R) (hf : constantCoeff f ≠ 0)
          (a : awayCompletion (powerSeriesXIdeal R) f),
          awayToAtPrimeCompletion (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)
              (fg_powerSeriesXIdeal R)
              ((mem_basicOpen_powerSeriesXGenericPoint_iff R f).mpr hf) a = 0 →
            ∃ e, ∃ (_ : constantCoeff e ≠ 0)
              (hle : basicOpen (powerSeriesXIdeal R) e ≤ basicOpen (powerSeriesXIdeal R) f),
              awayCompletionRestrict (powerSeriesXIdeal R) f e (fg_powerSeriesXIdeal R) hle a = 0) ∧
        ∀ b : AdicCompletion (pointIdeal (powerSeriesXIdeal R) (powerSeriesXGenericPoint R))
            (Localization.AtPrime
              (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R))),
          ∃ f, ∃ (hf : constantCoeff f ≠ 0),
            ∃ a, awayToAtPrimeCompletion (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)
              (fg_powerSeriesXIdeal R)
              ((mem_basicOpen_powerSeriesXGenericPoint_iff R f).mpr hf) a = b := by
  rw [isStalkLimit_powerSeriesX_iff]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun f hf a ha => ?_, fun b => ?_⟩
    · obtain ⟨e, he, hle, hres⟩ := hinj f _ a ha
      exact ⟨e, (mem_basicOpen_powerSeriesXGenericPoint_iff R e).mp he, hle, hres⟩
    · obtain ⟨f, hf, a, ha⟩ := hsurj b
      exact ⟨f, (mem_basicOpen_powerSeriesXGenericPoint_iff R f).mp hf, a, ha⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun f hf a ha => ?_, fun b => ?_⟩
    · obtain ⟨e, he, hle, hres⟩ :=
        hinj f ((mem_basicOpen_powerSeriesXGenericPoint_iff R f).mp hf) a ha
      exact ⟨e, (mem_basicOpen_powerSeriesXGenericPoint_iff R e).mpr he, hle, hres⟩
    · obtain ⟨f, hf, a, ha⟩ := hsurj b
      exact ⟨f, (mem_basicOpen_powerSeriesXGenericPoint_iff R f).mpr hf, a, ha⟩

/-- **The uncompleted surjectivity at the generic point, with the quantifier written out.**
`FormalSpectrum.exists_awayToAtPrime_eq` at this point: every element of the local ring of `R⟦X⟧`
at `(X)` is the image of an element of `Localization.Away f` for some `f` with nonzero constant
term. **It is not the surjectivity half**, which quantifies over the completion. -/
theorem exists_awayToAtPrime_eq_powerSeriesXGenericPoint
    (c : Localization.AtPrime
      (pointPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R))) :
    ∃ (f : PowerSeries R) (hf : constantCoeff f ≠ 0) (a : Localization.Away f),
      awayToAtPrime (powerSeriesXIdeal R) (powerSeriesXGenericPoint R)
        ((mem_basicOpen_powerSeriesXGenericPoint_iff R f).mpr hf) a = c := by
  obtain ⟨f, hf, a, ha⟩ :=
    exists_awayToAtPrime_eq (powerSeriesXIdeal R) (powerSeriesXGenericPoint R) c
  exact ⟨f, (mem_basicOpen_powerSeriesXGenericPoint_iff R f).mp hf, a, ha⟩

end Generic

/-! ### The four checks at `R = ℤ` -/

section Int

/-- `PowerSeries.C 2` is not a unit of `ℤ⟦X⟧`: `PowerSeries.constantCoeff` would carry a unit to a
unit of `ℤ`, and `2` is neither `1` nor `-1`. -/
theorem not_isUnit_C_two_powerSeries : ¬ IsUnit (PowerSeries.C (2 : ℤ)) := by
  intro h
  have h2 : IsUnit ((constantCoeff (R := ℤ)) (PowerSeries.C (2 : ℤ))) := h.map _
  rw [constantCoeff_C, Int.isUnit_iff] at h2
  omega

/-- `PowerSeries.C 2` is outside the prime under the generic point of `Spf (ℤ⟦X⟧, (X))`, that prime
being `(X)`. With `FormalSpectrum.not_isUnit_C_two_powerSeries` this is the promised term-level
witness that `FormalSpectrum.isStalkLimit_of_isUnit_notMem_pointPrime` does not apply here. -/
theorem C_two_notMem_pointPrime_powerSeriesXIntGenericPoint :
    (PowerSeries.C (2 : ℤ)) ∉
      pointPrime (powerSeriesXIdeal ℤ) (powerSeriesXGenericPoint ℤ) := by
  rw [pointPrime_powerSeriesXGenericPoint, powerSeriesXIdeal_eq_ker, RingHom.mem_ker,
    constantCoeff_C]
  omega

/-- The generic point of `Spf (ℤ⟦X⟧, (X))` is not closed, `ℤ` not being a field. -/
theorem not_isClosed_powerSeriesXIntGenericPoint :
    ¬ IsClosed ({powerSeriesXGenericPoint ℤ} :
      Set (FormalSpectrum (powerSeriesXIdeal ℤ))) :=
  not_isClosed_powerSeriesXGenericPoint ℤ Int.not_isField

/-- `(X) ⊆ ℤ⟦X⟧` is not nilpotent: `FormalSpectrum.not_isNilpotent_powerSeriesXIdeal` at `R = ℤ`,
recorded to check that the instantiation transfers and that this target is still outside the regime
of `FormalSpectrum.isStalkLimit_bot` and `FormalSpectrum.isStalkLimit_of_isNilpotent`. -/
theorem not_isNilpotent_powerSeriesXIdealInt : ¬ IsNilpotent (powerSeriesXIdeal ℤ) :=
  not_isNilpotent_powerSeriesXIdeal ℤ

end Int

end FormalSpectrum
