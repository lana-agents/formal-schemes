import FormalSchemes.StructureSheafStalkPowerSeriesCounterexample
import Mathlib.Order.Filter.Germ.Basic

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

* `FormalSpectrum.not_hasBoundedDenominators_of_primes` asks for a family of primes that **no**
  single `m ≠ 0` is divisible by. In an ultrapower that hypothesis is unsatisfiable, and
  `FormalSpectrum.exists_forall_dvd_intUltrapower` is exactly the statement that it is: *every*
  countable family of nonzero elements, primes or not, is divisible into a single element.
* `FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated` and the classification
  `FormalSpectrum.hasBoundedDenominators_iff_finite_primes` both assume
  `[UniqueFactorizationMonoid R]`, and `FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower`
  says the ultrapower does not satisfy it — so both are inapplicable by a theorem and not merely by
  an instance nobody has supplied.

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
  product that clears everything.
* `FormalSpectrum.not_exists_denominator_intUltrapower`,
  `FormalSpectrum.not_exists_forall_dvd_pow_intUltrapower`,
  `FormalSpectrum.not_exists_isField_away_intUltrapower`: **the other three spellings of the
  collapse fail at the ultrapower too**, each refuted on the right-hand side its own `↔` states.
* `FormalSpectrum.hasBoundedDenominators_and_not_exists_surjective_intUltrapower`,
  `FormalSpectrum.hasBoundedDenominators_and_no_collapse_intUltrapower`,
  `FormalSpectrum.not_forall_hasBoundedDenominators_imp_exists_surjective`: **the countability
  hypothesis of the collapse is needed**, in each of its four spellings, stated at the ultrapower
  and as the refutation of the quantified implication.
* `FormalSpectrum.not_countable_intUltrapower`,
  `FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower`,
  `FormalSpectrum.not_isNoetherianRing_intUltrapower`: **the ultrapower is uncountable, is not a
  unique factorisation domain and is not Noetherian** — each from the two halves above, with no
  factorisation theory, no cardinal arithmetic and no model theory.
* `FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_intUltrapower`,
  `FormalSpectrum.isStalkLimit_and_not_exists_surjective_intUltrapower`: **the geometric value**,
  and that no single localization explains it.

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

**The ring's three negative properties are proved; its factorisation theory is not.** That
`FormalSpectrum.IntUltrapower φ` is uncountable, is not a unique factorisation domain and is not
Noetherian are the section *What the ring is not*, and each is read off the two halves above rather
than developed. That the germs of `2, 3, 5, …` are prime in it is also true and is **not proved
below**; nothing here needs it. No irreducible element is exhibited, no prime of the ring is named,
no prime is counted, and no cardinal is computed — `FormalSpectrum.not_countable_intUltrapower` is
a negation of `Countable` and supplies no lower bound.

In particular the paragraph above about the refuting criteria still argues from their
**hypotheses** and not from any factorisation theory: one asks for a family no element is divisible
by, which `FormalSpectrum.exists_forall_dvd_intUltrapower` refutes outright, and the other asks for
unique factorisation, which `FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower` now
refutes as a theorem rather than leaving unavailable.

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
line over the 559 modules under `FormalSchemes/` (a module is not counted in its own closure; the
aggregator at the repository root is outside the walk).

`FormalSchemes.StructureSheafStalkPowerSeriesDedekind` and
`FormalSchemes.StructureSheafStalkPowerSeriesLocal` are **not** imported: their refuting criteria
are the ones this file argues do not apply, and importing them would be four modules for
statements that are only discussed.

**This leaf adds exactly one module to the project's Mathlib closure**,
`Mathlib/Order/Filter/Germ/Basic.lean`, measured by walking `import` and `public import` over
Mathlib's sources from every `import Mathlib…` line under `FormalSchemes/`: 2726 modules at base
and 2727 at head. `Mathlib/Order/Filter/Ultrafilter/Basic.lean` (for `Filter.hyperfilter` and
`Ultrafilter.eventually_or`) and `Mathlib/Data/Nat/Prime/Infinite.lean` (for
`Nat.exists_infinite_primes`) are already in it and are reached through the import above.
`Mathlib/Order/Filter/FilterProduct.lean`, the ultraproduct file, is **not** imported: it supplies
the field structure of an ultrapower of a field, and neither half below needs it.

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

/-- **A nonzero germ is nonzero on a set of the ultrafilter.** This is the first of the two places
where the filter has to be an ultrafilter: `Ultrafilter.eventually_not` turns the *failure*
of eventual vanishing into eventual non-vanishing, which is false at a general filter. -/
theorem eventually_ne_zero_intUltrapower {f : ℕ → ℤ} (hf : (f : IntUltrapower φ) ≠ 0) :
    ∀ᶠ i in (φ : Filter ℕ), f i ≠ 0 :=
  Ultrafilter.eventually_not.mpr fun h => hf ((coe_eq_zero_iff_intUltrapower φ f).mpr h)

/-- **The ultrapower has no zero divisors**, which is the second and last place the ultrafilter is
used for its own sake: `Ultrafilter.eventually_or` splits *eventually one of the two factors
vanishes* into *one of the two vanishes eventually*. Over a filter that is not an ultrafilter the
germ ring has zero divisors and nothing in this file survives. -/
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

`FormalSpectrum.hasBoundedDenominators_iff_finite_primes` is **not** on the list and is not
touched: it assumes `[UniqueFactorizationMonoid R]` rather than `[Countable (FractionRing R)]`,
and `FormalSpectrum.not_uniqueFactorizationMonoid_intUltrapower` below says the ultrapower has
nothing to tell it. -/
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
`FormalSpectrum.not_hasBoundedDenominators_of_primes_not_associated` and
`FormalSpectrum.hasBoundedDenominators_iff_finite_primes` are inapplicable here as a **theorem**
rather than as an observation about an instance that happens not to be available. -/
theorem not_uniqueFactorizationMonoid_intUltrapower (hφ : (φ : Filter ℕ) ≤ atTop) :
    ¬ UniqueFactorizationMonoid (IntUltrapower φ) := fun _ =>
  not_exists_forall_dvd_pow_intUltrapower φ
    (exists_forall_dvd_pow_of_hasBoundedDenominators (IntUltrapower φ)
      (hasBoundedDenominators_intUltrapower φ hφ))

/-- The germ of the constant sequence `2` is not a unit: an inverse would have `2 * g i = 1` in `ℤ`
at some index, since a set of the filter is nonempty.

Nothing about `2` matters beyond its being a nonzero non-unit of `ℤ`, and it is written as a
coercion rather than given a name because a `def` would need its equation lemma supplied before
the rewrites below fire. -/
theorem not_isUnit_coe_two_intUltrapower :
    ¬ IsUnit ((((fun _ => (2 : ℤ)) : ℕ → ℤ) : IntUltrapower φ)) := by
  rw [isUnit_iff_exists_inv]
  rintro ⟨v, hv⟩
  induction v using Germ.inductionOn with
  | h g =>
    rw [← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq] at hv
    obtain ⟨i, hi⟩ := hv.exists
    simp only [Pi.mul_apply, Pi.one_apply] at hi
    omega

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

end FormalSpectrum

end
