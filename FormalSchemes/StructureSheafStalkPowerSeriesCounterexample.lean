import FormalSchemes.StructureSheafStalkPowerSeriesGeneric

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
shorter for going through it. It characterises **one conjunct at one point**, not
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

**Naming it decides nothing.** Which rings satisfy `FormalSpectrum.HasBoundedDenominators` is not
determined here: three values are three rings, not a classification, and none of the obvious
guesses about Dedekind or semilocal domains is checked anywhere below.

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

**No general statement about `IsStalkLimit` at a non-closed point.** The proof uses `ℤ` through
`FormalSpectrum.unitFractionSeries` and the infinitude of the primes. The two identifications hold
much more generally — the first at every commutative ring, the second at every domain — but the
final step does not, and no attempt is made to characterise the rings where it does.

**Nothing under a Noetherian hypothesis**, and nothing that uses one.

**No comparison with `Spec`.** `FormalSchemes.SpfDiscrete` is not imported; measured at **42**
modules besides itself on top of this file's closure, 43 including it, and nothing here needs it.

## Implementation notes

The five `AdicCompletion` lemmas at the top of the file mention no formal geometry and would sit
naturally in `FormalSchemes.Completion`, whose reverse closure is 434 of the project's 543 modules
against this leaf's 0. They are kept here on the disposition
`FormalSchemes.StructureSheafStalkPowerSeries` recorded for
`AdicCompletion.bijective_mapCompletion` — which is the same shape and is still in that leaf — and
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

A leaf over `FormalSchemes.StructureSheafStalkPowerSeriesGeneric`: forward closure **51** project
modules besides itself (52 counted with itself), reverse closure **0**, counted by walking every
`^import` line over the 543 modules under `FormalSchemes/`. It adds no Mathlib import;
`Mathlib/RingTheory/AdicCompletion/Completeness.lean`, which carries the
`IsAdicComplete (.span {X}) (PowerSeries R)` instance, is already reached. The discrete-valuation
section adds none either: `IsDiscreteValuationRing`,
`IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible` and `PowerSeries.map_surjective`
are all in this closure already.

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
* `FormalSpectrum.surjective_awayToFractionRing_of_irreducible`: `R[1/ϖ] → Frac R` is **surjective**
  at a uniformizer of a discrete valuation ring, which is what `ℤ` cannot do at any `m`.
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
* `FormalSpectrum.hasBoundedDenominators_of_field`: **a field satisfies it**, with `m = 1`. This
  is a value of the condition and not of `FormalSpectrum.IsStalkLimit`; the latter at a field is
  `FormalSpectrum.isStalkLimit_powerSeriesX_field`, by a different route.
* `FormalSpectrum.not_hasBoundedDenominators_int`: **`ℤ` does not**, which is the whole of the
  refutation with no formal geometry in it.
* `FormalSpectrum.hasBoundedDenominators_of_isDiscreteValuationRing`: **a discrete valuation ring
  does**, with a uniformizer as the denominator.

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
to depend on the family. `∃ m, ∀ x` is strictly stronger and is false at `ℤ`, since it implies
this one. `∀ x, ∀ n, ∃ m` is strictly weaker and holds at every domain, because a single element
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
strengthening to `∃ m, ∀ x` implies this one and so is false at `ℤ`.

This is exactly the surjectivity half of
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff` at the generic point of `R`, by
`FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXGenericPoint_iff_denominators`. It
is **one conjunct at one point** and not `FormalSpectrum.IsStalkLimit`, whose other conjunct holds
at the generic point of every domain
(`FormalSpectrum.exists_awayCompletionRestrict_eq_zero_powerSeriesXGenericPoint`). Naming it
decides nothing: which rings satisfy it is not determined here, and the three values below are
three rings and not a classification.

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
the proof below uses none of it. -/
theorem hasBoundedDenominators_of_field (K : Type u) [Field K] : HasBoundedDenominators K := by
  intro x
  refine ⟨1, one_ne_zero, fun n => ⟨0, ?_⟩⟩
  rw [pow_zero, map_one, one_mul]
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := K) (x n)
  exact ⟨r / s, by rw [← hrs, map_div₀]⟩

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
infinitely many primes to put in a denominator and a discrete valuation ring has one. -/
theorem hasBoundedDenominators_of_isDiscreteValuationRing : HasBoundedDenominators R :=
  (hasBoundedDenominators_iff_range R).mpr
    ((IsDiscreteValuationRing.exists_irreducible R).elim fun ϖ hϖ x =>
      ⟨ϖ, hϖ.ne_zero, fun n =>
        surjective_awayToFractionRing_of_irreducible R hϖ (x n)⟩)

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
