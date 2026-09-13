import FormalSchemes.StructureSheafStalkPowerSeriesDedekind

set_option linter.style.header false

/-!
# `IsStalkLimit` takes both values on one formal spectrum

`FormalSchemes.StructureSheafStalkPowerSeries` proves `FormalSpectrum.IsStalkLimit` at the
**closed** point of `Spf (R⟦X⟧, (X))` for every local ring `R`
(`FormalSpectrum.isStalkLimit_powerSeriesXClosedPoint`), and
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` proves that at the **generic** point of
a domain the predicate is exactly the denominator condition
(`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`). Put together,
a **local domain at which the denominator condition fails** settles the two points of one space
oppositely. Neither of those files exhibits such a ring, and the closed-point theorem says what one
would have to be.

**This file exhibits one**, the localization of `ℤ[X]` at the prime `(2, X)`:

> `FormalSpectrum.exists_isStalkLimit_and_not_isStalkLimit`: there are a formal spectrum and two of
> its points at which `FormalSpectrum.IsStalkLimit` is **true** and **false** respectively.

So the predicate is not a function of the ring: it depends on the point. A corollary that comes for
free is that the closed point and the generic point of that space are **distinct**
(`FormalSpectrum.powerSeriesXClosedPoint_ne_powerSeriesXGenericPoint_polyIntLocal`), proved by the
predicate rather than by the primes underneath the two points.

## Why this ring and not a shorter one

The criterion that refutes the condition here is
`FormalSpectrum.not_hasBoundedDenominators_of_primeIdeals` — a family of nonzero prime ideals lying
inside no single `m ≠ 0`, at an arbitrary domain. Being local puts two of the tree's other rings out
of reach, and it is worth saying which and why.

* **A discrete valuation ring is not a witness.** It is local, and it *satisfies* the denominator
  condition; the predicate holds at both of its points.
* **The Dedekind material cannot produce a witness at all.**
  `FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals` assumes `Ring.DimensionLEOne`,
  and a local Noetherian domain of dimension at most one has exactly **one** nonzero prime, so its
  hypothesis and locality exclude each other. The witness has to come from the arbitrary-domain
  criterion, and therefore from a ring of dimension at least two.

The localization of `ℤ[X]` at `(2, X)` is the cheapest such ring the project can reach: the ideals
`(X - 2(n+1))` for `n : ℕ` are pairwise distinct nonzero primes of `ℤ[X]`, all of them lie in
`(2, X)`, and no nonzero polynomial lies in all of them, since it would have infinitely many roots.
**No Mathlib import is added by this file**; the whole construction runs on what
`FormalSchemes.StructureSheafStalkPowerSeriesDedekind` already brings in.

## One choice that is load-bearing rather than cosmetic

**The base of the localization is a polynomial ring in one variable over `ℤ`, and it has to be.**
The first construction tried here was `k[X][Y]` localized at `(X, Y)`, which is the same argument
with the two primes replaced by evaluation kernels; every algebraic step elaborated, and then the
*statement* `FormalSpectrum (powerSeriesXIdeal …)` timed out at `whnf` at a million heartbeats. The
unifier is asked for

```
powerSeriesXIdeal L : @Ideal (PowerSeries L) MvPowerSeries.instSemiring
   against            @Ideal ?R            CommRing.toCommSemiring.toSemiring
```

— the `PowerSeries` semiring diamond, which is discharged instantly over `ℤ`, over `Polynomial ℚ`
and over a localization of `Polynomial ℚ`, and diverges when the base of the localization is
`Polynomial (Polynomial ℚ)`. That was isolated by a controlled run differing in the base ring alone:
`Polynomial ℚ` elaborates in 0.03 s and `Polynomial (Polynomial ℚ)` does not terminate. **Anyone
rewriting this file over `k[X,Y]` for elegance will reintroduce that timeout.**

## Main results

* `FormalSpectrum.polyIntRootPrime_le_polyIntTwoX`: **the primes `(X - 2(n+1))` all lie in
  `(2, X)`**, which is what allows them to survive the localization.
* `FormalSpectrum.exists_notMem_polyIntRootPrime`: **no nonzero polynomial lies in all of them**,
  because a polynomial with infinitely many roots over a domain is zero.
* `FormalSpectrum.not_hasBoundedDenominators_polyIntLocal`: **the denominator condition fails at
  `ℤ[X]` localized at `(2, X)`** — the first *local* ring on this tree at which it fails.
* `FormalSpectrum.exists_isStalkLimit_and_not_isStalkLimit_of_not_hasBoundedDenominators`: **at any
  local domain failing the condition the predicate takes both values** on `Spf (R⟦X⟧, (X))`.
* `FormalSpectrum.exists_isStalkLimit_and_not_isStalkLimit`: **and its hypothesis is inhabited**, so
  `FormalSpectrum.IsStalkLimit` genuinely varies across a single formal spectrum.
* `FormalSpectrum.powerSeriesXClosedPoint_ne_powerSeriesXGenericPoint_polyIntLocal`: **the two
  points are distinct**, by the predicate.

The division of labour between the fourth and the fifth of those is deliberate. **All of the
mathematics of the headline is in the fourth**, which is four lines and quotes the two theorems
named at the top of this file; the ring occupying most of this module exists only to show that the
fourth is not vacuous.

## What is *not* proved here

**Nothing here repairs EGA I 10.8's stalk half, and this is not a step towards a repair.** It is a
sharper refutation: the earlier counterexamples say the stalk half fails at some rings, and this one
says the failure is not even a property of the ring, since the same formal spectrum has a point
where the statement holds and a point where it does not. Which hypothesis makes EGA I 10.8 true is
still undetermined and nothing below bears on it.

**This ring does not exercise anything the element criterion could not reach.**
`FormalSpectrum.polyIntRootPrime` is generated by `X - 2(n+1)`, a prime **element**, so
`FormalSpectrum.not_hasBoundedDenominators_of_primes` would also refute the condition here once the
generators were transported through the localization. The ideal criterion is used because the
primality of the localized ideals is exactly `IsLocalization.isPrime_of_isPrime_disjoint`, which is
stated for ideals and needs no principality argument. **This file is not evidence that the ideal
criterion is stronger**; `FormalSchemes.StructureSheafStalkPowerSeriesDedekind` says where that
evidence is, at a nonprincipal maximal ideal.

**`FormalSpectrum.polyIntTwoX` is proved prime and nothing more.** It is the ideal `(2, X)` and it
is maximal, and neither of those is stated or used below; the localization needs primality alone.
Likewise `FormalSpectrum.PolyIntLocal` is a two-dimensional regular Noetherian local unique
factorisation domain and **none of those four words is proved here**, because none of them is
needed: the refutation runs on `IsDomain`, `IsLocalRing` and the explicit family.

**Nothing here is a statement about `ℤ⟦X⟧` or about `ℤ[X]` itself.** The denominator condition at
`ℤ` is settled in `FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` and is not touched;
`ℤ[X]` is not local and is used here only as the ring being localized.

**No hypothesis is removed from anything on the tree.** Not `[Countable (FractionRing R)]` from the
collapse — like every refutation on this cluster the proof builds one `ℕ`-indexed family and never
quantifies over a fraction field — and not `[IsLocalRing R]` from the closed-point theorem, which is
used exactly as it stands.

## Placement

A leaf over `FormalSchemes.StructureSheafStalkPowerSeriesDedekind`, which holds the arbitrary-domain
refuting criterion this file feeds: forward closure **55** project modules besides itself, reverse
closure **0**, counted by walking every `^import FormalSchemes.` line over the modules under
`FormalSchemes/` (a module is not counted in its own closure; the aggregator at the repository
root is outside the walk).

**The leaf carries no Mathlib import, so the usual argument for one does not apply here**, and the
reason to keep it separate is different: the material is a single concrete ring, and both files it
would otherwise be appended to are general theory over an arbitrary ring. It also keeps two
concurrent rows off `FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, which by commit
count is the most edited file on this tree. **The project's Mathlib closure is unchanged by this
branch** — walking `import` and `public import` over Mathlib's sources from every `import Mathlib…`
line under
`FormalSchemes/` gives the same figure at base and at head, since the only new module imports one
project module and nothing else.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX).
-/

noncomputable section

universe u

namespace FormalSpectrum

open Polynomial

/-! ### The prime `(2, X)` of `ℤ[X]`, and the primes inside it -/

/-- **The prime `(2, X)` of `ℤ[X]`**, presented as the polynomials whose constant term is even —
the contraction of `(2) ⊆ ℤ` along evaluation at `0`.

The presentation is chosen so that primality is `Ideal.comap_isPrime` and needs no computation of a
quotient ring. That it is the ideal `(2, X)`, and that it is maximal, are both true and neither is
proved or used: the localization below asks only that it be prime. -/
def polyIntTwoX : Ideal (Polynomial ℤ) :=
  (Ideal.span {(2 : ℤ)}).comap (Polynomial.evalRingHom (0 : ℤ))

instance : polyIntTwoX.IsPrime := Ideal.comap_isPrime _ _

/-- **The prime `(X - 2(n+1))` of `ℤ[X]`**, presented as the kernel of evaluation at `2(n+1)`.

Prime because `ℤ` is a domain (`RingHom.ker_isPrime`); the identification with the span of
`X - C (2(n+1))` is not needed and is not made. The multiples of `2` are used because
`FormalSpectrum.polyIntRootPrime_le_polyIntTwoX` needs each root to be even, and the shift by one is
used because `0` is not allowed to be a root: at `n = 0` the ideal would be `(X)`, which is still
inside `(2, X)`, so the shift buys nothing there — it is the injectivity of `n ↦ 2(n+1)` on `ℕ` that
is wanted, and starting at `2` keeps the family visibly inside the nonzero primes. -/
def polyIntRootPrime (n : ℕ) : Ideal (Polynomial ℤ) :=
  RingHom.ker (Polynomial.evalRingHom (2 * (n + 1) : ℤ))

instance (n : ℕ) : (polyIntRootPrime n).IsPrime := RingHom.ker_isPrime _

/-- **Every `(X - 2(n+1))` lies in `(2, X)`**, which is what lets the whole family survive the
localization at `(2, X)`.

The step is not substitution: from `f (2(n+1)) = 0` one gets `2 ∣ f 0` through
`Polynomial.sub_dvd_eval_sub`, the statement that `a - b` divides `f a - f b`. At `a = 2(n+1)` and
`b = 0` that reads `2(n+1) ∣ - f 0`, and `2 ∣ 2(n+1)`. -/
theorem polyIntRootPrime_le_polyIntTwoX (n : ℕ) : polyIntRootPrime n ≤ polyIntTwoX := by
  intro f hf
  rw [polyIntRootPrime, RingHom.mem_ker, Polynomial.coe_evalRingHom] at hf
  rw [polyIntTwoX, Ideal.mem_comap, Polynomial.coe_evalRingHom, Ideal.mem_span_singleton]
  have hdvd : (2 * (n + 1) : ℤ) - 0 ∣ f.eval (2 * (n + 1) : ℤ) - f.eval 0 :=
    Polynomial.sub_dvd_eval_sub _ _ f
  rw [hf, sub_zero, zero_sub] at hdvd
  exact dvd_neg.mp (dvd_trans ⟨(n + 1 : ℤ), rfl⟩ hdvd)

/-- **No nonzero polynomial lies in every `(X - 2(n+1))`**, which is the last hypothesis of
`FormalSpectrum.not_hasBoundedDenominators_of_primeIdeals`, read downstairs.

A polynomial in all of them has every `2(n+1)` as a root, so infinitely many roots, so is zero
(`Polynomial.eq_zero_of_infinite_isRoot`). The infinitude of the root set is
`Set.infinite_range_of_injective` followed by `Set.Infinite.mono` — the same pair, in the same
order, as in `FormalSpectrum.infinite_setOf_isPrime_ringOfIntegers`, where the injection is into the
primes of a ring of integers rather than into the roots of a polynomial. -/
theorem exists_notMem_polyIntRootPrime (f : Polynomial ℤ) (hf : f ≠ 0) :
    ∃ n, f ∉ polyIntRootPrime n := by
  by_contra hcon
  push Not at hcon
  refine hf (Polynomial.eq_zero_of_infinite_isRoot f ?_)
  have hinj : Function.Injective (fun n : ℕ => (2 * (n + 1) : ℤ)) := by
    intro a b hab
    simp only at hab
    omega
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hinj)
  rintro _ ⟨n, rfl⟩
  have hz := hcon n
  rw [polyIntRootPrime, RingHom.mem_ker, Polynomial.coe_evalRingHom] at hz
  simpa [Polynomial.IsRoot] using hz

/-! ### The local ring, and the denominator condition at it -/

/-- **`ℤ[X]` localized at `(2, X)`**: a local domain, and the witness this file is written for.

Both `IsLocalRing` and `IsDomain` are found by instance synthesis with no help once
`FormalSpectrum.polyIntTwoX` is known to be prime, which is the only input either of them takes;
nothing about the ring is supplied by hand. -/
abbrev PolyIntLocal : Type := Localization.AtPrime polyIntTwoX

/-- The image of `FormalSpectrum.polyIntRootPrime` in the localization. -/
def polyIntLocalPrime (n : ℕ) : Ideal PolyIntLocal :=
  (polyIntRootPrime n).map (algebraMap (Polynomial ℤ) PolyIntLocal)

/-- Each `(X - 2(n+1))` misses the multiplicative set being inverted, because it lies in `(2, X)`.
This is the one hypothesis both statements below need. -/
theorem disjoint_primeCompl_polyIntRootPrime (n : ℕ) :
    Disjoint (polyIntTwoX.primeCompl : Set (Polynomial ℤ))
      ((polyIntRootPrime n : Ideal (Polynomial ℤ)) : Set (Polynomial ℤ)) :=
  Set.disjoint_left.mpr fun _ hx hx' => hx (polyIntRootPrime_le_polyIntTwoX n hx')

instance (n : ℕ) : (polyIntLocalPrime n).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint polyIntTwoX.primeCompl _ (polyIntRootPrime n)
    inferInstance (disjoint_primeCompl_polyIntRootPrime n)

/-- **The localized primes contract back to the primes they came from.** This is the whole reason
the covering condition descends to the localization: membership of a fraction in
`FormalSpectrum.polyIntLocalPrime` depends on its numerator only, and the numerator's membership is
read off upstairs. -/
theorem under_polyIntLocalPrime (n : ℕ) :
    (polyIntLocalPrime n).under (Polynomial ℤ) = polyIntRootPrime n :=
  IsLocalization.under_map_of_isPrime_disjoint polyIntTwoX.primeCompl _ inferInstance
    (disjoint_primeCompl_polyIntRootPrime n)

/-- The nonzero element of `FormalSpectrum.polyIntLocalPrime n` that
`FormalSpectrum.not_hasBoundedDenominators_of_primeIdeals` asks for: the image of `X - 2(n+1)`. -/
def polyIntLocalWitness (n : ℕ) : PolyIntLocal :=
  algebraMap (Polynomial ℤ) PolyIntLocal (Polynomial.X - Polynomial.C (2 * (n + 1) : ℤ))

/-- `X - 2(n+1)` is a root of itself, so its image lies in the localized prime. -/
theorem polyIntLocalWitness_mem (n : ℕ) : polyIntLocalWitness n ∈ polyIntLocalPrime n := by
  refine Ideal.mem_map_of_mem _ ?_
  rw [polyIntRootPrime, RingHom.mem_ker]
  simp

/-- `ℤ[X] → ℤ[X]_(2,X)` is injective: the complement of a prime in a domain consists of
non-zero-divisors. Used only to keep the witnesses nonzero. -/
theorem injective_algebraMap_polyIntLocal :
    Function.Injective (algebraMap (Polynomial ℤ) PolyIntLocal) :=
  IsLocalization.injective PolyIntLocal polyIntTwoX.primeCompl_le_nonZeroDivisors

/-- The witnesses are nonzero, since `X - C a` is nonzero and the localization map is injective. -/
theorem polyIntLocalWitness_ne_zero (n : ℕ) : polyIntLocalWitness n ≠ 0 :=
  (map_ne_zero_iff _ injective_algebraMap_polyIntLocal).mpr (Polynomial.X_sub_C_ne_zero _)

/-- **No nonzero element of the localization lies in every `FormalSpectrum.polyIntLocalPrime n`.**

`FormalSpectrum.exists_notMem_polyIntRootPrime` transported along the localization map. A fraction
lies in the image of an ideal exactly when its numerator does (`IsLocalization.mk'_mem_iff`), and
the numerator's membership is membership in the contraction, which is
`FormalSpectrum.under_polyIntLocalPrime`. **The denominator plays no part**, which is why the
statement descends at all. -/
theorem exists_notMem_polyIntLocalPrime (m : PolyIntLocal) (hm : m ≠ 0) :
    ∃ n, m ∉ polyIntLocalPrime n := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective polyIntTwoX.primeCompl m
  have ha : a ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  obtain ⟨n, hn⟩ := exists_notMem_polyIntRootPrime a ha
  refine ⟨n, fun hmem => hn ?_⟩
  rw [IsLocalization.mk'_mem_iff] at hmem
  have hu : a ∈ (polyIntLocalPrime n).under (Polynomial ℤ) := hmem
  rwa [under_polyIntLocalPrime] at hu

/-- **The denominator condition fails at `ℤ[X]` localized at `(2, X)`** — the first *local* ring on
this tree at which it fails.

`FormalSpectrum.not_hasBoundedDenominators_of_primeIdeals` at the family above. That criterion is
the one stated at an arbitrary domain, with no factorisation, Noetherian or dimension hypothesis,
and it has to be: the Noetherian criterion beside it,
`FormalSpectrum.not_hasBoundedDenominators_of_infinite_primeIdeals`, assumes dimension at most one,
which a local ring with infinitely many nonzero primes cannot have. -/
theorem not_hasBoundedDenominators_polyIntLocal : ¬ HasBoundedDenominators PolyIntLocal :=
  not_hasBoundedDenominators_of_primeIdeals PolyIntLocal polyIntLocalPrime (fun _ => inferInstance)
    polyIntLocalWitness polyIntLocalWitness_mem polyIntLocalWitness_ne_zero
    exists_notMem_polyIntLocalPrime

/-! ### The predicate at the two points -/

/-- **`FormalSpectrum.IsStalkLimit` takes both values on `Spf (R⟦X⟧, (X))`, for every local domain
`R` at which the denominator condition fails.**

This is where all the mathematics of this file's headline is, and it is a composition of two
theorems proved elsewhere at their own generality:
`FormalSpectrum.isStalkLimit_powerSeriesXClosedPoint` needs only that `R` be local, and
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators` needs only that it
be a domain. Neither was proved with this statement in view, and no new argument is added here.

**The hypothesis is not vacuous**, which is the only thing the rest of this file does:
`FormalSpectrum.exists_isStalkLimit_and_not_isStalkLimit` is this theorem at
`FormalSpectrum.PolyIntLocal`. -/
theorem exists_isStalkLimit_and_not_isStalkLimit_of_not_hasBoundedDenominators (R : Type u)
    [CommRing R] [IsDomain R] [IsLocalRing R] (h : ¬ HasBoundedDenominators R) :
    ∃ x y : FormalSpectrum (powerSeriesXIdeal R), IsStalkLimit (powerSeriesXIdeal R) x ∧
      ¬ IsStalkLimit (powerSeriesXIdeal R) y :=
  ⟨powerSeriesXClosedPoint R, powerSeriesXGenericPoint R,
    isStalkLimit_powerSeriesXClosedPoint R,
    fun hh => h ((isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators R).mp hh)⟩

/-- **`FormalSpectrum.IsStalkLimit` is false at the generic point of `PolyIntLocal⟦X⟧`.** -/
theorem not_isStalkLimit_polyIntLocalGenericPoint :
    ¬ IsStalkLimit (powerSeriesXIdeal PolyIntLocal)
      (powerSeriesXGenericPoint PolyIntLocal) := fun h =>
  not_hasBoundedDenominators_polyIntLocal
    ((isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators PolyIntLocal).mp h)

/-- **And true at the closed point of the same space**, by
`FormalSpectrum.isStalkLimit_powerSeriesXClosedPoint`, which asks for nothing but locality. -/
theorem isStalkLimit_polyIntLocalClosedPoint :
    IsStalkLimit (powerSeriesXIdeal PolyIntLocal) (powerSeriesXClosedPoint PolyIntLocal) :=
  isStalkLimit_powerSeriesXClosedPoint PolyIntLocal

/-- **`FormalSpectrum.IsStalkLimit` varies across a single formal spectrum.**

The two witnesses are the closed point and the generic point of `Spf (R⟦X⟧, (X))` for
`R = FormalSpectrum.PolyIntLocal`. Read with
`FormalSpectrum.not_isStalkLimit_powerSeriesXIntGenericPoint` and
`FormalSpectrum.not_isStalkLimit_powerSeriesXRingOfIntegersGenericPoint`, which refute the predicate
at one point of many spaces, this refutes the idea that the answer depends on the ring alone. -/
theorem exists_isStalkLimit_and_not_isStalkLimit :
    ∃ x y : FormalSpectrum (powerSeriesXIdeal PolyIntLocal),
      IsStalkLimit (powerSeriesXIdeal PolyIntLocal) x ∧
        ¬ IsStalkLimit (powerSeriesXIdeal PolyIntLocal) y :=
  exists_isStalkLimit_and_not_isStalkLimit_of_not_hasBoundedDenominators PolyIntLocal
    not_hasBoundedDenominators_polyIntLocal

/-- **The closed point and the generic point of this space are distinct**, proved by the predicate:
they cannot be equal, since `FormalSpectrum.IsStalkLimit` holds at one and fails at the other.

`FormalSpectrum.powerSeriesXClosedPoint`'s own docstring gives the general reason two such points
differ — a local domain that is not a field — and that reason is more general than this one and
stands. This is a second route, available only where the predicate separates them. -/
theorem powerSeriesXClosedPoint_ne_powerSeriesXGenericPoint_polyIntLocal :
    powerSeriesXClosedPoint PolyIntLocal ≠ powerSeriesXGenericPoint PolyIntLocal := fun h =>
  not_isStalkLimit_polyIntLocalGenericPoint (h ▸ isStalkLimit_polyIntLocalClosedPoint)

end FormalSpectrum

end
