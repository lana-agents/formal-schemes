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

Every negative value of the predicate that predates this file is at a **generic** point.

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

**The generic-point theorem is not recovered as a corollary, and must not be quoted as one.**
`FormalSpectrum.powerSeriesXPoint_bot` says the *point* is the same one, so the main theorem below
is about the same object as
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`. The two
*conditions* are not literally the same statement: that one is about `FractionRing R` and this one
about `Localization.AtPrime` at `⊥`, and **identifying those two models of the same localization
is not done here**. Nothing below should be read as deriving either theorem from the other, and
neither is reproved.

**`FormalSpectrum.HasBoundedDenominatorsAt` is named and not developed.** No classification, no
criterion, and no comparison with `FormalSpectrum.HasBoundedDenominators` beyond the observation
that the two definitions differ by replacing `m ≠ 0` with `m ∉ p` and the fraction field with the
local ring. Whether it is monotone in the prime, whether it follows from the condition at `⊥`, and
whether the classification at a unique factorisation domain has an analogue here are all open and
none is touched below.

**The closed point is not decided in general.**
`FormalSpectrum.isClosed_and_not_isStalkLimit_powerSeriesXPoint_intTwo` is one closed point of one
ring. It refutes no theorem on this tree: `FormalSpectrum.powerSeriesXClosedPoint` is *defined*
only at a local ring, so `FormalSpectrum.isStalkLimit_powerSeriesXClosedPoint`'s `[IsLocalRing R]`
cannot be deleted from a statement that would not typecheck without it. What it refutes is the
reading that closed points are the points where the colimit has nothing to do — over `ℤ` the basic
opens through the point over `(2)` are a genuinely filtered system and the colimit misses `1 / q`
for every prime `q` larger than the denominator on offer.

**Nothing about the ultrapower, unique factorisation, Dedekind or Noetherian hypotheses.** No
statement below carries any of them, and none of the material in
`FormalSchemes.StructureSheafStalkPowerSeriesUltrapower`,
`FormalSchemes.StructureSheafStalkPowerSeriesDedekind` or
`FormalSchemes.StructureSheafStalkPowerSeriesNumberField` is consumed or contradicted.

## Placement

A leaf over `FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, which holds the two
identifications at the generic point and the levelwise completion criterion the target
identification below reuses: forward closure **53** project modules besides itself, reverse closure
**0**, counted by walking every `^import FormalSchemes.` line over the 560 modules under
`FormalSchemes/` (a module is not counted in its own closure; the aggregator at the repository root
is outside the walk). It adds no Mathlib import.

`FormalSpectrum.awayCompletionEquivPowerSeriesAway` lives there too, is already stated at every
commutative ring, and is reused below unchanged.

**One instance was moved down to make room for this file.**
`FormalSpectrum.isPrime_span_singleton_two` — `(2)` is prime in `ℤ` — was declared in
`FormalSchemes.StructureSheafStalkPowerSeriesLocal`, which is a *sibling* leaf: neither file can
reach the other, so the closed point below would have needed a second copy of it. It now sits in
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, which both leaves reach, and is
declared once. `Int.span_two_isMaximal` (`FormalSchemes.TwoAdicDegeneracy`) is the same fact about
maximality and is **not** moved: it is in neither leaf's closure, it has a consumer where it is,
and the one use of maximality below is a term rather than a named theorem.

**A new module is not free here and the alternative was measured.** Appending to
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` would cost the rebuild of its reverse
closure and would put an arbitrary-point theory inside a file whose subject is one point; appending
to `FormalSchemes.StructureSheafStalkPowerSeriesLocal`, the leaf whose subject is closest, would
cost nothing at all in figures, because a leaf added to a leaf moves no closure. What a new module
costs instead is prose: the module count and every reverse closure through
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` move by one, which is twenty-three
figures in fifteen files, all of them numerals. That cost is paid in the same commit and is the
reason the diff is wider than the mathematics.

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
* `FormalSpectrum.isClosed_and_not_isStalkLimit_powerSeriesXPoint_intTwo`: **a closed point at
  which the predicate fails**, at `(X) ⊆ ℤ⟦X⟧` over `(2)`.
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
one is not reproved; the two targets are `FractionRing R` and `Localization.AtPrime` at `⊥`, and
identifying those is not done anywhere here. -/
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

**Nothing is proved about it here beyond that.** It is not compared with
`FormalSpectrum.HasBoundedDenominators`, it is not decided at any ring, and no criterion for it is
given; what it is for is that the surjectivity half of the criterion at the point over `p` is
literally it (`FormalSpectrum.exists_awayToAtPrimeCompletion_eq_powerSeriesXPoint_iff`). -/
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
complement is (`Ideal.primeCompl_le_nonZeroDivisors`). **This is the only place a proof in this
file needs `[IsDomain R]`**, and it is why the main theorem below carries it while the
surjectivity half does not. The binder occurs once more, on
`FormalSpectrum.powerSeriesXPoint_bot`, and no proof there consumes it: it is there so that the
statement typechecks, `FormalSpectrum.powerSeriesXGenericPoint` being defined only at a domain. -/
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
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators`.** By
`FormalSpectrum.powerSeriesXPoint_bot` the two are about the same point when `p = ⊥`, but their
right-hand sides are conditions on two different models of the same localization and identifying
those is not done here; neither theorem is derived from the other. -/
theorem isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt :
    IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXPoint R p) ↔
      HasBoundedDenominatorsAt R p :=
  (isStalkLimit_powerSeriesXPoint_iff R p).trans
    ⟨fun h => (exists_awayToAtPrimeCompletion_eq_powerSeriesXPoint_iff R p).mp h.2,
     fun h =>
      ⟨exists_awayCompletionRestrict_eq_zero_powerSeriesXPoint R p,
        (exists_awayToAtPrimeCompletion_eq_powerSeriesXPoint_iff R p).mpr h⟩⟩

end Domain

/-! ### A closed point at which the predicate fails -/

section Int

/-- A prime at least `n + 3`, hence odd. `Nat.exists_infinite_primes` is the same source the
`ℤ` refutation at the generic point draws its primes from. -/
def bigOddPrime (n : ℕ) : ℕ := (Nat.exists_infinite_primes (n + 3)).choose

theorem bigOddPrime_prime (n : ℕ) : (bigOddPrime n).Prime :=
  (Nat.exists_infinite_primes (n + 3)).choose_spec.2

theorem le_bigOddPrime (n : ℕ) : n + 3 ≤ bigOddPrime n :=
  (Nat.exists_infinite_primes (n + 3)).choose_spec.1

theorem bigOddPrime_notMem (n : ℕ) : ((bigOddPrime n : ℕ) : ℤ) ∉ Ideal.span {(2 : ℤ)} := by
  rw [Ideal.mem_span_singleton]
  intro hdvd
  have h2 : (2 : ℕ) ∣ bigOddPrime n := by
    have hcast : ((2 : ℕ) : ℤ) ∣ ((bigOddPrime n : ℕ) : ℤ) := by exact_mod_cast hdvd
    exact_mod_cast hcast
  rcases (Nat.Prime.eq_one_or_self_of_dvd (bigOddPrime_prime n) 2 h2) with h | h
  · omega
  · have := le_bigOddPrime n
    omega

/-- **The family that refutes the condition at `(2) ⊆ ℤ`**: the reciprocals of an infinite set of
odd primes, each of them a legitimate element of the local ring because its denominator is odd.

The `ℤ` refutation at the generic point uses `FormalSpectrum.unitFractionSeries`, the reciprocals
of *all* the positive integers; that family is not available here, because `1 / 2` is not in the
local ring at `(2)`. -/
def intTwoFamily (n : ℕ) : Localization.AtPrime (Ideal.span {(2 : ℤ)}) :=
  IsLocalization.mk' (M := (Ideal.span {(2 : ℤ)}).primeCompl) _ (1 : ℤ)
    ⟨((bigOddPrime n : ℕ) : ℤ), bigOddPrime_notMem n⟩

/-- **The denominator condition fails at `(2) ⊆ ℤ`.** For any odd `m`, a prime `q` exceeding `|m|`
divides no power of `m`, so `1 / q` is not cleared into `ℤ` by any power of `m` — and the family
above contains such a `q` for every `m`, because it contains a prime past every bound.

The step that makes the descent legal is that `ℤ → ℤ_(2)` is injective, the prime complement of a
prime of a domain consisting of nonzero divisors. -/
theorem not_hasBoundedDenominatorsAt_intTwo :
    ¬ HasBoundedDenominatorsAt ℤ (Ideal.span {(2 : ℤ)}) := by
  rw [hasBoundedDenominatorsAt_iff_range]
  intro h
  obtain ⟨m, hm, hall⟩ := h intTwoFamily
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ Ideal.zero_mem _)
  obtain ⟨z, hz⟩ := hall m.natAbs
  obtain ⟨⟨a, y⟩, hy⟩ := IsLocalization.mk'_surjective (Submonoid.powers m) z
  have hspec : algebraMap ℤ (Localization.Away m) (y : ℤ) * z =
      algebraMap ℤ (Localization.Away m) a := by
    rw [← hy]; exact IsLocalization.mk'_spec' _ a y
  have himg := congrArg (awayToLocalizationAtPrime ℤ (Ideal.span {(2 : ℤ)}) m hm) hspec
  rw [map_mul, awayToLocalizationAtPrime_algebraMap,
    awayToLocalizationAtPrime_algebraMap, hz, intTwoFamily] at himg
  have hmul := congrArg
    (· * algebraMap ℤ (Localization.AtPrime (Ideal.span {(2 : ℤ)}))
      ((bigOddPrime m.natAbs : ℕ) : ℤ)) himg
  simp only [mul_assoc] at hmul
  rw [IsLocalization.mk'_spec, map_one, mul_one, ← map_mul] at hmul
  have hinj : Function.Injective
      (algebraMap ℤ (Localization.AtPrime (Ideal.span {(2 : ℤ)}))) :=
    IsLocalization.injective _
      (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(2 : ℤ)}))
  have heq : (y : ℤ) = a * ((bigOddPrime m.natAbs : ℕ) : ℤ) := hinj hmul
  obtain ⟨k, hk⟩ := y.2
  have hdvd : ((bigOddPrime m.natAbs : ℕ) : ℤ) ∣ m ^ k :=
    ⟨a, by rw [show m ^ k = (y : ℤ) from hk, heq]; ring⟩
  have hqp : Prime ((bigOddPrime m.natAbs : ℕ) : ℤ) :=
    Nat.prime_iff_prime_int.mp (bigOddPrime_prime m.natAbs)
  have hqm : ((bigOddPrime m.natAbs : ℕ) : ℤ) ∣ m := hqp.dvd_of_dvd_pow hdvd
  have hnat : bigOddPrime m.natAbs ∣ m.natAbs := by
    have hd := Int.natAbs_dvd_natAbs.mpr hqm
    simpa using hd
  have hle : bigOddPrime m.natAbs ≤ m.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hm0) hnat
  have := le_bigOddPrime m.natAbs
  omega

/-- **`FormalSpectrum.IsStalkLimit` fails at the point of `Spf (ℤ⟦X⟧, (X))` over `(2)`.** -/
theorem not_isStalkLimit_powerSeriesXPoint_intTwo :
    ¬ IsStalkLimit (powerSeriesXIdeal ℤ) (powerSeriesXPoint ℤ (Ideal.span {(2 : ℤ)})) :=
  fun h => not_hasBoundedDenominatorsAt_intTwo
    ((isStalkLimit_powerSeriesXPoint_iff_hasBoundedDenominatorsAt ℤ
      (Ideal.span {(2 : ℤ)})).mp h)

/-- **A closed point at which `FormalSpectrum.IsStalkLimit` fails.**

Every negative value of the predicate that predates this file is at a **generic** point — of
`ℤ⟦X⟧`, of the local domain in `FormalSchemes.StructureSheafStalkPowerSeriesLocal`, and of the ring
of integers of a number field in
`FormalSchemes.StructureSheafStalkPowerSeriesNumberField` — and every positive value at a closed
point carries `[IsLocalRing R]`.

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

end FormalSpectrum

end
