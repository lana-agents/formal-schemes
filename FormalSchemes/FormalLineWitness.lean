import FormalSchemes.Completion
import FormalSchemes.RestrictedPowerSeries

set_option linter.style.header false

/-!
# A second adic witness, whose formal spectrum is not a point: `ℤ⟦X⟧`

`FormalSchemes/TwoAdicWitness.lean` gave the tree its first adic witness, the `2`-adic integers
`twoAdicIdeal = (2)·ℤ^`. It rules out what it was built to rule out — `I = ⊥`, where the tower
`R ⧸ Iⁿ⁺¹` is constant and the whole ind-scheme layer says nothing — and it stays the right
witness for that.

It cannot rule out anything topological. `FormalSpectrum I` is *defined* as
`PrimeSpectrum (R ⧸ I)` (`FormalSchemes/FormalSpectrum.lean`), and `ℤ^ ⧸ 2ℤ^` is `𝔽₂`, so
`|Spf ℤ^|` is a **one-point space**. Every open cover of a point has a member equal to `⊤`, so a
theorem about *decomposing* `|Spf R|` — covers, charts, gluing, the remaining programme of EGA I
10.6.10 — is indistinguishable at that witness from the same theorem with `|Spf R|` a point. That
degeneracy is proved, not merely asserted: see `FormalSpectrum.twoAdic_exists_eq_top` in
`FormalSchemes/TwoAdicDegeneracy.lean`.

This file supplies a witness where that does not happen: the **formal affine line over `ℤ`**,
`ℤ[X]` completed at `(X)`, i.e. `ℤ⟦X⟧` with its ideal of definition. Its residue ring is `ℤ`, so

```
|Spf ℤ⟦X⟧|  ≃ₜ  Spec ℤ
```

(`FormalSpectrum.homeoSpecInt`) — infinite, and covered by two basic opens neither of which is
everything (`FormalSpectrum.iSup_twoChart`, `FormalSpectrum.twoChart_ne_top`).

## Why `(X)` and not `(2)`

Issue 1031 proposed `ℤ[X]` completed at `(2)`, whose residue ring is `𝔽₂[X]`. That works too, and
its `Spf` is also infinite, but reaching it costs a chain through
`Ideal.polynomialQuotientEquivQuotientPolynomial` and a proof that `(2 : ℤ)` is prime — and
`Prime (2 : ℤ)` is not in this project's Mathlib import closure, so it would have meant a new
import as well.

Completing the *same ring* at `(X)` instead gives a strictly better witness for less: the residue
ring is `ℤ` rather than `𝔽₂[X]`, `Spec ℤ` needs no new API, and `1 = 3 - 2` is the whole proof
that `D(2)` and `D(3)` cover it. `ℤ⟦X⟧` is also the more standard example — it is `𝔸¹` over `ℤ`
completed at the origin, the first formal scheme anyone writes down.

## Main definitions and results

* `FormalSpectrum.formalLineIdeal`, `FormalSpectrum.isAdicRing_formalLineIdeal`: the witness.
  As in `TwoAdicWitness.lean` the `IsAdicRing` fact is a plain theorem, **not** a global instance;
  activate it per section with `attribute [local instance]`.
* `FormalSpectrum.residueRingEquiv`, `FormalSpectrum.homeoSpecInt`: the residue ring is `ℤ`, and
  hence `|Spf ℤ⟦X⟧| ≃ₜ Spec ℤ`.
* `FormalSpectrum.ofPrimeInt`, `FormalSpectrum.mem_basicOpen_ofPrimeInt`: points of `|Spf ℤ⟦X⟧|`
  from primes of `ℤ`, and the membership rule that makes them usable.
* `FormalSpectrum.twoChart`, `FormalSpectrum.iSup_twoChart`,
  `FormalSpectrum.twoChart_ne_top`: **a genuinely two-piece open cover** — `D(2) ∪ D(3) = ⊤`
  with neither piece `⊤`.
* `FormalSpectrum.nontrivial_formalSpectrum`: **`|Spf ℤ⟦X⟧|` has at least two points.**

## Implementation notes

`polyXIdeal` and `formalLineIdeal` are `abbrev`s, not `def`s, for the reason recorded in
`TwoAdicWitness.lean`: they are the *index of a typeclass argument* (`[IsAdicRing _]`,
`AdicCompletion _ _`), instance search runs at `instances` transparency, and a `def` there fails to
synthesize in any witness section that spells the ideal out rather than using the name.

`Opens (FormalSpectrum I)` and `Opens (PrimeSpectrum (R ⧸ I))` are definitionally equal but carry
syntactically different topology instances (`instTopologicalSpace` versus `zariskiTopology`), so
`rw` with a `PrimeSpectrum` lemma against a `FormalSpectrum` goal fails with the usual
*"not type-correct under the `instances` transparency level"* note. That is why the cover is proved
pointwise, through `exists_mem_twoChart`, and the `⨆ … = ⊤` form derived from it by `Opens.ext`
rather than from `PrimeSpectrum.iSup_basicOpen_eq_top_iff` directly. Neither a transparency bump
nor a heartbeat bump is needed anywhere in this file.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1, §10.6.
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open Polynomial AlgebraicGeometry TopologicalSpace

namespace FormalSpectrum

/-- The ideal `(X) ⊆ ℤ[X]`: the origin of the affine line over `ℤ`. -/
abbrev polyXIdeal : Ideal ℤ[X] := Ideal.span {(X : ℤ[X])}

theorem polyXIdeal_fg : polyXIdeal.FG := Submodule.fg_span (Set.finite_singleton _)

/-- The ideal of definition of `ℤ⟦X⟧`, the `(X)`-adic completion of `ℤ[X]`.

An `abbrev` for the reason `TwoAdicWitness.lean` records: it is a typeclass index, and instance
search sees through `@[reducible]` and nothing else. -/
abbrev formalLineIdeal : Ideal (AdicCompletion polyXIdeal ℤ[X]) :=
  AdicCompletion.idealOfDefinition polyXIdeal

/-- **`ℤ⟦X⟧`, with its ideal of definition, is an adic ring.** Deliberately not a global
instance — see the module docstring of `FormalSchemes/TwoAdicWitness.lean`. -/
theorem isAdicRing_formalLineIdeal : IsAdicRing formalLineIdeal :=
  AdicCompletion.isAdicRing_map _ polyXIdeal_fg

/-- `(X) = (X - C 0)`, the form `Polynomial.quotientSpanXSubCAlgEquiv` expects. -/
theorem polyXIdeal_eq : polyXIdeal = Ideal.span {(X : ℤ[X]) - C (0 : ℤ)} := by
  rw [map_zero, sub_zero]

/-- **The residue ring of `ℤ⟦X⟧` is `ℤ`.** Completion does not change the level-`1` thickening
(`AdicCompletion.quotientEquiv`), and `ℤ[X] ⧸ (X)` is `ℤ` by evaluation at `0`. -/
def residueRingEquiv : (AdicCompletion polyXIdeal ℤ[X] ⧸ formalLineIdeal) ≃+* ℤ :=
  (AdicCompletion.quotientEquiv polyXIdeal polyXIdeal_fg).trans <|
    (Ideal.quotEquivOfEq polyXIdeal_eq).trans
      (Polynomial.quotientSpanXSubCAlgEquiv (0 : ℤ)).toRingEquiv

/-- A non-unit of `ℤ` lies in some prime. Used to produce points of `Spec ℤ`, and hence of
`|Spf ℤ⟦X⟧|`, at which a given basic open is missed. -/
theorem exists_prime_mem (n : ℤ) (hn : ¬ IsUnit n) : ∃ p : PrimeSpectrum ℤ, n ∈ p.asIdeal := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {n})
    fun h => hn (Ideal.span_singleton_eq_top.mp h)
  exact ⟨⟨M, hM.isPrime⟩, hle (Ideal.subset_span rfl)⟩

section Witness

attribute [local instance] isAdicRing_formalLineIdeal

/-- **The formal spectrum of `ℤ⟦X⟧` is `Spec ℤ`.** This is `formalCompletion.homeo` for the pair
`(ℤ[X], (X))`, composed with `residueRingEquiv`; unlike `|Spf ℤ^|`, which is a single point, this
space is infinite. -/
def homeoSpecInt : FormalSpectrum formalLineIdeal ≃ₜ PrimeSpectrum ℤ :=
  PrimeSpectrum.homeomorphOfRingEquiv residueRingEquiv

/-- The point of `|Spf ℤ⟦X⟧|` attached to a prime of `ℤ`. -/
def ofPrimeInt (p : PrimeSpectrum ℤ) : FormalSpectrum formalLineIdeal :=
  PrimeSpectrum.comap (residueRingEquiv : _ →+* ℤ) p

/-- Membership in a basic open, at a point coming from `Spec ℤ`: true by definition, and the rule
every computation below runs on. -/
theorem mem_basicOpen_ofPrimeInt (p : PrimeSpectrum ℤ) (f : AdicCompletion polyXIdeal ℤ[X]) :
    ofPrimeInt p ∈ basicOpen formalLineIdeal f ↔
      residueRingEquiv (Ideal.Quotient.mk formalLineIdeal f) ∉ p.asIdeal :=
  Iff.rfl

/-- **A two-piece open cover of `|Spf ℤ⟦X⟧|`**: `D(2)` and `D(3)`. -/
def twoChart : Bool → Opens (FormalSpectrum formalLineIdeal) :=
  fun b => basicOpen formalLineIdeal (if b then 2 else 3)

/-- The two charts cover, pointwise: a prime containing both `2` and `3` would contain
`3 - 2 = 1`. -/
theorem exists_mem_twoChart (x : FormalSpectrum formalLineIdeal) : ∃ b, x ∈ twoChart b := by
  by_contra hcon
  have h2 : Ideal.Quotient.mk formalLineIdeal (2 : AdicCompletion polyXIdeal ℤ[X]) ∈ x.asIdeal :=
    not_not.mp fun h => hcon ⟨true, h⟩
  have h3 : Ideal.Quotient.mk formalLineIdeal (3 : AdicCompletion polyXIdeal ℤ[X]) ∈ x.asIdeal :=
    not_not.mp fun h => hcon ⟨false, h⟩
  refine x.asIdeal.ne_top_iff_one.mp x.isPrime.ne_top ?_
  have hone : (1 : AdicCompletion polyXIdeal ℤ[X] ⧸ formalLineIdeal) =
      Ideal.Quotient.mk formalLineIdeal 3 - Ideal.Quotient.mk formalLineIdeal 2 := by
    rw [← map_sub]; norm_num
  rw [hone]
  exact sub_mem h3 h2

/-- **`D(2)` and `D(3)` cover `|Spf ℤ⟦X⟧|`.** -/
theorem iSup_twoChart : ⨆ b, twoChart b = ⊤ := by
  refine TopologicalSpace.Opens.ext (Set.eq_univ_iff_forall.mpr fun x => ?_)
  obtain ⟨b, hb⟩ := exists_mem_twoChart x
  rw [TopologicalSpace.Opens.coe_iSup]
  exact Set.mem_iUnion.mpr ⟨b, hb⟩

/-- **Neither chart is everything.** This is what `|Spf ℤ^|` cannot provide: there, every open
cover has a member equal to `⊤`, so `iSup_twoChart` alone would say nothing. -/
theorem twoChart_ne_top (b : Bool) : twoChart b ≠ ⊤ := by
  intro h
  cases b with
  | true =>
    obtain ⟨p, hp⟩ := exists_prime_mem 2 (by rw [Int.isUnit_iff]; decide)
    have hmem : ofPrimeInt p ∈ twoChart true := h ▸ trivial
    rw [twoChart, if_pos rfl, mem_basicOpen_ofPrimeInt, map_ofNat, map_ofNat] at hmem
    exact hmem hp
  | false =>
    obtain ⟨p, hp⟩ := exists_prime_mem 3 (by rw [Int.isUnit_iff]; decide)
    have hmem : ofPrimeInt p ∈ twoChart false := h ▸ trivial
    rw [twoChart, if_neg (by simp), mem_basicOpen_ofPrimeInt, map_ofNat, map_ofNat] at hmem
    exact hmem hp

/-- **`|Spf ℤ⟦X⟧|` has at least two points** — the primes of `ℤ` above `2` and above `3`. This is
the statement `|Spf ℤ^|` makes false, and the reason this witness exists. -/
theorem nontrivial_formalSpectrum : Nontrivial (FormalSpectrum formalLineIdeal) := by
  obtain ⟨p, hp⟩ := exists_prime_mem 2 (by rw [Int.isUnit_iff]; decide)
  obtain ⟨q, hq⟩ := exists_prime_mem 3 (by rw [Int.isUnit_iff]; decide)
  refine ⟨ofPrimeInt p, ofPrimeInt q, fun hpq => ?_⟩
  obtain ⟨b, hb⟩ := exists_mem_twoChart (ofPrimeInt p)
  cases b with
  | true =>
    rw [twoChart, if_pos rfl, mem_basicOpen_ofPrimeInt, map_ofNat, map_ofNat] at hb
    exact hb hp
  | false =>
    rw [hpq, twoChart, if_neg (by simp), mem_basicOpen_ofPrimeInt, map_ofNat, map_ofNat] at hb
    exact hb hq

end Witness

end FormalSpectrum

end
