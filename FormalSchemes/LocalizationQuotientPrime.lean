import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic

set_option linter.style.header false

/-!
# Localization at a prime commutes with quotient by an ideal

For a commutative ring `R`, an ideal `K : Ideal R` and a prime `P` of `R ⧸ K`, localizing the
quotient `R ⧸ K` at `P` is the same as quotienting the localization of `R` at the prime `p` below
`P` by the extension of `K`. Concretely, writing `A = Localization.AtPrime p` with
`p = P.comap (Ideal.Quotient.mk K)`, the natural map `R ⧸ K → A ⧸ K·A` exhibits `A ⧸ K·A` as a
localization of `R ⧸ K` at `P`.

This is the prime-complement analogue of `FormalSchemes.LocalizationQuotient`, which does the same
for `Submonoid.powers f`, and both are the same Mathlib fact — `IsLocalization.of_surjective`,
instantiated in `Mathlib/RingTheory/Localization/Ideal.lean` as `S ⧸ K.map (algebraMap R S)` being
a localization of `R ⧸ K` at `Algebra.algebraMapSubmonoid (R ⧸ K) M` — specialised to a different
submonoid `M`. All that changes is the identification of the image submonoid, which for a prime
complement is `IsLocalization.algebraMapSubmonoid_primeCompl_comap` below.

It sits in its own file rather than beside its `Localization.Away` sibling because the two are used
at opposite scales, and it is the ratio and not either figure that decides.
`FormalSchemes.LocalizationQuotient` has reverse closure **509**, counted by walking every
`import FormalSchemes.` line, transitively, over the 564 modules under `FormalSchemes/` (a module
is not counted in its own closure, and the aggregator at the repository root is outside the walk).
This module's reverse closure is **17**, and exactly one module imports it directly,
`FormalSchemes.StructureSheafStalkLevels`, which is also the only module whose code names anything
declared here. The other sixteen reach this file only through that one and, imports being
transitive, see these declarations without using any: *sees*, *is recompiled by* and *uses* part
company here, and merging the two files would move the first two and not the third. It would put
this statement in front of every module that reaches the away one and recompile almost all of them
for something they do not use. Both absolutes go stale the moment a module is added above either
file, and they are here as the evidence for the ratio rather than as facts worth keeping in sync;
the split stops paying when this module is reached by as much of the tree as the away one is, and
it is nowhere near that.

The statement is phrased against an arbitrary prime `p` of `R` together with a hypothesis
`P.comap (Ideal.Quotient.mk K) = p`, rather than against `P.comap (Ideal.Quotient.mk K)` itself.
That is what a tower of quotients needs: there `K` varies with the level while the prime of `R`
below does not, and the consumer must be able to name one ring `A` for all levels.

## Main results

* `IsLocalization.algebraMapSubmonoid_primeCompl_comap`: the image in `R ⧸ K` of the complement of
  `P.comap (Ideal.Quotient.mk K)` is the complement of `P`.
* `IsLocalization.atPrime_quotient`: `A ⧸ K.map (algebraMap R A)` is a localization of `R ⧸ K`
  at `P`, where `A = Localization.AtPrime p`.
* `Localization.atPrimeQuotientEquiv`: the resulting ring isomorphism
  `Localization.AtPrime P ≃+* A ⧸ K.map (algebraMap R A)`, with
  `Localization.atPrimeQuotientEquiv_algebraMap` saying it is a map of `R ⧸ K`-algebras.

## References

`FormalSchemes.LocalizationQuotient`, whose `Localization.Away` statements this file mirrors
declaration for declaration, and `IsLocalization.of_surjective` in Mathlib, which is the fact both
rest on.
-/

namespace IsLocalization

variable {R : Type*} [CommRing R] (K : Ideal R) (P : Ideal (R ⧸ K)) [P.IsPrime]

/-- The image in `R ⧸ K` of the complement of the prime `P.comap (Ideal.Quotient.mk K)` is the
complement of `P`. Both inclusions are immediate from `Ideal.Quotient.mk` being surjective and
`P.comap (Ideal.Quotient.mk K)` being, by definition, its preimage. -/
theorem algebraMapSubmonoid_primeCompl_comap :
    Algebra.algebraMapSubmonoid (R ⧸ K) (P.comap (Ideal.Quotient.mk K)).primeCompl =
      P.primeCompl := by
  ext y
  refine ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ hx, fun hy => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨x, hy, rfl⟩

variable (p : Ideal R) [p.IsPrime] (hp : P.comap (Ideal.Quotient.mk K) = p)

include hp in
/-- **Localization at a prime commutes with quotient.** For a prime `p` of `R` lying under a prime
`P` of `R ⧸ K`, the quotient of `Localization.AtPrime p` by the extension of `K` is a localization
of `R ⧸ K` at `P`.

This is the Mathlib instance exhibiting `S ⧸ K.map (algebraMap R S)` as a localization of `R ⧸ K`
at `Algebra.algebraMapSubmonoid (R ⧸ K) M`, rewritten along
`IsLocalization.algebraMapSubmonoid_primeCompl_comap`. -/
theorem atPrime_quotient :
    IsLocalization.AtPrime
      (Localization.AtPrime p ⧸ K.map (algebraMap R (Localization.AtPrime p))) P := by
  subst hp
  rw [IsLocalization.AtPrime, ← algebraMapSubmonoid_primeCompl_comap K P]
  infer_instance

end IsLocalization

namespace Localization

variable {R : Type*} [CommRing R] (K : Ideal R) (P : Ideal (R ⧸ K)) [P.IsPrime]
  (p : Ideal R) [p.IsPrime] (hp : P.comap (Ideal.Quotient.mk K) = p)

/-- **Localization at a prime commutes with quotient (packaged as an isomorphism).** The
localization of `R ⧸ K` at `P` is isomorphic, as a ring, to the quotient of `Localization.AtPrime p`
by the extension of `K`, for `p` the prime of `R` below `P`. Both are localizations of `R ⧸ K` at
`P` (see `IsLocalization.atPrime_quotient`), so they are canonically isomorphic by uniqueness of
localizations. -/
noncomputable def atPrimeQuotientEquiv :
    Localization.AtPrime P ≃+*
      Localization.AtPrime p ⧸ K.map (algebraMap R (Localization.AtPrime p)) :=
  haveI := IsLocalization.atPrime_quotient K P p hp
  (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
    (Localization.AtPrime p ⧸ K.map (algebraMap R (Localization.AtPrime p)))).toRingEquiv

/-- `Localization.atPrimeQuotientEquiv` is an `R ⧸ K`-algebra map: it sends the image of
`y : R ⧸ K` in `Localization.AtPrime P` to its image in `A ⧸ K·A`. This is the naturality input
needed downstream, where the two sides are identified level by level in a tower of quotients. -/
@[simp]
theorem atPrimeQuotientEquiv_algebraMap (y : R ⧸ K) :
    atPrimeQuotientEquiv K P p hp (algebraMap (R ⧸ K) (Localization.AtPrime P) y) =
      algebraMap (R ⧸ K)
        (Localization.AtPrime p ⧸ K.map (algebraMap R (Localization.AtPrime p))) y :=
  haveI := IsLocalization.atPrime_quotient K P p hp
  (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) _).commutes y

end Localization
