import FormalSchemes.AdicRing
import Mathlib.RingTheory.Spectrum.Prime.Topology

set_option linter.style.header false

/-!
# The formal spectrum of an adic ring

Given an adic ring `R` with ideal of definition `I` (see `IsAdicRing`), its **formal spectrum**
`Spf R` is, as a set, the collection of *open* prime ideals of `R`: those primes that are open
subsets of `R` for its given topology. Since the topology is the `I`-adic one, a prime `p` is
open iff it contains some power `I ^ n`, and since `p` is prime this happens iff `p` contains `I`
itself. So the underlying set of `Spf R` is `{p : PrimeSpectrum R // I ≤ p.asIdeal}`, which is in
canonical order- and homeomorphism with `Spec (R ⧸ I)` via
`Ideal.primeSpectrumQuotientOrderIsoZeroLocus`. We take this quotient description as our
*definition* of the topological space underlying `Spf R`, and record that it sits inside `Spec R`
as the closed subspace of primes containing `I`.

This file only builds the underlying topological space of `Spf R`; the structure sheaf of adically
complete rings that makes it a locally ringed space is future work.

## Main definitions

* `FormalSpectrum I`: the topological space `Spf R`, defined as `Spec (R ⧸ I)`.
* `FormalSpectrum.toPrimeSpectrum`: the induced inclusion `Spf R → Spec R`.

## Main results

* `FormalSpectrum.isClosedEmbedding_toPrimeSpectrum`: `toPrimeSpectrum` is a closed embedding.
* `FormalSpectrum.range_toPrimeSpectrum`: the range of `toPrimeSpectrum` is `zeroLocus I`, i.e.
  exactly the primes of `R` containing the ideal of definition `I`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.
* [The Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY)
-/

open Topology

variable {R : Type*} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-- The **formal spectrum** `Spf R` of an adic ring `R` with ideal of definition `I`, as a
topological space. It is defined as `Spec (R ⧸ I)`, which parametrizes exactly the open primes
of `R`, i.e. those primes containing `I`; see `FormalSpectrum.range_toPrimeSpectrum`. -/
def FormalSpectrum : Type _ := PrimeSpectrum (R ⧸ I)

namespace FormalSpectrum

noncomputable instance : TopologicalSpace (FormalSpectrum I) :=
  inferInstanceAs (TopologicalSpace (PrimeSpectrum (R ⧸ I)))

/-- The inclusion of the formal spectrum `Spf R` into `Spec R`, sending an open prime of `R ⧸ I`
to its preimage under `R → R ⧸ I`. -/
def toPrimeSpectrum : FormalSpectrum I → PrimeSpectrum R :=
  PrimeSpectrum.comap (Ideal.Quotient.mk I)

omit [TopologicalSpace R] [IsAdicRing I] in
theorem range_toPrimeSpectrum :
    Set.range (toPrimeSpectrum I) = PrimeSpectrum.zeroLocus (I : Set R) := by
  have := range_comap_of_surjective _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rwa [Ideal.mk_ker] at this

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `Spf R` is a closed subspace of `Spec R`: the primes of `R` containing the ideal of
definition `I`. -/
theorem isClosedEmbedding_toPrimeSpectrum : IsClosedEmbedding (toPrimeSpectrum I) :=
  PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective

end FormalSpectrum
