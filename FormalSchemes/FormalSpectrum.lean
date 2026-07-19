import FormalSchemes.AdicRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Spectral.Basic

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
* `FormalSpectrum.map`: a ring homomorphism `φ : R →+* S` mapping the ideal of definition `I`
  into the ideal of definition `J` induces a map `Spf S → Spf R`, making `Spf` a contravariant
  functor.

## Main results

* `FormalSpectrum.isClosedEmbedding_toPrimeSpectrum`: `toPrimeSpectrum` is a closed embedding.
* `FormalSpectrum.range_toPrimeSpectrum`: the range of `toPrimeSpectrum` is `zeroLocus I`, i.e.
  exactly the primes of `R` containing the ideal of definition `I`.
* `FormalSpectrum.instSpectralSpace`: `Spf R` is a spectral space, i.e. it is quasi-compact,
  T0, sober, quasi-separated, and its quasi-compact opens form a basis, just like `Spec R`.
* `FormalSpectrum.continuous_map`, `FormalSpectrum.map_id`, `FormalSpectrum.map_comp`:
  `FormalSpectrum.map` is continuous and functorial.
* `FormalSpectrum.toPrimeSpectrum_map`: `FormalSpectrum.map` commutes with the inclusions
  into the prime spectra, i.e. the square relating `Spf` and `Spec` commutes.

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

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `Spf R` is a spectral space, being homeomorphic to `Spec (R ⧸ I)`. In particular it is
quasi-compact, `T0`, sober, and quasi-separated. -/
instance instSpectralSpace : SpectralSpace (FormalSpectrum I) :=
  inferInstanceAs (SpectralSpace (PrimeSpectrum (R ⧸ I)))

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

/-!
### Functoriality

A ring homomorphism `φ : R →+* S` between adic rings that maps the ideal of definition `I`
of `R` into the ideal of definition `J` of `S` induces a map `Spf S → Spf R`, sending an open
prime `q` of `S` to the open prime `φ ⁻¹' q` of `R`. Note that such a `φ` is automatically
continuous for the adic topologies, since `φ '' (I ^ n) ⊆ J ^ n` for all `n`. This makes
`Spf` a contravariant functor, compatible with `Spec` under the closed embeddings
`toPrimeSpectrum`; see EGA I, 10.2.
-/

section Functoriality

omit [TopologicalSpace R] [IsAdicRing I]

variable {S : Type*} [CommRing S] (J : Ideal S) {T : Type*} [CommRing T] (K : Ideal T)

/-- The map `Spf S → Spf R` induced by a ring homomorphism `φ : R →+* S` mapping the ideal
of definition `I` of `R` into the ideal of definition `J` of `S`. It sends an open prime of
`S` to its preimage under `φ`, which is open since `φ` is continuous for the adic
topologies. -/
def map (φ : R →+* S) (h : I ≤ J.comap φ) : FormalSpectrum J → FormalSpectrum I :=
  PrimeSpectrum.comap (Ideal.quotientMap J φ h)

theorem continuous_map (φ : R →+* S) (h : I ≤ J.comap φ) : Continuous (map I J φ h) :=
  PrimeSpectrum.continuous_comap (Ideal.quotientMap J φ h)

@[simp]
theorem map_id : map I I (RingHom.id R) (Ideal.comap_id I).ge = id := by
  have hq : Ideal.quotientMap I (RingHom.id R) (Ideal.comap_id I).ge = RingHom.id (R ⧸ I) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun x => by simp [Ideal.quotientMap_mk])
  funext x
  change PrimeSpectrum.comap (Ideal.quotientMap I (RingHom.id R) (Ideal.comap_id I).ge) x = x
  rw [hq, PrimeSpectrum.comap_id]

theorem map_comp (φ : R →+* S) (ψ : S →+* T) (hIJ : I ≤ J.comap φ) (hJK : J ≤ K.comap ψ)
    (hIK : I ≤ K.comap (ψ.comp φ)) :
    map I K (ψ.comp φ) hIK = map I J φ hIJ ∘ map J K ψ hJK := by
  have hq : Ideal.quotientMap K (ψ.comp φ) hIK =
      (Ideal.quotientMap K ψ hJK).comp (Ideal.quotientMap J φ hIJ) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun x => by simp [Ideal.quotientMap_mk])
  funext x
  change PrimeSpectrum.comap (Ideal.quotientMap K (ψ.comp φ) hIK) x = _
  rw [hq, PrimeSpectrum.comap_comp_apply]
  rfl

/-- The inclusions `Spf → Spec` intertwine `FormalSpectrum.map φ` with the usual induced map
`Spec S → Spec R`: the square

```
Spf S  →  Spf R
  ↓          ↓
Spec S →  Spec R
```

commutes. -/
theorem toPrimeSpectrum_map (φ : R →+* S) (h : I ≤ J.comap φ) (x : FormalSpectrum J) :
    toPrimeSpectrum I (map I J φ h x) = PrimeSpectrum.comap φ (toPrimeSpectrum J x) := by
  change PrimeSpectrum.comap (Ideal.Quotient.mk I)
      (PrimeSpectrum.comap (Ideal.quotientMap J φ h) x)
      = PrimeSpectrum.comap φ (PrimeSpectrum.comap (Ideal.Quotient.mk J) x)
  rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
    Ideal.quotientMap_comp_mk]

end Functoriality

end FormalSpectrum
