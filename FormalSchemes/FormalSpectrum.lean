import FormalSchemes.AdicRing
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
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
* `FormalSpectrum.thickeningHomeomorph`: `Spf R` is homeomorphic to each of its infinitesimal
  thickenings `Spec (R ⧸ I ^ n)`, `n ≠ 0`, compatibly with the transition maps of the tower
  (`FormalSpectrum.comap_factor_comp_toThickening`) and with the closed embeddings into
  `Spec R` (`FormalSpectrum.comap_mk_toThickening`).

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
### Basic opens

The topology of `Spf R` has a basis of *basic opens* `D(f)`, `f ∈ R`, consisting of the open
primes not containing `f`. Under the identification of `Spf R` with `Spec (R ⧸ I)` these are
the usual basic opens attached to the residues `f mod I`, and every basic open of `Spec (R ⧸ I)`
arises this way since `R → R ⧸ I` is surjective. See EGA I, 10.1.4.
-/

section BasicOpen

omit [TopologicalSpace R] [IsAdicRing I]

/-- The basic open `D(f) ⊆ Spf R` attached to `f : R`: the set of open primes of `R` not
containing `f`. Under the identification `Spf R = Spec (R ⧸ I)` it is the basic open of the
residue of `f` modulo `I`. -/
def basicOpen (f : R) : TopologicalSpace.Opens (FormalSpectrum I) :=
  PrimeSpectrum.basicOpen (Ideal.Quotient.mk I f)

theorem mem_basicOpen (f : R) (x : FormalSpectrum I) :
    x ∈ basicOpen I f ↔ Ideal.Quotient.mk I f ∉ x.asIdeal :=
  Iff.rfl

@[simp]
theorem basicOpen_one : basicOpen I (1 : R) = ⊤ := by
  rw [basicOpen, map_one]
  exact PrimeSpectrum.basicOpen_one

@[simp]
theorem basicOpen_zero : basicOpen I (0 : R) = ⊥ := by
  rw [basicOpen, map_zero]
  exact PrimeSpectrum.basicOpen_zero

theorem basicOpen_mul (f g : R) : basicOpen I (f * g) = basicOpen I f ⊓ basicOpen I g := by
  rw [basicOpen, map_mul]
  exact PrimeSpectrum.basicOpen_mul _ _

/-- Every basic open of `Spec (R ⧸ I)` is a basic open of `Spf R`, since `R → R ⧸ I` is
surjective. -/
theorem exists_basicOpen_eq (g : R ⧸ I) :
    ∃ f : R, basicOpen I f = PrimeSpectrum.basicOpen g := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
  exact ⟨f, rfl⟩

/-- The basic opens `D(f)`, `f ∈ R`, form a basis of the topology of `Spf R`. -/
theorem isTopologicalBasis_basicOpen :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun f : R => (basicOpen I f : Set (FormalSpectrum I))) := by
  have h : (Set.range fun f : R => (basicOpen I f : Set (FormalSpectrum I))) =
      Set.range fun g : R ⧸ I => (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (R ⧸ I))) := by
    apply subset_antisymm
    · rintro _ ⟨f, rfl⟩
      exact ⟨Ideal.Quotient.mk I f, rfl⟩
    · rintro _ ⟨g, rfl⟩
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
      exact ⟨f, rfl⟩
  rw [h]
  exact PrimeSpectrum.isTopologicalBasis_basic_opens

end BasicOpen

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

/-!
### Infinitesimal thickenings

For `n ≠ 0` the canonical surjection `R ⧸ I ^ n →+* R ⧸ I` has nilpotent kernel `I ⧸ I ^ n`,
so the induced map `Spf R = Spec (R ⧸ I) → Spec (R ⧸ I ^ n)` is a homeomorphism: all the
infinitesimal thickenings `Spec (R ⧸ I ^ n)` share the same underlying topological space,
namely `Spf R`. This is the topological content of EGA I, 10.6.3: the formal spectrum is the
colimit of the tower `Spec (R ⧸ I) ↪ Spec (R ⧸ I ^ 2) ↪ ⋯`, and topologically the tower is
constant. The structure sheaf of `Spf R` (future work) will be the inverse limit of the
structure sheaves of the thickenings, transported along these homeomorphisms.
-/

section Thickenings

omit [TopologicalSpace R] [IsAdicRing I]

/-- The canonical map from `Spf R` to its `n`-th infinitesimal thickening `Spec (R ⧸ I ^ n)`,
induced by the surjection `R ⧸ I ^ n →+* R ⧸ I`. It is a homeomorphism; see
`FormalSpectrum.isHomeomorph_toThickening` and `FormalSpectrum.thickeningHomeomorph`. -/
def toThickening (n : ℕ) (hn : n ≠ 0) : FormalSpectrum I → PrimeSpectrum (R ⧸ I ^ n) :=
  PrimeSpectrum.comap (Ideal.Quotient.factor (Ideal.pow_le_self hn))

/-- The kernel of `R ⧸ I ^ n →+* R ⧸ I` consists of nilpotent elements, since any lift of an
element of the kernel lies in `I` and hence its `n`-th power lies in `I ^ n`. -/
theorem ker_factor_le_nilradical (n : ℕ) (hn : n ≠ 0) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self hn : I ^ n ≤ I)) ≤
      nilradical (R ⧸ I ^ n) := by
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  refine mem_nilradical.mpr ⟨n, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hx n)

/-- The map from `Spf R` to its `n`-th infinitesimal thickening `Spec (R ⧸ I ^ n)` is a
homeomorphism: nilpotents do not affect the prime spectrum. -/
theorem isHomeomorph_toThickening (n : ℕ) (hn : n ≠ 0) :
    IsHomeomorph (toThickening I n hn) :=
  PrimeSpectrum.isHomeomorph_comap _
    (fun x => ⟨1, one_pos, by
      rw [pow_one]
      exact RingHom.mem_range.mpr (Ideal.Quotient.factor_surjective _ x)⟩)
    (ker_factor_le_nilradical I n hn)

/-- `Spf R` is homeomorphic to each of its infinitesimal thickenings `Spec (R ⧸ I ^ n)`,
`n ≠ 0`, via `FormalSpectrum.toThickening`. -/
noncomputable def thickeningHomeomorph (n : ℕ) (hn : n ≠ 0) :
    FormalSpectrum I ≃ₜ PrimeSpectrum (R ⧸ I ^ n) :=
  IsHomeomorph.homeomorph _ (isHomeomorph_toThickening I n hn)

@[simp]
theorem thickeningHomeomorph_apply (n : ℕ) (hn : n ≠ 0) (x : FormalSpectrum I) :
    thickeningHomeomorph I n hn x = toThickening I n hn x :=
  rfl

/-- The maps to the thickenings are compatible with the transition maps
`Spec (R ⧸ I ^ m) → Spec (R ⧸ I ^ n)` of the tower, `m ≤ n`: the triangle over
`Spf R` commutes. -/
theorem comap_factor_comp_toThickening {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≤ n) :
    PrimeSpectrum.comap (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)) ∘
      toThickening I m hm = toThickening I n hn := by
  funext x
  change PrimeSpectrum.comap (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn))
      (PrimeSpectrum.comap (Ideal.Quotient.factor (Ideal.pow_le_self hm)) x) = _
  rw [← PrimeSpectrum.comap_comp_apply, Ideal.Quotient.factor_comp]
  rfl

/-- The closed embedding `Spec (R ⧸ I ^ n) → Spec R` restricted along `toThickening`
recovers the inclusion `Spf R → Spec R`: the thickenings all sit inside `Spec R`
compatibly. -/
theorem comap_mk_toThickening (n : ℕ) (hn : n ≠ 0) (x : FormalSpectrum I) :
    PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ n)) (toThickening I n hn x) =
      toPrimeSpectrum I x := by
  rw [toThickening, toPrimeSpectrum, ← PrimeSpectrum.comap_comp_apply,
    Ideal.Quotient.factor_comp_mk]

/-- The preimage of the basic open `D(f mod I ^ n) ⊆ Spec (R ⧸ I ^ n)` under the map to the
`n`-th infinitesimal thickening is the basic open `D(f) ⊆ Spf R`. -/
theorem toThickening_preimage_basicOpen (n : ℕ) (hn : n ≠ 0) (f : R) :
    toThickening I n hn ⁻¹'
        (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ n) f) : Set (PrimeSpectrum (R ⧸ I ^ n)))
      = (basicOpen I f : Set (FormalSpectrum I)) := by
  ext x
  change Ideal.Quotient.mk (I ^ n) f ∉ (PrimeSpectrum.comap _ x).asIdeal ↔ _
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.Quotient.factor_mk]
  rfl

/-- The image of the basic open `D(f) ⊆ Spf R` in the `n`-th infinitesimal thickening
`Spec (R ⧸ I ^ n)` is the basic open `D(f mod I ^ n)`. -/
theorem toThickening_image_basicOpen (n : ℕ) (hn : n ≠ 0) (f : R) :
    toThickening I n hn '' (basicOpen I f : Set (FormalSpectrum I)) =
      (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ n) f) :
        Set (PrimeSpectrum (R ⧸ I ^ n))) := by
  rw [← toThickening_preimage_basicOpen I n hn f,
    Set.image_preimage_eq _ (isHomeomorph_toThickening I n hn).bijective.surjective]

end Thickenings

end FormalSpectrum
