import FormalSchemes.FormalSpectrum

set_option linter.style.header false

/-!
# Ideals of definition of a formal spectrum

An *ideal of definition* of a topological ring `R` is an ideal `I` for which the topology on
`R` is the `I`-adic topology (`IsAdic I`; see `FormalSchemes.AdicRing`). Such an ideal is not
unique: `R` may carry several ideals of definition, all inducing the same topology. This file
records that the affine formal spectrum `Spf R` depends only on the topological ring `R`, not
on the chosen ideal of definition, formalizing the affine part of EGA I, §10.3.

## Main results

* `IsAdic.exists_pow_le`: if `I` and `J` are two ideals of definition of the same topological
  ring `R`, then some power of `J` is contained in `I` (and, symmetrically, some power of `I`
  is contained in `J`). Thus the two adic filtrations are cofinal in one another.
* `IsAdic.radical_eq`: two ideals of definition have the same radical.
* `IsAdic.zeroLocus_eq` / `IsAdic.range_toPrimeSpectrum_eq`: consequently the formal spectra
  `FormalSpectrum I` and `FormalSpectrum J` cut out the same closed subset of `Spec R`.
* `IsAdic.homeomorphFormalSpectrum`: the canonical homeomorphism
  `FormalSpectrum I ≃ₜ FormalSpectrum J` identifying the two descriptions of `Spf R`, together
  with its compatibility `IsAdic.toPrimeSpectrum_homeomorphFormalSpectrum` with the inclusions
  into `Spec R`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], §10.3.
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

open TopologicalSpace Topology

variable {R : Type*} [CommRing R] [TopologicalSpace R] {I J : Ideal R}

namespace IsAdic

/-- If `I` and `J` are both ideals of definition of the topological ring `R` (both induce the
`I`-adic topology), then some power of `J` is contained in `I`: since `I` is an open
neighbourhood of `0`, it contains a basic neighbourhood `J ^ n` of the `J`-adic topology. -/
theorem exists_pow_le (hI : IsAdic I) (hJ : IsAdic J) : ∃ n : ℕ, J ^ n ≤ I := by
  have hInhds : (I : Set R) ∈ 𝓝 (0 : R) := by
    have := hI.hasBasis_nhds_zero.mem_of_mem (i := 1) trivial
    rwa [pow_one] at this
  obtain ⟨n, -, hn⟩ := hJ.hasBasis_nhds_zero.mem_iff.mp hInhds
  exact ⟨n, SetLike.coe_subset_coe.mp hn⟩

/-- An ideal of definition is contained in the radical of any other ideal of definition of the
same topological ring. -/
theorem le_radical (hI : IsAdic I) (hJ : IsAdic J) : J ≤ I.radical := by
  obtain ⟨n, hn⟩ := hI.exists_pow_le hJ
  intro x hx
  exact Ideal.mem_radical_of_pow_mem (Ideal.le_radical (hn (Ideal.pow_mem_pow hx n)))

/-- Two ideals of definition of the same topological ring have the same radical. -/
theorem radical_eq (hI : IsAdic I) (hJ : IsAdic J) : I.radical = J.radical :=
  le_antisymm (Ideal.radical_le_radical_iff.mpr (hJ.le_radical hI))
    (Ideal.radical_le_radical_iff.mpr (hI.le_radical hJ))

/-- Two ideals of definition of the same topological ring cut out the same closed subset of
`Spec R`. -/
theorem zeroLocus_eq (hI : IsAdic I) (hJ : IsAdic J) :
    PrimeSpectrum.zeroLocus (I : Set R) = PrimeSpectrum.zeroLocus (J : Set R) := by
  rw [← PrimeSpectrum.zeroLocus_radical I, ← PrimeSpectrum.zeroLocus_radical J,
    hI.radical_eq hJ]

/-- The inclusions of `FormalSpectrum I` and `FormalSpectrum J` into `Spec R` have the same
range: both are the closed subset `V(I) = V(J)`. -/
theorem range_toPrimeSpectrum_eq (hI : IsAdic I) (hJ : IsAdic J) :
    Set.range (FormalSpectrum.toPrimeSpectrum I) =
      Set.range (FormalSpectrum.toPrimeSpectrum J) := by
  rw [FormalSpectrum.range_toPrimeSpectrum, FormalSpectrum.range_toPrimeSpectrum,
    hI.zeroLocus_eq hJ]

/-- The canonical homeomorphism between the two descriptions `FormalSpectrum I` and
`FormalSpectrum J` of the underlying space of `Spf R`: both are closed subspaces of `Spec R`
with the same range, so they are homeomorphic. This makes precise that `Spf R` depends only on
the topological ring `R`, not on the chosen ideal of definition. -/
noncomputable def homeomorphFormalSpectrum (hI : IsAdic I) (hJ : IsAdic J) :
    FormalSpectrum I ≃ₜ FormalSpectrum J :=
  ((FormalSpectrum.isClosedEmbedding_toPrimeSpectrum I).isEmbedding.toHomeomorph.trans
        (Homeomorph.setCongr (hI.range_toPrimeSpectrum_eq hJ))).trans
    (FormalSpectrum.isClosedEmbedding_toPrimeSpectrum J).isEmbedding.toHomeomorph.symm

/-- The homeomorphism `homeomorphFormalSpectrum` is compatible with the inclusions into
`Spec R`: it sends a point to the point of `FormalSpectrum J` lying over the same prime of
`R`. -/
@[simp]
theorem toPrimeSpectrum_homeomorphFormalSpectrum (hI : IsAdic I) (hJ : IsAdic J)
    (x : FormalSpectrum I) :
    FormalSpectrum.toPrimeSpectrum J (hI.homeomorphFormalSpectrum hJ x) =
      FormalSpectrum.toPrimeSpectrum I x := by
  set embJ := (FormalSpectrum.isClosedEmbedding_toPrimeSpectrum J).isEmbedding with hembJ
  rw [← embJ.toHomeomorph_apply_coe (hI.homeomorphFormalSpectrum hJ x)]
  simp only [homeomorphFormalSpectrum, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  rfl

end IsAdic
