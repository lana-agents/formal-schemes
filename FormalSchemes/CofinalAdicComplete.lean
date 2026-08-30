import FormalSchemes.CofinalAdicRing

set_option linter.style.header false

/-!
# Adic completeness at a positive power of the ideal

`FormalSchemes.CofinalAdicRing` proves that `IsHausdorff`, `IsPrecomplete` and `IsAdicComplete`
transfer between cofinal ideals, with no containment hypothesis between them. This file records
the one corollary the affine-locality relaxation
(`FormalSchemes.CofinalTopFiniteTypeAffineLocal`) uses directly, and which is also the standard
witness that the transfer is not vacuous.

## Why a separate declaration

`IsAdicComplete.of_isCofinal` is stated at an arbitrary pair of cofinal ideals, so applying it at
`Ideal.IsCofinal.pow` (`FormalSchemes.CofinalIdeal`) means naming a cofinality proof and orienting
it. The corollary below does that once. `I` and `I ^ k` are different ideals with the same
completions, which is the same example that refutes the on-the-nose form of
`FormalSpectrum.isCofinal_map_spfIsoRingEquiv` (`FormalSchemes.SpfIsoIdealRecovery`), and it is
the shape in which `AlgebraicGeometry.IsTopologicallyFiniteType.self_of_two_charts_pow` exercises
the relaxation against a cofinality that is not reflexive.

## Main results

* `IsAdicComplete.pow`: a module complete for `I` is complete for every positive power of `I`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.2.
* [The Stacks Project, Tag 0317](https://stacks.math.columbia.edu/tag/0317).
-/

universe u v

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- **A module complete for `I` is complete for every positive power of `I`.** An application of
`IsAdicComplete.of_isCofinal` (`FormalSchemes.CofinalAdicRing`) to `Ideal.IsCofinal.pow`
(`FormalSchemes.CofinalIdeal`), oriented so that the *conclusion*'s ideal is the power.

Compare `IsTopologicallyFiniteType.pow` (`FormalSchemes.CofinalTopFiniteType`), which is the same
application of the same instance of `Ideal.IsCofinal` one layer up. -/
theorem IsAdicComplete.pow [IsAdicComplete I M] {k : ℕ} (hk : k ≠ 0) :
    IsAdicComplete (I ^ k) M :=
  IsAdicComplete.of_isCofinal (M := M) (Ideal.IsCofinal.pow I hk).symm
