import FormalSchemes.AffineFibreProductScheme
import FormalSchemes.ClosedImmersion
import FormalSchemes.ClosedImmersionSections

set_option linter.style.header false

/-!
# The affine diagonal as a closed immersion of formal schemes

`FormalSchemes/ClosedImmersion.lean` introduced the predicate `FormalScheme.IsClosedImmersion` on a
morphism of formal schemes. `FormalSchemes/ClosedImmersionSections.lean` proved the affine EGA I
§10.15 diagonal to be a closed immersion, but phrased as the raw conjunction on
`FormalSpectrum.map` / `presheafedSpaceMap` of the surjective codiagonal `∇ : A ⊗̂_R A → A`.

This file bridges the two: it repackages that conjunction through the new predicate for the
formal-scheme diagonal `CompletedTensorProduct.schemeDiagonal` (the `FormalScheme.Hom` version of
`Δ_{A/R} : Spf A ⟶ Spf (A ⊗̂_R A)`, `FormalSchemes/AffineFibreProductScheme.lean`), so downstream
consumers can cite a single `FormalScheme.IsClosedImmersion` fact instead of re-deriving the
closed-embedding-and-surjective-stalks conjunction.

The bridge is definitional glue: `schemeDiagonal hI = FormalScheme.Hom.mk (diagonal hI)` (so its
underlying locally-ringed-space morphism is `CompletedTensorProduct.diagonal hI`), whose base map is
`FormalSpectrum.map ∇` (`diagonal_base_eq`, by `rfl`). Hence the closed-embedding half is
`isClosedEmbedding_diagonal_base` and the stalk-surjectivity half is the second component of
`diagonal_isClosedImmersion`.

## Main results

* `CompletedTensorProduct.schemeDiagonal_isClosedImmersion`: the affine diagonal
  `Δ_{A/R} : Spf A ⟶ Spf (A ⊗̂_R A)` is a `FormalScheme.IsClosedImmersion` — the affine case of
  EGA I §10.15 separatedness in the reusable predicate.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [The Stacks Project, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A]
variable [TopologicalSpace R] [IsAdicRing I]
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
variable [TopologicalSpace (CompletedTensorProduct R I A A)]
  [IsAdicRing (idealOfDefinition R I A A)]

/-- **The affine diagonal `Δ_{A/R} : Spf A ⟶ Spf (A ⊗̂_R A)` is a closed immersion of formal
schemes** (EGA I §10.15). This packages the two-part conjunction `diagonal_isClosedImmersion`
(a closed topological embedding of the base map, `isClosedEmbedding_diagonal_base`, together with
surjective stalk maps, the inducing ring hom being the surjective codiagonal `∇ : A ⊗̂_R A → A`)
into the `FormalScheme.IsClosedImmersion` predicate for the formal-scheme diagonal
`schemeDiagonal`. It is the affine model of §10.15 separatedness: `Spf A` is separated over
`Spf R`. -/
theorem schemeDiagonal_isClosedImmersion (hI : I.FG) :
    FormalScheme.IsClosedImmersion (schemeDiagonal (R := R) (I := I) (A := A) hI) where
  base_closedEmbedding := isClosedEmbedding_diagonal_base hI
  surjective_stalkMap := (diagonal_isClosedImmersion hI).2

end CompletedTensorProduct

end
