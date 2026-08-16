import FormalSchemes.AdicMorphism
import FormalSchemes.ClosedImmersion
import FormalSchemes.ClosedImmersionSections

set_option linter.style.header false

/-!
# The closed formal subscheme as a closed immersion of formal schemes

`FormalSchemes/ClosedImmersion.lean` introduced the predicate `FormalScheme.IsClosedImmersion` on a
morphism of formal schemes. `FormalSchemes/AdicMorphism.lean` built the closed formal subscheme
`Spf (R ⧸ a) ⟶ Spf R` attached to an adically closed ideal `a` (EGA I §10.14) as a morphism of
*locally ringed spaces* (`closedFormalSubscheme`), and `FormalSchemes/ClosedImmersionSections.lean`
proved it satisfies both closed-immersion conditions, but phrased as the raw conjunction on
`FormalSpectrum.map` / `presheafedSpaceMap` of the surjective quotient map `R → R ⧸ a`.

This file bridges the two, exactly as `FormalSchemes/ClosedImmersionAffine.lean` does for the affine
diagonal: it first packages `closedFormalSubscheme` as a `FormalScheme.Hom`
(`closedSubschemeSchemeHom`) and then repackages the conjunction through the new predicate
(`closedSubschemeSchemeHom_isClosedImmersion`), so downstream consumers can cite a single
`FormalScheme.IsClosedImmersion` fact instead of re-deriving the
closed-embedding-and-surjective-stalks conjunction. Since `R ⧸ a` carries its adic topology only
through an internal `letI` in `closedFormalSubscheme`, both declarations reinstate those instances
in their signatures.

The bridge is definitional glue:
`closedSubschemeSchemeHom = FormalScheme.Hom.mk closedFormalSubscheme` (so its underlying
locally-ringed-space morphism is `closedFormalSubscheme`, hence its base map is
`FormalSpectrum.map (Ideal.Quotient.mk a)` and its stalk maps are those of `presheafedSpaceMap`).
Hence the closed-embedding half is `isClosedEmbedding_closedSubschemeBase` and the
stalk-surjectivity half is the second component of `closedFormalSubscheme_isClosedImmersion`.

## Main results

* `closedSubschemeSchemeHom`: the closed formal subscheme `Spf (R ⧸ a) ⟶ Spf R` as a morphism of
  formal schemes.
* `closedSubschemeSchemeHom_isClosedImmersion`: it is a `FormalScheme.IsClosedImmersion` — the
  §10.14 closed subscheme in the reusable predicate.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.14.
* [The Stacks Project, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I] (a : Ideal R)

/-- The **closed formal subscheme** `Spf (R ⧸ a) ⟶ Spf R` attached to an adically closed ideal `a`
of an adic ring `R` (EGA I §10.14), packaged as a morphism of formal schemes: the
`FormalScheme.Hom` wrapper of the locally-ringed-space morphism `closedFormalSubscheme`. The
quotient `R ⧸ a` is given its adic topology (and the resulting `IsAdicRing` instance) as in
`closedFormalSubscheme`. -/
def closedSubschemeSchemeHom (ha : (Ideal.Quotient.mk a).AdicKerClosed I) :
    letI : TopologicalSpace (R ⧸ a) := (I.map (Ideal.Quotient.mk a)).adicTopology
    letI := isAdicRing_quotient I a ha
    FormalScheme.Spf (I.map (Ideal.Quotient.mk a)) ⟶ FormalScheme.Spf I :=
  letI : TopologicalSpace (R ⧸ a) := (I.map (Ideal.Quotient.mk a)).adicTopology
  letI := isAdicRing_quotient I a ha
  FormalScheme.Hom.mk (closedFormalSubscheme I a ha)

/-- **The closed formal subscheme `Spf (R ⧸ a) ⟶ Spf R` is a closed immersion of formal schemes**
(EGA I §10.14). This packages the two-part conjunction `closedFormalSubscheme_isClosedImmersion`
(a closed topological embedding of the base map, `isClosedEmbedding_closedSubschemeBase`, together
with surjective stalk maps, the inducing ring hom being the surjective quotient map
`Ideal.Quotient.mk a`) into the `FormalScheme.IsClosedImmersion` predicate for the formal-scheme
morphism `closedSubschemeSchemeHom`. -/
theorem closedSubschemeSchemeHom_isClosedImmersion
    (ha : (Ideal.Quotient.mk a).AdicKerClosed I) (hI : I.FG) :
    letI : TopologicalSpace (R ⧸ a) := (I.map (Ideal.Quotient.mk a)).adicTopology
    letI := isAdicRing_quotient I a ha
    FormalScheme.IsClosedImmersion (closedSubschemeSchemeHom I a ha) :=
  letI : TopologicalSpace (R ⧸ a) := (I.map (Ideal.Quotient.mk a)).adicTopology
  letI := isAdicRing_quotient I a ha
  { base_closedEmbedding := isClosedEmbedding_closedSubschemeBase I a
    surjective_stalkMap := (closedFormalSubscheme_isClosedImmersion I a hI).2 }

end
