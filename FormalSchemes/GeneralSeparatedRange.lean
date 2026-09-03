import FormalSchemes.GeneralSeparatedTopological

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Separatedness over `Spf R` is closedness of the diagonal's image (EGA I §10.15)

`FormalSchemes/ClosedImmersionSplitMono.lean` (issues 499b, 1545) proves that a morphism of formal
schemes with a retraction owes `FormalScheme.IsClosedImmersion` nothing beyond closedness of its
image: the retraction discharges both the stalk half (`surjective_stalkMap_of_retraction`) and the
embedding half of the topological condition (`isEmbedding_base_of_retraction`). This file is the
consequence for the general diagonal, which is a **section** of the first projection
(`BothChartedFibreDatumXY.diagonal'_comp_pr₁`):

```
IsSeparated DX σX hστX hσcX ↔
  IsClosed (Set.range ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base)
```

which is how §10.15 is normally stated — `X` is separated over `S` when `Δ(X)` is closed in
`X ×_S X`. A separatedness proof owes exactly one topological fact.

## Main results

* `AlgebraicGeometry.BothChartedFibreDatumXY.isEmbedding_diagonal'_base` and
  `_schemeDiagonal'_base`: the general diagonal is a topological embedding, unconditionally.
* `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_iff_isClosed_range_diagonal_base`:
  **separatedness is exactly closedness of the diagonal's image.**
* `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_diagonal_cover_isClosed_range`: the
  per-chart criterion, with the closed-embedding hypothesis of
  `isSeparated_of_diagonal_cover_base` weakened to closedness of a range.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum Topology
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {BX : Type u} [CommRing BX] [Algebra R BX]
variable (DX : AffineChartedFibreDatumX R I hI BX)
variable
  (σX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (DX.A i'))) (DX.g i' i'' * DX.g i' i)))
  (hστX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (DX.g i' i'') (DX.g i' i) hI) =
      (furtherLocFst I (DX.g i i') (DX.g i i'') hI).comp (DX.τ i i' h1).symm.toAlgHom)
  (hσcX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
      (σX i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'')))

/-- **The general diagonal is a topological embedding**, for an arbitrary datum and with no
hypotheses: it is a section of the first projection (`diagonal'_comp_pr₁`), and a morphism of
locally ringed spaces with a retraction has an embedding base map.

This is the topological twin of `surjective_stalkMap_diagonal'`, proved from the same retraction. -/
theorem isEmbedding_diagonal'_base :
    IsEmbedding ⇑(diagonal' DX σX hστX hσcX).base :=
  isEmbedding_base_of_retraction _
    ((diagonalDatum DX σX hστX hσcX).pr₁
      (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX))
    (diagonal'_comp_pr₁ DX σX hστX hσcX)

/-- The scheme-level general diagonal is a topological embedding: its underlying
locally-ringed-space morphism is `diagonal'`. -/
theorem isEmbedding_schemeDiagonal'_base :
    IsEmbedding ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base :=
  isEmbedding_diagonal'_base DX σX hστX hσcX

/-- **A closed diagonal image suffices for separatedness.** Both the stalk half
(`surjective_stalkMap_schemeDiagonal'`) and the embedding half
(`isEmbedding_schemeDiagonal'_base`) of the closed-immersion predicate are automatic, so only
closedness of the image has to be verified. -/
theorem isSeparated_of_isClosed_range_diagonal_base
    (hrange : IsClosed (Set.range ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base)) :
    IsSeparated DX σX hστX hσcX :=
  isSeparated_of_isClosedEmbedding_diagonal_base DX σX hστX hσcX
    ⟨isEmbedding_schemeDiagonal'_base DX σX hστX hσcX, hrange⟩

/-- **Separatedness over `Spf R` is exactly the statement that the diagonal's image is closed**
(EGA I §10.15): `X` is separated over `Spf R` precisely when `Δ(X)` is closed in `X ×_{Spf R} X`.

This is the sharp form of `isSeparated_iff_isClosedEmbedding_diagonal_base`: the diagonal is always
an embedding with surjective stalk maps, so closedness of its image is the entire content of the
definition. -/
theorem isSeparated_iff_isClosed_range_diagonal_base :
    IsSeparated DX σX hστX hσcX ↔
      IsClosed (Set.range ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base) :=
  ⟨fun hsep => hsep.base_closedEmbedding.isClosed_range,
    isSeparated_of_isClosed_range_diagonal_base DX σX hστX hσcX⟩

/-- **Separatedness is local on the target of the diagonal, as a statement about ranges.** This is
the drop-in weakening of `isSeparated_of_diagonal_cover_base`: over the affine cover of
`X ×_{Spf R} X` each chart owes only that the diagonal's image *meets it in a closed set*, rather
than that the diagonal restricts to a closed embedding there.

The embedding half of each per-chart hypothesis is free for the same reason the global one is: the
diagonal is an embedding (`isEmbedding_schemeDiagonal'_base`), and a restriction to the preimage of
a subset of the target stays one (`Topology.IsEmbedding.restrictPreimage`). -/
theorem isSeparated_of_diagonal_cover_isClosed_range
    (hrange : ∀ j, IsClosed (Set.range (Set.restrictPreimage
      (Set.range
        ((diagonalDatum DX σX hστX hσcX).generalFibreProduct.affineCover.map j).toLRSHom.base)
      (schemeDiagonal' DX σX hστX hσcX).toLRSHom.base))) :
    IsSeparated DX σX hστX hσcX :=
  isSeparated_of_diagonal_cover_base DX σX hστX hσcX fun j =>
    ⟨(isEmbedding_schemeDiagonal'_base DX σX hστX hσcX).restrictPreimage _, hrange j⟩

end BothChartedFibreDatumXY

end AlgebraicGeometry

end
