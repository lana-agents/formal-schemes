import FormalSchemes.ClosedImmersionSplitMono
import FormalSchemes.GeneralSeparated

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Separatedness over `Spf R` is a purely topological condition (EGA I §10.15)

`FormalSchemes/GeneralSeparated.lean` (issue 499) defines `BothChartedFibreDatumXY.IsSeparated` as
the statement that the scheme-level general diagonal `Δ' : X ⟶ X ×_{Spf R} X` is a closed immersion,
i.e. — unfolding `FormalScheme.IsClosedImmersion` — that its base map is a closed embedding **and**
that all of its stalk maps are surjective. Its local-on-target reduction
`isSeparated_of_diagonal_cover` accordingly carries both a per-chart topological hypothesis and a
global stalk hypothesis.

This file discharges the stalk hypothesis **once and for all, for every datum**. The general
diagonal is a section of the first projection (`diagonal'_comp_pr₁`, issue 487), so
`FormalSchemes/ClosedImmersionSplitMono.lean` applies: its stalk maps are surjective for purely
formal reasons. Separatedness of a datum-presented formal scheme is therefore *equivalent* to the
topological statement that the diagonal's base map is a closed embedding.

This is the general analogue of the Tate-specific stalk computation
`tateSelfProductDiagonal_surjective_stalkMap` (issue 410), which established the same fact for the
two-chart Tate model by descending along the charts to the affine diagonal. Nothing of that shape is
needed: no cover of the source, no affine section surjectivity, no Noetherian hypothesis.

## Main results

* `BothChartedFibreDatumXY.surjective_stalkMap_diagonal'` and `_schemeDiagonal'`: the general
  diagonal has surjective stalk maps, unconditionally.
* `BothChartedFibreDatumXY.isSeparated_of_isClosedEmbedding_diagonal_base`: a closed-embedding base
  map suffices for separatedness.
* `BothChartedFibreDatumXY.isSeparated_of_diagonal_cover_base`: the stalk-free strengthening of
  `isSeparated_of_diagonal_cover` — only the per-chart topological hypothesis remains.
* `BothChartedFibreDatumXY.isSeparated_iff_isClosedEmbedding_diagonal_base`: **separatedness is
  exactly the topological condition.**

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

/-- **The general diagonal has surjective stalk maps**, for an arbitrary datum and with no
hypotheses: it is a section of the first projection (`diagonal'_comp_pr₁`), and a morphism of
locally ringed spaces with a retraction has surjective stalk maps. -/
theorem surjective_stalkMap_diagonal' (x : (diagonalDatum DX σX hστX hσcX).xGlued) :
    Function.Surjective ⇑((diagonal' DX σX hστX hσcX).stalkMap x).hom :=
  surjective_stalkMap_of_retraction _
    ((diagonalDatum DX σX hστX hσcX).pr₁
      (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX))
    (diagonal'_comp_pr₁ DX σX hστX hσcX) x

/-- The scheme-level general diagonal has surjective stalk maps: its underlying locally-ringed-space
morphism is `diagonal'`. -/
theorem surjective_stalkMap_schemeDiagonal' (x : (diagonalDatum DX σX hστX hσcX).xGlued) :
    Function.Surjective ⇑((schemeDiagonal' DX σX hστX hσcX).toLRSHom.stalkMap x).hom :=
  surjective_stalkMap_diagonal' DX σX hστX hσcX x

/-- **A closed-embedding diagonal base map suffices for separatedness.** The stalk half of the
closed-immersion predicate is automatic (`surjective_stalkMap_schemeDiagonal'`), so only the
topological half has to be verified. -/
theorem isSeparated_of_isClosedEmbedding_diagonal_base
    (hbase : IsClosedEmbedding ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base) :
    IsSeparated DX σX hστX hσcX where
  base_closedEmbedding := hbase
  surjective_stalkMap := surjective_stalkMap_schemeDiagonal' DX σX hστX hσcX

/-- **Separatedness is local on the target of the diagonal, topologically.** This is the stalk-free
strengthening of `isSeparated_of_diagonal_cover`: over the affine cover of `X ×_{Spf R} X` only the
per-chart closed-embedding hypothesis remains, the global stalk hypothesis being automatic.

For the Tate curve model this means that issue 410's stalk computation is not needed at all: the
per-chart closed embeddings of issue 424 are the whole of separatedness. -/
theorem isSeparated_of_diagonal_cover_base
    (hbase : ∀ j, IsClosedEmbedding (Set.restrictPreimage
      (Set.range
        ((diagonalDatum DX σX hστX hσcX).generalFibreProduct.affineCover.map j).toLRSHom.base)
      (schemeDiagonal' DX σX hστX hσcX).toLRSHom.base)) :
    IsSeparated DX σX hστX hσcX :=
  isSeparated_of_diagonal_cover DX σX hστX hσcX hbase
    (surjective_stalkMap_schemeDiagonal' DX σX hστX hσcX)

/-- **Separatedness over `Spf R` is exactly the topological condition** that the diagonal's base map
is a closed embedding (EGA I §10.15). The forward direction projects out the topological half of the
closed-immersion predicate; the backward direction is
`isSeparated_of_isClosedEmbedding_diagonal_base`. -/
theorem isSeparated_iff_isClosedEmbedding_diagonal_base :
    IsSeparated DX σX hστX hσcX ↔
      IsClosedEmbedding ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base :=
  ⟨fun hsep => hsep.base_closedEmbedding, isSeparated_of_isClosedEmbedding_diagonal_base _ _ _ _⟩

end BothChartedFibreDatumXY

end AlgebraicGeometry

end
