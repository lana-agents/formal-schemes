import FormalSchemes.GeneralSeparatedTopological

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Separatedness over `Spf R` is closedness of the diagonal's image (EGA I §10.15)

`FormalSchemes/ClosedImmersionSplitMono.lean` (issue 499b) observed that the general diagonal is a
**section** of the first projection (`BothChartedFibreDatumXY.diagonal'_comp_pr₁`), and used the
retraction to discharge the *stalk* half of `FormalScheme.IsClosedImmersion` once and for all. This
file makes the same retraction pay a second time: it also discharges the *embedding* half.

The observation is elementary. If `f ≫ r = 𝟙 X` then `⇑r.base ∘ ⇑f.base = id`, so `⇑f.base` is a
homeomorphism onto its image (`Function.LeftInverse.isEmbedding`): a continuous map with a
continuous retraction is always a topological embedding. Since a closed embedding is exactly an
embedding with closed range, the whole remaining content of `FormalScheme.IsClosedImmersion` for a
split monomorphism — and hence of `BothChartedFibreDatumXY.IsSeparated` — is that the image be
**closed**:

```
IsSeparated DX σX hστX hσcX ↔
  IsClosed (Set.range ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base)
```

which is how §10.15 is normally stated — `X` is separated over `S` when `Δ(X)` is closed in
`X ×_S X`. Taken together with issue 499b, both halves of the closed-immersion predicate are now
free for the diagonal, and a separatedness proof owes exactly one topological fact.

Nothing here is specific to the diagonal until the last section: the split-mono statements of
`FormalSchemes.ClosedImmersionSplitMono` are sharpened in the same generality in which they were
stated.

## Main results

* `AlgebraicGeometry.isEmbedding_base_of_retraction`: a morphism of locally ringed spaces with a
  retraction has a base map which is a topological embedding.
* `AlgebraicGeometry.FormalScheme.isClosedImmersion_of_isClosed_range_of_retraction` and
  `FormalScheme.isClosedImmersion_iff_isClosed_range_of_isSplitMono`: for a section, being a closed
  immersion *is* having a closed image.
* `AlgebraicGeometry.FormalScheme.isClosedImmersion_of_openCover_isClosed_range`: the same, chart by
  chart over an open cover of the target.
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

/-- **A morphism of locally ringed spaces with a retraction has a base map which is a topological
embedding.** The base map of `f ≫ r = 𝟙 X` is `⇑r.base ∘ ⇑f.base = id`, so `⇑f.base` is injective
and `⇑r.base` restricts to a continuous inverse on its image.

This is the topological companion of `surjective_stalkMap_of_retraction`: the same retraction
discharges the algebraic half of `FormalScheme.IsClosedImmersion` there and the embedding half of
its topological condition here. -/
theorem isEmbedding_base_of_retraction {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (r : Y ⟶ X)
    (h : f ≫ r = 𝟙 X) : IsEmbedding ⇑f.base := by
  have key : ⇑r.base ∘ ⇑f.base = id :=
    congrArg (fun g : X ⟶ X => ⇑g.base) h
  exact Function.LeftInverse.isEmbedding (congrFun key) r.base.hom.continuous f.base.hom.continuous

namespace FormalScheme

variable {X Y : FormalScheme.{u}}

/-- **A section of a morphism of formal schemes has a base map which is a topological
embedding.** -/
theorem isEmbedding_base_of_retraction (f : X ⟶ Y) (r : Y ⟶ X) (h : f ≫ r = 𝟙 X) :
    IsEmbedding ⇑f.toLRSHom.base :=
  _root_.AlgebraicGeometry.isEmbedding_base_of_retraction f.toLRSHom r.toLRSHom
    (by rw [← comp_toLRSHom, h, id_toLRSHom])

/-- A split monomorphism of formal schemes has a base map which is a topological embedding. -/
theorem isEmbedding_base_of_isSplitMono (f : X ⟶ Y) [IsSplitMono f] :
    IsEmbedding ⇑f.toLRSHom.base :=
  isEmbedding_base_of_retraction f (retraction f) (IsSplitMono.id f)

/-- **A section of a morphism of formal schemes is a closed immersion as soon as its image is
closed.** Both halves of `FormalScheme.IsClosedImmersion` beyond closedness of the image are
supplied by the retraction: the stalk maps by `surjective_stalkMap_of_retraction` and the embedding
by `isEmbedding_base_of_retraction`. -/
theorem isClosedImmersion_of_isClosed_range_of_retraction (f : X ⟶ Y) (r : Y ⟶ X)
    (h : f ≫ r = 𝟙 X) (hrange : IsClosed (Set.range ⇑f.toLRSHom.base)) :
    IsClosedImmersion f :=
  isClosedImmersion_of_retraction f r h ⟨isEmbedding_base_of_retraction f r h, hrange⟩

/-- A split monomorphism of formal schemes whose image is closed is a closed immersion. -/
theorem isClosedImmersion_of_isClosed_range_of_isSplitMono (f : X ⟶ Y) [IsSplitMono f]
    (hrange : IsClosed (Set.range ⇑f.toLRSHom.base)) : IsClosedImmersion f :=
  isClosedImmersion_of_isClosed_range_of_retraction f (retraction f) (IsSplitMono.id f) hrange

/-- **For a split monomorphism, being a closed immersion is exactly having a closed image.** This
sharpens `isClosedImmersion_iff_isClosedEmbedding_base_of_isSplitMono`: not only is the stalk
condition free, so is the embedding half of the topological one. -/
theorem isClosedImmersion_iff_isClosed_range_of_isSplitMono (f : X ⟶ Y) [IsSplitMono f] :
    IsClosedImmersion f ↔ IsClosed (Set.range ⇑f.toLRSHom.base) :=
  ⟨fun hf => hf.base_closedEmbedding.isClosed_range,
    isClosedImmersion_of_isClosed_range_of_isSplitMono f⟩

/-- **Local on the target, for a section**: a morphism of formal schemes with a retraction is a
closed immersion as soon as its image meets each chart of an open cover of the target in a closed
set. This is the closed-range form of `isClosedImmersion_of_openCover`; both of that lemma's other
hypotheses — the per-chart embedding and the global stalk surjectivity — are supplied by the
retraction. -/
theorem isClosedImmersion_of_openCover_isClosed_range (f : X ⟶ Y) (r : Y ⟶ X)
    (h : f ≫ r = 𝟙 X) (𝒰 : OpenCover Y)
    (hrange : ∀ j, IsClosed (Set.range (Set.restrictPreimage
      (Set.range (𝒰.map j).toLRSHom.base) f.toLRSHom.base))) :
    IsClosedImmersion f :=
  isClosedImmersion_of_openCover f 𝒰
    (fun j => ⟨(isEmbedding_base_of_retraction f r h).restrictPreimage _, hrange j⟩)
    (fun y => surjective_stalkMap_of_retraction f.toLRSHom r.toLRSHom
      (by rw [← comp_toLRSHom, h, id_toLRSHom]) y)

end FormalScheme

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
