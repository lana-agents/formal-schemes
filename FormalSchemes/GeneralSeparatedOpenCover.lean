import FormalSchemes.GeneralSeparatedRange

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The per-chart separatedness criterion over an *arbitrary* open cover (EGA I §10.15)

`FormalSchemes/GeneralSeparated.lean` (issue 499), `FormalSchemes/GeneralSeparatedTopological.lean`
(issue 549) and `FormalSchemes/GeneralSeparatedRange.lean` (issue 764) each reduce
`BothChartedFibreDatumXY.IsSeparated` to a per-chart condition on the diagonal — but all three
quantify over one specific cover, `generalFibreProduct.affineCover`. That cover
(`FormalSchemes/OpenCover.lean`) is indexed by the **points** of the space, and its chart at `x` is
`AffineChart.choice`, a `Classical.choice` drawn from `FormalScheme.exists_openImmersion`. Its
charts, and in particular the ranges of its maps, are opaque, so a concrete `X` has nothing to say
about them.

The closed-immersion criterion those three are built on has no such restriction:
`FormalScheme.isClosedImmersion_of_openCover` (issue 492) and its closed-range form take an
**arbitrary** `𝒰 : FormalScheme.OpenCover`. This file passes that generality through to the datum
layer, and then one step further:

* over an arbitrary `𝒰 : FormalScheme.OpenCover`, in the three strengths of the existing family;
* over an arbitrary **topological** open cover — a family `U : ι → Opens |X ×_{Spf R} X|` with
  `TopologicalSpace.IsOpenCover U` — which is possible because, after issue 764, closedness of the
  diagonal's image is the *entire* content of separatedness, and closedness of a set is local on
  any open cover of the space whatsoever. No cover by formal schemes is needed.

The last form is the one a concrete instance already has. `TateDiagonalClosedCover.lean` builds
`tateSelfProductChartCover : ULift (Bool × Bool) → Opens …` together with a
`TopologicalSpace.IsOpenCover` witness, indexed by the chart index type; the three-chart open-cover
datum of `FormalSchemes/ThreeChartCoverDatum.lean` produces data of the same shape from its own glue
data. Neither is a `FormalScheme.OpenCover`, and neither can be obtained from `affineCover`.

The three existing criteria are recovered as the `𝒰 := affineCover` special cases of the lemmas
here; they are left in place untouched.

## Main results

* `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_isOpenCover_isClosed_range` and
  `isSeparated_iff_isOpenCover_isClosed_range`: **separatedness from a purely topological open
  cover** of `X ×_{Spf R} X`, each chart owing only that the diagonal's image meets it in a closed
  set.
* `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_openCover`,
  `isSeparated_of_openCover_base`, `isSeparated_of_openCover_isClosed_range`: the arbitrary-cover
  forms of `isSeparated_of_diagonal_cover`, `isSeparated_of_diagonal_cover_base` and
  `isSeparated_of_diagonal_cover_isClosed_range`.

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

/-! ### Over an arbitrary topological open cover -/

section IsOpenCover

variable {ι : Type*}
  {U : ι → TopologicalSpace.Opens (diagonalDatum DX σX hστX hσcX).generalFibreProduct}

/-- **Separatedness from a purely topological open cover of `X ×_{Spf R} X`.** Given any family of
opens covering the fibre product, `X` is separated over `Spf R` as soon as the diagonal's image
meets each one in a closed set.

This is the weakest form of the §10.15 criterion available: by issue 764 the whole content of
separatedness is that `Set.range Δ` be closed, and closedness is local on an arbitrary open cover
(`TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage`). Nothing about the cover need be
compatible with the formal-scheme structure — in particular it need not be a
`FormalScheme.OpenCover`, let alone the point-indexed `affineCover` that
`isSeparated_of_diagonal_cover_isClosed_range` asks for. -/
theorem isSeparated_of_isOpenCover_isClosed_range (hU : TopologicalSpace.IsOpenCover U)
    (hrange : ∀ j, IsClosed (Set.range ((U j : Set _).restrictPreimage
      ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base))) :
    IsSeparated DX σX hστX hσcX :=
  isSeparated_of_isClosed_range_diagonal_base DX σX hστX hσcX
    (hU.isClosed_iff_coe_preimage.mpr fun j => by
      have h := hrange j
      rw [Set.range_restrictPreimage] at h
      exact h)

/-- **Separatedness *is* the per-chart closedness statement, over any open cover.** The sharp form
of `isSeparated_of_isOpenCover_isClosed_range`: the forward direction takes the globally closed
image of the diagonal (`isSeparated_iff_isClosed_range_diagonal_base`) and restricts it to each
chart. -/
theorem isSeparated_iff_isOpenCover_isClosed_range (hU : TopologicalSpace.IsOpenCover U) :
    IsSeparated DX σX hστX hσcX ↔
      ∀ j, IsClosed (Set.range ((U j : Set _).restrictPreimage
        ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base)) := by
  refine ⟨fun hsep j => ?_, isSeparated_of_isOpenCover_isClosed_range DX σX hστX hσcX hU⟩
  have h := hU.isClosed_iff_coe_preimage.mp hsep.base_closedEmbedding.isClosed_range j
  rw [← Set.range_restrictPreimage] at h
  exact h

end IsOpenCover

/-! ### Over an arbitrary cover by formal schemes -/

section OpenCover

variable (𝒰 : FormalScheme.OpenCover (diagonalDatum DX σX hστX hσcX).generalFibreProduct)

/-- **Separatedness is local on the target of the diagonal, over any cover by formal schemes.**
This is `isSeparated_of_diagonal_cover` with the point-indexed `affineCover` replaced by an
arbitrary `𝒰`; that lemma is the special case `𝒰 := affineCover`. The generality is inherited
directly from `FormalScheme.isClosedImmersion_of_openCover`, which always had it. -/
theorem isSeparated_of_openCover
    (hbase : ∀ j, IsClosedEmbedding (Set.restrictPreimage
      (Set.range (𝒰.map j).toLRSHom.base)
      ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base))
    (hstalk : ∀ y,
      Function.Surjective ⇑((schemeDiagonal' DX σX hστX hσcX).toLRSHom.stalkMap y).hom) :
    IsSeparated DX σX hστX hσcX :=
  FormalScheme.isClosedImmersion_of_openCover (schemeDiagonal' DX σX hστX hσcX) 𝒰 hbase hstalk

/-- **The stalk-free form over an arbitrary cover**: `isSeparated_of_diagonal_cover_base` with
`affineCover` replaced by an arbitrary `𝒰`. The stalk hypothesis is discharged by
`surjective_stalkMap_schemeDiagonal'`, which holds for every datum (issue 549). -/
theorem isSeparated_of_openCover_base
    (hbase : ∀ j, IsClosedEmbedding (Set.restrictPreimage
      (Set.range (𝒰.map j).toLRSHom.base)
      ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base)) :
    IsSeparated DX σX hστX hσcX :=
  isSeparated_of_openCover DX σX hστX hσcX 𝒰 hbase
    (surjective_stalkMap_schemeDiagonal' DX σX hστX hσcX)

/-- **The closed-range form over an arbitrary cover**:
`isSeparated_of_diagonal_cover_isClosed_range` with `affineCover` replaced by an arbitrary `𝒰`.
Each chart owes only that the diagonal's image meets it in a closed set; the embedding half is free
for every datum (issue 764). -/
theorem isSeparated_of_openCover_isClosed_range
    (hrange : ∀ j, IsClosed (Set.range (Set.restrictPreimage
      (Set.range (𝒰.map j).toLRSHom.base)
      ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base))) :
    IsSeparated DX σX hστX hσcX :=
  isSeparated_of_openCover_base DX σX hστX hσcX 𝒰 fun j =>
    ⟨(isEmbedding_schemeDiagonal'_base DX σX hστX hσcX).restrictPreimage _, hrange j⟩

end OpenCover

end BothChartedFibreDatumXY

end AlgebraicGeometry

end
