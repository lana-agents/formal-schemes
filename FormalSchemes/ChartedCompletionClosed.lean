import FormalSchemes.ChartedCompletionSupport

set_option linter.style.header false

/-!
# The image of `X_{/Y} ⟶ X` is closed, at an arbitrary index (EGA I, 10.8)

`FormalSchemes.ChartedCompletionRange` computed the image of `X_{/Y} ⟶ X` for a
`AlgebraicGeometry.ChartedCompletionDatum` as `⋃ i, (specι i) '' V (K i)`, and
`FormalSchemes.ChartedCompletionSupport` read that image on each chart:

```
(specι i)⁻¹ (range (D.toScheme).base) = V (K i)
```

This file draws the topological conclusion: **the image is closed**. That is the statement EGA I
10.8 makes — *the completion of `X` along `Y` is supported on the closed subset `Y`* — and it is
now available for a scheme glued from arbitrarily many affine charts rather than from two.

## The argument, which is `CompletionTwoPatchClosed`'s with a `⋃`

Closedness is local on an open cover and the charts of `specGlued` are open immersions that cover
it, so it suffices that each chart preimage be closed — which is what the support statement gives,
both being zero loci. The proof runs that on the **complement**, which is why no covering
machinery appears: `Sᶜ` is the union of the images of its own chart preimages (joint surjectivity,
and nothing more), each preimage is the complement of a zero locus hence open, and each `specι i`
is an open map. Two patches down this is a two-term `∪`; here it is a `⋃` and `isOpen_iUnion`.

`FormalSchemes.CompletionTwoPatchClosed` records, and a reader should not re-derive, why
`TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage` is deliberately not used (it is stated for
`Opens` and *subtype* preimages, so consuming it means assembling an `IsOpenCover` and transporting
each preimage across a homeomorphism), and two shortcuts that cannot work: the source is
quasi-compact but the glued space is not T1, so compact does not give closed; and
`(specι i) '' V (K i)` is not closed on its own, `specι i` being an *open* immersion. Any correct
argument must use `hθ`, and this one does — through the chart preimages.

## Scope

**`Topology.IsClosedEmbedding` is not proved here, and no longer needs to be priced.** It is
`Topology.IsEmbedding` plus the closed range this file supplies, and the embedding half is
`AlgebraicGeometry.ChartedCompletionDatum.isClosedEmbedding_toScheme_base`
(`FormalSchemes.ChartedCompletionEmbedding`), a downstream leaf. The mixed-chart case that made
the statement look expensive — two points in *different* charts of `X_{/Y}` with one image in `X`
— is discharged there by the covering criterion, off
`formalCompletion.mem_range_basicOpenImmersion`, the converse of the overlap analysis of
`FormalSchemes.CompletionTwoPatchDoubled`.

## Main results

* `AlgebraicGeometry.ChartedCompletionDatum.isClosed_range_toScheme_base`: **the image of
  `X_{/Y} ⟶ X` is closed in `X`.**
* `AlgebraicGeometry.isClosed_range_projectiveLineCompletionToScheme_base` and
  `AlgebraicGeometry.range_projectiveLineCompletionToScheme_base_nonempty`: the witness. That the
  image is not *everything* is
  `AlgebraicGeometry.range_projectiveLineCompletionToScheme_base_ne_univ`, which is one file
  earlier because it needs only the support statement; no alias for it is added here.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace ChartedCompletionDatum

variable (D : ChartedCompletionDatum.{u})

/-- **The charts of the glued ambient scheme cover it**, read at this datum. -/
theorem specGlued_jointly_surjective (x : D.specGlued) :
    ∃ (i : D.J) (y : Spec.locallyRingedSpaceObj (CommRingCat.of (D.C i))),
      (D.specι i).base y = x :=
  D.toChartedSchemeDatum.specGlued_jointly_surjective x

/-- **The glued completion is supported on a closed subset** (EGA I, 10.8): the image of
`X_{/Y} ⟶ X` is closed in the glued scheme `X`.

Every chart preimage of the image is a zero locus
(`ChartedCompletionDatum.preimage_range_toScheme_base`), so every chart preimage of the
*complement* is open; the complement is the union of their images under the chart open immersions,
by joint surjectivity, hence open. -/
theorem isClosed_range_toScheme_base : IsClosed (Set.range ⇑D.toScheme.base) := by
  set S := Set.range ⇑D.toScheme.base with hS
  rw [← isOpen_compl_iff]
  have hpre : ∀ i : D.J, ⇑(D.specι i).base ⁻¹' Sᶜ =
      (PrimeSpectrum.zeroLocus ((D.K i : Ideal (D.C i)) : Set (D.C i)))ᶜ := by
    intro i
    rw [Set.preimage_compl, hS, D.preimage_range_toScheme_base i]
    rfl
  have hcover : Sᶜ = ⋃ i : D.J, ⇑(D.specι i).base '' (⇑(D.specι i).base ⁻¹' Sᶜ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, y, rfl⟩ := D.specGlued_jointly_surjective x
      exact Set.mem_iUnion.mpr ⟨i, y, hx, rfl⟩
    · intro hx
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact hy
  rw [hcover]
  refine isOpen_iUnion fun i => ?_
  rw [hpre i]
  exact (D.toChartedSchemeDatum.specι_isOpenImmersion i).base_open.isOpenMap _
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

end ChartedCompletionDatum

/-! ### The witness

`IsClosed` is true of `∅` and of the whole space, so the theorem above says nothing until an
instance is exhibited in which the image is neither. The projective line over a nontrivial `R`,
completed at the origin of its first chart, is one: the image is the first chart's `V (X)`, which
is non-empty because `(X)` is a proper ideal, and it misses the entire second chart. -/

section Witness

open Polynomial

variable (R : Type u) [CommRing R]

/-- **The image is closed**, for the projective line completed at the origin of its first chart. -/
theorem isClosed_range_projectiveLineCompletionToScheme_base :
    IsClosed (Set.range ⇑(projectiveLineCompletionToScheme R).base) :=
  (projectiveLineDatum R).isClosed_range_toScheme_base

/-- **The image is not empty**: `(X)` is a proper ideal of `R[X]`, so `V (X)` has a point, and its
image under the first chart is in the image of `X_{/Y} ⟶ X`. -/
theorem range_projectiveLineCompletionToScheme_base_nonempty [Nontrivial R] :
    (Set.range ⇑(projectiveLineCompletionToScheme R).base).Nonempty := by
  obtain ⟨p, hp⟩ : (PrimeSpectrum.zeroLocus
      ((Ideal.span {(X : R[X])} : Ideal R[X]) : Set R[X])).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun he => span_X_ne_top R (PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp he)
  exact ⟨((projectiveLineDatum R).specι ⟨false⟩).base p,
    (preimage_range_projectiveLineCompletionToScheme_base_false R).ge hp⟩

end Witness

end AlgebraicGeometry

end
