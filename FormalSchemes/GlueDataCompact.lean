import FormalSchemes.Gluing

set_option linter.style.header false

/-!
# Quasi-compactness of a glued formal scheme

A `FormalScheme.GlueData` `D` presents its glued formal scheme `D.gluedFormalScheme` as covered by
the open images of its pieces (`FormalScheme.GlueData.ι_jointly_surjective`). If the index type is
**finite** and every piece is **quasi-compact**, that is a finite cover by quasi-compact subsets, so
the glued object is quasi-compact.

This is the formal-scheme analogue of Mathlib's `AlgebraicGeometry.Scheme.OpenCover.compactSpace`,
which is unavailable here: the objects of this development are `LocallyRingedSpace`s carrying a
`FormalScheme` structure, not `AlgebraicGeometry.Scheme`s, so none of Mathlib's `Scheme.Cover` API
applies to them.

## Why this lemma lives in its own file, directly above `FormalSchemes/Gluing.lean`

It has consumers on unrelated branches of the development — the glued formal *completion* of
`FormalSchemes/CompletionGlueTwoPatch.lean` and the glued formal Tate annulus of
`FormalSchemes/TateGlueTwoPatch.lean`, neither of which imports the other — and it will apply
unchanged to the arbitrary-index completion glue datum when that exists, since nothing below is
special to a two-element index. Putting it in any one of those leaves would put it out of reach of
the others.

## Main results

* `AlgebraicGeometry.FormalScheme.GlueData.compactSpace`: a formal scheme glued from finitely many
  quasi-compact pieces is quasi-compact.

## Implementation note

The hypothesis is stated as `∀ i, CompactSpace (D.toLocallyRingedSpaceGlueData.U i)`, whose sort
coercion goes through `LocallyRingedSpace`'s `CoeSort`, while `isCompact_range` asks for
`CompactSpace ↑↑(…).toPresheafedSpace`. The two are definitionally equal but **not reducibly** so,
and instance search works up to reducible transparency, so the hypothesis does not discharge the
side goal by itself. The `haveI … := H i` in the proof is a type ascription, which is checked at
default transparency; that is what bridges the gap. It is load-bearing, not decoration.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [The Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY)
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormalScheme.GlueData

/-- **A formal scheme glued from finitely many quasi-compact pieces is quasi-compact.** The images
of the pieces cover the glued object (`ι_jointly_surjective`), each is the range of a continuous map
out of a compact space, and a finite union of compact sets is compact. -/
theorem compactSpace (D : FormalScheme.GlueData.{u})
    [Finite D.toLocallyRingedSpaceGlueData.J]
    (H : ∀ i, CompactSpace (D.toLocallyRingedSpaceGlueData.U i)) :
    CompactSpace D.gluedFormalScheme.toLocallyRingedSpace := by
  constructor
  have h : ⋃ i, Set.range (D.ι i).base =
      (Set.univ : Set D.gluedFormalScheme.toLocallyRingedSpace) := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x
    exact Set.mem_iUnion.2 ⟨i, y, hy⟩
  rw [← h]
  refine isCompact_iUnion fun i => ?_
  haveI : CompactSpace ↑↑(D.toLocallyRingedSpaceGlueData.U i).toPresheafedSpace := H i
  exact isCompact_range (D.ι i).base.hom.continuous

end AlgebraicGeometry.FormalScheme.GlueData
