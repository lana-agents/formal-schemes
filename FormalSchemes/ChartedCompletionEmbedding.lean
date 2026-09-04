import FormalSchemes.ChartedCompletionClosed

set_option linter.style.header false

/-!
# `X_{/Y} ⟶ X` is a closed embedding, at an arbitrary index (EGA I, 10.8)

For a `AlgebraicGeometry.ChartedCompletionDatum` — an arbitrary family of affine charts with
unrelated coordinate rings, each carrying an ideal of its own — this file proves that the
canonical morphism `X_{/Y} ⟶ X` from the glued formal completion to the glued scheme is a
**closed embedding on underlying spaces**. That is the statement EGA I 10.8 makes: the completion
of `X` along `Y` has `Y` itself as its underlying space.

The affine case has been available since the beginning, as
`formalCompletion.isClosedEmbedding_toSpec_base`, and the two-patch case is
`AlgebraicGeometry.isClosedEmbedding_completionTwoPatchToScheme_base`
(`FormalSchemes.CompletionTwoPatchEmbedding`). The arbitrary-index line stopped one step short:
`FormalSchemes.ChartedCompletionRange` computed the image, `FormalSchemes.ChartedCompletionSupport`
read it chart by chart, and `FormalSchemes.ChartedCompletionClosed` showed it is closed, but none
of them says the map is injective, let alone a homeomorphism onto that image.

## The argument, which is the two-patch one with the scaffolding deleted

`Topology.IsClosedEmbedding` is `Topology.IsEmbedding` together with a closed range, and the
closed range is `ChartedCompletionDatum.isClosed_range_toScheme_base`, so the whole content is the
embedding. It comes from `isEmbedding_of_iSup_eq_top_of_preimage_subset_range`, which
asks for an open cover of the **target**, a family of maps into the **source** whose ranges cover
the corresponding preimages, and that each composite is an embedding. Injectivity is then
`.injective` of the result and never has to be proved by hand — which matters, because the
mixed-chart case is the only one with content and the covering lemma discharges it as part of the
same bookkeeping that handles the cover.

Two patches down, that lemma's demand for a *family of types* forced a `Bool`-indexed encoding of
the two charts, four `private` declarations of pure scaffolding. Here `ChartedCompletionDatum.chart`
is already a genuine dependent family, so none of it is needed and the file is shorter than the
special case it generalises.

## The step with content

`ChartedCompletionDatum.preimage_range_specι_subset`: a point of `X_{/Y}` lying over the `i`-th
chart of `X` is in the `i`-th chart of `X_{/Y}`. Given such a point in the `j`-th chart with
`j ≠ i`, its image under `formalCompletion.toSpec` lies in `D (g j i)`
(`ChartedCompletionDatum.preimage_range_specι`), hence the point itself lies in the completed
basic open (`formalCompletion.mem_range_basicOpenImmersion`), and
`ChartedCompletionDatum.completion_glue_condition` carries it over into the `i`-th chart.

Note that `ChartedCompletionDatum.preimage_range_specι` is the lemma to use rather than
`ChartedSchemeDatum.preimage_range_specι`: the latter is stated at
`ChartedCompletionDatum.toChartedSchemeDatum`, so its `g` is spelled through that projection and
the rewrite fails on a goal spelled with this datum's own `g`, reporting a type-correctness error
that reads like a transparency problem and is not one.

## Scope

**The scheme-theoretic closed immersion is not attempted**, exactly as in the two-patch file:
everything here is about underlying topological spaces, and a closed immersion additionally asks
for surjectivity of the map of structure sheaves on stalks. `FormalScheme.IsClosedImmersion` is a
predicate on morphisms of *formal* schemes, whose target here is an honest scheme; that mismatch
has to be resolved before the question can be posed.

Also out of scope, and unchanged by this file: whether `ChartedCompletionDatum.completionGlued` is
affine (`FormalSchemes.CompletionTwoPatchDoubled` explains why no topological argument can decide
it), the universal property of the completion, and the stalk half of 10.8.

## Main results

* `AlgebraicGeometry.ChartedCompletionDatum.preimage_range_specι_subset`: **a point of `X_{/Y}`
  lying over a chart of `X` is in the corresponding chart of `X_{/Y}`.**
* `AlgebraicGeometry.ChartedCompletionDatum.isEmbedding_toScheme_comp_completionι`: on each chart
  the morphism is the affine `formalCompletion.toSpec` followed by an open immersion, hence an
  embedding.
* `AlgebraicGeometry.ChartedCompletionDatum.isEmbedding_toScheme_base`,
  `..isClosedEmbedding_toScheme_base` and `..injective_toScheme_base`: **`X_{/Y} ⟶ X` is a closed
  embedding**, and in particular injective.
* `AlgebraicGeometry.isClosedEmbedding_projectiveLineCompletionToScheme_base` and
  `AlgebraicGeometry.not_surjective_projectiveLineCompletionToScheme_base`: the witness, and that
  the closed subspace it embeds onto is a proper one.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory Topology TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace ChartedCompletionDatum

variable (D : ChartedCompletionDatum.{u})

/-! ### The chart preimages of `X_{/Y} ⟶ X` -/

/-- **A point of `X_{/Y}` lying over the `i`-th chart of `X` is in the `i`-th chart of `X_{/Y}`.**

The point lies in some chart `j` of `X_{/Y}`; if `j = i` there is nothing to do. Otherwise its
image under `formalCompletion.toSpec` lies in the preimage of the `i`-th chart of `X` inside the
`j`-th, which is `D (g j i)` by `ChartedCompletionDatum.preimage_range_specι`, so the point itself
lies in the completed basic open by `formalCompletion.mem_range_basicOpenImmersion`, and
`ChartedCompletionDatum.completion_glue_condition` carries it into the `i`-th chart of `X_{/Y}`. -/
theorem preimage_range_specι_subset (i : D.J) :
    ⇑D.toScheme.base ⁻¹' Set.range ⇑(D.specι i).base ⊆
      Set.range ⇑(D.completionι i).base := by
  intro u hu
  obtain ⟨j, z, rfl⟩ := D.completionGlued_jointly_surjective u
  rw [Set.mem_preimage, D.toScheme_base_completionι j z] at hu
  by_cases h : j = i
  · subst h
    exact ⟨z, rfl⟩
  · have hmem : (formalCompletion.toSpec (D.C j) (D.K j) (D.hK j)).base z ∈
        (PrimeSpectrum.basicOpen (D.g j i) : Set (PrimeSpectrum (D.C j))) := by
      rw [← D.preimage_range_specι j i h]
      exact hu
    obtain ⟨w, hw⟩ := formalCompletion.mem_range_basicOpenImmersion (D.K j) (D.hK j) (D.g j i) z
      ((PrimeSpectrum.mem_basicOpen _ _).mp hmem)
    rw [← hw]
    refine ⟨(D.overlapImmersion i j).base ((D.overlapIso i j (Ne.symm h)).inv.base w), ?_⟩
    have key := congrArg (fun m : D.overlap i j ⟶ D.completionGlued.toLocallyRingedSpace =>
        m.base ((D.overlapIso i j (Ne.symm h)).inv.base w))
      (D.completion_glue_condition i j (Ne.symm h))
    simp only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
      Function.comp_apply] at key
    rw [← key]
    congr 2
    have hw' : ((D.overlapIso i j (Ne.symm h)).inv ≫
        (D.overlapIso i j (Ne.symm h)).hom).base w = w := by
      rw [(D.overlapIso i j (Ne.symm h)).inv_hom_id]
      rfl
    simpa only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
      Function.comp_apply] using hw'

/-! ### The closed embedding -/

/-- **On the `i`-th chart, `X_{/Y} ⟶ X` is an embedding**: it is the affine
`formalCompletion.toSpec`, a closed embedding, followed by the open immersion `specι i`
(`ChartedCompletionDatum.toScheme_base_completionι`).

This is a named theorem rather than an inline step of
`ChartedCompletionDatum.isEmbedding_toScheme_base` because the covering criterion below retypes
the composite through its chart-family argument: stated here, in the `formalCompletion` spelling,
the composite admits the rewrite; stated inside that `refine` it does not, while `exact` still
accepts this statement for it. -/
theorem isEmbedding_toScheme_comp_completionι (i : D.J) :
    IsEmbedding (⇑D.toScheme.base ∘ ⇑(D.completionι i).base) := by
  have h : ⇑D.toScheme.base ∘ ⇑(D.completionι i).base =
      ⇑(D.specι i).base ∘ ⇑(formalCompletion.toSpec (D.C i) (D.K i) (D.hK i)).base :=
    funext fun z => D.toScheme_base_completionι i z
  rw [h]
  exact (D.toChartedSchemeDatum.specι_isOpenImmersion i).base_open.isEmbedding.comp
    (formalCompletion.isClosedEmbedding_toSpec_base (D.C i) (D.K i) (D.hK i)).isEmbedding

/-- **`X_{/Y} ⟶ X` is a topological embedding** (EGA I, 10.8), at an arbitrary index.

`isEmbedding_of_iSup_eq_top_of_preimage_subset_range` over the chart ranges of
`ChartedCompletionDatum.specGlued`, which are open because `ChartedCompletionDatum.specι` is an
open immersion and cover because `ChartedCompletionDatum.specGlued_jointly_surjective`. Its three
remaining inputs are the continuity of each `ChartedCompletionDatum.completionι`, the chart
preimage `ChartedCompletionDatum.preimage_range_specι_subset`, and the per-chart embedding
`ChartedCompletionDatum.isEmbedding_toScheme_comp_completionι`. -/
theorem isEmbedding_toScheme_base : IsEmbedding ⇑D.toScheme.base := by
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range _ D.toScheme.base.hom.continuous
    (fun i : D.J => ⟨Set.range ⇑(D.specι i).base,
      (D.toChartedSchemeDatum.specι_isOpenImmersion i).base_open.isOpen_range⟩)
    ?_ (fun i : D.J => (D.chart i : Type u)) (fun i => ⇑(D.completionι i).base) ?_ ?_ ?_
  · intro z _
    obtain ⟨i, y, rfl⟩ := D.specGlued_jointly_surjective z
    exact Opens.mem_iSup.mpr ⟨i, ⟨y, rfl⟩⟩
  · exact fun i => (D.completionι i).base.hom.continuous
  · exact fun i => D.preimage_range_specι_subset i
  · exact fun i => D.isEmbedding_toScheme_comp_completionι i

/-- **The glued completion is a closed subspace of the glued scheme** (EGA I, 10.8): the canonical
morphism `X_{/Y} ⟶ X` is a closed embedding, for an arbitrary family of affine charts.

This is `ChartedCompletionDatum.isEmbedding_toScheme_base` paired with
`ChartedCompletionDatum.isClosed_range_toScheme_base`; the affine case is
`formalCompletion.isClosedEmbedding_toSpec_base` and the two-patch case is
`AlgebraicGeometry.isClosedEmbedding_completionTwoPatchToScheme_base`. -/
theorem isClosedEmbedding_toScheme_base : IsClosedEmbedding ⇑D.toScheme.base :=
  ⟨D.isEmbedding_toScheme_base, D.isClosed_range_toScheme_base⟩

/-- **`X_{/Y} ⟶ X` is injective.** Two points of the glued completion with the same image in the
glued scheme are equal — including the case where they lie in *different* charts, which is the
only one with any content and which the embedding criterion discharges. -/
theorem injective_toScheme_base : Function.Injective ⇑D.toScheme.base :=
  D.isEmbedding_toScheme_base.injective

end ChartedCompletionDatum

/-! ### The witness

`Topology.IsClosedEmbedding` is trivially true of a map out of an empty space, and a closed
embedding onto the whole space says nothing, so the theorem needs an instance in which the image
is neither. The projective line over a nontrivial `R`, completed at the origin of its first
chart, is one: the image is nonempty
(`AlgebraicGeometry.range_projectiveLineCompletionToScheme_base_nonempty`) and it is not
everything (`AlgebraicGeometry.range_projectiveLineCompletionToScheme_base_ne_univ`), because it
misses the whole second chart. -/

section Witness

variable (R : Type u) [CommRing R]

/-- **`X_{/Y} ⟶ X` is a closed embedding**, for the projective line completed at the origin of its
first chart — the arbitrary-index theorem at the tree's sharpest completion datum. -/
theorem isClosedEmbedding_projectiveLineCompletionToScheme_base :
    IsClosedEmbedding ⇑(projectiveLineCompletionToScheme R).base :=
  (projectiveLineDatum R).isClosedEmbedding_toScheme_base

/-- **The closed subspace is a proper one.** Without this the closed embedding above would be
compatible with `X_{/Y} ⟶ X` being a homeomorphism; the image misses the entire second chart, by
`range_projectiveLineCompletionToScheme_base_ne_univ`. -/
theorem not_surjective_projectiveLineCompletionToScheme_base [Nontrivial R] :
    ¬ Function.Surjective ⇑(projectiveLineCompletionToScheme R).base := fun hsurj =>
  range_projectiveLineCompletionToScheme_base_ne_univ R hsurj.range_eq

end Witness

end AlgebraicGeometry

end
