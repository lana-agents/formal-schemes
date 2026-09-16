import FormalSchemes.GeneralFibreProductBothObject
import FormalSchemes.CompletedTensorBaseChange
import FormalSchemes.GlueDataImageInter
import FormalSchemes.GeneralFibreProductBothOverlapRange
import FormalSchemes.CompletedTensorAwayInterchangePullbackLegs
import FormalSchemes.AwayTopFiniteType

set_option linter.style.header false

/-!
# The base change of a general fibre product, glued from its charts

`FormalSchemes.CompletedTensorBaseChange` builds, for a tower `R → R'` with `I' = I·R'`, the
comparison `Spf (A ⊗̂_{R'} B) ⟶ Spf (A ⊗̂_R B)` and proves it a closed immersion. The charts of
`AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct` are exactly of that shape, one per
ordered pair of charts, so that comparison is the chart level of

```
X ×_{Spf I'} Y ⟶ X ×_{Spf I} Y
```

and what is missing is the assembly. This file does the assembly, and isolates what the assembly
costs.

## The obstacle, and why it is not the one the tree expected

For the one-sided `X` the base change moves only the *ideal* on each chart — the chart ring `A i`
is the same ring over `R` and over `R'` — and the glued object is literally **equal**
(`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr`,
`FormalSchemes.GeneralFibreProductExposeXIdealCongr`, and its tower form in
`FormalSchemes.AwayBaseChangeGluedX`). For the fibre product the base change moves the chart
**ring**: `A_i ⊗̂_R B_j` and `A_i ⊗̂_{R'} B_j` are different rings. So the `…OfIdeals` idiom of
that file — abstract the ideal family to a variable and `subst` — has nothing to abstract here,
there is no equality to state, and only a morphism can relate the two glued objects.

## What is assembled, and on what hypothesis

A morphism out of a glued formal scheme is a compatible family of chart morphisms
(`AlgebraicGeometry.FormalScheme.GlueData.glueMorphisms`, `FormalSchemes.GlueMorphisms`). The
compatibility is a square relating the chart comparison at `p` to the fibre product's transition
between the `p`-th and `p'`-th charts. **That square is an input here, not an output**, and it is
named: `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapCompatible`. The reason is measured
rather than assumed and is recorded under *What is not proved here* below.

To state two fibre products over two bases at once, the chart family has to be a *parameter* and
not a field. `AlgebraicGeometry.BothChartedFibreDatum` carries `A` and `B` as fields, so two of
them over different bases share nothing that a statement can quantify over. This file therefore
repeats the carried geometric glue as `AlgebraicGeometry.DoubleChartGlue`, a structure over a
**fixed** chart family `A`, `B` and adic base `(R, I)`, and
`AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct_eq` says by `rfl` that nothing is
lost: the glued fibre product reads off a datum exactly its chart algebras and its eight geometric
fields, and none of `gX`, `gY`, `τX`, `τY`, which are documentation of intent there.

## Main definitions and results

* `AlgebraicGeometry.FormalScheme.GlueData.mapGlued`: a morphism **between** two glued formal
  schemes from an index map and a compatible family of chart morphisms, with
  `AlgebraicGeometry.FormalScheme.GlueData.ι_mapGlued` and
  `AlgebraicGeometry.FormalScheme.GlueData.mapGlued_ext`.
* `AlgebraicGeometry.DoubleChartGlue`: the geometric glue of a two-sided fibre product over a fixed
  chart family, with `AlgebraicGeometry.DoubleChartGlue.fibreProduct` its glued object and
  `AlgebraicGeometry.DoubleChartGlue.ι` its chart immersions.
* `AlgebraicGeometry.BothChartedFibreDatum.toDoubleChartGlue` and
  `AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct_eq`: every datum's fibre product is
  one of these, by `rfl`.
* `AlgebraicGeometry.DoubleChartGlue.map`: a morphism of glued fibre products over two bases from a
  family of chart morphisms owed only at **distinct** pairs, with
  `AlgebraicGeometry.DoubleChartGlue.ι_map` and `AlgebraicGeometry.DoubleChartGlue.map_ext`.
* `AlgebraicGeometry.DoubleChartGlue.chartBaseChange`: the chart-level comparison, which is
  `CompletedTensorProduct.schemeBaseChange` underneath
  (`AlgebraicGeometry.DoubleChartGlue.chartBaseChange_eq_schemeBaseChange`), hence a closed
  immersion at every chart.
* `AlgebraicGeometry.DoubleChartGlue.f_comp_ι`: the glue condition of the fibre product, written in
  the vocabulary of the carried glue rather than of the assembled datum.
* `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapCompatible`: **the square**, and
  `AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_overlapComparison`, which
  reduces it to a comparison of the two glues' overlap objects — see *Reducing the square* below.
* `AlgebraicGeometry.DoubleChartGlue.baseChange`: the glued comparison
  `X ×_{Spf I'} Y ⟶ X ×_{Spf I} Y`, with `AlgebraicGeometry.DoubleChartGlue.ι_baseChange` and
  `AlgebraicGeometry.DoubleChartGlue.baseChange_ext`.
* `AlgebraicGeometry.DoubleChartGlue.ι_jointly_surjective`,
  `AlgebraicGeometry.DoubleChartGlue.injective_ι_base`,
  `AlgebraicGeometry.DoubleChartGlue.ι_glue_apply` and
  `AlgebraicGeometry.DoubleChartGlue.preimage_range_ι`: the glued fibre product read at a point —
  the charts cover it, each chart immersion is injective, the glue identifies exactly the overlap,
  and the part of one chart landing in another *is* the overlap.
* `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapSaturated`: **the second hypothesis**, and
  the subject of the section below.
* `AlgebraicGeometry.bothAlgDataOverlapElt` and
  `AlgebraicGeometry.range_bothAlgDataF_base_eq_basicOpen`: the
  dispatched overlap of two distinct product-index charts is the **basic open of one element**, in
  all three branches of `AlgebraicGeometry.bothAlgDataF`, with
  `AlgebraicGeometry.baseChangeHom_bothAlgDataOverlapElt` carrying that element across the base
  change.
* `AlgebraicGeometry.DoubleChartGlue.preimage_basicOpen_chartBaseChange_base`,
  `AlgebraicGeometry.DoubleChartGlue.preimage_range_eq_of_range_eq_basicOpen` and
  `AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapSaturated_of_range_eq_basicOpen`: **the
  saturation holds, as an equality, whenever the two overlaps are cut out by corresponding
  elements** — the general criterion, which asks nothing about the transitions.
* `AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapSaturated_of_range_eq_bothAlgDataF`: **the
  second hypothesis discharged** at a pair carrying the dispatched overlap immersions.
* `AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base_of_injective_chartBaseChange` and
  `AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base`: **the glued comparison is
  injective on points**, from the square, the saturation and injectivity of the chart legs — which
  `AlgebraicGeometry.DoubleChartGlue.injective_chartBaseChange_base` supplies for free once the
  adic instances are in scope.
* `CompletedTensorAwayInterchange.interchangeChartBaseChange` and
  `CompletedTensorAwayInterchange.interchangeOpenImmersion_comp_baseChange`: **the immersion half
  of the reduction, at one branch of the dispatch** — the comparison of the two glues' overlap
  objects at a pair whose `X`-coordinate differs and whose `Y`-coordinate does not, and the square
  it satisfies. `CompletedTensorAwayInterchange.baseChangeHom_comp_gCHom` is the ring square
  underneath it, `CompletedTensorAwayInterchange.interchangeChartObj_congr` the transport it costs,
  and `AlgebraicGeometry.DoubleChartGlue.interchangeOpenImmersion_comp_chartBaseChange` the same
  square in this file's chart vocabulary.

## Reducing the square to the carried overlap data

`AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapCompatible` is stated with
`AlgebraicGeometry.DoubleChartGlue.ι` in it, so as written it is a condition about the **glued**
target. It need not be discharged in that form.
`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_overlapComparison` produces it
from a family `w p p' hne : G'.V p p' hne ⟶ G.V p p' hne` subject to two conditions in which the
glued object does not occur: `w` commutes with the overlap immersions against the chart comparison,
and `w` commutes with the overlap transitions. The proof is the target's own glue condition
(`AlgebraicGeometry.DoubleChartGlue.f_comp_ι`) between two rewrites.

The reduction is worth stating separately because the two conditions are of **different species**,
and a pair produced by `AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraData` meets them for
different reasons:

* The immersion condition is a commutation of `CompletedTensorProduct.baseChangeHom` with the three
  interchange open immersions of `FormalSchemes.GeneralFibreProductBothAlgebraDataObject`'s
  dispatch. Each branch is algebra about one pair of charts, and the two glues' overlap objects are
  built over the *same* rings there: under `I.map (algebraMap R R') = I'` the two extended ideals
  agree (`Ideal.map_algebraMap_of_tower`, `FormalSchemes.AwayTopFiniteType`), so no comparison of
  away completions has to be constructed and only a transport along that equality is needed. The
  branch where the `X`-coordinate differs and the `Y`-coordinate does not is discharged below,
  under *The first interchange branch against the chart comparison*, and the transport it costs is
  one `eqToHom` over one `congrArg`.
* The transition condition compares the chart transitions supplied to the smart constructor on the
  two sides. Over a general tower `R → R'` those are independent data: an `R`-algebra equivalence
  of chart rings is not an `R'`-algebra equivalence, so the condition constrains how the primed
  datum is chosen. It becomes automatic at `R' = R{1/f}`, where
  `FormalSpectrum.awayCompletionChartAlgEquivBase` (`FormalSchemes.AwayCompletionUniversal`)
  enlarges the scalars for free — that is a statement about the away completion as a source, not
  about a general base.

## Why injectivity needs a second hypothesis

`AlgebraicGeometry.DoubleChartGlue.baseChange` is injective on points as soon as its chart legs are
*and* the source overlaps are saturated: at `p ≠ p'`, a point of the source's `p`-th chart whose
comparison image lies in the target's overlap of `p` and `p'` must already lie in the *source's*
overlap of the same pair. That is `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapSaturated`,
and it is a second hypothesis rather than a consequence of the first:

* **Chartwise injectivity does not glue.** Two points of *different* source charts can share an
  image while no chart leg identifies anything, so no strengthening of the chart-level statement
  reaches the glued map — `CompletedTensorProduct.schemeBaseChange_isClosedImmersion` included. The
  missing content is about the glue, not about the charts.
* **The square does not supply it.**
  `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapCompatible` says the two chart comparisons
  agree *where the source glues*. It says nothing about where the **target** glues, which is
  exactly what injectivity of the glued map is about.
* **At a general pair injectivity is false.** Take `R' = R`, `I' = I`, the same chart family, `G`
  any glue with a nonempty overlap at some `p ≠ p'`, and `G'` the same charts with every overlap
  object replaced by the initial locally ringed space
  (`AlgebraicGeometry.LocallyRingedSpace.emptyIsInitial`). Each square is then an equation between
  two morphisms out of an initial object and holds; the source is the charts side by side, the
  target glues two of them, and the comparison identifies the two copies of the overlap. **This is
  an argument and not a formalisation** — no such pair is constructed below, and the file's
  contribution is the named hypothesis and the theorem over it.

## What is not proved here

* **The square is not discharged.**
  `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapCompatible` is a hypothesis of
  `AlgebraicGeometry.DoubleChartGlue.baseChange`, and nothing here produces one outright at a
  general pair of glues. This is not a gap that a harder proof closes: at a general pair the two
  glues are *unrelated data*, and the square is then false as often as it is true.
  `AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_overlapComparison` produces
  one from a comparison of the two glues' overlap objects, which is again data, and nothing here
  produces one of those either. The square becomes a theorem only for a pair produced by the smart
  constructor
  `AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraData`, where the overlap objects are the
  three-branch interchange dispatch of `FormalSchemes.GeneralFibreProductBothAlgebraDataObject`.
  *Reducing the square* above says what is left there, and it is two things rather than three. The
  first is a commutation of `CompletedTensorProduct.baseChangeHom` with each of the three
  interchange open immersions, and it is **partly** discharged below: the branch at
  `CompletedTensorAwayInterchange.interchangeOpenImmersion` is
  `CompletedTensorAwayInterchange.interchangeOpenImmersion_comp_baseChange`, and the branches at
  `CompletedTensorAwayInterchange.rightInterchangeOpenImmersion` and
  `CompletedTensorAwayInterchange.bothInterchangeOpenImmersion` — the conjugate by
  `CompletedTensorAwayInterchange.commSpfIso` and the composite of the two — are not here, and
  neither is the assembly of the three across the `eqToHom` dispatch of
  `AlgebraicGeometry.bothAlgDataF`. No base change of
  `FormalSpectrum.awayCompletion` is among any of them, because the two away completions involved
  are the same ring. The second is the agreement of the primed transitions with the unprimed ones,
  which is
  a condition on the primed datum over a general tower and is produced rather than assumed only at
  an away base, where `FormalSchemes.AwayBaseChangeGluedX` builds it on the one-sided side.
* **The saturation is discharged, and the square is not.** The two hypotheses were filed
  together and they did not cost the same.
  `AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapSaturated_of_range_eq_bothAlgDataF` below
  proves `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapSaturated` at a pair carrying the
  dispatched overlap immersions, which is what the smart constructor
  `AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraData` produces, and it proves it as an
  *equality*. What remains unproduced is the **primed glue itself**: assembling one needs the
  transitions and the double-overlap data over `(R', I')`, which is the second of the square's two
  outstanding needs above and not this section's. So the saturation is a theorem over hypotheses
  that are `rfl` for a smart-constructor glue, and it waits on a constructor rather than on an
  argument.
* **No cancellation, and no separation statement.** Nothing here mentions
  `AlgebraicGeometry.BothChartedFibreDatumXY.IsSeparated` or
  `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf`.
* **Injectivity is all the glued comparison gets.** Nothing here says it is a closed immersion, or
  that its range is closed. That does not follow from the two hypotheses plus chartwise closedness
  — the range of the glued map is a union of chart images, and closedness of such a union is a
  question about the target's glue that neither hypothesis answers. Continuity, on the other hand,
  is free: the base map of a morphism of locally ringed spaces is a morphism of topological spaces.
* **The general base is not available and is not an oversight.** Every statement below carries
  `I.map (algebraMap R R') = I'`, inherited from `CompletedTensorProduct.map_baseChangeHom`;
  `FormalSchemes.CompletedTensorBaseChange` records why, and `FormalSchemes.AdicOnSections` is the
  refutation it points at.

## Implementation notes

The off-diagonal bookkeeping this file's glue conditions need —
`CategoryTheory.GlueData.ofGlueData'_f_comp` and its converse
`CategoryTheory.GlueData.ofGlueData'_f_comp_of` — is **not** stated here. It lives in
`FormalSchemes.GlueMorphisms`, beside
`AlgebraicGeometry.FormalScheme.GlueData.glueMorphisms`, which is the declaration that asks for the
condition at every pair; this file reaches that module through its imports and uses both from
there. They were first stated here and moved down (issue 2048) once a second consumer appeared:
the proof of `AlgebraicGeometry.AffineChartedFibreDatumX.glueChartMorphisms`
(`FormalSchemes.ChartedDatumGlueMorphisms`) had been doing the same `by_cases`, the same `dif_neg`
unfolding and the same closing `rw` inline, and now calls
`CategoryTheory.GlueData.ofGlueData'_f_comp` instead.

## Placement

Over six parents. `FormalSchemes.GeneralFibreProductBothObject` has forward closure
**64**; `FormalSchemes.CompletedTensorBaseChange` has forward closure **44**;
`FormalSchemes.GlueDataImageInter` has forward closure **2**;
`FormalSchemes.GeneralFibreProductBothOverlapRange` has forward closure **70**;
`FormalSchemes.CompletedTensorAwayInterchangePullbackLegs` has forward closure **37**; and
`FormalSchemes.AwayTopFiniteType` has forward closure **28**. This file's own
forward closure is **93**, and this file's reverse closure is **1** —
`FormalSchemes.GeneralSeparatedBaseChange`, which consumes the injectivity theorem (issue 2035).
This module was a leaf when it landed and the paragraph below was written then.
`FormalSchemes.GlueMorphisms`, whose
`AlgebraicGeometry.FormalScheme.GlueData.glueMorphisms` this file consumes, is already inside the
first parent's closure, so the edge to it is free and it is not imported again.

The third parent is the whole cost of the injectivity section: it and
`FormalSchemes.GlueDataCarrier` are the only two modules it adds, and this file's reverse closure
is **1**, so almost nothing downstream pays for them.
`AlgebraicGeometry.LocallyRingedSpace.GlueData.preimage_range_ι` is the one statement on the tree
that turns *"these two chart images meet"* into *"this point is in the overlap object"*, and no
weaker import reaches it.

The fourth parent is the whole cost of the saturation section: it adds six modules — itself,
`FormalSchemes.GeneralFibreProductBothAlgebraDataObject`,
`FormalSchemes.CompletedTensorAwayInterchangeBoth`,
`FormalSchemes.CompletedTensorAwayInterchangeRight`, `FormalSchemes.CompletionBasicOpen` and
`FormalSchemes.CompletionNestedBasicOpen`. The edge was taken rather than a new leaf because this
file's reverse closure is **1**: extending in place moves six such figures by one each and leaves
the rest of the tree alone, where a new module would have moved ninety-three of them.
`AlgebraicGeometry.range_bothAlgDataF_base` is the range computation the saturation is *about* and
no weaker import reaches it — the dispatch it consumes,
`FormalSchemes.GeneralFibreProductBothAlgebraDataObject`, is one module below and would not have
been enough, since restating that range here rather than consuming it is what this section
deliberately does not do.

The fifth and sixth parents are the whole cost of the interchange-branch section, and between them
they add six modules: themselves, `FormalSchemes.CompletedTensorAwayInterchangePullback`,
`FormalSchemes.PullbackIsoRangeLegs`, `FormalSchemes.PullbackRangeLRS` and
`FormalSchemes.AwayCompletionSurjective`. The fifth is what
`CompletedTensorAwayInterchange.interchangeOpenImmersion_eq_map` and
`CompletedTensorAwayInterchange.gCHom_le_comap` live in, and no weaker import reaches them: the
ring map underlying the interchange open immersion is named one module lower, but the
identification of the *geometric* immersion with `FormalSpectrum.locallyRingedSpaceMap` of it is
not. The sixth is
`Ideal.map_algebraMap_of_tower`, which is the whole of this section's ideal bookkeeping. Both edges
were taken rather than a new leaf on the same arithmetic as the fourth: six reverse-closure figures
move by one each, against ninety-three for a new module.

The two parents are import-incomparable, so the statement costs either an import edge or a new
leaf, and the edge was rejected in both directions. Adding to
`FormalSchemes.GeneralFibreProductBothObject` puts the whole completed-tensor base change inside
the closure of a module whose reverse closure is **68**; adding to
`FormalSchemes.CompletedTensorBaseChange`, whose reverse closure is **2**, puts the entire
fibre-product cluster inside a module that is otherwise affine throughout. A separate module keeps
both parents at the cost they were landed at, and this file's own reverse closure is **1**, so
almost nothing pays for it. This is the disposition `FormalSchemes.AwayBaseChangeGluedX` reached,
for the same pair of reasons, on the one-sided side of the same question.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
* [The Stacks Project, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorProduct

universe u

namespace AlgebraicGeometry

/-! ### A morphism between two glued formal schemes -/

namespace FormalScheme.GlueData

variable (G' G : FormalScheme.GlueData.{u})

/-- **A morphism between two glued formal schemes.** Given an index map `e` and a family of chart
morphisms `k i : U' i ⟶ U (e i)` whose composites with the target's chart immersions agree on the
source's overlaps, the induced morphism of glued formal schemes.

This is `AlgebraicGeometry.FormalScheme.GlueData.glueMorphisms` at the target
`(G.gluedFormalScheme).toLocallyRingedSpace`: a morphism *between* two glued objects is a morphism
*out of* the source into the glued target, and nothing more is needed. -/
def mapGlued (e : G'.toLocallyRingedSpaceGlueData.J → G.toLocallyRingedSpaceGlueData.J)
    (k : ∀ i, G'.toLocallyRingedSpaceGlueData.U i ⟶ G.toLocallyRingedSpaceGlueData.U (e i))
    (h : ∀ i j, G'.toLocallyRingedSpaceGlueData.toGlueData.f i j ≫ k i ≫ G.ι (e i) =
      G'.toLocallyRingedSpaceGlueData.toGlueData.t i j ≫
        G'.toLocallyRingedSpaceGlueData.toGlueData.f j i ≫ k j ≫ G.ι (e j)) :
    (G'.gluedFormalScheme).toLocallyRingedSpace ⟶ (G.gluedFormalScheme).toLocallyRingedSpace :=
  G'.glueMorphisms (fun i => k i ≫ G.ι (e i)) (by simpa only [Category.assoc] using h)

@[reassoc (attr := simp)]
theorem ι_mapGlued (e) (k) (h) (i) : G'.ι i ≫ G'.mapGlued G e k h = k i ≫ G.ι (e i) :=
  G'.ι_glueMorphisms _ _ i

/-- **Uniqueness**: a morphism of glued formal schemes restricting to `k i` on every chart is the
glued one. -/
theorem mapGlued_ext {e k h} {m : (G'.gluedFormalScheme).toLocallyRingedSpace ⟶
      (G.gluedFormalScheme).toLocallyRingedSpace}
    (hm : ∀ i, G'.ι i ≫ m = k i ≫ G.ι (e i)) : m = G'.mapGlued G e k h :=
  G'.hom_ext fun i => by rw [hm i, ι_mapGlued]

end FormalScheme.GlueData

/-! ### The two-sided fibre-product glue over a fixed chart family -/

variable {JX JY : Type u}
variable (R : Type u) [CommRing R] (I : Ideal R)
variable (A : JX → Type u) (B : JY → Type u)
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]

/-- The `p`-th double-tensor chart `Spf (A_{p.1} ⊗̂_R B_{p.2})` as a locally ringed space. -/
abbrev doubleChartObj (p : JX × JY) : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))

/-- **The geometric glue of a two-sided fibre product over a fixed chart family.** These are
exactly the eight geometric fields of `AlgebraicGeometry.BothChartedFibreDatum`, with the chart
algebras `A`, `B` and the adic base `(R, I)` moved out of the structure and into its parameters.

That move is the whole reason the structure exists: a base change compares two fibre products over
*different* bases on the *same* charts, and a field cannot be shared between two structures.
`AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct_eq` shows nothing is lost. -/
structure DoubleChartGlue where
  /-- The overlap object of two distinct product-index charts. -/
  V : ∀ (p p' : JX × JY), p ≠ p' → LocallyRingedSpace.{u}
  /-- The overlap immersion into the `p`-th chart. -/
  f : ∀ (p p' : JX × JY) (h : p ≠ p'), V p p' h ⟶ doubleChartObj R I A B p
  /-- Each overlap immersion is an open immersion. -/
  hf : ∀ (p p' : JX × JY) (h : p ≠ p'), LocallyRingedSpace.IsOpenImmersion (f p p' h)
  /-- The transition between the two overlap objects of a pair of distinct charts. -/
  t : ∀ (p p' : JX × JY) (h : p ≠ p'), V p p' h ⟶ V p' p h.symm
  /-- The transitions are mutually inverse. -/
  t_inv : ∀ (p p' : JX × JY) (h : p ≠ p'), t p p' h ≫ t p' p h.symm = 𝟙 _
  /-- The geometric triple-overlap transition. -/
  t' : ∀ (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p''),
    letI := hf p p' hpp'
    letI := hf p p'' hpp''
    letI := hf p' p'' hp'p''
    letI := hf p' p hpp'.symm
    (pullback (f p p' hpp') (f p p'' hpp'') ⟶ pullback (f p' p'' hp'p'') (f p' p hpp'.symm))
  /-- Compatibility of `t'` with the transition `t`. -/
  t_fac : ∀ (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p''),
    letI := hf p p' hpp'
    letI := hf p p'' hpp''
    letI := hf p' p'' hp'p''
    letI := hf p' p hpp'.symm
    t' p p' p'' hpp' hpp'' hp'p'' ≫ pullback.snd (f p' p'' hp'p'') (f p' p hpp'.symm) =
      pullback.fst (f p p' hpp') (f p p'' hpp'') ≫ t p p' hpp'
  /-- The triple cocycle. -/
  cocycle : ∀ (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p''),
    letI := hf p p' hpp'
    letI := hf p p'' hpp''
    letI := hf p' p'' hp'p''
    letI := hf p' p hpp'.symm
    letI := hf p'' p hpp''.symm
    letI := hf p'' p' hp'p''.symm
    t' p p' p'' hpp' hpp'' hp'p'' ≫ t' p' p'' p hp'p'' hpp'.symm hpp''.symm ≫
      t' p'' p p' hpp''.symm hp'p''.symm hpp' = 𝟙 _

namespace DoubleChartGlue

variable {R I A B} (G : DoubleChartGlue R I A B)

/-- The `CategoryTheory.GlueData'` of a `AlgebraicGeometry.DoubleChartGlue`. -/
def glueData' : CategoryTheory.GlueData'.{u} LocallyRingedSpace where
  J := JX × JY
  U := doubleChartObj R I A B
  V := G.V
  f := G.f
  f_mono := fun p p' h => by
    haveI := G.hf p p' h
    infer_instance
  f_hasPullback := fun p p' p'' hpp' hpp'' => by
    haveI := G.hf p p' hpp'
    haveI := G.hf p p'' hpp''
    infer_instance
  t := G.t
  t' := G.t'
  t_fac := G.t_fac
  t_inv := G.t_inv
  cocycle := G.cocycle

/-- The `AlgebraicGeometry.LocallyRingedSpace.GlueData` of a `AlgebraicGeometry.DoubleChartGlue`.
Off the diagonal each glue map is `eqToHom ≫ (carried immersion)`; on the diagonal it is `eqToHom`.
-/
def lrsGlueData : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' G.glueData' with
    f_open := by
      rintro p p'
      simp only [glueData', CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · haveI := G.hf p p' h
        exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _ ≫ G.f p p' h)) }

/-- The `AlgebraicGeometry.FormalScheme.GlueData` of a `AlgebraicGeometry.DoubleChartGlue`. -/
def formalGlueData (hI : I.FG) : FormalScheme.GlueData.{u} where
  toLocallyRingedSpaceGlueData := G.lrsGlueData
  isFormalScheme := fun p =>
    haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2)) :=
      CompletedTensorProduct.isAdicRing R I (A p.1) (B p.2) hI
    ⟨FormalScheme.Spf (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2)),
      ⟨Iso.refl _⟩⟩

/-- **The glued fibre product** of a `AlgebraicGeometry.DoubleChartGlue`. -/
def fibreProduct (hI : I.FG) : FormalScheme.{u} := (G.formalGlueData hI).gluedFormalScheme

/-- The open immersion of the `p`-th chart into the glued fibre product. -/
abbrev ι (hI : I.FG) (p : JX × JY) :
    doubleChartObj R I A B p ⟶ (G.fibreProduct hI).toLocallyRingedSpace :=
  (G.formalGlueData hI).ι p

/-- **The glue condition of the fibre product, in the vocabulary of the carried glue**: the two
ways of pushing the `p`-`p'` overlap into the glued object agree.
`CategoryTheory.GlueData.glue_condition` says this at the assembled datum, whose overlap object is
a `dite` and whose index type is `JX × JY` only after unfolding;
`CategoryTheory.GlueData.ofGlueData'_f_comp_of` is the step back. -/
theorem f_comp_ι (hI : I.FG) (p p' : JX × JY) (h : p ≠ p') :
    G.f p p' h ≫ G.ι hI p = G.t p p' h ≫ G.f p' p h.symm ≫ G.ι hI p' :=
  CategoryTheory.GlueData.ofGlueData'_f_comp_of G.glueData' (fun q => G.ι hI q)
    (fun q q' => (G.lrsGlueData.toGlueData.glue_condition q q').symm) p p' h

/-! ### The points of the glued fibre product -/

/-- **The charts cover the glued fibre product**, with the chart index read as a pair.
`AlgebraicGeometry.FormalScheme.GlueData.ι_jointly_surjective` says the same thing over
`(G.formalGlueData hI).toLocallyRingedSpaceGlueData.J`, which is `JX × JY` only after unfolding two
definitions; this restatement is the one a `by_cases` on a pair of indices can consume. -/
theorem ι_jointly_surjective (hI : I.FG) (u : (G.fibreProduct hI).toLocallyRingedSpace) :
    ∃ (p : JX × JY) (x : (doubleChartObj R I A B p).toPresheafedSpace),
      (G.ι hI p).base x = u :=
  (G.formalGlueData hI).ι_jointly_surjective u

/-- **Each chart immersion is injective on points**, being an open immersion. -/
theorem injective_ι_base (hI : I.FG) (p : JX × JY) :
    Function.Injective ⇑(G.ι hI p).base :=
  ((G.formalGlueData hI).ι_isOpenImmersion p).base_open.injective

/-- The assembled glue datum's overlap inclusion, off the diagonal, in the vocabulary of the
carried glue. `CategoryTheory.GlueData.ofGlueData'` prefixes an `eqToHom` transporting along the
`dite` that defines its overlap object, and `dif_neg` is the whole content. -/
theorem lrsGlueData_f (p p' : JX × JY) (h : p ≠ p') :
    G.lrsGlueData.toGlueData.f p p' = eqToHom (dif_neg h) ≫ G.f p p' h :=
  dif_neg h

/-- **The assembled overlap inclusion has the same range as the carried one.** The `eqToHom` of
`AlgebraicGeometry.DoubleChartGlue.lrsGlueData_f` is an isomorphism, so it is invisible to the
range. This is what lets the statements a caller reads stay in the vocabulary of the carried glue —
its own overlap inclusions and transitions — while the proofs that produce them work in the
assembled one. -/
theorem range_lrsGlueData_f (p p' : JX × JY) (h : p ≠ p') :
    Set.range ⇑(G.lrsGlueData.toGlueData.f p p').base = Set.range ⇑(G.f p p' h).base := by
  have haux : ∀ {X Y Z : LocallyRingedSpace.{u}} (e : X = Y) (g : Y ⟶ Z),
      Set.range ⇑(eqToHom e ≫ g).base = Set.range ⇑g.base := by
    rintro X Y Z rfl g
    simp
  rw [G.lrsGlueData_f p p' h]
  exact haux _ _

/-- **The glue condition at a point**: a point of the `p`-`p'` overlap has the same image in the
glued fibre product whether it is pushed into the `p`-th chart or transported and pushed into the
`p'`-th one. This is `CategoryTheory.GlueData.glue_condition` for the assembled datum, read through
`AlgebraicGeometry.LocallyRingedSpace.comp_base`.

The overlap object is the assembled one rather than `G.V p p' h`: the two `eqToHom`s of
`AlgebraicGeometry.DoubleChartGlue.lrsGlueData_f` do not cancel against each other pointwise, and
nothing below needs them to — a point of the assembled overlap is all the statement is asked
for. -/
theorem ι_glue_apply (hI : I.FG) (p p' : JX × JY)
    (v : G.lrsGlueData.toGlueData.V (p, p')) :
    (G.ι hI p').base ((G.lrsGlueData.toGlueData.f p' p).base
        ((G.lrsGlueData.toGlueData.t p p').base v)) =
      (G.ι hI p).base ((G.lrsGlueData.toGlueData.f p p').base v) := by
  have key := G.lrsGlueData.toGlueData.glue_condition p p'
  have keyb : (G.lrsGlueData.toGlueData.t p p').base ≫ (G.lrsGlueData.toGlueData.f p' p).base ≫
      (G.lrsGlueData.toGlueData.ι p').base =
      (G.lrsGlueData.toGlueData.f p p').base ≫ (G.lrsGlueData.toGlueData.ι p).base := by
    rw [← LocallyRingedSpace.comp_base, ← LocallyRingedSpace.comp_base,
      ← LocallyRingedSpace.comp_base, key]
  have hv := ConcreteCategory.congr_hom keyb v
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply] at hv
  exact hv

/-- **The part of one chart that lands in another is exactly their overlap.** This is
`AlgebraicGeometry.LocallyRingedSpace.GlueData.preimage_range_ι` read at the assembled glue datum
and carried back into the carried vocabulary by
`AlgebraicGeometry.DoubleChartGlue.range_lrsGlueData_f`. It is the only place the injectivity
argument below looks at the *target's* glue, and it is why that argument needs a glue-level input
rather than a chart-level one. -/
theorem preimage_range_ι (hI : I.FG) (p p' : JX × JY) (h : p ≠ p') :
    ⇑(G.ι hI p).base ⁻¹' Set.range ⇑(G.ι hI p').base = Set.range ⇑(G.f p p' h).base :=
  (G.lrsGlueData.preimage_range_ι p' p).trans (G.range_lrsGlueData_f p p' h)

/-! ### A morphism of glued fibre products -/

section Map

variable {R' : Type u} [CommRing R'] {I' : Ideal R'}
variable [∀ i, Algebra R' (A i)] [∀ j, Algebra R' (B j)]
variable (G' : DoubleChartGlue R' I' A B) (G : DoubleChartGlue R I A B)

/-- **A morphism of glued fibre products from a family of chart morphisms** that agree on the
overlaps of the source. The square is owed only at **distinct** pairs, by
`CategoryTheory.GlueData.ofGlueData'_f_comp`. -/
def map (hI' : I'.FG) (hI : I.FG)
    (k : ∀ p : JX × JY, doubleChartObj R' I' A B p ⟶ doubleChartObj R I A B p)
    (h : ∀ (p p' : JX × JY) (hne : p ≠ p'), G'.f p p' hne ≫ k p ≫ G.ι hI p =
      G'.t p p' hne ≫ G'.f p' p hne.symm ≫ k p' ≫ G.ι hI p') :
    (G'.fibreProduct hI').toLocallyRingedSpace ⟶ (G.fibreProduct hI).toLocallyRingedSpace :=
  (G'.formalGlueData hI').mapGlued (G.formalGlueData hI) id (fun p => k p)
    (CategoryTheory.GlueData.ofGlueData'_f_comp G'.glueData' (fun p => k p ≫ G.ι hI p) h)

@[reassoc (attr := simp)]
theorem ι_map (hI' : I'.FG) (hI : I.FG) (k) (h) (p : JX × JY) :
    G'.ι hI' p ≫ G'.map G hI' hI k h = k p ≫ G.ι hI p :=
  (G'.formalGlueData hI').ι_mapGlued _ _ _ _ p

/-- **Uniqueness**: a morphism of glued fibre products restricting to `k p` on every chart is
`AlgebraicGeometry.DoubleChartGlue.map`. -/
theorem map_ext (hI' : I'.FG) (hI : I.FG) {k} {h}
    {m : (G'.fibreProduct hI').toLocallyRingedSpace ⟶ (G.fibreProduct hI).toLocallyRingedSpace}
    (hm : ∀ p, G'.ι hI' p ≫ m = k p ≫ G.ι hI p) : m = G'.map G hI' hI k h :=
  (G'.formalGlueData hI').mapGlued_ext _ hm

end Map

/-! ### The base change -/

section BaseChange

variable {R' : Type u} [CommRing R'] [Algebra R R'] {I' : Ideal R'}
variable [∀ i, Algebra R' (A i)] [∀ i, IsScalarTower R R' (A i)]
variable [∀ j, Algebra R' (B j)] [∀ j, IsScalarTower R R' (B j)]
variable (G' : DoubleChartGlue R' I' A B) (G : DoubleChartGlue R I A B)

/-- **The chart-level base-change comparison**
`Spf (A_{p.1} ⊗̂_{R'} B_{p.2}) ⟶ Spf (A_{p.1} ⊗̂_R B_{p.2})`, which is
`CompletedTensorProduct.schemeBaseChange` read as a morphism of locally ringed spaces. -/
def chartBaseChange (hI : I.FG) (hII' : I.map (algebraMap R R') = I') (p : JX × JY) :
    doubleChartObj R' I' A B p ⟶ doubleChartObj R I A B p :=
  locallyRingedSpaceMap (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))
    (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))
    (CompletedTensorProduct.baseChangeHom (A := A p.1) (B := B p.2) hI hII')
    (CompletedTensorProduct.le_comap_baseChangeHom hI hII')

/-- **The overlap square**: the hypothesis the glued base change needs. At `p ≠ p'` the chart
comparisons at `p` and at `p'` must agree on the source's overlap of the two charts.

It is not discharged here at a pair a smart constructor produces, but it is reduced: see
`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_overlapComparison`, which asks
instead for a comparison of the two glues' overlap objects and mentions the glued target nowhere.
`AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapSaturated` is the glued base change's other
hypothesis and is a different obligation; the reduction does not supply it, and supplies the
*opposite* containment of the one it asks for. That one is discharged below, by
`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapSaturated_of_range_eq_bothAlgDataF`. -/
def IsBaseChangeOverlapCompatible (hI : I.FG) (hII' : I.map (algebraMap R R') = I') : Prop :=
  ∀ (p p' : JX × JY) (hne : p ≠ p'),
    G'.f p p' hne ≫ chartBaseChange hI hII' p ≫ G.ι hI p =
      G'.t p p' hne ≫ G'.f p' p hne.symm ≫ chartBaseChange hI hII' p' ≫ G.ι hI p'

/-- **The base change of a glued fibre product**, `X ×_{Spf I'} Y ⟶ X ×_{Spf I} Y`, assembled from
the chart comparisons of `FormalSchemes.CompletedTensorBaseChange`. -/
def baseChange (hI' : I'.FG) (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
    (h : G'.IsBaseChangeOverlapCompatible G hI hII') :
    (G'.fibreProduct hI').toLocallyRingedSpace ⟶ (G.fibreProduct hI).toLocallyRingedSpace :=
  G'.map G hI' hI (chartBaseChange hI hII') h

/-- **The glued base change restricts to the chart comparison on every chart.** -/
@[reassoc (attr := simp)]
theorem ι_baseChange (hI' : I'.FG) (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
    (h : G'.IsBaseChangeOverlapCompatible G hI hII') (p : JX × JY) :
    G'.ι hI' p ≫ G'.baseChange G hI' hI hII' h = chartBaseChange hI hII' p ≫ G.ι hI p :=
  G'.ι_map G hI' hI _ h p

/-- **Uniqueness of the glued base change** among morphisms restricting to the chart comparisons.
-/
theorem baseChange_ext (hI' : I'.FG) (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
    (h : G'.IsBaseChangeOverlapCompatible G hI hII')
    {m : (G'.fibreProduct hI').toLocallyRingedSpace ⟶ (G.fibreProduct hI).toLocallyRingedSpace}
    (hm : ∀ p, G'.ι hI' p ≫ m = chartBaseChange hI hII' p ≫ G.ι hI p) :
    m = G'.baseChange G hI' hI hII' h :=
  G'.map_ext G hI' hI hm

/-! ### Reducing the square to the carried overlap data -/

/-- **The square follows from a comparison of the overlap objects.** Given a family
`w p p' hne : G'.V p p' hne ⟶ G.V p p' hne` that commutes with the overlap immersions and with the
overlap transitions, the glued base change's hypothesis holds.

The point is what is *absent* from the two hypotheses: `AlgebraicGeometry.DoubleChartGlue.ι` does
not appear in either, so neither mentions the glued object. The square as stated is a condition on
the target's glue; this reduces it to two conditions on the carried overlap data of the two glues,
each of which is a statement about one pair of charts at a time.

The two hypotheses are also of different species, and a discharge will find them so. The first
compares the overlap *immersions* — at a pair produced by
`AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraData` that is a commutation of
`CompletedTensorProduct.baseChangeHom` with the interchange open immersions, which is algebra about
one chart. The second compares the overlap *transitions*, which at such a pair are built from the
chart transitions supplied to the smart constructor; over a general tower `R → R'` those are
independent data on the two sides, so the second hypothesis constrains how the primed datum is
chosen rather than following from how it is built. -/
theorem isBaseChangeOverlapCompatible_of_overlapComparison (hI : I.FG)
    (hII' : I.map (algebraMap R R') = I')
    (w : ∀ (p p' : JX × JY) (hne : p ≠ p'), G'.V p p' hne ⟶ G.V p p' hne)
    (hfw : ∀ (p p' : JX × JY) (hne : p ≠ p'),
      G'.f p p' hne ≫ chartBaseChange (A := A) (B := B) hI hII' p = w p p' hne ≫ G.f p p' hne)
    (htw : ∀ (p p' : JX × JY) (hne : p ≠ p'),
      G'.t p p' hne ≫ w p' p hne.symm = w p p' hne ≫ G.t p p' hne) :
    G'.IsBaseChangeOverlapCompatible G hI hII' := by
  intro p p' hne
  have h1 : G'.f p p' hne ≫ chartBaseChange hI hII' p ≫ G.ι hI p =
      w p p' hne ≫ G.f p p' hne ≫ G.ι hI p := by
    rw [← Category.assoc, hfw p p' hne, Category.assoc]
  have h2 : G'.t p p' hne ≫ G'.f p' p hne.symm ≫ chartBaseChange hI hII' p' ≫ G.ι hI p' =
      w p p' hne ≫ G.t p p' hne ≫ G.f p' p hne.symm ≫ G.ι hI p' := by
    rw [← Category.assoc (G'.f p' p hne.symm), hfw p' p hne.symm, Category.assoc,
      ← Category.assoc, htw p p' hne, Category.assoc]
  rw [h1, h2, G.f_comp_ι hI p p' hne]

/-! ### Injectivity of the glued base change -/

/-- **The overlap saturation condition**, the second hypothesis the glued comparison needs: at
`p ≠ p'`, a point of the source's `p`-th chart whose comparison image lies in the target's overlap
of `p` and `p'` already lies in the source's overlap of that pair.

It is independent of `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapCompatible`, which
constrains the comparison only where the *source* glues; this constrains it where the *target*
does. The module docstring's *Why injectivity needs a second hypothesis* says why neither implies
the other and why no chart-level strengthening replaces this one.

Only the containment is asked for, and nothing here needs more. In the pair a smart constructor
produces both sides are built from the same away-completion data and an equality is the expected
answer, and that is what
`AlgebraicGeometry.DoubleChartGlue.preimage_range_eq_of_range_eq_bothAlgDataF` below delivers; the
containment this asks for is the weaker half of it. -/
def IsBaseChangeOverlapSaturated (hI : I.FG) (hII' : I.map (algebraMap R R') = I') : Prop :=
  ∀ (p p' : JX × JY) (hne : p ≠ p'),
    ⇑(chartBaseChange (A := A) (B := B) hI hII' p).base ⁻¹' Set.range ⇑(G.f p p' hne).base ⊆
      Set.range ⇑(G'.f p p' hne).base

/-- **The glued base change at a point of a chart.** This is
`AlgebraicGeometry.DoubleChartGlue.ι_baseChange` read through
`AlgebraicGeometry.LocallyRingedSpace.comp_base`. -/
theorem ι_baseChange_apply (hI' : I'.FG) (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
    (h : G'.IsBaseChangeOverlapCompatible G hI hII') (p : JX × JY)
    (x : (doubleChartObj R' I' A B p).toPresheafedSpace) :
    (G'.baseChange G hI' hI hII' h).base ((G'.ι hI' p).base x) =
      (G.ι hI p).base ((chartBaseChange hI hII' p).base x) := by
  have key := G'.ι_baseChange G hI' hI hII' h p
  have keyb : (G'.ι hI' p).base ≫ (G'.baseChange G hI' hI hII' h).base =
      (chartBaseChange (A := A) (B := B) hI hII' p).base ≫ (G.ι hI p).base := by
    rw [← LocallyRingedSpace.comp_base, ← LocallyRingedSpace.comp_base, key]
  have hx := ConcreteCategory.congr_hom keyb x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hx
  exact hx

/-- **The glued base change is injective on points**, given the square, the saturation, and
injectivity of every chart leg.

The argument is the one the chart legs cannot make. Two source points with the same image sit in
charts `p` and `p'`; at `p = p'` the two chart immersions and the chart leg settle it. At `p ≠ p'`
the common image puts the first point's comparison image in the target's `p`-`p'` overlap
(`AlgebraicGeometry.DoubleChartGlue.preimage_range_ι`), the saturation moves that conclusion back
across the comparison into the *source's* overlap, and
`AlgebraicGeometry.DoubleChartGlue.ι_glue_apply` transports the first point to a point of the
`p'`-th source chart with the same image in the glued source. That transported point and the second
one now sit in one chart, so the chart leg and the target's `p'`-th immersion identify them.
**Nowhere does the argument use anything about a chart leg beyond injectivity**, which is why
`AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base` can hand it a closed immersion and
gain nothing extra. -/
theorem injective_baseChange_base_of_injective_chartBaseChange (hI' : I'.FG) (hI : I.FG)
    (hII' : I.map (algebraMap R R') = I')
    (h : G'.IsBaseChangeOverlapCompatible G hI hII')
    (hsat : G'.IsBaseChangeOverlapSaturated G hI hII')
    (hinj : ∀ p : JX × JY,
      Function.Injective ⇑(chartBaseChange (A := A) (B := B) hI hII' p).base) :
    Function.Injective ⇑(G'.baseChange G hI' hI hII' h).base := by
  intro u u' huu'
  obtain ⟨p, x, rfl⟩ := G'.ι_jointly_surjective hI' u
  obtain ⟨p', y, rfl⟩ := G'.ι_jointly_surjective hI' u'
  have hchart : (G.ι hI p).base ((chartBaseChange hI hII' p).base x) =
      (G.ι hI p').base ((chartBaseChange hI hII' p').base y) := by
    rw [← G'.ι_baseChange_apply G hI' hI hII' h p, ← G'.ι_baseChange_apply G hI' hI hII' h p']
    exact huu'
  by_cases hne : p = p'
  · subst hne
    exact congrArg _ (hinj p (G.injective_ι_base hI p hchart))
  · have hx : ⇑(chartBaseChange (A := A) (B := B) hI hII' p).base x ∈
        Set.range ⇑(G.f p p' hne).base := by
      rw [← G.preimage_range_ι hI p p' hne]
      exact ⟨_, hchart.symm⟩
    obtain ⟨w, hw⟩ := hsat p p' hne hx
    obtain ⟨v, hv⟩ : x ∈ Set.range ⇑(G'.lrsGlueData.toGlueData.f p p').base := by
      rw [G'.range_lrsGlueData_f p p' hne]
      exact ⟨w, hw⟩
    have hglue := G'.ι_glue_apply hI' p p' v
    rw [hv] at hglue
    have hy : (G'.lrsGlueData.toGlueData.f p' p).base
        ((G'.lrsGlueData.toGlueData.t p p').base v) = y := by
      apply hinj p'
      apply G.injective_ι_base hI p'
      rw [← G'.ι_baseChange_apply G hI' hI hII' h p', ← G'.ι_baseChange_apply G hI' hI hII' h p',
        hglue]
      exact huu'
    rw [← hglue, hy]

section Scheme

variable [TopologicalSpace R] [IsAdicRing I]
variable [∀ i, TopologicalSpace (A i)] [∀ i, IsAdicRing (I.map (algebraMap R (A i)))]
variable [∀ j, TopologicalSpace (B j)] [∀ j, IsAdicRing (I.map (algebraMap R (B j)))]
variable [∀ p : JX × JY, IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))]
variable
  [∀ p : JX × JY, IsAdicRing (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))]

/-- **The chart-level comparison is `CompletedTensorProduct.schemeBaseChange`**, so by
`CompletedTensorProduct.schemeBaseChange_isClosedImmersion` every chart leg of
`AlgebraicGeometry.DoubleChartGlue.baseChange` is a closed immersion of affine formal schemes. What
the glued morphism inherits from that is **injectivity and nothing more**, and only against a
second hypothesis: `AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base` keeps the
injectivity half of this closed immersion and asks for the saturation besides. -/
theorem chartBaseChange_eq_schemeBaseChange (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
    (p : JX × JY) :
    chartBaseChange (A := A) (B := B) hI hII' p =
      (CompletedTensorProduct.schemeBaseChange (A := A p.1) (B := B p.2) hI hII').toLRSHom :=
  rfl

/-- **Every chart leg of the glued base change is injective on points**, being a closed immersion
by `CompletedTensorProduct.schemeBaseChange_isClosedImmersion`. This is the hypothesis
`AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base_of_injective_chartBaseChange` asks
for, and it is the only part of the chart-level closed immersion that the glued statement uses. -/
theorem injective_chartBaseChange_base (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
    (p : JX × JY) :
    Function.Injective ⇑(chartBaseChange (A := A) (B := B) hI hII' p).base :=
  (CompletedTensorProduct.schemeBaseChange_isClosedImmersion
    (A := A p.1) (B := B p.2) hI hII').base_closedEmbedding.injective

/-- **The glued base change is injective on points.** *Reach for this one*: over an adic base the
chart legs are closed immersions, so the only thing a caller owes beyond the square is the
saturation.
`AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base_of_injective_chartBaseChange` is the
form to reach for when the chart legs are not of that shape, and it is what this proof consumes. -/
theorem injective_baseChange_base (hI' : I'.FG) (hI : I.FG)
    (hII' : I.map (algebraMap R R') = I')
    (h : G'.IsBaseChangeOverlapCompatible G hI hII')
    (hsat : G'.IsBaseChangeOverlapSaturated G hI hII') :
    Function.Injective ⇑(G'.baseChange G hI' hI hII' h).base :=
  G'.injective_baseChange_base_of_injective_chartBaseChange G hI' hI hII' h hsat fun p =>
    injective_chartBaseChange_base hI hII' p

end Scheme

end BaseChange

end DoubleChartGlue

/-! ### The dispatched overlaps, and the saturation they satisfy -/

section Saturation

variable {R I A B}
variable {R' : Type u} [CommRing R'] [Algebra R R'] {I' : Ideal R'}
variable [∀ i, Algebra R' (A i)] [∀ i, IsScalarTower R R' (A i)]
variable [∀ j, Algebra R' (B j)] [∀ j, IsScalarTower R R' (B j)]

/-- **The preimage of a basic open under the chart-level comparison is the basic open of the
image.** `AlgebraicGeometry.DoubleChartGlue.chartBaseChange` is `Spf` of
`CompletedTensorProduct.baseChangeHom`, so this is `FormalSpectrum.map_preimage_basicOpen` read as
an equality of sets rather than of opens. It is the only topology in the section below: everything
else is the algebra of which element cuts out which overlap. -/
theorem DoubleChartGlue.preimage_basicOpen_chartBaseChange_base (hI : I.FG)
    (hII' : I.map (algebraMap R R') = I') (p : JX × JY)
    (c : CompletedTensorProduct R I (A p.1) (B p.2)) :
    ⇑(DoubleChartGlue.chartBaseChange (A := A) (B := B) hI hII' p).base ⁻¹'
        (FormalSpectrum.basicOpen
            (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2)) c :
          Set (FormalSpectrum
            (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2)))) =
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))
          (CompletedTensorProduct.baseChangeHom (A := A p.1) (B := B p.2) hI hII' c) :
        Set (FormalSpectrum
          (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2)))) := by
  rw [← FormalSpectrum.map_preimage_basicOpen _ _
    (CompletedTensorProduct.baseChangeHom (A := A p.1) (B := B p.2) hI hII')
    (CompletedTensorProduct.le_comap_baseChangeHom hI hII') c]
  rfl

/-- **The saturation is an equality, not merely a containment**, as soon as the two overlaps are
cut out by corresponding elements: if the target's `p`-`p'` overlap is the basic open of `c` and
the source's is the basic open of `c`'s image, then the comparison's preimage of the first *is* the
second.

This is the general criterion, and it asks nothing about the glue beyond the two ranges — which is
the reason the saturation is cheap where the square is not. A square is an equation between
morphisms and has to be traced through the transitions; a saturation is a containment of subsets of
one chart, and a chart of a fibre product carries its overlaps as basic opens. -/
theorem DoubleChartGlue.preimage_range_eq_of_range_eq_basicOpen
    (G' : DoubleChartGlue R' I' A B) (G : DoubleChartGlue R I A B) (hI : I.FG)
    (hII' : I.map (algebraMap R R') = I') (p p' : JX × JY) (hne : p ≠ p')
    (c : CompletedTensorProduct R I (A p.1) (B p.2))
    (hG : Set.range ⇑(G.f p p' hne).base =
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2)) c :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2)))))
    (hG' : Set.range ⇑(G'.f p p' hne).base =
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))
          (CompletedTensorProduct.baseChangeHom (A := A p.1) (B := B p.2) hI hII' c) :
        Set (FormalSpectrum
          (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))))) :
    ⇑(DoubleChartGlue.chartBaseChange (A := A) (B := B) hI hII' p).base ⁻¹'
        Set.range ⇑(G.f p p' hne).base = Set.range ⇑(G'.f p p' hne).base := by
  rw [hG, hG', DoubleChartGlue.preimage_basicOpen_chartBaseChange_base (A := A) (B := B) hI hII' p]

/-- **The general criterion for the saturation**, from
`AlgebraicGeometry.DoubleChartGlue.preimage_range_eq_of_range_eq_basicOpen` at every pair. The
containment `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapSaturated` asks for is the
`le_of_eq` of an equality. -/
theorem DoubleChartGlue.isBaseChangeOverlapSaturated_of_range_eq_basicOpen
    (G' : DoubleChartGlue R' I' A B) (G : DoubleChartGlue R I A B) (hI : I.FG)
    (hII' : I.map (algebraMap R R') = I')
    (c : ∀ (p p' : JX × JY), p ≠ p' → CompletedTensorProduct R I (A p.1) (B p.2))
    (hG : ∀ (p p' : JX × JY) (hne : p ≠ p'), Set.range ⇑(G.f p p' hne).base =
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))
          (c p p' hne) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2)))))
    (hG' : ∀ (p p' : JX × JY) (hne : p ≠ p'), Set.range ⇑(G'.f p p' hne).base =
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))
          (CompletedTensorProduct.baseChangeHom (A := A p.1) (B := B p.2) hI hII' (c p p' hne)) :
        Set (FormalSpectrum
          (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))))) :
    G'.IsBaseChangeOverlapSaturated G hI hII' := fun p p' hne =>
  le_of_eq (DoubleChartGlue.preimage_range_eq_of_range_eq_basicOpen G' G hI hII' p p' hne
    (c p p' hne) (hG p p' hne) (hG' p p' hne))

end Saturation

/-! ### The dispatched overlaps of a smart-constructor datum -/

section Dispatched

variable {R I A B}

open scoped Classical in
/-- **The element that cuts out the dispatched overlap.** The overlap object of two distinct
product-index charts is `AlgebraicGeometry.bothAlgDataV`, dispatched on which coordinate differs,
and its image in `Spf(A_{p.1} ⊗̂_R B_{p.2})` is a basic open in every branch: the basic open of
the second factor's away-element when only the second coordinate differs, of the first factor's
when only the first, and the intersection of the two when both differ — which is the basic open of
their product, by `FormalSpectrum.basicOpen_mul`. Collapsing the three branches to one element is
what lets a single criterion cover all three. -/
noncomputable def bothAlgDataOverlapElt (gX : ∀ i _ : JX, A i) (gY : ∀ j _ : JY, B j)
    (p p' : JX × JY) : CompletedTensorProduct R I (A p.1) (B p.2) :=
  if p.1 = p'.1 then CompletedTensorProduct.inr R I (A p.1) (B p.2) (gY p.2 p'.2)
  else if p.2 = p'.2 then CompletedTensorProduct.inl R I (A p.1) (B p.2) (gX p.1 p'.1)
  else CompletedTensorProduct.inl R I (A p.1) (B p.2) (gX p.1 p'.1) *
    CompletedTensorProduct.inr R I (A p.1) (B p.2) (gY p.2 p'.2)

/-- **The dispatched overlap immersion's range is the basic open of one element.**
`AlgebraicGeometry.range_bothAlgDataF_base` (`FormalSchemes.GeneralFibreProductBothOverlapRange`)
already computes that range, as an intersection of two branch-dispatched sets; this restates it in
the single-element form the criterion above consumes. Collapsing the intersection is
`FormalSpectrum.basicOpen_mul`, and the branch where *both* coordinates agree is `absurd`. -/
theorem range_bothAlgDataF_base_eq_basicOpen (hI : I.FG) (gX : ∀ i _ : JX, A i)
    (gY : ∀ j _ : JY, B j) (p p' : JX × JY) (h : p ≠ p') :
    Set.range ⇑(bothAlgDataF (R := R) (I := I) (A := A) (B := B) hI gX gY p p' h).base =
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))
          (bothAlgDataOverlapElt gX gY p p') :
        Set (FormalSpectrum
          (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2)))) := by
  rw [range_bothAlgDataF_base hI gX gY p p' h]
  unfold bothAlgDataOverlapElt
  by_cases h1 : p.1 = p'.1
  · rw [if_pos h1, if_pos h1, Set.univ_inter]
    by_cases h2 : p.2 = p'.2
    · exact absurd (Prod.ext h1 h2) h
    · rw [if_neg h2]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : p.2 = p'.2
    · rw [if_pos h2, if_pos h2, Set.inter_univ]
    · rw [if_neg h2, if_neg h2, FormalSpectrum.basicOpen_mul,
        TopologicalSpace.Opens.coe_inf]

variable {R' : Type u} [CommRing R'] [Algebra R R'] {I' : Ideal R'}
variable [∀ i, Algebra R' (A i)] [∀ i, IsScalarTower R R' (A i)]
variable [∀ j, Algebra R' (B j)] [∀ j, IsScalarTower R R' (B j)]

/-- **The comparison carries the dispatched overlap element to the dispatched overlap element.**
The two `if`s branch on the same pair of coordinate equalities, so the three branches match up, and
each is `CompletedTensorProduct.baseChangeHom_inl`, `..baseChangeHom_inr`, or their product. The
away-elements are the *same* elements on both sides — the chart algebras do not move
under the base change, only the base does — and that is the whole reason the saturation holds at a
smart-constructor pair. -/
theorem baseChangeHom_bothAlgDataOverlapElt (hI : I.FG)
    (hII' : I.map (algebraMap R R') = I') (gX : ∀ i _ : JX, A i) (gY : ∀ j _ : JY, B j)
    (p p' : JX × JY) :
    CompletedTensorProduct.baseChangeHom (A := A p.1) (B := B p.2) hI hII'
        (bothAlgDataOverlapElt (I := I) gX gY p p') =
      bothAlgDataOverlapElt (I := I') gX gY p p' := by
  unfold bothAlgDataOverlapElt
  split_ifs
  · exact CompletedTensorProduct.baseChangeHom_inr hI hII' _
  · exact CompletedTensorProduct.baseChangeHom_inl hI hII' _
  · rw [map_mul, CompletedTensorProduct.baseChangeHom_inl hI hII',
      CompletedTensorProduct.baseChangeHom_inr hI hII']

/-- **At a dispatched pair the saturation holds as an equality.** The hypotheses say only that the
two glues carry the dispatched overlap immersions with the *same* away-elements, which is `rfl` for
a glue the smart constructor `AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraData` produced. -/
theorem DoubleChartGlue.preimage_range_eq_of_range_eq_bothAlgDataF
    (G' : DoubleChartGlue R' I' A B) (G : DoubleChartGlue R I A B) (hI' : I'.FG) (hI : I.FG)
    (hII' : I.map (algebraMap R R') = I') (gX : ∀ i _ : JX, A i) (gY : ∀ j _ : JY, B j)
    (hG : ∀ (p p' : JX × JY) (hne : p ≠ p'), Set.range ⇑(G.f p p' hne).base =
      Set.range ⇑(bothAlgDataF hI gX gY p p' hne).base)
    (hG' : ∀ (p p' : JX × JY) (hne : p ≠ p'), Set.range ⇑(G'.f p p' hne).base =
      Set.range ⇑(bothAlgDataF hI' gX gY p p' hne).base)
    (p p' : JX × JY) (hne : p ≠ p') :
    ⇑(DoubleChartGlue.chartBaseChange (A := A) (B := B) hI hII' p).base ⁻¹'
        Set.range ⇑(G.f p p' hne).base = Set.range ⇑(G'.f p p' hne).base := by
  rw [hG p p' hne, hG' p p' hne, range_bothAlgDataF_base_eq_basicOpen,
    range_bothAlgDataF_base_eq_basicOpen,
    DoubleChartGlue.preimage_basicOpen_chartBaseChange_base (A := A) (B := B) hI hII' p,
    baseChangeHom_bothAlgDataOverlapElt (A := A) (B := B) hI hII']

/-- **The saturation, discharged at a dispatched pair.** *Reach for this one*: together with a
discharge of `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapCompatible` it is everything
`AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base` asks for beyond the standing
hypotheses. -/
theorem DoubleChartGlue.isBaseChangeOverlapSaturated_of_range_eq_bothAlgDataF
    (G' : DoubleChartGlue R' I' A B) (G : DoubleChartGlue R I A B) (hI' : I'.FG) (hI : I.FG)
    (hII' : I.map (algebraMap R R') = I') (gX : ∀ i _ : JX, A i) (gY : ∀ j _ : JY, B j)
    (hG : ∀ (p p' : JX × JY) (hne : p ≠ p'), Set.range ⇑(G.f p p' hne).base =
      Set.range ⇑(bothAlgDataF hI gX gY p p' hne).base)
    (hG' : ∀ (p p' : JX × JY) (hne : p ≠ p'), Set.range ⇑(G'.f p p' hne).base =
      Set.range ⇑(bothAlgDataF hI' gX gY p p' hne).base) :
    G'.IsBaseChangeOverlapSaturated G hI hII' := fun p p' hne =>
  le_of_eq (DoubleChartGlue.preimage_range_eq_of_range_eq_bothAlgDataF G' G hI' hI hII' gX gY
    hG hG' p p' hne)

end Dispatched

/-! ### Every datum's fibre product is one of these -/

namespace BothChartedFibreDatum

variable {R I} {hI : I.FG}

/-- The geometric glue carried by a two-sided charted fibre-product datum. -/
def toDoubleChartGlue (D : BothChartedFibreDatum R I hI) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    DoubleChartGlue R I D.A D.B :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  { V := D.V, f := D.f, hf := D.hf, t := D.t, t_inv := D.t_inv, t' := D.t',
    t_fac := D.t_fac, cocycle := D.cocycle }

/-- **The glued fibre product of a datum is the glued object of its carried glue**, by `rfl`. This
is the content of the structure above:
`AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct` reads off a datum its chart algebras
and its eight geometric fields, and nothing else — not `gX`, `gY`, `τX` or `τY`, which
`AlgebraicGeometry.BothChartedFibreDatum` carries as documentation of intent. -/
theorem generalFibreProduct_eq (D : BothChartedFibreDatum R I hI) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    D.generalFibreProduct = D.toDoubleChartGlue.fibreProduct hI := rfl

end BothChartedFibreDatum

end AlgebraicGeometry

/-! ### The first interchange branch against the chart comparison

The immersion half of *Reducing the square*, at one branch of `AlgebraicGeometry.bothAlgDataF`:
the one where the `X`-coordinate of the pair differs and the `Y`-coordinate does not, so the
overlap immersion is `CompletedTensorAwayInterchange.interchangeOpenImmersion`. The other two
branches — the conjugate by `CompletedTensorAwayInterchange.commSpfIso` and the composite of the
two — are not here, and neither is the transition half. -/

namespace CompletedTensorAwayInterchange

variable {R R' A B : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
variable [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R' A] [Algebra R' B]
variable [IsScalarTower R R' A] [IsScalarTower R R' B]
variable {I : Ideal R} {I' : Ideal R'}

/-- **The ring square of the branch**: the chart comparison at `A ⊗̂ B` followed by the primed
completed-tensor lift is the unprimed lift followed by the chart comparison at the *localized*
chart `A{1/f} ⊗̂ B`. Both sides are ring maps out of `A ⊗̂_R B`, so
`CompletedTensorProduct.hom_ext` compares them on `CompletedTensorProduct.inl` and
`CompletedTensorProduct.inr`, where each is one of `CompletedTensorProduct.baseChangeHom_inl`,
`..baseChangeHom_inr`, `CompletedTensorAwayInterchange.gCHom_inl` and `..gCHom_inr`.

The primed lift is a **hypothesis** `φ` given by its values on the two canonical maps rather than
the term `CompletedTensorAwayInterchange.gCHom I' f hI'`, and that is forced rather than stylistic:
`gCHom I' f hI'` lands in the localized chart of the *primed* base, `A{1/f}` taken at
`I'·A`, which is the same ring as `A{1/f}` taken at `I·A` (the ideals agree, by
`Ideal.map_algebraMap_of_tower`) but not the same *term*. Quantifying over `φ` is what lets the
whole transport be discharged once, in
`CompletedTensorAwayInterchange.interchangeChartBaseChange_comp_interchangeOpenImmersion`, by a
single `subst` on a variable ideal. -/
theorem baseChangeHom_comp_gCHom (f : A) (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
    (φ : CompletedTensorProduct R' I' A B →+*
      CompletedTensorProduct R' I' (awayCompletion (I.map (algebraMap R A)) f) B)
    (hφ : ∀ (m : ℕ) (x : CompletedTensorProduct R' I' A B),
      x ∈ (idealOfDefinition R' I' A B) ^ m →
        φ x ∈ (idealOfDefinition R' I' (awayCompletion (I.map (algebraMap R A)) f) B) ^ m)
    (hφl : ∀ a : A, φ (inl R' I' A B a) =
      inl R' I' (awayCompletion (I.map (algebraMap R A)) f) B
        (algebraMap A (awayCompletion (I.map (algebraMap R A)) f) a))
    (hφr : ∀ b : B, φ (inr R' I' A B b) =
      inr R' I' (awayCompletion (I.map (algebraMap R A)) f) B b) :
    φ.comp (baseChangeHom (A := A) (B := B) hI hII') =
      (baseChangeHom (A := awayCompletion (I.map (algebraMap R A)) f) (B := B) hI hII').comp
        (gCHom I f hI) := by
  haveI : IsAdicComplete (idealOfDefinition R' I' (awayCompletion (I.map (algebraMap R A)) f) B)
      (CompletedTensorProduct R' I' (awayCompletion (I.map (algebraMap R A)) f) B) :=
    (isAdicRing R' I' (awayCompletion (I.map (algebraMap R A)) f) B
      (fg_of_map_eq hI hII')).toIsAdicComplete
  refine hom_ext (idealOfDefinition R' I' (awayCompletion (I.map (algebraMap R A)) f) B) hI
    (fun m x hx => ?_) (fun m x hx => ?_) (fun a => ?_) (fun b => ?_)
  · rw [RingHom.comp_apply]
    exact hφ m _ (baseChangeHom_mem_pow hI hII' m hx)
  · rw [RingHom.comp_apply]
    exact baseChangeHom_mem_pow hI hII' m (gCHom_mem_pow I f hI m hx)
  · rw [RingHom.comp_apply, RingHom.comp_apply, baseChangeHom_inl, hφl a, gCHom_inl, gA_apply,
      baseChangeHom_inl]
  · rw [RingHom.comp_apply, RingHom.comp_apply, baseChangeHom_inr, hφr b, gCHom_inr,
      baseChangeHom_inr]

/-- **The localized double chart depends on the away ideal only through its value.** Written as an
equality of locally ringed spaces rather than as a transport of rings, because that is the only
form the branch's comparison needs: the two ideals of `A` in play are `I·A` and `I'·A`, which agree
under `I.map (algebraMap R R') = I'` by `Ideal.map_algebraMap_of_tower`
(`FormalSchemes.AwayTopFiniteType`), and `FormalSpectrum.locallyRingedSpaceObj` lands in a type
that does not mention the ideal, so `congrArg` suffices and no `subst` is needed here. -/
theorem interchangeChartObj_congr {K L : Ideal A} (h : K = L) (f : A) :
    locallyRingedSpaceObj (idealOfDefinition R' I' (awayCompletion K f) B) =
      locallyRingedSpaceObj (idealOfDefinition R' I' (awayCompletion L f) B) :=
  congrArg (fun J : Ideal A =>
    locallyRingedSpaceObj (idealOfDefinition R' I' (awayCompletion J f) B)) h

/-- **The comparison of the two glues' overlap objects at this branch**, which is the `w` that
`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_overlapComparison` asks for:
the chart-level base change at the *localized* chart `A{1/f}`, preceded by the transport that
identifies the primed localized chart with the unprimed one.

The transport is the whole of the bookkeeping this branch costs — one `eqToHom` over one
`congrArg`, and no family of transported ring maps. The away ideal is left as a parameter `K` with
`hK : K = I·A` so that the theorem below can `subst` it; a caller wanting the primed glue's overlap
object passes `K := I'.map (algebraMap R' A)` and
`hK := (Ideal.map_algebraMap_of_tower I I' hII').symm`. -/
def interchangeChartBaseChange {K : Ideal A} (hK : K = I.map (algebraMap R A)) (f : A) (hI : I.FG)
    (hII' : I.map (algebraMap R R') = I') :
    locallyRingedSpaceObj (idealOfDefinition R' I' (awayCompletion K f) B) ⟶
      locallyRingedSpaceObj
        (idealOfDefinition R I (awayCompletion (I.map (algebraMap R A)) f) B) :=
  eqToHom (interchangeChartObj_congr hK f) ≫
    locallyRingedSpaceMap (idealOfDefinition R I (awayCompletion (I.map (algebraMap R A)) f) B)
      (idealOfDefinition R' I' (awayCompletion (I.map (algebraMap R A)) f) B)
      (baseChangeHom hI hII') (le_comap_baseChangeHom hI hII')

/-- **The geometric square of the branch, over an abstract primed lift.** Every leg is a
`FormalSpectrum.locallyRingedSpaceMap`, so `FormalSpectrum.locallyRingedSpaceMap_comp` merges each
side into a single one and the whole statement reduces to the ring square
`CompletedTensorAwayInterchange.baseChangeHom_comp_gCHom`; the transport of
`CompletedTensorAwayInterchange.interchangeChartBaseChange` is an `eqToHom` at a reflexive equality
once `hK` has been substituted, and disappears.

This is the one place the branch pays for the two localized charts being equal rather than
identical, and it pays once. -/
theorem interchangeChartBaseChange_comp_interchangeOpenImmersion {K : Ideal A}
    (hK : K = I.map (algebraMap R A)) (f : A) (hI : I.FG)
    (hII' : I.map (algebraMap R R') = I')
    (φ : CompletedTensorProduct R' I' A B →+* CompletedTensorProduct R' I' (awayCompletion K f) B)
    (hφle : idealOfDefinition R' I' A B ≤
      (idealOfDefinition R' I' (awayCompletion K f) B).comap φ)
    (hφ : ∀ (m : ℕ) (x : CompletedTensorProduct R' I' A B),
      x ∈ (idealOfDefinition R' I' A B) ^ m →
        φ x ∈ (idealOfDefinition R' I' (awayCompletion K f) B) ^ m)
    (hφl : ∀ a : A, φ (inl R' I' A B a) =
      inl R' I' (awayCompletion K f) B (algebraMap A (awayCompletion K f) a))
    (hφr : ∀ b : B, φ (inr R' I' A B b) = inr R' I' (awayCompletion K f) B b) :
    locallyRingedSpaceMap (idealOfDefinition R' I' A B)
          (idealOfDefinition R' I' (awayCompletion K f) B) φ hφle ≫
        locallyRingedSpaceMap (idealOfDefinition R I A B) (idealOfDefinition R' I' A B)
          (baseChangeHom (A := A) (B := B) hI hII') (le_comap_baseChangeHom hI hII') =
      interchangeChartBaseChange hK f hI hII' ≫ interchangeOpenImmersion I f hI := by
  subst hK
  have hlhs : idealOfDefinition R I A B ≤
      (idealOfDefinition R' I' (awayCompletion (I.map (algebraMap R A)) f) B).comap
        (φ.comp (baseChangeHom (A := A) (B := B) hI hII')) := by
    rw [← Ideal.comap_comap]
    exact (le_comap_baseChangeHom hI hII').trans (Ideal.comap_mono hφle)
  have hrhs : idealOfDefinition R I A B ≤
      (idealOfDefinition R' I' (awayCompletion (I.map (algebraMap R A)) f) B).comap
        ((baseChangeHom (A := awayCompletion (I.map (algebraMap R A)) f) (B := B) hI hII').comp
          (gCHom I f hI)) := by
    rw [← Ideal.comap_comap]
    exact (gCHom_le_comap I f hI).trans (Ideal.comap_mono (le_comap_baseChangeHom hI hII'))
  rw [interchangeChartBaseChange]
  simp only [eqToHom_refl, Category.id_comp]
  rw [interchangeOpenImmersion_eq_map,
    ← locallyRingedSpaceMap_comp _ _ _ _ _ _ _ hlhs,
    ← locallyRingedSpaceMap_comp _ _ _ _ _ _ _ hrhs]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _
    (baseChangeHom_comp_gCHom f hI hII' φ hφ hφl hφr)

/-- **The square of the branch.** *Reach for this one*: the interchange open immersion of the
primed base, followed by the chart comparison, is the overlap comparison
`CompletedTensorAwayInterchange.interchangeChartBaseChange` followed by the interchange open
immersion of the unprimed base.

This is the first hypothesis of
`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_overlapComparison` at the
branch where the `X`-coordinate differs and the `Y`-coordinate does not, with the `eqToHom` of
`AlgebraicGeometry.bothAlgDataV_fst` still to be crossed on each side — that crossing, and the
other two branches, belong to the assembly. -/
theorem interchangeOpenImmersion_comp_baseChange (f : A) (hI : I.FG)
    (hII' : I.map (algebraMap R R') = I') :
    interchangeOpenImmersion (B := B) I' f (fg_of_map_eq hI hII') ≫
        locallyRingedSpaceMap (idealOfDefinition R I A B) (idealOfDefinition R' I' A B)
          (baseChangeHom (A := A) (B := B) hI hII') (le_comap_baseChangeHom hI hII') =
      interchangeChartBaseChange (Ideal.map_algebraMap_of_tower I I' hII').symm f hI hII' ≫
        interchangeOpenImmersion I f hI := by
  rw [interchangeOpenImmersion_eq_map]
  refine interchangeChartBaseChange_comp_interchangeOpenImmersion
    (Ideal.map_algebraMap_of_tower I I' hII').symm f hI hII' _ _
    (gCHom_mem_pow I' f (fg_of_map_eq hI hII')) (fun a => ?_)
    (gCHom_inr I' f (fg_of_map_eq hI hII'))
  rw [gCHom_inl, gA_apply]

end CompletedTensorAwayInterchange

namespace AlgebraicGeometry.DoubleChartGlue

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
variable {I : Ideal R} {I' : Ideal R'}
variable {JX JY : Type u} {A : JX → Type u} {B : JY → Type u}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
variable [∀ i, Algebra R' (A i)] [∀ i, IsScalarTower R R' (A i)]
variable [∀ j, Algebra R' (B j)] [∀ j, IsScalarTower R R' (B j)]

/-- **The square of the branch, in the chart vocabulary of this file.**
`AlgebraicGeometry.DoubleChartGlue.chartBaseChange` at the pair `p` is by definition the morphism
`FormalSpectrum.locallyRingedSpaceMap` of `CompletedTensorProduct.baseChangeHom` at the chart
algebras `A p.1` and `B p.2`, so this is
`CompletedTensorAwayInterchange.interchangeOpenImmersion_comp_baseChange` with nothing added; it is
stated so that an assembly of the three branches can consume it without restating it. -/
theorem interchangeOpenImmersion_comp_chartBaseChange (hI : I.FG)
    (hII' : I.map (algebraMap R R') = I') (p : JX × JY) (g : A p.1) :
    CompletedTensorAwayInterchange.interchangeOpenImmersion (B := B p.2) I' g
          (CompletedTensorProduct.fg_of_map_eq hI hII') ≫
        chartBaseChange (A := A) (B := B) hI hII' p =
      CompletedTensorAwayInterchange.interchangeChartBaseChange
          (Ideal.map_algebraMap_of_tower I I' hII').symm g hI hII' ≫
        CompletedTensorAwayInterchange.interchangeOpenImmersion I g hI :=
  CompletedTensorAwayInterchange.interchangeOpenImmersion_comp_baseChange g hI hII'

end AlgebraicGeometry.DoubleChartGlue

end
