import FormalSchemes.ProjectiveLineCompletion

set_option linter.style.header false

/-!
# The underlying set of `X_{/Y}` inside `X`, at an arbitrary index (EGA I, 10.8)

`FormalSchemes/ChartedCompletionToScheme.lean` builds `ChartedCompletionDatum.toScheme`, the
canonical morphism `X_{/Y} ⟶ X` from the glued completion of a charted datum to the glued scheme,
and characterises it *categorically*: chart by chart (`..completionι_comp_toScheme`), and uniquely
so (`..toScheme_unique`). Nothing there says what it does to **points**.

For an affine `X` that question is settled in `FormalSchemes/CompletionToSpec.lean`:
`formalCompletion.range_toSpec_base` says the image of `Spf R^ ⟶ Spec R` is the zero locus `V(I)`.
`FormalSchemes/CompletionTwoPatchRange.lean` lifts that to the **two**-patch glued scheme on
`ULift Bool`. This file is the arbitrary-index version, which is the shape EGA I 10.8 is stated in:
*the completion of `X` along `Y` is supported on `Y`*, with `Y` glued from the `V (K i)`.

## What is proved

```
range (D.toScheme).base = ⋃ i, (D.specι i).base '' V (K i)
```

(`ChartedCompletionDatum.range_toScheme_base`), off two facts used in both directions: the
completion charts cover (`..completionGlued_jointly_surjective`), and on each of them the morphism
is the affine `formalCompletion.toSpec` (`..toScheme_base_completionι`), whose range is the zero
locus. **The compatibility hypotheses `hθ` and `hσθ` play no part** — they are what make the two
glued objects exist, not what computes this image. That is the same observation
`FormalSchemes/CompletionTwoPatchRange.lean` makes two patches down, and it survives the
generalisation unchanged: a `⋃` replaces a two-term `∪` and the `ULift Bool` case split disappears,
so the proof is shorter here than there rather than longer.

## The witness, and why it is the projective line

`AlgebraicGeometry.range_projectiveLineCompletionToScheme_base` runs the theorem at
`AlgebraicGeometry.projectiveLineDatum`: the projective line over `R`, completed at the origin of
its first chart. Its second chart ideal is `⊤`, so that chart contributes `V (⊤) = ∅` and the union
**collapses to a single term**. This is the point of taking that datum rather than an
`ofTwoPatch` with two proper ideals: the general statement is a union over the whole index type,
and a witness in which every term contributes cannot show that a term ever drops out. The
collapse is also visible one level down — `AlgebraicGeometry.isEmpty_projectiveLine_chart_true`
already says the second completion chart is empty as a space.

## What is *not* proved *here*

* **No chart preimage, and hence no closedness.** The two-patch line continues
  `ι₀⁻¹(range) = V(I)` (`FormalSchemes/CompletionTwoPatchSupport.lean`) and then "the image is
  closed" (`FormalSchemes/CompletionTwoPatchClosed.lean`). Neither is in this file, and the
  preimage is where `hθ` and the glue datum's `glue_condition` are spent — that file's "Why `hθ`
  had to appear here and nowhere earlier" section is the map. **Both are now available one and two
  files downstream**, as `AlgebraicGeometry.ChartedCompletionDatum.preimage_range_toScheme_base`
  (`FormalSchemes.ChartedCompletionSupport`) and
  `..isClosed_range_toScheme_base` (`FormalSchemes.ChartedCompletionClosed`); nothing in *this*
  file's proofs is progress on either, which is the point of saying so.
* **No properness statement.** `CompletionTwoPatchRange.lean` pairs its range computation with
  `notMem_range_completionTwoPatchToScheme_base`, on the ground that an equality of sets is
  compatible with the image being *everything*, and the proof of that runs through
  `specTwoPatchι₀_base_notMem_range_specTwoPatchι₁`. What the projective-line witness below gives
  instead is that the union *collapses*, which is a statement about the shape of the image rather
  than about its complement. The arbitrary-index twin of that `notMem_range` — the brick this
  file recorded as missing — is
  `AlgebraicGeometry.ChartedSchemeDatum.specι_base_notMem_range_specι`
  (`FormalSchemes.ChartedSchemeDatumChartOverlap`), and the properness statement it yields is
  `..ChartedCompletionDatum.notMem_range_toScheme_base`.
* No closed embedding **here**, and it is no longer open at either index. It needs injectivity of
  the base map and hence the converse of `FormalSchemes.CompletionTwoPatchDoubled`'s overlap
  analysis, which is `formalCompletion.mem_range_basicOpenImmersion`
  (`FormalSchemes.CompletionBasicOpenMap`); the two statements are
  `AlgebraicGeometry.isClosedEmbedding_completionTwoPatchToScheme_base`
  (`FormalSchemes.CompletionTwoPatchEmbedding`) two patches down and
  `AlgebraicGeometry.ChartedCompletionDatum.isClosedEmbedding_toScheme_base`
  (`FormalSchemes.ChartedCompletionEmbedding`) at an arbitrary index.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace ChartedCompletionDatum

variable (D : ChartedCompletionDatum.{u})

/-! ### The base map of the canonical morphism, chart by chart -/

/-- **On the `i`-th chart, the canonical morphism is the affine `formalCompletion.toSpec`.** This
is `ChartedCompletionDatum.completionι_comp_toScheme` evaluated at a point. -/
theorem toScheme_base_completionι (i : D.J) (z : D.chart i) :
    D.toScheme.base ((D.completionι i).base z) =
      (D.specι i).base ((formalCompletion.toSpec (D.C i) (D.K i) (D.hK i)).base z) := by
  simpa using congrArg (fun m : D.chart i ⟶ D.specGlued => m.base z)
    (D.completionι_comp_toScheme i)

/-! ### The range -/

/-- **The glued completion is supported on the glued closed subset** (EGA I, 10.8). The image of
`ChartedCompletionDatum.toScheme` is the union, over the charts, of the images of the zero loci
`V (K i)`.

Both inclusions are the same two facts used twice: the completion charts cover
(`ChartedCompletionDatum.completionGlued_jointly_surjective`), and on each of them the morphism is
the affine `formalCompletion.toSpec` (`ChartedCompletionDatum.toScheme_base_completionι`), whose
range is the zero locus (`formalCompletion.range_toSpec_base`). In particular neither `hθ` nor
`hσθ` is used: they are needed to *build* the glued objects, not to compute this image. -/
theorem range_toScheme_base :
    Set.range ⇑D.toScheme.base =
      ⋃ i : D.J,
        ⇑(D.specι i).base '' PrimeSpectrum.zeroLocus ((D.K i : Ideal (D.C i)) : Set (D.C i)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨i, z, rfl⟩ := D.completionGlued_jointly_surjective y
    refine Set.mem_iUnion.mpr ⟨i, (formalCompletion.toSpec (D.C i) (D.K i) (D.hK i)).base z, ?_,
      (D.toScheme_base_completionι i z).symm⟩
    rw [← formalCompletion.range_toSpec_base (D.C i) (D.K i) (D.hK i)]
    exact ⟨z, rfl⟩
  · intro hx
    obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp hx
    rw [← formalCompletion.range_toSpec_base (D.C i) (D.K i) (D.hK i)] at hp
    obtain ⟨z, rfl⟩ := hp
    exact ⟨(D.completionι i).base z, D.toScheme_base_completionι i z⟩

/-- **A chart whose ideal is the unit ideal contributes nothing to the image.** `Spf` of a ring
modulo `⊤` is empty, so the `i`-th term of `ChartedCompletionDatum.range_toScheme_base` is empty
exactly when `K i = ⊤`; this is the direction the projective line needs. -/
theorem image_zeroLocus_eq_empty_of_eq_top {i : D.J} (hi : D.K i = ⊤) :
    ⇑(D.specι i).base '' PrimeSpectrum.zeroLocus ((D.K i : Ideal (D.C i)) : Set (D.C i)) = ∅ := by
  rw [hi, Submodule.top_coe, PrimeSpectrum.zeroLocus_univ]
  exact Set.image_empty _

end ChartedCompletionDatum

/-! ### The witness: the projective line completed at the origin of its first chart -/

section Witness

open Polynomial

variable (R : Type u) [CommRing R]

/-- **The image of `X_{/Y} ⟶ X` for the projective line completed at the origin of its first
chart**: the `⊤`-chart drops out of the union, so the image is the first chart's copy of `V (X)`
alone.

This is the point of running the general theorem at
`AlgebraicGeometry.projectiveLineDatum` rather than at an `ofTwoPatch` with two proper ideals —
the general statement is a union over the whole index type, and a witness in which every term
contributes cannot exhibit a term dropping out. -/
theorem range_projectiveLineCompletionToScheme_base :
    Set.range ⇑(projectiveLineCompletionToScheme R).base =
      ⇑((projectiveLineDatum R).specι ⟨false⟩).base ''
        PrimeSpectrum.zeroLocus ((Ideal.span {(X : R[X])} : Ideal R[X]) : Set R[X]) := by
  change Set.range ⇑(projectiveLineDatum R).toScheme.base = _
  rw [(projectiveLineDatum R).range_toScheme_base]
  refine subset_antisymm (Set.iUnion_subset fun i => ?_) fun y hy =>
    Set.mem_iUnion.mpr ⟨⟨false⟩, hy⟩
  obtain ⟨b⟩ := i
  cases b with
  | false => exact subset_rfl
  | true =>
    rw [(projectiveLineDatum R).image_zeroLocus_eq_empty_of_eq_top
      (projectiveLineDatum_K_true R)]
    exact Set.empty_subset _

end Witness

end AlgebraicGeometry

end
