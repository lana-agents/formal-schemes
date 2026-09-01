import FormalSchemes.GlueDataImageInter
import FormalSchemes.ProjectiveLineCompletion

set_option linter.style.header false

/-!
# Where one chart of the glued scheme sits inside another, at an arbitrary index

`FormalSchemes/ChartedSchemeDatum.lean` glues the affine charts `Spec (C i)` of a
`AlgebraicGeometry.ChartedSchemeDatum` along the basic opens `D(g i j)` into
`AlgebraicGeometry.ChartedSchemeDatum.specGlued`, with `..specι i` the `i`-th chart. Everything
proved about that object so far is *covering* information — the charts are open immersions and they
are jointly surjective. Nothing said where two charts **meet**.

This file says it: the part of the `i`-th chart that lands in the `j`-th is exactly the basic open
`D(g i j)` it was glued along, and no more. That is the arbitrary-index form of
`AlgebraicGeometry.preimage_range_specTwoPatchι₀` / `..ι₁`
(`FormalSchemes.CompletionTwoPatchSupport`), and of
`AlgebraicGeometry.specTwoPatchι₀_base_notMem_range_specTwoPatchι₁`
(`FormalSchemes.SpecTwoPatchNonAffine`).

## The route, and why it is short

The two-patch proof hand-rolls both inclusions out of
`AlgebraicGeometry.LocallyRingedSpace.GlueData.range_ι_inter_subset` and the glue condition, in
about forty lines. None of that is repeated here. Mathlib proves the statement on carriers
(`TopCat.GlueData.preimage_range`), and `FormalSchemes.GlueDataImageInter` now transports it to a
`AlgebraicGeometry.LocallyRingedSpace.GlueData` as
`AlgebraicGeometry.LocallyRingedSpace.GlueData.preimage_range_ι`; what is left here is to identify
the glue datum's overlap inclusion `f i j` with the affine chart `specAwayMap (g i j)`, whose range
is `D(g i j)` by `AlgebraicGeometry.range_specAwayMap`.

**Note the hypothesis this file does *not* use.** `AlgebraicGeometry.ChartedSchemeDatum` carries the
ideal compatibility `hθ`, and it plays no part below: this is a statement about the ambient glued
scheme, not about the ideals `K i`. The first place `hθ` is spent on the two-patch line is
`FormalSchemes.CompletionTwoPatchSupport`, one layer further up, where the *completion*'s image is
computed chart by chart; that layer is still missing at an arbitrary index and these lemmas are its
first input.

## Main results

* `AlgebraicGeometry.ChartedSchemeDatum.range_specLRSGlueData_f_of_ne`: off the diagonal the glue
  datum's overlap inclusion has range `D(g i j)`.
* `AlgebraicGeometry.ChartedSchemeDatum.specι_injective`: each chart is injective on points.
* `AlgebraicGeometry.ChartedSchemeDatum.preimage_range_specι`: **the charts meet exactly over the
  overlap**, `specι i ⁻¹' range (specι j) = D(g i j)`.
* `AlgebraicGeometry.ChartedSchemeDatum.specι_base_notMem_range_specι`: the properness form — a
  point of the `i`-th chart outside `D(g i j)` is not in the `j`-th chart.
* `AlgebraicGeometry.ChartedCompletionDatum.preimage_range_specι` and
  `..specι_base_notMem_range_specι`: the same, read at a completion datum.
* `AlgebraicGeometry.preimage_range_projectiveLine_specι` and
  `AlgebraicGeometry.projectiveLine_specι_false_base_notMem_range`: the witness, at
  `AlgebraicGeometry.projectiveLineDatum` — the part of `Spec R[X]` that lands in the second chart
  of the projective line is `D(X)`, so a prime containing `X` maps outside the second chart.

## What is *not* proved

* **Nothing about the completion.** The image of `AlgebraicGeometry.ChartedCompletionDatum.toScheme`
  and, above it, its chart *preimage* — the statement that needs `hθ` and the glue datum's
  `glue_condition`, and whose two-patch form is `FormalSchemes.CompletionTwoPatchSupport` — are a
  separate line of work. These lemmas are an input to that preimage rather than a step of it: the
  `j ≠ i` terms it has to dispose of are exactly the ones `preimage_range_specι` locates.
* No injectivity of `toScheme.base` and no closed embedding. Both are priced as open even two
  patches down in `FormalSchemes.CompletionTwoPatchClosed`.
* The two-patch statements are not retired in favour of these. They are stated at a glue datum built
  by a different route, and rewiring them has no consumer.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
-/

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace ChartedSchemeDatum

variable (D : ChartedSchemeDatum.{u})

/-! ### The overlap inclusion of the glue datum -/

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- The transparency requirement is the one
-- `AlgebraicGeometry.range_specTwoPatchLRSGlueData_f_false_true` documents: the glue datum is a
-- `def`, so its index type does not reduce to `D.J` at `instances` transparency and the `dif_neg`
-- rewrite is otherwise rejected as ill-typed.
/-- **Off the diagonal, the glue datum's overlap inclusion is the affine chart of `D(g i j)`.**
`CategoryTheory.GlueData.ofGlueData'` pads the diagonal, so `f i j` is `specAwayMap (g i j)`
preceded by an `eqToHom`; an `eqToHom` is an isomorphism and does not change a range. The
arbitrary-index form of `AlgebraicGeometry.range_specTwoPatchLRSGlueData_f_false_true`. -/
theorem range_specLRSGlueData_f_of_ne (i j : D.J) (hij : i ≠ j) :
    Set.range (D.specLRSGlueData.toGlueData.f i j).base =
      (PrimeSpectrum.basicOpen (D.g i j) : Set (PrimeSpectrum (D.C i))) := by
  -- The `dite` condition lives at `D.J` while the glue datum indexes by `D.specLRSGlueData.J`, so
  -- the disequality has to be re-typed before `dif_neg` fires.
  have hij' : ¬ @Eq D.J i j := hij
  have h : D.specLRSGlueData.toGlueData.f i j =
      eqToHom (dif_neg hij') ≫ specAwayMap (D.g i j) := dif_neg hij'
  rw [h, LocallyRingedSpace.range_eqToHom_comp_base]
  -- `rw` elaborates at `instances` transparency and fails here; `exact` does not.
  exact range_specAwayMap (D.g i j)

/-! ### The charts meet exactly over the overlap -/

/-- **Each chart of the glued scheme is injective on points**, being an open immersion. -/
theorem specι_injective (i : D.J) : Function.Injective ⇑(D.specι i).base :=
  (D.specι_isOpenImmersion i).base_open.injective

/-- **The charts meet exactly over the overlap.** The part of the `i`-th chart `Spec (C i)` that
lands in the `j`-th chart is precisely the basic open `D(g i j)` the two were glued along.

The arbitrary-index form of `AlgebraicGeometry.preimage_range_specTwoPatchι₁`, and — unlike that
one — an immediate consequence of
`AlgebraicGeometry.LocallyRingedSpace.GlueData.preimage_range_ι`. The compatibility hypothesis `hθ`
plays no part: this is a statement about the ambient glued scheme, not about the ideals. -/
theorem preimage_range_specι (i j : D.J) (hij : i ≠ j) :
    ⇑(D.specι i).base ⁻¹' Set.range ⇑(D.specι j).base =
      (PrimeSpectrum.basicOpen (D.g i j) : Set (PrimeSpectrum (D.C i))) := by
  exact (D.specLRSGlueData.preimage_range_ι j i).trans
    (D.range_specLRSGlueData_f_of_ne i j hij)

/-- **A point outside the overlap is not in the other chart.** The properness form of
`ChartedSchemeDatum.preimage_range_specι`, and the arbitrary-index form of
`AlgebraicGeometry.specTwoPatchι₀_base_notMem_range_specTwoPatchι₁`: together with
`ChartedSchemeDatum.specGlued_jointly_surjective` it pins the gluing down to `D(g i j)` and nowhere
else. -/
theorem specι_base_notMem_range_specι (i j : D.J) (hij : i ≠ j) {p : PrimeSpectrum (D.C i)}
    (hp : p ∉ (PrimeSpectrum.basicOpen (D.g i j) : Set (PrimeSpectrum (D.C i)))) :
    (D.specι i).base p ∉ Set.range ⇑(D.specι j).base := fun hmem =>
  hp ((D.preimage_range_specι i j hij) ▸ hmem)

end ChartedSchemeDatum

namespace ChartedCompletionDatum

variable (D : ChartedCompletionDatum.{u})

/-- **The charts of the ambient scheme meet exactly over the overlap**, read at a completion datum.
`ChartedCompletionDatum.specι` delegates to `ChartedSchemeDatum.specι` through
`toChartedSchemeDatum`, so this is that datum's statement with no transport. -/
theorem preimage_range_specι (i j : D.J) (hij : i ≠ j) :
    ⇑(D.specι i).base ⁻¹' Set.range ⇑(D.specι j).base =
      (PrimeSpectrum.basicOpen (D.g i j) : Set (PrimeSpectrum (D.C i))) :=
  D.toChartedSchemeDatum.preimage_range_specι i j hij

/-- **A point outside the overlap is not in the other chart**, read at a completion datum. -/
theorem specι_base_notMem_range_specι (i j : D.J) (hij : i ≠ j) {p : PrimeSpectrum (D.C i)}
    (hp : p ∉ (PrimeSpectrum.basicOpen (D.g i j) : Set (PrimeSpectrum (D.C i)))) :
    (D.specι i).base p ∉ Set.range ⇑(D.specι j).base :=
  D.toChartedSchemeDatum.specι_base_notMem_range_specι i j hij hp

end ChartedCompletionDatum

/-! ### The witness: the projective line -/

section Witness

open Polynomial

variable (R : Type u) [CommRing R]

/-- **The two charts of the projective line meet exactly over `D(X)`.** The part of the first chart
`Spec R[X]` that lands in the second is the complement of the origin, which is what the projective
line is glued along.

This is the witness for `ChartedSchemeDatum.preimage_range_specι`: `projectiveLineDatum` has two
charts with *independent* ideals, and the statement here is about the ambient gluing, so it is
visibly not the trivial identity — `D(X)` is neither empty nor everything for `R` nontrivial
(`AlgebraicGeometry.span_X_ne_top` is the ideal-level form of the second).

The index disequality is `AlgebraicGeometry.cgcNe`
(`FormalSchemes.CompletionGlueTwoPatchCondition`) rather than a fresh `by simp`: the tree already
carries five copies of `¬ @Eq (ULift Bool) ⟨false⟩ ⟨true⟩`, one of them public, and a sixth would be
the lemma multiplication this development has had to undo before. Note that `by decide` does **not**
work in this position — the goal carries the free variable `R`. -/
theorem preimage_range_projectiveLine_specι :
    ⇑((projectiveLineDatum R).specι ⟨false⟩).base ⁻¹'
        Set.range ⇑((projectiveLineDatum R).specι ⟨true⟩).base =
      (PrimeSpectrum.basicOpen (X : R[X]) : Set (PrimeSpectrum R[X])) :=
  (projectiveLineDatum R).preimage_range_specι ⟨false⟩ ⟨true⟩ cgcNe

/-- **The origin of the first chart of the projective line is not in the second chart.** A prime of
`R[X]` containing `X` lies outside `D(X)`, hence outside the overlap, hence its image in
`projectiveLine R` is not reached by the second chart at all.

This is the properness form at the witness: it exhibits a point of the glued scheme that one chart
sees and the other does not, which a statement about the *ranges* alone cannot. The point it
produces is the one the completion of the projective line is supported at — `K ⟨false⟩` is
`Ideal.span {X}` — so it is also the point a later chart-preimage statement will have to keep
inside the image. -/
theorem projectiveLine_specι_false_base_notMem_range (p : PrimeSpectrum R[X])
    (hp : (X : R[X]) ∈ p.asIdeal) :
    ((projectiveLineDatum R).specι ⟨false⟩).base p ∉
      Set.range ⇑((projectiveLineDatum R).specι ⟨true⟩).base :=
  (projectiveLineDatum R).specι_base_notMem_range_specι ⟨false⟩ ⟨true⟩ cgcNe
    (by
      rw [projectiveLineDatum_g_false_true]
      intro hmem
      exact (PrimeSpectrum.mem_basicOpen (X : R[X]) p).mp hmem hp)

end Witness

end AlgebraicGeometry

end
