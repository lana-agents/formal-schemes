import FormalSchemes.ChartedSchemeDatumDesc
import FormalSchemes.GlueDataImageInter
import FormalSchemes.LocallyRingedSpaceRange

set_option linter.style.header false

/-!
# The charts of the glued scheme meet exactly over their overlaps (EGA I, 10.8)

`FormalSchemes.ChartedSchemeDatum` glues the affine charts `Spec (C i)` of a
`AlgebraicGeometry.ChartedSchemeDatum` along the localization transitions `θ i j`, and
`FormalSchemes.ChartedSchemeDatumDesc` supplies the universal property. Neither says anything about
**where the charts sit** inside the glued space: everything proved about `specι` so far is either
categorical or the containment `AlgebraicGeometry.LocallyRingedSpace.GlueData.range_ι_inter_subset`.

This file computes the intersection, as an equality:

```
(specι i)⁻¹ (range (specι j)) = D (g i j)        for i ≠ j
```

and the refinement of it that names *which* part of the `j`-th chart a given subset comes from:

```
(specι i)⁻¹ (specι j '' U) = D(g i j)-chart '' (θ i j-translate)⁻¹ (overlap chart⁻¹ U)
```

That is the arbitrary-index form of `AlgebraicGeometry.preimage_range_specTwoPatchι₁`
(`FormalSchemes.SpecTwoPatchNonAffine`). Both halves come at once from
`AlgebraicGeometry.LocallyRingedSpace.GlueData.preimage_range_ι`
(`FormalSchemes.GlueDataImageInter`), which is Mathlib's `TopCat.GlueData.preimage_range`
transported across the carrier comparison: the topological gluing already knows that
`ι j ⁻¹' range (ι i)` is the range of the overlap inclusion, for any glue datum whatever. All that
is left here is to say which affine chart that overlap inclusion is.

## Why this is the brick the support statement needs

`FormalSchemes.ChartedCompletionRange` computes the image of `X_{/Y} ⟶ X` at an arbitrary index as
`⋃ i, (specι i) '' V (K i)`, and stops: the chart preimage of that union needs to know that the
`j ≠ i` terms only ever reach the `i`-th chart inside `D (g i j)`, which is exactly the statement
above. That file records the absence of any range computation for `specι` as the reason it cannot
continue, and this file is the answer to it.

Nothing here uses the ideals `K i` or the compatibility `hθ`: this is a statement about the glued
**scheme**, not about any completion of it. `hθ` enters one file later, where the zero loci do.
Neither statement here opens the glue datum's `glue_condition` field either — both come from the
topological gluing, where the glue condition is spent inside Mathlib's
`TopCat.GlueData.image_inter`: one level below `TopCat.GlueData.preimage_range`, two below
`TopCat.GlueData.preimage_image_eq_image`.

## The glue condition at a point is deliberately not stated, here or two patches down

This file used to carry the glue condition read at a point at an arbitrary index, and
`FormalSchemes/CompletionTwoPatchSupport.lean` used to carry the two-patch pair together with a
`B`-side morphism-level companion whose only consumer was one of them. All four lost their last
consumer when the chart preimages were rerouted through the topological gluing, and all four are
now gone. Their names are deliberately not repeated here: a backticked name that resolves to
nothing is itself a defect on this tree.

**The rule, stated once here so that it is not re-derived a fourth time.** A zero-consumer
*point-level* reading of a morphism-level identity that keeps its own consumers is **deleted**,
not kept and flagged. The identity is where the fact lives, and the reading is one
`congrArg` at the point followed by a `simp only` that pushes `.base` through the composite — so
nothing is lost that a future consumer cannot restate in four lines, at the shape it actually
wants. Here the surviving identity is
`AlgebraicGeometry.ChartedSchemeDatum.specAwayMap_comp_specι`
(`FormalSchemes.ChartedSchemeDatumDesc`); two patches down it is
`AlgebraicGeometry.specTwoPatch_glue` (`FormalSchemes.CompletionTwoPatchToScheme`). Both keep
consumers of their own.

Three successive pull requests each re-argued this judgement in a different docstring, each time
keeping the declarations on the speculative ground that a datum-level mapping-out argument needing
to name *which* prime of `C j` a prime of `D (g i j)` becomes would want them. No such consumer
appeared. The nearest live mapping-out row is the `Spf`-target analogue of EGA I 10.6.10, whose
remaining content is the surjectivity of `FormalSpectrum.restrictToThickeningsLRS` — a question
about sections of `𝒪_{Spf R}`, reached through `FormalSpectrum.sectionsLimitIso`, in a part of the
tree that imports neither this file nor its two-patch counterpart. Deleting is therefore the call
supported by measurement; keeping was the call supported by speculation.

## Main results

* `AlgebraicGeometry.ChartedSchemeDatum.range_specLRSGlueData_f`: off the diagonal the glue datum's
  overlap inclusion has the range of the affine chart `Spec ((C i)_{g i j}) ⟶ Spec (C i)`, the
  `CategoryTheory.GlueData.ofGlueData'` `eqToHom` being invisible to a range.
* `AlgebraicGeometry.ChartedSchemeDatum.preimage_range_specι`: **the equality**, off the general
  glue-datum statement.
* `AlgebraicGeometry.ChartedSchemeDatum.specLRSGlueData_t_comp_f`: off the diagonal the glue datum's
  transition-then-inclusion `t i j ≫ f j i` is `eqToHom` followed by `Spec (θ i j)` and the affine
  chart of `D (g j i)` — the same `eqToHom` that prefixes `f i j`, which is what lets the two cancel
  below.
* `AlgebraicGeometry.ChartedSchemeDatum.preimage_image_specι`: **the equality for the image of a
  subset**, off `AlgebraicGeometry.LocallyRingedSpace.GlueData.preimage_image_ι`. Taking
  `U = Set.univ` gives `preimage_range_specι` back, but the general form is what a statement about a
  *closed subset* of the `j`-th chart needs, and it is stated in the `PrimeSpectrum.comap` language
  its consumers speak.
* `AlgebraicGeometry.ChartedSchemeDatum.specι_base_notMem_range_specι` and
  `..._of_mem`: **the gluing is proper** — a point of the `i`-th chart outside `D (g i j)` maps
  outside the `j`-th chart, read off the equality. This is the arbitrary-index twin of
  `AlgebraicGeometry.specTwoPatchι₀_base_notMem_range_specTwoPatchι₁`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace ChartedSchemeDatum

variable (D : ChartedSchemeDatum.{u})

/-! ### The glue datum's overlap inclusion, off the diagonal -/

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- The glue datum is a `def`, so `D.specLRSGlueData.J` does not reduce to `D.J` at `instances`
-- transparency and the `dif_neg` below is otherwise rejected as ill-typed. Same requirement as
-- `specGD_f` in `FormalSchemes.ChartedSchemeDatumDesc`.
/-- **Off the diagonal the glue datum's overlap inclusion is the affine chart of the basic open.**
`CategoryTheory.GlueData.ofGlueData'` precedes it with an `eqToHom`, which is an isomorphism and so
invisible to a range (`AlgebraicGeometry.LocallyRingedSpace.range_eqToHom_comp_base`). -/
theorem range_specLRSGlueData_f (i j : D.J) (h : i ≠ j) :
    Set.range (D.specLRSGlueData.toGlueData.f i j).base =
      Set.range (specAwayMap (D.g i j)).base := by
  have hf : D.specLRSGlueData.toGlueData.f i j = eqToHom (dif_neg h) ≫ specAwayMap (D.g i j) :=
    dif_neg h
  rw [hf, LocallyRingedSpace.range_eqToHom_comp_base]
  rfl

/-! ### The charts meet exactly over the overlap -/

/-- **The `i`-th and `j`-th charts of the glued scheme meet exactly over `D (g i j)`.**

This is `AlgebraicGeometry.LocallyRingedSpace.GlueData.preimage_range_ι` — the general statement
for any glue datum, transported from `TopCat.GlueData.preimage_range` in
`FormalSchemes.GlueDataImageInter` — followed by `range_specLRSGlueData_f` and
`AlgebraicGeometry.range_specAwayMap` to name the overlap. Neither the glue *condition* nor the
containment `range_ι_inter_subset` is spent **here**: both halves are already inside the topological
statement, which is where the glue condition goes instead — Mathlib proves `preimage_range` from
`TopCat.GlueData.image_inter`, whose `⊇` half is
`CategoryTheory.GlueData.glue_condition_apply`. That is what makes this three lines rather than the
forty the two-patch model originally took; the content has moved, not vanished.

At two patches this is `AlgebraicGeometry.preimage_range_specTwoPatchι₁`
(`FormalSchemes.SpecTwoPatchNonAffine`), which is now the same three-line term at
`specTwoPatchLRSGlueData`. -/
theorem preimage_range_specι (i j : D.J) (h : i ≠ j) :
    ⇑(D.specι i).base ⁻¹' Set.range ⇑(D.specι j).base =
      (PrimeSpectrum.basicOpen (D.g i j) : Set (PrimeSpectrum (D.C i))) :=
  (D.specLRSGlueData.preimage_range_ι j i).trans
    ((D.range_specLRSGlueData_f i j h).trans (range_specAwayMap (D.g i j)))

/-! ### The image of a subset of one chart, seen in another -/

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- Same transparency requirement as `range_specLRSGlueData_f` above, and for the same reason: the
-- glue datum is a `def`, so `D.specLRSGlueData.J` does not reduce to `D.J` at `instances`
-- transparency and the two `dif_neg`s are otherwise rejected as ill-typed.
/-- **Off the diagonal the glue datum's transition-then-inclusion is `Spec (θ i j)` followed by the
affine chart of `D (g j i)`**, up to the `CategoryTheory.GlueData.ofGlueData'` `eqToHom`. The two
inner `eqToHom`s introduced by `ofGlueData'` — one at the end of `t i j`, one at the start of
`f j i` — are mutually inverse and cancel; what is left in front is exactly the `eqToHom` that also
prefixes `f i j`, which is what `preimage_image_specι` needs. -/
theorem specLRSGlueData_t_comp_f (i j : D.J) (h : i ≠ j) :
    D.specLRSGlueData.toGlueData.t i j ≫ D.specLRSGlueData.toGlueData.f j i =
      eqToHom (dif_neg h) ≫ (specGlueIso (D.g i j) (D.g j i) (D.θ i j h)).hom ≫
        specAwayMap (D.g j i) := by
  have ht : D.specLRSGlueData.toGlueData.t i j =
      eqToHom (dif_neg h) ≫ (specGlueIso (D.g i j) (D.g j i) (D.θ i j h)).hom ≫
        eqToHom (dif_neg (Ne.symm h)).symm := dif_neg h
  have hf : D.specLRSGlueData.toGlueData.f j i =
      eqToHom (dif_neg (Ne.symm h)) ≫ specAwayMap (D.g j i) := dif_neg (Ne.symm h)
  rw [ht, hf, Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **The part of the `i`-th chart that lands in a given subset `U` of the `j`-th chart.** It is the
image, under the affine chart of `D (g i j)`, of the part of the overlap that the `θ i j`-translate
carries into `U`.

This is `AlgebraicGeometry.LocallyRingedSpace.GlueData.preimage_image_ι`
(`FormalSchemes.GlueDataImageInter`), which is Mathlib's `TopCat.GlueData.preimage_image_eq_image`
transported across the carrier comparison, followed by the identification of this datum's `f` and
`t`. At `U = Set.univ` it is `preimage_range_specι`; the general form is what a statement about a
*closed subset* of the `j`-th chart needs, and `FormalSchemes.ChartedCompletionSupport` spends `hθ`
on exactly the middle preimage.

Unlike `preimage_range_specι`, this one cannot discard the `ofGlueData'` `eqToHom` with
`AlgebraicGeometry.LocallyRingedSpace.range_eqToHom_comp_base`: an isomorphism is invisible to a
range but not to the image of a named subset. The two occurrences cancel against each other instead,
which is what `specLRSGlueData_t_comp_f` and
`AlgebraicGeometry.LocallyRingedSpace.image_preimage_eqToHom_comp_base` are for. -/
theorem preimage_image_specι (i j : D.J) (h : i ≠ j) (U : Set (PrimeSpectrum (D.C j))) :
    ⇑(D.specι i).base ⁻¹' (⇑(D.specι j).base '' U) =
      PrimeSpectrum.comap (algebraMap (D.C i) (Localization.Away (D.g i j))) ''
        (PrimeSpectrum.comap (D.θ i j h).symm.toRingHom ⁻¹'
          (PrimeSpectrum.comap (algebraMap (D.C j) (Localization.Away (D.g j i))) ⁻¹' U)) := by
  have hf : D.specLRSGlueData.toGlueData.f i j =
      eqToHom (dif_neg h) ≫ specAwayMap (D.g i j) := dif_neg h
  refine (D.specLRSGlueData.preimage_image_ι j i U).trans ?_
  rw [D.specLRSGlueData_t_comp_f i j h, hf,
    LocallyRingedSpace.image_preimage_eqToHom_comp_base, LocallyRingedSpace.comp_base,
    TopCat.coe_comp, Set.preimage_comp]
  rfl

/-! ### The gluing is proper -/

/-- **A point of the `i`-th chart outside the overlap misses the `j`-th chart.** The arbitrary-index
form of `AlgebraicGeometry.specTwoPatchι₀_base_notMem_range_specTwoPatchι₁`, read off
`preimage_range_specι`. -/
theorem specι_base_notMem_range_specι (i j : D.J) (h : i ≠ j)
    (x : PrimeSpectrum (D.C i)) (hx : x ∉ Set.range (specAwayMap (D.g i j)).base) :
    (D.specι i).base x ∉ Set.range (D.specι j).base := fun hmem => by
  refine hx ?_
  rw [range_specAwayMap]
  exact (D.preimage_range_specι i j h).subset hmem

/-- **The gluing is proper, phrased ring-theoretically**: a prime of the `i`-th chart containing the
overlap element `g i j` maps outside the `j`-th chart. -/
theorem specι_base_notMem_range_specι_of_mem (i j : D.J) (h : i ≠ j)
    {x : PrimeSpectrum (D.C i)} (hx : D.g i j ∈ x.asIdeal) :
    (D.specι i).base x ∉ Set.range (D.specι j).base :=
  D.specι_base_notMem_range_specι i j h x (by
    rw [range_specAwayMap]
    exact fun hmem => (PrimeSpectrum.mem_basicOpen _ _).mp hmem hx)

end ChartedSchemeDatum

end AlgebraicGeometry

end
