import FormalSchemes.ChartedSchemeDatumDesc
import FormalSchemes.GlueDataImageInter

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
**scheme**, not about any completion of it. `hθ` enters one file later, where the zero loci do —
and neither does the glue condition any longer, though `specι_base_comap_algebraMap` still lives
here because that later file consumes it.

## Main results

* `AlgebraicGeometry.ChartedSchemeDatum.range_specLRSGlueData_f`: off the diagonal the glue datum's
  overlap inclusion has the range of the affine chart `Spec ((C i)_{g i j}) ⟶ Spec (C i)`, the
  `CategoryTheory.GlueData.ofGlueData'` `eqToHom` being invisible to a range.
* `AlgebraicGeometry.ChartedSchemeDatum.preimage_range_specι`: **the equality**, off the general
  glue-datum statement.
* `AlgebraicGeometry.ChartedSchemeDatum.specι_base_notMem_range_specι` and
  `..._of_mem`: **the gluing is proper** — a point of the `i`-th chart outside `D (g i j)` maps
  outside the `j`-th chart, read off the equality. This is the arbitrary-index twin of
  `AlgebraicGeometry.specTwoPatchι₀_base_notMem_range_specTwoPatchι₁`.
* `AlgebraicGeometry.ChartedSchemeDatum.specι_base_comap_algebraMap`: the glue condition at a
  point. The equality above no longer needs it; `FormalSchemes.ChartedCompletionSupport` does, for
  the step where `hθ` is spent, and this is its home.

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

/-! ### The glue condition at a point -/

/-- **The glue condition at a point**: a prime of the overlap `(C i)_{g i j}`, pushed into the glued
scheme through the `i`-th chart, is the image through the `j`-th chart of its `θ i j`-translate.
This is `AlgebraicGeometry.ChartedSchemeDatum.specAwayMap_comp_specι` evaluated at a point, and it
is what supplies the converse containment below. -/
theorem specι_base_comap_algebraMap (i j : D.J) (h : i ≠ j)
    (y : PrimeSpectrum (Localization.Away (D.g i j))) :
    (D.specι i).base (PrimeSpectrum.comap (algebraMap (D.C i) (Localization.Away (D.g i j))) y) =
      (D.specι j).base (PrimeSpectrum.comap (algebraMap (D.C j) (Localization.Away (D.g j i)))
        (PrimeSpectrum.comap (D.θ i j h).symm.toRingHom y)) := by
  have hcomp := congrArg
    (fun m : Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away (D.g i j))) ⟶
      D.specGlued => m.base y) (D.specAwayMap_comp_specι i j h)
  simp only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
    Function.comp_apply] at hcomp
  exact hcomp

end ChartedSchemeDatum

end AlgebraicGeometry

end
