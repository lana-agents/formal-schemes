import FormalSchemes.ChartedSchemeDatumDesc

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
(`FormalSchemes.CompletionTwoPatchSupport`), and — like it — the `⊆` half is the containment the
glue datum gives for free while the `⊇` half consumes the glue **condition**, in the form
`AlgebraicGeometry.ChartedSchemeDatum.specAwayMap_comp_specι`.

## Why this is the brick the support statement needs

`FormalSchemes.ChartedCompletionRange` computes the image of `X_{/Y} ⟶ X` at an arbitrary index as
`⋃ i, (specι i) '' V (K i)`, and stops: the chart preimage of that union needs to know that the
`j ≠ i` terms only ever reach the `i`-th chart inside `D (g i j)`, which is exactly the statement
above. That file records the absence of any range computation for `specι` as the reason it cannot
continue, and this file is the answer to it.

Nothing here uses the ideals `K i` or the compatibility `hθ`: this is a statement about the glued
**scheme**, not about any completion of it. `hθ` enters one file later, where the zero loci do.

## Main results

* `AlgebraicGeometry.ChartedSchemeDatum.range_specLRSGlueData_f`: off the diagonal the glue datum's
  overlap inclusion has the range of the affine chart `Spec ((C i)_{g i j}) ⟶ Spec (C i)`, the
  `CategoryTheory.GlueData.ofGlueData'` `eqToHom` being invisible to a range.
* `AlgebraicGeometry.ChartedSchemeDatum.specι_base_notMem_range_specι` and
  `..._of_mem`: **the gluing is proper** — a point of the `i`-th chart outside `D (g i j)` maps
  outside the `j`-th chart. This is the arbitrary-index twin of
  `AlgebraicGeometry.specTwoPatchι₀_base_notMem_range_specTwoPatchι₁`.
* `AlgebraicGeometry.ChartedSchemeDatum.specι_base_comap_algebraMap`: the glue condition at a
  point.
* `AlgebraicGeometry.ChartedSchemeDatum.preimage_range_specι`: **the equality**, the two halves
  above combined.

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

/-! ### The gluing is proper -/

/-- **A point of the `i`-th chart outside the overlap misses the `j`-th chart.** The arbitrary-index
form of `AlgebraicGeometry.specTwoPatchι₀_base_notMem_range_specTwoPatchι₁`: it is
`AlgebraicGeometry.LocallyRingedSpace.GlueData.range_ι_inter_subset` — *the charts meet at most
over the overlap* — together with `range_specLRSGlueData_f` to name the overlap. Only this
containment half is available from the glue datum alone; the converse is `preimage_range_specι`
below. -/
theorem specι_base_notMem_range_specι (i j : D.J) (h : i ≠ j)
    (x : PrimeSpectrum (D.C i)) (hx : x ∉ Set.range (specAwayMap (D.g i j)).base) :
    (D.specι i).base x ∉ Set.range (D.specι j).base := by
  rintro ⟨y, hy⟩
  obtain ⟨w, hw⟩ := D.specLRSGlueData.range_ι_inter_subset i j
    (⟨⟨x, rfl⟩, ⟨y, hy⟩⟩ :
      (D.specι i).base x ∈ Set.range (D.specι i).base ∩ Set.range (D.specι j).base)
  refine hx ?_
  rw [← D.range_specLRSGlueData_f i j h]
  exact ⟨w, (D.specι_isOpenImmersion i).base_open.injective hw⟩

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

/-! ### The equality -/

/-- **The `i`-th and `j`-th charts of the glued scheme meet exactly over `D (g i j)`.** The
containment `⊆` is `specι_base_notMem_range_specι`, which the glue datum gives for free; the
converse spends the glue **condition**, through `specι_base_comap_algebraMap`, and is the reason
this file exists.

At two patches this is `AlgebraicGeometry.preimage_range_specTwoPatchι₁`
(`FormalSchemes.CompletionTwoPatchSupport`), whose docstring records the same asymmetry. -/
theorem preimage_range_specι (i j : D.J) (h : i ≠ j) :
    ⇑(D.specι i).base ⁻¹' Set.range ⇑(D.specι j).base =
      (PrimeSpectrum.basicOpen (D.g i j) : Set (PrimeSpectrum (D.C i))) := by
  ext p
  constructor
  · intro hp
    by_contra hpg
    refine D.specι_base_notMem_range_specι i j h p ?_ hp
    rw [range_specAwayMap]
    exact hpg
  · intro hp
    obtain ⟨y, rfl⟩ : p ∈ Set.range (specAwayMap (D.g i j)).base := by
      rw [range_specAwayMap]
      exact hp
    exact ⟨_, (D.specι_base_comap_algebraMap i j h y).symm⟩

end ChartedSchemeDatum

end AlgebraicGeometry

end
