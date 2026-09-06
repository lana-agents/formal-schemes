import FormalSchemes.AdicSectionsRestrictOpen
import FormalSchemes.SpfGammaBase

set_option linter.style.header false

/-!
# Germs read on a chart: the prime of the chart decides invertibility

`FormalSpectrum.isUnit_germ_top_iff` (`FormalSchemes.SpfGammaBase`) decides invertibility of the
germ of a **global section of a formal spectrum**: it is a unit at `x` exactly when the section's
class modulo the ideal of definition avoids the prime `x`. Every germ the Tate cluster asks about
is instead a germ on a formal scheme presented by charts, of a section over an open — and
`AlgebraicGeometry.FormalScheme.AffineChart.opensSectionsHom` reads such a section on a chart. The
two sides had no bridge: that reading is an equality of *sections*, and the criterion wants
*germs*.

This file is that bridge.

> `AlgebraicGeometry.LocallyRingedSpace.isUnit_germ_sectionsMapOfRangeSubset_iff`: for any morphism
> of locally ringed spaces `f : W ⟶ Y` whose range lies in `U`, a section over `U` has invertible
> germ at `f w` exactly when its restriction to `W` has invertible germ at `w`.

Both directions are the same fact about `AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap` — it
is a *local* homomorphism, so it both preserves and reflects units — and **no open immersion is
needed**:
the `↔` holds at an arbitrary morphism of locally ringed spaces. That is what makes the two
consequences below cheap.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.isUnit_germ_sectionsMapOfRangeSubset_iff`: **the bridge.**
* `AlgebraicGeometry.FormalScheme.AffineChart.isUnit_germ_iff`: at a chart of a formal scheme and a
  point of its range, the germ of a section over an open containing that range is a unit exactly
  when the class of its chart-reading modulo the chart's ideal of definition avoids the prime the
  point comes from. **The right-hand side mentions only the chart's ring, its ideal of definition
  and that prime** — no stalk, no germ and no colimit.
* `AlgebraicGeometry.FormalScheme.isUnit_germ_top_restrictOpen_iff`: the same for a *global* section
  of the open formal subscheme `X|_U`, which is the shape
  `AlgebraicGeometry.FormalScheme.restrictOpenTopSectionsHom` puts a section over `U` into.

## What is *not* proved here

**Nothing here says a chart exists.** All three statements take the chart as an argument. Producing
one at a given point is what `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` does, and
that is a `Classical.choice`; the criterion below is stated at a chart the caller already has, so a
caller with an explicitly constructed chart pays no `Classical.choice` for the *criterion* itself.

**Nothing here decides invertibility at any particular section.** The right-hand sides are
membership questions in a prime of the chart's ring modulo its ideal of definition, and no such
question is answered here.

**No comparison of two charts is made.** Two charts at the same point give two right-hand sides,
both correct; nothing below relates them, and nothing below says the preimage of the point under a
chart is unique.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.4, §10.4.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite

universe u

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- **Invertibility of a germ is unchanged by restricting along a morphism whose range lies in the
open.** For `f : W ⟶ Y` with `Set.range f.base ⊆ U` and a section `s` over `U`, the germ of
`AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset f U h s` at `w` is a unit exactly
when the germ of `s` at `f w` is.

Both directions come from `AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap`: it carries the one
germ to the other (`AlgebraicGeometry.LocallyRingedSpace.stalkMap_germ_apply`, once the transport
to `⊤` that `AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset` performs is absorbed
by `TopCat.Presheaf.germ_res`), and it is a local homomorphism, so `isUnit_map_iff` applies.
**`f` need not be an open immersion.** -/
theorem LocallyRingedSpace.isUnit_germ_sectionsMapOfRangeSubset_iff
    {W Y : LocallyRingedSpace.{u}} (f : W ⟶ Y) (U : Opens Y)
    (h : Set.range f.base ⊆ (U : Set Y)) (w : W) (s : Y.presheaf.obj (op U)) :
    IsUnit ((W.presheaf.germ ⊤ w trivial).hom
        ((LocallyRingedSpace.sectionsMapOfRangeSubset f U h).hom s)) ↔
      IsUnit ((Y.presheaf.germ U (f.base w) (h ⟨w, rfl⟩)).hom s) := by
  have hmem : f.base w ∈ U := h ⟨w, rfl⟩
  have key : ((W.presheaf.germ ⊤ w trivial).hom
      ((LocallyRingedSpace.sectionsMapOfRangeSubset f U h).hom s))
      = (f.stalkMap w).hom ((Y.presheaf.germ U (f.base w) hmem).hom s) := by
    rw [LocallyRingedSpace.stalkMap_germ_apply f U w hmem s,
      LocallyRingedSpace.sectionsMapOfRangeSubset]
    simp only [CommRingCat.comp_apply]
    rw [← CommRingCat.comp_apply]
    congr 1
    exact congrArg ConcreteCategory.hom (W.presheaf.germ_res
      (eqToHom (opens_map_obj_eq_top_of_range_subset f U h).symm) w trivial)
  rw [key]
  exact isUnit_map_iff (f.stalkMap w).hom _

namespace FormalScheme

set_option backward.isDefEq.respectTransparency false in
/-- **The chart decides the germ.** Let `c` be an affine chart of a formal scheme `X` whose range
lies in an open `U`, let `w` be a point of the chart's formal spectrum and let `z` be its image
`c.map.base w`. Then a section `s` over `U` has invertible germ at `z` exactly when the class
modulo the chart's ideal of definition of its chart-reading
`AlgebraicGeometry.FormalScheme.AffineChart.opensSectionsHom` avoids the prime `w`.

The image point is taken as an argument with `hz : c.map.base w = z` so that a caller holding a
point of `X` and a preimage of it under the chart can use the statement without rewriting under the
membership proof of the germ.

`AlgebraicGeometry.LocallyRingedSpace.isUnit_germ_sectionsMapOfRangeSubset_iff` moves the germ onto
the chart's formal spectrum, where it is a germ of a global section and
`FormalSpectrum.isUnit_germ_top_iff` applies; the chart-reading is that global section by the
definition of `AlgebraicGeometry.FormalScheme.AffineChart.opensSectionsHom`. -/
theorem AffineChart.isUnit_germ_iff {X : FormalScheme.{u}} {x : X} (c : AffineChart X x)
    (U : Opens X) (h : Set.range c.map.base ⊆ (U : Set X)) (w : FormalSpectrum c.I)
    {z : X} (hz : c.map.base w = z) (hzU : z ∈ U) (s : X.presheaf.obj (op U)) :
    IsUnit ((X.presheaf.germ U z hzU).hom s) ↔
      Ideal.Quotient.mk c.I (c.opensSectionsHom U h s) ∉ w.asIdeal := by
  subst hz
  rw [← LocallyRingedSpace.isUnit_germ_sectionsMapOfRangeSubset_iff c.map U h w s,
    ← isUnit_germ_top_iff c.I w (c.opensSectionsHom U h s)]
  congr! 2
  rw [AffineChart.opensSectionsHom]
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The same criterion for a global section of the open formal subscheme `X|_U`.** A section over
`U` becomes a global section of `X.restrictOpen hX U` through
`AlgebraicGeometry.FormalScheme.restrictOpenTopSectionsHom`, and its germ at a point `x` of that
subscheme is decided by any chart of `X` inside `U` through which `x` is visible.

The inclusion `AlgebraicGeometry.FormalScheme.restrictOpenι` is itself a morphism whose range lies
in `U`, so this is the bridge applied twice: once to strip the restriction, once at the chart. -/
theorem isUnit_germ_top_restrictOpen_iff {X : FormalScheme.{u}} (hX : X.LocallyFG) (U : Opens X)
    {y : X} (c : AffineChart X y) (h : Set.range c.map.base ⊆ (U : Set X))
    (x : X.restrictOpen hX U) (w : FormalSpectrum c.I)
    (hw : c.map.base w = (X.restrictOpenι hX U).base x) (t : X.presheaf.obj (op U)) :
    IsUnit (((X.restrictOpen hX U).presheaf.germ ⊤ x trivial).hom
        (X.restrictOpenTopSectionsHom hX U t)) ↔
      Ideal.Quotient.mk c.I (c.opensSectionsHom U h t) ∉ w.asIdeal := by
  rw [restrictOpenTopSectionsHom,
    LocallyRingedSpace.isUnit_germ_sectionsMapOfRangeSubset_iff (X.restrictOpenι hX U) U
      (range_restrictOpenι_subset X hX U) x t,
    AffineChart.isUnit_germ_iff c U h w hw]

end FormalScheme

end AlgebraicGeometry

end
