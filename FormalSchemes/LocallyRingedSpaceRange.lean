import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

set_option linter.style.header false

/-!
# Precomposing with an isomorphism does not change a range

Let `X, Y, Z` be locally ringed spaces. If `e : X ≅ Y` is an isomorphism and `h : Y ⟶ Z` any
morphism, then `e.hom ≫ h` and `h` have the same range on underlying spaces, because `e.hom`'s base
map is a homeomorphism and in particular surjective. This file records that fact and its `eqToHom`
specialisation, which is the form every `CategoryTheory.GlueData.ofGlueData'` goal presents.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.range_iso_hom_comp_base`
* `AlgebraicGeometry.LocallyRingedSpace.range_eqToHom_comp_base` — the `eqToHom` case, a one-line
  corollary through `CategoryTheory.eqToIso.hom`.

## Why this file exists, and why it is this low

Nothing below mentions a ring, an ideal, a spectrum or a formal scheme, and the statements are
wanted at three unrelated places in the tree: the Tate chain's glue datum
(`FormalSchemes.TateChainGlue`), the two-patch `Spec` glue datum
(`FormalSchemes.SpecTwoPatchNonAffine`) and the nested basic-open completion charts
(`FormalSchemes.CompletionNestedBasicOpen`). No module already in all three import closures is
about bare locally ringed spaces — the intersection is 26 modules and every one of them is an
adic-ring or formal-spectrum module — so the file sits directly on Mathlib, as
`FormalSchemes/PullbackRangeLRS.lean` and `FormalSchemes/LocallyRingedSpaceHomExt.lean` already do
for their own general facts.

Five modules import this one. Three of them — `TateChainGlue`, `SpecTwoPatchNonAffine`,
`CompletionNestedBasicOpen` — are the minimal antichain among the sixteen citing files *as the tree
stood before issue 1399*. The other two, `ChartedSchemeDatumDesc` and `CompletionTwoPatchDoubled`,
imported `SpecTwoPatchNonAffine` *only* for the copy that used to live there; they now import what
they actually use, which is exactly what removed their route to this module, so they take it
directly. Counting each file itself, their closures fall from 52 to **47** and from 48 to **39**:
six and ten modules drop out and this one is added back. `ChartedSchemeDatumChartOverlap`, which
does use a declaration of `SpecTwoPatchNonAffine` and had been reaching it through
`ChartedSchemeDatumDesc`, takes that import directly and goes 53 to 54 — the same +1, with nothing
to set against it.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **Precomposing with an isomorphism does not change the range.** The base map of `e.hom` is a
homeomorphism, hence surjective, so the range of `e.hom ≫ h` is the whole range of `h`.

Stated with uniform source/target objects so that the range decomposition avoids the
defeq-presentation mismatch between `FormalSpectrum.locallyRingedSpaceObj (…)` and
`(formalCompletion …).toLocallyRingedSpace`. -/
theorem range_iso_hom_comp_base {X Y Z : LocallyRingedSpace.{u}} (e : X ≅ Y) (h : Y ⟶ Z) :
    Set.range ⇑(e.hom ≫ h).base = Set.range ⇑h.base := by
  have hsurj : Function.Surjective ⇑e.hom.base := fun y =>
    ⟨e.inv.base y, LocallyRingedSpace.iso_inv_base_hom_base_apply e y⟩
  have hcomp : ⇑(e.hom ≫ h).base = ⇑h.base ∘ ⇑e.hom.base := by
    ext x
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply]
  rw [hcomp, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]

/-- **The `eqToHom` case.** Precomposing with the `eqToHom` of an equality of objects does not
change the range on underlying spaces. This is `range_iso_hom_comp_base` at `eqToIso pf`, and it is
the spelling that `CategoryTheory.GlueData.ofGlueData'` bookkeeping produces. -/
theorem range_eqToHom_comp_base {X Y Z : LocallyRingedSpace.{u}} (pf : X = Y) (h : Y ⟶ Z) :
    Set.range ⇑(eqToHom pf ≫ h).base = Set.range ⇑h.base := by
  rw [← eqToIso.hom pf]
  exact range_iso_hom_comp_base (eqToIso pf) h

end AlgebraicGeometry.LocallyRingedSpace
