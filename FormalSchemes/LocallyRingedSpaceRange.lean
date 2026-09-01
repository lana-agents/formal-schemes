import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

set_option linter.style.header false

/-!
# An `eqToHom` prefix is invisible to a locally ringed space morphism's base map

Let `X, Y, Z` be locally ringed spaces. If `e : X ≅ Y` is an isomorphism and `h : Y ⟶ Z` any
morphism, then `e.hom ≫ h` and `h` have the same range on underlying spaces, because `e.hom`'s base
map is a homeomorphism and in particular surjective. This file records that fact, its `eqToHom`
specialisation — the form every `CategoryTheory.GlueData.ofGlueData'` goal presents — and the
image/preimage statement that the same bookkeeping needs when the subset in play is a *named*
subset rather than a whole chart.

The two are not the same fact, and the difference is why both are here. A range is insensitive to
precomposition with any surjection, so the `eqToHom` can simply be discarded. The image of a named
subset is not, so there the `eqToHom` prefixing the two legs has to **cancel against itself**;
`image_preimage_eqToHom_comp_base` is that cancellation and it does not follow from the range
statement.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.range_iso_hom_comp_base`
* `AlgebraicGeometry.LocallyRingedSpace.range_eqToHom_comp_base` — the `eqToHom` case, a one-line
  corollary through `CategoryTheory.eqToIso.hom`.
* `AlgebraicGeometry.LocallyRingedSpace.image_preimage_eqToHom_comp_base` — the image/preimage
  form, for a named subset of the target.

## Why this file exists, and why it is this low

Nothing below mentions a ring, an ideal, a spectrum or a formal scheme, and the statements are
wanted at unrelated places in the tree: the range pair at the Tate chain's glue datum
(`FormalSchemes.TateChainGlue`), the two-patch `Spec` glue datum
(`FormalSchemes.SpecTwoPatchNonAffine`) and the nested basic-open completion charts
(`FormalSchemes.CompletionNestedBasicOpen`); the image/preimage lemma at the two-patch and the
arbitrary-index chart-overlap computations
(`FormalSchemes.SpecTwoPatchNonAffine`, `FormalSchemes.ChartedSchemeDatumChartOverlap`). No module
already in all of those import closures is about bare locally ringed spaces — the intersection is
26 modules and every one of them is an adic-ring or formal-spectrum module — so the file sits
directly on Mathlib, as `FormalSchemes/PullbackRangeLRS.lean` and
`FormalSchemes/LocallyRingedSpaceHomExt.lean` already do for their own general facts.

Six modules import this one, and each imports it because it uses a declaration of it; counts below
are self-inclusive over project modules. `TateChainGlue`, `SpecTwoPatchNonAffine` and
`CompletionNestedBasicOpen` were the minimal antichain among the sixteen files that cited the range
lemmas *as the tree stood before issue 1399*. `ChartedSchemeDatumDesc` and
`CompletionTwoPatchDoubled` had been importing `SpecTwoPatchNonAffine` *only* for the copy of the
range lemma that used to live there, and issue 1399 gave them this module instead: their closures
fell from 52 to **47** and from 48 to **39**. `ChartedSchemeDatumChartOverlap` is the sixth and
came here on issue 1425, for the opposite reason: its *only* code use of `SpecTwoPatchNonAffine` —
checked over all 27 of that file's declarations — was `image_preimage_eqToHom_comp_base`, so moving
that lemma here let it drop `SpecTwoPatchNonAffine`, `SpecTwoPatchScheme` and `TwoPatchWitness` and
gain nothing (this module was already in its closure through `ChartedSchemeDatumDesc`), taking it
from 54 to **51**. That gives back the +1 issue 1399 cost it, and two more.
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

/-- **The image/preimage form of the same fact.** Precomposing *both* legs with the same `eqToHom`
does not change the image of the preimage: `eqToHom e` is an isomorphism, so its base map is a
bijection and `φ '' (φ ⁻¹' S) = S`.

This is not a consequence of `range_eqToHom_comp_base` above: a range is insensitive to
precomposition with any surjection, but the image of a *named* subset is not, so the two `eqToHom`s
have to cancel against each other rather than be discarded one at a time. That is why the
image-shaped chart preimage `AlgebraicGeometry.ChartedSchemeDatum.preimage_image_specι` needs this
and the range-shaped `AlgebraicGeometry.ChartedSchemeDatum.preimage_range_specι` does not. -/
theorem image_preimage_eqToHom_comp_base {W X Y Z : LocallyRingedSpace.{u}}
    (e : W = X) (α : X ⟶ Y) (β : X ⟶ Z) (U : Set Z) :
    ⇑(eqToHom e ≫ α).base '' (⇑(eqToHom e ≫ β).base ⁻¹' U) = ⇑α.base '' (⇑β.base ⁻¹' U) := by
  subst e
  rw [eqToHom_refl, Category.id_comp, Category.id_comp]

end AlgebraicGeometry.LocallyRingedSpace
