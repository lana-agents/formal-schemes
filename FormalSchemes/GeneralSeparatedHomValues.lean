import FormalSchemes.AffineSeparatedScheme
import FormalSchemes.GeneralSeparatedHom
import FormalSchemes.ThreeChartCoverOpenSubscheme

set_option linter.style.header false

/-!
# The first inhabitants of `FormalScheme.IsSeparatedHom`

`FormalSchemes.GeneralSeparatedHom` defines separatedness of a morphism `g : X ⟶ Y` of formal
schemes at an arbitrary target and proves conservativity's easy direction. A definition that
elaborates is not a notion; this file supplies the values that make it one.

There are two, and **both are the base-affine value plus a transport**, which is what
`FormalScheme.isSeparatedHom_of_isSeparatedOverSpf` is for:

* `Spf A ⟶ Spf R`, from `spf_isSeparatedOverSpf` (`FormalSchemes.AffineSeparatedScheme`);
* `D(f₀) ∪ D(f₁) ∪ D(f₂) ⊆ Spf A`, over `Spf R`, from
  `ThreeChartCover.coverSubscheme_isSeparatedOverSpf`
  (`FormalSchemes.ThreeChartCoverOpenSubscheme`).

**Neither is evidence about a general target**, and the second is the interesting one only because
its *source* is a union of three basic opens rather than an affine formal scheme — the target is
`Spf R` in both cases. Two values at an arbitrary target are downstream of this file:
`FormalScheme.isSeparatedHom_id` (`FormalSchemes.GeneralSeparatedHomIdentity`), which is an
identity morphism, and `FormalScheme.isSeparatedHom_restrictOpenHom`
(`FormalSchemes.GeneralSeparatedHomRestrictOpen`), the inclusion of an open formal subscheme, which
is not one. See `FormalSchemes.GeneralSeparatedHom`'s "What is *not* proved here" for what the two
together leave open.

**A third value is one lemma away and the lemma is not on the tree.** The Tate curve formal model
has `tateCurveModel_isSeparatedOverSpf` (`FormalSchemes.TateSeparatedScheme`), but
`FormalScheme.IsSeparatedHom` cannot be *stated* about it without a `FormalScheme.LocallyFG`
witness for `tateCurveModel`, and the tree has none — `tateTwoPatch_locallyFG` is about a different
object. Supplying it is a row of its own, and it would pull the Tate cluster into this module's
import closure, which is why it is named here rather than taken.

## Why the values live here rather than in the modules that own the objects

`FormalSchemes.GeneralSeparatedScheme` records the rule that a value belongs in the module that owns
its object, and the three `FormalScheme.IsSeparatedOverSpf` values follow it. This file does not,
for a reason that is about imports rather than taste: `FormalScheme.IsSeparatedHom` is stated
through the restriction calculus of `FormalSchemes.OpenFormalSubscheme`, which
`FormalSchemes.AffineSeparatedScheme` does not import, so stating the first value in its owner would
add an import edge into the middle of the tree and rebuild everything downstream of it. Collecting
both values in one leaf module costs one module and moves nothing. If a third value arrives whose
owner already imports the restriction calculus, it belongs in that owner and not here.

## Main results

* `AlgebraicGeometry.spf_isSeparatedHom`: **the structural morphism `Spf A ⟶ Spf R` is
  separated.**
* `AlgebraicGeometry.ThreeChartCover.coverSubscheme_isSeparatedHom`: **the structural morphism
  `D(f₀) ∪ D(f₁) ∪ D(f₂) ⟶ Spf R` is separated**, with the source not affine.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A] [TopologicalSpace A]
variable [IsAdicRing (I.map (algebraMap R A))]

/-- **The structural morphism `Spf A ⟶ Spf R` is separated** (EGA I §10.15), as a morphism.

This is `spf_isSeparatedOverSpf` read through `FormalScheme.isSeparatedHom_of_isSeparatedOverSpf`,
so it is the affine-target value transported and nothing more: the cover of `Spf R` it produces is
the one-element cover at `⊤`. Its content is exactly that of the base-affine statement, and it is
here to show that `FormalScheme.IsSeparatedHom` is inhabited rather than to say anything new about
`Spf A`.

`Spf (I·A)` is `FormalScheme.LocallyFG` because `Ideal.FG` is carried onto `I·A` by
`Ideal.FG.map`. -/
theorem spf_isSeparatedHom :
    FormalScheme.IsSeparatedHom
      (FormalScheme.locallyFG_Spf (I := I.map (algebraMap R A)) (hI.map (algebraMap R A)))
      (FormalScheme.locallyFG_Spf hI)
      (FormalScheme.Hom.mk
        (locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map)) :=
  FormalScheme.isSeparatedHom_of_isSeparatedOverSpf hI _ _ (spf_isSeparatedOverSpf hI)

namespace ThreeChartCover

variable (I) (f : ULift.{u} (Fin 3) → A)

/-- **The structural morphism of `D(f₀) ∪ D(f₁) ∪ D(f₂) ⊆ Spf A` over `Spf R` is separated** (EGA I
§10.15), as a morphism, with no presentation in the statement.

Unlike `spf_isSeparatedHom` the source here is an open formal subscheme of `Spf A` cut out by a
union of three basic opens, so it is not affine in general —
`FormalSchemes.ThreeChartCoverOpenImmersion` is about the degenerate case where the three opens do
cover and it is affine after all. **The target is still `Spf R`**, so this is again
`FormalScheme.isSeparatedHom_of_isSeparatedOverSpf` applied to
`ThreeChartCover.coverSubscheme_isSeparatedOverSpf` and is not a statement about a general target.

The wrapper `ThreeChartCover.coverSubschemeStructHom` is `FormalScheme.Hom.mk
(coverSubschemeStructMap …)`, which is why the transported hypothesis is the one
`ThreeChartCover.coverSubscheme_isSeparatedOverSpf` states. -/
theorem coverSubscheme_isSeparatedHom (hI : I.FG) :
    FormalScheme.IsSeparatedHom (coverSubscheme_locallyFG I f hI) (FormalScheme.locallyFG_Spf hI)
      (coverSubschemeStructHom I f hI) :=
  FormalScheme.isSeparatedHom_of_isSeparatedOverSpf hI _ _
    (coverSubscheme_isSeparatedOverSpf I f hI)

end ThreeChartCover

end AlgebraicGeometry

end
