import FormalSchemes.OpenCoverHomExt
import FormalSchemes.ThreeChartCoverToBase

set_option linter.style.header false

/-!
# The three-chart cover maps to `Spf A` *over* `Spf R` (EGA I §10.13, §10.15)

`FormalSchemes.ThreeChartCoverToBase` supplies the morphism
`ThreeChartCover.gluedXToBase : gluedX ⟶ Spf A` from the glued three-chart cover down to its
ambient affine, together with the fact that each chart maps by an open immersion onto `D(f_i)`.
That morphism is not yet related to anything: `gluedX` also carries the datum's structural morphism
`(datumX I f B hI).xStructMap : gluedX ⟶ Spf R`, and nothing so far says the two are compatible.

This file says they are:

```
gluedXToBase ≫ ambientStructMap  =  xStructMap
```

so that `gluedX` is an object **over `Spf A`, over `Spf R`** rather than an object carrying two
unrelated morphisms. That is the frame in which "`gluedX` is an open formal subscheme of `Spf A`"
has to be stated — an open immersion `gluedX ⟶ Spf A` is only the right statement if it is a
morphism over the base — so this is the last piece of scaffolding before the immersion itself.

## What is here and what is not

`gluedXToBase` is still **not** shown to be an open immersion, and its range is still **not**
identified with `D(f₀) ∪ D(f₁) ∪ D(f₂)`. Those carry the geometry and are untouched here; what is
proved below is a compatibility, and no amount of it adds up to the immersion. In particular
nothing here makes the separatedness (`FormalSchemes.ThreeChartCoverSeparatedScheme`) or
topological-finite-type (`FormalSchemes.ThreeChartCoverTopFiniteType`) results chart-free — both
still speak of a presentation's glued object, and will until the immersion lands.

## Where the proofs came from

The mathematical content of this file was measured and written for PR #309 (issue 862), which
built its own copy of the cover map before PR #308 (issue 860) landed. Review established that the
two copies were the *same definition* — `ThreeChartCover.chartToBase` and #309's `chartInclusion`
are equal by `rfl`, since `awayCompletionHom (I·A) (f i)` and `algebraMap A (A{1/f_i})` are the
same map and the two `le_comap` witnesses are proof-irrelevant — so this file keeps only #309's
non-duplicated half, restated over the merged `gluedXToBase`. The proofs transferred verbatim.

The one simplification the merge bought: at #308's spelling, the chart-level compatibility is the
scalar tower `R → A → A{1/f_i}` and closes with `IsScalarTower.algebraMap_eq` alone. #309 needed
`awayCompletionHom_comp_algebraMap_base` and a private `le_comap_comp` helper — which would have
been a *sixth* copy of that two-line lemma. Neither is needed now, and no new private helper is
introduced.

## The transparency wall in `gluedXToBase_comp_ambientStructMap`

Reducing along `FormalScheme.OpenCover.hom_ext`, the final rewrite must be term-mode
`(cancel_epi _).mpr` rather than `rw`. `rw` fails there with *"Did not find an occurrence of the
pattern"* and a `Full error:` tail reporting the target is not type-correct at `instances`
transparency, because the open cover indexes by `xFormalGlueData.openCover.J` while `ι` indexes by
`xFormalGlueData.toLocallyRingedSpaceGlueData.J` — the same type only after unfolding. The
cancelled morphism is `⋯.some.hom`, an isomorphism and hence an epi, so this loses nothing. This is
the third recorded instance of the wall in this tree (issues 858 and 862 hit it with
`Category.id_comp`); when a glue-data index type is involved, go term-mode first.

## `A` is not assumed adic, except where it must be

`FormalSpectrum.locallyRingedSpaceObj` needs only a `CommRing` and an ideal, so everything outside
the final section carries **no hypothesis on `A`** — matching `FormalSchemes.ThreeChartCoverCharts`,
which deliberately does not require `A` to be adic, and `xStructMap`, which is a morphism of locally
ringed spaces for the same reason.

`A` adic for `I·A` is needed only for `Spf A` to be a *formal scheme*, hence only to repackage the
above in `FormalScheme`. That is the extra hypothesis on the `Adic` section, and it is not
restrictive where it matters: over a Noetherian base it is automatic for a topologically finite
type `A` (`IsTopologicallyFiniteType.isAdicRing_of_noetherian`), which is precisely the setting
`FormalSchemes.ThreeChartCoverTopFiniteType` works in.

## Nothing here is specific to three charts

`ULift (Fin 3)` is never case-split on and its cardinality is never used. The results lift verbatim
to any `AffineChartedFibreDatumX` whose chart algebras are completed localizations of a single
ambient `A`, with the chart maps to `Spf A` supplied. They are *not* lifted: the three-chart cover
is the only such datum on the board, and this tree has repeatedly paid for generic layers with no
second consumer. If a second one appears, the lift needs only `chartToBase` and its naturality as
hypotheses.

## Main definitions and results

* `AlgebraicGeometry.ThreeChartCover.ambientStructMap`: the ambient affine's structural morphism
  `Spf A ⟶ Spf R`.
* `AlgebraicGeometry.ThreeChartCover.chartToBase_comp_ambientStructMap`: each chart maps to
  `Spf A` over `Spf R`.
* `AlgebraicGeometry.ThreeChartCover.gluedXToBase_comp_ambientStructMap`: **the cover map is a
  morphism over `Spf R`.**
* `AlgebraicGeometry.ThreeChartCover.ambientStructHom`,
  `AlgebraicGeometry.ThreeChartCover.gluedXToBaseHom`,
  `AlgebraicGeometry.ThreeChartCover.gluedXToBaseHom_comp_ambientStructHom`: the same two facts in
  the category of formal schemes, for adic `A`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.13, §10.15.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

namespace ThreeChartCover

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A]
variable (f : ULift.{u} (Fin 3) → A)

/-! ### The ambient affine over the base -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The ambient affine's structural morphism** `Spf A ⟶ Spf R`, the map of formal spectra induced
by `algebraMap R A`. It is named because both results below mention it, and it is the same shape as
`AffineChartedFibreDatumX.xStructMapChart` one level up: a chart's structural morphism, for the
one-chart cover of `Spf A` by itself. -/
def ambientStructMap :
    locallyRingedSpaceObj (I.map (algebraMap R A)) ⟶ locallyRingedSpaceObj I :=
  locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Each chart maps to `Spf A` over `Spf R`**: including the `i`-th chart into `Spf A` and then
mapping down to `Spf R` is the chart's own structural morphism, i.e.
`(datumX I f B hI).xStructMapChart i` after the datum's chart algebras are unfolded.

The whole content is the scalar tower `R → A → A{1/f_i}`: both sides collapse to a single
`locallyRingedSpaceMap`, and the two underlying ring homs agree by `IsScalarTower.algebraMap_eq`.
Unlike the double-overlap square of `chartToBase_naturality`, which genuinely needs the transition
to fix the image of `A`, there is nothing to prove here beyond the tower. -/
theorem chartToBase_comp_ambientStructMap (i : ULift.{u} (Fin 3)) :
    chartToBase I f i ≫ ambientStructMap I =
      locallyRingedSpaceMap I (I.map (algebraMap R (chartAlgebra I f i)))
        (algebraMap R (chartAlgebra I f i)) Ideal.le_comap_map := by
  rw [chartToBase, ambientStructMap, ← FormalSpectrum.locallyRingedSpaceMap_comp
    (hIK := by
      rw [← IsScalarTower.algebraMap_eq R A (chartAlgebra I f i)]; exact Ideal.le_comap_map)]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  exact (IsScalarTower.algebraMap_eq R A (chartAlgebra I f i)).symm

/-! ### The cover map is a morphism over the base -/

variable (B : Type u) [CommRing B] [Algebra R B]

/-- **The cover map `gluedX ⟶ Spf A` is a morphism over `Spf R`**: composing it with
`Spf A ⟶ Spf R` recovers the datum's own structural morphism.

Together with `ι_gluedXToBase` this makes the three-chart cover an object *over `Spf A`* over
`Spf R`. That is the frame in which "`gluedX` is an open formal subscheme of `Spf A`" is to be
stated — an open immersion into `Spf A` is the right statement only if it is a morphism over the
base — and it is the last piece of scaffolding before that claim; it is not the claim, and it does
not make the cover's separatedness or finite-type statements chart-free.

Proved by uniqueness of morphisms out of the canonical open cover of the glued object
(`FormalScheme.OpenCover.hom_ext`), reduced chartwise to `chartToBase_comp_ambientStructMap`. The
last step must be term-mode `(cancel_epi _).mpr`; see the module docstring for why `rw` fails
there. -/
theorem gluedXToBase_comp_ambientStructMap (hI : I.FG) :
    gluedXToBase I f B hI ≫ ambientStructMap I = (datumX I f B hI).xStructMap := by
  refine ((datumX I f B hI).xFormalGlueData.openCover).hom_ext _ _ fun i => ?_
  have key : (datumX I f B hI).xFormalGlueData.ι i ≫ gluedXToBase I f B hI ≫ ambientStructMap I =
      (datumX I f B hI).xFormalGlueData.ι i ≫ (datumX I f B hI).xStructMap := by
    rw [ι_gluedXToBase_assoc, (datumX I f B hI).ι_xStructMap i]
    exact chartToBase_comp_ambientStructMap I f i
  simp only [FormalScheme.GlueData.openCover, FormalScheme.Hom.toLRSHom, Category.assoc]
  exact (cancel_epi _).mpr key

/-! ### In the category of formal schemes, for adic `A` -/

section Adic

variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]

/-- **The ambient affine's structural morphism as a morphism of formal schemes** `Spf A ⟶ Spf R`,
available once `A` is a complete adic ring for `I·A` — the hypothesis under which `Spf A` is a
formal scheme at all. -/
def ambientStructHom : FormalScheme.Spf (I.map (algebraMap R A)) ⟶ FormalScheme.Spf I :=
  FormalScheme.Hom.mk (ambientStructMap I)

/-- **The cover map as a morphism of formal schemes** `gluedX ⟶ Spf A`. -/
def gluedXToBaseHom (hI : I.FG) :
    gluedX I f B hI ⟶ FormalScheme.Spf (I.map (algebraMap R A)) :=
  FormalScheme.Hom.mk (gluedXToBase I f B hI)

/-- **`gluedXToBaseHom` is a morphism over `Spf R`**, the formal-scheme form of
`gluedXToBase_comp_ambientStructMap`. Composition in `FormalScheme` is `Hom.mk` of the composition
of the underlying morphisms of locally ringed spaces, so this is that identity under
`FormalScheme.Hom.ext'`. -/
theorem gluedXToBaseHom_comp_ambientStructHom (hI : I.FG) :
    gluedXToBaseHom I f B hI ≫ ambientStructHom I =
      FormalScheme.Hom.mk (datumX I f B hI).xStructMap :=
  FormalScheme.Hom.ext' (gluedXToBase_comp_ambientStructMap I f B hI)

end Adic

end ThreeChartCover

end AlgebraicGeometry

end
