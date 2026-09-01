import FormalSchemes.ChartedDatumGlueMorphisms
import FormalSchemes.GeneralFibreProductBothOverlapRange
import FormalSchemes.ThreeChartCoverDatum
import FormalSchemes.ThreeChartCoverSeparated

set_option linter.style.header false

/-!
# The three-chart open cover maps down to `Spf A` (EGA I §10.15)

`AlgebraicGeometry.ThreeChartCover.gluedX` (`FormalSchemes.ThreeChartCoverDatum`) is the formal
scheme glued from the three basic-open charts `A{1/f_0}`, `A{1/f_1}`, `A{1/f_2}` of `Spf A`. Two
EGA properties of it are on master — separatedness over `Spf R`
(`FormalSchemes.ThreeChartCoverSeparatedScheme`) and, over it, topological finite type — and both
are, deliberately and by their own docstrings, statements about *a presentation's glued object*
rather than about a named formal scheme. The structural morphism can only be spelled
`(datumX I f B hI).xStructMap`, because the tree has never related `gluedX` to `Spf A` at all.

This file supplies that relation: the morphism `gluedXToBase : gluedX ⟶ Spf A` restricting on each
chart to the basic-open chart `Spf A{1/f_i} ⟶ Spf A`. It is the first step of the identification
of `gluedX` with the open formal subscheme `D(f₀) ∪ D(f₁) ∪ D(f₂) ⊆ Spf A`, which
`FormalSchemes.ThreeChartCoverSeparated`'s module docstring records as deliberately avoided.

## What is here and what is not

Delivered: the morphism, its restriction law, and the fact that each chart maps by an **open
immersion** — `chartToBase i` is `basicOpenChart (I·A) (f i)` up to the ideal-of-definition
transport of `map_algebraMap_awayCompletion_eq`, so its range is the basic open `D(f_i)`.

**Not** delivered here, and not attempted here: that `gluedXToBase` is itself an open immersion,
that its range is `D(f₀) ∪ D(f₁) ∪ D(f₂)`, and the resulting chart-free restatements of the two EGA
properties. Those need the range of a glued morphism, which is genuine geometric content, and they
were carved as their own issues and delivered downstream — `range_gluedXToBase_base` and
`isOpenImmersion_gluedXToBase` in `FormalSchemes.ThreeChartCoverOpenImmersion`, and the open formal
subscheme `coverSubscheme` with the chart-free restatements in
`FormalSchemes.ThreeChartCoverOpenSubscheme`. Nothing *here* should be read as having established
them.

## Why the transition fixes `A`, and why that is the whole content

The overlap obligation is that the two chart-local presentations of `D(f_i) ∩ D(f_j)` map to the
same points of `Spf A`. Unlike the structural morphism to `Spf R` — where both sides collapse
because `τ i j` is an `R`-algebra isomorphism and `AlgEquiv.commutes` finishes it — `tau` is
**not** an `A`-algebra isomorphism by construction, so nothing formal discharges this.

It is nevertheless true, and `FormalSchemes.ThreeChartCoverSeparated` (issue 779) already proved
exactly the needed fact for its own purposes: `ThreeChartCover.tau_symm_algebraMap`, that the
transition fixes the image of `A`. `FormalSchemes.AwayCongrAlgebraMap`'s docstring calls such
transitions *inert*, and records that a datum whose transition is a genuine automorphism — like the
Tate model's — does **not** have the property. So the three-chart cover maps to `Spf A` for the
same structural reason that made it separable, and this construction does not transfer to the Tate
model. (What *is* claimed there is only the failure of inertness; whether `𝔈_q` admits some other
morphism to a `Spf` of its chart algebra is not addressed anywhere and is not claimed here.)

## Helpers: what was duplicated and what was not

Three small facts are needed that already exist somewhere in the tree; the choice was measured in
each case rather than guessed.

* `LocallyRingedSpace.range_eqToHom_comp_base` is public in
  `FormalSchemes.LocallyRingedSpaceRange`, a Mathlib-only leaf that is in this file's import
  closure — reusing it adds nothing, so it is reused. **When this paragraph was written the
  measurement was against one copy of a statement the tree carried five times**, in five files
  under four names; the one it found happened to be in closure, and the sentence above read as
  evidence that the question had been settled. It had not been. Issue 1399 merged the five.
* The scalar-tower fact `A → A{1/f_i} → A{1/f_i}{1/g_ij}` is
  `FormalSpectrum.awayCompletionHom_comp_algebraMap`, and it is reused at no cost: it now lives in
  `FormalSchemes.BasicOpenChart`, beside `awayCompletionHom` itself, which was already in this
  file's closure. Until issue 881 it lived in `FormalSchemes.RelativeTopFiniteTypeBasis`, and
  importing it cost **5** modules — the whole topologically-finite-type sub-tower
  (`RelativeTopFiniteTypeBasis`, `RelativeTopFiniteType`, `GlobalTopFiniteType`,
  `AwayTopFiniteType`, `TopFiniteTypeBasis`) — dragged into a gluing file for one `IsScalarTower`
  rewrite. That import is gone and this file's closure is 5 modules smaller.
* The ideal-of-definition transport `FormalSpectrum.eqToHom_comp_locallyRingedSpaceMap` is reused.
  Until issue 876 it was not: it lived in `FormalSchemes.TateFibreProductHom`, above the Tate
  self-product tower, and importing it cost **15** modules — among them
  `TateSelfProductAdicOverBase`, `TateXGluedIso` and `TateOverlapChartIso`, the region issues 636
  and 737 document as the tree's memory hazard — so this file carried a private copy of it
  instead. 876 moved the lemma to `FormalSchemes.SpfFunctorial`, which was already in this file's
  closure, so it now costs nothing and the copy is gone. The call site takes it at `h.symm` and
  `.symm`s the result, which is the transport in the other orientation.

## Main definitions and results

* `AlgebraicGeometry.ThreeChartCover.chartToBase`: the `i`-th chart's morphism `Spf A{1/f_i} ⟶
  Spf A`, in the ideal spelling the datum's charts are built at.
* `AlgebraicGeometry.ThreeChartCover.chartToBase_eq`: it is `basicOpenChart (I·A) (f i)` composed
  with the ideal transport, hence an open immersion
  (`AlgebraicGeometry.ThreeChartCover.isOpenImmersion_chartToBase`) with range `D(f_i)`
  (`AlgebraicGeometry.ThreeChartCover.range_chartToBase_base`).
* `AlgebraicGeometry.ThreeChartCover.chartToBase_naturality`: the double-overlap square.
* `AlgebraicGeometry.ThreeChartCover.gluedXToBase`: **the glued morphism `gluedX ⟶ Spf A`**, and
  `AlgebraicGeometry.ThreeChartCover.ι_gluedXToBase`, its restriction law.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6, §10.15.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

namespace ThreeChartCover

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A]
variable (f : ULift.{u} (Fin 3) → A)

/-! ### The chart morphisms -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The structure map `A → A{1/f_i}` carries `I·A` into `I·A{1/f_i}`: it is
`awayCompletionHom (I·A) (f i)` (`IsScalarTower.algebraMap_eq`), whose continuity is
`le_comap_awayCompletionHom` once the target ideal is put in the `awayCompletionIdeal` convention
by `map_algebraMap_awayCompletion_eq`. -/
theorem le_comap_chartToBase (i : ULift.{u} (Fin 3)) :
    I.map (algebraMap R A) ≤
      (I.map (algebraMap R (chartAlgebra I f i))).comap (algebraMap A (chartAlgebra I f i)) := by
  rw [map_algebraMap_awayCompletion_eq,
    IsScalarTower.algebraMap_eq A (Localization.Away (f i)) (chartAlgebra I f i)]
  exact le_comap_awayCompletionHom _ _

/-- **The `i`-th chart's morphism down to `Spf A`**, `Spf A{1/f_i} ⟶ Spf A`. It is the basic-open
chart at `f i` (`chartToBase_eq`), written with its source's ideal of definition in the spelling
`I.map (algebraMap R (chartAlgebra I f i))` that the datum's charts carry, rather than the
`awayCompletionIdeal` spelling `basicOpenChart` produces. -/
def chartToBase (i : ULift.{u} (Fin 3)) :
    locallyRingedSpaceObj (I.map (algebraMap R (chartAlgebra I f i))) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R A)) :=
  locallyRingedSpaceMap (I.map (algebraMap R A)) (I.map (algebraMap R (chartAlgebra I f i)))
    (algebraMap A (chartAlgebra I f i)) (le_comap_chartToBase I f i)

/-! ### Identification with the basic-open chart -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The `i`-th chart, in the datum's ideal spelling, is the source of `basicOpenChart (I·A) (f i)`.
The two spellings of its ideal of definition are `map_algebraMap_awayCompletion_eq`. -/
theorem chartObj_eq (i : ULift.{u} (Fin 3)) :
    locallyRingedSpaceObj (I.map (algebraMap R (chartAlgebra I f i))) =
      locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R A)) (f i)) :=
  congrArg _ (map_algebraMap_awayCompletion_eq I (f i))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **`chartToBase i` is the basic-open chart at `f i`**, up to the transport of its source along
the two spellings of that source's ideal of definition. This is what makes the chart morphisms of
this file geometric rather than merely formal: everything known about `basicOpenChart` — that it is
an open immersion with range `D(f_i)` — transfers along an `eqToHom`. -/
theorem chartToBase_eq (i : ULift.{u} (Fin 3)) :
    chartToBase I f i =
      eqToHom (chartObj_eq I f i) ≫ basicOpenChart (I.map (algebraMap R A)) (f i) := by
  rw [chartToBase, basicOpenChart,
    (eqToHom_comp_locallyRingedSpaceMap (map_algebraMap_awayCompletion_eq I (f i)).symm
      (algebraMap A (chartAlgebra I f i))
      ((IsScalarTower.algebraMap_eq A (Localization.Away (f i)) (chartAlgebra I f i)) ▸
        le_comap_awayCompletionHom (I.map (algebraMap R A)) (f i))
      (le_comap_chartToBase I f i)).symm]
  refine congrArg _ (locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_)
  exact IsScalarTower.algebraMap_eq A (Localization.Away (f i)) (chartAlgebra I f i)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The chart morphism is an open immersion**: an `eqToHom` followed by `basicOpenChart`, which
is one by `isOpenImmersion_basicOpenChart` (issue 163). -/
theorem isOpenImmersion_chartToBase (hI : I.FG) (i : ULift.{u} (Fin 3)) :
    LocallyRingedSpace.IsOpenImmersion (chartToBase I f i) := by
  rw [chartToBase_eq]
  haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R A)) (f i) (hI.map _)
  haveI : IsIso (eqToHom (chartObj_eq I f i)) := inferInstance
  exact LocallyRingedSpace.IsOpenImmersion.comp _ _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The range of the `i`-th chart is the basic open `D(f_i)`** of `Spf A`. -/
theorem range_chartToBase_base (hI : I.FG) (i : ULift.{u} (Fin 3)) :
    Set.range (chartToBase I f i).base =
      (FormalSpectrum.basicOpen (I.map (algebraMap R A)) (f i) :
        Set (FormalSpectrum (I.map (algebraMap R A)))) := by
  rw [chartToBase_eq, LocallyRingedSpace.range_eqToHom_comp_base]
  exact range_basicOpenChart_base (I.map (algebraMap R A)) (f i) (hI.map _)

/-! ### The glued morphism -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The double-overlap compatibility square.** The `(i,j)`-overlap chart followed by the `i`-th
chart's map to `Spf A` equals the transition followed by the `(j,i)`-overlap chart and the `j`-th
chart's map — the datum `glueChartMorphisms` consumes.

Both sides collapse to a single `locallyRingedSpaceMap` out of `Spf A{1/f_i}{1/g_ij}`, and the
underlying ring maps agree because `(tau I f hI i j).symm` fixes the image of `A`
(`tau_symm_algebraMap`, issue 779). That is the one non-formal step: `tau` is an `R`-algebra
isomorphism by construction, not an `A`-algebra one, so this does not follow from
`AlgEquiv.commutes` the way the corresponding square for `xStructMap` does. -/
theorem chartToBase_naturality (hI : I.FG) (i j : ULift.{u} (Fin 3)) :
    basicOpenChart (I.map (algebraMap R (chartAlgebra I f i))) (overlapElt I f i j) ≫
        chartToBase I f i =
      awayCompletionTransition (overlapElt I f i j) (overlapElt I f j i) (tau I f hI i j) ≫
        basicOpenChart (I.map (algebraMap R (chartAlgebra I f j))) (overlapElt I f j i) ≫
          chartToBase I f j := by
  rw [chartToBase, chartToBase, basicOpenChart, basicOpenChart, awayCompletionTransition,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp (algebraMap A (chartAlgebra I f i))
        (awayCompletionHom (I.map (algebraMap R (chartAlgebra I f i))) (overlapElt I f i j))
        (le_comap_chartToBase I f i) (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp (algebraMap A (chartAlgebra I f j))
        (awayCompletionHom (I.map (algebraMap R (chartAlgebra I f j))) (overlapElt I f j i))
        (le_comap_chartToBase I f j) (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp
        ((awayCompletionHom (I.map (algebraMap R (chartAlgebra I f j))) (overlapElt I f j i)).comp
          (algebraMap A (chartAlgebra I f j)))
        (tau I f hI i j).symm.toRingHom
        (le_comap_comp (algebraMap A (chartAlgebra I f j))
          (awayCompletionHom (I.map (algebraMap R (chartAlgebra I f j))) (overlapElt I f j i))
          (le_comap_chartToBase I f j) (le_comap_awayCompletionHom _ _))
        (awayCompletionTransition_le_comap (overlapElt I f i j) (overlapElt I f j i)
          (tau I f hI i j)))]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  rw [FormalSpectrum.awayCompletionHom_comp_algebraMap (R := A),
    FormalSpectrum.awayCompletionHom_comp_algebraMap (R := A)]
  exact RingHom.ext fun a => (tau_symm_algebraMap I f hI i j a).symm

variable (B : Type u) [CommRing B] [Algebra R B]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The three-chart open cover maps to `Spf A`** — the morphism `gluedX ⟶ Spf A` gluing the
three basic-open charts, via `AffineChartedFibreDatumX.glueChartMorphisms`.

By `ι_gluedXToBase` and `range_chartToBase_base` its range *contains* each `D(f_i)`. That it is
exactly `D(f₀) ∪ D(f₁) ∪ D(f₂)`, and that the morphism is an isomorphism onto that open formal
subscheme — which is what would make the cover's separatedness and finite-type statements
chart-free — is **not** proved here and should not be assumed; see the module docstring. -/
def gluedXToBase (hI : I.FG) :
    (gluedX I f B hI).toLocallyRingedSpace ⟶ locallyRingedSpaceObj (I.map (algebraMap R A)) :=
  (datumX I f B hI).glueChartMorphisms (fun i => chartToBase I f i)
    (fun i j _ => chartToBase_naturality I f hI i j)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The glued morphism restricts to the `i`-th basic-open chart.** -/
@[reassoc (attr := simp)]
theorem ι_gluedXToBase (hI : I.FG) (i : ULift.{u} (Fin 3)) :
    (datumX I f B hI).xFormalGlueData.ι i ≫ gluedXToBase I f B hI = chartToBase I f i :=
  (datumX I f B hI).ι_glueChartMorphisms _ _ i

end ThreeChartCover

end AlgebraicGeometry

end
