import FormalSchemes.ChartSpfHomIndep
import FormalSchemes.ChartSpfHomOverlap
import FormalSchemes.ThickeningColimitTarget

set_option linter.style.header false

/-!
# The chart morphism `Spf R{1/r} ⟶ X`, at a chart that need not be affine

`FormalSchemes/ThickeningChartSpfHom.lean` builds, from a compatible family
`f n : Spec (R ⧸ Iⁿ⁺¹) ⟶ X`, an open `U ⊆ X` **identified with `Spec B`**, and a basic open
`D(r) ⊆ |Spf R|` lying over `U`, a morphism `chartSpfHomAmbient : Spf R{1/r} ⟶ X`.
`ChartSpfHomIndep.lean` and `ChartSpfHomOverlap.lean` prove it independent of the affine chart and
compatible on overlaps.

Only **one** of the three files uses the affineness of `U`, and it uses it once: `chartSpfHom` is
`(thickeningRestrictionEquiv (awayCompletionIdeal I r) B).symm` of the restricted family. Every
other step — the assembly of the family, its compatibility, the elimination of `U` and `e` from
the restriction rule, the independence, the overlap agreement — mentions the affine ring only in
the *type* it happens to be stated at.

This file re-runs the three of them with `Spec B` replaced by an arbitrary
`Y : LocallyRingedSpace` satisfying `FormalSpectrum.IsThickeningColimitTarget`
(`FormalSchemes/ThickeningColimitTarget.lean`), which is the exact hypothesis that one step
needs. Since `Spf L` satisfies it for `L.FG`, the chart morphism now exists at a **formal-affine**
chart, which is issue 62m's step 3.

## The naming, and why nothing here is a duplicate

The declarations live in `FormalSpectrum.ColimitTarget` and reuse the names of their `Spec`-shaped
originals, because they are the same construction at a weaker hypothesis. They are not additional
copies of it:

* `ColimitTarget.chartFamily` and `ColimitTarget.chartFamily_step` **subsume** `chartFamily` and
  `chartFamily_step` — the proof of the latter never mentions `B`, and the proof here is that
  proof unchanged. The originals cannot be deleted from here, because
  `ThickeningChartSpfHom.lean` is five modules further up the import graph than
  `ThickeningColimitTarget.lean` can be placed; rehoming the whole chain is a separate row.
* `ColimitTarget.chartSpfHomAmbient_eq` proves that at `Y = Spec B` the morphism built here **is**
  `chartSpfHomAmbient`. So the two layers are one construction with two entry points, and that is
  checked rather than asserted.

## Main definitions

* `FormalSpectrum.ColimitTarget.chartFamily`, `…chartThickeningFamily`: the restricted family,
  landing in `Y`.
* `FormalSpectrum.ColimitTarget.chartSpfHom`, `…chartSpfHomAmbient`: the morphisms
  `Spf R{1/r} ⟶ Y` and `Spf R{1/r} ⟶ X`.

## Main results

* `FormalSpectrum.ColimitTarget.thickeningMap_comp_chartSpfHomAmbient`: the restriction rule, with
  `U`, `e` and `Y` all absent from the right-hand side — the form the gluing step consumes.
* `FormalSpectrum.ColimitTarget.chartSpfHomAmbient_congr`: independence of the chart, now also of
  the *kind* of chart: an affine one and a formal-affine one over the same `r` give the same
  morphism.
* `FormalSpectrum.ColimitTarget.chartSpfHomAmbient_overlap`: the overlap agreement.
* `FormalSpectrum.ColimitTarget.chartSpfHomAmbient_eq`: at an affine chart this is the landed
  `chartSpfHomAmbient`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FormalSpectrum.ColimitTarget

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : LocallyRingedSpace.{u}}

variable (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (U : Opens X.toTopCat) (r : R)
    (hr : basicOpen I r ≤ (Opens.map (commonBase I f)).obj U)
    (hI : I.FG) {Y : LocallyRingedSpace.{u}} (e : X.restrict U.isOpenEmbedding ≅ Y)

/-- **The level-`n` member of the family on the tower of `R{1/r}`**, landing in the chart `Y`.
Identical to `FormalSpectrum.chartFamily` except that the last map is an isomorphism onto an
arbitrary locally ringed space rather than onto a `Spec`. -/
def chartFamily (n : ℕ) :
    Spec.locallyRingedSpaceObj
        (CommRingCat.of (awayCompletion I r ⧸ (awayCompletionIdeal I r) ^ (n + 1))) ⟶ Y :=
  (chartIsoLRS I r hI n).inv ≫ chartInclusion I f hf U r hr n ≫ chartRestrict I f U n ≫ e.hom

omit [TopologicalSpace R] [IsAdicRing I] in
set_option linter.style.setOption false in
-- Mixes `Spec (CommRingCat.of _)` (from `chartStep`) with
-- `Spec.locallyRingedSpaceObj (CommRingCat.of _)` (from `stepChartRestrict`). The two are `rfl`
-- but not at `instances` transparency; the same accommodation `ThickeningChartSpfHom.lean` makes.
set_option backward.isDefEq.respectTransparency false in
/-- **The restricted family is compatible.** This is `FormalSpectrum.chartFamily_step`'s proof
unchanged — it never mentions the affine ring, which is the observation this whole file rests
on. -/
theorem chartFamily_step (n : ℕ) :
    Spec.locallyRingedSpaceMap (stepRingHom (awayCompletionIdeal I r) n) ≫
        chartFamily I f hf U r hr hI e (n + 1) =
      chartFamily I f hf U r hr hI e n := by
  have hstep : Spec.locallyRingedSpaceMap (stepRingHom (awayCompletionIdeal I r) n) =
      (chartIsoLRS I r hI n).inv ≫ Scheme.forgetToLocallyRingedSpace.map (chartStep I r n) ≫
        (chartIsoLRS I r hI (n + 1)).hom := by
    rw [chartStepLRS_comp_chartIsoLRS, Iso.inv_hom_id_assoc]
  rw [chartFamily, chartFamily, hstep]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [chartStepLRS_comp_chartInclusion_assoc,
    ← Category.assoc (stepChartRestrict I f hf U n), stepChartRestrict_comp_chartRestrict]

section Assemble

variable [IsAdicRing (awayCompletionIdeal I r)]

/-- The family of `chartFamily`, packaged as a `ThickeningFamilyLRS` for the adic ring `R{1/r}`.
Note the type: `ThickeningFamily` is only available at an affine target. -/
def chartThickeningFamily : ThickeningFamilyLRS (awayCompletionIdeal I r) Y :=
  ⟨chartFamily I f hf U r hr hI e, chartFamily_step I f hf U r hr hI e⟩

variable (hY : IsThickeningColimitTarget Y)

omit [TopologicalSpace R] [IsAdicRing I] [IsAdicRing (awayCompletionIdeal I r)] in
include hI in
/-- **The ideal of definition of `R{1/r}` is finitely generated** when `I` is, which is the side
condition `IsThickeningColimitTarget` carries. It is `FormalSpectrum.awayCompletionIdeal_fg`, which
this file cannot cite: that lemma sits in `FormalSchemes/TateInvNodeChartComplete.lean`, far to the
right of this module in the import graph. Rehoming it — it has ten hand-rolled copies elsewhere on
the tree — is its own row. -/
theorem awayCompletionIdeal_fg : (awayCompletionIdeal I r).FG :=
  map_awayCompletionHom I r ▸ hI.map (awayCompletionHom I r)

/-- **The morphism `Spf R{1/r} ⟶ Y`.** Where `FormalSpectrum.chartSpfHom` inverts the affine-target
bijection, this takes the preimage supplied by `hY`; `injective_restrictToThickeningsLRS` makes the
choice immaterial, and `chartSpfHom_uniq` records that. -/
def chartSpfHom : locallyRingedSpaceObj (awayCompletionIdeal I r) ⟶ Y :=
  (hY (awayCompletionIdeal I r) (awayCompletionIdeal_fg I r hI)
    (chartThickeningFamily I f hf U r hr hI e)).choose

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Computation rule.** Cite this rather than unfolding `chartSpfHom`. -/
@[reassoc]
theorem thickeningMap_comp_chartSpfHom (n : ℕ) :
    thickeningMap (awayCompletionIdeal I r) n ≫ chartSpfHom I f hf U r hr hI e hY =
      chartFamily I f hf U r hr hI e n :=
  congrFun (congrArg Subtype.val
    (hY (awayCompletionIdeal I r) (awayCompletionIdeal_fg I r hI)
      (chartThickeningFamily I f hf U r hr hI e)).choose_spec) n

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **…and it is the only morphism with that restriction**, since restriction to the thickenings
is injective at every target (`injective_restrictToThickeningsLRS`). -/
theorem chartSpfHom_uniq (g : locallyRingedSpaceObj (awayCompletionIdeal I r) ⟶ Y)
    (hg : ∀ n : ℕ, thickeningMap (awayCompletionIdeal I r) n ≫ g =
      chartFamily I f hf U r hr hI e n) :
    g = chartSpfHom I f hf U r hr hI e hY :=
  hom_ext_thickeningMap_lrs _ _ fun n =>
    (hg n).trans (thickeningMap_comp_chartSpfHom I f hf U r hr hI e hY n).symm

/-- **The morphism into the ambient space**, `Spf R{1/r} ⟶ X`. -/
def chartSpfHomAmbient : locallyRingedSpaceObj (awayCompletionIdeal I r) ⟶ X :=
  chartSpfHom I f hf U r hr hI e hY ≫ e.inv ≫ X.ofRestrict U.isOpenEmbedding

omit [TopologicalSpace R] [IsAdicRing I] in
set_option linter.style.setOption false in
-- Same mixture of the two spellings of `Spec`; see `chartFamily_step`.
set_option backward.isDefEq.respectTransparency false in
/-- **The restriction rule, with the chart eliminated.** Neither `U`, nor `e`, nor `Y` appears on
the right-hand side: it is a statement about the input family alone. That is what makes the
morphisms attached to two different charts — of two different *kinds* of chart — comparable. -/
theorem thickeningMap_comp_chartSpfHomAmbient (n : ℕ) :
    thickeningMap (awayCompletionIdeal I r) n ≫ chartSpfHomAmbient I f hf U r hr hI e hY =
      (chartIsoLRS I r hI n).inv ≫
        (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
          (chartOpen I r n).isOpenEmbedding ≫ f n := by
  rw [chartSpfHomAmbient, ← Category.assoc, thickeningMap_comp_chartSpfHom, chartFamily]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [chartRestrict_comp_ofRestrict, chartInclusion_comp_ofRestrict_assoc]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The restriction rule characterises the morphism.** Cite this to recognise a morphism built by
hand — in particular, `ColimitTarget.chartSpfHomAmbient_eq` uses it to identify this construction
with the landed affine-chart one. -/
theorem chartSpfHomAmbient_uniq (g : locallyRingedSpaceObj (awayCompletionIdeal I r) ⟶ X)
    (hg : ∀ n : ℕ, thickeningMap (awayCompletionIdeal I r) n ≫ g =
      (chartIsoLRS I r hI n).inv ≫
        (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
          (chartOpen I r n).isOpenEmbedding ≫ f n) :
    g = chartSpfHomAmbient I f hf U r hr hI e hY :=
  hom_ext_thickeningMap_lrs _ _ fun n =>
    (hg n).trans (thickeningMap_comp_chartSpfHomAmbient I f hf U r hr hI e hY n).symm

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **At an affine chart this is the landed construction.** The two are built through different
bijections — `thickeningRestrictionEquiv` there, an arbitrary preimage here — so this is a theorem
and not `rfl`; it is what makes this file a generalisation of `ThickeningChartSpfHom.lean` rather
than a second copy of it. -/
theorem chartSpfHomAmbient_eq (B : Type u) [CommRing B]
    (e : X.restrict U.isOpenEmbedding ≅ Spec.locallyRingedSpaceObj (CommRingCat.of B)) :
    chartSpfHomAmbient I f hf U r hr hI e (isThickeningColimitTarget_spec B) =
      FormalSpectrum.chartSpfHomAmbient I f hf U r hr hI B e :=
  FormalSpectrum.chartSpfHomAmbient_uniq I f hf r hI U hr B e _
    (thickeningMap_comp_chartSpfHomAmbient I f hf U r hr hI e _)

end Assemble

/-!
### Independence of the chart

`ChartSpfHomIndep.lean` proves the affine chart cannot be observed. The same proof shows more here:
the *kind* of chart cannot be observed either, so a `Spec`-shaped chart and a `Spf`-shaped chart
over the same `r` produce the same morphism `Spf R{1/r} ⟶ X`.
-/

section Indep

variable [IsAdicRing (awayCompletionIdeal I r)]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The morphism does not depend on the chart it was built from**, and the two charts are allowed
to be of different kinds: `Y` and `Y'` are unrelated locally ringed spaces. Both sides restrict on
the `n`-th thickening to `f n` read along `D(r)`, a statement in which no chart appears. -/
theorem chartSpfHomAmbient_congr (hY : IsThickeningColimitTarget Y)
    (U' : Opens X.toTopCat) (hr' : basicOpen I r ≤ (Opens.map (commonBase I f)).obj U')
    {Y' : LocallyRingedSpace.{u}} (e' : X.restrict U'.isOpenEmbedding ≅ Y')
    (hY' : IsThickeningColimitTarget Y') :
    chartSpfHomAmbient I f hf U r hr hI e hY = chartSpfHomAmbient I f hf U' r hr' hI e' hY' :=
  hom_ext_thickeningMap_lrs _ _ fun n => by
    rw [thickeningMap_comp_chartSpfHomAmbient, thickeningMap_comp_chartSpfHomAmbient]

end Indep

/-!
### The overlap agreement

`ChartSpfHomOverlap.lean`'s proof, unchanged: the charts are eliminated by
`thickeningMap_comp_chartSpfHomAmbient` before the comparison begins, so nothing in it was ever
about the affine ring.
-/

section Overlap

variable (s : R) [IsAdicRing (awayCompletionIdeal I r)] [IsAdicRing (awayCompletionIdeal I s)]
    (hY : IsThickeningColimitTarget Y)
    (U' : Opens X.toTopCat) (hr' : basicOpen I s ≤ (Opens.map (commonBase I f)).obj U')
    {Y' : LocallyRingedSpace.{u}} (e' : X.restrict U'.isOpenEmbedding ≅ Y')
    (hY' : IsThickeningColimitTarget Y')

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The chart morphisms agree on the overlap** (EGA I, 10.6.10). The two charts `(U, Y, e)` and
`(U', Y', e')` are unrelated and may be of different kinds; what is compared is the input family
read along `D(r)` and along `D(s)`, and both readings restrict to the chart of `D(r·s)`. -/
theorem chartSpfHomAmbient_overlap :
    basicOpenChartFurtherLeft I r s hI ≫ chartSpfHomAmbient I f hf U r hr hI e hY =
      basicOpenChartFurtherRight I r s hI ≫ chartSpfHomAmbient I f hf U' s hr' hI e' hY' := by
  refine hom_ext_thickeningMap_lrs _ _ fun n => ?_
  rw [basicOpenChartFurtherLeft, basicOpenChartFurtherRight,
    thickeningMap_comp_locallyRingedSpaceMap_assoc,
    thickeningMap_comp_locallyRingedSpaceMap_assoc,
    thickeningMap_comp_chartSpfHomAmbient, thickeningMap_comp_chartSpfHomAmbient,
    chartIsoLRS_inv_comp_ofRestrict_further_left_assoc,
    chartIsoLRS_inv_comp_ofRestrict_further_right_assoc]

end Overlap

end FormalSpectrum.ColimitTarget

end
