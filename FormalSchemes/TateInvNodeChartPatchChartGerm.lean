import FormalSchemes.ChartGermCriterion
import FormalSchemes.TateInvNodeChartBasicOpenPreimage
import FormalSchemes.TateInvNodeChartPatchChartAdic

set_option linter.style.header false

/-!
# The germ of `nodeChartPsi g` on the patch chart, computed

`FormalSchemes.TateInvNodeChartBasicOpenPreimage` named the preimage of `D(g)` along
`AlgebraicGeometry.nodeChartAdicHom` as the locus where the germ of
`AlgebraicGeometry.nodeChartPsi g` is invertible, and recorded that **no germ was computed**: the
three space-half clauses of hypothesis 4 of
`AlgebraicGeometry.exists_formalScheme_of_adicSections` are all statements about those loci, and
nothing on the tree evaluated one. This file evaluates them, on the patch-`i` basic-open chart.

> `AlgebraicGeometry.isUnit_germ_nodeChartPsi_iff`: at a point of the chain visible through the
> chart at a point `w` of `Spf A{1/(x + y − 1)}`, the germ of `AlgebraicGeometry.nodeChartPsi g` is
> a unit **iff** the class modulo `FormalSpectrum.awayCompletionIdeal` of the image of `g` in
> `A{1/(x + y − 1)}` avoids the prime `w`.

The right-hand side contains no quotient, no chart and no `Classical.choice`: the image of `g` is
`(AlgebraicGeometry.tateInvNodeChartAwaySubring …).subtype` of
`AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv … g`, i.e. `g` read as an element of the
annulus algebra, and `w` is a point of the affine formal spectrum the chart is modelled on. **The
index `i` does not enter the answer**, for the reason
`FormalSchemes.TateInvNodeChartPatchChartAdic` gives: every patch sees `π^* t` as the same section,
so `AlgebraicGeometry.theta_nodeChartPatchChart` holds at every `i` with the same right-hand side.

## The two halves of the route

* **The germ half is general and is in `FormalSchemes.ChartGermCriterion`.**
  `AlgebraicGeometry.FormalScheme.isUnit_germ_top_restrictOpen_iff` decides the germ at any chart of
  any formal scheme, because `AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap` is a local
  homomorphism and therefore both preserves and reflects units. That is the bridge between an
  equality of *sections* and a statement about *germs*, and it did not exist on the tree.
* **The arithmetic half was already landed.** `AlgebraicGeometry.theta_nodeChartPatchChart` says the
  chart-reading of `π^* g` **is** the subring inclusion applied to `g`; that is the whole
  computation, and this file only has to apply it (`AlgebraicGeometry.theta_nodeChartPatchChart` is
  an equality of `RingHom`s, so evaluating it at
  `AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv … g` is
  `AlgebraicGeometry.opensSectionsHom_nodeChartPatchChart_apply`).

## Main definitions and results

* `AlgebraicGeometry.opensSectionsHom_nodeChartPatchChart_apply`:
  `AlgebraicGeometry.theta_nodeChartPatchChart`, evaluated.
* `AlgebraicGeometry.isUnit_germ_nodeChartPsi_iff`: **the formula.**
* `AlgebraicGeometry.nodeChartPatchChartLift` and
  `AlgebraicGeometry.nodeChartPatchChartLift_comp`: the patch chart, lifted through the inclusion
  of the saturated locus, so that it is a chart of
  `AlgebraicGeometry.nodeChartSaturationFormalScheme` itself.
* `AlgebraicGeometry.preimage_basicOpen_nodeChartPatchChartLift`: **the non-vanishing locus, pulled
  back to the chart, is the basic open cut out by the image of `g`.**
* `AlgebraicGeometry.preimage_basicOpen_nodeChartAdicHom_comp_nodeChartPatchChartLift` and
  `AlgebraicGeometry.mem_basicOpen_base_nodeChartAdicHom_nodeChartPatchChartLift_iff`: the same
  statement read as the preimage of `D(g)` along the chart followed by
  `AlgebraicGeometry.nodeChartAdicHom`, as opens and at a point.
* `AlgebraicGeometry.eq_base_nodeChartAdicHom_nodeChartPatchChartLift`: **the formula determines the
  image point**, so it is a description of the base map on points and not only of a preimage.

## What is *not* proved here

**`hnode` is undecided in both directions and nothing here moves it.** The chain back to it runs
through `AlgebraicGeometry.exists_formalScheme_of_iso_restrict_tateInvNodeChartQuotientOpens`,
which is **one-way**: even all four hypotheses would give the existence of the formal scheme and not
the converse. And **refuting hypothesis 4 would not refute `hnode`**, because the hypothesis of
`AlgebraicGeometry.exists_formalScheme_of_isIso_desc` is existential while hypothesis 4 is that
condition at a *named* morphism.

**No clause of hypothesis 4 is decided here.** Not orbit separation, not surjectivity of
`(AlgebraicGeometry.nodeChartAdicHom …).base`, not its openness, and not the sheaf half. What the
formula gives is a **handle on all three space-half clauses at once**, since each of them is a
statement about the loci `{x | IsUnit (germ ⊤ x _ (nodeChartPsi g))}` and
`AlgebraicGeometry.preimage_basicOpen_nodeChartPatchChartLift` computes every one of those loci on
every chart. It gives **no** handle on the sheaf half, which is about section rings and not about
points; rows 1752 and 1761 have that.

**The three space-half clauses are read on the chain, and the charts here cover the chain, not the
quotient.** `AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff` quantifies over pairs of
points of the chain; nothing below compares two charts, or a chart with its `σ`-translates, so
nothing below says when two points with the same pattern are in the same orbit.

**The sheaf half and `AlgebraicGeometry.nonvanishingSectionsHom` are untouched.**

**`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` is still a `Classical.choice`**, and
`AlgebraicGeometry.nodeChartAdicHom` is still built from it, so `Classical.choice` still appears in
`#print axioms` of every statement below that mentions `hX`. That is the ambient one and not a new
one; the formula itself, `AlgebraicGeometry.isUnit_germ_nodeChartPsi_iff`, does not mention `hX`.

**Nothing here bears on `AlgebraicGeometry.tateInvNodeChartAmbientHom`**, whose refutation as an
open immersion (`AlgebraicGeometry.not_isOpenImmersion_tateInvNodeChartAmbientHom_of_ne_top`) is
untouched, and nothing here decides whether
`AlgebraicGeometry.tateInvNodeChartAwaySubring` is proper in the ambient ring.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.4, §10.4 (10.4.6), §10.6.
* [Deligne–Rapoport], II.1 — the Néron 1-gon.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)
variable [IsAdicRing (annulusIdealOfDefinition R I q)]
variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
  (annulusNodeChartCoord R I q))]
variable (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
variable [LocallyRingedSpace.IsOpenImmersion
    (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
      (tateChainInvFormalGlueData R I q hq hI).ι i)]

/-! ### `θ` at the patch chart, evaluated at a section -/

/-- **The chart-reading of `π^* g` is the image of `g` in the annulus algebra.**
`AlgebraicGeometry.theta_nodeChartPatchChart` is an equality of `RingHom`s whose right-hand side is
the inclusion of `AlgebraicGeometry.tateInvNodeChartAwaySubring`; evaluating it at
`AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv … g` cancels the
`AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv` on the left and leaves this. -/
theorem opensSectionsHom_nodeChartPatchChart_apply {y : (tateChainInv R I q hq hI)}
    (hy : y ∈ Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι i).base) (g) :
    (nodeChartPatchChart R I q hq hI i hy).opensSectionsHom
        (nodeChartSaturationOpens R I q hq hI)
        (range_nodeChartPatchChart_subset R I q hq hI i)
        ((((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app
          (op (tateInvNodeChartQuotientOpens R I q hq hI))).hom) g)
      = (tateInvNodeChartAwaySubring R I q hq hI).subtype
        (tateInvNodeChartQuotientRingEquiv R I q hq hI g) := by
  have h := RingHom.congr_fun (theta_nodeChartPatchChart R I q hq hI i hy)
    (tateInvNodeChartQuotientRingEquiv R I q hq hI g)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply] at h
  exact h

/-! ### The patch chart as a chart of the saturated locus -/

/-- **The patch-`i` basic-open chart, lifted through the inclusion of the saturated locus.** Its
range lies in that locus (`AlgebraicGeometry.range_nodeChartPatchChart_subset`), so the universal
property of the open immersion `AlgebraicGeometry.FormalScheme.restrictOpenι` lifts it. This is the
morphism the loci below are pulled back along; unlike
`AlgebraicGeometry.nodeChartPatchChart` it is a chart of
`AlgebraicGeometry.nodeChartSaturationFormalScheme` and not of the chain.

The inner type ascription is load-bearing: instance synthesis for
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion` of the inclusion only matches the
`AlgebraicGeometry.FormalScheme.restrictOpen` spelling, which
`AlgebraicGeometry.nodeChartSaturationFormalScheme` is definitionally but not syntactically. -/
def nodeChartPatchChartLift :
    FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) ⟶
      (nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace :=
  (LocallyRingedSpace.IsOpenImmersion.lift
    ((tateChainInv R I q hq hI).restrictOpenι (tateChainInv_locallyFG R I q hq hI)
      (nodeChartSaturationOpens R I q hq hI))
    (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
      (tateChainInvFormalGlueData R I q hq hI).ι i)
    (by
      rw [FormalScheme.range_restrictOpenι_base]
      exact range_nodeChartPatchChart_subset R I q hq hI i) :
    FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) ⟶
      ((tateChainInv R I q hq hI).restrictOpen (tateChainInv_locallyFG R I q hq hI)
        (nodeChartSaturationOpens R I q hq hI)).toLocallyRingedSpace)

omit [IsAdicRing (annulusIdealOfDefinition R I q)]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
    (annulusNodeChartCoord R I q))]
  [LocallyRingedSpace.IsOpenImmersion
    (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
      (tateChainInvFormalGlueData R I q hq hI).ι i)] in
/-- **The lift factors the patch chart through the inclusion**, which is what lets a point of the
chart be read either on the chain or on the saturated locus.
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac`. -/
theorem nodeChartPatchChartLift_comp :
    nodeChartPatchChartLift R I q hq hI i ≫ (tateChainInv R I q hq hI).restrictOpenι
        (tateChainInv_locallyFG R I q hq hI) (nodeChartSaturationOpens R I q hq hI)
      = basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι i := by
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac
    ((tateChainInv R I q hq hI).restrictOpenι (tateChainInv_locallyFG R I q hq hI)
      (nodeChartSaturationOpens R I q hq hI))
    (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
      (tateChainInvFormalGlueData R I q hq hI).ι i) _

/-! ### The formula -/

/-- **The germ of `AlgebraicGeometry.nodeChartPsi g`, computed on the patch chart.** At a point `x`
of the saturated locus which the patch-`i` chart hits at `w`, the germ is a unit exactly when the
class modulo `FormalSpectrum.awayCompletionIdeal` of the image of `g` in the annulus algebra
`A{1/(x + y − 1)}` avoids the prime `w`.

Two landed facts and nothing else:
`AlgebraicGeometry.FormalScheme.isUnit_germ_top_restrictOpen_iff`
(`FormalSchemes.ChartGermCriterion`) decides the germ at any chart in terms of the chart-reading of
the section, and `AlgebraicGeometry.opensSectionsHom_nodeChartPatchChart_apply` says that reading
is the subring inclusion. `AlgebraicGeometry.nodeChartPsi_eq` puts
`AlgebraicGeometry.nodeChartPsi` into the shape the first one consumes.

**The index `i` appears only in the hypotheses**: the right-hand side does not mention it. -/
theorem isUnit_germ_nodeChartPsi_iff {y : (tateChainInv R I q hq hI)}
    (hy : y ∈ Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι i).base)
    (x : nodeChartSaturationFormalScheme R I q hq hI)
    (w : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)))
    (hw : (nodeChartPatchChart R I q hq hI i hy).map.base w =
      ((tateChainInv R I q hq hI).restrictOpenι (tateChainInv_locallyFG R I q hq hI)
        (nodeChartSaturationOpens R I q hq hI)).base x) (g) :
    IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤ x trivial
        (nodeChartPsi R I q hq hI g)) ↔
      Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q))
        ((tateInvNodeChartAwaySubring R I q hq hI).subtype
          (tateInvNodeChartQuotientRingEquiv R I q hq hI g)) ∉ w.asIdeal := by
  have hg : nodeChartPsi R I q hq hI g =
      (tateChainInv R I q hq hI).restrictOpenTopSectionsHom (tateChainInv_locallyFG R I q hq hI)
        (nodeChartSaturationOpens R I q hq hI)
        ((((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app
          (op (tateInvNodeChartQuotientOpens R I q hq hI))).hom) g) := by
    rw [nodeChartPsi_eq]
    rfl
  rw [hg, ← opensSectionsHom_nodeChartPatchChart_apply R I q hq hI i hy g]
  exact FormalScheme.isUnit_germ_top_restrictOpen_iff (tateChainInv_locallyFG R I q hq hI)
    (nodeChartSaturationOpens R I q hq hI) (nodeChartPatchChart R I q hq hI i hy)
    (range_nodeChartPatchChart_subset R I q hq hI i) x w hw _

/-! ### The non-vanishing locus, pulled back to the chart -/

/-- **The non-vanishing locus of `AlgebraicGeometry.nodeChartPsi g` meets the patch-`i` chart in the
basic open cut out by the image of `g`.** This is
`AlgebraicGeometry.isUnit_germ_nodeChartPsi_iff` at every point of the chart at once, with the
membership hypothesis supplied by the point itself.

It is the statement `FormalSchemes.TateInvNodeChartBasicOpenPreimage` records as missing: the loci
that its three space-half statements quantify over are, chart by chart, basic opens of the affine
formal spectrum `Spf A{1/(x + y − 1)}`. -/
theorem preimage_basicOpen_nodeChartPatchChartLift (g) :
    (Opens.map (nodeChartPatchChartLift R I q hq hI i).base).obj
        ((nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace.toRingedSpace.basicOpen
          (nodeChartPsi R I q hq hI g))
      = basicOpen (awayCompletionIdeal (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q))
        ((tateInvNodeChartAwaySubring R I q hq hI).subtype
          (tateInvNodeChartQuotientRingEquiv R I q hq hI g)) := by
  refine TopologicalSpace.Opens.ext (Set.ext fun w => ?_)
  have hy : (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q) ≫ (tateChainInvFormalGlueData R I q hq hI).ι i).base w ∈
      Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q) ≫
          (tateChainInvFormalGlueData R I q hq hI).ι i).base := ⟨w, rfl⟩
  have hw : (nodeChartPatchChart R I q hq hI i hy).map.base w
      = ((tateChainInv R I q hq hI).restrictOpenι (tateChainInv_locallyFG R I q hq hI)
        (nodeChartSaturationOpens R I q hq hI)).base
        ((nodeChartPatchChartLift R I q hq hI i).base w) := by
    have h := nodeChartPatchChartLift_comp R I q hq hI i
    exact (congrFun (congrArg (fun m : FormalSpectrum.locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q)) ⟶ (tateChainInv R I q hq hI).toLocallyRingedSpace =>
      ⇑(ConcreteCategory.hom m.base)) h) w).symm
  exact (RingedSpace.mem_basicOpen _ (nodeChartPsi R I q hq hI g) _ trivial).trans
    (isUnit_germ_nodeChartPsi_iff R I q hq hI i hy _ w hw g)

/-! ### The preimage of `D(g)` along the chart -/

variable [TopologicalSpace ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
  (op (tateInvNodeChartQuotientOpens R I q hq hI)))]
variable [IsAdicRing (tateInvNodeChartQuotientIdeal R I q hq hI)]
variable (hfgI : (tateInvNodeChartQuotientIdeal R I q hq hI).FG)
variable (hX : FormalScheme.AdicSectionsLocallyFG (tateInvNodeChartQuotientIdeal R I q hq hI)
  (nodeChartPsi R I q hq hI))

/-- **The preimage of `D(g)` along the chart followed by `AlgebraicGeometry.nodeChartAdicHom` is the
basic open of the image of `g`.**
`AlgebraicGeometry.preimage_basicOpen_nodeChartAdicHom_base` identifies the preimage with the
non-vanishing locus, and `AlgebraicGeometry.preimage_basicOpen_nodeChartPatchChartLift` pulls that
back to the chart. -/
theorem preimage_basicOpen_nodeChartAdicHom_comp_nodeChartPatchChartLift (g) :
    (Opens.map (nodeChartPatchChartLift R I q hq hI i ≫
        nodeChartAdicHom R I q hq hI hfgI hX).base).obj
        (basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g)
      = basicOpen (awayCompletionIdeal (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q))
        ((tateInvNodeChartAwaySubring R I q hq hI).subtype
          (tateInvNodeChartQuotientRingEquiv R I q hq hI g)) := by
  rw [LocallyRingedSpace.comp_base, Opens.map_comp_obj,
    preimage_basicOpen_nodeChartAdicHom_base R I q hq hI hfgI hX g,
    preimage_basicOpen_nodeChartPatchChartLift R I q hq hI i g]

/-- **The pointwise form.** Which basic opens of the node chart's formal spectrum contain the image
of a point of the patch chart is decided by the prime of that point. -/
theorem mem_basicOpen_base_nodeChartAdicHom_nodeChartPatchChartLift_iff
    (w : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q))) (g) :
    (nodeChartAdicHom R I q hq hI hfgI hX).base
        ((nodeChartPatchChartLift R I q hq hI i).base w) ∈
        basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g ↔
      w ∈ basicOpen (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q))
        ((tateInvNodeChartAwaySubring R I q hq hI).subtype
          (tateInvNodeChartQuotientRingEquiv R I q hq hI g)) := by
  rw [← preimage_basicOpen_nodeChartAdicHom_comp_nodeChartPatchChartLift R I q hq hI i hfgI hX g]
  exact Iff.rfl

/-- **The formula determines the image point.** A point of the node chart's formal spectrum whose
basic opens are exactly the ones the formula predicts *is* the image of `w`, because a point of a
formal spectrum is determined by the basic opens containing it
(`FormalSpectrum.eq_of_forall_mem_basicOpen_iff`).

So the base map of `AlgebraicGeometry.nodeChartAdicHom` is described on points, at every point of
every patch chart, and not only through its preimages. -/
theorem eq_base_nodeChartAdicHom_nodeChartPatchChartLift
    (w : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)))
    (z : FormalSpectrum (tateInvNodeChartQuotientIdeal R I q hq hI))
    (hz : ∀ g, z ∈ basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g ↔
      w ∈ basicOpen (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q))
        ((tateInvNodeChartAwaySubring R I q hq hI).subtype
          (tateInvNodeChartQuotientRingEquiv R I q hq hI g))) :
    z = (nodeChartAdicHom R I q hq hI hfgI hX).base
      ((nodeChartPatchChartLift R I q hq hI i).base w) :=
  FormalSpectrum.eq_of_forall_mem_basicOpen_iff (tateInvNodeChartQuotientIdeal R I q hq hI)
    fun g => (hz g).trans
      (mem_basicOpen_base_nodeChartAdicHom_nodeChartPatchChartLift_iff
        R I q hq hI i hfgI hX w g).symm

end AlgebraicGeometry

end
