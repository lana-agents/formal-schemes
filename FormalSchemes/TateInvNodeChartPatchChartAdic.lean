import FormalSchemes.BasicOpenChartOpensSections
import FormalSchemes.TateInvNodeChartAdicSectionsChain

set_option linter.style.header false

/-!
# The node chart's source is adic over `nodeChartPsi`: the first of the four hypotheses

`FormalSchemes.TateInvNodeChartAdicSectionsChain` (row 1707) reduced the first hypothesis of
`AlgebraicGeometry.exists_formalScheme_of_adicSections` to an inequality of ideals at a chart of the
**chain**, and recorded that the ring homomorphism the bound is taken along,

```
θ d hd = ((d.opensSectionsHom (nodeChartSaturationOpens …) hd).comp
           ((actionQuotientπ …).c.app (op (tateInvNodeChartQuotientOpens …))).hom).comp
           (tateInvNodeChartQuotientRingEquiv …).symm
```

had **never been evaluated at any chart**. This file evaluates it, and the answer is the one that
file guessed:

> `AlgebraicGeometry.theta_nodeChartPatchChart`: at the basic-open chart
> `Spf A{1/(x + y − 1)} ⟶ Spf A ⟶ T_inv` cut out of the patch at **any** index `i`, `θ` is the
> inclusion `AlgebraicGeometry.tateInvNodeChartAwaySubring ↪ A{1/(x + y − 1)}`.

The bound is then `AlgebraicGeometry.tateInvNodeChartAwayIdeal`'s own definition — it *is*
`(awayCompletionIdeal …).comap (…).subtype` — so it holds by `le_rfl`, and since the chain's patches
are jointly surjective the charts exhaust the saturated locus. That gives
`AlgebraicGeometry.adicSectionsLocallyFG_nodeChartPsi`: **the first of the four hypotheses of
`AlgebraicGeometry.exists_formalScheme_of_adicSections` is true.**

## Why the `σ`-translates cost nothing

Row 1707 expected the computation to work at the patch at index `0` — where
`AlgebraicGeometry.tateInvChartSectionHom` is defined — and expected the rest of the saturated locus
to need a translate of it. It does not. Two facts do the work:

* `AlgebraicGeometry.map_ι_of_eq_tateInvSaturateOpens` holds at **every** index: the preimage of the
  saturated locus in each patch is the same open, `AlgebraicGeometry.tateInvPatchSaturateOpens`,
  which at the node-chart locus is the basic open `D(x + y − 1)`
  (`AlgebraicGeometry.map_tateChainInvι_nodeChartSaturationOpens`).
* `AlgebraicGeometry.tateInvConstFamily_tateInvChartSection` says every patch sees `π^* t` as the
  **same** section — `AlgebraicGeometry.tateInvConstFamily` of
  `AlgebraicGeometry.tateInvChartSection`, i.e. one section transported, not a family of different
  ones. So `AlgebraicGeometry.map_eqToHom_c_app_tateChainInvι_actionQuotientπ` reads the same
  element at every `i`.

So the index never enters the answer. That is a fact about the *projection* — it coequalises the
action — and not about a translation argument that had to be performed.

## The other half: the chart side meets the section side

The evaluation needs one general fact, proved in `FormalSchemes.BasicOpenChartOpensSections`: the
chart-side reading of a section over an open (through
`AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset` and
`FormalSpectrum.globalSectionsEquiv`) agrees with the EGA I 10.1.4 reading
(`FormalSpectrum.sectionsEquivOfEqBasicOpen`) that the whole Tate cluster's section rings are
spelled with. Without it the two sides of this file could not be compared at all.

## Main definitions and results

* `AlgebraicGeometry.map_tateChainInvι_nodeChartSaturationOpens`: the patch-`i` preimage of the
  saturated node-chart locus is `D(x + y − 1)`, for every `i`.
* `AlgebraicGeometry.nodeChartPatchChart` and
  `AlgebraicGeometry.range_nodeChartPatchChart_subset`: the chart, and the fact that it sits inside
  the saturated locus.
* `AlgebraicGeometry.map_eqToHom_c_app_tateChainInvι_actionQuotientπ`: every patch sees the same
  section.
* `AlgebraicGeometry.opensSectionsHom_nodeChartPatchChart`: the chart-restriction at that chart.
* `AlgebraicGeometry.theta_nodeChartPatchChart`: **`θ` is the subring inclusion.**
* `AlgebraicGeometry.exists_affineChart_le_comap_tateInvNodeChartAwayIdeal`: the bound holds at
  every point of the saturated locus.
* `AlgebraicGeometry.adicSectionsLocallyFG_nodeChartPsi`: **hypothesis 1 of four.**

## What is *not* proved here

**`hnode` is undecided, in both directions, and this file does not move it.** The hypothesis of
`AlgebraicGeometry.exists_formalScheme_of_adicSections` is one `∃` bundling four things. After this
file:

1. `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` at `AlgebraicGeometry.nodeChartPsi` —
   **proved here**.
2. `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.OverlapAdic` — **open**, untouched. It is a
   condition on charts of the *overlaps* of a cover, not on charts of the source; nothing here
   applies to it, and `FormalSchemes.AdicSectionsChart`'s module docstring records a further open
   question about it.
3. Invariance of `AlgebraicGeometry.nodeChartAdicHom` under
   `AlgebraicGeometry.tateInvNodeChartRestrictedAction` — **open**, not attempted anywhere.
4. `IsIso` of the descended morphism — **open**, not attempted anywhere.

Three of the four are open, and the chain back to `hnode` runs through
`AlgebraicGeometry.exists_formalScheme_of_iso_restrict_tateInvNodeChartQuotientOpens`, which is
**one-way**: even all four would give the existence of the formal scheme and not the converse.
Nothing here should be read as evidence that the node chart exists.

**Nothing here bears on `AlgebraicGeometry.tateInvNodeChartAmbientHom`.**
`AlgebraicGeometry.not_isOpenImmersion_tateInvNodeChartAmbientHom_of_ne_top` refutes it as an open
immersion and that refutation is untouched: `AlgebraicGeometry.theta_nodeChartPatchChart` is a
statement about *section maps*, which neither implies nor is implied by anything about open
immersions. In particular the subring inclusion appearing here is not a claim that the node chart's
ring is the ambient one — nothing on this tree decides whether
`AlgebraicGeometry.tateInvNodeChartAwaySubring` is the whole of the ambient ring or a proper subring
of it, in either direction, and `AlgebraicGeometry.tateInvNodeChartAwayIdeal` remains **not**
shown to be an ideal of definition (`FormalSchemes.TateInvNodeChartAmbient` records that only
Hausdorffness is proved of it).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.4, §10.4 (10.4.6), §10.6.
* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron 1-gon.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- **The patch-`i` preimage of the saturated node-chart locus is `D(x + y − 1)`, for every `i`.**
`AlgebraicGeometry.map_ι_of_eq_tateInvSaturateOpens` gives the same
`AlgebraicGeometry.tateInvPatchSaturateOpens` at every index, and
`AlgebraicGeometry.tateInvNodeChartOpens_eq_basicOpen` identifies it with the basic open. -/
theorem map_tateChainInvι_nodeChartSaturationOpens
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    (Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι i).base).obj
        (nodeChartSaturationOpens R I q hq hI)
      = basicOpen (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) :=
  (map_ι_of_eq_tateInvSaturateOpens (isOpen_tateInvNodeChartLocus R I q)
      (preimage_tateInvNodeChartQuotientOpens R I q hq hI) i).trans
    (tateInvNodeChartOpens_eq_basicOpen R I q hq hI)

set_option backward.isDefEq.respectTransparency false in
/-- **The patch-`i` basic-open chart sits inside the saturated node-chart locus.** Its range is the
image of `D(x + y − 1)`, and `AlgebraicGeometry.map_tateChainInvι_nodeChartSaturationOpens` says
that basic open is exactly the patch's preimage of the locus — so the containment is an equality on
the patch, not a proper one. -/
theorem range_nodeChartPatchChart_subset
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    Set.range (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι i).base
      ⊆ SetLike.coe (nodeChartSaturationOpens R I q hq hI) := by
  rintro z ⟨w, rfl⟩
  have hb : (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)).base w ∈ SetLike.coe
        ((Opens.map ((tateChainInvFormalGlueData R I q hq hI).ι i).base).obj
          (nodeChartSaturationOpens R I q hq hI)) := by
    have hw : (basicOpenChart (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)).base w ∈ Set.range (basicOpenChart
          (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)).base := ⟨w, rfl⟩
    rw [range_basicOpenChart_base _ _ (annulusIdealOfDefinition_fg R I q hI)] at hw
    rw [map_tateChainInvι_nodeChartSaturationOpens]
    exact hw
  simp only [LocallyRingedSpace.comp_base, TopCat.comp_app]
  exact hb

/-- The `RingHom` spelling of the split of the EGA I 10.1.4 reading at the intermediate open
`AlgebraicGeometry.tateInvPatchSaturateOpens`, which is where
`AlgebraicGeometry.tateInvNodeChartAmbientEquiv` is stated. -/
theorem sectionsEquivOfEqBasicOpen_map_tateChainInvι_comp
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    (sectionsEquivOfEqBasicOpen (annulusIdealOfDefinition R I q)
        (map_tateChainInvι_nodeChartSaturationOpens R I q hq hI i)).toRingHom
      = (tateInvNodeChartAmbientEquiv R I q hq hI).toRingHom.comp
        (((locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.map
          (eqToHom (congrArg op (map_ι_of_eq_tateInvSaturateOpens
            (isOpen_tateInvNodeChartLocus R I q)
            (preimage_tateInvNodeChartQuotientOpens R I q hq hI) i)))).hom) :=
  RingHom.ext fun s => sectionsEquivOfEqBasicOpen_trans (annulusIdealOfDefinition R I q)
    (annulusNodeChartCoord R I q)
    (map_ι_of_eq_tateInvSaturateOpens (isOpen_tateInvNodeChartLocus R I q)
      (preimage_tateInvNodeChartQuotientOpens R I q hq hI) i)
    (tateInvNodeChartOpens_eq_basicOpen R I q hq hI) s

/-- **Every patch sees the same section.** Restricting `π^* t` to the patch at index `i` and
transporting to `D(x + y − 1)` gives `AlgebraicGeometry.tateInvChartSection`, independently of `i`.
This is `AlgebraicGeometry.tateInvConstFamily_tateInvChartSection` with the transport of
`AlgebraicGeometry.tateInvConstFamily` cancelled against its inverse, and it is the reason the
`σ`-translates of the node chart cost nothing. -/
theorem map_eqToHom_c_app_tateChainInvι_actionQuotientπ
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
    (t : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
      (op (tateInvNodeChartQuotientOpens R I q hq hI))) :
    (((locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.map
        (eqToHom (congrArg op (map_ι_of_eq_tateInvSaturateOpens
          (isOpen_tateInvNodeChartLocus R I q)
          (preimage_tateInvNodeChartQuotientOpens R I q hq hI) i)))).hom)
        (((((tateChainInvFormalGlueData R I q hq hI).ι i).c.app
          (op (nodeChartSaturationOpens R I q hq hI))).hom)
          ((((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app
            (op (tateInvNodeChartQuotientOpens R I q hq hI))).hom) t))
      = tateInvChartSection (tateInvNodeChartQuotientOpens R I q hq hI)
          (isOpen_tateInvNodeChartLocus R I q)
          (preimage_tateInvSaturateQuotientOpens (isOpen_tateInvNodeChartLocus R I q)) t := by
  have hc : (((tateChainInvFormalGlueData R I q hq hI).ι i).c.app
        (op (nodeChartSaturationOpens R I q hq hI))).hom
        ((((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app
          (op (tateInvNodeChartQuotientOpens R I q hq hI))).hom) t)
      = tateInvConstFamily (isOpen_tateInvNodeChartLocus R I q)
          (preimage_tateInvNodeChartQuotientOpens R I q hq hI)
          (tateInvChartSection (tateInvNodeChartQuotientOpens R I q hq hI)
            (isOpen_tateInvNodeChartLocus R I q)
            (preimage_tateInvSaturateQuotientOpens (isOpen_tateInvNodeChartLocus R I q)) t) i :=
    tateInvConstFamily_tateInvChartSection _ _ _ t i
  rw [hc, tateInvConstFamily, ← CommRingCat.comp_apply, ← Functor.map_comp]
  simp only [eqToHom_trans, eqToHom_refl]
  erw [CategoryTheory.Functor.map_id]
  rfl

/-- **The away subring's inclusion, precomposed with the identification of the quotient's sections,
is the ambient reading of `AlgebraicGeometry.tateInvChartSectionHom`.** This is `rfl`:
`AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv` is built out of
`AlgebraicGeometry.tateInvChartRingEquiv`, a codomain restriction of that homomorphism, and of
`AlgebraicGeometry.tateInvNodeChartSubringEquivAway`, a `RingEquiv.subringMap` along
`AlgebraicGeometry.tateInvNodeChartAmbientEquiv`. -/
theorem subtype_comp_tateInvNodeChartQuotientRingEquiv :
    (tateInvNodeChartAwaySubring R I q hq hI).subtype.comp
        (tateInvNodeChartQuotientRingEquiv R I q hq hI).toRingHom
      = (tateInvNodeChartAmbientEquiv R I q hq hI).toRingHom.comp
        (tateInvChartSectionHom (tateInvNodeChartQuotientOpens R I q hq hI)
          (isOpen_tateInvNodeChartLocus R I q)
          (preimage_tateInvSaturateQuotientOpens (isOpen_tateInvNodeChartLocus R I q))) := rfl

section Chart

variable [IsAdicRing (annulusIdealOfDefinition R I q)]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
    (annulusNodeChartCoord R I q))]

variable (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)

variable [LocallyRingedSpace.IsOpenImmersion
    (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
      (tateChainInvFormalGlueData R I q hq hI).ι i)]

/-- **The patch-`i` basic-open chart of the chain**, at a point of its range:
`AlgebraicGeometry.FormalScheme.AffineChart.ofPatchBasicOpen` at the annulus and the node-chart
coordinate. Its ring is `A{1/(x + y − 1)}` and its ideal of definition is
`FormalSpectrum.awayCompletionIdeal` of that, both on the nose. -/
def nodeChartPatchChart {y : (tateChainInv R I q hq hI)}
    (hy : y ∈ Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι i).base) :
    FormalScheme.AffineChart (tateChainInv R I q hq hI) y :=
  FormalScheme.AffineChart.ofPatchBasicOpen (annulusIdealOfDefinition R I q)
    (annulusNodeChartCoord R I q) ((tateChainInvFormalGlueData R I q hq hI).ι i) hy

/-- **Its chart-restriction of a section over the saturated locus is the patch's sheaf component
followed by the EGA I 10.1.4 reading.**
`AlgebraicGeometry.FormalScheme.AffineChart.opensSectionsHom_ofPatchBasicOpen`
(`FormalSchemes.BasicOpenChartOpensSections`) at the patch inclusion; the hypothesis it needs — that
the patch's preimage of the locus *is* the basic open — is
`AlgebraicGeometry.map_tateChainInvι_nodeChartSaturationOpens`. -/
theorem opensSectionsHom_nodeChartPatchChart {y : (tateChainInv R I q hq hI)}
    (hy : y ∈ Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι i).base) :
    (nodeChartPatchChart R I q hq hI i hy).opensSectionsHom
        (nodeChartSaturationOpens R I q hq hI)
        (range_nodeChartPatchChart_subset R I q hq hI i)
      = (sectionsEquivOfEqBasicOpen (annulusIdealOfDefinition R I q)
          (map_tateChainInvι_nodeChartSaturationOpens R I q hq hI i)).toRingHom.comp
        ((((tateChainInvFormalGlueData R I q hq hI).ι i).c.app
          (op (nodeChartSaturationOpens R I q hq hI))).hom) :=
  FormalScheme.AffineChart.opensSectionsHom_ofPatchBasicOpen _ _ _
    (annulusIdealOfDefinition_fg R I q hI) hy _ _
    (map_tateChainInvι_nodeChartSaturationOpens R I q hq hI i)

set_option backward.isDefEq.respectTransparency false in
/-- **`θ` at the patch-`i` basic-open chart is the inclusion of the away subring.** This is the
evaluation `FormalSchemes.TateInvNodeChartAdicSectionsChain` left open, at every patch at once.

The proof is a single factorisation: the chart-restriction is the patch's sheaf component followed
by the ambient reading (`AlgebraicGeometry.opensSectionsHom_nodeChartPatchChart` and
`AlgebraicGeometry.sectionsEquivOfEqBasicOpen_map_tateChainInvι_comp`), the sheaf component of the
projection composed with the patch's is `AlgebraicGeometry.tateInvChartSectionHom`
(`AlgebraicGeometry.map_eqToHom_c_app_tateChainInvι_actionQuotientπ`), and the ambient reading of
that is the identification the away subring is defined by
(`AlgebraicGeometry.subtype_comp_tateInvNodeChartQuotientRingEquiv`, which is `rfl`). -/
theorem theta_nodeChartPatchChart {y : (tateChainInv R I q hq hI)}
    (hy : y ∈ Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι i).base) :
    (((nodeChartPatchChart R I q hq hI i hy).opensSectionsHom
          (nodeChartSaturationOpens R I q hq hI)
          (range_nodeChartPatchChart_subset R I q hq hI i)).comp
        ((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app
          (op (tateInvNodeChartQuotientOpens R I q hq hI))).hom).comp
        (tateInvNodeChartQuotientRingEquiv R I q hq hI).symm
      = (tateInvNodeChartAwaySubring R I q hq hI).subtype := by
  have hP : ((((locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.map
          (eqToHom (congrArg op (map_ι_of_eq_tateInvSaturateOpens
            (isOpen_tateInvNodeChartLocus R I q)
            (preimage_tateInvNodeChartQuotientOpens R I q hq hI) i)))).hom).comp
        ((((tateChainInvFormalGlueData R I q hq hI).ι i).c.app
          (op (nodeChartSaturationOpens R I q hq hI))).hom)).comp
        ((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app
          (op (tateInvNodeChartQuotientOpens R I q hq hI))).hom
      = tateInvChartSectionHom (tateInvNodeChartQuotientOpens R I q hq hI)
          (isOpen_tateInvNodeChartLocus R I q)
          (preimage_tateInvSaturateQuotientOpens (isOpen_tateInvNodeChartLocus R I q)) :=
    RingHom.ext fun t => map_eqToHom_c_app_tateChainInvι_actionQuotientπ R I q hq hI i t
  have hcomp : ((sectionsEquivOfEqBasicOpen (annulusIdealOfDefinition R I q)
        (map_tateChainInvι_nodeChartSaturationOpens R I q hq hI i)).toRingHom.comp
        ((((tateChainInvFormalGlueData R I q hq hI).ι i).c.app
          (op (nodeChartSaturationOpens R I q hq hI))).hom)).comp
        ((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app
          (op (tateInvNodeChartQuotientOpens R I q hq hI))).hom
      = (tateInvNodeChartAwaySubring R I q hq hI).subtype.comp
        (tateInvNodeChartQuotientRingEquiv R I q hq hI).toRingHom := by
    rw [subtype_comp_tateInvNodeChartQuotientRingEquiv,
      sectionsEquivOfEqBasicOpen_map_tateChainInvι_comp, RingHom.comp_assoc, RingHom.comp_assoc]
    exact congrArg _ hP
  rw [opensSectionsHom_nodeChartPatchChart, hcomp, RingHom.comp_assoc]
  rw [show ((tateInvNodeChartQuotientRingEquiv R I q hq hI).toRingHom.comp
      (↑(tateInvNodeChartQuotientRingEquiv R I q hq hI).symm))
      = RingHom.id _ from RingHom.ext fun z =>
        (tateInvNodeChartQuotientRingEquiv R I q hq hI).apply_symm_apply z]
  exact RingHom.comp_id _

end Chart

set_option backward.isDefEq.respectTransparency false in
/-- **The bound holds at every point of the saturated node-chart locus.** The chart is the
patch-`i` one for any `i` whose image contains the point — the chain's patches are jointly
surjective — and the bound is then `AlgebraicGeometry.tateInvNodeChartAwayIdeal`'s own definition,
`le_rfl`.

This is the right-hand side of `AlgebraicGeometry.adicSectionsLocallyFG_nodeChartPsi_iff_awayIdeal`
verbatim, so it is the reduced condition and not a variant of it. -/
theorem exists_affineChart_le_comap_tateInvNodeChartAwayIdeal
    {y : (tateChainInv R I q hq hI)} (hy : y ∈ nodeChartSaturationOpens R I q hq hI) :
    ∃ (d : FormalScheme.AffineChart (tateChainInv R I q hq hI) y)
      (hd : Set.range d.map.base ⊆ SetLike.coe (nodeChartSaturationOpens R I q hq hI)),
      d.I.FG ∧ tateInvNodeChartAwayIdeal R I q hq hI ≤ d.I.comap
        (((d.opensSectionsHom (nodeChartSaturationOpens R I q hq hI) hd).comp
          ((actionQuotientπ (tateInvPeriodAction R I q hq hI)).c.app
            (op (tateInvNodeChartQuotientOpens R I q hq hI))).hom).comp
          (tateInvNodeChartQuotientRingEquiv R I q hq hI).symm) := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) := isAdicRing_tateInvNodeChartAmbient R I q hI
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) :=
    isOpenImmersion_basicOpenChart _ _ (annulusIdealOfDefinition_fg R I q hI)
  obtain ⟨i, z, rfl⟩ := (tateChainInvFormalGlueData R I q hq hI).ι_jointly_surjective y
  haveI := (tateChainInvFormalGlueData R I q hq hI).ι_isOpenImmersion i
  haveI : LocallyRingedSpace.IsOpenImmersion
      (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι i) := inferInstance
  have hz : z ∈ Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)).base := by
    rw [range_basicOpenChart_base _ _ (annulusIdealOfDefinition_fg R I q hI),
      ← map_tateChainInvι_nodeChartSaturationOpens R I q hq hI i]
    exact hy
  obtain ⟨w, hw⟩ := hz
  have hy' : ((tateChainInvFormalGlueData R I q hq hI).ι i).base z ∈
      Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q) ≫
          (tateChainInvFormalGlueData R I q hq hI).ι i).base := by
    refine ⟨w, ?_⟩
    simp only [LocallyRingedSpace.comp_base, TopCat.comp_app]
    exact congrArg _ hw
  refine ⟨nodeChartPatchChart R I q hq hI i hy',
    range_nodeChartPatchChart_subset R I q hq hI i,
    awayCompletionIdeal_fg _ _ (annulusIdealOfDefinition_fg R I q hI), ?_⟩
  rw [theta_nodeChartPatchChart]
  exact le_rfl

/-- **The first of the four hypotheses of `AlgebraicGeometry.exists_formalScheme_of_adicSections`
holds**, over a principal base ideal generated by a non-zero-divisor: the node chart's source is
adic over `AlgebraicGeometry.nodeChartPsi` on a neighbourhood basis.

The `letI`/`haveI` are the ones that theorem states its own hypothesis under, so this theorem's
conclusion is literally the first component of its `∃`.

**It does not decide `hnode`.** Three of the four remain open and the chain back is one-way; see
this file's "What is *not* proved here". -/
theorem adicSectionsLocallyFG_nodeChartPsi (t : R) (ht : I = Ideal.span {t})
    (hreg : IsLeftRegular t) :
    letI : TopologicalSpace ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
        (op (tateInvNodeChartQuotientOpens R I q hq hI))) :=
      (tateInvNodeChartQuotientIdeal R I q hq hI).adicTopology
    haveI : IsAdicRing (tateInvNodeChartQuotientIdeal R I q hq hI) :=
      isAdicRing_tateInvNodeChartQuotientIdeal_of_isLeftRegular_base R I q hq hI t ht hreg
    FormalScheme.AdicSectionsLocallyFG (tateInvNodeChartQuotientIdeal R I q hq hI)
      (nodeChartPsi R I q hq hI) :=
  adicSectionsLocallyFG_nodeChartPsi_of_charts R I q hq hI t ht hreg
    fun _ hy => exists_affineChart_le_comap_tateInvNodeChartAwayIdeal R I q hq hI hy

end AlgebraicGeometry
end
