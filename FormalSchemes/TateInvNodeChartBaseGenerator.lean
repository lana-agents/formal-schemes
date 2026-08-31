import FormalSchemes.TateInvChartBaseImage
import FormalSchemes.TateInvNodeChartPrincipal

set_option linter.style.header false

/-!
# The node chart over a principal base ideal, with the membership hypothesis discharged

`FormalSchemes.TateInvNodeChartPrincipal` (issue 1284) reduces adic completeness and finite
generation of the node chart's candidate ideal of definition, over a base with `I = (t)`, to three
hypotheses: the membership

```
hmem : algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
         (annulusNodeChartCoord R I q)) t ∈ tateInvNodeChartAwaySubring R I q hq hI
```

and left-regularity of the images of that element under the two forward legs. Its module docstring
records `hmem` as unproved, and records why: computing a leg on the structural image of the base
crosses the boundary between the `FormalSpectrum.structureSheaf` and
`FormalSpectrum.locallyRingedSpaceObj` spellings of a section ring, and doing that at these concrete
rings does not typecheck.

`FormalSchemes.AdicOnOpenSectionsPointwise` removes that obstruction and
`FormalSchemes.TateInvChartBaseImage` uses it to prove
`AlgebraicGeometry.algebraMap_mem_tateInvNodeChartAwaySubring`, which **is** `hmem`, for every
`r : R` and with no hypothesis beyond the standing ones. This file feeds that in.

## What is proved

* `AlgebraicGeometry.hasCofinalInducedFiltration_tateInvNodeChartAwaySubring'`,
  `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_principal'` and
  `AlgebraicGeometry.fg_tateInvNodeChartAwayIdeal_of_principal'` — the three results of
  `FormalSchemes.TateInvNodeChartPrincipal` with `hmem` gone. **Left-regularity of the two forward
  legs' images is still a hypothesis of each**, unchanged and unweakened.

That is the whole content: one of the three hypotheses is now a theorem, and the primed statements
say so. Nothing here says anything about the other two.

## What is *not* proved

* **Left-regularity is still not supplied at any base with `t ≠ 0`**, no counterexample is known,
  and it is not shown necessary. It is no longer a question about a twice-completed localization,
  though: `FormalSchemes.TateInvNodeChartLegRegular` computes both leg images and shows that
  left-regularity of `algebraMap R (annulusAlgebra R I q) t` in `R{x, y}/(x·y − q)` itself
  suffices. That file's
  `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular`
  and its two companions are these three results with the two leg hypotheses replaced by that one.
  **The reduction is one-way** and exhibits no witness.
  `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_bot` and
  `AlgebraicGeometry.fg_tateInvNodeChartAwayIdeal_bot`
  (`FormalSchemes.TateInvNodeChartPrincipal`) remain the only unconditional case, and they do not
  come from the principal criterion — at `c = 0` its saturation hypothesis reads `S = ⊤`.
* **Nothing here is a chart.** No adic structure is claimed on the ring beyond what is stated, no
  open immersion is built, and nothing is said about the chart ring being proper or larger than the
  base.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- **The filtration bridge over a principal base ideal, with the membership hypothesis
discharged.** `AlgebraicGeometry.hasCofinalInducedFiltration_tateInvNodeChartAwaySubring` fed
`AlgebraicGeometry.algebraMap_mem_tateInvNodeChartAwaySubring`.

The two left-regularity hypotheses are unchanged; only `hmem` is gone. -/
theorem hasCofinalInducedFiltration_tateInvNodeChartAwaySubring' (t : R)
    (ht : I = Ideal.span {t})
    (hregX : IsLeftRegular (tateInvNodeChartAwayLegX R I q hq hI (algebraMap R _ t)))
    (hregY : IsLeftRegular (tateInvNodeChartAwayLegY R I q hq hI (algebraMap R _ t))) :
    (tateInvNodeChartAwaySubring R I q hq hI).HasCofinalInducedFiltration
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) :=
  hasCofinalInducedFiltration_tateInvNodeChartAwaySubring R I q hq hI t ht
    (algebraMap_mem_tateInvNodeChartAwaySubring (hq := hq) (hI := hI) t) hregX hregY

/-- **Adic completeness of the node chart ring over a principal base ideal, with the membership
hypothesis discharged.** `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_principal`
fed `AlgebraicGeometry.algebraMap_mem_tateInvNodeChartAwaySubring`. -/
theorem isAdicComplete_tateInvNodeChartAwayIdeal_of_principal' (t : R) (ht : I = Ideal.span {t})
    (hregX : IsLeftRegular (tateInvNodeChartAwayLegX R I q hq hI (algebraMap R _ t)))
    (hregY : IsLeftRegular (tateInvNodeChartAwayLegY R I q hq hI (algebraMap R _ t))) :
    IsAdicComplete (tateInvNodeChartAwayIdeal R I q hq hI)
      (tateInvNodeChartAwaySubring R I q hq hI) :=
  isAdicComplete_tateInvNodeChartAwayIdeal_of_principal R I q hq hI t ht
    (algebraMap_mem_tateInvNodeChartAwaySubring (hq := hq) (hI := hI) t) hregX hregY

/-- **Finite generation of the candidate ideal of definition over a principal base ideal, with the
membership hypothesis discharged.** `AlgebraicGeometry.fg_tateInvNodeChartAwayIdeal_of_principal`
fed `AlgebraicGeometry.algebraMap_mem_tateInvNodeChartAwaySubring`. -/
theorem fg_tateInvNodeChartAwayIdeal_of_principal' (t : R) (ht : I = Ideal.span {t})
    (hregX : IsLeftRegular (tateInvNodeChartAwayLegX R I q hq hI (algebraMap R _ t)))
    (hregY : IsLeftRegular (tateInvNodeChartAwayLegY R I q hq hI (algebraMap R _ t))) :
    (tateInvNodeChartAwayIdeal R I q hq hI).FG :=
  fg_tateInvNodeChartAwayIdeal_of_principal R I q hq hI t ht
    (algebraMap_mem_tateInvNodeChartAwaySubring (hq := hq) (hI := hI) t) hregX hregY

end AlgebraicGeometry
