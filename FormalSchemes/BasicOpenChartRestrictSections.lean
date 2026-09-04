import FormalSchemes.BasicOpenChartRestrict
import FormalSchemes.BasicOpenRestrictionIdentification
import FormalSchemes.SpfGamma

set_option linter.style.header false

/-!
# The chart inclusion of a basic open acts on global sections as the restriction

For an adic ring `(R, I)` with `I` finitely generated and an inclusion of basic opens
`D(g) ≤ D(f)`, two maps `R{1/f} → R{1/g}` are in play and they were built by unrelated routes:

* the **sheaf-theoretic** one, `FormalSpectrum.basicOpenRes`
  (`FormalSchemes.BasicOpenRestriction`), the restriction `Γ(D(f)) ⟶ Γ(D(g))` of the structure
  sheaf of `Spf R` conjugated by `FormalSpectrum.sectionsBasicOpenEquiv`;
* the **geometric** one, obtained by taking global sections of the chart inclusion
  `FormalSpectrum.basicOpenChartRestrict I f g hI hle : Spf R{1/g} ⟶ Spf R{1/f}`
  (`FormalSchemes.BasicOpenChartRestrict`).

This file says they agree. It is the statement that ties the geometric layer — where the charts of
the basic opens form a diagram over `Spf R` — to the sheaf layer, and it needs a file of its own
because the two files above are siblings: neither imports the other, so whichever hosted the
statement would have to import the other one. `FormalSchemes.BasicOpenChartRestrict` is also
deliberately free of any topology on `R`, which is what keeps its statements at their present
generality, and this statement cannot be made without one.

## Main results

* `FormalSpectrum.globalSectionsMap_basicOpenChartRestrict`: **the identification.**
* `FormalSpectrum.basicOpenChartRestrict_le_comap_globalSectionsMap`: a chart inclusion is adic on
  global sections, the form in which `FormalSchemes.AdicOnSections` consumes such statements.

## Implementation notes

The mathematics is two rewrites; the work is instance data, and there are four pieces of it. A
topology on `R` and `IsAdicRing I` are needed for `FormalSpectrum.basicOpenRes` to exist at all,
since it is a restriction map of the structure sheaf of `Spf R`. `IsAdicRing` on each of
`FormalSpectrum.awayCompletionIdeal I f` and `awayCompletionIdeal I g` is needed for
`FormalSpectrum.globalSectionsMap` at those two rings, because
`FormalSpectrum.globalSectionsEquiv` (`FormalSchemes.Sections`) is stated for adic rings.

The topology on `R{1/f}` is not a hypothesis: `FormalSpectrum.awayCompletion I f` is an
`AdicCompletion`, and the adic topology of the extended ideal is already an instance on it
(`FormalSchemes.RestrictedPowerSeries`). Only completeness and Hausdorffness — that is,
`IsAdicRing` — has to be supplied, and it is not an instance because it needs `Ideal.FG`.

The two chart-level instances are therefore **redundant** here: `hI : I.FG` is already a hypothesis
of every statement below, and `FormalSpectrum.isAdicRing_awayCompletionIdeal`
(`FormalSchemes.BasicOpenChart`) turns it into both of them. They are still taken as instance
hypotheses, spelled out in each statement rather than in the `variable` block, because that is the
convention this tree settled on — `FormalSchemes.AdicOnSections` carries
`[IsAdicRing (awayCompletionIdeal I f)]` in exactly this way for the chart one level down, and a
consumer discharges it with that lemma.

## What is *not* proved here

**Nothing about stalks, germs, colimits or `FormalSpectrum.IsStalkLimit`**
(`FormalSchemes.StructureSheafStalks`), which is undecided on this tree in both directions. A
statement about the global sections of *one* chart inclusion is not a partial answer to it.

**Nothing about sections over an open other than `⊤`.** `FormalSpectrum.globalSectionsMap` is
about the section over the whole space; the sheaf component of `basicOpenChartRestrict` at a
general open is a larger piece of work and nothing below approaches it.

**The identification of `FormalSpectrum.basicOpenRes` with
`FormalSpectrum.awayCompletionRestrict` is not proved here.** It is
`FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict`
(`FormalSchemes.BasicOpenRestrictionIdentification`) and it is the substance of what is used below;
this file only transports it across `FormalSpectrum.globalSectionsMap`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1, §10.4.6.
-/

noncomputable section

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I] (f g : R)

/-- **The chart inclusion attached to `D(g) ≤ D(f)` acts on global sections as the structure-sheaf
restriction.** Taking global sections of `FormalSpectrum.basicOpenChartRestrict`
(`FormalSchemes.BasicOpenChartRestrict`) returns `FormalSpectrum.basicOpenRes`
(`FormalSchemes.BasicOpenRestriction`).

Two inputs, one for each half. `FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap`
(`FormalSchemes.SpfGamma`) — one half of EGA I 10.4.6 — says that global sections of `Spf` of a
continuous ring map give that ring map back; the chart inclusion is `Spf` of
`FormalSpectrum.awayCompletionRestrict` by definition, so it gives that. That the resulting ring
map is the structure-sheaf restriction is `FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict`
(`FormalSchemes.BasicOpenRestrictionIdentification`), which is not proved here.

The two `IsAdicRing` instances on the completed localizations are what
`FormalSpectrum.globalSectionsMap` needs at its two rings; both follow from the `Ideal.FG`
hypothesis already present, by `FormalSpectrum.isAdicRing_awayCompletionIdeal`
(`FormalSchemes.BasicOpenChart`). -/
@[simp]
theorem globalSectionsMap_basicOpenChartRestrict
    [IsAdicRing (awayCompletionIdeal I f)] [IsAdicRing (awayCompletionIdeal I g)]
    (hI : I.FG) (hle : basicOpen I g ≤ basicOpen I f) :
    globalSectionsMap (awayCompletionIdeal I f) (awayCompletionIdeal I g)
      (basicOpenChartRestrict I f g hI hle) = basicOpenRes I hle := by
  rw [basicOpenChartRestrict, globalSectionsMap_locallyRingedSpaceMap,
    basicOpenRes_eq_awayCompletionRestrict]

/-- **A chart inclusion is adic on global sections**: the ideal of definition of `R{1/f}` is
carried into the ideal of definition of `R{1/g}`. This is the peer, one chart up, of
`FormalSpectrum.basicOpenChart_le_comap_globalSectionsMap` (`FormalSchemes.AdicOnSections`), and it
is the form in which `FormalSpectrum.le_comap_globalSectionsMap_comp` there consumes such a
statement when a composite of charts has to discharge a continuity obligation.

It is `FormalSpectrum.le_comap_basicOpenRes` (`FormalSchemes.BasicOpenRestrictionIdentification`)
moved across the identification above; on the sheaf side the ideal is carried *onto* the ideal and
not merely into it, by `FormalSpectrum.map_basicOpenRes` there. -/
theorem basicOpenChartRestrict_le_comap_globalSectionsMap
    [IsAdicRing (awayCompletionIdeal I f)] [IsAdicRing (awayCompletionIdeal I g)]
    (hI : I.FG) (hle : basicOpen I g ≤ basicOpen I f) :
    awayCompletionIdeal I f ≤ (awayCompletionIdeal I g).comap
      (globalSectionsMap (awayCompletionIdeal I f) (awayCompletionIdeal I g)
        (basicOpenChartRestrict I f g hI hle)) := by
  rw [globalSectionsMap_basicOpenChartRestrict]
  exact le_comap_basicOpenRes I hle

end FormalSpectrum
