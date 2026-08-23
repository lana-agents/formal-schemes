import FormalSchemes.GeneralFibreProductBothExposeXY

set_option linter.style.header false

/-!
# Global sections of the chart structural morphisms of a two-sided datum

For a two-sided fibre-product datum `D : BothChartedFibreDatumXY R I hI` with `X`-charts `Spf(A i)`
and `Y`-charts `Spf(B j)`, each chart carries a structural morphism to `Spf R`
(`BothChartedFibreDatumXY.xStructMapChart` / `yStructMapChart`,
`FormalSchemes.GeneralFibreProductBothExposeXY`). This file records the one fact about them that
the descent machinery keeps needing: on global sections they are the structure algebra maps.

## Main results

* `BothChartedFibreDatumXY.globalSectionsMap_xStructMapChart`,
  `BothChartedFibreDatumXY.globalSectionsMap_yStructMapChart`:
  `Γ(xStructMapChart i) = algebraMap R (A i)` and `Γ(yStructMapChart j) = algebraMap R (B j)`.

Both are consumed when a per-piece `R`-algebra map is built from a chart factorization — by
`FormalSchemes.GeneralFibreProductLiftCharts` (`xAlgOf` / `yAlgOf`),
`FormalSchemes.GeneralFibreProductLiftUniqueAdic`, and
`FormalSchemes.BothDatumAdicOverBase` (where the composite's adicity is read off from
`Ideal.le_comap_map`).

## What this module used to be, and the name (issue 812)

It used to build the whole per-piece `R`-algebra package — `refinedStructHom`, `refinedAlgebra`,
`refinedAlgebra_hIL`, `xAlg`, `yAlg` and the two factorization identities — for the
`Classical.choice` refined cover of `FormalSchemes.GlueOpenCoverFactorBoth`. That cover is gone
(see that module's docstring for why), and the parametrised tower in
`FormalSchemes.GeneralFibreProductLiftCharts` carries its own `…Of` versions of every one of those
declarations, built over a user-supplied chart family instead. Only the two chart-level lemmas
above were shared, so only they remain.

The module name is a leftover from that history and no longer describes the contents. Renaming it
would touch three importers and the generated import list for no mathematical gain, so it is left
for whenever this file is next edited for a real reason.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6, §10.7.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology FormalSpectrum

universe u

namespace AlgebraicGeometry.BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable (D : BothChartedFibreDatumXY R I hI)

/-- `globalSectionsMap` of the `X`-chart structure map `xStructMapChart i` is the algebra map
`R → A_i`. -/
theorem globalSectionsMap_xStructMapChart (i : D.JX) :
    letI := D.commRingA; letI := D.algebraA; letI := D.topologyA; letI := D.isAdicA
    globalSectionsMap I (I.map (algebraMap R (D.A i))) (D.xStructMapChart i) =
      algebraMap R (D.A i) := by
  letI := D.commRingA; letI := D.algebraA; letI := D.topologyA; letI := D.isAdicA
  exact globalSectionsMap_locallyRingedSpaceMap I (I.map (algebraMap R (D.A i)))
    (algebraMap R (D.A i)) Ideal.le_comap_map

/-- `globalSectionsMap` of the `Y`-chart structure map `yStructMapChart j` is the algebra map
`R → B_j`. -/
theorem globalSectionsMap_yStructMapChart (j : D.JY) :
    letI := D.commRingB; letI := D.algebraB; letI := D.topologyB; letI := D.isAdicB
    globalSectionsMap I (I.map (algebraMap R (D.B j))) (D.yStructMapChart j) =
      algebraMap R (D.B j) := by
  letI := D.commRingB; letI := D.algebraB; letI := D.topologyB; letI := D.isAdicB
  exact globalSectionsMap_locallyRingedSpaceMap I (I.map (algebraMap R (D.B j)))
    (algebraMap R (D.B j)) Ideal.le_comap_map

end AlgebraicGeometry.BothChartedFibreDatumXY

end
