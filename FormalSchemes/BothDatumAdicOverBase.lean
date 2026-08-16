import FormalSchemes.AdicOverBaseChart
import FormalSchemes.GlueOpenCoverFactorBothAlg

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The glued factor `xGlued` is adic over its structural morphism `xStructMap`

For a two-sided fibre-product datum `D : BothChartedFibreDatumXY R I hI`, the glued factor
`D.xGlued` is glued from the affine charts `Spf(I·A_i)` whose structural morphism into the base is
`D.xStructMapChart i`, and on global sections `Γ (xStructMapChart i) = algebraMap R (A_i)`
(`globalSectionsMap_xStructMapChart`), which is adic (`I ≤ (I·A_i).comap (algebraMap R (A_i))`,
`Ideal.le_comap_map`). Since the gluing charts `ι i` jointly cover `xGlued` and each satisfies
`ι i ≫ xStructMap = xStructMapChart i` (`ι_xStructMap`), they exhibit `xGlued` as **adic over the
base** `D.xStructMap` in the sense of `FormalScheme.AdicOverBaseLocallyFG`.

Combined with `exists_affineChart_subset_adicOverBase`, this gives an adic-over-`xStructMap` affine
neighborhood basis of `xGlued` — the missing ingredient behind the general diagonal's continuity
witness `hs` (issues 468/487): a refined chart of `xGlued` chosen from this basis is adic over the
base, so its X-leg `xFactor` is adic on global sections. (Threading this bound through the
`Classical.choice` refined-cover construction so that the *chosen* `bothRefinedChart` carries it is
the remaining, separate step; this file supplies the base-relative geometric input.)

The `Y`-side statement `AdicOverBaseLocallyFG D.yGlued D.yStructMap` is identical with the `A`/`X`
data replaced by `B`/`Y`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6, §10.7, §10.12.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology FormalSpectrum

universe u

namespace AlgebraicGeometry.BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]

set_option backward.isDefEq.respectTransparency false in
/-- **`xGlued` is adic over its structural morphism `xStructMap`.** Every point lies in a gluing
chart `ι i : Spf(I·A_i) ⟶ xGlued`, an open immersion, whose composite with `xStructMap` is
`xStructMapChart i` (`ι_xStructMap`), adic on global sections because
`Γ (xStructMapChart i) = algebraMap R (A_i)` carries `I` into `I·A_i` (`Ideal.le_comap_map`). -/
theorem adicOverBase_xStructMap (D : BothChartedFibreDatumXY R I hI) :
    FormalScheme.AdicOverBaseLocallyFG D.xGlued D.xStructMap := by
  letI := D.commRingA; letI := D.algebraA; letI := D.topologyA; letI := D.isAdicA
  intro x
  obtain ⟨i, y, hy⟩ := D.xFormalGlueData.ι_jointly_surjective x
  refine ⟨D.A i, inferInstance, inferInstance, I.map (algebraMap R (D.A i)), inferInstance,
    D.xFormalGlueData.ι i, hI.map _, ⟨y, hy⟩, inferInstance, ?_⟩
  rw [D.ι_xStructMap i, D.globalSectionsMap_xStructMapChart i]
  exact Ideal.le_comap_map

set_option backward.isDefEq.respectTransparency false in
/-- **`yGlued` is adic over its structural morphism `yStructMap`.** The `Y`-side analogue of
`adicOverBase_xStructMap`. -/
theorem adicOverBase_yStructMap (D : BothChartedFibreDatumXY R I hI) :
    FormalScheme.AdicOverBaseLocallyFG D.yGlued D.yStructMap := by
  letI := D.commRingB; letI := D.algebraB; letI := D.topologyB; letI := D.isAdicB
  intro x
  obtain ⟨j, y, hy⟩ := D.yFormalGlueData.ι_jointly_surjective x
  refine ⟨D.B j, inferInstance, inferInstance, I.map (algebraMap R (D.B j)), inferInstance,
    D.yFormalGlueData.ι j, hI.map _, ⟨y, hy⟩, inferInstance, ?_⟩
  rw [D.ι_yStructMap j, D.globalSectionsMap_yStructMapChart j]
  exact Ideal.le_comap_map

end AlgebraicGeometry.BothChartedFibreDatumXY

end
