import FormalSchemes.GeneralFibreProductExposeX
import FormalSchemes.CompletedTensorAwayInterchangePrLeft

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The structural morphism of the exposed affine-charted `X`

`FormalSchemes.GeneralFibreProductExposeX` builds the glued affine-charted formal scheme
`AlgebraicGeometry.AffineChartedFibreDatumX.xGlued` over `Spf R` from the algebra data of an
`AffineChartedFibreDatum` (charts `Spf(A i)`, overlap charts `basicOpenChart (I·A_i) (g i j)`,
transitions `awayCompletionTransition`). It did **not** build `X`'s structural morphism to the base.

This file delivers `AffineChartedFibreDatumX.xStructMap : X ⟶ Spf R`, gluing the per-chart affine
structural morphisms `Spf(algebraMap R (A i)) : Spf(A i) ⟶ Spf R` across the (arbitrary-index) cover
via `FormalScheme.GlueData.glueMorphisms`. It is the exposed-`X` analogue of the Tate-chain
structural morphism `AlgebraicGeometry.tateChainStructMap` (`FormalSchemes.TateChainStructMap`),
and it is the input `f = X ⟶ Spf R` that the cone identity `pr₁ ≫ f = pr₂ ≫ g` of the general
fibre product `X ×_{Spf R} Spf B` consumes (issue 316, Step 3; EGA I §10.7).

The overlap compatibility `glueMorphisms` consumes on each double overlap is the naturality square

`basicOpenChart (I·A_i) (g i j) ≫ structMapChart i =
  awayCompletionTransition (g i j) (g j i) (τ i j) ≫
    basicOpenChart (I·A_j) (g j i) ≫ structMapChart j`

(`AffineChartedFibreDatumX.xStructMap_naturality`). Unlike the Tate case — where the overlap
transition is only a *geometric* `Spf`-iso and intertwining the base needs a load-bearing ring
reconstruction — here `τ i j` is a genuine `R`-algebra isomorphism, so both sides collapse to a
single `locallyRingedSpaceMap` out of `Spf(A_i{1/g_ij})` whose underlying ring maps agree by
`AlgEquiv.commutes`: the transition fixes the image of the base `R`.

## Main definitions

* `AffineChartedFibreDatumX.xStructMapChart`: the per-chart structural morphism `Spf(A i) ⟶ Spf R`.
* `AffineChartedFibreDatumX.xStructMap_naturality`: the double-overlap compatibility square.
* `AffineChartedFibreDatumX.xStructMap`: the glued structural morphism `X ⟶ Spf R`.
* `AffineChartedFibreDatumX.ι_xStructMap`: it restricts to `xStructMapChart i` along each `ι i`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

namespace AffineChartedFibreDatumX

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable {B : Type u} [CommRing B] [Algebra R B]
variable (D : AffineChartedFibreDatumX R I hI B)

/-- **The per-chart structural morphism** `Spf(A i) ⟶ Spf R`, the map of formal spectra induced by
the `R`-algebra structure map `algebraMap R (A i)`, phrased over the ideal of definition
`I·A_i = I.map (algebraMap R (A i))`. -/
def xStructMapChart (i : D.J) :
    letI := D.commRing
    letI := D.algebra
    locallyRingedSpaceObj (I.map (algebraMap R (D.A i))) ⟶ locallyRingedSpaceObj I :=
  letI := D.commRing
  letI := D.algebra
  locallyRingedSpaceMap I (I.map (algebraMap R (D.A i))) (algebraMap R (D.A i)) Ideal.le_comap_map

/-- **The double-overlap compatibility square of the structural morphism.** For distinct charts
`i ≠ j`, the `(i,j)`-overlap chart followed by the structural morphism of chart `i` equals the
`X`-side transition `awayCompletionTransition (g i j) (g j i) (τ i j)` followed by the
`(j,i)`-overlap chart and the structural morphism of chart `j` — the datum `glueMorphisms` consumes
to glue `xStructMap` across the cover. Both sides collapse to a single `locallyRingedSpaceMap` out
of `Spf(A_i{1/g_ij})`, and the underlying ring maps agree because `(τ i j).symm` is an `R`-algebra
map (`AlgEquiv.commutes`): the transition fixes the image of the base `R`. -/
theorem xStructMap_naturality (i j : D.J) (h : i ≠ j) :
    letI := D.commRing
    letI := D.algebra
    basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i j) ≫ D.xStructMapChart i =
      awayCompletionTransition (D.g i j) (D.g j i) (D.τ i j h) ≫
        basicOpenChart (I.map (algebraMap R (D.A j))) (D.g j i) ≫ D.xStructMapChart j := by
  letI := D.commRing
  letI := D.algebra
  rw [xStructMapChart, xStructMapChart, basicOpenChart, basicOpenChart, awayCompletionTransition,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp (algebraMap R (D.A i))
        (awayCompletionHom (I.map (algebraMap R (D.A i))) (D.g i j))
        Ideal.le_comap_map (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp (algebraMap R (D.A j))
        (awayCompletionHom (I.map (algebraMap R (D.A j))) (D.g j i))
        Ideal.le_comap_map (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp
        ((awayCompletionHom (I.map (algebraMap R (D.A j))) (D.g j i)).comp (algebraMap R (D.A j)))
        (D.τ i j h).symm.toRingHom
        (le_comap_comp (algebraMap R (D.A j))
          (awayCompletionHom (I.map (algebraMap R (D.A j))) (D.g j i))
          Ideal.le_comap_map (le_comap_awayCompletionHom _ _))
        (awayCompletionTransition_le_comap (D.g i j) (D.g j i) (D.τ i j h)))]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  rw [awayCompletionHom_comp_algebraMap, awayCompletionHom_comp_algebraMap]
  exact RingHom.ext fun r => ((D.τ i j h).symm.commutes r).symm

/-- **The glued structural morphism of the exposed affine-charted `X`** `X ⟶ Spf R`, assembled from
the per-chart structural morphisms `xStructMapChart i : Spf(A i) ⟶ Spf R` via `glueMorphisms`. Off
the diagonal the overlap obligation is `xStructMap_naturality`; on the diagonal it collapses through
`GlueData.t_id`. -/
def xStructMap :
    D.xGlued.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  D.xFormalGlueData.glueMorphisms (fun i => D.xStructMapChart i) (by
    intro i j
    by_cases hij : i = j
    · -- diagonal: `t i i = 𝟙`, so both sides collapse to `f i i ≫ xStructMapChart`.
      subst hij
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · -- off-diagonal: unfold the `ofGlueData'` `if`-forms; the dite conditions are on `= : D.J`,
      -- so re-type the disequalities in `¬ Eq` form before rewriting.
      have hij' : ¬ @Eq D.J i j := hij
      have hji' : ¬ @Eq D.J j i := fun heq => hij heq.symm
      simp only [xFormalGlueData, xLrsGlueData, xGlueData', CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji', Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [D.xStructMap_naturality i j hij'])

/-- **The structural morphism restricts to `xStructMapChart i` along each glue inclusion.** -/
@[reassoc (attr := simp)]
theorem ι_xStructMap (i : D.J) :
    D.xFormalGlueData.ι i ≫ D.xStructMap = D.xStructMapChart i :=
  D.xFormalGlueData.ι_glueMorphisms _ _ i

end AffineChartedFibreDatumX

end AlgebraicGeometry
