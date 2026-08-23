import FormalSchemes.ChartedDatumGlueMorphisms
import FormalSchemes.GeneralFibreProductBothOverlapRange
import FormalSchemes.GlueMorphismsOpenImmersion

set_option linter.style.header false

/-!
# When a charted datum's glued morphism is an open immersion

`AlgebraicGeometry.AffineChartedFibreDatumX.glueChartMorphisms`
(`FormalSchemes.ChartedDatumGlueMorphisms`, issue 860) glues a family of chart morphisms
`k i : Spf (A i) ⟶ Y` into a morphism `xGlued ⟶ Y`. This file transports the open-immersion
criterion of `FormalSchemes.GlueMorphismsOpenImmersion` from the raw glue datum down to the charted
datum, where the overlap objects are named `Spf (A i{1/g_ij})` rather than
`toLocallyRingedSpaceGlueData.V (i, j)`.

## What the transport costs

Exactly one thing: `CategoryTheory.GlueData.ofGlueData'` pads the diagonal of a `GlueData'`, so the
glue datum's overlap immersion `f i j` is not `basicOpenChart (I·A_i) (g i j)` on the nose but that
morphism preceded by an `eqToHom` — and on the diagonal it is an `eqToHom` alone. An `eqToHom` is an
isomorphism, so neither changes a range (`range_eqToHom_comp_base`), and the two lemmas below record
the resulting range identities. The `dite` conditions live at `D.J` while the glue datum indexes by
`D.xFormalGlueData.toLocallyRingedSpaceGlueData.J`, so the disequality has to be re-typed as
`¬ @Eq D.J i j` before `dif_neg` fires — the same step, for the same reason, that
`glueChartMorphisms` itself performs.

The hypothesis a consumer must supply is therefore stated in the datum's own spelling, and only for
`i ≠ j`: on the diagonal the condition is vacuous, since the overlap immersion is an isomorphism.

## Main results

* `AlgebraicGeometry.AffineChartedFibreDatumX.range_xGlueData_f_comp_of_ne` and
  `range_xGlueData_f_comp_self`: the two range identities above.
* `AlgebraicGeometry.AffineChartedFibreDatumX.range_glueChartMorphisms`: the range of the glued
  morphism is the union of the ranges of the chart morphisms.
* `AlgebraicGeometry.AffineChartedFibreDatumX.isOpenImmersion_glueChartMorphisms`: **the criterion**
  — chart morphisms that are open immersions and meet only along `D(g_ij)` glue to an open
  immersion.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6, §10.15.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum Topology

universe u

namespace AlgebraicGeometry

namespace AffineChartedFibreDatumX

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable {B : Type u} [CommRing B] [Algebra R B]
variable (D : AffineChartedFibreDatumX R I hI B) {Y : LocallyRingedSpace.{u}}

/-! ### The glue datum's overlap immersion, in the datum's own spelling -/

/-- Off the diagonal, the glue datum's overlap immersion is `basicOpenChart (I·A_i) (g i j)`
preceded by an `eqToHom`, so composing with any `kk` leaves the range unchanged. -/
theorem range_xGlueData_f_comp_of_ne (i j : D.J) (hij : i ≠ j)
    (kk : letI := D.commRing; letI := D.algebra;
      locallyRingedSpaceObj (I.map (algebraMap R (D.A i))) ⟶ Y) :
    letI := D.commRing; letI := D.algebra
    Set.range (D.xFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.f i j ≫ kk).base =
      Set.range (basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i j) ≫ kk).base := by
  letI := D.commRing
  letI := D.algebra
  have hij' : ¬ @Eq D.J i j := hij
  simp only [xFormalGlueData, xLrsGlueData, xGlueData', CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', dif_neg hij', Category.assoc]
  exact range_eqToHom_comp_base _ _

/-- On the diagonal, the glue datum's overlap immersion is an `eqToHom`, so composing with any `kk`
gives back the range of `kk`. -/
theorem range_xGlueData_f_comp_self (i : D.J)
    (kk : letI := D.commRing; letI := D.algebra;
      locallyRingedSpaceObj (I.map (algebraMap R (D.A i))) ⟶ Y) :
    letI := D.commRing; letI := D.algebra
    Set.range (D.xFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.f i i ≫ kk).base =
      Set.range kk.base := by
  letI := D.commRing
  letI := D.algebra
  simp only [xFormalGlueData, xLrsGlueData, xGlueData', CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', dif_pos trivial]
  exact range_eqToHom_comp_base _ _

/-! ### The glued morphism -/

variable (k : letI := D.commRing; letI := D.algebra; letI := D.topology; letI := D.isAdic;
    ∀ i : D.J, locallyRingedSpaceObj (I.map (algebraMap R (D.A i))) ⟶ Y)
  (hk : letI := D.commRing; letI := D.algebra; letI := D.topology; letI := D.isAdic;
    ∀ (i j : D.J) (h : i ≠ j),
      basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i j) ≫ k i =
        awayCompletionTransition (D.g i j) (D.g j i) (D.τ i j h) ≫
          basicOpenChart (I.map (algebraMap R (D.A j))) (D.g j i) ≫ k j)

/-- **The range of the glued morphism is the union of the ranges of the chart morphisms.** -/
theorem range_glueChartMorphisms :
    Set.range (D.glueChartMorphisms k hk).base = ⋃ i, Set.range (k i).base :=
  D.xFormalGlueData.range_glueMorphisms k _

/-- **A family of chart morphisms that are open immersions and meet only along the double overlaps
glues to an open immersion.** The hypothesis `hmeet` is required only off the diagonal; on it the
glue datum's overlap immersion is an isomorphism, so the condition is automatic. -/
theorem isOpenImmersion_glueChartMorphisms
    (hoi : letI := D.commRing; letI := D.algebra;
      ∀ i, LocallyRingedSpace.IsOpenImmersion (k i))
    (hmeet : letI := D.commRing; letI := D.algebra;
      ∀ (i j : D.J), i ≠ j → Set.range (k i).base ∩ Set.range (k j).base ⊆
        Set.range (basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i j) ≫ k i).base) :
    LocallyRingedSpace.IsOpenImmersion (D.glueChartMorphisms k hk) := by
  letI := D.commRing
  letI := D.algebra
  refine D.xFormalGlueData.isOpenImmersion_glueMorphisms k _ hoi fun i j => ?_
  by_cases hij : i = j
  · subst hij
    rw [D.range_xGlueData_f_comp_self i (k i)]
    exact Set.inter_subset_left
  · rw [D.range_xGlueData_f_comp_of_ne i j hij (k i)]
    exact hmeet i j hij

end AffineChartedFibreDatumX

end AlgebraicGeometry

end
