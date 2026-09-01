import FormalSchemes.GeneralFibreProductExposeX
import FormalSchemes.GeneralFibreProductExposeXStructMap
import FormalSchemes.GlueMorphisms

set_option linter.style.header false

/-!
# Gluing a family of chart morphisms out of an affine-charted formal scheme

`AlgebraicGeometry.AffineChartedFibreDatumX.xGlued` (`FormalSchemes.GeneralFibreProductExposeX`)
is the formal scheme glued from the affine charts `Spf (A i)` of a charted datum along the
basic-open overlaps `Spf (A i{1/g i j})` and the transitions `τ i j`. Building a morphism *out* of
it means supplying one morphism per chart and checking they agree on the double overlaps.

`FormalSchemes.GeneralFibreProductExposeXStructMap` already does this once, for the structural
morphism `xGlued ⟶ Spf R`. This file abstracts that assembly over the target: the same three-line
`GlueData.ofGlueData'` bookkeeping serves any target, and no consumer should have to repeat it.

## The bookkeeping, and why it is worth factoring out

`FormalScheme.GlueData.glueMorphisms` asks for compatibility at *every* pair `(i, j)`, including
`i = j`, whereas a charted datum's transitions are only defined for `i ≠ j` — `xGlueData'` is a
`CategoryTheory.GlueData'`, and `GlueData.ofGlueData'` fills the diagonal with `eqToHom`s guarded
by `dite`s. Discharging that costs a `by_cases`, a `GlueData.t_id` collapse on the diagonal, and
off it a `simp only` unfolding four definitions to expose the `dite`s.

Two details bite every time and are settled here once:

* the disequalities must be re-typed as `¬ @Eq D.J i j` before `dif_neg` will fire, because the
  `dite` conditions live at `D.J` while `glueMorphisms` indexes by
  `D.xFormalGlueData.toLocallyRingedSpaceGlueData.J`, which is `D.J` only by unfolding;
* the hypothesis and the chart family both need the datum's own instances in scope, so both carry
  the `letI` prologue in their *types* — the idiom `xStructMapChart` already uses.

## Main definitions and results

* `AlgebraicGeometry.AffineChartedFibreDatumX.glueChartMorphisms`: **a family of morphisms out of
  the charts, agreeing on the double overlaps, glues to a morphism out of `xGlued`.**
* `AlgebraicGeometry.AffineChartedFibreDatumX.ι_glueChartMorphisms`: it restricts to the `i`-th
  chart morphism along each glue inclusion.
* `AlgebraicGeometry.AffineChartedFibreDatumX.xStructMap_eq_glueChartMorphisms`: the validation —
  the structural morphism *is* this combinator at the chart structural maps, by `rfl`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

namespace AffineChartedFibreDatumX

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable {B : Type u} [CommRing B] [Algebra R B]
variable (D : AffineChartedFibreDatumX R I hI B) {Y : LocallyRingedSpace.{u}}

/-- **Gluing a family of chart morphisms out of `xGlued`.** Given a morphism `k i : Spf (A i) ⟶ Y`
for each chart, agreeing on every double overlap in the sense of `hk`, the induced morphism
`xGlued ⟶ Y`.

This is the assembly of `AffineChartedFibreDatumX.xStructMap`
(`FormalSchemes.GeneralFibreProductExposeXStructMap`) with its target `Spf R` abstracted away;
`xStructMap` is the instance at `k := xStructMapChart` and `hk := xStructMap_naturality`.

The overlap obligation `FormalScheme.GlueData.glueMorphisms` consumes is over *all* pairs, while
`hk` only speaks of `i ≠ j`: on the diagonal the glue transition is the identity
(`GlueData.t_id`), so both sides collapse without touching `hk`. -/
def glueChartMorphisms
    (k : letI := D.commRing; letI := D.algebra; letI := D.topology; letI := D.isAdic;
      ∀ i : D.J, locallyRingedSpaceObj (I.map (algebraMap R (D.A i))) ⟶ Y)
    (hk : letI := D.commRing; letI := D.algebra; letI := D.topology; letI := D.isAdic;
      ∀ (i j : D.J) (h : i ≠ j),
        basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i j) ≫ k i =
          awayCompletionTransition (D.g i j) (D.g j i) (D.τ i j h) ≫
            basicOpenChart (I.map (algebraMap R (D.A j))) (D.g j i) ≫ k j) :
    D.xGlued.toLocallyRingedSpace ⟶ Y :=
  D.xFormalGlueData.glueMorphisms k (by
    intro i j
    by_cases hij : i = j
    · -- diagonal: `t i i = 𝟙`, so both sides collapse to `f i i ≫ k i`.
      subst hij
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · -- off-diagonal: unfold the `GlueData.ofGlueData'` `dite`-forms; the conditions are on
      -- `= : D.J`, so re-type the disequalities in `¬ @Eq D.J` form before `dif_neg` will fire.
      have hij' : ¬ @Eq D.J i j := hij
      have hji' : ¬ @Eq D.J j i := fun heq => hij heq.symm
      simp only [xFormalGlueData, xLrsGlueData, xGlueData', CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji', Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [hk i j hij'])

/-- **The glued morphism restricts to `k i` along each glue inclusion.** -/
@[reassoc (attr := simp)]
theorem ι_glueChartMorphisms
    (k : letI := D.commRing; letI := D.algebra; letI := D.topology; letI := D.isAdic;
      ∀ i : D.J, locallyRingedSpaceObj (I.map (algebraMap R (D.A i))) ⟶ Y)
    (hk : letI := D.commRing; letI := D.algebra; letI := D.topology; letI := D.isAdic;
      ∀ (i j : D.J) (h : i ≠ j),
        basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i j) ≫ k i =
          awayCompletionTransition (D.g i j) (D.g j i) (D.τ i j h) ≫
            basicOpenChart (I.map (algebraMap R (D.A j))) (D.g j i) ≫ k j)
    (i : D.J) :
    D.xFormalGlueData.ι i ≫ D.glueChartMorphisms k hk = k i :=
  D.xFormalGlueData.ι_glueMorphisms _ _ i

/-! ### Validation: the structural morphism is an instance -/

/-- **`xStructMap` is this combinator**, at `k := xStructMapChart` and `hk := xStructMap_naturality`
(`FormalSchemes.GeneralFibreProductExposeXStructMap`). It holds by `rfl`, which is the check that
the abstraction is faithful rather than merely parallel: had the diagonal bookkeeping been
discharged differently the two would only be propositionally equal.

Stated rather than used: rerouting `xStructMap`'s definition through the combinator would be a
non-additive change to a module that a large part of the tree sits above, and it buys nothing that
this equation does not already give a consumer. -/
theorem xStructMap_eq_glueChartMorphisms :
    D.xStructMap =
      D.glueChartMorphisms (fun i => D.xStructMapChart i)
        (fun i j h => D.xStructMap_naturality i j h) :=
  rfl

end AffineChartedFibreDatumX

end AlgebraicGeometry

end
