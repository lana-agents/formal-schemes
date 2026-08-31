import FormalSchemes.ChartedCompletionDatum
import FormalSchemes.ChartedSchemeDatumDesc

set_option linter.style.header false

/-!
# The canonical morphism `X_{/Y} ⟶ X` at an arbitrary index (EGA I, 10.8)

`FormalSchemes/CompletionTwoPatchToScheme.lean` builds `completionTwoPatchToScheme`, the morphism
from the glued completion of a **two**-chart scheme to that scheme, on `ULift Bool`. This file is
its arbitrary-index version: for a `AlgebraicGeometry.ChartedCompletionDatum`
(`FormalSchemes.ChartedCompletionDatum`) the glued completion maps to the glued scheme, chart by
chart by the affine `formalCompletion.toSpec`.

Both objects come from the same datum — that is the point of packaging the localization data once
— so the two sides of the overlap obligation are the two glue conditions, one on each side, and
nothing has to be transported between two unrelated presentations.

## The `Spec`-side glue condition

`AlgebraicGeometry.ChartedSchemeDatum.specAwayMap_comp_specι` is
`AlgebraicGeometry.specTwoPatch_glue` at an arbitrary index type: the affine charts of `specGlued`
agree over their overlaps. It is `CategoryTheory.GlueData.glue_condition` with the
`CategoryTheory.GlueData.ofGlueData'` bookkeeping cancelled off both sides. It lives in
`FormalSchemes.ChartedSchemeDatumDesc`, next to the other statements about mapping out of
`specGlued`; what this file adds is
`AlgebraicGeometry.ChartedCompletionDatum.specAwayMap_comp_specι`, the same lemma read at a
completion datum through `toChartedSchemeDatum`.

## Main definitions and results

* `AlgebraicGeometry.ChartedCompletionDatum.specAwayMap_comp_specι`: the ambient scheme's glue
  condition, at an arbitrary index, read at a completion datum.
* `AlgebraicGeometry.ChartedCompletionDatum.toScheme_overlapCompat`: the per-chart morphisms
  `Spf (C i)^ ⟶ Spec (C i) ⟶ X` agree over every overlap.
* `AlgebraicGeometry.ChartedCompletionDatum.toScheme`: the canonical morphism `X_{/Y} ⟶ X`, with
  `..toScheme_eq_desc`, the computation rule `..completionι_comp_toScheme`, and
  `..toScheme_unique`.

## What is *not* proved

* **No universal property.** `toScheme_unique` says the morphism is the only one restricting to the
  affine `formalCompletion.toSpec`s chart by chart; the affine case of the universal property of
  `formalCompletion.toSpec` is not on master, so nothing stronger is available.
* No closed-embedding or support statement for the arbitrary-index morphism. The two-patch line has
  those (`FormalSchemes.CompletionTwoPatchClosed`, `FormalSchemes.CompletionTwoPatchSupport`) and
  generalising them is separate work.
* Nothing promotes `specGlued` to `AlgebraicGeometry.Scheme`.

## The comparison with `AffineChartedFibreDatumX`, measured

The natural question is whether a `ChartedCompletionDatum` yields an
`AlgebraicGeometry.AffineChartedFibreDatumX` (`FormalSchemes.GeneralFibreProductExposeX`) by
completing each chart, so that `completionGlued` would be an
`AlgebraicGeometry.AffineChartedFibreDatumX.xGlued`. **It does not, and two independent things
obstruct it** — read off that structure's fields, not guessed:

1. **One base ring, one ideal.** `AffineChartedFibreDatum` fixes `R`, `I : Ideal R` and `hI : I.FG`
   as parameters, asks every chart for `[Algebra R (A i)]`, and never carries a per-chart ideal at
   all: the ideal of the `i`-th chart is *spelled* `I.map (algebraMap R (A i))` throughout. A
   `ChartedCompletionDatum` has an independent `K i : Ideal (C i)` in an unrelated ring, which is
   exactly what `FormalSchemes.ChartedSchemeDatum`'s docstring introduces the datum shape to allow
   — the projective line completed at a closed point wants `K₀ = (x)` in `k[x]` and `K₁ = ⊤` in
   `k[y]`, and no single `(R, I)` produces that pair.
2. **A second base and a whole extra cocycle.** `AffineChartedFibreDatum` also fixes `B` with
   `[Algebra R B]` and carries `t'`, `t_fac` and `cocycle` at the level of
   `CompletedTensorAwayInterchange.interchangeOpenImmersion` — the *fibre-product* side — as well
   as `AffineChartedFibreDatumX.xt'`, `AffineChartedFibreDatumX.xt_fac` and
   `AffineChartedFibreDatumX.xcocycle`, which are `X`'s own. None of that is determined by a
   `ChartedCompletionDatum`; producing it would mean inventing `B` and its interchange cocycle.

So the two lines meet only over a common base, and even there the fibre-product datum is new input.
This is the same measurement 1343 made in the other direction (`AffineChartedFibreDatumX` cannot
supply the ambient scheme, because its transition lives at the away *completion*), and the two
together are why the `Spec` side needed a datum of its own.

`FormalSchemes/CompletionAsChartedGlued.lean`'s stale opening paragraph is **not** touched by this
file and stays for the next editor of it.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace ChartedCompletionDatum

variable (D : ChartedCompletionDatum.{u})

/-- **The affine charts of the glued ambient scheme agree over their overlaps**, read at this
datum. -/
theorem specAwayMap_comp_specι (i j : D.J) (h : i ≠ j) :
    specAwayMap (D.g i j) ≫ D.specι i =
      (specGlueIso (D.g i j) (D.g j i) (D.θ i j h)).hom ≫ specAwayMap (D.g j i) ≫ D.specι j :=
  D.toChartedSchemeDatum.specAwayMap_comp_specι i j h

/-- **The overlap compatibility of the per-chart morphisms `Spf (C i)^ ⟶ Spec (C i) ⟶ X`.** This is
the hypothesis `completionDesc` consumes, and it is where the two sides of the datum meet: the
completion side contributes `formalCompletion.basicOpenImmersion_comp_toSpec` and
`formalCompletion.map_comp_toSpec`, the scheme side `specAwayMap_comp_specι`. -/
theorem toScheme_overlapCompat (i j : D.J) (h : i ≠ j) :
    D.overlapImmersion i j ≫
        (formalCompletion.toSpec (D.C i) (D.K i) (D.hK i) ≫ D.specι i) =
      (D.overlapIso i j h).hom ≫ D.overlapImmersion j i ≫
        (formalCompletion.toSpec (D.C j) (D.K j) (D.hK j) ≫ D.specι j) := by
  rw [← Category.assoc, formalCompletion.basicOpenImmersion_comp_toSpec, Category.assoc,
    D.specAwayMap_comp_specι i j h]
  rw [← Category.assoc (D.overlapImmersion j i), formalCompletion.basicOpenImmersion_comp_toSpec]
  have hg : (D.overlapIso i j h).hom =
      (formalCompletion.map ((D.hK j).map _) ((D.hK i).map _) (D.θ i j h).symm.toRingHom
        (D.hθ_symm i j h).le).toLRSHom := rfl
  rw [hg]
  simp only [Category.assoc]
  rw [reassoc_of% (formalCompletion.map_comp_toSpec ((D.hK j).map _) ((D.hK i).map _)
    (D.θ i j h).symm.toRingHom (D.hθ_symm i j h).le)]
  rfl

/-- **The canonical morphism from the glued completion to the glued scheme** (EGA I, 10.8):
`X_{/Y} ⟶ X` for the scheme glued from the charts `Spec (C i)` along `θ`, completed along the
closed subset glued from the `V (K i)`. It is the descent of the affine
`formalCompletion.toSpec`s. -/
def toScheme : D.completionGlued.toLocallyRingedSpace ⟶ D.specGlued :=
  D.completionDesc (fun i => formalCompletion.toSpec (D.C i) (D.K i) (D.hK i) ≫ D.specι i)
    D.toScheme_overlapCompat

/-- **The canonical morphism is a descent**, definitionally, so that the general results about
`completionDesc` apply to it by rewriting rather than by unfolding a `def`. -/
theorem toScheme_eq_desc :
    D.toScheme =
      D.completionDesc (fun i => formalCompletion.toSpec (D.C i) (D.K i) (D.hK i) ≫ D.specι i)
        D.toScheme_overlapCompat :=
  rfl

/-- **The computation rule**: on the `i`-th chart the canonical morphism is the affine
`formalCompletion.toSpec` followed by the `i`-th chart of the glued scheme. This is what every
consumer cites; the descent itself should never be unfolded downstream. -/
theorem completionι_comp_toScheme (i : D.J) :
    D.completionι i ≫ D.toScheme =
      formalCompletion.toSpec (D.C i) (D.K i) (D.hK i) ≫ D.specι i :=
  D.completionι_comp_desc _ _ i

/-- **Uniqueness**: the canonical morphism is the only one restricting to the affine
`formalCompletion.toSpec`s chart by chart. -/
theorem toScheme_unique (f : D.completionGlued.toLocallyRingedSpace ⟶ D.specGlued)
    (hf : ∀ i : D.J, D.completionι i ≫ f =
      formalCompletion.toSpec (D.C i) (D.K i) (D.hK i) ≫ D.specι i) :
    f = D.toScheme :=
  D.completionGlued_hom_ext fun i => (hf i).trans (D.completionι_comp_toScheme i).symm

end ChartedCompletionDatum

end AlgebraicGeometry

end
