import FormalSchemes.CompletedTensorAwayInterchangeBothPullback
import FormalSchemes.TateTensorOverlapChartIsoBoth
import FormalSchemes.TateTensorOverlapSummandAffine

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000

/-!
# The four summands of the tensored both-factor Tate overlap

The two-sided companion of `FormalSchemes.TateTensorOverlapSummandAffine`, split off from it because
of build cost: the objects here are four-fold coproducts of doubly-localised completed tensor
products, and every statement about them is an order of magnitude more expensive to elaborate.

739 (`FormalSchemes.TateTensorOverlapChartIsoBoth`) identified the both-factor overlap of
`Spf A ×_{Spf R} Spf A` in its two presentations,

```
tensorOverlapChartIsoBoth :
    Spf(A{1/(x+y)}^ ⊗̂_R A{1/(x+y)}^) ≅ (d_xx ⨿ d_xy) ⨿ (d_yx ⨿ d_yy) ,
    d_ab = Spf(A{1/a}^ ⊗̂_R A{1/b}^) ,
```

through `IsOpenImmersion.isoOfRangeEq`, which says nothing about what the maps do. This file names
the four summand inclusions — `mapSpf` of the corresponding pair of projections of 644's splitting —
and proves that they *are* the summand inclusions, by the mono argument of 703.

## Main definitions and results

* `AlgebraicGeometry.tensorOverlapSummandXXBoth` and its three siblings `XY`, `YX`, `YY`, with the
  laws `…_comp` placing each over the merged chart at `(x + y, x + y)`.
* `AlgebraicGeometry.coprod_inl_inl_comp_tensorOverlapChartIsoBoth_inv` and its three siblings:
  **the headline**.

## Build cost, measured

Two attribute forms that 703 uses one level down do not survive at this size, and both failures are
silent-looking stack overflows rather than Lean errors:

* `@[reassoc …]` on a headline overflows the elaborator's stack on its own;
* `@[simp]` overflows *cumulatively* — one such lemma in the simp set is fine, a second one
  elaborated afterwards in the same module is not.

So the four headline lemmas are shipped **bare**. There is also no packaged `coprod.desc` form; see
the section note at the end for the measurement.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits FormalSpectrum
open CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The both-factor overlap: the four summand inclusions

`tensorOverlapChartIsoBoth` identifies `Spf(A{1/(x+y)}^ ⊗̂_R A{1/(x+y)}^)` with the four-fold
coproduct `(d_xx ⨿ d_xy) ⨿ (d_yx ⨿ d_yy)`. Each summand inclusion is `mapSpf` of a pair of
projections of the splitting; the nesting is the one `bothFactorOverlapChart` is built with. -/

/-- **The `(x, x)`-summand of the tensored both-factor overlap, as an affine
morphism.** -/
def tensorOverlapSummandXXBoth (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) ⟶
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q))) :=
  CompletedTensorProduct.mapSpf hI (annulusTensorProjXₐ R I q hq) (annulusTensorProjXₐ R I q hq)

/-- **The `(x, x)`-summand lies over the merged both-factor chart at `(x + y, x + y)`.** -/
@[reassoc]
theorem tensorOverlapSummandXXBoth_comp (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandXXBoth R I q hq hI ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapX R I q + overlapY R I q) (overlapX R I q + overlapY R I q) hI =
      bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
        (overlapX R I q) (overlapX R I q) hI := by
  rw [tensorOverlapSummandXXBoth, bothInterchangeOpenImmersion_eq_mapSpf,
    bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
    annulusTensorProjXₐ_comp]

/-- **The `(x, y)`-summand of the tensored both-factor overlap, as an affine
morphism.** -/
def tensorOverlapSummandXYBoth (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) ⟶
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q))) :=
  CompletedTensorProduct.mapSpf hI (annulusTensorProjXₐ R I q hq) (annulusTensorProjYₐ R I q hq)

/-- **The `(x, y)`-summand lies over the merged both-factor chart at `(x + y, x + y)`.** -/
@[reassoc]
theorem tensorOverlapSummandXYBoth_comp (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandXYBoth R I q hq hI ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapX R I q + overlapY R I q) (overlapX R I q + overlapY R I q) hI =
      bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
        (overlapX R I q) (overlapY R I q) hI := by
  rw [tensorOverlapSummandXYBoth, bothInterchangeOpenImmersion_eq_mapSpf,
    bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
    annulusTensorProjXₐ_comp, annulusTensorProjYₐ_comp]

/-- **The `(y, x)`-summand of the tensored both-factor overlap, as an affine
morphism.** -/
def tensorOverlapSummandYXBoth (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) ⟶
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q))) :=
  CompletedTensorProduct.mapSpf hI (annulusTensorProjYₐ R I q hq) (annulusTensorProjXₐ R I q hq)

/-- **The `(y, x)`-summand lies over the merged both-factor chart at `(x + y, x + y)`.** -/
@[reassoc]
theorem tensorOverlapSummandYXBoth_comp (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandYXBoth R I q hq hI ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapX R I q + overlapY R I q) (overlapX R I q + overlapY R I q) hI =
      bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
        (overlapY R I q) (overlapX R I q) hI := by
  rw [tensorOverlapSummandYXBoth, bothInterchangeOpenImmersion_eq_mapSpf,
    bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
    annulusTensorProjYₐ_comp, annulusTensorProjXₐ_comp]

/-- **The `(y, y)`-summand of the tensored both-factor overlap, as an affine
morphism.** -/
def tensorOverlapSummandYYBoth (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) ⟶
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q))) :=
  CompletedTensorProduct.mapSpf hI (annulusTensorProjYₐ R I q hq) (annulusTensorProjYₐ R I q hq)

/-- **The `(y, y)`-summand lies over the merged both-factor chart at `(x + y, x + y)`.** -/
@[reassoc]
theorem tensorOverlapSummandYYBoth_comp (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandYYBoth R I q hq hI ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapX R I q + overlapY R I q) (overlapX R I q + overlapY R I q) hI =
      bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
        (overlapY R I q) (overlapY R I q) hI := by
  rw [tensorOverlapSummandYYBoth, bothInterchangeOpenImmersion_eq_mapSpf,
    bothInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
    annulusTensorProjYₐ_comp]

/-- **The `(x, x)`-summand inclusion of the tensored both-factor overlap is `mapSpf`
of the corresponding pair of projections.**

Build-cost note: unlike 703's un-tensored analogues this is shipped **bare**, with neither
`reassoc` nor `simp`. The left-hand side is a doubly-nested coproduct inclusion into the `inv` of a
four-fold coproduct isomorphism of completed tensor products, and at that size both attributes
overflow the elaborator's stack: `reassoc` on its own, and `simp` cumulatively — one such lemma in
the simp set is fine, a second one elaborated afterwards in the same module is not. Bare, the four
elaborate in ~45 s each. Rewrite with them explicitly and reassociate with `Category.assoc`. -/
theorem coprod_inl_inl_comp_tensorOverlapChartIsoBoth_inv (hq : q ∈ I) (hI : I.FG) :
    coprod.inl ≫ coprod.inl ≫ (tensorOverlapChartIsoBoth R I q hq hI).inv =
      tensorOverlapSummandXXBoth R I q hq hI := by
  haveI := isOpenImmersion_bothInterchangeOpenImmersion (A := annulusAlgebra R I q)
    (B := annulusAlgebra R I q) I (overlapX R I q + overlapY R I q)
    (overlapX R I q + overlapY R I q) hI
  refine (cancel_mono (bothInterchangeOpenImmersion (A := annulusAlgebra R I q)
    (B := annulusAlgebra R I q) I (overlapX R I q + overlapY R I q)
    (overlapX R I q + overlapY R I q) hI)).mp ?_
  rw [Category.assoc, Category.assoc, tensorOverlapChartIsoBoth_inv_fac,
    bothFactorOverlapChart, coprod.inl_desc, coprod.inl_desc]
  exact (tensorOverlapSummandXXBoth_comp R I q hq hI).symm

/-- **The `(x, y)`-summand inclusion of the tensored both-factor overlap is `mapSpf`
of the corresponding pair of projections.**

Build-cost note: unlike 703's un-tensored analogues this is shipped **bare**, with neither
`reassoc` nor `simp`. The left-hand side is a doubly-nested coproduct inclusion into the `inv` of a
four-fold coproduct isomorphism of completed tensor products, and at that size both attributes
overflow the elaborator's stack: `reassoc` on its own, and `simp` cumulatively — one such lemma in
the simp set is fine, a second one elaborated afterwards in the same module is not. Bare, the four
elaborate in ~45 s each. Rewrite with them explicitly and reassociate with `Category.assoc`. -/
theorem coprod_inr_inl_comp_tensorOverlapChartIsoBoth_inv (hq : q ∈ I) (hI : I.FG) :
    coprod.inr ≫ coprod.inl ≫ (tensorOverlapChartIsoBoth R I q hq hI).inv =
      tensorOverlapSummandXYBoth R I q hq hI := by
  haveI := isOpenImmersion_bothInterchangeOpenImmersion (A := annulusAlgebra R I q)
    (B := annulusAlgebra R I q) I (overlapX R I q + overlapY R I q)
    (overlapX R I q + overlapY R I q) hI
  refine (cancel_mono (bothInterchangeOpenImmersion (A := annulusAlgebra R I q)
    (B := annulusAlgebra R I q) I (overlapX R I q + overlapY R I q)
    (overlapX R I q + overlapY R I q) hI)).mp ?_
  rw [Category.assoc, Category.assoc, tensorOverlapChartIsoBoth_inv_fac,
    bothFactorOverlapChart, coprod.inl_desc, coprod.inr_desc]
  exact (tensorOverlapSummandXYBoth_comp R I q hq hI).symm

/-- **The `(y, x)`-summand inclusion of the tensored both-factor overlap is `mapSpf`
of the corresponding pair of projections.**

Build-cost note: unlike 703's un-tensored analogues this is shipped **bare**, with neither
`reassoc` nor `simp`. The left-hand side is a doubly-nested coproduct inclusion into the `inv` of a
four-fold coproduct isomorphism of completed tensor products, and at that size both attributes
overflow the elaborator's stack: `reassoc` on its own, and `simp` cumulatively — one such lemma in
the simp set is fine, a second one elaborated afterwards in the same module is not. Bare, the four
elaborate in ~45 s each. Rewrite with them explicitly and reassociate with `Category.assoc`. -/
theorem coprod_inl_inr_comp_tensorOverlapChartIsoBoth_inv (hq : q ∈ I) (hI : I.FG) :
    coprod.inl ≫ coprod.inr ≫ (tensorOverlapChartIsoBoth R I q hq hI).inv =
      tensorOverlapSummandYXBoth R I q hq hI := by
  haveI := isOpenImmersion_bothInterchangeOpenImmersion (A := annulusAlgebra R I q)
    (B := annulusAlgebra R I q) I (overlapX R I q + overlapY R I q)
    (overlapX R I q + overlapY R I q) hI
  refine (cancel_mono (bothInterchangeOpenImmersion (A := annulusAlgebra R I q)
    (B := annulusAlgebra R I q) I (overlapX R I q + overlapY R I q)
    (overlapX R I q + overlapY R I q) hI)).mp ?_
  rw [Category.assoc, Category.assoc, tensorOverlapChartIsoBoth_inv_fac,
    bothFactorOverlapChart, coprod.inr_desc, coprod.inl_desc]
  exact (tensorOverlapSummandYXBoth_comp R I q hq hI).symm

/-- **The `(y, y)`-summand inclusion of the tensored both-factor overlap is `mapSpf`
of the corresponding pair of projections.**

Build-cost note: unlike 703's un-tensored analogues this is shipped **bare**, with neither
`reassoc` nor `simp`. The left-hand side is a doubly-nested coproduct inclusion into the `inv` of a
four-fold coproduct isomorphism of completed tensor products, and at that size both attributes
overflow the elaborator's stack: `reassoc` on its own, and `simp` cumulatively — one such lemma in
the simp set is fine, a second one elaborated afterwards in the same module is not. Bare, the four
elaborate in ~45 s each. Rewrite with them explicitly and reassociate with `Category.assoc`. -/
theorem coprod_inr_inr_comp_tensorOverlapChartIsoBoth_inv (hq : q ∈ I) (hI : I.FG) :
    coprod.inr ≫ coprod.inr ≫ (tensorOverlapChartIsoBoth R I q hq hI).inv =
      tensorOverlapSummandYYBoth R I q hq hI := by
  haveI := isOpenImmersion_bothInterchangeOpenImmersion (A := annulusAlgebra R I q)
    (B := annulusAlgebra R I q) I (overlapX R I q + overlapY R I q)
    (overlapX R I q + overlapY R I q) hI
  refine (cancel_mono (bothInterchangeOpenImmersion (A := annulusAlgebra R I q)
    (B := annulusAlgebra R I q) I (overlapX R I q + overlapY R I q)
    (overlapX R I q + overlapY R I q) hI)).mp ?_
  rw [Category.assoc, Category.assoc, tensorOverlapChartIsoBoth_inv_fac,
    bothFactorOverlapChart, coprod.inr_desc, coprod.inr_desc]
  exact (tensorOverlapSummandYYBoth_comp R I q hq hI).symm

/-! ### No packaged `coprod.desc` form here — measured, not skipped

The one-sided sections ship `coprod_desc_tensorOverlapSummandFirst` / `…Second`, packaging the four
summand identifications as `coprod.desc … = …inv`. The four-fold analogue

```
coprod.desc (coprod.desc XX XY) (coprod.desc YX YY) = (tensorOverlapChartIsoBoth …).inv
```

is **deliberately absent**. Its *statement* does not elaborate: building the nested coproduct object
from the four completed-tensor summands and unifying it with the isomorphism's codomain exceeds
`maxHeartbeats 3200000` in `whnf`, before any proof is attempted. Three proof routes were tried
(nested `coprod.hom_ext`, `cancel_mono` + `coprod.desc_comp`, and unfolding `bothFactorOverlapChart`
first) and all three die at the same place, which is the header, not the tactic block.

Nothing is lost: the four `coprod_in?_in?_comp_tensorOverlapChartIsoBoth_inv` lemmas above determine
the inverse completely, and a consumer that needs the packaged form should use `coprod.hom_ext`
twice at the point of use, where the coproduct object is already fixed by the surrounding goal and
so costs nothing to elaborate. -/

end AlgebraicGeometry

end
