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
* `AlgebraicGeometry.coprod_desc_tensorOverlapSummandBoth`: the packaged form
  `coprod.desc (coprod.desc XX XY) (coprod.desc YX YY) = (tensorOverlapChartIsoBoth …).inv`, which
  is what 705c consumes, with its two row halves.

## Build cost, measured

Two attribute forms that 703 uses one level down do not survive at this size, and both failures are
silent-looking stack overflows rather than Lean errors:

* `@[reassoc …]` on a headline overflows the elaborator's stack on its own;
* `@[simp]` overflows *cumulatively* — one such lemma in the simp set is fine, a second one
  elaborated afterwards in the same module is not.

So the four headline lemmas are shipped **bare**. A third cost of the same kind — an inline nested
`coprod.hom_ext` re-elaborating the four-fold coproduct object once per branch — shapes the proof of
the packaged form; see the section note at the end.

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
`reassoc` nor `simp`. The left-hand side is a doubly-nested coproduct inclusion into the `Iso.inv`
of a four-fold coproduct isomorphism of completed tensor products, and at that size both attributes
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
`reassoc` nor `simp`. The left-hand side is a doubly-nested coproduct inclusion into the `Iso.inv`
of a four-fold coproduct isomorphism of completed tensor products, and at that size both attributes
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
`reassoc` nor `simp`. The left-hand side is a doubly-nested coproduct inclusion into the `Iso.inv`
of a four-fold coproduct isomorphism of completed tensor products, and at that size both attributes
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
`reassoc` nor `simp`. The left-hand side is a doubly-nested coproduct inclusion into the `Iso.inv`
of a four-fold coproduct isomorphism of completed tensor products, and at that size both attributes
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

/-! ### The packaged `coprod.desc` form

The one-sided sections of `FormalSchemes.TateTensorOverlapSummandAffine` ship
`coprod_desc_tensorOverlapSummandFirst` / `…Second`, packaging their summand identifications as
`coprod.desc … = …inv`. This is the four-fold analogue, and it is the shape 705c's `coprod.hom_ext`
consumes.

Build-cost note, because the shape of the proof is forced and not a matter of taste. The
*statement* is cheap — it elaborates in about 8 s. What is not cheap is proving it with the two
`coprod.hom_ext`s **nested inline**, one inside each branch of the other: that re-elaborates the
four-fold coproduct object separately in every branch, and the fourth branch times out at `whnf` at
`maxHeartbeats 3200000` (the first three do close). Splitting the two halves out as the top-level
lemmas below, and reaching them with `exact`, pins each coproduct object once and takes the whole
group to about 26 s.

This is the same discipline as the note on the four headline lemmas above: at this size, never let a
four-fold coproduct of completed tensor products be re-elaborated inside a tactic branch. -/

/-- **The left half of the packaged form**: the `x`-row of the both-factor overlap. -/
theorem coprod_desc_tensorOverlapSummandXBoth (hq : q ∈ I) (hI : I.FG) :
    coprod.desc (tensorOverlapSummandXXBoth R I q hq hI)
        (tensorOverlapSummandXYBoth R I q hq hI) =
      coprod.inl ≫ (tensorOverlapChartIsoBoth R I q hq hI).inv := by
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc]
    exact (coprod_inl_inl_comp_tensorOverlapChartIsoBoth_inv R I q hq hI).symm
  · rw [coprod.inr_desc]
    exact (coprod_inr_inl_comp_tensorOverlapChartIsoBoth_inv R I q hq hI).symm

/-- **The right half of the packaged form**: the `y`-row of the both-factor overlap. -/
theorem coprod_desc_tensorOverlapSummandYBoth (hq : q ∈ I) (hI : I.FG) :
    coprod.desc (tensorOverlapSummandYXBoth R I q hq hI)
        (tensorOverlapSummandYYBoth R I q hq hI) =
      coprod.inr ≫ (tensorOverlapChartIsoBoth R I q hq hI).inv := by
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc]
    exact (coprod_inl_inr_comp_tensorOverlapChartIsoBoth_inv R I q hq hI).symm
  · rw [coprod.inr_desc]
    exact (coprod_inr_inr_comp_tensorOverlapChartIsoBoth_inv R I q hq hI).symm

/-- **The packaged form**: the inverse of the tensored both-factor identification is the four-fold
coproduct of the affine summand maps, nested as `bothFactorOverlapChart` nests them. -/
theorem coprod_desc_tensorOverlapSummandBoth (hq : q ∈ I) (hI : I.FG) :
    coprod.desc (coprod.desc (tensorOverlapSummandXXBoth R I q hq hI)
          (tensorOverlapSummandXYBoth R I q hq hI))
        (coprod.desc (tensorOverlapSummandYXBoth R I q hq hI)
          (tensorOverlapSummandYYBoth R I q hq hI)) =
      (tensorOverlapChartIsoBoth R I q hq hI).inv := by
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc]
    exact coprod_desc_tensorOverlapSummandXBoth R I q hq hI
  · rw [coprod.inr_desc]
    exact coprod_desc_tensorOverlapSummandYBoth R I q hq hI

end AlgebraicGeometry

end
