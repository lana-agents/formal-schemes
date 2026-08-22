import FormalSchemes.TateTensorOverlapChartIso

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000

/-!
# The tensored Tate two-chart overlap is a single chart: the both-factor shape

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`, let
`A = R{x, y}/(x·y − q)` be the coordinate ring of the formal Tate annulus, and write
`C = A ⊗̂_R A`.

`FormalSchemes.TateTensorOverlapChartIso` (705a) identified the two presentations of each
**one-sided** overlap shape of `Spf A ×_{Spf R} Spf A` — merged basic open at `x + y` versus
coproduct of the charts at `x` and at `y`. This file does the remaining shape, where **both**
product coordinates differ:

```
Spf(A{1/(x+y)}^ ⊗̂_R A{1/(x+y)}^) ≅
  (Spf(A{1/x}^ ⊗̂ A{1/x}^) ⨿ Spf(A{1/x}^ ⊗̂ A{1/y}^)) ⨿
    (Spf(A{1/y}^ ⊗̂ A{1/x}^) ⨿ Spf(A{1/y}^ ⊗̂ A{1/y}^))
```

over `Spf C`. Together the two files close the overlap discrepancy between the generic
fibre-product datum of `AffineChartedFibreDatum` and `tateSelfProduct` (issue 705's step-0
report), which is what 705c's `tateFibreProductIso` needs.

## Route

Identical to 705a, and the four-fold nesting never has to be taken apart: both sides are open
immersions into `Spf C`, so `IsOpenImmersion.isoOfRangeEq` gives the isomorphism and both
factorisations from a range equality, and the range equality is a *distributive law* between the
two one-sided ones.

* the merged side's range is `D(inl (x+y)) ⊓ D(inr (x+y))`
  (`range_bothInterchangeOpenImmersion_base`);
* the coproduct side's range is the four-fold union of `D(inl a) ⊓ D(inr b)`
  (`range_bothFactorOverlapChart`), already assembled through `range_coprodDesc_base`;
* 705a's `selfProductBasicOpen_inl_add` / `_inr_add` rewrite each factor as a join, and
  `inf_sup_right` / `inf_sup_left` distribute — `TopologicalSpace.Opens` is a frame, so the
  distribution is available with no side conditions, and it produces exactly the nesting
  `((a ⊓ c) ⊔ (a ⊓ d)) ⊔ ((b ⊓ c) ⊔ (b ⊓ d))` that `bothFactorOverlapChart` was built with.

## Main definitions and results

* `AlgebraicGeometry.range_bothFactorOverlapChart_eq`: the two charts have the same range.
* `AlgebraicGeometry.tensorOverlapChartIsoBoth`, with `_hom_fac` and `_inv_fac`: the isomorphism,
  over `Spf C`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits FormalSpectrum
open CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- **The merged and the coproduct both-factor overlap charts have the same range.** The merged
side is the intersection `D(inl (x+y)) ⊓ D(inr (x+y))`; rewriting each factor by 705a's
`selfProductBasicOpen_inl_add` / `_inr_add` and distributing gives precisely the four-fold union
the coproduct chart covers. -/
theorem range_bothFactorOverlapChart_eq (hq : q ∈ I) (hI : I.FG) :
    Set.range (bothInterchangeOpenImmersion (A := annulusAlgebra R I q)
        (B := annulusAlgebra R I q) I (overlapX R I q + overlapY R I q)
        (overlapX R I q + overlapY R I q) hI).base =
      Set.range (bothFactorOverlapChart R I q hI).base := by
  rw [range_bothInterchangeOpenImmersion_base, range_bothFactorOverlapChart,
    selfProductBasicOpen_inl_add R I q hq, selfProductBasicOpen_inr_add R I q hq,
    inf_sup_right, inf_sup_left, inf_sup_left]
  rfl

/-- **The both-factor overlap of `Spf A ×_{Spf R} Spf A` is affine**: the four-fold coproduct of the
doubly-localised tensored charts is isomorphic to the single tensored chart at `(x+y, x+y)`.

The two-sided companion of `tensorOverlapChartIsoFirst`, built the same way — from a range
equality, so no ring-level splitting of `A{1/(x+y)}^ ⊗̂_R A{1/(x+y)}^` is needed or proved. -/
def tensorOverlapChartIsoBoth (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q))) ≅
      ((locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) ⨿
          locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) ⨿
        (locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) ⨿
          locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))))) :=
  haveI := isOpenImmersion_bothInterchangeOpenImmersion (A := annulusAlgebra R I q)
    (B := annulusAlgebra R I q) I (overlapX R I q + overlapY R I q)
    (overlapX R I q + overlapY R I q) hI
  haveI := isOpenImmersion_bothFactorOverlapChart R I q hq hI
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _
    (range_bothFactorOverlapChart_eq R I q hq hI)

/-- **The both-factor identification is a morphism over `Spf C`**: composing it with the four-fold
coproduct of the doubly-localised charts recovers the single merged chart. -/
@[reassoc (attr := simp)]
theorem tensorOverlapChartIsoBoth_hom_fac (hq : q ∈ I) (hI : I.FG) :
    (tensorOverlapChartIsoBoth R I q hq hI).hom ≫ bothFactorOverlapChart R I q hI =
      bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
        (overlapX R I q + overlapY R I q) (overlapX R I q + overlapY R I q) hI := by
  haveI := isOpenImmersion_bothInterchangeOpenImmersion (A := annulusAlgebra R I q)
    (B := annulusAlgebra R I q) I (overlapX R I q + overlapY R I q)
    (overlapX R I q + overlapY R I q) hI
  haveI := isOpenImmersion_bothFactorOverlapChart R I q hq hI
  exact LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _
    (range_bothFactorOverlapChart_eq R I q hq hI)

/-- The reverse factorisation of `tensorOverlapChartIsoBoth_hom_fac`, shipped because the glue-datum
comparison of 705c rewrites in both directions. -/
@[reassoc (attr := simp)]
theorem tensorOverlapChartIsoBoth_inv_fac (hq : q ∈ I) (hI : I.FG) :
    (tensorOverlapChartIsoBoth R I q hq hI).inv ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapX R I q + overlapY R I q) (overlapX R I q + overlapY R I q) hI =
      bothFactorOverlapChart R I q hI := by
  haveI := isOpenImmersion_bothInterchangeOpenImmersion (A := annulusAlgebra R I q)
    (B := annulusAlgebra R I q) I (overlapX R I q + overlapY R I q)
    (overlapX R I q + overlapY R I q) hI
  haveI := isOpenImmersion_bothFactorOverlapChart R I q hq hI
  exact LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_inv_fac _ _
    (range_bothFactorOverlapChart_eq R I q hq hI)

end AlgebraicGeometry

end
