import FormalSchemes.BasicOpenDisjointUnion
import FormalSchemes.OpenImmersionIsoOfRangeEq
import FormalSchemes.TateSelfProductTripleOverlap

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000

/-!
# The tensored Tate two-chart overlap is a single chart

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`, let
`A = R{x, y}/(x·y − q)` be the coordinate ring of the formal Tate annulus, and write
`C = A ⊗̂_R A` for the coordinate ring of `Spf A ×_{Spf R} Spf A`.

671 (`FormalSchemes.TateOverlapChartIso`) proved that the two presentations of the *two-chart
overlap* of `𝔈_q` agree,
`tateOverlapChartIso : Spf A{1/(x+y)}^ ≅ Spf A{1/x}^ ⨿ Spf A{1/y}^`, as an isomorphism over
`Spf A`. This file proves the same statement **tensored with a second factor**: for each of the two
one-sided overlap shapes of `Spf A ×_{Spf R} Spf A`,

```
Spf(A{1/(x+y)}^ ⊗̂_R A) ≅ Spf(A{1/x}^ ⊗̂_R A) ⨿ Spf(A{1/y}^ ⊗̂_R A)
Spf(A ⊗̂_R A{1/(x+y)}^) ≅ Spf(A ⊗̂_R A{1/x}^) ⨿ Spf(A ⊗̂_R A{1/y}^)
```

each over `Spf C`.

## Why this is needed

The two four-chart presentations of `𝔈_q ×_{Spf R} 𝔈_q` disagree at exactly this point (issue 705's
step-0 report). `tateSelfProduct` (`FormalSchemes.TateSelfProductObject`) was built before 601a and
presents every overlap as a **coproduct**, `D(x) ⊔ D(y)` tensored with the other factor; the
generic fibre-product datum of `AffineChartedFibreDatum` presents it as the **single** basic open
`D(x + y)`, because that is the shape `AffineChartedFibreDatum.g` demands and 601a supplies. The
charts and the indexing of the two presentations match; the overlaps are the whole discrepancy, and
these isomorphisms are what closes it.

## Route

The same one as 671, and for the same reason: both sides are open immersions into `Spf C`, so
`LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq` produces the isomorphism *and* both
factorisations from a **range equality** — no ring-level splitting of `A{1/(x+y)}^ ⊗̂_R A` is
needed, and none is proved here.

The range equality is two rewrites on each side. The merged side's range is `D(inl (x + y))`
(`range_interchangeOpenImmersion_base`); the coproduct side's is `D(inl x) ∪ D(inl y)`
(`range_firstFactorOverlapChart`, already assembled through `range_coprodDesc_base`); and the two
agree by the generic `FormalSpectrum.basicOpen_add_of_mul_eq_zero` — `D(f + g) = D(f) ⊔ D(g)`
whenever `f · g` vanishes modulo the ideal of definition — whose hypothesis here is
`inl x · inl y = q` (`selfProductInl_mul`, and `selfProductInr_mul` on the other side) together
with `q ∈ I` (`mk_algebraMap_q_eq_zero_tensor`). That is 601a's argument, transported along `inl`
and along `inr`.

## Main definitions and results

* `AlgebraicGeometry.selfProductBasicOpen_inl_add` / `_inr_add`:
  `D(inl (x+y)) = D(inl x) ⊔ D(inl y)` in `Spf C`, and its second-factor mirror.
* `AlgebraicGeometry.range_firstFactorOverlapChart_eq` / `range_secondFactorOverlapChart_eq`: the
  merged and coproduct charts of each one-sided shape have the same range.
* `AlgebraicGeometry.tensorOverlapChartIsoFirst` / `tensorOverlapChartIsoSecond`, with
  `_hom_fac` and `_inv_fac`: the isomorphisms, over `Spf C`.

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

/-! ### The overlap locus of each one-sided shape is a single basic open -/

/-- **The first-factor overlap locus of `Spf C` is a single basic open**: `D(x⊗1)` and `D(y⊗1)`
are disjoint (`selfProductOverlap_basicOpen_disjoint`) and their union is cut out by `inl (x + y)`.
This is 601a's `annulusOverlap_basicOpen_add` transported along `inl`. -/
theorem selfProductBasicOpen_inl_add (hq : q ∈ I) :
    basicOpen (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q))
        (CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)
          (overlapX R I q + overlapY R I q)) =
      basicOpen (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
          (annulusAlgebra R I q))
          (CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)
            (overlapX R I q)) ⊔
        basicOpen (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
            (annulusAlgebra R I q))
            (CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)
              (overlapY R I q)) := by
  rw [map_add]
  refine FormalSpectrum.basicOpen_add_of_mul_eq_zero _ _ _ ?_
  rw [selfProductInl_mul]
  exact mk_algebraMap_q_eq_zero_tensor R I q hq

/-- **The second-factor overlap locus of `Spf C` is a single basic open**, the `inr` mirror of
`selfProductBasicOpen_inl_add`. -/
theorem selfProductBasicOpen_inr_add (hq : q ∈ I) :
    basicOpen (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q))
        (CompletedTensorProduct.inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)
          (overlapX R I q + overlapY R I q)) =
      basicOpen (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
          (annulusAlgebra R I q))
          (CompletedTensorProduct.inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)
            (overlapX R I q)) ⊔
        basicOpen (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
            (annulusAlgebra R I q))
            (CompletedTensorProduct.inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)
              (overlapY R I q)) := by
  rw [map_add]
  refine FormalSpectrum.basicOpen_add_of_mul_eq_zero _ _ _ ?_
  rw [selfProductInr_mul]
  exact mk_algebraMap_q_eq_zero_tensor R I q hq

/-! ### The two range equalities -/

/-- **The merged and the coproduct first-factor overlap charts have the same range**, namely
`D(inl x) ∪ D(inl y) = D(inl (x + y)) ⊆ Spf C`. This is the sole hypothesis of
`tensorOverlapChartIsoFirst`. -/
theorem range_firstFactorOverlapChart_eq (hq : q ∈ I) (hI : I.FG) :
    Set.range (interchangeOpenImmersion (B := annulusAlgebra R I q) I
        (overlapX R I q + overlapY R I q) hI).base =
      Set.range (firstFactorOverlapChart R I q hI).base := by
  rw [range_interchangeOpenImmersion_base, range_firstFactorOverlapChart,
    selfProductBasicOpen_inl_add R I q hq]
  rfl

/-- **The merged and the coproduct second-factor overlap charts have the same range.** -/
theorem range_secondFactorOverlapChart_eq (hq : q ∈ I) (hI : I.FG) :
    Set.range (rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I
        (overlapX R I q + overlapY R I q) hI).base =
      Set.range (secondFactorOverlapChart R I q hI).base := by
  rw [range_rightInterchangeOpenImmersion_base, range_secondFactorOverlapChart,
    selfProductBasicOpen_inr_add R I q hq]
  rfl

/-! ### The two identifications -/

/-- **The first-factor overlap of `Spf A ×_{Spf R} Spf A` is affine**: the coproduct
`Spf(A{1/x}^ ⊗̂_R A) ⨿ Spf(A{1/y}^ ⊗̂_R A)` of the two tensored overlap charts is isomorphic to the
single tensored chart `Spf(A{1/(x+y)}^ ⊗̂_R A)`.

This is 671's `tateOverlapChartIso` tensored with a second factor, and it is built the same way:
both sides are open immersions into `Spf C` with the same range
(`range_firstFactorOverlapChart_eq`), so `IsOpenImmersion.isoOfRangeEq` supplies the isomorphism
together with the two factorisations below. In particular nothing here needs — or proves — a
splitting of `A{1/(x+y)}^ ⊗̂_R A` as a ring. -/
def tensorOverlapChartIsoFirst (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q)) (annulusAlgebra R I q)) ≅
      (locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
          (annulusAlgebra R I q)) ⨿
        locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
          (annulusAlgebra R I q))) :=
  haveI := isOpenImmersion_interchangeOpenImmersion (B := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI
  haveI := isOpenImmersion_firstFactorOverlapChart R I q hq hI
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _
    (range_firstFactorOverlapChart_eq R I q hq hI)

/-- **The first-factor identification is a morphism over `Spf C`**: composing it with the coproduct
of the two tensored overlap charts recovers the single merged chart. -/
@[reassoc (attr := simp)]
theorem tensorOverlapChartIsoFirst_hom_fac (hq : q ∈ I) (hI : I.FG) :
    (tensorOverlapChartIsoFirst R I q hq hI).hom ≫ firstFactorOverlapChart R I q hI =
      interchangeOpenImmersion (B := annulusAlgebra R I q) I
        (overlapX R I q + overlapY R I q) hI := by
  haveI := isOpenImmersion_interchangeOpenImmersion (B := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI
  haveI := isOpenImmersion_firstFactorOverlapChart R I q hq hI
  exact LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _
    (range_firstFactorOverlapChart_eq R I q hq hI)

/-- The reverse factorisation of `tensorOverlapChartIsoFirst_hom_fac`. Shipped alongside because the
glue-datum comparison of 705c rewrites in both directions. -/
@[reassoc (attr := simp)]
theorem tensorOverlapChartIsoFirst_inv_fac (hq : q ∈ I) (hI : I.FG) :
    (tensorOverlapChartIsoFirst R I q hq hI).inv ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I
          (overlapX R I q + overlapY R I q) hI =
      firstFactorOverlapChart R I q hI := by
  haveI := isOpenImmersion_interchangeOpenImmersion (B := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI
  haveI := isOpenImmersion_firstFactorOverlapChart R I q hq hI
  exact LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_inv_fac _ _
    (range_firstFactorOverlapChart_eq R I q hq hI)

/-- **The second-factor overlap of `Spf A ×_{Spf R} Spf A` is affine**, the mirror of
`tensorOverlapChartIsoFirst`. -/
def tensorOverlapChartIsoSecond (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q))) ≅
      (locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) ⨿
        locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) :=
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI
  haveI := isOpenImmersion_secondFactorOverlapChart R I q hq hI
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _
    (range_secondFactorOverlapChart_eq R I q hq hI)

/-- **The second-factor identification is a morphism over `Spf C`.** -/
@[reassoc (attr := simp)]
theorem tensorOverlapChartIsoSecond_hom_fac (hq : q ∈ I) (hI : I.FG) :
    (tensorOverlapChartIsoSecond R I q hq hI).hom ≫ secondFactorOverlapChart R I q hI =
      rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I
        (overlapX R I q + overlapY R I q) hI := by
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI
  haveI := isOpenImmersion_secondFactorOverlapChart R I q hq hI
  exact LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _
    (range_secondFactorOverlapChart_eq R I q hq hI)

/-- The reverse factorisation of `tensorOverlapChartIsoSecond_hom_fac`. -/
@[reassoc (attr := simp)]
theorem tensorOverlapChartIsoSecond_inv_fac (hq : q ∈ I) (hI : I.FG) :
    (tensorOverlapChartIsoSecond R I q hq hI).inv ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I
          (overlapX R I q + overlapY R I q) hI =
      secondFactorOverlapChart R I q hI := by
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI
  haveI := isOpenImmersion_secondFactorOverlapChart R I q hq hI
  exact LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_inv_fac _ _
    (range_secondFactorOverlapChart_eq R I q hq hI)

end AlgebraicGeometry

end
