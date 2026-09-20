import FormalSchemes.TateSeparated

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The mixed-chart glue relations of the Tate self-fibre product

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`, and let
`A = R{x, y}/(x·y − q)`. The self fibre product `𝔈_q ×_{Spf R} 𝔈_q = tateSelfProductInv` is glued
from four copies of `Spf(A ⊗̂_R A)` indexed by `ULift (Bool × Bool)`.

`TateSeparated` extracts the glue relation for the *both-factors-differing* pair
`(false,false)`–`(true,true)` (`tateSelfProduct_both_glue_condition_inv`), the one the glued
diagonal `Δ` is built from. This file extracts the four remaining relations involving a **mixed**
chart `(b, ¬b)`:

* the two *second-factor-differing* pairs `(b, ¬b)`–`(b, b)`, whose overlap chart is
  `secondFactorOverlapChart` and whose transition is `tateSelfProductRightTransitionInv`;
* the two *first-factor-differing* pairs `(b, ¬b)`–`(¬b, ¬b)`, whose overlap chart is
  `firstFactorOverlapChart` and whose transition is `tateSelfProductFirstTransitionInv`.

These are the relations that transport the diagonal, which lives in the charts `(c, c)`, into a
mixed chart; they are the categorical input for the mixed-chart preimage computation of
`range Δ.base` (issue 503b/424-ii, EGA I §10.15).

## Main results

* `AlgebraicGeometry.tateSelfProduct_second_glue_condition_inv_ft`,
  `..._second_glue_condition_inv_tf`: the two second-factor-differing relations.
* `AlgebraicGeometry.tateSelfProduct_first_glue_condition_inv_ft`,
  `..._first_glue_condition_inv_tf`: the two first-factor-differing relations.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- **Second-factor glue relation, `(false, true)`–`(false, false)`.** The two charts differ only in
the second factor, so their overlap chart is `secondFactorOverlapChart` and the transition is the
second-factor inversion transition. Extracted from
`LocallyRingedSpace.GlueData.glue_condition`, mirroring
`tateSelfProduct_both_glue_condition_inv`. -/
theorem tateSelfProduct_second_glue_condition_inv_ft (hq : q ∈ I) (hI : I.FG) :
    secondFactorOverlapChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, true)⟩ =
      (tateSelfProductRightTransitionInv R I q hI).hom ≫ secondFactorOverlapChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ := by
  have hij : ({ down := (false, true) } : ULift.{u} (Bool × Bool)) ≠
      { down := (false, false) } := by decide
  exact CategoryTheory.GlueData.ofGlueData'_f_comp_of (tateSelfProductGlueData'Inv R I q hq hI) _
    (fun i j => ((tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.glue_condition i j).symm)
    ⟨(false, true)⟩ ⟨(false, false)⟩ hij

omit [IsNoetherianRing R] in
/-- **Second-factor glue relation, `(true, false)`–`(true, true)`.** -/
theorem tateSelfProduct_second_glue_condition_inv_tf (hq : q ∈ I) (hI : I.FG) :
    secondFactorOverlapChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, false)⟩ =
      (tateSelfProductRightTransitionInv R I q hI).hom ≫ secondFactorOverlapChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
  have hij : ({ down := (true, false) } : ULift.{u} (Bool × Bool)) ≠ { down := (true, true) } := by
    decide
  exact CategoryTheory.GlueData.ofGlueData'_f_comp_of (tateSelfProductGlueData'Inv R I q hq hI) _
    (fun i j => ((tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.glue_condition i j).symm)
    ⟨(true, false)⟩ ⟨(true, true)⟩ hij

omit [IsNoetherianRing R] in
/-- **First-factor glue relation, `(false, true)`–`(true, true)`.** The two charts differ only in
the first factor, so their overlap chart is `firstFactorOverlapChart` and the transition is the
first-factor inversion transition. -/
theorem tateSelfProduct_first_glue_condition_inv_ft (hq : q ∈ I) (hI : I.FG) :
    firstFactorOverlapChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, true)⟩ =
      (tateSelfProductFirstTransitionInv R I q hI).hom ≫ firstFactorOverlapChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
  have hij : ({ down := (false, true) } : ULift.{u} (Bool × Bool)) ≠ { down := (true, true) } := by
    decide
  exact CategoryTheory.GlueData.ofGlueData'_f_comp_of (tateSelfProductGlueData'Inv R I q hq hI) _
    (fun i j => ((tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.glue_condition i j).symm)
    ⟨(false, true)⟩ ⟨(true, true)⟩ hij

omit [IsNoetherianRing R] in
/-- **First-factor glue relation, `(true, false)`–`(false, false)`.** -/
theorem tateSelfProduct_first_glue_condition_inv_tf (hq : q ∈ I) (hI : I.FG) :
    firstFactorOverlapChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, false)⟩ =
      (tateSelfProductFirstTransitionInv R I q hI).hom ≫ firstFactorOverlapChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ := by
  have hij : ({ down := (true, false) } : ULift.{u} (Bool × Bool)) ≠
      { down := (false, false) } := by decide
  exact CategoryTheory.GlueData.ofGlueData'_f_comp_of (tateSelfProductGlueData'Inv R I q hq hI) _
    (fun i j => ((tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.glue_condition i j).symm)
    ⟨(true, false)⟩ ⟨(false, false)⟩ hij

end AlgebraicGeometry
