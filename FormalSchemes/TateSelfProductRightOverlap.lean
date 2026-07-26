import FormalSchemes.TateSelfProductOverlap
import FormalSchemes.CompletedTensorAwayInterchangeRight

set_option linter.style.header false
-- The completed-tensor interchange morphisms range over the nested localization/completion
-- towers of the completed tensor product, which are slow for the elaborator and the kernel;
-- raise the budgets (matching `TateSelfProductOverlap.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The second-factor base-changed overlap chart of the Tate self-fibre-product

Companion to `FormalSchemes.TateSelfProductOverlap`, which assembles the overlap chart of the self
fibre-product `𝔈_q ×_{Spf R} 𝔈_q` for the chart shape where the *first* factor differs. This file
delivers the mirror datum where the *second* factor differs and the first is held fixed at the full
annulus.

Fix an adic base `(R, I)` with `q ∈ I` and finitely generated `I`, and let
`A = annulusAlgebra R I q = R{x, y}/(x·y − q)` be the coordinate ring of the formal Tate annulus.
With `C = A ⊗̂_R A` the completed tensor product (coordinate ring of `Spf A ×_{Spf R} Spf A`), the
two coordinates `x, y ∈ A` give rise, via the *second-factor* completed-tensor / away-localization
interchange (`CompletedTensorAwayInterchange.rightInterchangeOpenImmersion`), to two open immersions

* `rightInterchangeOpenImmersion I overlapX hI : Spf(A ⊗̂_R (A{1/x})) ⟶ Spf C`, image `D(1⊗x)`, and
* `rightInterchangeOpenImmersion I overlapY hI : Spf(A ⊗̂_R (A{1/y})) ⟶ Spf C`, image `D(1⊗y)`,

both landing in the *same* target `Spf C`. Exactly as for the first-factor overlap
(`FormalSchemes.TateSelfProductOverlap`), the relation `x·y = q` with `q ∈ I` topologically
nilpotent forces the images `D(1⊗x) = D(inr x)` and `D(1⊗y) = D(inr y)` to be disjoint, so the
combined chart

`coprod.desc (rightInterchangeOpenImmersion I overlapX hI)
    (rightInterchangeOpenImmersion I overlapY hI)`

is an open immersion onto `D(1⊗x) ∪ D(1⊗y) ⊆ Spf C`. This is the `V`/`f` overlap datum (for the
second-factor-differing chart shape) that the eventual four-chart glue of `𝔈_q ×_{Spf R} 𝔈_q`
consumes, alongside the first-factor datum of `TateSelfProductOverlap`.

## Main results

* `selfProductInr_mul`: `inr(x) · inr(y) = algebraMap R C q` in `C = A ⊗̂_R A`.
* `selfProductRightOverlap_basicOpen_disjoint`: `D(inr x) ⊓ D(inr y) = ⊥` in `Spf C`, when `q ∈ I`.
* `selfProductRightOverlapChart_range_disjoint`: the underlying-space ranges of the two
  second-factor interchange overlap charts are disjoint.
* `isOpenImmersion_tateSelfProductRightOverlapChart`: the combined coproduct chart into `Spf C` is
  an open immersion.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.13.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The coordinate ring of the formal Tate annulus, base for the self fibre-product. -/
private abbrev A : Type u := annulusAlgebra R I q

/-- The completed tensor product `A ⊗̂_R A`, coordinate ring of `Spf A ×_{Spf R} Spf A`. -/
private abbrev C : Type u := CompletedTensorProduct R I (A R I q) (A R I q)

/-- **The second-factor analogue of `selfProductInl_mul`.** In `C = A ⊗̂_R A` the product of the
images of the two overlap coordinates `x, y ∈ A` under `inr` is the image of the Tate parameter:
`inr(x) · inr(y) = algebraMap R C q`. This uses that `inr` is an `R`-algebra homomorphism
(multiplicative, and commuting with `algebraMap R`), together with the annulus relation
`x · y = q`. -/
theorem selfProductInr_mul :
    CompletedTensorProduct.inr R I (A R I q) (A R I q) (overlapX R I q) *
        CompletedTensorProduct.inr R I (A R I q) (A R I q) (overlapY R I q)
      = algebraMap R (C R I q) q := by
  rw [← map_mul, overlapX_mul_overlapY, AlgHom.commutes]

/-- **The doubly-invertible locus of the second-factor base-changed Tate annulus overlap is empty.**
When the Tate parameter `q` is topologically nilpotent (`q ∈ I`), the two basic opens `D(inr x)` and
`D(inr y)` of `Spf C` (`C = A ⊗̂_R A`) are disjoint, because `(1⊗x) · (1⊗y) = q` maps to `0` in the
residue ring of the ideal of definition of `C`. Second-factor analogue of
`selfProductOverlap_basicOpen_disjoint`. -/
theorem selfProductRightOverlap_basicOpen_disjoint (hq : q ∈ I) :
    basicOpen (CompletedTensorProduct.idealOfDefinition R I (A R I q) (A R I q))
        (CompletedTensorProduct.inr R I (A R I q) (A R I q) (overlapX R I q))
      ⊓ basicOpen (CompletedTensorProduct.idealOfDefinition R I (A R I q) (A R I q))
          (CompletedTensorProduct.inr R I (A R I q) (A R I q) (overlapY R I q)) = ⊥ := by
  rw [← basicOpen_mul, selfProductInr_mul, basicOpen, mk_algebraMap_q_eq_zero_tensor R I q hq]
  exact PrimeSpectrum.basicOpen_zero

/-- **The two second-factor interchange overlap charts have disjoint ranges.** The underlying-space
images of `CompletedTensorAwayInterchange.rightInterchangeOpenImmersion I overlapX hI` (the locus
`D(inr x)`) and `... overlapY hI` (the locus `D(inr y)`), both landing in `Spf C`
(`C = A ⊗̂_R A`), are disjoint when `q ∈ I`. This is the geometric input needed to assemble the
second-factor base-changed overlap chart of the self fibre-product `𝔈_q ×_{Spf R} 𝔈_q` as an open
immersion. -/
theorem selfProductRightOverlapChart_range_disjoint (hq : q ∈ I) (hI : I.FG) :
    Disjoint
      (Set.range (CompletedTensorAwayInterchange.rightInterchangeOpenImmersion
        (A := A R I q) I (overlapX R I q) hI).base)
      (Set.range (CompletedTensorAwayInterchange.rightInterchangeOpenImmersion
        (A := A R I q) I (overlapY R I q) hI).base) := by
  rw [CompletedTensorAwayInterchange.range_rightInterchangeOpenImmersion_base,
    CompletedTensorAwayInterchange.range_rightInterchangeOpenImmersion_base]
  refine Set.disjoint_iff_inter_eq_empty.mpr ?_
  rw [← TopologicalSpace.Opens.coe_inf, selfProductRightOverlap_basicOpen_disjoint R I q hq,
    TopologicalSpace.Opens.coe_bot]

/-- **The combined second-factor base-changed overlap chart is an open immersion.** The coproduct
`coprod.desc` of the two second-factor interchange overlap charts
`rightInterchangeOpenImmersion I overlapX hI` (image `D(inr x)`) and `... overlapY hI`
(image `D(inr y)`), both into `Spf C` (`C = A ⊗̂_R A`), is an open immersion of locally ringed
spaces, because the two images are disjoint. This is the `V`/`f` overlap datum (for the
second-factor-differing chart shape) feeding the eventual four-chart glue of the self fibre-product
`𝔈_q ×_{Spf R} 𝔈_q`. -/
theorem isOpenImmersion_tateSelfProductRightOverlapChart (hq : q ∈ I) (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion
      (coprod.desc
        (CompletedTensorAwayInterchange.rightInterchangeOpenImmersion (A := A R I q) I
          (overlapX R I q) hI)
        (CompletedTensorAwayInterchange.rightInterchangeOpenImmersion (A := A R I q) I
          (overlapY R I q) hI)) := by
  haveI := CompletedTensorAwayInterchange.isOpenImmersion_rightInterchangeOpenImmersion
    (A := A R I q) I (overlapX R I q) hI
  haveI := CompletedTensorAwayInterchange.isOpenImmersion_rightInterchangeOpenImmersion
    (A := A R I q) I (overlapY R I q) hI
  exact LocallyRingedSpace.IsOpenImmersion.coprodDesc _ _
    (selfProductRightOverlapChart_range_disjoint R I q hq hI)

end AlgebraicGeometry
