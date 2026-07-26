import FormalSchemes.TateOverlapDisjoint
import FormalSchemes.CompletedTensorAwayInterchangeSpf
import FormalSchemes.CoproductOpenImmersion

set_option linter.style.header false
-- The completed-tensor interchange morphisms range over the nested localization/completion
-- towers of the completed tensor product, which are slow for the elaborator and the kernel;
-- raise the budgets (matching `CompletedTensorAwayInterchangeSpf.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The base-changed overlap chart of the Tate self-fibre-product

Fix an adic base `(R, I)` with `q ∈ I` (the Tate parameter is topologically nilpotent) and finitely
generated `I`, and let `A = annulusAlgebra R I q = R{x, y}/(x·y − q)` be the coordinate ring of the
formal Tate annulus. This file assembles the **base-changed overlap chart** of the self
fibre-product `𝔈_q ×_{Spf R} 𝔈_q`: the piece of the eventual four-chart glue datum where the *first*
factor's chart differs (`D(x)` vs `D(y)`) and the second factor is held fixed at the full annulus.

Concretely, with `C = A ⊗̂_R A` the completed tensor product of the annulus algebra with itself
(coordinate ring of `Spf A ×_{Spf R} Spf A`), the two coordinates `x, y ∈ A` give rise, via the
completed-tensor / away-localization interchange (`CompletedTensorAwayInterchange`), to two open
immersions

* `interchangeOpenImmersion I overlapX hI : Spf((A{1/x}) ⊗̂_R A) ⟶ Spf C`, image `D(x⊗1)`, and
* `interchangeOpenImmersion I overlapY hI : Spf((A{1/y}) ⊗̂_R A) ⟶ Spf C`, image `D(y⊗1)`,

both landing in the *same* target `Spf C`. Exactly as for the plain annulus overlap
(`FormalSchemes.TateOverlapDisjoint`), the relation `x·y = q` with `q ∈ I` topologically nilpotent
forces the images `D(x⊗1)` and `D(y⊗1)` to be disjoint, so the combined chart

`coprod.desc (interchangeOpenImmersion I overlapX hI) (interchangeOpenImmersion I overlapY hI)
    : Spf((A{1/x}) ⊗̂_R A) ⨿ Spf((A{1/y}) ⊗̂_R A) ⟶ Spf C`

is an open immersion onto `D(x⊗1) ∪ D(y⊗1) ⊆ Spf C`. This is the `V`/`f` overlap datum (for the
one-factor-differing chart shape) that the eventual four-chart glue of `𝔈_q ×_{Spf R} 𝔈_q` consumes.

## Main results

* `selfProductInl_mul`: `inl(x) · inl(y) = algebraMap R C q` in `C = A ⊗̂_R A`.
* `mk_algebraMap_q_eq_zero_tensor`: the image of `algebraMap R C q` vanishes in the residue ring of
  the ideal of definition of `C`, when `q ∈ I`.
* `selfProductOverlap_basicOpen_disjoint`: `D(x⊗1) ⊓ D(y⊗1) = ⊥` in `Spf C`, when `q ∈ I`.
* `selfProductOverlapChart_range_disjoint`: the underlying-space ranges of the two interchange
  overlap charts are disjoint.
* `isOpenImmersion_tateSelfProductOverlapChart`: the combined coproduct chart into `Spf C` is an
  open immersion.

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

/-- **The self-product analogue of `overlapX_mul_overlapY`.** In `C = A ⊗̂_R A` the product of the
images of the two overlap coordinates `x, y ∈ A` under `inl` is the image of the Tate parameter:
`inl(x) · inl(y) = algebraMap R C q`. This uses that `inl` is an `R`-algebra homomorphism
(multiplicative, and commuting with `algebraMap R`), together with the annulus relation
`x · y = q`. -/
theorem selfProductInl_mul :
    CompletedTensorProduct.inl R I (A R I q) (A R I q) (overlapX R I q) *
        CompletedTensorProduct.inl R I (A R I q) (A R I q) (overlapY R I q)
      = algebraMap R (C R I q) q := by
  rw [← map_mul, overlapX_mul_overlapY, AlgHom.commutes]

/-- The image of the Tate parameter `q` in the residue ring of the ideal of definition of
`C = A ⊗̂_R A` vanishes when `q ∈ I`, because `idealOfDefinition R I A A = I.map (algebraMap R C)`
is the extension of `I` and `q ∈ I`. Analogue of `mk_algebraMap_q_eq_zero`. -/
theorem mk_algebraMap_q_eq_zero_tensor (hq : q ∈ I) :
    Ideal.Quotient.mk (CompletedTensorProduct.idealOfDefinition R I (A R I q) (A R I q))
        (algebraMap R (C R I q) q) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, CompletedTensorProduct.idealOfDefinition_eq_map]
  exact Ideal.mem_map_of_mem _ hq

/-- **The doubly-invertible locus of the base-changed Tate annulus overlap is empty.** When the
Tate parameter `q` is topologically nilpotent (`q ∈ I`), the two basic opens `D(x⊗1)` and `D(y⊗1)`
of `Spf C` (`C = A ⊗̂_R A`) are disjoint, because `(x⊗1) · (y⊗1) = q` maps to `0` in the residue
ring of the ideal of definition of `C`. Analogue of `annulusOverlap_basicOpen_disjoint`. -/
theorem selfProductOverlap_basicOpen_disjoint (hq : q ∈ I) :
    basicOpen (CompletedTensorProduct.idealOfDefinition R I (A R I q) (A R I q))
        (CompletedTensorProduct.inl R I (A R I q) (A R I q) (overlapX R I q))
      ⊓ basicOpen (CompletedTensorProduct.idealOfDefinition R I (A R I q) (A R I q))
          (CompletedTensorProduct.inl R I (A R I q) (A R I q) (overlapY R I q)) = ⊥ := by
  rw [← basicOpen_mul, selfProductInl_mul, basicOpen, mk_algebraMap_q_eq_zero_tensor R I q hq]
  exact PrimeSpectrum.basicOpen_zero

/-- **The two interchange overlap charts have disjoint ranges.** The underlying-space images of
`CompletedTensorAwayInterchange.interchangeOpenImmersion I overlapX hI` (the locus `D(x⊗1)`) and
`CompletedTensorAwayInterchange.interchangeOpenImmersion I overlapY hI` (the locus `D(y⊗1)`), both
landing in `Spf C` (`C = A ⊗̂_R A`), are disjoint when `q ∈ I`. This is the geometric input needed
to assemble the base-changed overlap chart of the self fibre-product `𝔈_q ×_{Spf R} 𝔈_q` as an open
immersion. -/
theorem selfProductOverlapChart_range_disjoint (hq : q ∈ I) (hI : I.FG) :
    Disjoint
      (Set.range (CompletedTensorAwayInterchange.interchangeOpenImmersion
        (B := A R I q) I (overlapX R I q) hI).base)
      (Set.range (CompletedTensorAwayInterchange.interchangeOpenImmersion
        (B := A R I q) I (overlapY R I q) hI).base) := by
  rw [CompletedTensorAwayInterchange.range_interchangeOpenImmersion_base,
    CompletedTensorAwayInterchange.range_interchangeOpenImmersion_base]
  refine Set.disjoint_iff_inter_eq_empty.mpr ?_
  rw [← TopologicalSpace.Opens.coe_inf, selfProductOverlap_basicOpen_disjoint R I q hq,
    TopologicalSpace.Opens.coe_bot]

/-- **The combined base-changed overlap chart is an open immersion.** The coproduct `coprod.desc`
of the two interchange overlap charts `interchangeOpenImmersion I overlapX hI` (image `D(x⊗1)`) and
`interchangeOpenImmersion I overlapY hI` (image `D(y⊗1)`), both into `Spf C` (`C = A ⊗̂_R A`), is an
open immersion of locally ringed spaces, because the two images are disjoint. This is the `V`/`f`
overlap datum (for the one-factor-differing chart shape) feeding the eventual four-chart glue of
the self fibre-product `𝔈_q ×_{Spf R} 𝔈_q`. -/
theorem isOpenImmersion_tateSelfProductOverlapChart (hq : q ∈ I) (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion
      (coprod.desc
        (CompletedTensorAwayInterchange.interchangeOpenImmersion (B := A R I q) I
          (overlapX R I q) hI)
        (CompletedTensorAwayInterchange.interchangeOpenImmersion (B := A R I q) I
          (overlapY R I q) hI)) := by
  haveI := CompletedTensorAwayInterchange.isOpenImmersion_interchangeOpenImmersion
    (B := A R I q) I (overlapX R I q) hI
  haveI := CompletedTensorAwayInterchange.isOpenImmersion_interchangeOpenImmersion
    (B := A R I q) I (overlapY R I q) hI
  exact LocallyRingedSpace.IsOpenImmersion.coprodDesc _ _
    (selfProductOverlapChart_range_disjoint R I q hq hI)

end AlgebraicGeometry
