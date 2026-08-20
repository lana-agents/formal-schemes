import Mathlib.RingTheory.AdicCompletion.Algebra

set_option linter.style.header false
set_option linter.style.setOption false

/-!
# The `R`-algebra transport of an adic completion along an equality of ideals

For equal ideals `K₁ = K₂` of a ring `B`, the completions `AdicCompletion K₁ B` and
`AdicCompletion K₂ B` are canonically isomorphic. The plain ring-level version of this is
`AdicCompletion.congrIdeal` (`FormalSchemes.TateOverlapImmersion`); this file supplies the
`R`-algebra version, which is what the `τ` field of an affine-charted glue datum consumes
(`AlgebraicGeometry.AffineChartedFibreDatum`, `FormalSchemes.GeneralFibreProductAffineBase`).

## Why this file exists at all

The transport is load-bearing in two separate towers — the Tate chart transitions and the
open-cover chart data — which for a while each carried their own copy: `congrIdealₐ` in
`FormalSchemes.TwoPatchFibreProduct` (behind the whole Tate tower) and `congrIdealAlg` in
`FormalSchemes.AwayCompletionNested` (three files above the bottom of the import graph). Neither
could cite the other without putting general commutative algebra downstream of the Tate curve, so
the duplication was deliberate and recorded in both docstrings. This file is the shared home the
two were waiting for: it imports nothing but Mathlib, so anything in the library may use it.

## Contents

* `AdicCompletion.congrIdealₐ`: the transport itself;
* `AdicCompletion.congrIdealₐ_algebraMap`: it fixes the structural image of the base ring.

## Implementation notes

`congrIdealₐ` is built by `subst` from `AlgEquiv.refl`, so its algebra-map compatibility is
definitional and the transport never has to be projected at a point. That matters: the pointwise
route through the ring-level `AdicCompletion.congrIdeal` is pathologically expensive at the
concrete completion types this library works with (cf. `FormalSchemes.TateChainStructMap`).
Compose these transports; do not evaluate them at elements.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4).
-/

noncomputable section

universe u

namespace AdicCompletion

/-- **The `R`-algebra transport of a completion along an equality of ideals.** The `R`-algebra
version of `AdicCompletion.congrIdeal`: for equal ideals `K₁ = K₂` the completions
`AdicCompletion K₁ B` and `AdicCompletion K₂ B` are canonically isomorphic as `R`-algebras.

Built by `subst` from `AlgEquiv.refl`, so its algebra-map compatibility is definitional and the
transport never has to be projected at a point — the pointwise route through `congrIdeal` is
pathologically expensive at the concrete completion types (cf.
`FormalSchemes.TateChainStructMap`). -/
def congrIdealₐ {B : Type u} [CommRing B] (R : Type u) [CommRing R] [Algebra R B]
    {K₁ K₂ : Ideal B} (h : K₁ = K₂) :
    AdicCompletion K₁ B ≃ₐ[R] AdicCompletion K₂ B := by
  subst h; exact AlgEquiv.refl

/-- The transport fixes the structural image of the base ring. -/
theorem congrIdealₐ_algebraMap {B : Type u} [CommRing B] (R : Type u) [CommRing R] [Algebra R B]
    {K₁ K₂ : Ideal B} (h : K₁ = K₂) (b : B) :
    congrIdealₐ R h (algebraMap B (AdicCompletion K₁ B) b) =
      algebraMap B (AdicCompletion K₂ B) b := by
  subst h; rfl

end AdicCompletion
