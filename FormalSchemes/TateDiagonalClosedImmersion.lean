import FormalSchemes.ClosedImmersionSplitMono
import FormalSchemes.TateDiagonalClosedRange

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The Tate diagonal is a closed immersion (EGA I §10.15)

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`. Over the
corrected (𝔾m-inversion, Néron 2-gon) model of the Tate curve `𝔈_q`, the glued diagonal

```
Δ : 𝔈_q ⟶ 𝔈_q ×_{Spf R} 𝔈_q
```

is a **closed immersion**: its base map is a closed topological embedding and all of its stalk maps
are surjective. This is the sharp EGA I §10.15 separatedness of `𝔈_q` over `Spf R`, upgrading the
`Mono` of `FormalSchemes/TateSeparated.lean`.

## What this file does

Nothing but assemble. Both halves are already on master:

* the topological half is `isClosedEmbedding_tateSelfProductDiagonal_base`
  (`FormalSchemes/TateDiagonalClosedRange.lean`), proved by checking closedness of `range Δ.base`
  local-at-target on the four-chart cover — the mixed charts being the hard case, where the
  preimage is the union of the two graphs of the 𝔾m-inversion transition;
* the sheaf half is `tateSelfProductDiagonal_surjective_stalkMap`
  (`FormalSchemes/TateSeparated.lean`), from the per-chart factorisation through the affine
  diagonal `diagChart` and the surjectivity of the codiagonal.

The statement's shape mirrors the affine `CompletedTensorProduct.diagonal_isClosedImmersion`
(`FormalSchemes/ClosedImmersionSections.lean`).

## The sheaf half is free

`tateSelfProductDiagonal_surjective_stalkMap_of_pr₁` re-derives the stalk half from the section
identity `Δ ≫ pr₁ = 𝟙` alone, with no stalk computation, via
`AlgebraicGeometry.surjective_stalkMap_of_retraction`. So the genuine content of separatedness for
the Tate model — as for any diagonal — is purely topological: it lives entirely in the closed
embedding, and the closed embedding lives entirely in the mixed charts.

## Not here: the `FormalScheme.IsClosedImmersion` predicate

`FormalScheme.IsClosedImmersion` (`FormalSchemes/ClosedImmersion.lean`) is stated for a
`FormalScheme.Hom`, whereas `tateSelfProductDiagonal` is a bare `LocallyRingedSpace` morphism
between the `toLocallyRingedSpace` of the two models. Bridging the two means exhibiting the Tate
model inside the `BothChartedFibreDatumXY` framework of `FormalSchemes/GeneralSeparated.lean`; that
is a separate job. Once it is done, `FormalScheme.isClosedImmersion_of_retraction` turns
`isClosedEmbedding_tateSelfProductDiagonal_base` into a `FormalScheme.IsClosedImmersion` directly.

## Main results

* `AlgebraicGeometry.restrictPreimage_diagonal`: the uniform four-chart local-at-target form.
* `AlgebraicGeometry.tateSelfProductDiagonal_surjective_stalkMap_of_pr₁`: the stalk half from the
  retraction.
* `AlgebraicGeometry.tateSelfProductDiagonal_isClosedImmersion`: the capstone.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [The Stacks Project, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ).
-/

noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]
variable [TopologicalSpace R] [IsAdicRing I]

/-- **The local-at-target form, uniform in the chart.** On *every* one of the four charts `p` of the
Tate self-product — diagonal and mixed alike — the restriction of `Δ.base` to the preimage of the
chart is a closed topological embedding.

Note the direction of the implication. The per-chart statements
`restrictPreimage_diagonal_diagChart` and `restrictPreimage_diagonal_offDiag` were originally meant
to be glued *into* the global closed embedding; in the end the global statement was proved first
(closedness of `range Δ.base` is what is local-at-target), and the per-chart statements fall out of
it by `Set.restrictPreimage_isClosedEmbedding`. That removes the `(b, b)` / `(b, ¬b)` case split
entirely. -/
theorem restrictPreimage_diagonal (hq : q ∈ I) (hI : I.FG) (p : ULift (Bool × Bool)) :
    IsClosedEmbedding
      (Set.restrictPreimage
        ((tateSelfProductChartCover R I q hq hI p :
          Set ((tateSelfProductInv R I q hq hI).toLocallyRingedSpace)))
        (tateSelfProductDiagonal R I q hq hI).base) :=
  Set.restrictPreimage_isClosedEmbedding _
    (isClosedEmbedding_tateSelfProductDiagonal_base R I q hq hI)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The stalk half of the closed immersion, for free from the section identity.** The diagonal is
a section of the first projection (`tateSelfProductDiagonal_comp_pr₁`), and a morphism of locally
ringed spaces with a retraction has surjective stalk maps
(`surjective_stalkMap_of_retraction`): the identity's stalk map factors through it.

This re-proves `tateSelfProductDiagonal_surjective_stalkMap` with no stalk computation and no
reference to the codiagonal — a Tate-level instance of the general fact that separatedness is a
purely topological condition on a split mono. -/
theorem tateSelfProductDiagonal_surjective_stalkMap_of_pr₁ (hq : q ∈ I) (hI : I.FG) :
    ∀ y, Function.Surjective ((tateSelfProductDiagonal R I q hq hI).stalkMap y).hom :=
  surjective_stalkMap_of_retraction (tateSelfProductDiagonal R I q hq hI)
    (tateSelfProductPr₁ R I q hq hI) (tateSelfProductDiagonal_comp_pr₁ R I q hq hI)

/-- **The glued diagonal of the Tate curve model is a closed immersion** (EGA I §10.15): its base
map is a closed topological embedding (`isClosedEmbedding_tateSelfProductDiagonal_base`) and all of
its stalk maps are surjective (`tateSelfProductDiagonal_surjective_stalkMap`). Equivalently, the
Tate curve model `𝔈_q` is separated over `Spf R` in the sharp sense, not merely `Mono`.

The statement mirrors the affine `CompletedTensorProduct.diagonal_isClosedImmersion`, which is the
one-chart case: there the closed embedding comes from `Spf` of the surjective codiagonal, here from
the global range computation over the four charts of the self-product. -/
theorem tateSelfProductDiagonal_isClosedImmersion (hq : q ∈ I) (hI : I.FG) :
    IsClosedEmbedding ⇑(tateSelfProductDiagonal R I q hq hI).base ∧
      ∀ y, Function.Surjective ((tateSelfProductDiagonal R I q hq hI).stalkMap y).hom :=
  ⟨isClosedEmbedding_tateSelfProductDiagonal_base R I q hq hI,
    tateSelfProductDiagonal_surjective_stalkMap R I q hq hI⟩

end AlgebraicGeometry
