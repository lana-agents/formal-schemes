import FormalSchemes.GeneralFibreProductOfFactors

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The diagonal datum `X ×_{Spf R} X`

For an affine-charted glued formal scheme `X` exposed as a single-factor datum
`DX : AlgebraicGeometry.AffineChartedFibreDatumX` (`FormalSchemes.GeneralFibreProductExposeX`), the
two-factor constructor `BothChartedFibreDatumXY.ofFactors`
(`FormalSchemes.GeneralFibreProductOfFactors`, issue 235a) applied to the *same* factor twice
produces the diagonal datum `X ×_{Spf R} X`. Because `ofFactors DX DX …` copies the exposed
`X`-side from `DX` into *both* sides, its `xGlued`/`yGlued` and `xStructMap`/`yStructMap` are
definitionally the same map (`ofFactors_xGlued`/`ofFactors_yGlued`, `ofFactors_xStructMap`/
`ofFactors_yStructMap` are all `rfl`).

That datum is all this file contains. The diagonal morphism itself lives one file up, in
`FormalSchemes.GeneralDiagonalUnconditional` (issue 487): `diagonal'`, its two universal-property
triangles `diagonal' ≫ pr₁ = 𝟙`, `diagonal' ≫ pr₂ = 𝟙`, and `mono_diagonal'`.

## History (issue 805)

This file used to also define a `diagonal` built from the general mediating morphism `fibreLift`
(issue 234c), carrying a per-refined-chart continuity hypothesis `hs`. That hypothesis is
**unreachable** — `bothRefinedChart` chooses its cover by `Classical.choice` from a subtype that
retains no adic-over-base bound (issue 460), and adicity does not descend along a source cover
(issue 471), which is why the route to discharge it turned out circular (issue 472). Issue 487
re-derived the whole tower over an *explicit* adic-carrying chart family (`fibreLiftOf`,
`FormalSchemes.GeneralFibreProductLiftCharts`) and produced the unconditional `diagonal'`; issue
794 did the same for an arbitrary source (`fibreLiftAdic`). Once issue 798 rerouted the last
consumer, `diagonal` and `fibreLift` had none left, and issue 805 deleted them. Do not reintroduce
an `hs`-shaped hypothesis: thread the adic bound into the chart *type* instead.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {BX : Type u} [CommRing BX] [Algebra R BX]
variable (DX : AffineChartedFibreDatumX R I hI BX)
variable
  (σX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (DX.A i'))) (DX.g i' i'' * DX.g i' i)))
  (hστX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (DX.g i' i'') (DX.g i' i) hI) =
      (furtherLocFst I (DX.g i i') (DX.g i i'') hI).comp (DX.τ i i' h1).symm.toAlgHom)
  (hσcX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
      (σX i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'')))

/-- **The diagonal datum** `X ×_{Spf R} X`: the two-sided fibre-product datum obtained by feeding
the single factor `DX` (with its double-overlap `σ`-data) to `ofFactors` twice. Its two exposed
factors
and two structural morphisms are definitionally `DX`'s, so `yGlued` is defeq `xGlued` and
`yStructMap` defeq `xStructMap`. -/
abbrev diagonalDatum : BothChartedFibreDatumXY R I hI :=
  ofFactors DX DX σX σX hστX hστX hσcX hσcX

end BothChartedFibreDatumXY

end AlgebraicGeometry
