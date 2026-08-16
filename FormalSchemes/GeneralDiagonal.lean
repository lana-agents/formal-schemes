import FormalSchemes.GeneralFibreProductOfFactors
import FormalSchemes.GeneralFibreProductLift

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The general diagonal `Δ : X ⟶ X ×_{Spf R} X`

For an affine-charted glued formal scheme `X` exposed as a single-factor datum
`DX : AlgebraicGeometry.AffineChartedFibreDatumX` (`FormalSchemes.GeneralFibreProductExposeX`), the
two-factor constructor `BothChartedFibreDatumXY.ofFactors`
(`FormalSchemes.GeneralFibreProductOfFactors`, issue 235a) applied to the *same* factor twice
produces the diagonal datum `X ×_{Spf R} X`. Because `ofFactors DX DX …` copies the exposed
`X`-side from `DX` into *both* sides, its `xGlued`/`yGlued` and `xStructMap`/`yStructMap` are
definitionally the same map (`ofFactors_xGlued`/`ofFactors_yGlued`, `ofFactors_xStructMap`/
`ofFactors_yStructMap` are all `rfl`).

This file defines the **general diagonal** `diagonal : X ⟶ X ×_{Spf R} X` as the general mediating
morphism `fibreLift` of the pair `(𝟙_X, 𝟙_X)` (`FormalSchemes.GeneralFibreProductLift`, issue 234c),
and proves its two universal-property triangles `diagonal ≫ pr₁ = 𝟙`, `diagonal ≫ pr₂ = 𝟙` (from
`fibreLift_comp_pr₁`/`_pr₂` with `a = b = 𝟙`) and its **monomorphism**-ness: the diagonal is a split
mono (the first projection is a retraction), hence a mono, exactly as the affine
`CompletedTensorProduct.mono_schemeDiagonal` (`FormalSchemes.AffineFibreProductScheme`).

The single continuity input `hs` (the per-refined-chart adicity on sections, matching the
continuity-restricted existence regime of issue 234c) stays a **hypothesis** here; it is discharged
unconditionally in issue 235c. This slice is the reusable categorical payload and is independently
mergeable — it is the input to EGA I §10.15 general separatedness.

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

/-- **The general diagonal** `Δ : X ⟶ X ×_{Spf R} X`, defined as the general fibre-product mediating
morphism `fibreLift` of the pair of identities `(𝟙_X, 𝟙_X)`. The base agreement `hcomm` is trivial
because `ofFactors DX DX` makes the two structural morphisms the same map; the per-refined-chart
continuity input `hs` stays a hypothesis (discharged in issue 235c). -/
def diagonal (hZ : (diagonalDatum DX σX hστX hσcX).xGlued.LocallyFG)
    (hs : ∀ c, I ≤ ((diagonalDatum DX σX hστX hσcX).bothRefinedChart
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) hZ c).J.comap
      ((diagonalDatum DX σX hστX hσcX).refinedStructHom
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) hZ c)) :
    (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace ⟶
      (diagonalDatum DX σX hστX hσcX).generalFibreProduct.toLocallyRingedSpace :=
  (diagonalDatum DX σX hστX hσcX).fibreLift
    (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)
    (Z := (diagonalDatum DX σX hστX hσcX).xGlued)
    (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
    (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) hZ
    rfl hs

/-- **The diagonal is a section of the first projection**: `Δ ≫ pr₁ = 𝟙_X`. -/
theorem diagonal_comp_pr₁ (hZ : (diagonalDatum DX σX hστX hσcX).xGlued.LocallyFG)
    (hs : ∀ c, I ≤ ((diagonalDatum DX σX hστX hσcX).bothRefinedChart
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) hZ c).J.comap
      ((diagonalDatum DX σX hστX hσcX).refinedStructHom
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) hZ c)) :
    diagonal DX σX hστX hσcX hZ hs ≫ (diagonalDatum DX σX hστX hσcX).pr₁
        (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX) =
      𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace :=
  (diagonalDatum DX σX hστX hσcX).fibreLift_comp_pr₁
    (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)
    (Z := (diagonalDatum DX σX hστX hσcX).xGlued)
    (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
    (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) hZ
    rfl hs

/-- **The diagonal is a section of the second projection**: `Δ ≫ pr₂ = 𝟙_X`. -/
theorem diagonal_comp_pr₂ (hZ : (diagonalDatum DX σX hστX hσcX).xGlued.LocallyFG)
    (hs : ∀ c, I ≤ ((diagonalDatum DX σX hστX hσcX).bothRefinedChart
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) hZ c).J.comap
      ((diagonalDatum DX σX hστX hσcX).refinedStructHom
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) hZ c)) :
    diagonal DX σX hστX hσcX hZ hs ≫ (diagonalDatum DX σX hστX hσcX).pr₂
        (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX) =
      𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace :=
  (diagonalDatum DX σX hστX hσcX).fibreLift_comp_pr₂
    (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)
    (Z := (diagonalDatum DX σX hστX hσcX).xGlued)
    (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
    (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) hZ
    rfl hs

/-- **The general diagonal is a split monomorphism**: the first projection is a retraction. -/
theorem isSplitMono_diagonal (hZ : (diagonalDatum DX σX hστX hσcX).xGlued.LocallyFG)
    (hs : ∀ c, I ≤ ((diagonalDatum DX σX hστX hσcX).bothRefinedChart
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) hZ c).J.comap
      ((diagonalDatum DX σX hστX hσcX).refinedStructHom
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) hZ c)) :
    IsSplitMono (diagonal DX σX hστX hσcX hZ hs) :=
  IsSplitMono.mk' ⟨(diagonalDatum DX σX hστX hσcX).pr₁
      (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX),
    diagonal_comp_pr₁ DX σX hστX hσcX hZ hs⟩

/-- **`X` is separated over `Spf R`** (EGA I §10.15, categorical level, continuity-restricted
regime): the general diagonal `Δ : X ⟶ X ×_{Spf R} X` is a monomorphism. -/
theorem mono_diagonal (hZ : (diagonalDatum DX σX hστX hσcX).xGlued.LocallyFG)
    (hs : ∀ c, I ≤ ((diagonalDatum DX σX hστX hσcX).bothRefinedChart
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) hZ c).J.comap
      ((diagonalDatum DX σX hστX hσcX).refinedStructHom
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) hZ c)) :
    Mono (diagonal DX σX hστX hσcX hZ hs) :=
  haveI := isSplitMono_diagonal DX σX hστX hσcX hZ hs
  inferInstance

end BothChartedFibreDatumXY

end AlgebraicGeometry
