import FormalSchemes.GeneralDiagonal
import FormalSchemes.GeneralFibreProductLiftCharts
import FormalSchemes.BothDatumAdicOverBase

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The unconditional general diagonal `Δ : X ⟶ X ×_{Spf R} X`

The general diagonal `diagonal` (`FormalSchemes.GeneralDiagonal`, issue 467) carries a standing
continuity hypothesis `hs`: each piece of the internally-chosen refined source cover must be adic on
global sections over the base. For the plain `bothRefinedChart` cover (built by `Classical.choice`)
that hypothesis is *unreachable* — the chosen chart carries no adic-over-base bound and
`Classical.choice` erases the witness, while "an open immersion is adic on sections" is false in
general (issues 460/468/472/487).

This file discharges `hs` by choosing the refined cover from the **adic-over-base neighborhood
basis**. Since `X = xGlued` is adic over its structural morphism `xStructMap`
(`adicOverBase_xStructMap`, issue 487), `exists_affineChart_subset_adicOverBase` supplies, around
every point, a finitely generated affine chart that lands in the required intersection of chart
preimages *and* is adic on global sections over `xStructMap`. Feeding that adic-carrying chart
family `adicDiagonalCharts` to the chart-parametrised mediating morphism `fibreLiftOf`
(`FormalSchemes.GeneralFibreProductLiftCharts`) yields the **unconditional** diagonal `diagonal'`,
whose two projection triangles and monomorphism-ness follow exactly as for `diagonal`.

`diagonal'`, `diagonal'_comp_pr₁`/`_pr₂` and `mono_diagonal'` are the input to EGA I §10.15 general
separatedness (issue 62): `X` is separated over `Spf R` iff its diagonal is a mono (a closed
immersion for the separated case).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.12, §10.15.
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

/-- **Existence of an adic-carrying refined chart** around each point of the diagonal datum's glued
factor `X = xGlued`, over the identity pair `(𝟙, 𝟙)`. Mirrors `nonempty_bothRefinedChart`, but draws
the chart from the *adic-over-base* neighborhood basis (`exists_affineChart_subset_adicOverBase`,
issue 487) of `X` relative to its structural morphism `xStructMap`, so the chart additionally
records the adic bound `I ≤ J.comap (Γ (map ≫ 𝟙 ≫ xStructMap))` — exactly the diagonal's per-piece
continuity witness `hs`. -/
theorem nonempty_adicDiagonalChart (z : (diagonalDatum DX σX hστX hσcX).xGlued) :
    Nonempty { chart : BothRefinedChart (diagonalDatum DX σX hστX hσcX)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) z //
      I ≤ chart.J.comap (globalSectionsMap I chart.J
        (chart.map ≫ (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) ≫
          (diagonalDatum DX σX hστX hσcX).xStructMap)) } := by
  let D := diagonalDatum DX σX hστX hσcX
  let a : D.xGlued.toLocallyRingedSpace ⟶ D.xGlued.toLocallyRingedSpace := 𝟙 _
  obtain ⟨i, y, hy⟩ := D.xFormalGlueData.ι_jointly_surjective (a.base z)
  obtain ⟨j, w, hw⟩ := D.yFormalGlueData.ι_jointly_surjective (a.base z)
  have hUopen : IsOpen
      ((a.base ⁻¹' Set.range (D.xFormalGlueData.ι i).base) ∩
        (a.base ⁻¹' Set.range (D.yFormalGlueData.ι j).base)) :=
    ((D.xFormalGlueData.ι_isOpenImmersion i).base_open.isOpen_range.preimage
        a.base.hom.continuous).inter
      ((D.yFormalGlueData.ι_isOpenImmersion j).base_open.isOpen_range.preimage
        a.base.hom.continuous)
  have hzU : z ∈
      ((a.base ⁻¹' Set.range (D.xFormalGlueData.ι i).base) ∩
        (a.base ⁻¹' Set.range (D.yFormalGlueData.ι j).base)) := by
    refine ⟨?_, ?_⟩ <;> simp only [Set.mem_preimage]
    · exact ⟨y, hy⟩
    · exact ⟨w, hw⟩
  obtain ⟨S, _, _, J, _, f, hJfg, hzmem, hsub, hoi, hadic⟩ :=
    D.xGlued.exists_affineChart_subset_adicOverBase D.xStructMap (adicOverBase_xStructMap D) z _
      hUopen hzU
  refine ⟨⟨{ xIdx := i, yIdx := j, R := S, J := J, map := f, fg := hJfg, mem := hzmem,
             xsubset := fun _ hp => (hsub hp).1, ysubset := fun _ hp => (hsub hp).2 }, ?_⟩⟩
  rw [Category.id_comp]
  exact hadic

/-- The chosen adic-carrying refined chart family for the diagonal, via `Classical.choice`. Its
`hadic` bound is recovered by `adicDiagonalCharts_hs`. -/
def adicDiagonalCharts (z : (diagonalDatum DX σX hστX hσcX).xGlued) :
    BothRefinedChart (diagonalDatum DX σX hστX hσcX)
      (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
      (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace) z :=
  (nonempty_adicDiagonalChart DX σX hστX hσcX z).some.1

/-- **The discharged continuity witness `hs` for the diagonal.** Each piece of the adic-carrying
refined cover `adicDiagonalCharts` is adic on global sections over the base, by construction. -/
theorem adicDiagonalCharts_hs (z : (diagonalDatum DX σX hστX hσcX).xGlued) :
    I ≤ (adicDiagonalCharts DX σX hστX hσcX z).J.comap
      ((diagonalDatum DX σX hστX hσcX).refinedStructHomOf
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (adicDiagonalCharts DX σX hστX hσcX) z) :=
  (nonempty_adicDiagonalChart DX σX hστX hσcX z).some.2

/-- **The unconditional general diagonal** `Δ' : X ⟶ X ×_{Spf R} X`, defined as `fibreLiftOf` of the
identity pair over the adic-carrying refined cover `adicDiagonalCharts`, whose continuity witness is
discharged by `adicDiagonalCharts_hs`. No `hs` hypothesis remains. -/
def diagonal' :
    (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace ⟶
      (diagonalDatum DX σX hστX hσcX).generalFibreProduct.toLocallyRingedSpace :=
  (diagonalDatum DX σX hστX hσcX).fibreLiftOf
    (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
    (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
    (adicDiagonalCharts DX σX hστX hσcX)
    (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)
    rfl
    (adicDiagonalCharts_hs DX σX hστX hσcX)

/-- **The unconditional diagonal is a section of the first projection**: `Δ' ≫ pr₁ = 𝟙_X`. -/
theorem diagonal'_comp_pr₁ :
    diagonal' DX σX hστX hσcX ≫ (diagonalDatum DX σX hστX hσcX).pr₁
        (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX) =
      𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace :=
  (diagonalDatum DX σX hστX hσcX).fibreLiftOf_comp_pr₁
    (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
    (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
    (adicDiagonalCharts DX σX hστX hσcX)
    (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)
    rfl
    (adicDiagonalCharts_hs DX σX hστX hσcX)

/-- **The unconditional diagonal is a section of the second projection**: `Δ' ≫ pr₂ = 𝟙_X`. -/
theorem diagonal'_comp_pr₂ :
    diagonal' DX σX hστX hσcX ≫ (diagonalDatum DX σX hστX hσcX).pr₂
        (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX) =
      𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace :=
  (diagonalDatum DX σX hστX hσcX).fibreLiftOf_comp_pr₂
    (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
    (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
    (adicDiagonalCharts DX σX hστX hσcX)
    (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)
    rfl
    (adicDiagonalCharts_hs DX σX hστX hσcX)

/-- **The unconditional general diagonal is a split monomorphism**: `pr₁` is a retraction. -/
theorem isSplitMono_diagonal' : IsSplitMono (diagonal' DX σX hστX hσcX) :=
  IsSplitMono.mk' ⟨(diagonalDatum DX σX hστX hσcX).pr₁
      (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX),
    diagonal'_comp_pr₁ DX σX hστX hσcX⟩

/-- **`X` is separated over `Spf R`** (EGA I §10.15, categorical level, *unconditional*): the
general diagonal `Δ' : X ⟶ X ×_{Spf R} X` is a monomorphism, with no standing continuity
hypothesis. -/
theorem mono_diagonal' : Mono (diagonal' DX σX hστX hσcX) :=
  haveI := isSplitMono_diagonal' DX σX hστX hσcX
  inferInstance

end BothChartedFibreDatumXY

end AlgebraicGeometry

end
