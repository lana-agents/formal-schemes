import FormalSchemes.TateDiagonalClosedCover
import FormalSchemes.RightCodiagonalClosedEmbedding
import FormalSchemes.GlueDataImageInter

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Global closedness of the range of the Tate self-product diagonal

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`. Over the
*corrected* (𝔾m-inversion, Néron 2-gon) model of the Tate curve `𝔈_q`, the glued diagonal

```
Δ : 𝔈_q ⟶ 𝔈_q ×_{Spf R} 𝔈_q
```

has **closed range**, so (being a topological embedding as a section of `pr₁`) it is a **closed
topological embedding**. This is the global (route b) form of the separatedness input of EGA I
§10.15: it collapses the per-chart bricks 424/425 into a single global fact, from which the
per-chart `restrictPreimage` closed-embedding statements follow immediately by
`Set.restrictPreimage_isClosedEmbedding`.

## Strategy

Closedness of `range Δ.base` is checked local-at-target along the four-chart open cover
`tateSelfProductChartCover` (`IsOpenCover.isClosed_iff_coe_preimage`):

* on the two **diagonal** charts `(b, b)` the coe-preimage of `range Δ.base` is closed because
  `restrictPreimage_diagonal_diagChart` already exhibits the chart restriction of `Δ.base` as a
  closed embedding, whose range is exactly that coe-preimage;
* on the two **mixed** charts `(b, ¬b)` the coe-preimage is the closed diagonal-over-overlap locus,
  the graph of the 𝔾m-inversion transition, realised as the range of `Spf` of a surjective right
  codiagonal (`isClosedEmbedding_map_rightCodiagonal`).

## Main results

* `AlgebraicGeometry.isClosed_range_tateSelfProductDiagonal_base`: `range Δ.base` is closed.
* `AlgebraicGeometry.isClosedEmbedding_tateSelfProductDiagonal_base`: `Δ.base` is a closed
  embedding.
* `AlgebraicGeometry.restrictPreimage_diagonal_offDiag`: the mixed-chart restriction of `Δ.base`
  is a closed embedding (issue 424).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]

/-! ### The range decomposition of the glued diagonal -/

/-- The factorisation of the glued diagonal on the `b`-chart:
`ι b ≫ Δ = diagChart ≫ ι (b, b)`. -/
theorem curve_ι_comp_diagonal (hq : q ∈ I) (hI : I.FG) (b : ULift Bool) :
    (tateCurveFormalGlueData R I q hq hI).ι b ≫ tateSelfProductDiagonal R I q hq hI =
      diagChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(b.down, b.down)⟩ := by
  rw [tateSelfProductDiagonal]
  exact (tateCurveFormalGlueData R I q hq hI).ι_glueMorphisms _ _ b

/-- **Range decomposition of the glued diagonal.** The range of `Δ.base` is the union, over the two
curve charts `b : ULift Bool`, of the ranges of the diagonal-chart composites
`diagChart ≫ ι (b, b)`. This follows from the joint surjectivity of the two curve-chart
inclusions together with the factorisation `ι b ≫ Δ = diagChart ≫ ι (b, b)`. -/
theorem range_tateSelfProductDiagonal_base_eq_union (hq : q ∈ I) (hI : I.FG) :
    Set.range (tateSelfProductDiagonal R I q hq hI).base =
      Set.range ((diagChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩).base) ∪
        Set.range ((diagChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩).base) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    obtain ⟨b, x', rfl⟩ := (tateCurveFormalGlueData R I q hq hI).ι_jointly_surjective x
    have hpt : (tateSelfProductDiagonal R I q hq hI).base
        (((tateCurveFormalGlueData R I q hq hI).ι b).base x') =
        (diagChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(b.down, b.down)⟩).base x' :=
      congrArg (fun m => m.base x') (curve_ι_comp_diagonal R I q hq hI b)
    rw [hpt]
    obtain ⟨_ | _⟩ := b
    · exact Or.inl ⟨x', rfl⟩
    · exact Or.inr ⟨x', rfl⟩
  · rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨((tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩).base x,
        congrArg (fun m => m.base x) (curve_ι_comp_diagonal R I q hq hI ⟨false⟩)⟩
    · exact ⟨((tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩).base x,
        congrArg (fun m => m.base x) (curve_ι_comp_diagonal R I q hq hI ⟨true⟩)⟩

/-! ### The mixed-chart coe-preimage is closed -/

/-- **The coe-preimage of `range Δ.base` over a mixed chart `(b, ¬b)` is closed.** This is the
genuine new content over the corrected inversion model: the diagonal-over-overlap locus in the mixed
chart is the graph of the 𝔾m-inversion transition, realised as the range of `Spf` of a surjective
right codiagonal, hence closed. -/
theorem isClosed_coe_preimage_range_diagonal_offChart (hq : q ∈ I) (hI : I.FG) (b : ULift Bool) :
    IsClosed (Subtype.val ⁻¹' Set.range (tateSelfProductDiagonal R I q hq hI).base :
      Set (tateSelfProductChartCover R I q hq hI ⟨(b.down, !b.down)⟩)) := by
  sorry

/-! ### Global closedness and the closed embedding -/

/-- **The range of the glued Tate self-product diagonal is closed.** Checked local-at-target along
the four-chart open cover: on the diagonal charts by `restrictPreimage_diagonal_diagChart`, on the
mixed charts by `isClosed_coe_preimage_range_diagonal_offChart`. -/
theorem isClosed_range_tateSelfProductDiagonal_base (hq : q ∈ I) (hI : I.FG) :
    IsClosed (Set.range (tateSelfProductDiagonal R I q hq hI).base) := by
  apply (tateSelfProductChartCover_isOpenCover R I q hq hI).isClosed_iff_coe_preimage.mpr
  rintro ⟨⟨c₁, c₂⟩⟩
  match c₁, c₂ with
  | false, false =>
    have h := (restrictPreimage_diagonal_diagChart R I q hq hI
      (⟨false⟩ : ULift.{u} Bool)).isClosed_range
    rwa [Set.range_restrictPreimage] at h
  | true, true =>
    have h := (restrictPreimage_diagonal_diagChart R I q hq hI
      (⟨true⟩ : ULift.{u} Bool)).isClosed_range
    rwa [Set.range_restrictPreimage] at h
  | false, true =>
    exact isClosed_coe_preimage_range_diagonal_offChart R I q hq hI (⟨false⟩ : ULift.{u} Bool)
  | true, false =>
    exact isClosed_coe_preimage_range_diagonal_offChart R I q hq hI (⟨true⟩ : ULift.{u} Bool)

/-- **The base map of the glued Tate self-product diagonal is a topological embedding.** It is a
section of the first projection `pr₁` (`tateSelfProductDiagonal_comp_pr₁`), hence a
left-invertible continuous map. -/
theorem isEmbedding_tateSelfProductDiagonal_base (hq : q ∈ I) (hI : I.FG) :
    IsEmbedding ⇑(tateSelfProductDiagonal R I q hq hI).base := by
  have hsecpt : ∀ c, (tateSelfProductPr₁ R I q hq hI).base
      ((tateSelfProductDiagonal R I q hq hI).base c) = c := fun c =>
    congrArg (fun m => m.base c) (tateSelfProductDiagonal_comp_pr₁ R I q hq hI)
  exact Topology.IsEmbedding.of_leftInverse hsecpt
    (tateSelfProductPr₁ R I q hq hI).base.hom.continuous
    (tateSelfProductDiagonal R I q hq hI).base.hom.continuous

/-- **The base map of the glued Tate self-product diagonal is a closed topological embedding**
(EGA I §10.15, route b): it is a topological embedding with closed range. -/
theorem isClosedEmbedding_tateSelfProductDiagonal_base (hq : q ∈ I) (hI : I.FG) :
    IsClosedEmbedding ⇑(tateSelfProductDiagonal R I q hq hI).base :=
  ⟨isEmbedding_tateSelfProductDiagonal_base R I q hq hI,
    isClosed_range_tateSelfProductDiagonal_base R I q hq hI⟩

/-- **The mixed-chart restriction of the diagonal is a closed embedding** (issue 424). On the mixed
chart `(b, ¬b)` the restriction of `Δ.base` to the preimage of the chart is a closed topological
embedding, immediately from the global closed embedding via
`Set.restrictPreimage_isClosedEmbedding`. -/
theorem restrictPreimage_diagonal_offDiag (hq : q ∈ I) (hI : I.FG) (b : ULift Bool) :
    IsClosedEmbedding
      ((tateSelfProductChartCover R I q hq hI ⟨(b.down, !b.down)⟩ :
        Set ((tateSelfProductInv R I q hq hI).toLocallyRingedSpace)).restrictPreimage
        (tateSelfProductDiagonal R I q hq hI).base) :=
  Set.restrictPreimage_isClosedEmbedding _
    (isClosedEmbedding_tateSelfProductDiagonal_base R I q hq hI)

end AlgebraicGeometry
