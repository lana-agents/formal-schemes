import FormalSchemes.GeneralSeparatedOpenCover

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The diagonal on a product chart, and the affine-local separatedness criterion (EGA I §10.15)

`FormalSchemes/GeneralSeparatedRange.lean` (issue 764) reduced separatedness of a datum-presented
`X` to closedness of the image of the diagonal, and
`FormalSchemes/GeneralSeparatedOpenCover.lean` (issue 772) made that closedness checkable on an
arbitrary open cover of `X ×_{Spf R} X`. Neither says which cover to use, and closedness of the
image is still a statement about the whole product.

This file supplies the cover the product comes with — its own **product charts**
`Spf(A i ⊗̂_R A j)` — and identifies what the diagonal does on each of them:

* `preimage_range_ι_diagonal'`: the diagonal's preimage of the product chart `(i, j)` is the
  **intersection of the two factor charts** `X_i ∩ X_j`. This is where the two projection laws of
  the diagonal (`diagonal'_comp_pr₁` / `_pr₂`, issue 487) meet the chart/preimage identity
  `range_ι_eq_pr_preimage_inter` (issue 426): a point of `X` lands in the product chart `(i, j)`
  exactly when it lies in the `i`-th chart (that is what `pr₁ ∘ Δ = 𝟙` says) *and* in the `j`-th
  (what `pr₂ ∘ Δ = 𝟙` says).
* `isSeparated_of_isClosed_preimage_ι`: **`X` is separated over `Spf R` as soon as, in each affine
  product chart `Spf(A i ⊗̂_R A j)`, the preimage of the image of the diagonal is closed** — and
  conversely (`isSeparated_iff_isClosed_preimage_ι`).

The criterion is affine-local in the honest sense: its hypothesis lives entirely inside the affine
formal spectrum `Spf(A i ⊗̂_R A j)`, with no subtype of the glued product and no `Classical.choice`
anywhere, and by `preimage_range_ι_diagonal'` together with `image_chartInter_diagonal'` the set
whose closedness is at stake is the image of `X_i ∩ X_j` — the overlap the datum already carries as
`Spf(A i{1/g i j}^)`. What an instance owes per chart is therefore a *ring* statement about a map
out of `A i ⊗̂_R A j`; for the affine one-chart datum it is the codiagonal
`∇ : A ⊗̂_R A → A` (`FormalSchemes/AffineSeparatedValue.lean`), and for the Tate curve model it is
the graph codiagonals of `FormalSchemes/TateDiagonalClosedRange.lean`.

## Main definitions and results

* `AlgebraicGeometry.BothChartedFibreDatumXY.diagonalChartCover` and
  `diagonalChartCover_isOpenCover`: the product charts of `X ×_{Spf R} X` as an open cover.
* `AlgebraicGeometry.BothChartedFibreDatumXY.preimage_range_ι_diagonal'`: the diagonal's preimage
  of the product chart `(i, j)` is `X_i ∩ X_j`.
* `AlgebraicGeometry.BothChartedFibreDatumXY.image_chartInter_diagonal'`: the image of `X_i ∩ X_j`
  under the diagonal is the part of the diagonal's image that the product chart `(i, j)` sees.
* `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_isClosed_preimage_ι` and
  `isSeparated_iff_isClosed_preimage_ι`: the affine-local separatedness criterion.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum Topology
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

/-! ### The product charts as an open cover -/

/-- **The product-chart cover of `X ×_{Spf R} X`.** The chart indexed by `p = (i, j)` contributes
the image of the affine chart `Spf(A i ⊗̂_R A j)` under its glue inclusion `ι p`; it is open because
`ι p` is an open immersion.

Unlike `FormalScheme.affineCover`, which is indexed by the *points* of the space and whose charts
are drawn by `Classical.choice`, this cover is indexed by the datum's own product index type and
its charts are the ones the datum is built from. It is the cover the criterion below is stated
over, and it is the reason that criterion is usable at all (issue 772). -/
def diagonalChartCover :
    (diagonalDatum DX σX hστX hσcX).JX × (diagonalDatum DX σX hστX hσcX).JY →
      TopologicalSpace.Opens
        (diagonalDatum DX σX hστX hσcX).generalFibreProduct.toLocallyRingedSpace :=
  fun p => ⟨Set.range ((diagonalDatum DX σX hστX hσcX).formalGlueData.ι p).base,
    ((diagonalDatum DX σX hστX hσcX).formalGlueData.ι_isOpenImmersion p).base_open.isOpen_range⟩

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The product charts cover `X ×_{Spf R} X`**, by joint surjectivity of the glue inclusions. -/
theorem diagonalChartCover_isOpenCover :
    TopologicalSpace.IsOpenCover (diagonalChartCover DX σX hστX hσcX) := by
  refine TopologicalSpace.IsOpenCover.mk (TopologicalSpace.Opens.ext ?_)
  rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.eq_univ_iff_forall]
  intro x
  obtain ⟨p, y, hy⟩ := (diagonalDatum DX σX hστX hσcX).formalGlueData.ι_jointly_surjective x
  exact Set.mem_iUnion.mpr ⟨p, y, hy⟩

/-! ### What the diagonal sees of a product chart -/

/-- **The diagonal's preimage of the product chart `(i, j)` is the intersection of the two factor
charts `X_i ∩ X_j`.**

Both inclusions are the same two-line computation. A point of the product lies in the chart `(i, j)`
iff its first projection lies in the `X`-chart `i` and its second in the `X`-chart `j`
(`range_ι_eq_pr_preimage_inter`, issue 426); and the two projections of a diagonal point are the
point itself, because `Δ` is a section of both (`diagonal'_comp_pr₁` / `_pr₂`, issue 487). So the
condition on `x` collapses to `x ∈ X_i ∧ x ∈ X_j`.

This is what makes the criterion below affine-local in a useful way: the per-chart obligation is
about the overlap `X_i ∩ X_j`, which the datum already carries as the affine formal spectrum
`Spf(A i{1/g i j}^)`, and not about some opaque piece of the glued product. -/
theorem preimage_range_ι_diagonal'
    (p : (diagonalDatum DX σX hστX hσcX).JX × (diagonalDatum DX σX hστX hσcX).JY) :
    ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base ⁻¹'
        Set.range ((diagonalDatum DX σX hστX hσcX).formalGlueData.ι p).base =
      Set.range ((diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι p.1).base ∩
      Set.range ((diagonalDatum DX σX hστX hσcX).yFormalGlueData.ι p.2).base := by
  have h1 : ⇑((diagonalDatum DX σX hστX hσcX).pr₁
        (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)).base ∘
      ⇑(diagonal' DX σX hστX hσcX).base = id :=
    congrArg (fun g : (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace ⟶
        (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace => ⇑g.base)
      (diagonal'_comp_pr₁ DX σX hστX hσcX)
  have h2 : ⇑((diagonalDatum DX σX hστX hσcX).pr₂
        (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)).base ∘
      ⇑(diagonal' DX σX hστX hσcX).base = id :=
    congrArg (fun g : (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace ⟶
        (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace => ⇑g.base)
      (diagonal'_comp_pr₂ DX σX hστX hσcX)
  -- `range_ι_eq_pr_preimage_inter` is stated under a `letI` prelude, so its equation is reached
  -- through an explicit type ascription rather than by `rw`.
  have hlem : Set.range ((diagonalDatum DX σX hστX hσcX).formalGlueData.ι p).base =
      ⇑((diagonalDatum DX σX hστX hσcX).pr₁
          (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
          (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
          (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)).base ⁻¹'
        Set.range ((diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι p.1).base ∩
      ⇑((diagonalDatum DX σX hστX hσcX).pr₂
          (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
          (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
          (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)).base ⁻¹'
        Set.range ((diagonalDatum DX σX hστX hσcX).yFormalGlueData.ι p.2).base :=
    (diagonalDatum DX σX hστX hσcX).range_ι_eq_pr_preimage_inter
      (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX) p
  have h1' : ∀ x, ((diagonalDatum DX σX hστX hσcX).pr₁
      (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)).base
        ((schemeDiagonal' DX σX hστX hσcX).toLRSHom.base x) = x := fun x => congrFun h1 x
  have h2' : ∀ x, ((diagonalDatum DX σX hστX hσcX).pr₂
      (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
      (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)).base
        ((schemeDiagonal' DX σX hστX hσcX).toLRSHom.base x) = x := fun x => congrFun h2 x
  refine Set.eq_of_subset_of_subset (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨hx1, hx2⟩ := hlem.le hx
    rw [Set.mem_preimage, h1' x] at hx1
    rw [Set.mem_preimage, h2' x] at hx2
    exact ⟨hx1, hx2⟩
  · refine hlem.ge ⟨?_, ?_⟩
    · rw [Set.mem_preimage, h1' x]; exact hx.1
    · rw [Set.mem_preimage, h2' x]; exact hx.2

/-- **What the product chart `(i, j)` sees of the diagonal is the image of `X_i ∩ X_j`.** The
image-of-preimage identity `Set.image_preimage_eq_inter_range` applied to
`preimage_range_ι_diagonal'`; it names the set whose closedness the criterion below asks for. -/
theorem image_chartInter_diagonal'
    (p : (diagonalDatum DX σX hστX hσcX).JX × (diagonalDatum DX σX hστX hσcX).JY) :
    ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base ''
        (Set.range ((diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι p.1).base ∩
          Set.range ((diagonalDatum DX σX hστX hσcX).yFormalGlueData.ι p.2).base) =
      Set.range ((diagonalDatum DX σX hστX hσcX).formalGlueData.ι p).base ∩
        Set.range ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base :=
  (congrArg (Set.image ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base)
    (preimage_range_ι_diagonal' DX σX hστX hσcX p).symm).trans
      Set.image_preimage_eq_inter_range

/-! ### The affine-local criterion -/

/-- **Separatedness is checkable inside the affine product charts.** `X` is separated over `Spf R`
as soon as, for every pair `(i, j)` of chart indices, the preimage of the diagonal's image under the
glue inclusion `ι (i, j) : Spf(A i ⊗̂_R A j) ⟶ X ×_{Spf R} X` is closed **in the affine formal
spectrum `Spf(A i ⊗̂_R A j)` itself**.

No subtype of the glued product occurs in the hypothesis, and no `Classical.choice`: this is the
form in which a concrete datum can actually discharge §10.15. It combines
`isSeparated_of_isOpenCover_isClosed_range` (issue 772) over the product-chart cover with the
homeomorphism `Spf(A i ⊗̂_R A j) ≃ₜ range (ι (i, j))` carried by the open immersion `ι (i, j)`.

By `image_chartInter_diagonal'` the set in question is the image of the overlap `X_i ∩ X_j`, so in
practice one exhibits the chart-restricted diagonal as `Spf` of a **surjective** map out of
`A i ⊗̂_R A j` and appeals to `FormalSpectrum.isClosedEmbedding_map_of_surjective`. -/
theorem isSeparated_of_isClosed_preimage_ι
    (h : ∀ p : (diagonalDatum DX σX hστX hσcX).JX × (diagonalDatum DX σX hστX hσcX).JY,
      IsClosed (⇑((diagonalDatum DX σX hστX hσcX).formalGlueData.ι p).base ⁻¹'
        Set.range ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base)) :
    IsSeparated DX σX hστX hσcX := by
  refine isSeparated_of_isOpenCover_isClosed_range DX σX hστX hσcX
    (diagonalChartCover_isOpenCover DX σX hστX hσcX) fun p => ?_
  have he : IsEmbedding ⇑((diagonalDatum DX σX hστX hσcX).formalGlueData.ι p).base :=
    ((diagonalDatum DX σX hστX hσcX).formalGlueData.ι_isOpenImmersion p).base_open.isEmbedding
  have hcl := (Homeomorph.isClosed_preimage he.toHomeomorph
    (s := Subtype.val ⁻¹' Set.range ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base)).mp (h p)
  rw [Set.range_restrictPreimage]
  exact hcl

/-- **The affine-local criterion is sharp.** The forward direction is closedness of the diagonal's
image (issue 764) pulled back along the continuous `ι p`. -/
theorem isSeparated_iff_isClosed_preimage_ι :
    IsSeparated DX σX hστX hσcX ↔
      ∀ p : (diagonalDatum DX σX hστX hσcX).JX × (diagonalDatum DX σX hστX hσcX).JY,
        IsClosed (⇑((diagonalDatum DX σX hστX hσcX).formalGlueData.ι p).base ⁻¹'
          Set.range ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base) :=
  ⟨fun hsep p => hsep.base_closedEmbedding.isClosed_range.preimage
      ((diagonalDatum DX σX hστX hσcX).formalGlueData.ι p).base.hom.continuous,
    isSeparated_of_isClosed_preimage_ι DX σX hστX hσcX⟩

end BothChartedFibreDatumXY

end AlgebraicGeometry

end
