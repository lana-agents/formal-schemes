import FormalSchemes.GeneralSeparatedRange
import FormalSchemes.GeneralFibreProductBaseChange
import FormalSchemes.GeneralFibreProductExposeXIdealCongr

set_option linter.style.header false

/-!
# Separatedness descends along the base change of the diagonal (EGA I §10.15)

`FormalSchemes.GeneralSeparatedRange` proves that separatedness of a datum-presented `X` over
`Spf R` is *exactly* closedness of one subset of one space:
`AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_iff_isClosed_range_diagonal_base`. The
diagonal is a section of the first projection
(`AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'_comp_pr₁`), so both the stalk half and the
embedding half of the closed-immersion predicate are free and only the range is at issue.

This file draws the consequence for a **base change of the adic base**. If the same charts are read
over `(R, I)` and over `(R', I')`, the glued factor `X` is literally the same formal scheme
(`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr`), the two fibre products
are related by the glued comparison of `FormalSchemes.GeneralFibreProductBaseChange`, and
separatedness over the first base gives separatedness over the second — **provided the two
diagonals are related by that comparison**, which is this file's one hypothesis and is discussed
under *What is not proved here*.

## The argument, in two steps

Both steps are re-derived here and neither is taken from a summary.

1. **Separatedness is closedness of a range.** Quoted from the tree rather than from a description:
   `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_iff_isClosed_range_diagonal_base` is an
   `Iff` between `AlgebraicGeometry.BothChartedFibreDatumXY.IsSeparated` and closedness of the
   range of the base map of
   `AlgebraicGeometry.BothChartedFibreDatumXY.schemeDiagonal'`.
   So there is **no stalk obligation anywhere in this file**, at either base.

2. **The cancellation is a preimage.** Write `Δ'` for the diagonal over `(R', I')`, `Δ` for the one
   over `(R, I)` and `ι` for the comparison, and suppose `Δ' ≫ ι = Δ` after the identification of
   the two sources. `AlgebraicGeometry.LocallyRingedSpace.range_base_eq_preimage_range_comp_base`
   says that for **injective** `ι` the range of `Δ'` is the `ι`-preimage of the range of `Δ' ≫ ι`;
   a preimage of a closed set under a continuous map is closed, and the base map of a morphism of
   locally ringed spaces is continuous by construction. **Injectivity is all that is asked of
   `ι`**, and `AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base` supplies it for the
   glued base change against its two hypotheses.

## What is not proved here

**The triangle `Δ' ≫ ι = Δ` is a hypothesis of both theorems below and is not discharged.** It is
not bookkeeping and it is not free:

* `AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'` is
  `AlgebraicGeometry.BothChartedFibreDatumXY.fibreLiftOf` of the identity pair over a refined chart
  family chosen by `Classical.choice`
  (`AlgebraicGeometry.BothChartedFibreDatumXY.adicDiagonalCharts`), so nothing about how it
  restricts to a chart of the glued source is available, and the triangle cannot be checked
  chartwise.
* What characterises it is its two projection triangles together with
  `AlgebraicGeometry.BothChartedFibreDatumXY.fibreLift_unique_adicOverBase`. That is exactly how
  the same-base transport `AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'_transport`
  (`FormalSchemes.GeneralSeparatedPresentation`) is proved, and it consumes
  `AlgebraicGeometry.BothChartedFibreDatumXY.compareIso_hom_comp_pr₁` — the statement that the
  comparison commutes with the first projection.
* **The base-change analogue of that statement does not exist on this tree.** Nothing says
  `AlgebraicGeometry.DoubleChartGlue.baseChange` commutes with
  `AlgebraicGeometry.BothChartedFibreDatumXY.pr₁`, and nothing says the chart-level
  `AlgebraicGeometry.DoubleChartGlue.chartBaseChange` commutes with
  `AlgebraicGeometry.BothChartedFibreDatumXY.pr₁ChartSelf`. Both are missing, the second is the
  input to the first, and neither is this file's subject.

## Is the implication an `Iff`?

**No, and not for a bookkeeping reason.** The converse asks for closedness of
`Set.range ⇑Δ.base`, which is `⇑ι.base '' Set.range ⇑Δ'.base`, so it needs the image of a closed
set under `ι` to be closed — a *closed-map* property of the glued comparison, not an injectivity
one. `FormalSchemes.GeneralFibreProductBaseChange` records that this is unavailable: its chart legs
are closed immersions (`AlgebraicGeometry.DoubleChartGlue.chartBaseChange_eq_schemeBaseChange` and
`CompletedTensorProduct.schemeBaseChange_isClosedImmersion`), but the range of the glued morphism
is a union of chart images and closedness of such a union is a question about the target's glue
that neither of that morphism's hypotheses answers. So the `Iff` is not free, and the implication
is what is stated.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.range_base_eq_preimage_range_comp_base` and
  `AlgebraicGeometry.LocallyRingedSpace.isClosed_range_base_of_isClosed_range_comp`: **left
  cancellation of a range against an injective postcomposition**, and its consequence for
  closedness. Nothing about rings, ideals or formal schemes enters either.
* `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_isSeparated_of_diagonal_factorization`:
  **the implication, with the comparison abstract** — any morphism of the two fibre products that
  is injective on points and receives the two diagonals.
* `AlgebraicGeometry.BothChartedFibreDatumXY.diagonalDoubleChartGlue` and
  `AlgebraicGeometry.BothChartedFibreDatumXY.xGlued_diagonalDatum_ofAlgebraData_congr`: the glue
  carried by the diagonal datum of a factor presented by algebra data, and the identification of
  the two glued factors that the theorem below needs as its source equality.
* `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_isSeparated_baseChange`: **the
  implication at the glued base change**, where the comparison is
  `AlgebraicGeometry.DoubleChartGlue.baseChange` and injectivity is discharged from its overlap
  square and its overlap saturation.

## Placement

A leaf over `FormalSchemes.GeneralSeparatedRange`, `FormalSchemes.GeneralFibreProductBaseChange`
and `FormalSchemes.GeneralFibreProductExposeXIdealCongr`: forward closure **184** project modules
besides itself (185 counted with itself), reverse closure **0**. None of the three imports is
implied by the others — the first two are incomparable, and the third contributes **5** modules
that neither of them reaches.

The two locally-ringed-space lemmas are here and **not** in
`FormalSchemes.LocallyRingedSpaceRange`, which is this tree's home for range statements about base
maps, for two measured reasons. That module's subject, stated in its own title, is that an
`eqToHom` **prefix** is invisible to a base map — a fact about precomposition with an isomorphism,
whose proof is surjectivity of that isomorphism's base map. Left cancellation against an injective
**postcomposition** is the other side of a composite and shares no step with it. And
`FormalSchemes.LocallyRingedSpaceRange` has reverse closure **260**: putting a lemma with one
consumer there adds it to the environment of that many modules and re-elaborates all of them,
against this file's **0**. If a second consumer appears at a module this one cannot reach, the move
is cheap and that file is where it goes.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum Topology
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

namespace LocallyRingedSpace

/-- **A range cancels on the left against an injective postcomposition.** For `g : X ⟶ Y` and
`f : Y ⟶ Z` with `f` injective on points, the range of `g` is the `f`-preimage of the range of
`g ≫ f`.

The `⊆` holds for any `f`; injectivity is what gives `⊇`, and it is the only thing asked of `f`. -/
theorem range_base_eq_preimage_range_comp_base {X Y Z : LocallyRingedSpace.{u}}
    (g : X ⟶ Y) (f : Y ⟶ Z) (hf : Function.Injective ⇑f.base) :
    Set.range ⇑g.base = ⇑f.base ⁻¹' Set.range ⇑(g ≫ f).base := by
  have himg : Set.range ⇑(g ≫ f).base = ⇑f.base '' Set.range ⇑g.base := by
    rw [← Set.range_comp]
    refine congrArg Set.range ?_
    funext x
    rw [LocallyRingedSpace.comp_base]
    simp
  rw [himg, Set.preimage_image_eq _ hf]

/-- **Closedness of a range descends along an injective postcomposition.** The range of `g` is a
preimage of the range of `g ≫ f` by `range_base_eq_preimage_range_comp_base`, and the base map of a
morphism of locally ringed spaces is continuous, so a closed range upstairs gives a closed range
downstairs.

Continuity costs nothing here: the base map of a morphism of locally ringed spaces is itself a
morphism of topological spaces. -/
theorem isClosed_range_base_of_isClosed_range_comp {X Y Z : LocallyRingedSpace.{u}}
    (g : X ⟶ Y) (f : Y ⟶ Z) (hf : Function.Injective ⇑f.base)
    (h : IsClosed (Set.range ⇑(g ≫ f).base)) :
    IsClosed (Set.range ⇑g.base) := by
  rw [range_base_eq_preimage_range_comp_base g f hf]
  exact h.preimage f.base.hom.continuous

end LocallyRingedSpace

namespace BothChartedFibreDatumXY

/-! ### The implication, with the comparison abstract -/

section Abstract

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {BX : Type u} [CommRing BX] [Algebra R BX]
variable {R' : Type u} [CommRing R'] {I' : Ideal R'} {hI' : I'.FG}
variable [TopologicalSpace R'] [IsAdicRing I']
variable {BX' : Type u} [CommRing BX'] [Algebra R' BX']
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
variable (DX' : AffineChartedFibreDatumX R' I' hI' BX')
variable
  (σX' : letI := DX'.commRing; letI := DX'.algebra;
    ∀ (i i' i'' : DX'.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I'.map (algebraMap R' (DX'.A i))) (DX'.g i i' * DX'.g i i'') ≃ₐ[R']
      awayCompletion (I'.map (algebraMap R' (DX'.A i'))) (DX'.g i' i'' * DX'.g i' i)))
  (hστX' : letI := DX'.commRing; letI := DX'.algebra;
    ∀ (i i' i'' : DX'.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX' i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I' (DX'.g i' i'') (DX'.g i' i) hI') =
      (furtherLocFst I' (DX'.g i i') (DX'.g i i'') hI').comp (DX'.τ i i' h1).symm.toAlgHom)
  (hσcX' : letI := DX'.commRing; letI := DX'.algebra;
    ∀ (i i' i'' : DX'.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX' i i' i'' h1 h2 h3).trans ((σX' i' i'' i h3 h1.symm h2.symm).trans
      (σX' i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R')
        (A₁ := awayCompletion (I'.map (algebraMap R' (DX'.A i))) (DX'.g i i' * DX'.g i i'')))

/-- **Separatedness descends along a comparison of the two fibre products that receives the two
diagonals.** The two data present the *same* glued factor `X` — that is the source hypothesis, an
equality of locally ringed spaces and not merely an isomorphism — and `ι` compares the fibre
products over the two bases.

Only two things are asked of `ι`: that it be injective on points, and that the two diagonals be
related by it. Continuity is free, and closedness of `ι`'s own range is never used. See this file's
*What is not proved here* for why the triangle is a hypothesis and not a theorem. -/
theorem isSeparated_of_isSeparated_of_diagonal_factorization
    (hsrc : (diagonalDatum DX' σX' hστX' hσcX').xGlued.toLocallyRingedSpace =
      (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
    (ι : (diagonalDatum DX' σX' hστX' hσcX').generalFibreProduct.toLocallyRingedSpace ⟶
      (diagonalDatum DX σX hστX hσcX).generalFibreProduct.toLocallyRingedSpace)
    (hinj : Function.Injective ⇑ι.base)
    (htri : diagonal' DX' σX' hστX' hσcX' ≫ ι = eqToHom hsrc ≫ diagonal' DX σX hστX hσcX)
    (hsep : IsSeparated DX σX hστX hσcX) :
    IsSeparated DX' σX' hστX' hσcX' := by
  rw [isSeparated_iff_isClosed_range_diagonal_base] at hsep ⊢
  refine LocallyRingedSpace.isClosed_range_base_of_isClosed_range_comp _ ι hinj ?_
  change IsClosed (Set.range ⇑(diagonal' DX' σX' hστX' hσcX' ≫ ι).base)
  rw [htri, LocallyRingedSpace.range_eqToHom_comp_base]
  exact hsep

end Abstract

/-! ### The diagonal glue of a factor presented by algebra data -/

section Glue

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable [TopologicalSpace R] [IsAdicRing I]
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable (g : ∀ i : J, J → A i)
variable [∀ i : J, TopologicalSpace (A i)]
variable [∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]

/-- **The geometric glue of the diagonal fibre product** `X ×_{Spf I} X` of a factor presented by
algebra data, read at the fixed chart family `A` rather than at the datum's own.

`AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct_eq` says by `rfl` that the datum's
fibre product is this glue's glued object, and the point of the restatement is that
`AlgebraicGeometry.DoubleChartGlue` takes its chart family as a **parameter**: two data over
different bases share nothing a statement can quantify over until the family is one. -/
abbrev diagonalDoubleChartGlue
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toAlgHom.comp (furtherLocSnd I (g j k) (g j i) hI) =
        (furtherLocFst I (g i j) (g i k) hI).comp (τ i j hij).symm.toAlgHom)
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))
    (BX : Type u) [CommRing BX] [Algebra R BX] :
    DoubleChartGlue R I A A :=
  (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
    σ hστ hσc).toBothChartedFibreDatum.toDoubleChartGlue

end Glue

/-! ### The implication at the glued base change -/

section OfAlgebraData

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable [TopologicalSpace R] [IsAdicRing I]
variable {R' : Type u} [CommRing R'] [Algebra R R'] {I' : Ideal R'} (hI' : I'.FG)
variable [TopologicalSpace R'] [IsAdicRing I']
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)]
variable [∀ i, Algebra R (A i)] [∀ i, Algebra R' (A i)] [∀ i, IsScalarTower R R' (A i)]
variable (g : ∀ i : J, J → A i)
variable [∀ i : J, TopologicalSpace (A i)]
variable [∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]
variable [∀ i : J, IsAdicRing (I'.map (algebraMap R' (A i)))]
variable
  (τ : ∀ (i j : J), i ≠ j →
    (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A j))) (g j i)))
  (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
  (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
    (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
  (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    (σ i j k hij hik hjk).symm.toAlgHom.comp (furtherLocSnd I (g j k) (g j i) hI) =
      (furtherLocFst I (g i j) (g i k) hI).comp (τ i j hij).symm.toAlgHom)
  (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
      (σ k i j hik.symm hjk.symm hij)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))
  (τ' : ∀ (i j : J), i ≠ j →
    (awayCompletion (I'.map (algebraMap R' (A i))) (g i j) ≃ₐ[R']
      awayCompletion (I'.map (algebraMap R' (A j))) (g j i)))
  (τ'_symm : ∀ (i j : J) (h : i ≠ j), τ' j i h.symm = (τ' i j h).symm)
  (σ' : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
    (awayCompletion (I'.map (algebraMap R' (A i))) (g i j * g i k) ≃ₐ[R']
      awayCompletion (I'.map (algebraMap R' (A j))) (g j k * g j i)))
  (hστ' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    (σ' i j k hij hik hjk).symm.toAlgHom.comp (furtherLocSnd I' (g j k) (g j i) hI') =
      (furtherLocFst I' (g i j) (g i k) hI').comp (τ' i j hij).symm.toAlgHom)
  (hσc' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    (σ' i j k hij hik hjk).trans ((σ' j k i hjk hij.symm hik.symm).trans
      (σ' k i j hik.symm hjk.symm hij)) =
      AlgEquiv.refl (R := R')
        (A₁ := awayCompletion (I'.map (algebraMap R' (A i))) (g i j * g i k)))
variable {BX : Type u} [CommRing BX] [Algebra R BX]
variable {BX' : Type u} [CommRing BX'] [Algebra R' BX']

omit [TopologicalSpace R] [IsAdicRing I] [Algebra R R'] [∀ i, IsScalarTower R R' (A i)]
  [TopologicalSpace R'] [IsAdicRing I'] in
/-- **The two diagonal data present the same glued factor.** This is
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr` read at the diagonal datum,
whose exposed factor is definitionally the factor it was built from, and pushed onto underlying
locally ringed spaces.

The three inputs are the ones that file asks for: the two induced ideal families agree, and the
single- and double-overlap transitions agree *as functions*. Nothing else about the two bases is
used. -/
theorem xGlued_diagonalDatum_ofAlgebraData_congr
    (hK : (fun i => I'.map (algebraMap R' (A i))) = fun i => I.map (algebraMap R (A i)))
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h)))
    (hσ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (⇑(σ' i j k hij hik hjk)) (⇑(σ i j k hij hik hjk))) :
    (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ'
        hστ' hσc') σ' hστ' hσc').xGlued.toLocallyRingedSpace =
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
        σ hστ hσc).xGlued.toLocallyRingedSpace :=
  congrArg FormalScheme.toLocallyRingedSpace
    (AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr (B := BX) (B' := BX') hI hI' A g
      τ τ_symm σ hστ hσc τ' τ'_symm σ' hστ' hσc' hK hτ hσ)

/-- **Separatedness descends along the glued base change.** One chart family `A`, one away family
`g`, two adic bases `(R, I)` and `(R', I')` with `I' = I·R'`, and two sets of algebra data whose
induced ideal families and transitions agree: if the factor is separated over `Spf R` then it is
separated over `Spf R'`.

The comparison is `AlgebraicGeometry.DoubleChartGlue.baseChange` and its injectivity is
`AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base`, so the square and the saturation
below are that morphism's two hypotheses and are the only things this proof asks of the glue. The
remaining hypothesis is the triangle discussed in this file's *What is not proved here*.

The conclusion is about a **datum**, `AlgebraicGeometry.BothChartedFibreDatumXY.IsSeparated`. It is
not `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf`, which quantifies existentially over a
presentation, and it says nothing about a datum whose charts are not shared between the two
bases. -/
theorem isSeparated_of_isSeparated_baseChange
    (hII' : I.map (algebraMap R R') = I')
    (hK : (fun i => I'.map (algebraMap R' (A i))) = fun i => I.map (algebraMap R (A i)))
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h)))
    (hσ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (⇑(σ' i j k hij hik hjk)) (⇑(σ i j k hij hik hjk)))
    (hsq : DoubleChartGlue.IsBaseChangeOverlapCompatible
      (diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX')
      (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI hII')
    (hsat : DoubleChartGlue.IsBaseChangeOverlapSaturated
      (diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX')
      (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI hII')
    (htri : diagonal' (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ'
          hστ' hσc') σ' hστ' hσc' ≫
        (diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX').baseChange
          (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI' hI hII' hsq =
      eqToHom (xGlued_diagonalDatum_ofAlgebraData_congr hI hI' A g τ τ_symm σ hστ hσc τ' τ'_symm
          σ' hστ' hσc' (BX := BX) (BX' := BX') hK hτ hσ) ≫
        diagonal' (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
          σ hστ hσc)
    (hsep : IsSeparated
      (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc) σ hστ hσc) :
    IsSeparated (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ' hστ' hσc')
      σ' hστ' hσc' := by
  haveI : ∀ p : J × J, IsAdicRing (idealOfDefinition R I (A p.1) (A p.2)) := fun p =>
    CompletedTensorProduct.isAdicRing R I (A p.1) (A p.2) hI
  haveI : ∀ p : J × J, IsAdicRing (idealOfDefinition R' I' (A p.1) (A p.2)) := fun p =>
    CompletedTensorProduct.isAdicRing R' I' (A p.1) (A p.2) hI'
  refine isSeparated_of_isSeparated_of_diagonal_factorization
    (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc) σ hστ hσc
    (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ' hστ' hσc')
    σ' hστ' hσc'
    (xGlued_diagonalDatum_ofAlgebraData_congr hI hI' A g τ τ_symm σ hστ hσc τ' τ'_symm σ' hστ'
      hσc' (BX := BX) (BX' := BX') hK hτ hσ)
    ((diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX').baseChange
      (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI' hI hII' hsq) ?_ htri hsep
  exact DoubleChartGlue.injective_baseChange_base _ _ hI' hI hII' hsq hsat

end OfAlgebraData

end BothChartedFibreDatumXY

end AlgebraicGeometry

end
