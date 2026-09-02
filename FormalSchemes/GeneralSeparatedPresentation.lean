import FormalSchemes.ClosedImmersionIso
import FormalSchemes.GeneralDiagonalUnconditionalAdic
import FormalSchemes.GeneralFibreProductCompare
import FormalSchemes.GeneralSeparated

set_option linter.style.header false

/-!
# Separatedness does not depend on the presentation

`FormalScheme`-level separatedness (`FormalSchemes.GeneralSeparated`) is **not** a predicate on a
formal scheme. `BothChartedFibreDatumXY.IsSeparated DX σX hστX hσcX` is a predicate on a
*presentation*: an affine charted datum `DX` together with its double-overlap cocycle data, saying
that the general diagonal `Δ' : X ⟶ X ×_{Spf R} X` built from those charts is a closed immersion.
Two chart systems presenting the same `X` therefore give two different propositions, and until now
nothing related them.

This file relates them. If the two glued factors are isomorphic over `Spf R` — an isomorphism of
locally ringed spaces `e : X₁ ≅ X₂` with `e.hom ≫ xStructMap₂ = xStructMap₁` — then

```
isSeparated_iff : IsSeparated DX₁ … ↔ IsSeparated DX₂ …
```

**Separatedness over `Spf R` is a property of the formal scheme and its structural morphism, not of
the charts used to write them down.**

## The argument

The diagonal is the mediating morphism of the identity pair (`diagonal'_eq_fibreLiftAdic`,
`FormalSchemes.GeneralDiagonalUnconditionalAdic`), so it is characterised by its two projection
triangles. `compareIso` (`FormalSchemes.GeneralFibreProductCompare`) transports the fibre product
along `e`, and `diagonal'_transport` says the two diagonals correspond under `e` and `compareIso`:

```
Δ'₂ = e.inv ≫ Δ'₁ ≫ compareIso.hom
```

proved by `fibreLift_unique_adicOverBase` at the second datum. Note that the adic-over-base witness
that step needs is `adicOverBase_xStructMap` — the witness for the glued **factor**
(`FormalSchemes.BothDatumAdicOverBase`, issues 468/487) — and not issue 832's witness for the fibre
product, because the source of the two competing morphisms is `xGlued`, not `X ×_R Y`. Issue 832's
witness is used one level down, inside `compareIso`.

Closed immersions are stable under composition with an isomorphism on either side
(`FormalScheme.IsClosedImmersion.iso_comp`, `.comp_iso`), which turns that equation into the
`Iff`. Getting there needs the two `LocallyRingedSpace` isomorphisms as isomorphisms of *formal
schemes*; since formal schemes are a full subcategory of locally ringed spaces, both legs are just
`FormalScheme.Hom.mk` and the round trips are `FormalScheme.Hom.ext'`, packaged as
`FormalScheme.isoOfLRSIso` (added to `FormalSchemes.ClosedImmersionIso` beside the new
`FormalScheme.isIso_of_isIso_toLRSHom`). That packaging, rather than `asIso` of the latter, is what
keeps `.hom` and `.inv` *definitionally* `FormalScheme.Hom.mk` of `e.hom` and `e.inv`, which is what
`schemeDiagonal'_transport`'s `Hom.ext'` proof needs — `asIso`'s `.inv` is only propositionally
`Hom.mk e.inv`.

## The `xGlued` spelling wall

`e` is taken at `(diagonalDatum DX₁ …).xGlued` rather than at `DX₁.xGlued`, even though
`ofFactors_xGlued` says the two are `rfl`. This is the wall documented in
`FormalSchemes.TateFibreProductHom`: a composite mixing the two spellings is not type-correct at
`instances` transparency and `rw` refuses to build a motive across it, reporting
`LocallyRingedSpace.instQuiver` against `LocallyRingedSpace.instCategory.toQuiver`. Stating the
hypothesis in `diagonal'`'s own spelling makes every `rw` in this file go through.

`isSeparated_iff_of_xGlued_iso` is the same statement in the `DX₁.xGlued` spelling a consumer will
actually hold, proved by `exact` on the first — the elaborator checks that at default transparency,
where the two spellings are freely interchangeable. This is `TateFibreProductHom`'s prescribed
remedy: restate once in each spelling rather than transport.

## What this does not do

It does not *redefine* `BothChartedFibreDatumXY.IsSeparated` as a predicate on a `FormalScheme`.
That is a real design question, it touches every §10.15 consumer including the Tate tower, and it
should be argued on its own now that this theorem exists to support it.

## Main results

* `BothChartedFibreDatumXY.compareDiagonalIso`: `compareIso` at a diagonal datum, where the two
  factors coincide.
* `BothChartedFibreDatumXY.diagonal'_transport`: the two general diagonals correspond.
* `BothChartedFibreDatumXY.schemeDiagonal'_transport`: the same at the `FormalScheme` level.
* `BothChartedFibreDatumXY.isSeparated_of_isSeparated`, `isSeparated_iff`,
  `isSeparated_iff_of_xGlued_iso`: **separatedness is independent of the presentation**.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum Topology
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry.BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {BX₁ : Type u} [CommRing BX₁] [Algebra R BX₁]
variable {BX₂ : Type u} [CommRing BX₂] [Algebra R BX₂]
variable (DX₁ : AffineChartedFibreDatumX R I hI BX₁)
variable
  (σX₁ : letI := DX₁.commRing; letI := DX₁.algebra;
    ∀ (i i' i'' : DX₁.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R (DX₁.A i))) (DX₁.g i i' * DX₁.g i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (DX₁.A i'))) (DX₁.g i' i'' * DX₁.g i' i)))
  (hστX₁ : letI := DX₁.commRing; letI := DX₁.algebra;
    ∀ (i i' i'' : DX₁.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX₁ i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (DX₁.g i' i'') (DX₁.g i' i) hI) =
      (furtherLocFst I (DX₁.g i i') (DX₁.g i i'') hI).comp (DX₁.τ i i' h1).symm.toAlgHom)
  (hσcX₁ : letI := DX₁.commRing; letI := DX₁.algebra;
    ∀ (i i' i'' : DX₁.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX₁ i i' i'' h1 h2 h3).trans ((σX₁ i' i'' i h3 h1.symm h2.symm).trans
      (σX₁ i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (DX₁.A i))) (DX₁.g i i' * DX₁.g i i'')))
variable (DX₂ : AffineChartedFibreDatumX R I hI BX₂)
variable
  (σX₂ : letI := DX₂.commRing; letI := DX₂.algebra;
    ∀ (i i' i'' : DX₂.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R (DX₂.A i))) (DX₂.g i i' * DX₂.g i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (DX₂.A i'))) (DX₂.g i' i'' * DX₂.g i' i)))
  (hστX₂ : letI := DX₂.commRing; letI := DX₂.algebra;
    ∀ (i i' i'' : DX₂.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX₂ i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (DX₂.g i' i'') (DX₂.g i' i) hI) =
      (furtherLocFst I (DX₂.g i i') (DX₂.g i i'') hI).comp (DX₂.τ i i' h1).symm.toAlgHom)
  (hσcX₂ : letI := DX₂.commRing; letI := DX₂.algebra;
    ∀ (i i' i'' : DX₂.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX₂ i i' i'' h1 h2 h3).trans ((σX₂ i' i'' i h3 h1.symm h2.symm).trans
      (σX₂ i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (DX₂.A i))) (DX₂.g i i' * DX₂.g i i'')))
variable
  (eX : (diagonalDatum DX₁ σX₁ hστX₁ hσcX₁).xGlued.toLocallyRingedSpace ≅
    (diagonalDatum DX₂ σX₂ hστX₂ hσcX₂).xGlued.toLocallyRingedSpace)
  (hX : eX.hom ≫ (diagonalDatum DX₂ σX₂ hστX₂ hσcX₂).xStructMap =
    (diagonalDatum DX₁ σX₁ hστX₁ hσcX₁).xStructMap)

/-- **The comparison isomorphism of two presentations of `X ×_{Spf R} X`.** `compareIso` at the two
diagonal data, with the same `e` used on both sides: for a diagonal datum the two exposed factors
and the two structural morphisms are definitionally `DX`'s (`ofFactors_xGlued`/`ofFactors_yGlued`
are `rfl`), so no separate `Y`-side input is needed. -/
def compareDiagonalIso :
    (diagonalDatum DX₁ σX₁ hστX₁ hσcX₁).generalFibreProduct.toLocallyRingedSpace ≅
      (diagonalDatum DX₂ σX₂ hστX₂ hσcX₂).generalFibreProduct.toLocallyRingedSpace :=
  compareIso (D₁ := diagonalDatum DX₁ σX₁ hστX₁ hσcX₁)
    (D₂ := diagonalDatum DX₂ σX₂ hστX₂ hσcX₂) eX eX hX hX
    (ofFactors_hV DX₁ DX₁ σX₁ σX₁ hστX₁ hστX₁ hσcX₁ hσcX₁)
    (ofFactors_hf DX₁ DX₁ σX₁ σX₁ hστX₁ hστX₁ hσcX₁ hσcX₁)
    (ofFactors_ht DX₁ DX₁ σX₁ σX₁ hστX₁ hστX₁ hσcX₁ hσcX₁)
    (ofFactors_hV DX₂ DX₂ σX₂ σX₂ hστX₂ hστX₂ hσcX₂ hσcX₂)
    (ofFactors_hf DX₂ DX₂ σX₂ σX₂ hστX₂ hστX₂ hσcX₂ hσcX₂)
    (ofFactors_ht DX₂ DX₂ σX₂ σX₂ hστX₂ hστX₂ hσcX₂ hσcX₂)

/-- **The two general diagonals correspond under `e`.** The right-hand side has the same two
projection triangles as `Δ'₂` — each collapses through `compareIso_hom_comp_pr₁`/`_pr₂` and
`diagonal'_comp_pr₁`/`_pr₂` to `e.inv ≫ e.hom = 𝟙` — so `fibreLift_unique_adicOverBase` at the
second datum identifies them.

The adic-over-base witness here is `adicOverBase_xStructMap`, the witness of the glued **factor**,
because the source of the two competing morphisms is `xGlued`. Issue 832's witness for the fibre
product itself is used one level down, inside `compareDiagonalIso`. -/
theorem diagonal'_transport :
    diagonal' DX₂ σX₂ hστX₂ hσcX₂ =
      eX.inv ≫ diagonal' DX₁ σX₁ hστX₁ hσcX₁ ≫
        (compareDiagonalIso DX₁ σX₁ hστX₁ hσcX₁ DX₂ σX₂ hστX₂ hσcX₂ eX hX).hom := by
  have hpr₁ : (eX.inv ≫ diagonal' DX₁ σX₁ hστX₁ hσcX₁ ≫
      (compareDiagonalIso DX₁ σX₁ hστX₁ hσcX₁ DX₂ σX₂ hστX₂ hσcX₂ eX hX).hom) ≫
      (diagonalDatum DX₂ σX₂ hστX₂ hσcX₂).pr₁
        (ofFactors_hV DX₂ DX₂ σX₂ σX₂ hστX₂ hστX₂ hσcX₂ hσcX₂)
        (ofFactors_hf DX₂ DX₂ σX₂ σX₂ hστX₂ hστX₂ hσcX₂ hσcX₂)
        (ofFactors_ht DX₂ DX₂ σX₂ σX₂ hστX₂ hστX₂ hσcX₂ hσcX₂) =
      𝟙 (diagonalDatum DX₂ σX₂ hστX₂ hσcX₂).xGlued.toLocallyRingedSpace := by
    rw [Category.assoc, Category.assoc, compareDiagonalIso, compareIso_hom_comp_pr₁,
      reassoc_of% (diagonal'_comp_pr₁ DX₁ σX₁ hστX₁ hσcX₁)]
    simp
  have hpr₂ : (eX.inv ≫ diagonal' DX₁ σX₁ hστX₁ hσcX₁ ≫
      (compareDiagonalIso DX₁ σX₁ hστX₁ hσcX₁ DX₂ σX₂ hστX₂ hσcX₂ eX hX).hom) ≫
      (diagonalDatum DX₂ σX₂ hστX₂ hσcX₂).pr₂
        (ofFactors_hV DX₂ DX₂ σX₂ σX₂ hστX₂ hστX₂ hσcX₂ hσcX₂)
        (ofFactors_hf DX₂ DX₂ σX₂ σX₂ hστX₂ hστX₂ hσcX₂ hσcX₂)
        (ofFactors_ht DX₂ DX₂ σX₂ σX₂ hστX₂ hστX₂ hσcX₂ hσcX₂) =
      𝟙 (diagonalDatum DX₂ σX₂ hστX₂ hσcX₂).xGlued.toLocallyRingedSpace := by
    rw [Category.assoc, Category.assoc, compareDiagonalIso, compareIso_hom_comp_pr₂,
      reassoc_of% (diagonal'_comp_pr₂ DX₁ σX₁ hστX₁ hσcX₁)]
    simp
  refine (diagonalDatum DX₂ σX₂ hστX₂ hσcX₂).fibreLift_unique_adicOverBase
    (ofFactors_hV DX₂ DX₂ σX₂ σX₂ hστX₂ hστX₂ hσcX₂ hσcX₂)
    (ofFactors_hf DX₂ DX₂ σX₂ σX₂ hστX₂ hστX₂ hσcX₂ hσcX₂)
    (ofFactors_ht DX₂ DX₂ σX₂ σX₂ hστX₂ hστX₂ hσcX₂ hσcX₂) _ _
    (diagonalDatum DX₂ σX₂ hστX₂ hσcX₂).xStructMap
    (adicOverBase_xStructMap (diagonalDatum DX₂ σX₂ hστX₂ hσcX₂)) ?_ ?_ ?_
  · rw [diagonal'_comp_pr₁, hpr₁]
  · rw [diagonal'_comp_pr₂, hpr₂]
  · rw [← Category.assoc, diagonal'_comp_pr₁, Category.id_comp]

/-- **`compareDiagonalIso` as an isomorphism of formal schemes**, via
`FormalScheme.isoOfLRSIso`. -/
def compareDiagonalSchemeIso :
    (diagonalDatum DX₁ σX₁ hστX₁ hσcX₁).generalFibreProduct ≅
      (diagonalDatum DX₂ σX₂ hστX₂ hσcX₂).generalFibreProduct :=
  FormalScheme.isoOfLRSIso (compareDiagonalIso DX₁ σX₁ hστX₁ hσcX₁ DX₂ σX₂ hστX₂ hσcX₂ eX hX)

/-- **The factor isomorphism as an isomorphism of formal schemes.** -/
def xGluedSchemeIso :
    (diagonalDatum DX₁ σX₁ hστX₁ hσcX₁).xGlued ≅ (diagonalDatum DX₂ σX₂ hστX₂ hσcX₂).xGlued :=
  FormalScheme.isoOfLRSIso eX

/-- **`BothChartedFibreDatumXY.diagonal'_transport` at the `FormalScheme` level.**
`BothChartedFibreDatumXY.schemeDiagonal'` is `FormalScheme.Hom.mk` of
`BothChartedFibreDatumXY.diagonal'` and both sides of the equation have the same underlying
locally-ringed-space morphism, so this is `Hom.ext'` on
`BothChartedFibreDatumXY.diagonal'_transport`. -/
theorem schemeDiagonal'_transport :
    schemeDiagonal' DX₂ σX₂ hστX₂ hσcX₂ =
      (xGluedSchemeIso DX₁ σX₁ hστX₁ hσcX₁ DX₂ σX₂ hστX₂ hσcX₂ eX).inv ≫
        schemeDiagonal' DX₁ σX₁ hστX₁ hσcX₁ ≫
          (compareDiagonalSchemeIso DX₁ σX₁ hστX₁ hσcX₁ DX₂ σX₂ hστX₂ hσcX₂ eX hX).hom :=
  FormalScheme.Hom.ext' (diagonal'_transport DX₁ σX₁ hστX₁ hσcX₁ DX₂ σX₂ hστX₂ hσcX₂ eX hX)

include eX hX in
/-- **Separatedness transports along an isomorphism of the glued factor over the base.** Rewrite
the second diagonal by `schemeDiagonal'_transport` and apply stability of closed immersions under
composition with an isomorphism on either side. -/
theorem isSeparated_of_isSeparated (h : IsSeparated DX₁ σX₁ hστX₁ hσcX₁) :
    IsSeparated DX₂ σX₂ hστX₂ hσcX₂ := by
  change FormalScheme.IsClosedImmersion (schemeDiagonal' DX₂ σX₂ hστX₂ hσcX₂)
  rw [schemeDiagonal'_transport DX₁ σX₁ hστX₁ hσcX₁ DX₂ σX₂ hστX₂ hσcX₂ eX hX]
  exact FormalScheme.IsClosedImmersion.iso_comp _ (h.comp_iso _)

include eX hX in
/-- **Separatedness is independent of the presentation.** Two affine charted data whose glued
factors are isomorphic over `Spf R` are separated or not together. The backward direction is the
forward one at `e.symm`, whose structural compatibility is `inv_comp_xStructMap`. -/
theorem isSeparated_iff :
    IsSeparated DX₁ σX₁ hστX₁ hσcX₁ ↔ IsSeparated DX₂ σX₂ hστX₂ hσcX₂ :=
  ⟨isSeparated_of_isSeparated DX₁ σX₁ hστX₁ hσcX₁ DX₂ σX₂ hστX₂ hσcX₂ eX hX,
    isSeparated_of_isSeparated DX₂ σX₂ hστX₂ hσcX₂ DX₁ σX₁ hστX₁ hσcX₁ eX.symm
      (inv_comp_xStructMap eX hX)⟩

/-- **`isSeparated_iff` in the `DX.xGlued` spelling.** The same statement with the isomorphism
given between the two data's own glued factors rather than their diagonal data's; the two spellings
are `rfl` (`ofFactors_xGlued`), and stating both is the remedy prescribed in
`FormalSchemes.TateFibreProductHom` for the `instances`-transparency wall described in the module
docstring. This is the form a consumer will hold. -/
theorem isSeparated_iff_of_xGlued_iso
    (e : DX₁.xGlued.toLocallyRingedSpace ≅ DX₂.xGlued.toLocallyRingedSpace)
    (he : e.hom ≫ DX₂.xStructMap = DX₁.xStructMap) :
    IsSeparated DX₁ σX₁ hστX₁ hσcX₁ ↔ IsSeparated DX₂ σX₂ hστX₂ hσcX₂ :=
  isSeparated_iff DX₁ σX₁ hστX₁ hσcX₁ DX₂ σX₂ hστX₂ hσcX₂ e he

end AlgebraicGeometry.BothChartedFibreDatumXY

end
