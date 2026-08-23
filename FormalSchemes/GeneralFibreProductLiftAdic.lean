import FormalSchemes.AdicOverBaseChart
import FormalSchemes.GeneralFibreProductLiftCharts

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The adic-over-base mediating morphism `Z ⟶ X ×_{Spf R} Y`

The general `fibreLift` (issue 234c, deleted in issue 805) carried two standing
hypotheses: `hZ : Z.LocallyFG`, and the per-piece continuity witness

```
hs : ∀ c, I ≤ (D.bothRefinedChart a b hZ c).J.comap (D.refinedStructHom a b hZ c)
```

asking each piece of the internally chosen refined source cover to be adic on global sections over
the base. As `FormalSchemes.GeneralDiagonalUnconditional` explains, `hs` is *unreachable* for that
cover: `bothRefinedChart` is drawn by `Classical.choice` from a cover carrying no adic-over-base
bound, the witness is erased, and "an open immersion is adic on sections" is **false** in general
(issues 460/468/472/487).

For the **diagonal** this was solved by issue 468 (235c): choose the refined cover from the
adic-over-base neighborhood basis instead of the plain one. Nothing in that argument uses the
diagonal — it needs only that the source is adic over some base morphism `s` and that the `X`-leg
is compatible with `s`. This file is `GeneralDiagonalUnconditional.lean` with the source `Z`, the
two legs `a`, `b` and the base morphism `s` made parameters, so that **every** source gets the same
treatment:

* `nonempty_adicBothChart` — around each point of `Z` there is a refined chart that *also* records
  the adic bound, obtained from `exists_affineChart_subset_adicOverBase` (issue 487);
* `adicBothCharts` / `adicBothCharts_hs` — the chosen family, and the discharged `hs`;
* `fibreLiftAdic` — `fibreLift` with **both** `hZ` and `hs` gone, replaced by the single hypothesis
  `AdicOverBaseLocallyFG Z s` (which supplies `LocallyFG` via `.locallyFG`) together with the base
  compatibility `hbase : a ≫ D.xStructMap = s`;
* `fibreLiftAdic_comp_pr₁` / `_comp_pr₂` — its two projection triangles.

This is the **existence** counterpart of issue 518's `fibreLift_unique_adicOverBase`, which already
runs on `AdicOverBaseLocallyFG`. Between them, the fibre product's universal property is available
for an adic-over-base source with no unreachable side condition on either half.

## Which hypothesis, and why this one

`refinedStructHomOf` is built from `a ≫ D.xStructMap`, so the adic bound the charts must carry is
one over `a ≫ D.xStructMap`. Taking the base morphism `s` as a parameter with
`hbase : a ≫ D.xStructMap = s` — rather than fixing `s := a ≫ D.xStructMap` — is what lets a
consumer supply an `AdicOverBaseLocallyFG` witness it already has in its own spelling, instead of
transporting one along an equality of morphisms into `Spf I`. For the diagonal, `s` is
`D.xStructMap` and `hbase` is `Category.id_comp _`; the diagonal's own `rw [Category.id_comp]` is
exactly this step.

## Faithfulness of the generalisation

`diagonal'_eq_fibreLiftAdic` records that `GeneralDiagonalUnconditional.diagonal'` **is** this
file's `fibreLiftAdic` at `Z := xGlued`, `a = b = 𝟙`, `s := xStructMap`. It is not needed by
anything; it is the check that nothing was quietly weakened in the generalisation, and it lives in
`FormalSchemes.GeneralDiagonalUnconditionalAdic` so that this file stays low in the import graph.

## The deleted `fibreLift` layer (issue 805)

Docstrings throughout this library — here, in `FormalSchemes.GeneralFibreProductLiftCharts`,
`…LiftPiece`, `…LiftUniqueAdic`, `FormalSchemes.GeneralDiagonalUnconditional` and the Tate
`TateFibreProduct*` files — explain the `Of`/`Adic` constructions by comparison with

  `BothChartedFibreDatumXY.fibreLift`, `fibreLiftPiece`, `fibreLift_overlap`,
  `fibreLift_comp_pr₁`/`_comp_pr₂`, `fibreLift_unique`, and `BothChartedFibreDatumXY.diagonal`.

**None of those declarations exist any more.** All of them carried the unreachable `hs`/`hcont`
hypothesis, all of them were superseded by the chart-parametrised layer, and issue 805 deleted them
once issue 798 removed their last consumer. Every mention of those names in this library is
**history**, not a live cross-reference; do not go looking for them, and do not reintroduce an
`hs`-shaped hypothesis in a new one. The live spellings are `fibreLiftOf`, `fibreLiftAdic`,
`fibreLift_unique_adicOverBase` and `diagonal'`.

## The deleted `Classical.choice` refined-cover layer (issue 812)

The same applies one layer down. Docstrings here and in
`FormalSchemes.GeneralFibreProductLiftCharts`, `FormalSchemes.GeneralDiagonalUnconditional`,
`FormalSchemes.AdicOverBaseChart` and `FormalSchemes.BothDatumAdicOverBase` motivate the
`Of`/`Adic` constructions by comparison with

  `BothChartedFibreDatumXY.nonempty_bothRefinedChart`, `bothRefinedChart`, `bothRefinedCover`,
  `xIndex`, `yIndex`, `xFactor`, `yFactor`, `xFactor_comp_ι`, `yFactor_comp_ι`,
  `refinedStructHom`, `refinedAlgebra`, `refinedAlgebra_hIL`, `xAlg`, `yAlg`,

and with a one-sided module `FormalSchemes.GlueOpenCoverFactor`
(`FormalScheme.GlueData.RefinedChart`, `refinedChart`, `refinedCover`, `chartIndex`, `factor`,
`factor_comp_ι`).

**None of those exist any more; the module is gone entirely.** They chose their charts by
`Classical.choice`, which is exactly what made the chosen chart carry no adic-over-base bound
(issue 460) and left every consumer with the unreachable `hs`. Issue 805 removed their last
callers and issue 812 deleted them. Every mention of those names in this library is **history**.

What survives, and is live: the **structure** `BothChartedFibreDatumXY.BothRefinedChart`
(`FormalSchemes.GlueOpenCoverFactorBoth`), now a pure data type over which the whole tower is
parametrised — `bothRefinedCoverOf`, `refinedStructHomOf`, `xAlgOf`, `yAlgOf`, `fibreLiftOf`
(`FormalSchemes.GeneralFibreProductLiftCharts`) — together with the families built to order by
`adicBothCharts` here and by `refinedChartAdic` / `RefinedChartAdic`
(`FormalSchemes.GeneralFibreProductLiftUniqueAdic`). **If you need a cover, build the family you
need and pass it in; do not reintroduce a chosen one.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.12, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorProduct

universe u

namespace AlgebraicGeometry

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {Z : FormalScheme.{u}} (D : BothChartedFibreDatumXY R I hI)
variable (a : Z.toLocallyRingedSpace ⟶ D.xGlued.toLocallyRingedSpace)
variable (b : Z.toLocallyRingedSpace ⟶ D.yGlued.toLocallyRingedSpace)
variable (s : Z.toLocallyRingedSpace ⟶ FormalSpectrum.locallyRingedSpaceObj I)

/-- **Existence of an adic-carrying refined chart** around each point of an arbitrary source `Z`.
Mirrors `nonempty_bothRefinedChart`, but draws the chart from the *adic-over-base* neighborhood
basis (`exists_affineChart_subset_adicOverBase`, issue 487) of `Z` relative to the base morphism
`s`, so the chart additionally records the bound `I ≤ J.comap (Γ (map ≫ a ≫ xStructMap))` — exactly
`fibreLift`'s per-piece continuity witness `hs`.

The only place the base compatibility `hbase` is used is in transporting the returned bound, which
is stated over `s`, into the bound over `a ≫ D.xStructMap` that `refinedStructHomOf` asks for. -/
theorem nonempty_adicBothChart (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s)
    (hbase : a ≫ D.xStructMap = s) (z : Z) :
    Nonempty { chart : BothRefinedChart D a b z //
      I ≤ chart.J.comap (globalSectionsMap I chart.J (chart.map ≫ a ≫ D.xStructMap)) } := by
  obtain ⟨i, y, hy⟩ := D.xFormalGlueData.ι_jointly_surjective (a.base z)
  obtain ⟨j, w, hw⟩ := D.yFormalGlueData.ι_jointly_surjective (b.base z)
  have hUopen : IsOpen
      ((a.base ⁻¹' Set.range (D.xFormalGlueData.ι i).base) ∩
        (b.base ⁻¹' Set.range (D.yFormalGlueData.ι j).base)) :=
    ((D.xFormalGlueData.ι_isOpenImmersion i).base_open.isOpen_range.preimage
        a.base.hom.continuous).inter
      ((D.yFormalGlueData.ι_isOpenImmersion j).base_open.isOpen_range.preimage
        b.base.hom.continuous)
  have hzU : z ∈
      ((a.base ⁻¹' Set.range (D.xFormalGlueData.ι i).base) ∩
        (b.base ⁻¹' Set.range (D.yFormalGlueData.ι j).base)) := by
    refine ⟨?_, ?_⟩ <;> simp only [Set.mem_preimage]
    · exact ⟨y, hy⟩
    · exact ⟨w, hw⟩
  obtain ⟨S, _, _, J, _, f, hJfg, hzmem, hsub, hoi, hadic⟩ :=
    Z.exists_affineChart_subset_adicOverBase s hZadic z _ hUopen hzU
  refine ⟨⟨{ xIdx := i, yIdx := j, R := S, J := J, map := f, fg := hJfg, mem := hzmem,
             xsubset := fun _ hp => (hsub hp).1, ysubset := fun _ hp => (hsub hp).2 }, ?_⟩⟩
  rw [hbase]
  exact hadic

/-- The chosen adic-carrying refined chart family for an arbitrary source, via `Classical.choice`.
Its retained bound is recovered by `adicBothCharts_hs`. -/
def adicBothCharts (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s)
    (hbase : a ≫ D.xStructMap = s) (z : Z) :
    BothRefinedChart D a b z :=
  (D.nonempty_adicBothChart a b s hZadic hbase z).some.1

/-- **The discharged continuity witness `hs`, for an arbitrary source.** Each piece of the
adic-carrying refined cover `adicBothCharts` is adic on global sections over the base, by
construction. -/
theorem adicBothCharts_hs (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s)
    (hbase : a ≫ D.xStructMap = s) (z : Z) :
    I ≤ (D.adicBothCharts a b s hZadic hbase z).J.comap
      (D.refinedStructHomOf a b (D.adicBothCharts a b s hZadic hbase) z) :=
  (D.nonempty_adicBothChart a b s hZadic hbase z).some.2

/-- **The adic-over-base mediating morphism** `Z ⟶ X ×_{Spf R} Y`, defined as `fibreLiftOf` over
the adic-carrying refined cover `adicBothCharts`, whose continuity witness is discharged by
`adicBothCharts_hs`.

Compared with `fibreLift` this drops **both** `hZ : Z.LocallyFG` and the unreachable `hs`, at the
cost of the single hypothesis `AdicOverBaseLocallyFG Z s` plus the base compatibility `hbase`. -/
def fibreLiftAdic (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s)
    (hbase : a ≫ D.xStructMap = s)
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap) :
    Z.toLocallyRingedSpace ⟶ D.generalFibreProduct.toLocallyRingedSpace :=
  D.fibreLiftOf a b (D.adicBothCharts a b s hZadic hbase) hV hf ht hcomm
    (D.adicBothCharts_hs a b s hZadic hbase)

/-- **`fibreLiftAdic` recovers the `X`-leg after the first projection.** -/
theorem fibreLiftAdic_comp_pr₁ (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s)
    (hbase : a ≫ D.xStructMap = s)
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap) :
    D.fibreLiftAdic a b s hZadic hbase hV hf ht hcomm ≫ D.pr₁ hV hf ht = a :=
  D.fibreLiftOf_comp_pr₁ a b (D.adicBothCharts a b s hZadic hbase) hV hf ht hcomm
    (D.adicBothCharts_hs a b s hZadic hbase)

/-- **`fibreLiftAdic` recovers the `Y`-leg after the second projection.** -/
theorem fibreLiftAdic_comp_pr₂ (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s)
    (hbase : a ≫ D.xStructMap = s)
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap) :
    D.fibreLiftAdic a b s hZadic hbase hV hf ht hcomm ≫ D.pr₂ hV hf ht = b :=
  D.fibreLiftOf_comp_pr₂ a b (D.adicBothCharts a b s hZadic hbase) hV hf ht hcomm
    (D.adicBothCharts_hs a b s hZadic hbase)

end BothChartedFibreDatumXY

end AlgebraicGeometry

end
