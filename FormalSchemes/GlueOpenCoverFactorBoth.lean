import FormalSchemes.GeneralFibreProductBothExposeXY

set_option linter.style.header false

/-!
# Two-sided refined charts for the general fibre product — the chart data type

For a two-sided fibre-product datum `D : BothChartedFibreDatumXY R I hI` — with exposed glued
factors `X := D.xGlued` (charts `Spf(A i)`, `i : D.JX`, glue inclusions `D.xFormalGlueData.ι i`)
and `Y := D.yGlued` (charts `Spf(B j)`, `j : D.JY`, glue inclusions `D.yFormalGlueData.ι j`) — and a
pair of morphisms `a : Z ⟶ X`, `b : Z ⟶ Y`, the universal property of `X ×_{Spf R} Y`
(EGA I §10.7, issue 234) is assembled by descent along a cover of `Z`. An arbitrary affine chart of
`Z` need not map into a single glued chart of either factor, so the cover has to be **refined**: at
each point `z` one wants an affine chart of `Z` landing inside
`a⁻¹(range (D.xFormalGlueData.ι i)) ∩ b⁻¹(range (D.yFormalGlueData.ι j))` for a single pair
`(i, j)`, so that both restrictions `map ≫ a` and `map ≫ b` factor through a single `X`-chart and a
single `Y`-chart simultaneously — the pair of charts whose double completed tensor product is the
product chart `Spf(A_i ⊗̂_R B_j)` that `chartLift` (issue 398) targets.

This file supplies the **data type** of such a chart, and nothing else.

## Main definitions

* `BothChartedFibreDatumXY.BothRefinedChart`: the per-point bundled data — a finitely generated
  affine chart of `Z` around `z` whose range lies in `a⁻¹(range (D.xFormalGlueData.ι i))` **and**
  `b⁻¹(range (D.yFormalGlueData.ι j))` for a chosen pair `(i, j)`.

## Why there is no `bothRefinedCover` here any more (issue 812)

This file used to also *produce* such a chart at every point, by `Classical.choice` from an
existence lemma, and assemble the results into an `OpenCover Z`
(`nonempty_bothRefinedChart`, `bothRefinedChart`, `bothRefinedCover`, `xIndex`, `yIndex`,
`xFactor`, `yFactor` and their factorization lemmas, plus a one-sided analogue in a module
`FormalSchemes.GlueOpenCoverFactor`). That layer is gone.

The reason is issue 460: a chart drawn by choice carries no *adic-over-base* bound, and
`Classical.choice` erases which witness was taken, so the bound cannot be recovered afterwards.
Every downstream consumer therefore had to carry an unreachable hypothesis (issues 468/472/487),
and the fix was to parametrise the whole tower over an **arbitrary user-supplied chart family**
`charts : ∀ z, BothRefinedChart D a b z` (`FormalSchemes.GeneralFibreProductLiftCharts`), with the
families that actually occur built to order — `refinedChartAdic` /
`FormalSchemes.GeneralFibreProductLiftUniqueAdic` from an adic-over-base neighbourhood basis, and
`adicBothCharts` / `FormalSchemes.GeneralFibreProductLiftAdic` for the fibre lift. After issue 805
deleted the last hypothesis-carrying consumers, the choice-based layer had no callers at all.

Keeping it would have been an active trap rather than dead weight: it is the shorter name, it
type-checks, and it leads to a hypothesis nobody can discharge. **If you want a cover here, build
the family you need and pass it in.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable {Z : FormalScheme.{u}} (D : BothChartedFibreDatumXY R I hI)
variable (a : Z.toLocallyRingedSpace ⟶ D.xGlued.toLocallyRingedSpace)
variable (b : Z.toLocallyRingedSpace ⟶ D.yGlued.toLocallyRingedSpace)

/-- The per-point data refining the source cover of `Z` along the pair `a : Z ⟶ D.xGlued`,
`b : Z ⟶ D.yGlued`: a finitely generated affine open-immersion chart of `Z` around `z` whose range
lies inside the preimage `a⁻¹(range (D.xFormalGlueData.ι xIdx))` of a single `X`-chart **and**
inside the preimage `b⁻¹(range (D.yFormalGlueData.ι yIdx))` of a single `Y`-chart. -/
structure BothRefinedChart (z : Z) where
  /-- The selected `X`-chart index. -/
  xIdx : D.JX
  /-- The selected `Y`-chart index. -/
  yIdx : D.JY
  /-- The underlying ring of the affine chart of `Z`. -/
  R : Type u
  /-- Its commutative ring structure. -/
  [commRing : CommRing R]
  /-- Its topology. -/
  [topR : TopologicalSpace R]
  /-- The ideal of definition. -/
  J : Ideal R
  /-- `(R, J)` is an adic ring, so `Spf J` is an affine formal scheme. -/
  [adic : IsAdicRing J]
  /-- The chart, an open immersion `Spf J ↪ Z`. -/
  map : FormalSpectrum.locallyRingedSpaceObj J ⟶ Z.toLocallyRingedSpace
  /-- The ideal of definition is finitely generated (needed for the basic-open chart). -/
  fg : J.FG
  /-- The chart covers `z`. -/
  mem : z ∈ Set.range map.base
  /-- The chart lands inside the preimage of the `xIdx`-th `X`-chart. -/
  xsubset : Set.range map.base ⊆ a.base ⁻¹' Set.range (D.xFormalGlueData.ι xIdx).base
  /-- The chart lands inside the preimage of the `yIdx`-th `Y`-chart. -/
  ysubset : Set.range map.base ⊆ b.base ⁻¹' Set.range (D.yFormalGlueData.ι yIdx).base
  /-- The chart is an open immersion. -/
  [isOpenImmersion : LocallyRingedSpace.IsOpenImmersion map]

attribute [instance] BothRefinedChart.commRing BothRefinedChart.topR BothRefinedChart.adic
  BothRefinedChart.isOpenImmersion

end AlgebraicGeometry.BothChartedFibreDatumXY

end
