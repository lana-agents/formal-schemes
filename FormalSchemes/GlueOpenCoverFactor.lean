import FormalSchemes.LocallyFG
import FormalSchemes.OpenCover

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Refining a source cover along a morphism into a glued formal scheme

Let `D : FormalScheme.GlueData` with glued object `G := D.gluedFormalScheme`, charts `D.U i` and
open-immersion inclusions `D.ι i`, and let `a : Z ⟶ G` be a morphism out of a locally
finitely-generated formal scheme `Z`. An arbitrary affine chart of `Z` need not map into a single
glued chart of `G`, so the plain `affineCover Z` is not fine enough for source-side descent
(EGA I §10.7, the general fibre-product universal property). This file refines the cover: every
point `z` gets an affine chart of `Z` whose range lands inside `a⁻¹(range (D.ι i))` for a single
`i`, so that the restriction of `a` to that piece **factors through the chart `D.U i`**.

## Main definitions and results

* `FormalScheme.GlueData.RefinedChart`: the per-point bundled data — a finitely generated affine
  chart of `Z` around `z` whose range lies in `a⁻¹(range (D.ι i))` for a chosen index `i`.
* `FormalScheme.GlueData.refinedCover`: the resulting `OpenCover Z`, indexed by the points of `Z`.
* `FormalScheme.GlueData.chartIndex`: the selected glued-chart index for each cover piece.
* `FormalScheme.GlueData.factor` / `factor_comp_ι`: the factorization of `map c ≫ a` through the
  chart `D.U (chartIndex c)`, obtained from the universal property of the open immersion `D.ι`.

These are the source-side inputs consumed by 234c (the general `fibreLift` assembly, via
`OpenCover.glueMorphisms`) and 234d (its uniqueness, via `OpenCover.hom_ext`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.FormalScheme.GlueData

variable {Z : FormalScheme.{u}} (D : GlueData.{u})
  (a : Z.toLocallyRingedSpace ⟶ D.gluedFormalScheme.toLocallyRingedSpace)

/-- The per-point data refining the source cover of `Z` along `a : Z ⟶ D.gluedFormalScheme`:
a finitely generated affine open-immersion chart of `Z` around `z` whose range lies inside the
preimage `a⁻¹(range (D.ι idx))` of a single glued chart. -/
structure RefinedChart (z : Z) where
  /-- The selected glued-chart index. -/
  idx : D.toLocallyRingedSpaceGlueData.J
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
  /-- The chart lands inside the preimage of the `idx`-th glued chart. -/
  subset : Set.range map.base ⊆ a.base ⁻¹' Set.range (D.ι idx).base
  /-- The chart is an open immersion. -/
  [isOpenImmersion : LocallyRingedSpace.IsOpenImmersion map]

attribute [instance] RefinedChart.commRing RefinedChart.topR RefinedChart.adic
  RefinedChart.isOpenImmersion

variable {D a}

/-- A refined chart exists around every point of a `LocallyFG` source: the glued charts jointly
cover `a z`, giving an index `i`; the preimage `a⁻¹(range (D.ι i))` is open and contains `z`, so
the affine-chart neighborhood basis (`exists_affineChart_subset`) supplies a finitely generated
affine chart landing inside it. -/
theorem nonempty_refinedChart (hZ : Z.LocallyFG) (z : Z) :
    Nonempty (RefinedChart D a z) := by
  obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective (a.base z)
  have hUopen : IsOpen (a.base ⁻¹' Set.range (D.ι i).base) :=
    (D.ι_isOpenImmersion i).base_open.isOpen_range.preimage a.base.hom.continuous
  have hzU : z ∈ a.base ⁻¹' Set.range (D.ι i).base := by
    simp only [Set.mem_preimage]; exact ⟨y, hy⟩
  obtain ⟨R, _, _, J, _, f, hJfg, hzmem, hsub, hoi⟩ :=
    Z.exists_affineChart_subset hZ z _ hUopen hzU
  exact ⟨{ idx := i, R := R, J := J, map := f, fg := hJfg, mem := hzmem, subset := hsub }⟩

variable (D a)

/-- A chosen refined chart around each point of a `LocallyFG` source, via `Classical.choice`. -/
def refinedChart (hZ : Z.LocallyFG) (z : Z) : RefinedChart D a z :=
  (nonempty_refinedChart hZ z).some

/-- The **refined open cover** of a locally finitely-generated formal scheme `Z` along a morphism
`a : Z ⟶ D.gluedFormalScheme`: indexed by the points of `Z`, the piece at `z` is the finitely
generated affine chart `refinedChart D a hZ z`, whose range lands inside a single glued chart. -/
def refinedCover (hZ : Z.LocallyFG) : OpenCover Z where
  J := Z
  obj z := FormalScheme.Spf (D.refinedChart a hZ z).J
  map z := Hom.mk (D.refinedChart a hZ z).map
  f z := z
  covers z := (D.refinedChart a hZ z).mem
  isOpenImmersion z := (D.refinedChart a hZ z).isOpenImmersion

/-- The glued-chart index selected for each piece of the refined cover. -/
def chartIndex (hZ : Z.LocallyFG) (c : (D.refinedCover a hZ).J) :
    D.toLocallyRingedSpaceGlueData.J :=
  (D.refinedChart a hZ c).idx

/-- The range of `map c ≫ a` on a refined-cover piece is contained in the range of the selected
glued chart `D.ι (chartIndex c)` — the containment that makes the factorization possible. -/
theorem refinedChart_range_comp_subset (hZ : Z.LocallyFG) (c : (D.refinedCover a hZ).J) :
    Set.range ((D.refinedChart a hZ c).map ≫ a).base ⊆
      Set.range (D.ι (D.chartIndex a hZ c)).base := by
  rintro w ⟨s, rfl⟩
  simp only [LocallyRingedSpace.comp_base, TopCat.comp_app]
  exact (D.refinedChart a hZ c).subset ⟨s, rfl⟩

/-- The **chart-wise factorization** of the source cover: on the piece `c`, the restriction
`map c ≫ a` of `a` factors through the single glued chart `D.U (chartIndex c)`. The lift is the
universal map from the open immersion `D.ι (chartIndex c)`. -/
def factor (hZ : Z.LocallyFG) (c : (D.refinedCover a hZ).J) :
    FormalSpectrum.locallyRingedSpaceObj (D.refinedChart a hZ c).J ⟶
      D.toLocallyRingedSpaceGlueData.U (D.chartIndex a hZ c) :=
  LocallyRingedSpace.IsOpenImmersion.lift (D.ι (D.chartIndex a hZ c))
    ((D.refinedChart a hZ c).map ≫ a) (D.refinedChart_range_comp_subset a hZ c)

/-- The factorization is compatible with the glued inclusion: `factor c ≫ D.ι (chartIndex c)`
recovers `map c ≫ a`. This is `lift_fac` for the open immersion `D.ι (chartIndex c)`. -/
@[reassoc]
theorem factor_comp_ι (hZ : Z.LocallyFG) (c : (D.refinedCover a hZ).J) :
    D.factor a hZ c ≫ D.ι (D.chartIndex a hZ c) = (D.refinedChart a hZ c).map ≫ a :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry.FormalScheme.GlueData

end
