import FormalSchemes.GlueOpenCoverFactor
import FormalSchemes.GeneralFibreProductBothExposeXY

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Two-sided refinement of a source cover for the general fibre product

For a two-sided fibre-product datum `D : BothChartedFibreDatumXY R I hI` — with exposed glued
factors `X := D.xGlued` (charts `Spf(A i)`, `i : D.JX`, glue inclusions `D.xFormalGlueData.ι i`)
and `Y := D.yGlued` (charts `Spf(B j)`, `j : D.JY`, glue inclusions `D.yFormalGlueData.ι j`) — and a
pair of morphisms `a : Z ⟶ X`, `b : Z ⟶ Y` out of a locally finitely-generated formal scheme `Z`,
the universal property of `X ×_{Spf R} Y` (EGA I §10.7, issue 234) is assembled by descent along a
cover of `Z`. But the one-sided refinement of `FormalSchemes.GlueOpenCoverFactor` (issue 412b) only
makes each piece land in a single chart of *one* factor. Here we take the **common refinement**: at
each point `z` we choose an affine chart of `Z` landing inside
`a⁻¹(range (D.xFormalGlueData.ι i)) ∩ b⁻¹(range (D.yFormalGlueData.ι j))` for a single pair
`(i, j)`, so that both restrictions `map ≫ a` and `map ≫ b` factor through a single `X`-chart and a
single `Y`-chart simultaneously — the pair of charts whose double completed tensor product is the
product chart `Spf(A_i ⊗̂_R B_j)` that `chartLift` (issue 398) targets.

## Main definitions and results

* `BothChartedFibreDatumXY.BothRefinedChart`: the per-point bundled data — a finitely generated
  affine chart of `Z` around `z` whose range lies in `a⁻¹(range (D.xFormalGlueData.ι i))` **and**
  `b⁻¹(range (D.yFormalGlueData.ι j))` for a chosen pair `(i, j)`.
* `BothChartedFibreDatumXY.bothRefinedCover`: the resulting `OpenCover Z`, indexed by the points
  of `Z`.
* `BothChartedFibreDatumXY.xIndex` / `yIndex`: the selected `X`- and `Y`-chart indices for each
  cover piece.
* `BothChartedFibreDatumXY.xFactor` / `xFactor_comp_ι` and `yFactor` / `yFactor_comp_ι`: the two
  factorizations of `map c ≫ a` through `D.xFormalGlueData.U (xIndex c)` and of `map c ≫ b` through
  `D.yFormalGlueData.U (yIndex c)`, from the universal property of the open immersions.

These are the source-side inputs the general `fibreLift` assembly (issue 234c) and its uniqueness
(issue 234d) consume, per piece, alongside the affine `chartLift`.

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

variable {D a b}

/-- A refined chart exists around every point of a `LocallyFG` source: the `X`-charts jointly cover
`a z`, giving an index `i`, and symmetrically the `Y`-charts give `j`; the intersection of the two
preimages `a⁻¹(range (ι^X i)) ∩ b⁻¹(range (ι^Y j))` is open and contains `z`, so the affine-chart
neighborhood basis (`exists_affineChart_subset`) supplies a finitely generated affine chart landing
inside it. -/
theorem nonempty_bothRefinedChart (hZ : Z.LocallyFG) (z : Z) :
    Nonempty (BothRefinedChart D a b z) := by
  obtain ⟨i, y, hy⟩ := D.xFormalGlueData.ι_jointly_surjective (a.base z)
  obtain ⟨j, w, hw⟩ := D.yFormalGlueData.ι_jointly_surjective (b.base z)
  have hUopen : IsOpen ((a.base ⁻¹' Set.range (D.xFormalGlueData.ι i).base) ∩
      (b.base ⁻¹' Set.range (D.yFormalGlueData.ι j).base)) :=
    ((D.xFormalGlueData.ι_isOpenImmersion i).base_open.isOpen_range.preimage
        a.base.hom.continuous).inter
      ((D.yFormalGlueData.ι_isOpenImmersion j).base_open.isOpen_range.preimage
        b.base.hom.continuous)
  have hzU : z ∈ (a.base ⁻¹' Set.range (D.xFormalGlueData.ι i).base) ∩
      (b.base ⁻¹' Set.range (D.yFormalGlueData.ι j).base) := by
    refine ⟨?_, ?_⟩ <;> simp only [Set.mem_preimage]
    · exact ⟨y, hy⟩
    · exact ⟨w, hw⟩
  obtain ⟨S, _, _, J, _, f, hJfg, hzmem, hsub, hoi⟩ :=
    Z.exists_affineChart_subset hZ z _ hUopen hzU
  exact ⟨{ xIdx := i, yIdx := j, R := S, J := J, map := f, fg := hJfg, mem := hzmem,
           xsubset := fun _ hp => (hsub hp).1, ysubset := fun _ hp => (hsub hp).2 }⟩

variable (D a b)

/-- A chosen refined chart around each point of a `LocallyFG` source, via `Classical.choice`. -/
def bothRefinedChart (hZ : Z.LocallyFG) (z : Z) : BothRefinedChart D a b z :=
  (nonempty_bothRefinedChart hZ z).some

/-- The **common refinement** of the source cover of a locally finitely-generated formal scheme `Z`
along the pair `a : Z ⟶ D.xGlued`, `b : Z ⟶ D.yGlued`: indexed by the points of `Z`, the piece at
`z` is the finitely generated affine chart `bothRefinedChart D a b hZ z`, whose range lands inside a
single `X`-chart and a single `Y`-chart simultaneously. -/
def bothRefinedCover (hZ : Z.LocallyFG) : FormalScheme.OpenCover Z where
  J := Z
  obj z := FormalScheme.Spf (D.bothRefinedChart a b hZ z).J
  map z := FormalScheme.Hom.mk (D.bothRefinedChart a b hZ z).map
  f z := z
  covers z := (D.bothRefinedChart a b hZ z).mem
  isOpenImmersion z := (D.bothRefinedChart a b hZ z).isOpenImmersion

/-- The `X`-chart index selected for each piece of the common refinement. -/
def xIndex (hZ : Z.LocallyFG) (c : (D.bothRefinedCover a b hZ).J) : D.JX :=
  (D.bothRefinedChart a b hZ c).xIdx

/-- The `Y`-chart index selected for each piece of the common refinement. -/
def yIndex (hZ : Z.LocallyFG) (c : (D.bothRefinedCover a b hZ).J) : D.JY :=
  (D.bothRefinedChart a b hZ c).yIdx

/-- The range of `map c ≫ a` on a refined-cover piece is contained in the range of the selected
`X`-chart `D.xFormalGlueData.ι (xIndex c)` — the containment that makes the `X`-side factorization
possible. -/
theorem bothRefinedChart_range_comp_xsubset (hZ : Z.LocallyFG) (c : (D.bothRefinedCover a b hZ).J) :
    Set.range ((D.bothRefinedChart a b hZ c).map ≫ a).base ⊆
      Set.range (D.xFormalGlueData.ι (D.xIndex a b hZ c)).base := by
  rintro w ⟨s, rfl⟩
  simp only [LocallyRingedSpace.comp_base, TopCat.comp_app]
  exact (D.bothRefinedChart a b hZ c).xsubset ⟨s, rfl⟩

/-- The range of `map c ≫ b` on a refined-cover piece is contained in the range of the selected
`Y`-chart `D.yFormalGlueData.ι (yIndex c)` — the containment that makes the `Y`-side factorization
possible. -/
theorem bothRefinedChart_range_comp_ysubset (hZ : Z.LocallyFG) (c : (D.bothRefinedCover a b hZ).J) :
    Set.range ((D.bothRefinedChart a b hZ c).map ≫ b).base ⊆
      Set.range (D.yFormalGlueData.ι (D.yIndex a b hZ c)).base := by
  rintro w ⟨s, rfl⟩
  simp only [LocallyRingedSpace.comp_base, TopCat.comp_app]
  exact (D.bothRefinedChart a b hZ c).ysubset ⟨s, rfl⟩

/-- The **`X`-side chart-wise factorization**: on the piece `c`, the restriction `map c ≫ a`
factors through the single `X`-chart `D.xFormalGlueData.U (xIndex c)`. -/
def xFactor (hZ : Z.LocallyFG) (c : (D.bothRefinedCover a b hZ).J) :
    FormalSpectrum.locallyRingedSpaceObj (D.bothRefinedChart a b hZ c).J ⟶
      D.xFormalGlueData.toLocallyRingedSpaceGlueData.U (D.xIndex a b hZ c) :=
  LocallyRingedSpace.IsOpenImmersion.lift (D.xFormalGlueData.ι (D.xIndex a b hZ c))
    ((D.bothRefinedChart a b hZ c).map ≫ a) (D.bothRefinedChart_range_comp_xsubset a b hZ c)

/-- The `X`-side factorization is compatible with the glued inclusion: `xFactor c ≫ ι (xIndex c)`
recovers `map c ≫ a`. This is `lift_fac` for the open immersion `D.xFormalGlueData.ι (xIndex c)`. -/
@[reassoc]
theorem xFactor_comp_ι (hZ : Z.LocallyFG) (c : (D.bothRefinedCover a b hZ).J) :
    D.xFactor a b hZ c ≫ D.xFormalGlueData.ι (D.xIndex a b hZ c) =
      (D.bothRefinedChart a b hZ c).map ≫ a :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- The **`Y`-side chart-wise factorization**: on the piece `c`, the restriction `map c ≫ b`
factors through the single `Y`-chart `D.yFormalGlueData.U (yIndex c)`. -/
def yFactor (hZ : Z.LocallyFG) (c : (D.bothRefinedCover a b hZ).J) :
    FormalSpectrum.locallyRingedSpaceObj (D.bothRefinedChart a b hZ c).J ⟶
      D.yFormalGlueData.toLocallyRingedSpaceGlueData.U (D.yIndex a b hZ c) :=
  LocallyRingedSpace.IsOpenImmersion.lift (D.yFormalGlueData.ι (D.yIndex a b hZ c))
    ((D.bothRefinedChart a b hZ c).map ≫ b) (D.bothRefinedChart_range_comp_ysubset a b hZ c)

/-- The `Y`-side factorization is compatible with the glued inclusion: `yFactor c ≫ ι (yIndex c)`
recovers `map c ≫ b`. This is `lift_fac` for the open immersion `D.yFormalGlueData.ι (yIndex c)`. -/
@[reassoc]
theorem yFactor_comp_ι (hZ : Z.LocallyFG) (c : (D.bothRefinedCover a b hZ).J) :
    D.yFactor a b hZ c ≫ D.yFormalGlueData.ι (D.yIndex a b hZ c) =
      (D.bothRefinedChart a b hZ c).map ≫ b :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry.BothChartedFibreDatumXY

end
