import FormalSchemes.AwayTopFiniteType
import FormalSchemes.GlobalTopFiniteType
import FormalSchemes.LocallyFG

set_option linter.style.header false

/-!
# Topologically-finite-type affine opens form a basis (EGA I §10.13)

`FormalScheme.IsLocallyTopFiniteType R I X` (`FormalSchemes.GlobalTopFiniteType`) asserts that `X`
admits *some* open cover by affine formal schemes `Spf L` with `L` topologically of finite type
over the adic base `(R, I)`. On its own that says nothing about any *other* cover: the predicate is
stuck at whatever cover the instance producing it happened to be born with.

This file shows the property is **local**. Tf-type affine opens form a neighbourhood basis, so any
open cover of a locally tf-type formal scheme can be refined to a tf-type affine one.

## Main definitions and results

* `FormalScheme.TfTypeChart`: the per-point bundled chart data — a tf-type affine open immersion
  into `X` around `x` whose range lies in a prescribed open `U`.
* `FormalScheme.IsLocallyTopFiniteType.nonempty_tfTypeChart` and
  `FormalScheme.IsLocallyTopFiniteType.exists_tfType_affineChart_subset`: such a chart exists
  around every point of every open set. This is the tf-type analogue of
  `FormalScheme.exists_affineChart_subset` (`FormalSchemes.LocallyFG`), with `J.FG` strengthened to
  `IsTopologicallyFiniteType R I A L`.
* `FormalScheme.OpenCover.ofTfTypeCharts`: the cover assembled from a **supplied** family of
  charts, and `ofTfTypeCharts_range_subset`, which records what each piece refines.
* `FormalScheme.IsLocallyTopFiniteType.exists_refinement`: every open cover of a locally tf-type
  `X` is refined by a tf-type affine one — the statement that makes the predicate independent of
  the cover it was born with.
* `FormalScheme.IsLocallyTopFiniteType.locallyFG`: locally tf-type implies `LocallyFG`.

## The one new ingredient

Refining inside an affine chart `Spf L` lands on a **basic open** `D(g)`, whose chart ring is the
completed localization `L{1/g}`. So the statement was out of reach until issue 807 proved that a
basic open of a tf-type formal affine is again tf-type
(`AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion`,
`FormalSchemes.AwayTopFiniteType`). Everything else here is the proof of
`exists_affineChart_subset` run again with that extra fact carried along.

Note the finite generation hypothesis `hI : I.FG` on the base ideal: it is what makes `L` finitely
generated (`L = I·A` for a tf-type `A`) and it is a hypothesis of
`IsTopologicallyFiniteType.awayCompletion`.

## Why the cover is assembled from a supplied family

`ofTfTypeCharts` takes the chart family as an argument rather than choosing one internally.
A cover whose charts are picked by `Classical.choice` cannot carry any property the caller did not
think to put in the chart type, because choice erases which witness was taken; issue 460 is the
cautionary tale and issue 812 deleted the layer it produced (see the tombstone in
`FormalSchemes.GeneralFibreProductLiftAdic`). Choice appears here only inside
`exists_refinement`, whose conclusion is a proposition, so nothing opaque is exported.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.FormalScheme

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- The per-point **tf-type chart data** on a formal scheme `X`: an affine open immersion
`Spf L ↪ X` whose ring is topologically of finite type over the adic base `(R, I)`, whose range
contains the point `x`, and whose range is contained in the prescribed open set `U`. -/
structure TfTypeChart (X : FormalScheme.{u}) (U : Set X) (x : X) where
  /-- The underlying ring of the chart. -/
  A : Type u
  /-- Its commutative ring structure. -/
  [commRing : CommRing A]
  /-- Its topology. -/
  [topologicalSpace : TopologicalSpace A]
  /-- Its algebra structure over the base. -/
  [algebra : Algebra R A]
  /-- The ideal of definition. -/
  L : Ideal A
  /-- `(A, L)` is an adic ring, so `Spf L` is an affine formal scheme. -/
  [adic : IsAdicRing L]
  /-- `A` is topologically of finite type over `(R, I)` — the point of the whole file. -/
  tfType : IsTopologicallyFiniteType R I A L
  /-- The chart, an open immersion `Spf L ↪ X`. -/
  map : FormalSpectrum.locallyRingedSpaceObj L ⟶ X.toLocallyRingedSpace
  /-- The chart covers `x`. -/
  mem : x ∈ Set.range map.base
  /-- The chart lands inside `U`. -/
  subset : Set.range map.base ⊆ U
  /-- The chart is an open immersion. -/
  [isOpenImmersion : LocallyRingedSpace.IsOpenImmersion map]

attribute [instance] TfTypeChart.commRing TfTypeChart.topologicalSpace TfTypeChart.algebra
  TfTypeChart.adic TfTypeChart.isOpenImmersion

variable {R I}

/-- The ideal of definition of a tf-type algebra is finitely generated when the base ideal is:
it is the extension `I·A`. -/
theorem _root_.AlgebraicGeometry.IsTopologicallyFiniteType.fg {A : Type u} [CommRing A]
    [Algebra R A] {L : Ideal A} (h : IsTopologicallyFiniteType R I A L) (hI : I.FG) : L.FG := by
  rw [← IsTopologicallyFiniteType.map_eq h]
  exact hI.map _

/-- **Tf-type affine charts form a neighbourhood basis.** On a locally tf-type formal scheme, every
point `x` lying in an open set `U` admits a tf-type affine open-immersion chart whose range is
contained in `U`. -/
theorem IsLocallyTopFiniteType.nonempty_tfTypeChart {X : FormalScheme.{u}}
    (hX : IsLocallyTopFiniteType R I X) (hI : I.FG) (x : X) (U : Set X) (hU : IsOpen U)
    (hxU : x ∈ U) : Nonempty (TfTypeChart R I X U x) := by
  obtain ⟨𝒰, h𝒰⟩ := hX
  obtain ⟨A, _, _, _, L, _, hL, ⟨e⟩⟩ := h𝒰 (𝒰.f x)
  haveI : IsIso e.inv.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map e.inv))
  -- the chart of `X` at `x`, transported along the affine identification `e`
  let m : FormalSpectrum.locallyRingedSpaceObj L ⟶ X.toLocallyRingedSpace :=
    e.inv.toLRSHom ≫ (𝒰.map (𝒰.f x)).toLRSHom
  haveI hm : LocallyRingedSpace.IsOpenImmersion m :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      (e.inv.toLRSHom ≫ (𝒰.map (𝒰.f x)).toLRSHom))
  obtain ⟨y, hy⟩ := 𝒰.covers x
  -- the preimage of `x` in the affine chart, with the chart's own point type
  have hxm : x ∈ Set.range m.base := by
    refine ⟨e.hom.toLRSHom.base y, ?_⟩
    change (e.hom ≫ e.inv ≫ 𝒰.map (𝒰.f x)).toLRSHom.base y = x
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    exact hy
  obtain ⟨x₀, hx₀⟩ := hxm
  -- refine inside the affine chart: a basic open of `Spf L` around `x₀`
  have hopen : IsOpen (m.base ⁻¹' U) := hU.preimage m.base.hom.continuous
  have hmem : x₀ ∈ m.base ⁻¹' U := by
    simp only [Set.mem_preimage, hx₀]; exact hxU
  obtain ⟨v, ⟨g, rfl⟩, hx₀v, hvsub⟩ :=
    (FormalSpectrum.isTopologicalBasis_basicOpen L).exists_subset_of_mem_open hmem hopen
  have hLfg : L.FG := IsTopologicallyFiniteType.fg hL hI
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal L g) :=
    AdicCompletion.isAdicRing_map (L.map (algebraMap A (Localization.Away g))) (hLfg.map _)
  haveI : LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.basicOpenChart L g) :=
    FormalSpectrum.isOpenImmersion_basicOpenChart L g hLfg
  have hrange : Set.range (FormalSpectrum.basicOpenChart L g).base =
      (FormalSpectrum.basicOpen L g : Set (FormalSpectrum L)) :=
    FormalSpectrum.range_basicOpenChart_base L g hLfg
  refine ⟨{ A := FormalSpectrum.awayCompletion L g
            L := FormalSpectrum.awayCompletionIdeal L g
            tfType := IsTopologicallyFiniteType.awayCompletion g hI hL
            map := FormalSpectrum.basicOpenChart L g ≫ m
            mem := ?_
            subset := ?_ }⟩
  · have hx₀mem : x₀ ∈ Set.range (FormalSpectrum.basicOpenChart L g).base := by
      rw [hrange]; exact hx₀v
    obtain ⟨w, hw⟩ := hx₀mem
    refine ⟨w, ?_⟩
    simp only [LocallyRingedSpace.comp_base, TopCat.comp_app]
    rw [hw]; exact hx₀
  · rw [LocallyRingedSpace.comp_base]
    intro z hz
    simp only [TopCat.comp_app, Set.mem_range] at hz
    obtain ⟨w, rfl⟩ := hz
    have hw : (FormalSpectrum.basicOpenChart L g).base w ∈
        (FormalSpectrum.basicOpen L g : Set (FormalSpectrum L)) := by
      rw [← hrange]; exact ⟨w, rfl⟩
    exact hvsub hw

/-- The unbundled form of `IsLocallyTopFiniteType.nonempty_tfTypeChart`, matching the shape of
`FormalScheme.exists_affineChart_subset`. -/
theorem IsLocallyTopFiniteType.exists_tfType_affineChart_subset {X : FormalScheme.{u}}
    (hX : IsLocallyTopFiniteType R I X) (hI : I.FG) (x : X) (U : Set X) (hU : IsOpen U)
    (hxU : x ∈ U) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : Algebra R A) (L : Ideal A)
      (_ : IsAdicRing L) (_ : IsTopologicallyFiniteType R I A L)
      (f : FormalSpectrum.locallyRingedSpaceObj L ⟶ X.toLocallyRingedSpace),
      x ∈ Set.range f.base ∧ Set.range f.base ⊆ U ∧
        LocallyRingedSpace.IsOpenImmersion f := by
  obtain ⟨c⟩ := IsLocallyTopFiniteType.nonempty_tfTypeChart hX hI x U hU hxU
  exact ⟨c.A, c.commRing, c.topologicalSpace, c.algebra, c.L, c.adic, c.tfType, c.map, c.mem,
    c.subset, c.isOpenImmersion⟩

/-- A locally tf-type formal scheme is locally finitely generated: the ideal of definition of a
tf-type algebra is `I·A`, which is finitely generated when `I` is. -/
theorem IsLocallyTopFiniteType.locallyFG {X : FormalScheme.{u}}
    (hX : IsLocallyTopFiniteType R I X) (hI : I.FG) : X.LocallyFG := by
  intro x
  obtain ⟨c⟩ :=
    IsLocallyTopFiniteType.nonempty_tfTypeChart hX hI x Set.univ isOpen_univ (Set.mem_univ x)
  exact ⟨c.A, c.commRing, c.topologicalSpace, c.L, c.adic, c.map,
    IsTopologicallyFiniteType.fg c.tfType hI, c.mem, c.isOpenImmersion⟩

/-- **The cover assembled from a supplied family of tf-type charts**, indexed by the points of `X`.
The family is an argument, not an internal choice — see the module docstring. -/
def OpenCover.ofTfTypeCharts {X : FormalScheme.{u}} (U : X → Set X)
    (charts : ∀ x : X, TfTypeChart R I X (U x) x) : OpenCover X where
  J := X
  obj x := FormalScheme.Spf (charts x).L
  map x := Hom.mk (charts x).map
  f x := x
  covers x := (charts x).mem
  isOpenImmersion x := (charts x).isOpenImmersion

/-- Every piece of `ofTfTypeCharts` is affine tf-type over `(R, I)`. -/
theorem OpenCover.ofTfTypeCharts_isAffineTopFiniteType {X : FormalScheme.{u}} (U : X → Set X)
    (charts : ∀ x : X, TfTypeChart R I X (U x) x) (x : X) :
    IsAffineTopFiniteType R I ((OpenCover.ofTfTypeCharts U charts).obj x) :=
  IsTopologicallyFiniteType.isAffineTopFiniteType (charts x).tfType

/-- Each piece of `ofTfTypeCharts` lands inside the open set the family was built against — the
containment that makes it a *refinement*. -/
theorem OpenCover.ofTfTypeCharts_range_subset {X : FormalScheme.{u}} (U : X → Set X)
    (charts : ∀ x : X, TfTypeChart R I X (U x) x) (x : X) :
    Set.range ((OpenCover.ofTfTypeCharts U charts).map x).toLRSHom.base ⊆ U x :=
  (charts x).subset

/-- **Any open cover of a locally tf-type formal scheme is refined by a tf-type affine one.** -/
theorem IsLocallyTopFiniteType.exists_refinement {X : FormalScheme.{u}}
    (hX : IsLocallyTopFiniteType R I X) (hI : I.FG) (𝒱 : OpenCover X) :
    ∃ 𝒲 : OpenCover X, (∀ j, IsAffineTopFiniteType R I (𝒲.obj j)) ∧
      ∀ j, ∃ i, Set.range ((𝒲.map j).toLRSHom.base) ⊆
        Set.range ((𝒱.map i).toLRSHom.base) := by
  have hchart : ∀ x : X, Nonempty
      (TfTypeChart R I X (Set.range ((𝒱.map (𝒱.f x)).toLRSHom.base)) x) := fun x =>
    IsLocallyTopFiniteType.nonempty_tfTypeChart hX hI x _
      ((𝒱.isOpenImmersion (𝒱.f x)).base_open.isOpen_range) (𝒱.covers x)
  let charts : ∀ x : X, TfTypeChart R I X (Set.range ((𝒱.map (𝒱.f x)).toLRSHom.base)) x :=
    fun x => (hchart x).some
  refine ⟨OpenCover.ofTfTypeCharts _ charts, fun x =>
    OpenCover.ofTfTypeCharts_isAffineTopFiniteType _ charts x, fun x =>
    ⟨𝒱.f x, OpenCover.ofTfTypeCharts_range_subset _ charts x⟩⟩

end AlgebraicGeometry.FormalScheme

end
