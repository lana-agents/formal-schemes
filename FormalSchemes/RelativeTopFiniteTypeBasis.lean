import FormalSchemes.RelativeTopFiniteType
import FormalSchemes.TopFiniteTypeBasis

set_option linter.style.header false

/-!
# The relative refinement: `IsRelativelyTopFiniteType` refines to any open cover (EGA I §10.13)

`FormalSchemes.TopFiniteTypeBasis` (issue 822) showed that tf-type affine opens form a
neighbourhood basis, so the *object-level* predicate `IsLocallyTopFiniteType` no longer depends on
the cover it was born with. This file does the same for the *relative* predicate
`FormalScheme.IsRelativelyTopFiniteType R I f` of a morphism `f : X ⟶ Spf R`
(`FormalSchemes.RelativeTopFiniteType`), which is the one a §10.13 instance actually wants, since
it is the one that says something about the morphism.

## Main definitions and results

* `AlgebraicGeometry.basicOpenChart_comp_structMap`: **the crux.** The basic-open chart of
  `Spf A`, followed by the structural morphism `Spf A ⟶ Spf R`, is the structural morphism of the
  completed localization: `basicOpenChart L g ≫ structMap h = structMap h'`.
  `basicOpenChartHom_comp_structHom` is the same statement one level up, for `FormalScheme.Hom`.
* `FormalScheme.RelTfTypeChart`: a `TfTypeChart` that additionally commutes with `f` over its own
  structural morphism.
* `FormalScheme.IsRelativelyTopFiniteType.nonempty_relTfTypeChart`: such a chart exists around
  every point of every open set — the relative analogue of
  `IsLocallyTopFiniteType.nonempty_tfTypeChart`.
* `FormalScheme.OpenCover.ofRelTfTypeCharts_isRelativelyTopFiniteType`: a cover assembled from a
  **supplied** family of relative charts witnesses `IsRelativelyTopFiniteType R I f`.
* `FormalScheme.IsRelativelyTopFiniteType.exists_refinement`: every open cover of `X` is refined
  by one that witnesses `IsRelativelyTopFiniteType R I f`.

## Why the relative version is barely harder than the absolute one

`IsRelativelyTopFiniteType` asks, per piece `j`, for an identification `e : 𝒰.obj j ≅ Spf L` with
`𝒰.map j ≫ f = e.hom ≫ structHom h`. Two things make the refinement cheap.

First, writing `m := e.inv ≫ 𝒰.map j` for the piece transported onto its affine model, the
hypothesis collapses to `m ≫ f = structHom h` by `e.inv_hom_id`: the identification disappears
from the problem before the refinement starts.

Second, the refined chart of issue 822 is `basicOpenChart L g ≫ m`, whose source is *literally*
`Spf` of its own ring `A{1/g}^`. So the refined piece needs no identification at all — its `e` is
`Iso.refl` — and the entire remaining obligation is the affine statement
`basicOpenChart L g ≫ structMap h = structMap h'`, which is `locallyRingedSpaceMap_comp`
(`FormalSchemes.SpfFunctorial`) together with the scalar-tower identity
`(awayCompletionHom L g) ∘ (algebraMap R A) = algebraMap R (A{1/g}^)`. That is the whole content.

The ideal bookkeeping that looks like the hard part — `I·A{1/g}^ = awayCompletionIdeal L g`, which
is what `structMap` needs at the completed localization — is `map_algebraMap_awayCompletion`, and
it already existed in `FormalSchemes.AwayTopFiniteType` (issue 807).

## Why the cover is assembled from a supplied family

Same reason as in `FormalSchemes.TopFiniteTypeBasis`, and it is worth repeating rather than
cross-referencing: a cover whose charts are picked by `Classical.choice` cannot carry any property
the caller did not think to put in the chart type, because choice erases which witness was taken.
Issue 460 is the cautionary tale and issue 812 deleted the layer it produced (see the tombstone in
`FormalSchemes.GeneralFibreProductLiftAdic`). Choice appears here only inside `exists_refinement`,
whose conclusion is a proposition.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A}

/-! ### The crux: a basic-open chart over the base -/

/-- The structural ring map `A → A{1/g}^` of the completed localization, precomposed with the
base's structure map, is the base's structure map for `A{1/g}^`: two applications of
`IsScalarTower.algebraMap_eq` along `R → A → A_g → A{1/g}^`. -/
theorem awayCompletionHom_comp_algebraMap (g : A) :
    (FormalSpectrum.awayCompletionHom L g).comp (algebraMap R A) =
      algebraMap R (FormalSpectrum.awayCompletion L g) := by
  rw [FormalSpectrum.awayCompletionHom, RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq R A (Localization.Away g),
    ← IsScalarTower.algebraMap_eq R (Localization.Away g) (FormalSpectrum.awayCompletion L g)]

variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace A] [IsAdicRing L]

/-- **The crux.** The basic-open chart `Spf A{1/g}^ ⟶ Spf A`, followed by the structural morphism
`Spf A ⟶ Spf R` of a tf-type `A`, is the structural morphism of `A{1/g}^`.

Both sides are `Spf` of a ring homomorphism, so this is `locallyRingedSpaceMap_comp` plus
`awayCompletionHom_comp_algebraMap`, glued by the pre-existing
`FormalSpectrum.locallyRingedSpaceMap_congr` (`FormalSchemes.SpfFunctorial`), which is needed
because `locallyRingedSpaceMap`'s continuity argument is a proof *about* the homomorphism being
rewritten, so a direct `rw` fails with "motive is not type correct".

The tf-type witness at the completed localization is taken as
an argument rather than produced by `IsTopologicallyFiniteType.awayCompletion`, so that the
statement is usable with whatever witness the caller already has: `structMap` sees only the
proof `map_eq`, and proofs are irrelevant. -/
theorem basicOpenChart_comp_structMap (g : A)
    [IsAdicRing (FormalSpectrum.awayCompletionIdeal L g)]
    (h : IsTopologicallyFiniteType R I A L)
    (h' : IsTopologicallyFiniteType R I (FormalSpectrum.awayCompletion L g)
      (FormalSpectrum.awayCompletionIdeal L g)) :
    FormalSpectrum.basicOpenChart L g ≫ IsTopologicallyFiniteType.structMap h.map_eq =
      IsTopologicallyFiniteType.structMap h'.map_eq := by
  rw [IsTopologicallyFiniteType.structMap, IsTopologicallyFiniteType.structMap,
    FormalSpectrum.basicOpenChart, ← FormalSpectrum.locallyRingedSpaceMap_comp]
  · exact _root_.FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
      (awayCompletionHom_comp_algebraMap g)
  · rw [awayCompletionHom_comp_algebraMap]
    exact Ideal.map_le_iff_le_comap.mp h'.map_eq.le

namespace FormalScheme

/-- `basicOpenChart_comp_structMap` for morphisms of formal schemes: the basic-open chart, as a
`FormalScheme.Hom`, composed with the structural morphism, is the structural morphism of the
completed localization. -/
theorem basicOpenChartHom_comp_structHom (g : A)
    [IsAdicRing (FormalSpectrum.awayCompletionIdeal L g)]
    (h : IsTopologicallyFiniteType R I A L)
    (h' : IsTopologicallyFiniteType R I (FormalSpectrum.awayCompletion L g)
      (FormalSpectrum.awayCompletionIdeal L g)) :
    (Hom.mk (FormalSpectrum.basicOpenChart L g) :
        FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal L g) ⟶ FormalScheme.Spf L) ≫
      IsTopologicallyFiniteType.structHom h =
        IsTopologicallyFiniteType.structHom h' :=
  Hom.ext' (basicOpenChart_comp_structMap g h h')

end FormalScheme

namespace FormalScheme

/-- **The refinement step, with everything but the ring generalised to a variable.** If a chart
`m : Spf A ⟶ X` sits over the base via `A`'s structural morphism, then so does its basic-open
refinement `Spf A{1/g}^ ⟶ Spf A ⟶ X`.

Stated at a variable `m` and a variable target `f` on purpose: instantiating first and proving the
composite identity afterwards makes the `Hom.mk`/`toLRSHom` unfolding step below time out at
`isDefEq`, because nothing pins `Hom.mk`'s implicit formal scheme. At a variable `m` the same step
is `rfl` on two small explicit terms. This is the tree's standing rule — generalise the constant to
a variable *before* the equation, never after. -/
theorem basicOpenChartHom_comp (g : A)
    [IsAdicRing (FormalSpectrum.awayCompletionIdeal L g)] {X : FormalScheme.{u}}
    {f : X ⟶ FormalScheme.Spf I} (m : FormalScheme.Spf L ⟶ X)
    (h : IsTopologicallyFiniteType R I A L)
    (h' : IsTopologicallyFiniteType R I (FormalSpectrum.awayCompletion L g)
      (FormalSpectrum.awayCompletionIdeal L g))
    (hm : m ≫ f = IsTopologicallyFiniteType.structHom h) :
    (Hom.mk (FormalSpectrum.basicOpenChart L g ≫ m.toLRSHom) :
        FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal L g) ⟶ X) ≫ f =
      IsTopologicallyFiniteType.structHom h' := by
  have hsplit : (Hom.mk (FormalSpectrum.basicOpenChart L g ≫ m.toLRSHom) :
        FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal L g) ⟶ X) =
      (Hom.mk (FormalSpectrum.basicOpenChart L g) :
        FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal L g) ⟶ FormalScheme.Spf L) ≫ m :=
    rfl
  rw [hsplit, Category.assoc, hm]
  exact basicOpenChartHom_comp_structHom g h h'

variable (R I) in
/-- A **relative tf-type chart**: a `TfTypeChart` (`FormalSchemes.TopFiniteTypeBasis`) whose
inclusion into `X` additionally commutes with `f : X ⟶ Spf R` over the chart's own structural
morphism.

No identification `e : ⋯ ≅ Spf L` appears, unlike in `IsRelativelyTopFiniteType`: the chart's
source *is* `Spf` of its own ring, so the identification would be `Iso.refl`. -/
structure RelTfTypeChart {X : FormalScheme.{u}} (f : X ⟶ FormalScheme.Spf I) (U : Set X) (x : X)
    extends TfTypeChart R I X U x where
  /-- The chart commutes with `f` over its own structural morphism `Spf L ⟶ Spf R`. -/
  structCompat : (Hom.mk toTfTypeChart.map :
      FormalScheme.Spf toTfTypeChart.L ⟶ X) ≫ f =
    IsTopologicallyFiniteType.structHom toTfTypeChart.tfType

variable {X : FormalScheme.{u}} {f : X ⟶ FormalScheme.Spf I}

/-- **Relative tf-type charts form a neighbourhood basis.** If `f : X ⟶ Spf R` is topologically of
finite type, every point `x` in an open `U` admits a tf-type affine chart contained in `U` that
commutes with `f`.

The relative analogue of `IsLocallyTopFiniteType.nonempty_tfTypeChart`, and the same proof with the
compatibility carried along: the piece's identification `e` is cancelled by `e.inv_hom_id` before
the refinement starts, and what the basic-open refinement then has to preserve is exactly
`basicOpenChartHom_comp_structHom`. -/
theorem IsRelativelyTopFiniteType.nonempty_relTfTypeChart
    (hf : IsRelativelyTopFiniteType R I f) (hI : I.FG) (x : X) (U : Set X) (hU : IsOpen U)
    (hxU : x ∈ U) : Nonempty (RelTfTypeChart R I f U x) := by
  obtain ⟨𝒰, h𝒰⟩ := hf
  obtain ⟨A, _, _, _, L, _, hL, e, hcomp⟩ := h𝒰 (𝒰.f x)
  haveI : IsIso e.inv.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map e.inv))
  -- the piece transported onto its affine model: the identification cancels out of the
  -- compatibility, leaving the chart sitting over the base by its own structural morphism
  have hmf : (e.inv ≫ 𝒰.map (𝒰.f x)) ≫ f = IsTopologicallyFiniteType.structHom hL := by
    rw [Category.assoc, hcomp, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  let m : FormalSpectrum.locallyRingedSpaceObj L ⟶ X.toLocallyRingedSpace :=
    (e.inv ≫ 𝒰.map (𝒰.f x)).toLRSHom
  haveI hm : LocallyRingedSpace.IsOpenImmersion m :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      (e.inv.toLRSHom ≫ (𝒰.map (𝒰.f x)).toLRSHom))
  obtain ⟨y, hy⟩ := 𝒰.covers x
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
            subset := ?_
            structCompat := ?_ }⟩
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
  · exact basicOpenChartHom_comp g (e.inv ≫ 𝒰.map (𝒰.f x)) hL
      (IsTopologicallyFiniteType.awayCompletion g hI hL) hmf

/-- The cover assembled from a **supplied** family of relative charts: it is
`OpenCover.ofTfTypeCharts` of the underlying tf-type charts, so every lemma proved there applies
verbatim. -/
abbrev OpenCover.ofRelTfTypeCharts (U : X → Set X)
    (charts : ∀ x : X, RelTfTypeChart R I f (U x) x) : OpenCover X :=
  OpenCover.ofTfTypeCharts U fun x => (charts x).toTfTypeChart

/-- **A cover assembled from relative charts witnesses `IsRelativelyTopFiniteType`.** The
identification demanded per piece is `Iso.refl`, because each piece is `Spf` of its own ring, and
the compatibility is then the chart's own `structCompat` field. -/
theorem OpenCover.ofRelTfTypeCharts_isRelativelyTopFiniteType (U : X → Set X)
    (charts : ∀ x : X, RelTfTypeChart R I f (U x) x) (x : X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : Algebra R A)
      (L : Ideal A) (_ : IsAdicRing L) (h : IsTopologicallyFiniteType R I A L)
      (e : (OpenCover.ofRelTfTypeCharts U charts).obj x ≅ FormalScheme.Spf L),
      (OpenCover.ofRelTfTypeCharts U charts).map x ≫ f =
        e.hom ≫ IsTopologicallyFiniteType.structHom h :=
  ⟨(charts x).A, inferInstance, inferInstance, inferInstance, (charts x).L, inferInstance,
    (charts x).tfType, Iso.refl _, (charts x).structCompat.trans (Category.id_comp _).symm⟩

/-- **Any open cover of `X` is refined by one witnessing that `f : X ⟶ Spf R` is topologically of
finite type.** The first conjunct is the body of `IsRelativelyTopFiniteType` with the cover
exposed, so a caller gets the per-piece data and not just the predicate it already had. -/
theorem IsRelativelyTopFiniteType.exists_refinement (hf : IsRelativelyTopFiniteType R I f)
    (hI : I.FG) (𝒱 : OpenCover X) :
    ∃ 𝒲 : OpenCover X,
      (∀ j, ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : Algebra R A)
        (L : Ideal A) (_ : IsAdicRing L) (h : IsTopologicallyFiniteType R I A L)
        (e : 𝒲.obj j ≅ FormalScheme.Spf L),
        𝒲.map j ≫ f = e.hom ≫ IsTopologicallyFiniteType.structHom h) ∧
      ∀ j, ∃ i, Set.range ((𝒲.map j).toLRSHom.base) ⊆
        Set.range ((𝒱.map i).toLRSHom.base) := by
  have hchart : ∀ x : X, Nonempty
      (RelTfTypeChart R I f (Set.range ((𝒱.map (𝒱.f x)).toLRSHom.base)) x) := fun x =>
    hf.nonempty_relTfTypeChart hI x _
      ((𝒱.isOpenImmersion (𝒱.f x)).base_open.isOpen_range) (𝒱.covers x)
  let charts : ∀ x : X, RelTfTypeChart R I f (Set.range ((𝒱.map (𝒱.f x)).toLRSHom.base)) x :=
    fun x => (hchart x).some
  exact ⟨OpenCover.ofRelTfTypeCharts _ charts,
    fun x => OpenCover.ofRelTfTypeCharts_isRelativelyTopFiniteType _ charts x,
    fun x => ⟨𝒱.f x, OpenCover.ofTfTypeCharts_range_subset _ _ x⟩⟩

end FormalScheme

end AlgebraicGeometry
