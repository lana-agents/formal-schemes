import FormalSchemes.ConservativityTopFiniteType

set_option linter.style.header false

/-!
# Refining the target cover to basic opens, and conservativity

`AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType R I f` is EGA I 10.13's finite-type
condition at an affine target and `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom f` its
general-target form (`FormalSchemes.RelativeTopFiniteType`, `FormalSchemes.TopFiniteTypeHom`).
One direction is `AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType.isTopFiniteTypeHom`.
**Conservativity** is the converse at `Y = FormalScheme.Spf I`, and this file proves it with no
hypothesis beyond `I.FG`.

`FormalSchemes.ConservativityTopFiniteType` assembled the converse from a hypothesis, and observed
where that hypothesis is spent: `IsTopFiniteTypeHomOn.isRelativelyTopFiniteType` needs it only at
the charts of the **target** cover `𝒱`, and
`IsTopFiniteTypeHomOn.isRelativelyTopFiniteType_of_basicOpen` needs nothing at all once the *range*
of every such chart is a basic open of `Spf I`. Since `IsRelativelyTopFiniteType` asserts the
existence of a cover, a witness may be refined before it is consumed. This file carries out that
refinement.

## The refinement

At a point `x` of `X`, the witness `IsTopFiniteTypeHomOn f 𝒱 𝒰` supplies a source chart
`m : Spf L ⟶ X` through `x`, a target chart `t : Spf K ⟶ Spf I`, and `A` tf-type over `(S, K)`
with `m ≫ f` factoring as `IsTopologicallyFiniteType.structHom` followed by `t`. Both halves are
then shrunk over one basic open:

* `FormalSpectrum.exists_basicOpenChart_le_affine_inter` (`FormalSchemes.TwoChartBasicOpen`) is
  stated for two affine charts of one locally ringed space. Reading it at `t` and at the
  **identity of `Spf I`** produces `c : S` and `d : R` with
  `Set.range (basicOpenChart K c ≫ t) = Set.range (basicOpenChart I d)` and the image of `x` in
  the left-hand side — that is, a basic open of the chart which is also a basic open of `Spf I`.
* `AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion_baseChange`
  (`FormalSchemes.AwayBaseChangeTopFiniteType`) makes `A{1/c}^` tf-type over
  `(S{1/c}^, K{1/c}^)`, and `FormalSpectrum.basicOpenChart_comp_structMap_baseChange`
  (`FormalSchemes.AwayChartStructMap`) is the square that keeps the factorisation.
* `FormalSpectrum.map_preimage_basicOpen` (`FormalSchemes.SpfMap`) puts `x` in the shrunk source
  chart: the structural morphism pulls `D(c)` back to `D(c · A)`.

The refined covers are these charts, indexed by the points of `X`, together with `Spf I` itself on
the target side — its range is `D(1)` (`FormalSpectrum.basicOpen_one`), so it satisfies the basic
range condition too, and it is what makes the family a cover of all of `Spf I` and not only of the
image of `f`.

## The step that turns out not to be needed

The route recorded in `FormalSchemes.ConservativityTopFiniteType`'s module docstring proposed
re-presenting the refined target chart on the base ring `R{1/d}^`, which would need
`IsTopologicallyFiniteType` to transport along a ring isomorphism of the **base**;
`IsTopologicallyFiniteType.ofAlgEquiv` (`FormalSchemes.CofinalTopFiniteType`) moves only the top
ring, so that lemma is not on this tree.

**It is not needed, and this file does not prove it.** The refined chart keeps the presentation
`S{1/c}^` that `AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion_baseChange` already
delivers, because
`IsTopFiniteTypeHomOn.isRelativelyTopFiniteType_of_basicOpen` constrains the *range* of a target
chart and not its presentation — which is exactly what
`FormalSpectrum.isCofinal_map_of_range_eq` (`FormalSchemes.AdicCofinalOpenImmersion`) bought. So
no isomorphism of formal spectra is used here at all, only a range equality, and
`FormalSpectrum.exists_basicOpenChart_inter_iso` is never called.

## What is *not* proved

`AlgebraicGeometry.FormalScheme.IsAdicOpenImmersionProperty I` — that an affine open immersion
into `Spf I` is adic up to cofinality, EGA I 10.12 — is **untouched and still open**, as is the
statement it reduces to, that an *arbitrary* affine open of `Spf I` is topologically of finite type
over `(R, I)`. Conservativity was previously reduced to those; the reduction was sufficient and not
necessary, and nothing here settles them. In particular the hypothesis of
`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.isRelativelyTopFiniteType`
(`FormalSchemes.ConservativityTopFiniteType`) is now redundant, but the property it names is not
thereby proved.

## Main definitions

* `AlgebraicGeometry.FormalScheme.BasicTargetChart`: the per-point data of a refined witness — a
  source chart through the point, a target chart whose range is a basic open of `Spf I`, and the
  tf-type algebra between them.
* `AlgebraicGeometry.FormalScheme.OpenCover.ofBasicTargetCharts` and
  `AlgebraicGeometry.FormalScheme.OpenCover.ofBasicTargetChartsTarget`: the two covers assembled
  from a family of those.

## Main results

* `AlgebraicGeometry.FormalScheme.nonempty_basicTargetChart`: **the construction** — a refined
  chart exists at every point of `X`.
* `AlgebraicGeometry.FormalScheme.isTopFiniteTypeHomOn_ofBasicTargetCharts` and
  `AlgebraicGeometry.FormalScheme.exists_range_eq_basicOpenChart_ofBasicTargetChartsTarget`: the
  assembled covers witness the predicate, and every chart of the target one has basic range.
* `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.exists_basicTargetRefinement`: **the
  target-side refinement.**
* `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHomOn.isRelativelyTopFiniteType_of_fg` and
  `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.isRelativelyTopFiniteType_of_fg`:
  **conservativity**, at a fixed pair of covers and in general.
* `AlgebraicGeometry.FormalScheme.isRelativelyTopFiniteType_iff_isTopFiniteTypeHom_of_fg`: the two
  notions agree at an affine target.
* `AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType.comp_isTopFiniteTypeHom` and
  `AlgebraicGeometry.FormalScheme.isRelativelyTopFiniteType_comp_chartMap`: two consequences that
  the base-affine notion could not reach on its own — a composite through an arbitrary formal
  scheme, and one through a chart of an arbitrary affine cover of `Spf I`.
* `AlgebraicGeometry.FormalScheme.isRelativelyTopFiniteType_comp_basicOpenChart`: non-vacuity, at
  a named intermediate and with every hypothesis discharged.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.12, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3.
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormalScheme

variable {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]
variable {X : FormalScheme.{u}}

/-- **The per-point data of a refined witness.** At a point `x` of `X`: an affine chart `src` of
`X` through `x`, an affine chart `mid` of `Spf I` whose range is a basic open `D(g)`, and an
algebra `A` tf-type over `(S, K)` making `f` structural through those two charts.

The target chart is carried as a morphism rather than as an index of a fixed cover, exactly as in
`AlgebraicGeometry.FormalScheme.TfTypeCompChart` (`FormalSchemes.TopFiniteTypeHomTrans`) and for
the same reason: the refined charts are built one point at a time and are pieces of neither given
cover.

Note what `AlgebraicGeometry.FormalScheme.BasicTargetChart.rangeMid` does *not* say. It constrains
the range of that chart and not its presentation:
`K` is whatever the shrunk witness produced, and is related to `FormalSpectrum.awayCompletionIdeal
I g` only through `FormalSpectrum.isCofinal_map_of_range_eq`
(`FormalSchemes.AdicCofinalOpenImmersion`). That is what keeps the base transport out of this
file. -/
structure BasicTargetChart (f : X ⟶ FormalScheme.Spf I) (x : X) where
  S : Type u
  [commRingS : CommRing S]
  [topS : TopologicalSpace S]
  K : Ideal S
  [adicK : IsAdicRing K]
  fgK : K.FG
  A : Type u
  [commRingA : CommRing A]
  [topA : TopologicalSpace A]
  [algSA : Algebra S A]
  L : Ideal A
  [adicL : IsAdicRing L]
  hA : IsTopologicallyFiniteType S K A L
  mid : FormalScheme.Spf K ⟶ FormalScheme.Spf I
  [isOpenImmersionMid : LocallyRingedSpace.IsOpenImmersion mid.toLRSHom]
  g : R
  rangeMid : Set.range mid.toLRSHom.base =
    Set.range (FormalSpectrum.basicOpenChart I g).base
  src : FormalScheme.Spf L ⟶ X
  [isOpenImmersionSrc : LocallyRingedSpace.IsOpenImmersion src.toLRSHom]
  mem : x ∈ Set.range src.toLRSHom.base
  compat : src ≫ f = IsTopologicallyFiniteType.structHom hA ≫ mid

attribute [instance] BasicTargetChart.commRingS BasicTargetChart.topS BasicTargetChart.adicK
  BasicTargetChart.commRingA BasicTargetChart.topA BasicTargetChart.algSA
  BasicTargetChart.adicL BasicTargetChart.isOpenImmersionMid
  BasicTargetChart.isOpenImmersionSrc

/-- **A refined chart exists at every point of `X`.** The witness is read at `𝒰.f x`, its target
chart is shrunk against the identity of `Spf I`, and its source chart is shrunk along.

The three ingredients, in the order they are used:
`FormalSpectrum.exists_basicOpenChart_le_affine_inter` (`FormalSchemes.TwoChartBasicOpen`) for the
common basic open — the second morphism handed to it is the identity, which is what makes the
resulting open basic in `Spf I` rather than merely in the chart;
`AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion_baseChange`
(`FormalSchemes.AwayBaseChangeTopFiniteType`) for the shrunk algebra; and
`FormalSpectrum.basicOpenChart_comp_structMap_baseChange` (`FormalSchemes.AwayChartStructMap`) for
the square. The point stays in the shrunk source chart by
`FormalSpectrum.map_preimage_basicOpen` (`FormalSchemes.SpfMap`), which computes the preimage of
`D(c)` under the structural morphism. -/
theorem nonempty_basicTargetChart {f : X ⟶ FormalScheme.Spf I} (hI : I.FG)
    {𝒱 : OpenCover (FormalScheme.Spf I)} {𝒰 : OpenCover X}
    (hOn : IsTopFiniteTypeHomOn f 𝒱 𝒰) (x : X) :
    Nonempty (BasicTargetChart f x) := by
  obtain ⟨i₀, S, _, _, K, _, hKfg, A, _, _, _, L, _, hA, e, e', hcomp⟩ := hOn (𝒰.f x)
  haveI : IsIso e.inv.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map e.inv))
  haveI : IsIso e'.inv.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map e'.inv))
  set m : FormalScheme.Spf L ⟶ X := e.inv ≫ 𝒰.map (𝒰.f x) with hm_def
  set t : FormalScheme.Spf K ⟶ FormalScheme.Spf I := e'.inv ≫ 𝒱.map i₀ with ht_def
  haveI hm : LocallyRingedSpace.IsOpenImmersion m.toLRSHom :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      (e.inv.toLRSHom ≫ (𝒰.map (𝒰.f x)).toLRSHom))
  haveI ht : LocallyRingedSpace.IsOpenImmersion t.toLRSHom :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      (e'.inv.toLRSHom ≫ (𝒱.map i₀).toLRSHom))
  have hmf : m ≫ f = IsTopologicallyFiniteType.structHom hA ≫ t := by
    rw [hm_def, ht_def, Category.assoc, hcomp, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨y₀, hy₀⟩ := 𝒰.covers x
  have hxm : x ∈ Set.range m.toLRSHom.base := by
    refine ⟨e.hom.toLRSHom.base y₀, ?_⟩
    change (e.hom ≫ m).toLRSHom.base y₀ = x
    rw [hm_def, ← Category.assoc, e.hom_inv_id, Category.id_comp]
    exact hy₀
  obtain ⟨x₀, hx₀⟩ := hxm
  set y : FormalScheme.Spf I := f.toLRSHom.base x with hy_def
  have hy_eq : t.toLRSHom.base
      ((IsTopologicallyFiniteType.structHom hA).toLRSHom.base x₀) = y := by
    have h1 := congrArg (fun φ : FormalScheme.Spf L ⟶ FormalScheme.Spf I =>
      φ.toLRSHom.base x₀) hmf
    simp only [FormalScheme.comp_toLRSHom, LocallyRingedSpace.comp_base, TopCat.comp_app] at h1
    rw [hx₀] at h1
    exact h1.symm
  have hyt : y ∈ Set.range t.toLRSHom.base := ⟨_, hy_eq⟩
  set tL : FormalSpectrum.locallyRingedSpaceObj K ⟶
    FormalSpectrum.locallyRingedSpaceObj I := t.toLRSHom with htL_def
  haveI : LocallyRingedSpace.IsOpenImmersion tL := ht
  set idI : FormalSpectrum.locallyRingedSpaceObj I ⟶ FormalSpectrum.locallyRingedSpaceObj I :=
    𝟙 (FormalSpectrum.locallyRingedSpaceObj I) with hidI_def
  haveI : LocallyRingedSpace.IsOpenImmersion idI := inferInstanceAs
    (LocallyRingedSpace.IsOpenImmersion (𝟙 (FormalSpectrum.locallyRingedSpaceObj I)))
  have hyid : y ∈ Set.range idI.base := ⟨y, rfl⟩
  obtain ⟨c, d, hEq, hyc⟩ :=
    FormalSpectrum.exists_basicOpenChart_le_affine_inter hKfg hI tL idI y hyt hyid
  have hrange : Set.range (FormalSpectrum.basicOpenChart K c ≫ tL).base =
      Set.range (FormalSpectrum.basicOpenChart I d).base := by
    rw [hEq, hidI_def, Category.comp_id]
  -- the away data
  have hLfg : L.FG := IsTopologicallyFiniteType.fg hA hKfg
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal K c) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal K c hKfg
  haveI : IsAdicComplete (K.map (algebraMap S A)) A := by rw [hA.map_eq]; infer_instance
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal L (algebraMap S A c)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal L _ hLfg
  letI := FormalSpectrum.awayBaseAlgebra c hKfg hA.map_eq
  have hA₂ : IsTopologicallyFiniteType (FormalSpectrum.awayCompletion K c)
      (FormalSpectrum.awayCompletionIdeal K c)
      (FormalSpectrum.awayCompletion L (algebraMap S A c))
      (FormalSpectrum.awayCompletionIdeal L (algebraMap S A c)) :=
    IsTopologicallyFiniteType.awayCompletion_baseChange hKfg hA c
  have hKcfg : (FormalSpectrum.awayCompletionIdeal K c).FG :=
    FormalSpectrum.awayCompletionIdeal_fg K c hKfg
  haveI : LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.basicOpenChart K c) :=
    FormalSpectrum.isOpenImmersion_basicOpenChart K c hKfg
  haveI : LocallyRingedSpace.IsOpenImmersion
      (FormalSpectrum.basicOpenChart L (algebraMap S A c)) :=
    FormalSpectrum.isOpenImmersion_basicOpenChart L _ hLfg
  set bcK : FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal K c) ⟶ FormalScheme.Spf K :=
    Hom.mk (FormalSpectrum.basicOpenChart K c) with hbcK_def
  set bcL : FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal L (algebraMap S A c)) ⟶
      FormalScheme.Spf L := Hom.mk (FormalSpectrum.basicOpenChart L (algebraMap S A c))
    with hbcL_def
  have q1 : LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.basicOpenChart K c) :=
    inferInstance
  have q2 : LocallyRingedSpace.IsOpenImmersion tL := inferInstance
  haveI hmidoi : LocallyRingedSpace.IsOpenImmersion (bcK ≫ t).toLRSHom :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (FormalSpectrum.basicOpenChart K c) q1 tL q2
  have q3 : LocallyRingedSpace.IsOpenImmersion
      (FormalSpectrum.basicOpenChart L (algebraMap S A c)) := inferInstance
  have q4 : LocallyRingedSpace.IsOpenImmersion m.toLRSHom := inferInstance
  haveI hsrcoi : LocallyRingedSpace.IsOpenImmersion (bcL ≫ m).toLRSHom :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (FormalSpectrum.basicOpenChart L (algebraMap S A c)) q3 m.toLRSHom q4
  -- the point lies in the shrunk source chart
  obtain ⟨w, hw⟩ := hyc
  have hstructmem : (IsTopologicallyFiniteType.structHom hA).toLRSHom.base x₀ ∈
      Set.range (FormalSpectrum.basicOpenChart K c).base := by
    refine ⟨w, ?_⟩
    refine ht.base_open.injective ?_
    simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at hw
    exact hw.trans hy_eq.symm
  have hx₀mem : x₀ ∈ Set.range (FormalSpectrum.basicOpenChart L (algebraMap S A c)).base := by
    rw [FormalSpectrum.range_basicOpenChart_base L _ hLfg]
    rw [FormalSpectrum.range_basicOpenChart_base K c hKfg] at hstructmem
    have hmem : x₀ ∈ (TopologicalSpace.Opens.map
        (FormalSpectrum.mapTop K L (algebraMap S A)
          (Ideal.map_le_iff_le_comap.mp hA.map_eq.le))).obj (FormalSpectrum.basicOpen K c) :=
      hstructmem
    rwa [FormalSpectrum.map_preimage_basicOpen] at hmem
  refine ⟨{ S := FormalSpectrum.awayCompletion K c
            K := FormalSpectrum.awayCompletionIdeal K c
            fgK := hKcfg
            A := FormalSpectrum.awayCompletion L (algebraMap S A c)
            L := FormalSpectrum.awayCompletionIdeal L (algebraMap S A c)
            hA := hA₂
            mid := bcK ≫ t
            g := d
            rangeMid := ?_
            src := bcL ≫ m
            mem := ?_
            compat := ?_ }⟩
  · rw [comp_toLRSHom]
    exact hrange
  · obtain ⟨v, hv⟩ := hx₀mem
    refine ⟨v, ?_⟩
    rw [comp_toLRSHom]
    change m.toLRSHom.base ((FormalSpectrum.basicOpenChart L (algebraMap S A c)).base v) = x
    rw [hv]
    exact hx₀
  · have hchart : bcL ≫ IsTopologicallyFiniteType.structHom hA =
        IsTopologicallyFiniteType.structHom hA₂ ≫ bcK :=
      congrArg Hom.mk (FormalSpectrum.basicOpenChart_comp_structMap_baseChange hKfg hA.map_eq c
        rfl hA₂.map_eq)
    calc (bcL ≫ m) ≫ f
        = bcL ≫ (m ≫ f) := by rw [Category.assoc]
      _ = bcL ≫ IsTopologicallyFiniteType.structHom hA ≫ t := by rw [hmf]
      _ = (bcL ≫ IsTopologicallyFiniteType.structHom hA) ≫ t := by rw [Category.assoc]
      _ = (IsTopologicallyFiniteType.structHom hA₂ ≫ bcK) ≫ t := by rw [hchart]
      _ = IsTopologicallyFiniteType.structHom hA₂ ≫ bcK ≫ t := by rw [Category.assoc]


/-! ### The two refined covers -/

variable {f : X ⟶ FormalScheme.Spf I}

/-- **The refined cover of `X`**, indexed by the points of `X`. The family is an argument rather
than an internal `Classical.choice`, for the reason
`AlgebraicGeometry.FormalScheme.OpenCover.ofTfTypeHomCharts` (`FormalSchemes.TopFiniteTypeHom`)
records: a cover whose charts are chosen inside the definition cannot carry any property the
caller did not put into the chart type, and the property wanted here is
`AlgebraicGeometry.FormalScheme.BasicTargetChart.rangeMid`. -/
def OpenCover.ofBasicTargetCharts (charts : ∀ x : X, BasicTargetChart f x) : OpenCover X where
  J := X
  obj x := FormalScheme.Spf (charts x).L
  map x := (charts x).src
  f x := x
  covers x := (charts x).mem
  isOpenImmersion x := (charts x).isOpenImmersionSrc

/-- **The refined cover of `Spf I`**: the refined target charts, together with `Spf I` itself.

The refined charts are indexed by the points of `X`, so they cover only the image of `f`; the
second summand is what makes the result a cover. Unlike the filler in
`AlgebraicGeometry.FormalScheme.OpenCover.ofCompChartsTarget`
(`FormalSchemes.TopFiniteTypeHomTrans`) this one cannot be an arbitrary cover of the target: every
chart has to satisfy the basic-range condition, and `𝟙 (FormalScheme.Spf I)` does, its range being
`D(1)`. -/
def OpenCover.ofBasicTargetChartsTarget (charts : ∀ x : X, BasicTargetChart f x) :
    OpenCover (FormalScheme.Spf I) where
  J := X ⊕ PUnit.{u + 1}
  obj := Sum.elim (fun x => FormalScheme.Spf (charts x).K) fun _ => FormalScheme.Spf I
  map j := match j with
    | .inl x => (charts x).mid
    | .inr _ => 𝟙 (FormalScheme.Spf I)
  f _ := .inr PUnit.unit
  covers y := ⟨y, rfl⟩
  isOpenImmersion j := match j with
    | .inl x => (charts x).isOpenImmersionMid
    | .inr _ => inferInstanceAs
        (LocallyRingedSpace.IsOpenImmersion (𝟙 (FormalScheme.Spf I).toLocallyRingedSpace))

/-- **The two assembled covers witness the predicate.** Both identifications are `Iso.refl` — each
chart *is* `Spf` of its own ring, which is the point of building the covers out of the charts
rather than refining given ones — so the compatibility square is
`AlgebraicGeometry.FormalScheme.BasicTargetChart.compat`. -/
theorem isTopFiniteTypeHomOn_ofBasicTargetCharts (charts : ∀ x : X, BasicTargetChart f x) :
    IsTopFiniteTypeHomOn f (OpenCover.ofBasicTargetChartsTarget charts)
      (OpenCover.ofBasicTargetCharts charts) := by
  intro x
  refine ⟨Sum.inl x, (charts x).S, inferInstance, inferInstance, (charts x).K, inferInstance,
    (charts x).fgK, (charts x).A, inferInstance, inferInstance, inferInstance, (charts x).L,
    inferInstance, (charts x).hA, Iso.refl _, Iso.refl _, ?_⟩
  simpa [OpenCover.ofBasicTargetCharts, OpenCover.ofBasicTargetChartsTarget] using
    (charts x).compat

/-- **Every chart of the refined target cover has a basic open of `Spf I` as its range** — the
refined ones by `AlgebraicGeometry.FormalScheme.BasicTargetChart.rangeMid`, and the filler at
`g = 1`, where `FormalSpectrum.basicOpen_one` and
`FormalSpectrum.range_basicOpenChart_base` identify the range of the identity with `D(1)`. -/
theorem exists_range_eq_basicOpenChart_ofBasicTargetChartsTarget (hI : I.FG)
    (charts : ∀ x : X, BasicTargetChart f x)
    (i : (OpenCover.ofBasicTargetChartsTarget charts).J) :
    ∃ g : R, Set.range ((OpenCover.ofBasicTargetChartsTarget charts).map i).toLRSHom.base =
      Set.range (FormalSpectrum.basicOpenChart I g).base := by
  match i with
  | .inl x => exact ⟨(charts x).g, (charts x).rangeMid⟩
  | .inr _ =>
    refine ⟨1, ?_⟩
    rw [FormalSpectrum.range_basicOpenChart_base I 1 hI, FormalSpectrum.basicOpen_one]
    exact Set.range_eq_univ.mpr fun z => ⟨z, rfl⟩

/-! ### The refinement, and conservativity -/

/-- **The target-side refinement.** A witness for `IsTopFiniteTypeHom f` at an affine target can
be replaced by one whose *target* cover is by opens with basic range.

This is the side the tree could not refine.
`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.exists_refinement`
(`FormalSchemes.TopFiniteTypeHom`) and
`AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType.exists_refinement`
(`FormalSchemes.RelativeTopFiniteTypeBasis`) both refine the cover of the *source* while keeping
the cover of the target fixed, which `FormalSchemes.RelativeTopFiniteTypeTrans` says of both of
them.

The refined source cover is **not** a refinement of the given `𝒰` in the subset sense: it is
indexed by the points of `X`, and each of its charts sits inside a chart of `𝒰` only because it
was built from one. Nothing below needs more than that. -/
theorem IsTopFiniteTypeHom.exists_basicTargetRefinement (hI : I.FG)
    (h : IsTopFiniteTypeHom f) :
    ∃ (𝒱' : OpenCover (FormalScheme.Spf I)) (𝒰' : OpenCover X),
      IsTopFiniteTypeHomOn f 𝒱' 𝒰' ∧
        ∀ i : 𝒱'.J, ∃ g : R, Set.range (𝒱'.map i).toLRSHom.base =
          Set.range (FormalSpectrum.basicOpenChart I g).base := by
  obtain ⟨𝒱, 𝒰, hOn⟩ := h
  set charts : ∀ x : X, BasicTargetChart f x :=
    fun x => (nonempty_basicTargetChart hI hOn x).some with hcharts_def
  exact ⟨OpenCover.ofBasicTargetChartsTarget charts, OpenCover.ofBasicTargetCharts charts,
    isTopFiniteTypeHomOn_ofBasicTargetCharts charts,
    exists_range_eq_basicOpenChart_ofBasicTargetChartsTarget hI charts⟩

/-- **Conservativity at a fixed pair of covers, with no adicity hypothesis.** The hypothesis-free
form of `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHomOn.isRelativelyTopFiniteType`
(`FormalSchemes.ConservativityTopFiniteType`): the given covers are discarded and replaced by the
refinement, so no chart of the cover this actually consumes needs the adicity as a hypothesis.

Unlike the theorem it replaces, this does **not** return the cover `𝒰` unrefined — the witness it
produces is against `OpenCover.ofBasicTargetCharts`. -/
theorem IsTopFiniteTypeHomOn.isRelativelyTopFiniteType_of_fg (hI : I.FG)
    {𝒱 : OpenCover (FormalScheme.Spf I)} {𝒰 : OpenCover X}
    (hOn : IsTopFiniteTypeHomOn f 𝒱 𝒰) : IsRelativelyTopFiniteType R I f := by
  set charts : ∀ x : X, BasicTargetChart f x :=
    fun x => (nonempty_basicTargetChart hI hOn x).some with hcharts_def
  exact (isTopFiniteTypeHomOn_ofBasicTargetCharts charts).isRelativelyTopFiniteType_of_basicOpen hI
    (exists_range_eq_basicOpenChart_ofBasicTargetChartsTarget hI charts)

/-- **Conservativity** (EGA I, 10.13), with no hypothesis beyond `I.FG`: at an affine target, a
topologically-finite-type morphism of formal schemes is topologically of finite type over the
base.

The converse is `AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType.isTopFiniteTypeHom`
(`FormalSchemes.TopFiniteTypeHom`). This supersedes
`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.isRelativelyTopFiniteType`
(`FormalSchemes.ConservativityTopFiniteType`), whose extra hypothesis
`AlgebraicGeometry.FormalScheme.IsAdicOpenImmersionProperty` is redundant — that property is not
proved here and remains open on its own terms. -/
theorem IsTopFiniteTypeHom.isRelativelyTopFiniteType_of_fg (hI : I.FG)
    (h : IsTopFiniteTypeHom f) : IsRelativelyTopFiniteType R I f := by
  obtain ⟨𝒱, 𝒰, hOn⟩ := h
  exact hOn.isRelativelyTopFiniteType_of_fg hI

/-- **The two notions of topological finite type agree at an affine target**, for `I` finitely
generated and with nothing else assumed. EGA I 10.13's equivalence, and the unconditional form of
`AlgebraicGeometry.FormalScheme.isRelativelyTopFiniteType_iff_isTopFiniteTypeHom`
(`FormalSchemes.ConservativityTopFiniteType`). -/
theorem isRelativelyTopFiniteType_iff_isTopFiniteTypeHom_of_fg (hI : I.FG)
    (f : X ⟶ FormalScheme.Spf I) :
    IsRelativelyTopFiniteType R I f ↔ IsTopFiniteTypeHom f :=
  ⟨fun h => h.isTopFiniteTypeHom hI, fun h => h.isRelativelyTopFiniteType_of_fg hI⟩

/-! ### Applications -/

/-- **The base-affine notion composes through a non-affine intermediate.** If `φ : W ⟶ Y` is
topologically of finite type as a morphism and `g : Y ⟶ Spf I` is topologically of finite type
over `(R, I)`, so is `φ ≫ g` — with `Y` an arbitrary formal scheme.

An application rather than a restatement, and one the base-affine notion cannot reach on its own:
`AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType.comp_structHom`
(`FormalSchemes.RelativeTopFiniteTypeTrans`) is the same shape with `Y` forced to be `Spf L` and
the second factor forced to be a structural morphism, and that file says so. The first hypothesis
here is `IsTopFiniteTypeHom`, which no base-affine datum produces, so the proof has to leave for
the general notion, compose there
(`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.trans`,
`FormalSchemes.TopFiniteTypeHomTrans`) and return — and returning is conservativity. -/
theorem IsRelativelyTopFiniteType.comp_isTopFiniteTypeHom (hI : I.FG)
    {W Y : FormalScheme.{u}} {φ : W ⟶ Y} (hφ : IsTopFiniteTypeHom φ)
    {g : Y ⟶ FormalScheme.Spf I} (hg : IsRelativelyTopFiniteType R I g) :
    IsRelativelyTopFiniteType R I (φ ≫ g) :=
  (hφ.trans (hg.isTopFiniteTypeHom hI)).isRelativelyTopFiniteType_of_fg hI

/-- **A tf-type morphism into a chart of an affine cover of `Spf I` is relatively tf-type over
`(R, I)`.** The affine cover is arbitrary — its charts are not assumed to be basic opens, nor to be
adic over `(R, I)` in any sense.

`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.comp_chartMap`
(`FormalSchemes.TopFiniteTypeHomTrans`) is the corresponding statement for the general notion, and
was landed there without a base-affine consequence because there was none to be had. This is that
consequence. -/
theorem isRelativelyTopFiniteType_comp_chartMap (hI : I.FG)
    (𝒰 : OpenCover (FormalScheme.Spf I))
    (h𝒰 : ∀ j, ∃ (S : Type u) (_ : CommRing S) (_ : TopologicalSpace S) (K : Ideal S)
      (_ : IsAdicRing K) (_ : K.FG), Nonempty (𝒰.obj j ≅ FormalScheme.Spf K))
    (i : 𝒰.J) {W : FormalScheme.{u}} {φ : W ⟶ 𝒰.obj i} (hφ : IsTopFiniteTypeHom φ) :
    IsRelativelyTopFiniteType R I (φ ≫ 𝒰.map i) :=
  (hφ.comp_chartMap 𝒰 h𝒰 i).isRelativelyTopFiniteType_of_fg hI

/-- **Non-vacuity, fully instantiated.** A topologically-finite-type morphism into the basic-open
chart `Spf (I{1/g}^)` of `Spf I` is relatively tf-type over `(R, I)` after composing down, for
every `g : R` and with no hypothesis beyond `I.FG`.

Every hypothesis is discharged at a named object, so this is an application and not a restatement:
`AlgebraicGeometry.FormalScheme.isRelativelyTopFiniteType_basicOpenChart`
(`FormalSchemes.ConservativityTopFiniteType`) supplies the second factor, and it is *not*
`AlgebraicGeometry.IsTopologicallyFiniteType.structHom` of anything on the nose — recognising it as
one is what `FormalSpectrum.structMap_eq_generalCofinalSpfIso_comp` does, and it fails `rfl` — so
`AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType.comp_structHom`
(`FormalSchemes.RelativeTopFiniteTypeTrans`) does not apply to it. -/
theorem isRelativelyTopFiniteType_comp_basicOpenChart (hI : I.FG) (g : R) {W : FormalScheme.{u}} :
    haveI := FormalSpectrum.isAdicRing_awayCompletionIdeal I g hI
    ∀ {φ : W ⟶ FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal I g)},
      IsTopFiniteTypeHom φ →
        IsRelativelyTopFiniteType R I (φ ≫ Hom.mk (FormalSpectrum.basicOpenChart I g)) :=
  haveI := FormalSpectrum.isAdicRing_awayCompletionIdeal I g hI
  fun hφ => IsRelativelyTopFiniteType.comp_isTopFiniteTypeHom hI hφ
    (isRelativelyTopFiniteType_basicOpenChart hI g)

end AlgebraicGeometry.FormalScheme
