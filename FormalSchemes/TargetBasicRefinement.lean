import FormalSchemes.ConservativityTopFiniteType

set_option linter.style.header false

/-!
# Refining the target cover of a finite-type morphism to basic opens
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormalScheme

variable {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]
variable {X : FormalScheme.{u}}

/-- The per-point data of a refined witness. -/
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

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **A refined chart exists at every point.** -/
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
  have hKcfg : (FormalSpectrum.awayCompletionIdeal K c).FG := by
    rw [← FormalSpectrum.map_awayCompletionHom]; exact hKfg.map _
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

/-- **The refined cover of `X`**, indexed by the points of `X`. -/
def OpenCover.ofBasicTargetCharts (charts : ∀ x : X, BasicTargetChart f x) : OpenCover X where
  J := X
  obj x := FormalScheme.Spf (charts x).L
  map x := (charts x).src
  f x := x
  covers x := (charts x).mem
  isOpenImmersion x := (charts x).isOpenImmersionSrc

/-- **The refined cover of `Spf I`**: the middle charts, together with `Spf I` itself. -/
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

/-- The two assembled covers witness `IsTopFiniteTypeHomOn`. -/
theorem isTopFiniteTypeHomOn_ofBasicTargetCharts (charts : ∀ x : X, BasicTargetChart f x) :
    IsTopFiniteTypeHomOn f (OpenCover.ofBasicTargetChartsTarget charts)
      (OpenCover.ofBasicTargetCharts charts) := by
  intro x
  refine ⟨Sum.inl x, (charts x).S, inferInstance, inferInstance, (charts x).K, inferInstance,
    (charts x).fgK, (charts x).A, inferInstance, inferInstance, inferInstance, (charts x).L,
    inferInstance, (charts x).hA, Iso.refl _, Iso.refl _, ?_⟩
  simpa [OpenCover.ofBasicTargetCharts, OpenCover.ofBasicTargetChartsTarget] using
    (charts x).compat

/-- **Every chart of the refined target cover has basic range.** -/
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

/-- **The target-side refinement.** -/
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

/-- **Conservativity at a fixed pair of covers, with no adicity hypothesis.** -/
theorem IsTopFiniteTypeHomOn.isRelativelyTopFiniteType_of_fg (hI : I.FG)
    {𝒱 : OpenCover (FormalScheme.Spf I)} {𝒰 : OpenCover X}
    (hOn : IsTopFiniteTypeHomOn f 𝒱 𝒰) : IsRelativelyTopFiniteType R I f := by
  set charts : ∀ x : X, BasicTargetChart f x :=
    fun x => (nonempty_basicTargetChart hI hOn x).some with hcharts_def
  exact (isTopFiniteTypeHomOn_ofBasicTargetCharts charts).isRelativelyTopFiniteType_of_basicOpen hI
    (exists_range_eq_basicOpenChart_ofBasicTargetChartsTarget hI charts)

/-- **Conservativity (EGA I, 10.13), with no hypothesis beyond `I.FG`.** -/
theorem IsTopFiniteTypeHom.isRelativelyTopFiniteType_of_fg (hI : I.FG)
    (h : IsTopFiniteTypeHom f) : IsRelativelyTopFiniteType R I f := by
  obtain ⟨𝒱, 𝒰, hOn⟩ := h
  exact hOn.isRelativelyTopFiniteType_of_fg hI

/-- **The two notions of topological finite type agree at an affine target.** -/
theorem isRelativelyTopFiniteType_iff_isTopFiniteTypeHom_of_fg (hI : I.FG)
    (f : X ⟶ FormalScheme.Spf I) :
    IsRelativelyTopFiniteType R I f ↔ IsTopFiniteTypeHom f :=
  ⟨fun h => h.isTopFiniteTypeHom hI, fun h => h.isRelativelyTopFiniteType_of_fg hI⟩

/-! ### Applications -/

/-- **The base-affine notion composes through a non-affine intermediate.** -/
theorem IsRelativelyTopFiniteType.comp_isTopFiniteTypeHom (hI : I.FG)
    {W Y : FormalScheme.{u}} {φ : W ⟶ Y} (hφ : IsTopFiniteTypeHom φ)
    {g : Y ⟶ FormalScheme.Spf I} (hg : IsRelativelyTopFiniteType R I g) :
    IsRelativelyTopFiniteType R I (φ ≫ g) :=
  (hφ.trans (hg.isTopFiniteTypeHom hI)).isRelativelyTopFiniteType_of_fg hI

/-- **A tf-type morphism into a chart of an affine cover of `Spf I` is relatively tf-type over
`(R, I)`.** -/
theorem isRelativelyTopFiniteType_comp_chartMap (hI : I.FG)
    (𝒰 : OpenCover (FormalScheme.Spf I))
    (h𝒰 : ∀ j, ∃ (S : Type u) (_ : CommRing S) (_ : TopologicalSpace S) (K : Ideal S)
      (_ : IsAdicRing K) (_ : K.FG), Nonempty (𝒰.obj j ≅ FormalScheme.Spf K))
    (i : 𝒰.J) {W : FormalScheme.{u}} {φ : W ⟶ 𝒰.obj i} (hφ : IsTopFiniteTypeHom φ) :
    IsRelativelyTopFiniteType R I (φ ≫ 𝒰.map i) :=
  (hφ.comp_chartMap 𝒰 h𝒰 i).isRelativelyTopFiniteType_of_fg hI

end AlgebraicGeometry.FormalScheme
