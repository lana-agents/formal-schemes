import FormalSchemes.AdicOverBaseChart
import FormalSchemes.AffineFibreProductLRS
import FormalSchemes.GeneralFibreProductChartInter
import FormalSchemes.GlueOpenCoverFactorBothAlg
import FormalSchemes.OpenCoverHomExt

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Adic-tracking refined cover and an internal-continuity uniqueness variant

This file provides an *adic-tracking* variant of the source-cover refinement of
`FormalSchemes.GlueOpenCoverFactor` together with a corresponding variant of
`BothChartedFibreDatumXY.fibreLift_unique` whose per-chart continuity hypothesis `hcont` is
discharged internally from a source `AdicOverBaseLocallyFG` witness.

## Part 1 — the adic-tracking cover

Mirroring `GlueOpenCoverFactor`, but with a base morphism `s : Z ⟶ Spf I`, the structure
`RefinedChartAdic` records, on top of the plain `RefinedChart` data, the base-relative adicity
bound `I ≤ J.comap (Γ (map ≫ s))` inherited from `AdicOverBaseLocallyFG`. The associated
`refinedCoverAdic` / `chartIndexAdic` / `factorAdic` / `factorAdic_comp_ι` mirror the plain
versions and thread the adic witness.

## Part 2 — the uniqueness variant

`BothChartedFibreDatumXY.fibreLift_unique_adicOverBase` replaces the standing `hcont` hypothesis of
`fibreLift_unique` with a source witness `hZadic : AdicOverBaseLocallyFG Z s` together with the
compatibility `m₁ ≫ (pr₁ ≫ xStructMap) = s`. The per-chart continuity fact is then *derived* from
the recorded adic bound of the refined chart, via the morphism identity
`chart.map ≫ s = factorAdic … ≫ (pr₁ChartSelf ≫ xStructMapChart)` pushed to global sections.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.FormalScheme.GlueData

variable {Z : FormalScheme.{u}} (D : GlueData.{u})
  (a : Z.toLocallyRingedSpace ⟶ D.gluedFormalScheme.toLocallyRingedSpace)
  {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]
  (s : Z.toLocallyRingedSpace ⟶ FormalSpectrum.locallyRingedSpaceObj I)

/-- The per-point data refining the source cover of `Z` along `a : Z ⟶ D.gluedFormalScheme`,
tracking base-relative adicity: a finitely generated affine open-immersion chart of `Z` around `z`
whose range lies inside `a⁻¹(range (D.ι idx))` for a single glued chart, together with the bound
`I ≤ J.comap (Γ (map ≫ s))` inherited from the base morphism `s : Z ⟶ Spf I`. -/
structure RefinedChartAdic (z : Z) where
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
  [adicRing : IsAdicRing J]
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
  /-- The chart is adic on global sections over the base `s`. -/
  adic : I ≤ J.comap (FormalSpectrum.globalSectionsMap I J (map ≫ s))

attribute [instance] RefinedChartAdic.commRing RefinedChartAdic.topR RefinedChartAdic.adicRing
  RefinedChartAdic.isOpenImmersion

variable {D a s}

/-- A refined adic-over-base chart exists around every point of an `AdicOverBaseLocallyFG` source:
the glued charts jointly cover `a z`, giving an index `i`; the preimage `a⁻¹(range (D.ι i))` is open
and contains `z`, so the adic-over-base neighborhood basis
(`exists_affineChart_subset_adicOverBase`) supplies a finitely generated affine chart landing inside
it that is adic on global sections over `s`. -/
theorem nonempty_refinedChartAdic (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s) (z : Z) :
    Nonempty (RefinedChartAdic D a s z) := by
  obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective (a.base z)
  have hUopen : IsOpen (a.base ⁻¹' Set.range (D.ι i).base) :=
    (D.ι_isOpenImmersion i).base_open.isOpen_range.preimage a.base.hom.continuous
  have hzU : z ∈ a.base ⁻¹' Set.range (D.ι i).base := by
    simp only [Set.mem_preimage]; exact ⟨y, hy⟩
  obtain ⟨S, _, _, J, _, f, hJfg, hzmem, hsub, hoi, hadicf⟩ :=
    Z.exists_affineChart_subset_adicOverBase s hZadic z _ hUopen hzU
  refine ⟨?_⟩
  exact
    { idx := i, R := S, J := J, map := f, fg := hJfg, mem := hzmem, subset := hsub,
      adic := hadicf }

variable (D a s)

/-- A chosen refined adic-over-base chart around each point, via `Classical.choice`. -/
def refinedChartAdic (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s) (z : Z) :
    RefinedChartAdic D a s z :=
  (nonempty_refinedChartAdic hZadic z).some

/-- The **refined adic-over-base open cover** of an `AdicOverBaseLocallyFG` source `Z` along a
morphism `a : Z ⟶ D.gluedFormalScheme`: indexed by the points of `Z`, the piece at `z` is the
finitely generated affine chart `refinedChartAdic D a s hZadic z`. -/
def refinedCoverAdic (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s) : OpenCover Z where
  J := Z
  obj z := FormalScheme.Spf (D.refinedChartAdic a s hZadic z).J
  map z := Hom.mk (D.refinedChartAdic a s hZadic z).map
  f z := z
  covers z := (D.refinedChartAdic a s hZadic z).mem
  isOpenImmersion z := (D.refinedChartAdic a s hZadic z).isOpenImmersion

/-- The glued-chart index selected for each piece of the refined adic-over-base cover. -/
def chartIndexAdic (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s)
    (c : (D.refinedCoverAdic a s hZadic).J) :
    D.toLocallyRingedSpaceGlueData.J :=
  (D.refinedChartAdic a s hZadic c).idx

/-- The range of `map c ≫ a` on a refined adic-over-base cover piece lies inside the range of the
selected glued chart `D.ι (chartIndexAdic c)`. -/
theorem refinedChartAdic_range_comp_subset (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s)
    (c : (D.refinedCoverAdic a s hZadic).J) :
    Set.range ((D.refinedChartAdic a s hZadic c).map ≫ a).base ⊆
      Set.range (D.ι (D.chartIndexAdic a s hZadic c)).base := by
  rintro w ⟨t, rfl⟩
  simp only [LocallyRingedSpace.comp_base, TopCat.comp_app]
  exact (D.refinedChartAdic a s hZadic c).subset ⟨t, rfl⟩

/-- The **chart-wise factorization** of the source cover: on the piece `c`, the restriction
`map c ≫ a` of `a` factors through the single glued chart `D.U (chartIndexAdic c)`. -/
def factorAdic (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s)
    (c : (D.refinedCoverAdic a s hZadic).J) :
    FormalSpectrum.locallyRingedSpaceObj (D.refinedChartAdic a s hZadic c).J ⟶
      D.toLocallyRingedSpaceGlueData.U (D.chartIndexAdic a s hZadic c) :=
  LocallyRingedSpace.IsOpenImmersion.lift (D.ι (D.chartIndexAdic a s hZadic c))
    ((D.refinedChartAdic a s hZadic c).map ≫ a)
    (D.refinedChartAdic_range_comp_subset a s hZadic c)

/-- The factorization is compatible with the glued inclusion:
`factorAdic c ≫ D.ι (chartIndexAdic c)` recovers `map c ≫ a`. -/
@[reassoc]
theorem factorAdic_comp_ι (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s)
    (c : (D.refinedCoverAdic a s hZadic).J) :
    D.factorAdic a s hZadic c ≫ D.ι (D.chartIndexAdic a s hZadic c) =
      (D.refinedChartAdic a s hZadic c).map ≫ a :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry.FormalScheme.GlueData

open CategoryTheory.Limits FormalSpectrum CompletedTensorProduct

namespace AlgebraicGeometry.BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable (D : BothChartedFibreDatumXY R I hI)

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace R] [IsAdicRing I] in
/-- The product chart inclusion composed with the `X`-structural map to the base factors through the
first product projection: `ι p ≫ (pr₁ ≫ xStructMap) = pr₁ChartSelf p ≫ xStructMapChart p.1`. This
is stated over an explicit product index `p : JX × JY` (so `p.1` is well-typed), and instantiated in
`fibreLift_unique_adicOverBase` at the refined-chart index `P`. -/
theorem ι_pr₁_comp_xStructMap
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (p : D.JX × D.JY) :
    D.formalGlueData.ι p ≫ (D.pr₁ hV hf ht ≫ D.xStructMap) =
      D.pr₁ChartSelf p ≫ D.xStructMapChart p.1 := by
  rw [← Category.assoc, D.ι_pr₁ hV hf ht p, Category.assoc, D.ι_xStructMap p.1]

/-- **Uniqueness of the general fibre-product mediating morphism, adic-over-base variant.** Two
morphisms `m₁ m₂ : Z ⟶ X ×_{Spf R} Y` out of a formal scheme `Z` equipped with a base morphism
`s : Z ⟶ Spf I` that agree after both projections coincide, provided `Z` is adic over the base `s`
(`hZadic`) and `m₁` followed by the `X`-structural composite `pr₁ ≫ xStructMap` equals `s`
(`hstruct`). This discharges the per-chart continuity hypothesis `hcont` of `fibreLift_unique`
internally, from the recorded adic bound of each refined chart. -/
theorem fibreLift_unique_adicOverBase
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    {Z : FormalScheme.{u}}
    (m₁ m₂ : Z.toLocallyRingedSpace ⟶ D.generalFibreProduct.toLocallyRingedSpace)
    (s : Z.toLocallyRingedSpace ⟶ FormalSpectrum.locallyRingedSpaceObj I)
    (hZadic : FormalScheme.AdicOverBaseLocallyFG Z s)
    (hpr₁ : m₁ ≫ D.pr₁ hV hf ht = m₂ ≫ D.pr₁ hV hf ht)
    (hpr₂ : m₁ ≫ D.pr₂ hV hf ht = m₂ ≫ D.pr₂ hV hf ht)
    (hstruct : m₁ ≫ (D.pr₁ hV hf ht ≫ D.xStructMap) = s) :
    m₁ = m₂ := by
  refine (D.formalGlueData.refinedCoverAdic m₁ s hZadic).hom_ext m₁ m₂ (fun c => ?_)
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  letI := D.topologyA
  letI := D.isAdicA
  letI := D.topologyB
  letI := D.isAdicB
  -- Abbreviations local to the piece `c`.
  set P := D.formalGlueData.chartIndexAdic m₁ s hZadic c with hP
  set chart := D.formalGlueData.refinedChartAdic m₁ s hZadic c with hchart
  set fac := D.formalGlueData.factorAdic m₁ s hZadic c with hfacdef
  haveI : IsAdicRing (idealOfDefinition R I (D.A P.1) (D.B P.2)) :=
    CompletedTensorProduct.isAdicRing R I (D.A P.1) (D.B P.2) hI
  -- The factorization of `w ≫ m₁` through the product chart `P`.
  have hfac : fac ≫ D.formalGlueData.ι P = chart.map ≫ m₁ :=
    D.formalGlueData.factorAdic_comp_ι m₁ s hZadic c
  -- STEP 3: `m₂`'s image on the piece lands in the same product chart `P`.
  have hsub : Set.range (chart.map ≫ m₂).base ⊆ Set.range (D.formalGlueData.ι P).base := by
    have hlem := D.range_ι_eq_pr_preimage_inter hV hf ht P
    rintro x ⟨t, rfl⟩
    refine hlem.ge ⟨?_, ?_⟩
    · rw [Set.mem_preimage]
      have e : (chart.map ≫ m₂) ≫ D.pr₁ hV hf ht =
          fac ≫ D.formalGlueData.ι P ≫ D.pr₁ hV hf ht := by
        have h1 : fac ≫ D.formalGlueData.ι P ≫ D.pr₁ hV hf ht =
            (chart.map ≫ m₁) ≫ D.pr₁ hV hf ht :=
          (reassoc_of% hfac) (D.pr₁ hV hf ht)
        rw [h1, Category.assoc, Category.assoc, hpr₁]
      have hpt := congrArg (fun m => m.base t) e
      have hip := congrArg (fun m => m.base (fac.base t)) (D.ι_pr₁ hV hf ht P)
      simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at hpt hip ⊢
      rw [hpt, hip]
      exact ⟨_, rfl⟩
    · rw [Set.mem_preimage]
      have e : (chart.map ≫ m₂) ≫ D.pr₂ hV hf ht =
          fac ≫ D.formalGlueData.ι P ≫ D.pr₂ hV hf ht := by
        have h1 : fac ≫ D.formalGlueData.ι P ≫ D.pr₂ hV hf ht =
            (chart.map ≫ m₁) ≫ D.pr₂ hV hf ht :=
          (reassoc_of% hfac) (D.pr₂ hV hf ht)
        rw [h1, Category.assoc, Category.assoc, hpr₂]
      have hpt := congrArg (fun m => m.base t) e
      have hip := congrArg (fun m => m.base (fac.base t)) (D.ι_pr₂ hV hf ht P)
      simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at hpt hip ⊢
      rw [hpt, hip]
      exact ⟨_, rfl⟩
  -- STEP 4: the second lift `factorSnd c`.
  set fSnd := LocallyRingedSpace.IsOpenImmersion.lift (D.formalGlueData.ι P)
    (chart.map ≫ m₂) hsub with hfSnd
  have hfSnd_fac : fSnd ≫ D.formalGlueData.ι P = chart.map ≫ m₂ := by
    rw [hfSnd]
    exact LocallyRingedSpace.IsOpenImmersion.lift_fac (D.formalGlueData.ι P)
      (chart.map ≫ m₂) hsub
  -- Projection agreements: cancel the mono chart inclusions `ι^X`, `ι^Y`.
  have hproj₁ : fac ≫ D.pr₁ChartSelf P = fSnd ≫ D.pr₁ChartSelf P := by
    have h1 : fac ≫ D.formalGlueData.ι P ≫ D.pr₁ hV hf ht =
        (chart.map ≫ m₁) ≫ D.pr₁ hV hf ht :=
      (reassoc_of% hfac) (D.pr₁ hV hf ht)
    have h2 : fSnd ≫ D.formalGlueData.ι P ≫ D.pr₁ hV hf ht =
        (chart.map ≫ m₂) ≫ D.pr₁ hV hf ht :=
      (reassoc_of% hfSnd_fac) (D.pr₁ hV hf ht)
    have e1 : (fac ≫ D.pr₁ChartSelf P) ≫ D.xFormalGlueData.ι P.1 =
        (chart.map ≫ m₁) ≫ D.pr₁ hV hf ht :=
      ((Category.assoc _ _ _).trans
        (congrArg (fun u => fac ≫ u) (D.ι_pr₁ hV hf ht P).symm)).trans h1
    have e2 : (fSnd ≫ D.pr₁ChartSelf P) ≫ D.xFormalGlueData.ι P.1 =
        (chart.map ≫ m₂) ≫ D.pr₁ hV hf ht :=
      ((Category.assoc _ _ _).trans
        (congrArg (fun u => fSnd ≫ u) (D.ι_pr₁ hV hf ht P).symm)).trans h2
    have emid : (chart.map ≫ m₁) ≫ D.pr₁ hV hf ht = (chart.map ≫ m₂) ≫ D.pr₁ hV hf ht := by
      rw [Category.assoc, Category.assoc, hpr₁]
    exact (cancel_mono (D.xFormalGlueData.ι P.1)).mp (e1.trans (emid.trans e2.symm))
  have hproj₂ : fac ≫ D.pr₂ChartSelf P = fSnd ≫ D.pr₂ChartSelf P := by
    have h1 : fac ≫ D.formalGlueData.ι P ≫ D.pr₂ hV hf ht =
        (chart.map ≫ m₁) ≫ D.pr₂ hV hf ht :=
      (reassoc_of% hfac) (D.pr₂ hV hf ht)
    have h2 : fSnd ≫ D.formalGlueData.ι P ≫ D.pr₂ hV hf ht =
        (chart.map ≫ m₂) ≫ D.pr₂ hV hf ht :=
      (reassoc_of% hfSnd_fac) (D.pr₂ hV hf ht)
    have e1 : (fac ≫ D.pr₂ChartSelf P) ≫ D.yFormalGlueData.ι P.2 =
        (chart.map ≫ m₁) ≫ D.pr₂ hV hf ht :=
      ((Category.assoc _ _ _).trans
        (congrArg (fun u => fac ≫ u) (D.ι_pr₂ hV hf ht P).symm)).trans h1
    have e2 : (fSnd ≫ D.pr₂ChartSelf P) ≫ D.yFormalGlueData.ι P.2 =
        (chart.map ≫ m₂) ≫ D.pr₂ hV hf ht :=
      ((Category.assoc _ _ _).trans
        (congrArg (fun u => fSnd ≫ u) (D.ι_pr₂ hV hf ht P).symm)).trans h2
    have emid : (chart.map ≫ m₁) ≫ D.pr₂ hV hf ht = (chart.map ≫ m₂) ≫ D.pr₂ hV hf ht := by
      rw [Category.assoc, Category.assoc, hpr₂]
    exact (cancel_mono (D.yFormalGlueData.ι P.2)).mp (e1.trans (emid.trans e2.symm))
  -- The `inl`/`algebraMap` global-sections identities (unchanged from `fibreLift_unique`).
  have hJ : idealOfDefinition R I (D.A P.1) (D.B P.2) =
      (I.map (algebraMap R (D.A P.1))).map (inl R I (D.A P.1) (D.B P.2)).toRingHom := by
    rw [idealOfDefinition_eq_map, Ideal.map_map]
    congr 1
  have hgpr : globalSectionsMap (I.map (algebraMap R (D.A P.1)))
      (idealOfDefinition R I (D.A P.1) (D.B P.2)) (D.pr₁ChartSelf P) =
      (inl R I (D.A P.1) (D.B P.2)).toRingHom :=
    globalSectionsMap_locallyRingedSpaceMap _ _ _ _
  have hcomp : (globalSectionsMap (idealOfDefinition R I (D.A P.1) (D.B P.2)) chart.J fac).comp
        (inl R I (D.A P.1) (D.B P.2)).toRingHom =
      (globalSectionsMap (idealOfDefinition R I (D.A P.1) (D.B P.2)) chart.J fSnd).comp
        (inl R I (D.A P.1) (D.B P.2)).toRingHom := by
    rw [← hgpr, ← globalSectionsMap_comp, ← globalSectionsMap_comp]
    exact congrArg (globalSectionsMap (I.map (algebraMap R (D.A P.1))) chart.J) hproj₁
  -- The genuinely new content: derive `factorAdic`'s continuity from the chart's adic bound.
  -- The base-relative morphism identity `chart.map ≫ s = fac ≫ (pr₁ChartSelf ≫ xStructMapChart)`.
  have hιcompat := D.ι_pr₁_comp_xStructMap hV hf ht P
  have hmorph : chart.map ≫ s = fac ≫ (D.pr₁ChartSelf P ≫ D.xStructMapChart P.1) := by
    have h1 : fac ≫ D.formalGlueData.ι P ≫ (D.pr₁ hV hf ht ≫ D.xStructMap) =
        (chart.map ≫ m₁) ≫ (D.pr₁ hV hf ht ≫ D.xStructMap) :=
      (reassoc_of% hfac) (D.pr₁ hV hf ht ≫ D.xStructMap)
    rw [hιcompat, Category.assoc, hstruct] at h1
    exact h1.symm
  -- Push the last factor to global sections: it is the algebra map `R → A ⊗̂_R B`.
  have hHeq : globalSectionsMap I (idealOfDefinition R I (D.A P.1) (D.B P.2))
      (D.pr₁ChartSelf P ≫ D.xStructMapChart P.1) =
      algebraMap R (CompletedTensorProduct R I (D.A P.1) (D.B P.2)) := by
    rw [globalSectionsMap_comp, D.globalSectionsMap_xStructMapChart P.1, hgpr]
    exact (inl R I (D.A P.1) (D.B P.2)).comp_algebraMap
  -- Continuity of `fac` (`hcontc`), from `chart.adic` via the morphism identity above.
  have hcontc : idealOfDefinition R I (D.A P.1) (D.B P.2) ≤
      chart.J.comap
        (globalSectionsMap (idealOfDefinition R I (D.A P.1) (D.B P.2)) chart.J fac) := by
    have hbase := chart.adic
    have hφ : globalSectionsMap I chart.J (fac ≫ (D.pr₁ChartSelf P ≫ D.xStructMapChart P.1))
        = globalSectionsMap I chart.J (chart.map ≫ s) :=
      congrArg (globalSectionsMap I chart.J) hmorph.symm
    have hcomap : chart.J.comap
          (globalSectionsMap I chart.J (fac ≫ (D.pr₁ChartSelf P ≫ D.xStructMapChart P.1)))
        = chart.J.comap (globalSectionsMap I chart.J (chart.map ≫ s)) :=
      congrArg (fun g => chart.J.comap g) hφ
    nth_rewrite 1 [idealOfDefinition_eq_map]
    rw [← hHeq, Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← globalSectionsMap_comp]
    exact le_of_le_of_eq hbase hcomap.symm
  -- Continuity of `factorSnd` is derived from that of `fac` (`hcontc`).
  have hc2 : idealOfDefinition R I (D.A P.1) (D.B P.2) ≤
      chart.J.comap
        (globalSectionsMap (idealOfDefinition R I (D.A P.1) (D.B P.2)) chart.J fSnd) := by
    have hc1 := hcontc
    nth_rewrite 1 [hJ] at hc1 ⊢
    rw [Ideal.map_le_iff_le_comap] at hc1 ⊢
    rw [Ideal.comap_comap, ← hcomp, ← Ideal.comap_comap]
    exact hc1
  -- STEP 5: the two lifts coincide by affine uniqueness.
  have hEq : fac = fSnd :=
    fibreLift_unique_lrs hI chart.fg fac fSnd hcontc hc2 hproj₁ hproj₂
  -- Conclude `w ≫ m₁ = w ≫ m₂`.
  have key : chart.map ≫ m₁ = chart.map ≫ m₂ := by
    rw [← hfac, hEq, hfSnd_fac]
  exact key

end AlgebraicGeometry.BothChartedFibreDatumXY

end
