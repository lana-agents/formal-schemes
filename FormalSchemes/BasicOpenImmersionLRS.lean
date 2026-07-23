import FormalSchemes.BasicOpenImmersionAssembly
import Mathlib.Geometry.RingedSpace.OpenImmersion

set_option linter.style.header false

/-!
# The affine basic-open chart is an open immersion of locally ringed spaces (issue 163)

For an adic ring `(R, I)` with `I.FG` and `f : R`, this file completes issue 163: the affine
basic-open chart `FormalSpectrum.basicOpenChart I f : Spf R{1/f} ⟶ Spf R` is a
`LocallyRingedSpace.IsOpenImmersion` with underlying-space range `basicOpen I f`.

The two halves are already merged:

* **base_open**: `isOpenEmbedding_basicOpenChartBase` / `range_basicOpenChartBase`
  (`BasicOpenChart.lean`) — the underlying map is an open topological embedding onto `D(f)`.
* **`c_iso` on the basis `{D(f·g)}`**: `bijective_chartComponent`
  (`BasicOpenImmersionAssembly.lean`) — the sheaf `c`-component of the chart on each basic open
  `D(f·g) ⊆ D(f)`, conjugated by `sectionsBasicOpenEquiv`, is a ring isomorphism.

This file packages those into `PresheafedSpace.IsOpenImmersion (basicOpenChart I f).toShHom.hom`
(defeq the `presheafedSpaceMap`), hence `SheafedSpace.IsOpenImmersion` and
`LocallyRingedSpace.IsOpenImmersion`.

## Main results

* `FormalSpectrum.isOpenImmersion_basicOpenChart` — `LocallyRingedSpace.IsOpenImmersion` of the
  chart.
* `FormalSpectrum.range_basicOpenChart` — the range of its base is `basicOpen I f`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Topology

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f : R)

section Packaging

variable {S : Type u} [CommRing S] (J : Ideal S) (φ : R →+* S)
  (hφ : I ≤ J.comap φ)

/-- The **source-space comparison morphism** of the chart: on a source open `W`, it is the
`c`-component `mapSheafHom.app` on the image `he.functor.obj W`, transported by the structure-sheaf
restriction along `(mapTop)⁻¹ (he.functor.obj W) = W`. As a morphism of the (source-space) sheaves
`he.functor.op ⋙ O_{Spf R}` (the pushforward/restriction of the target structure sheaf) and
`O_{Spf S}`, it is a *global* iso exactly when the chart's `c`-component is an isomorphism on every
open contained in the range — which we verify on a basis. -/
def chartComparison (he : IsOpenEmbedding (mapTop I J φ hφ)) :
    (he.functor.op ⋙ (structureSheaf I).presheaf) ⟶ (structureSheaf J).presheaf where
  app W := ((mapSheafHom I J φ hφ).hom.app (he.functor.op.obj W)) ≫
    (structureSheaf J).presheaf.map (eqToHom (congrArg op
      (Opens.map_functor_eq' (mapTop I J φ hφ) he W.unop)))
  naturality U V i := by
    have hn := (mapSheafHom I J φ hφ).hom.naturality (he.functor.op.map i)
    dsimp only [Functor.comp_map, Functor.op_map]
    rw [Category.assoc]
    erw [reassoc_of% hn]
    congr 1
    simp only [TopCat.Sheaf.pushforward_obj_val, TopCat.Presheaf.pushforward_obj_map]
    erw [← Functor.map_comp, ← Functor.map_comp]
    congr 1

/-- The comparison morphism packaged as a morphism of sheaves on the source space `Spf S`. -/
def chartComparisonSheaf (he : IsOpenEmbedding (mapTop I J φ hφ)) :
    ((sheafedSpaceObj I).restrict he).sheaf ⟶ structureSheaf J :=
  ObjectProperty.homMk (chartComparison I J φ hφ he)

end Packaging

/-!
### Route

`LocallyRingedSpace.IsOpenImmersion (basicOpenChart I f)` unfolds to
`PresheafedSpace.IsOpenImmersion (presheafedSpaceMap I J φ hφ)`, whose two fields are the open
embedding `base_open` (from `isOpenEmbedding_basicOpenChartBase`) and `c_iso`, an isomorphism of the
`c`-component `mapSheafHom.app` on every open `he.functor.obj U ⊆ D(f)`.

The `c`-component is *not* a global iso on `FormalSpectrum I` (over `⊤` it is `R → R{1/f}`), so we
transfer to a morphism of sheaves **on the source space** `FormalSpectrum J`, where it is a global
iso: `chartComparison` reads the chart's `c`-component on the image `he.functor.obj W` of each
source open `W`, and `isIso_chartComparisonSheaf` proves it a global sheaf isomorphism on the basis
of preimages of `{D(f·g)}` (`isIso_c_app_basicOpen` + `TopCat.Sheaf.isIso_iff_isIso_basis`). Reading
off the component at `op U` and cancelling the structure-sheaf restriction gives the `c_iso` field.
-/

/-- **The chart's sheaf `c`-component is an isomorphism on each basic open `D(g) ⊆ D(f)`.**
Extracted from `bijective_chartComponent` by cancelling the three flanking isomorphisms
(`sectionsBasicOpenEquiv` on both sides and the structure-sheaf restriction along the open equality
`(mapTop)⁻¹ D(g) = D(ḡ)`) that conjugate the sheaf component into `chartComponent`. -/
theorem isIso_c_app_basicOpen (hI : I.FG) (g : R)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    IsIso ((basicOpenChart I f).c.app (op (basicOpen I g))) := by
  set J := awayCompletionIdeal I f with hJ
  set φ := awayCompletionHom I f with hφd
  set hφ := le_comap_awayCompletionHom I f with hφl
  rw [ConcreteCategory.isIso_iff_bijective]
  -- bijectivity of the chart's conjugated component (the ring-side fact) …
  have hb := bijective_chartComponent I f g hI hfg
  -- … and bijectivity of the three flanking isomorphisms
  have h1 := (sectionsBasicOpenEquiv J (φ g)).bijective
  have h3 := (sectionsBasicOpenEquiv I g).symm.bijective
  haveI hM : IsIso ((structureSheaf J).presheaf.map
      (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g)))) := inferInstance
  have h2 := (ConcreteCategory.isIso_iff_bijective ((structureSheaf J).presheaf.map
      (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g))))).mp hM
  -- unfold `chartComponent` to the composite of the four ring homomorphisms and peel the flanks
  unfold chartComponent at hb
  simp only [RingHom.coe_comp] at hb
  replace hb := (h1.of_comp_iff' _).mp hb
  replace hb := (h2.of_comp_iff' _).mp hb
  exact (Function.Bijective.of_comp_iff _ h3).mp hb

/-- The image under the chart's open embedding of the preimage of a basic open `D(h)` is
`D(f · h) = D(h) ⊓ D(f)` (intersect with the range `D(f)`). -/
theorem chartFunctor_image_preimage (hI : I.FG) (h : R)
    (he : IsOpenEmbedding (mapTop I (awayCompletionIdeal I f) (awayCompletionHom I f)
      (le_comap_awayCompletionHom I f))) :
    he.functor.obj ((Opens.map (mapTop I (awayCompletionIdeal I f) (awayCompletionHom I f)
      (le_comap_awayCompletionHom I f))).obj (basicOpen I h)) = basicOpen I (f * h) := by
  rw [Opens.functor_obj_map_obj]
  have htop : he.functor.obj ⊤ = basicOpen I f := by
    apply Opens.ext
    rw [IsOpenMap.coe_functor_obj, Opens.coe_top, Set.image_univ]
    exact range_basicOpenChartBase I f hI
  rw [htop, basicOpen_mul]

/-- **The source-space comparison sheaf morphism of the chart is a (global) isomorphism.** Proved on
the basis of preimages `(mapTop)⁻¹ D(h)` of the basic opens of `Spf R`, where the comparison
restricts (on `(mapTop)⁻¹ D(h)`, whose image is `D(f · h) ⊆ D(f)`) to the chart's `c`-component,
an isomorphism by `isIso_c_app_basicOpen`. -/
theorem isIso_chartComparisonSheaf (hI : I.FG)
    (he : IsOpenEmbedding (mapTop I (awayCompletionIdeal I f) (awayCompletionHom I f)
      (le_comap_awayCompletionHom I f))) :
    IsIso (chartComparisonSheaf I (awayCompletionIdeal I f) (awayCompletionHom I f)
      (le_comap_awayCompletionHom I f) he) := by
  set J := awayCompletionIdeal I f with hJ
  set φ := awayCompletionHom I f with hφd
  set hφ := le_comap_awayCompletionHom I f with hφl
  set B : R → Opens (FormalSpectrum J) :=
    fun h => (Opens.map (mapTop I J φ hφ)).obj (basicOpen I h) with hB
  have hbasis : Opens.IsBasis (Set.range B) := by
    change TopologicalSpace.IsTopologicalBasis (((↑) : _ → Set (FormalSpectrum J)) '' Set.range B)
    have h2 := (isTopologicalBasis_basicOpen I).isInducing he.isInducing
    have heq : (((↑) : _ → Set (FormalSpectrum J)) '' Set.range B) =
        Set.preimage ⇑(mapTop I J φ hφ) ''
          Set.range (fun g => (basicOpen I g : Set (FormalSpectrum I))) := by
      rw [hB, ← Set.range_comp, ← Set.range_comp]
      rfl
    rw [heq]; exact h2
  have happ : ∀ h : R, IsIso ((chartComparisonSheaf I J φ hφ he).hom.app (op (B h))) := by
    intro h
    have hkey : IsIso ((basicOpenChart I f).c.app (op (basicOpen I (f * h)))) :=
      isIso_c_app_basicOpen I f hI (f * h) (isUnit_algebraMap_away_left f h)
    have h1 : IsIso ((mapSheafHom I J φ hφ).hom.app (he.functor.op.obj (op (B h)))) := by
      have hidx : he.functor.op.obj (op (B h)) = op (basicOpen I (f * h)) :=
        congrArg op (chartFunctor_image_preimage I f hI h he)
      rw [hidx]; exact hkey
    have hB2 : IsIso ((structureSheaf J).presheaf.map
        (eqToHom (congrArg op (Opens.map_functor_eq' (mapTop I J φ hφ) he (op (B h)).unop)))) :=
      inferInstance
    change IsIso ((chartComparison I J φ hφ he).app (op (B h)))
    rw [chartComparison]
    change IsIso (_ ≫ _)
    exact IsIso.comp_isIso' h1 hB2
  exact TopCat.Sheaf.isIso_iff_isIso_basis hbasis happ

/-- **Issue 163 — the affine basic-open chart is an open immersion.** For `(R, I)` adic with `I.FG`
and `f : R`, the chart `basicOpenChart I f : Spf R{1/f} ⟶ Spf R` is an open immersion of locally
ringed spaces. -/
theorem isOpenImmersion_basicOpenChart (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion (basicOpenChart I f) := by
  set J := awayCompletionIdeal I f with hJ
  set φ := awayCompletionHom I f with hφd
  set hφ := le_comap_awayCompletionHom I f with hφl
  have he : IsOpenEmbedding (mapTop I J φ hφ) := isOpenEmbedding_basicOpenChartBase I f hI
  haveI := isIso_chartComparisonSheaf I f hI he
  haveI hval : IsIso (chartComparison I J φ hφ he) :=
    inferInstanceAs (IsIso ((TopCat.Sheaf.forget CommRingCat _).map
      (chartComparisonSheaf I J φ hφ he)))
  refine ⟨he, fun U => ?_⟩
  change IsIso ((mapSheafHom I J φ hφ).hom.app (op (he.functor.obj U)))
  haveI happU : IsIso ((chartComparison I J φ hφ he).app (op U)) := inferInstance
  have heq : (Opens.map (mapTop I J φ hφ)).obj (he.functor.obj U) = U :=
    Opens.map_functor_eq' (mapTop I J φ hφ) he U
  haveI hB : IsIso ((structureSheaf J).presheaf.map (eqToHom (congrArg op heq))) := by
    rw [eqToHom_map]; infer_instance
  -- Work at the level of underlying ring maps to avoid the `TopCat.Presheaf` opacity: the chart's
  -- conjugated component `chartComparison.app` is `mapSheafHom.app ≫ (restriction)` definitionally,
  -- both bijective; cancelling the (bijective) restriction leaves `mapSheafHom.app` bijective.
  rw [ConcreteCategory.isIso_iff_bijective]
  have hbij := (ConcreteCategory.isIso_iff_bijective _).mp happU
  have hgbij := (ConcreteCategory.isIso_iff_bijective _).mp hB
  have happ_eq : (chartComparison I J φ hφ he).app (op U) =
      (mapSheafHom I J φ hφ).hom.app (op (he.functor.obj U)) ≫
        (structureSheaf J).presheaf.map (eqToHom (congrArg op heq)) := rfl
  rw [happ_eq] at hbij
  have hcoe : ⇑((mapSheafHom I J φ hφ).hom.app (op (he.functor.obj U)) ≫
        (structureSheaf J).presheaf.map (eqToHom (congrArg op heq))) =
      ⇑((structureSheaf J).presheaf.map (eqToHom (congrArg op heq))) ∘
        ⇑((mapSheafHom I J φ hφ).hom.app (op (he.functor.obj U))) := by
    funext x; rfl
  rw [hcoe] at hbij
  exact (hgbij.of_comp_iff' _).mp hbij

/-- The range of the base map of the affine basic-open chart is `basicOpen I f = D(f)`. -/
theorem range_basicOpenChart (hI : I.FG) :
    Set.range (basicOpenChart I f).toShHom.hom.base = (basicOpen I f : Set (FormalSpectrum I)) := by
  exact range_basicOpenChartBase I f hI

end FormalSpectrum
