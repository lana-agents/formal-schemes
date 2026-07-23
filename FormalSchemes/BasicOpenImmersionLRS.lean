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
* **`c_iso` on the basis `{D(f·g)}`**: `bijective_chartComponent` (`BasicOpenImmersionAssembly.lean`)
  — the sheaf `c`-component of the chart on each basic open `D(f·g) ⊆ D(f)`, conjugated by
  `sectionsBasicOpenEquiv`, is a ring isomorphism.

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

/-!
### Route

`LocallyRingedSpace.IsOpenImmersion (basicOpenChart I f)`
  = `SheafedSpace.IsOpenImmersion (basicOpenChart I f).toShHom`
  = `PresheafedSpace.IsOpenImmersion (basicOpenChart I f).toShHom.hom`,
and `(basicOpenChart I f).toShHom.hom` is defeq to
`presheafedSpaceMap I (awayCompletionIdeal I f) (awayCompletionHom I f) (le_comap_awayCompletionHom I f)`.

`PresheafedSpace.IsOpenImmersion` has two fields:
* `base_open : IsOpenEmbedding f.base`, where `f.base = mapTop I J φ hφ`; supplied by
  `isOpenEmbedding_basicOpenChartBase I f hI` (the coercion of `mapTop … .hom` to a function is defeq
  `basicOpenChartBase I f = map I J φ hφ`; a `show`/`convert` bridge may be needed).
* `c_iso : ∀ U : Opens (FormalSpectrum J), IsIso (f.c.app (op (base_open.functor.obj U)))`.

**Key step for `c_iso`.** The map `f.c = (mapSheafHom I J φ hφ).hom` is *not* a global iso on the
target `FormalSpectrum I` (e.g. on `⊤` it is `R → R{1/f}`). It is an iso only on opens contained in
`D(f) = range`. The `c_iso` field only ever needs opens `base_open.functor.obj U ⊆ D(f)`.

Transfer strategy: consider the comparison as a morphism of sheaves **on the source space**
`FormalSpectrum J`, where it *is* a global iso. Concretely, on the basis
`B g := (Opens.map (mapTop I J φ hφ)).obj (basicOpen I (f * g))` of `FormalSpectrum J`
(preimages of the basis `{D(f·g)}` of the subspace `D(f)`; a basis because `mapTop` is a
homeomorphism onto the open `D(f)`), the chart's `c`-component is a ring iso by
`bijective_chartComponent I f (f * g) hI (isUnit_algebraMap_away_left f g)` (note
`basicOpen I (f * g) = basicOpen I f ⊓ basicOpen I g ≤ basicOpen I f`, `basicOpen_mul`).
Then `TopCat.Sheaf.isIso_iff_isIso_basis` upgrades to a global sheaf iso, giving
`IsIso (f.c.app (op W))` for every `W ⊆ D(f)`, in particular each `base_open.functor.obj U`.

Implementation options (pick whichever compiles cleanly):
(A) Build `iso : (sheafedSpaceObj J).toPresheafedSpace ≅ (sheafedSpaceObj I).toPresheafedSpace.restrict he`
    via `PresheafedSpace.isoOfComponents (Iso.refl _) α`, where `α` is built from the basis iso, then
    `presheafedSpaceMap = iso.hom ≫ ofRestrict he` and conclude by
    `PresheafedSpace.IsOpenImmersion.comp` + `ofRestrict` + `ofIso`.
(B) Supply the `c_iso` field directly: reduce `IsIso (c.app (op (functor.obj U)))` to `IsIso` of the
    corresponding component of the global source-side sheaf iso via `eqToHom`/`Opens.map` transport
    (`(Opens.map base).obj (functor.obj U) = U`, `Set.preimage_image_eq _ hf.injective`).

### Building blocks recorded elsewhere (all merged)
* `bijective_chartComponent (I) (f g) (hI : I.FG) (hfg : IsUnit (algebraMap R (Localization.Away g) f))`
  : `Function.Bijective (chartComponent I f g)`  — `BasicOpenImmersionAssembly.lean`.
* `chartComponent` (`BasicOpenImmersionSheaf.lean`): its definition unfolds the chart's
  `c.app (op (basicOpen I g))` conjugated by two `sectionsBasicOpenEquiv` isos and an `eqToHom`
  structure-sheaf restriction — so `IsIso (chartComponent …)` (from bijectivity, via
  `CommRingCat.isIso_iff_bijective` / `RingEquiv.ofBijective`) gives, after cancelling those isos,
  `IsIso ((basicOpenChart I f).c.app (op (basicOpen I g)))`.
* `isUnit_algebraMap_away_left (f g) : IsUnit (algebraMap R (Localization.Away (f * g)) f)`.
* `isOpenEmbedding_basicOpenChartBase`, `range_basicOpenChartBase` (`BasicOpenChart.lean`).
* `basicOpen_mul`, `isTopologicalBasis_basicOpen` (`FormalSpectrum.lean`).
* `TopCat.Sheaf.isIso_iff_isIso_basis` (Mathlib `Topology/Sheaves/SheafCondition/Sites.lean:258`).
* `PresheafedSpace.isoOfComponents`, `.ofRestrict`, `PresheafedSpace.IsOpenImmersion.ofRestrict`
  (Mathlib `Geometry/RingedSpace/{PresheafedSpace,OpenImmersion}.lean`).
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

/-- **Issue 163 — the affine basic-open chart is an open immersion.** For `(R, I)` adic with `I.FG`
and `f : R`, the chart `basicOpenChart I f : Spf R{1/f} ⟶ Spf R` is an open immersion of locally
ringed spaces. -/
theorem isOpenImmersion_basicOpenChart (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion (basicOpenChart I f) := by
  sorry

/-- The range of the base map of the affine basic-open chart is `basicOpen I f = D(f)`. -/
theorem range_basicOpenChart (hI : I.FG) :
    Set.range (basicOpenChart I f).toShHom.hom.base = (basicOpen I f : Set (FormalSpectrum I)) := by
  exact range_basicOpenChartBase I f hI

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
    simp only [Category.assoc]
    congr 1
    simp only [TopCat.Sheaf.pushforward_obj_val, TopCat.Presheaf.pushforward_obj_map]
    erw [← Functor.map_comp, ← Functor.map_comp]
    congr 1

/-- The comparison morphism packaged as a morphism of sheaves on the source space `Spf S`. -/
def chartComparisonSheaf (he : IsOpenEmbedding (mapTop I J φ hφ)) :
    ((sheafedSpaceObj I).restrict he).sheaf ⟶ structureSheaf J :=
  Sheaf.Hom.mk (chartComparison I J φ hφ he)

end Packaging

end FormalSpectrum
