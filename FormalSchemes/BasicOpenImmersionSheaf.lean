import FormalSchemes.BasicOpenImmersion

set_option linter.style.header false

/-!
# Sheaf-side level reading of the affine basic-open chart (issue 163)

For an adic ring `(R, I)` with `I.FG` and `f : R`, the affine basic-open chart
`FormalSpectrum.basicOpenChart I f : Spf R{1/f} ⟶ Spf R` (`BasicOpenImmersion.lean`) is expected
to be a `LocallyRingedSpace.IsOpenImmersion`. The underlying base map is already an open embedding
onto `D(f)` (`isOpenEmbedding_basicOpenChartBase`, `range_basicOpenChartBase`); the remaining
ingredient is the `c_iso` field, i.e. that the sheaf component is an isomorphism on the basis of
basic opens `D(g) ⊆ D(f)`.

This file supplies the **sheaf-side level-`n` reading** of the chart's `c`-component on a basic
open `D(g) ⊆ D(f)`, conjugated by `FormalSpectrum.sectionsBasicOpenEquiv` on both sides (the target
open `(mapTop)⁻¹ D(g) = D(ḡ)` identified via `map_preimage_basicOpen`). The conjugated component
`chartComponent` is a ring hom `R{1/g} →+* R{1/f}{1/ḡ}`; its level-`k + 1` evaluation
(`evalₐ_chartComponent`) is the `basicOpenLevelEquiv`-conjugation of the structure-sheaf `comap`
of the induced level map `levelRingHom`, read through the defining `ℕᵒᵖ`-limit
`O_{Spf R} = limit (structureSheafFunctor I)`. This mirrors, on basic opens, the `⊤`-case value
chase of `globalSectionsMap_locallyRingedSpaceMap` (`SpfGamma.lean`).

## Main results

* `FormalSpectrum.chartComponent`: the chart's sheaf `c`-component on `D(g) ⊆ D(f)` read through
  `sectionsBasicOpenEquiv` on both sides, as a ring hom `R{1/g} →+* R{1/f}{1/ḡ}`.
* `FormalSpectrum.evalₐ_chartComponent`: its level-`k + 1` evaluation, as the
  `basicOpenLevelEquiv`-conjugation of `comap (levelRingHom …)`.

## Remaining follow-up (issue 163 `c_iso` assembly)

Matching `evalₐ_chartComponent` (the sheaf side, here) against the merged
`FormalSpectrum.evalₐ_awayCompletionChartEquiv` (the ring side, `BasicOpenImmersion.lean`) — i.e.
identifying the two level-`k + 1` ring maps `R_g ⧸ (I·R_g)^{k+1} → R_f{ḡ} ⧸ (…)^{k+1}` via
`IsLocalization.ringHom_ext` on `Submonoid.powers (Ideal.Quotient.mk (I^{k+1}) g)` (the source is
a localization-away of `R ⧸ I^{k+1}`, `isLocalization_away_basicOpen_sections`), agreeing on the
`algebraMap` image by `comap_algebraMap` / `levelRingHom_mk` / `basicOpenLevelEquiv_algebraMap_mk`
— gives `chartComponent = awayCompletionChartEquiv` by `AdicCompletion.ext_evalₐ`. That upgrades
the chart's `c`-component to an isomorphism on each basic open `D(f * g)`, whence
`TopCat.Sheaf.isIso_iff_isIso_basis` on the basis of basic opens below `D(f)` yields
`PresheafedSpace.IsOpenImmersion` and then `LocallyRingedSpace.IsOpenImmersion`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f g : R)

/-- The chart's sheaf `c`-component on the basic open `D(g) ⊆ D(f)`, conjugated by
`sectionsBasicOpenEquiv` on both sides (the target open `(mapTop)⁻¹ D(g) = D(ḡ)` identified by
`map_preimage_basicOpen` and transported by the structure-sheaf restriction along that equality of
opens), as a ring hom `awayCompletion I g →+* awayCompletion (awayCompletionIdeal I f) (φ g)`.
This is the sheaf-level incarnation of the algebraic chart iso `awayCompletionChartEquiv`. -/
def chartComponent :
    awayCompletion I g →+*
      awayCompletion (awayCompletionIdeal I f) (awayCompletionHom I f g) :=
  (sectionsBasicOpenEquiv (awayCompletionIdeal I f) (awayCompletionHom I f g)).toRingHom.comp
    ((((structureSheaf (awayCompletionIdeal I f)).presheaf.map
        (eqToHom (congrArg op (map_preimage_basicOpen I (awayCompletionIdeal I f)
          (awayCompletionHom I f) (le_comap_awayCompletionHom I f) g)))).hom).comp
      (((basicOpenChart I f).c.app (op (basicOpen I g))).hom.comp
        (sectionsBasicOpenEquiv I g).symm.toRingHom))

/-- Naturality of the level-`k` limit projection past a structure-sheaf restriction along an
equality of opens `V = W`. -/
theorem limitπ_map_eqToHom {S : Type u} [CommRing S] (J : Ideal S) (k : ℕ)
    (V W : Opens (FormalSpectrum J)) (h : V = W)
    (σ : (structureSheaf J).presheaf.obj (op V)) :
    ((limit.π (structureSheafFunctor J) ⟨k⟩).hom.app (op W)).hom
        (((structureSheaf J).presheaf.map (eqToHom (congrArg op h))).hom σ) =
      ((thickeningSheaf J k).presheaf.map (eqToHom (congrArg op h))).hom
        (((limit.π (structureSheafFunctor J) ⟨k⟩).hom.app (op V)).hom σ) :=
  DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    ((limit.π (structureSheafFunctor J) ⟨k⟩).hom.naturality (eqToHom (congrArg op h)))) σ

/-- **Level-`k` reading of the chart's conjugated sheaf component.** Evaluating
`chartComponent I f g x` at level `k + 1` is the `basicOpenLevelEquiv`-conjugation of the
structure-sheaf `comap` of the level map `levelRingHom` (transported along the open equality
`(mapTop)⁻¹ D(g) = D(ḡ)`), applied to the level-`k + 1` component of `x`. -/
theorem evalₐ_chartComponent (k : ℕ) (x : awayCompletion I g) :
    AdicCompletion.evalₐ ((awayCompletionIdeal I f).map (algebraMap (awayCompletion I f)
        (Localization.Away (awayCompletionHom I f g)))) (k + 1) (chartComponent I f g x) =
      basicOpenLevelEquiv (awayCompletionIdeal I f) (awayCompletionHom I f g) k
        (((thickeningSheaf (awayCompletionIdeal I f) k).presheaf.map
          (eqToHom (congrArg op (map_preimage_basicOpen I (awayCompletionIdeal I f)
            (awayCompletionHom I f) (le_comap_awayCompletionHom I f) g)))).hom
          (((levelSheafHom I (awayCompletionIdeal I f) (awayCompletionHom I f)
              (le_comap_awayCompletionHom I f) k).hom.app (op (basicOpen I g))).hom
            ((basicOpenLevelEquiv I g k).symm
              (AdicCompletion.evalₐ (I.map (algebraMap R (Localization.Away g)))
                (k + 1) x)))) := by
  set J := awayCompletionIdeal I f
  set φ := awayCompletionHom I f
  set hφ := le_comap_awayCompletionHom I f
  -- unfold chartComponent, rewrite the chart's `c`-component to `mapSheafHom`, and fully apply
  rw [chartComponent, show (basicOpenChart I f).c.app (op (basicOpen I g)) =
      (mapSheafHom I J φ hφ).hom.app (op (basicOpen I g)) from rfl]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  -- apply the target sections rule, then push the projection past the eqToHom restriction
  rw [eval_sectionsBasicOpenEquiv J (φ g) k,
    limitπ_map_eqToHom J k _ _ (map_preimage_basicOpen I J φ hφ g)]
  congr 2
  -- read the chart's sheaf component level by level via mapSheafHom_hom_app_pi
  erw [mapSheafHom_hom_app_pi I J φ hφ k (basicOpen I g)
    ((sectionsBasicOpenEquiv I g).symm x)]
  -- identify the source level-`k + 1` component with `(basicOpenLevelEquiv I g k).symm (evalₐ x)`
  congr 1
  rw [RingEquiv.eq_symm_apply, ← eval_sectionsBasicOpenEquiv I g k, RingEquiv.apply_symm_apply]

end FormalSpectrum
