import FormalSchemes.BasicOpenImmersionSheaf
import FormalSchemes.Completion

set_option linter.style.header false

/-!
# The reconstructed morphism's sheaf component on basic opens is a completed localization

For adic rings `(R, I)` and `(S, J)` and a continuous ring homomorphism `φ : R →+* S`
(`hφ : I ≤ J.comap φ`), the model morphism of formal spectra
`FormalSpectrum.locallyRingedSpaceMap I J φ hφ : Spf S ⟶ Spf R` has, on a basic open
`D(g) ⊆ Spf R`, a sheaf `c`-component

```
Γ(D(g), O_{Spf R}) ⟶ Γ((mapTop)⁻¹ D(g), O_{Spf S}) = Γ(D(φ g), O_{Spf S}).
```

This file identifies that component, conjugated by `FormalSpectrum.sectionsBasicOpenEquiv` on both
sides (the target open `(mapTop)⁻¹ D(g) = D(φ g)` via `map_preimage_basicOpen`), with a single
completed-localization ring map `R{1/g} →+* S{1/φ g}` — namely `AdicCompletion.mapCompletion` of
the *localized* homomorphism `Localization.awayMap φ g : R_g →+* S_{φ g}` (issue 60's completion
functor). This is the affine-basic-open incarnation, for an **arbitrary** continuous ring hom `φ`,
of the sheaf-component computation that `globalSectionsMap_locallyRingedSpaceMap` performs on `⊤`;
it generalises the affine basic-open *chart* case (issue 163,
`FormalSpectrum.chartComponent_eq_awayCompletionChartEquiv`, the special case where `φ` is a
localization map `R → R{1/f}`) to a general `φ`.

It is the model-morphism half of step (b) of the converse of EGA I 10.4.6 (issue 157): it says
the *reconstructed* morphism `Spf φ`, read on basic opens through the sections identifications, is
`Spf` of the localized ring map, exactly the completed-localization map the ind-scheme description
predicts. The remaining, harder half of step (b) — matching `f.c` on `D(g)` for an **arbitrary**
morphism `f` (via locality `f.prop` + the step-(a) base identification `base_toPrimeSpectrum_eq`) —
is left as follow-up.

## Main results

* `FormalSpectrum.modelSheafComponent`: the model morphism `Spf φ`'s sheaf `c`-component on
  `D(g)`, conjugated by `sectionsBasicOpenEquiv` on both sides, as a ring hom
  `R{1/g} →+* S{1/φ g}`.
* `FormalSpectrum.evalₐ_modelSheafComponent`: its level-`k + 1` reading, as the
  `basicOpenLevelEquiv`-conjugation of `comap (levelRingHom …)` (the general-`φ` analogue of
  `evalₐ_chartComponent`).
* `FormalSpectrum.modelSheafComponent_eq_mapCompletion`: the component equals
  `AdicCompletion.mapCompletion (Localization.awayMap φ g) …`, the completed localization of `φ`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]
variable (φ : R →+* S) (hφ : I ≤ J.comap φ) (g : R)

/-- The model morphism `Spf φ`'s sheaf `c`-component on the basic open `D(g)`, conjugated by
`sectionsBasicOpenEquiv` on both sides (the target open `(mapTop)⁻¹ D(g) = D(φ g)` identified by
`map_preimage_basicOpen` and transported by the structure-sheaf restriction along that equality of
opens), as a ring hom `R{1/g} →+* S{1/φ g}`. This is the general-`φ` analogue of the affine
basic-open chart's `chartComponent`. -/
def modelSheafComponent :
    awayCompletion I g →+* awayCompletion J (φ g) :=
  (sectionsBasicOpenEquiv J (φ g)).toRingHom.comp
    ((((structureSheaf J).presheaf.map
        (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g)))).hom).comp
      (((mapSheafHom I J φ hφ).hom.app (op (basicOpen I g))).hom.comp
        (sectionsBasicOpenEquiv I g).symm.toRingHom))

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] in
/-- **Level-`k` reading of the model morphism's conjugated sheaf component.** Evaluating
`modelSheafComponent I J φ hφ g x` at level `k + 1` is the `basicOpenLevelEquiv`-conjugation of the
structure-sheaf `comap` of the level map `levelRingHom` (transported along the open equality
`(mapTop)⁻¹ D(g) = D(φ g)`), applied to the level-`k + 1` component of `x`. This is the general-`φ`
analogue of `evalₐ_chartComponent`. -/
theorem evalₐ_modelSheafComponent (k : ℕ) (x : awayCompletion I g) :
    AdicCompletion.evalₐ (J.map (algebraMap S (Localization.Away (φ g)))) (k + 1)
        (modelSheafComponent I J φ hφ g x) =
      basicOpenLevelEquiv J (φ g) k
        (((thickeningSheaf J k).presheaf.map
          (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g)))).hom
          (((levelSheafHom I J φ hφ k).hom.app (op (basicOpen I g))).hom
            ((basicOpenLevelEquiv I g k).symm
              (AdicCompletion.evalₐ (I.map (algebraMap R (Localization.Away g)))
                (k + 1) x)))) := by
  rw [modelSheafComponent]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  -- apply the target sections rule, then push the projection past the eqToHom restriction
  rw [eval_sectionsBasicOpenEquiv J (φ g) k,
    limitπ_map_eqToHom J k _ _ (map_preimage_basicOpen I J φ hφ g)]
  congr 2
  -- read the sheaf component level by level via mapSheafHom_hom_app_pi
  erw [mapSheafHom_hom_app_pi I J φ hφ k (basicOpen I g)
    ((sectionsBasicOpenEquiv I g).symm x)]
  -- identify the source level-`k + 1` component with `(basicOpenLevelEquiv I g k).symm (evalₐ x)`
  congr 1
  rw [RingEquiv.eq_symm_apply, ← eval_sectionsBasicOpenEquiv I g k, RingEquiv.apply_symm_apply]

omit [TopologicalSpace R] [TopologicalSpace S] in
/-- The localized homomorphism `Localization.awayMap φ g : R_g →+* S_{φ g}` intertwines the
structure maps: `awayMap φ g ∘ algebraMap R R_g = algebraMap S S_{φ g} ∘ φ`. -/
theorem awayMap_comp_algebraMap :
    (Localization.awayMap φ g).comp (algebraMap R (Localization.Away g)) =
      (algebraMap S (Localization.Away (φ g))).comp φ := by
  ext r
  simp only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
    IsLocalization.map_eq]

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J] in
include hφ in
/-- The localized homomorphism carries the ideal of definition `I·R_g` of `awayCompletion I g`
into the ideal of definition `J·S_{φ g}` of `awayCompletion J (φ g)` — continuity of the
localized `φ`. -/
theorem awayCompletionIdeal_map_awayMap_le :
    (I.map (algebraMap R (Localization.Away g))).map (Localization.awayMap φ g) ≤
      J.map (algebraMap S (Localization.Away (φ g))) := by
  rw [Ideal.map_map, awayMap_comp_algebraMap φ g, ← Ideal.map_map]
  exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr hφ)

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J] in
include hφ in
/-- The level-`n` continuity bound needed by `AdicCompletion.evalₐ_mapCompletion` for the
localized `φ`. -/
theorem awayCompletionIdeal_pow_le_comap (n : ℕ) :
    (I.map (algebraMap R (Localization.Away g))) ^ n ≤
      ((J.map (algebraMap S (Localization.Away (φ g)))) ^ n).comap (Localization.awayMap φ g) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (awayCompletionIdeal_map_awayMap_le I J φ hφ g) n

set_option linter.style.setOption false in
set_option maxHeartbeats 4000000 in
-- The section rings of the thickening/structure sheaves unfold slowly through the defining
-- `ℕᵒᵖ`-limit, so this level-matching proof needs a generous heartbeat budget.
omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J] in
/-- **The model morphism's sheaf `c`-component on `D(g)` is the completed localization of `φ`.**
Conjugated by `sectionsBasicOpenEquiv` on both sides, the component `modelSheafComponent I J φ hφ g`
agrees with `AdicCompletion.mapCompletion (Localization.awayMap φ g) …`, the completion of the
localized ring map `R_g →+* S_{φ g}`. Proved by matching at every level `n` through the defining
`ℕᵒᵖ`-limit, via `AdicCompletion.ext_evalₐ`. -/
theorem modelSheafComponent_eq_mapCompletion (hI : I.FG) (hJ : J.FG) :
    modelSheafComponent I J φ hφ g =
      AdicCompletion.mapCompletion (Localization.awayMap φ g)
        (awayCompletionIdeal_map_awayMap_le I J φ hφ g) (hJ.map _) := by
  refine RingHom.ext fun x => ?_
  refine AdicCompletion.ext_evalₐ fun n => ?_
  cases n with
  | zero =>
    haveI : Subsingleton (Localization.Away (φ g) ⧸
        (J.map (algebraMap S (Localization.Away (φ g)))) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
    exact Subsingleton.elim _ _
  | succ k =>
    rw [evalₐ_modelSheafComponent I J φ hφ g k x,
      AdicCompletion.evalₐ_mapCompletion (Localization.awayMap φ g)
        (awayCompletionIdeal_map_awayMap_le I J φ hφ g) (hJ.map _) (hI.map _) (k + 1)
        (awayCompletionIdeal_pow_le_comap I J φ hφ g (k + 1)) x]
    -- reduce both sides to a ring-hom identity out of `Γ(D(g), thickeningSheaf I k)`
    set y := AdicCompletion.evalₐ (I.map (algebraMap R (Localization.Away g))) (k + 1) x with hy
    -- the load-bearing ring-hom equality, checked on `algebraMap (mk r)`
    have key :
        ((basicOpenLevelEquiv J (φ g) k).toRingHom.comp
          (((thickeningSheaf J k).presheaf.map
            (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g)))).hom.comp
            ((levelSheafHom I J φ hφ k).hom.app (op (basicOpen I g))).hom)) =
        ((Ideal.quotientMap ((J.map (algebraMap S (Localization.Away (φ g)))) ^ (k + 1))
            (Localization.awayMap φ g)
            (awayCompletionIdeal_pow_le_comap I J φ hφ g (k + 1))).comp
          (basicOpenLevelEquiv I g k).toRingHom) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (I ^ (k + 1)) g))
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun r => ?_
      change basicOpenLevelEquiv J (φ g) k
          (((thickeningSheaf J k).presheaf.map
            (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g)))).hom
            (((levelSheafHom I J φ hφ k).hom.app (op (basicOpen I g))).hom
              (algebraMap (R ⧸ I ^ (k + 1))
                ((thickeningSheaf I k).presheaf.obj (op (basicOpen I g)))
                (Ideal.Quotient.mk (I ^ (k + 1)) r)))) =
        Ideal.quotientMap ((J.map (algebraMap S (Localization.Away (φ g)))) ^ (k + 1))
            (Localization.awayMap φ g)
            (awayCompletionIdeal_pow_le_comap I J φ hφ g (k + 1))
          (basicOpenLevelEquiv I g k
            (algebraMap (R ⧸ I ^ (k + 1))
              ((thickeningSheaf I k).presheaf.obj (op (basicOpen I g)))
              (Ideal.Quotient.mk (I ^ (k + 1)) r)))
      -- LHS: read the `levelSheafHom` component; `comap` + `eqToHom` restriction on
      -- `algebraMap (mk r)` is `algebraMap (mk (φ r))` over `D(φ g)`
      rw [levelSheafHom_hom_app I J φ hφ k (basicOpen I g)]
      have hval : ((thickeningSheaf J k).presheaf.map
            (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g)))).hom
            ((CommRingCat.ofHom (StructureSheaf.comap (levelRingHom I J φ hφ k)
              (thickeningOpen I k (basicOpen I g))
              (thickeningOpen J k ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I g)))
              (thickeningOpen_map_le I J φ hφ k (basicOpen I g)))).hom
              (algebraMap (R ⧸ I ^ (k + 1))
                ((thickeningSheaf I k).presheaf.obj (op (basicOpen I g)))
                (Ideal.Quotient.mk (I ^ (k + 1)) r))) =
          algebraMap (S ⧸ J ^ (k + 1))
            ((thickeningSheaf J k).presheaf.obj (op (basicOpen J (φ g))))
            (Ideal.Quotient.mk (J ^ (k + 1)) (φ r)) := by
        have hc := comap_algebraMap (levelRingHom I J φ hφ k)
          (thickeningOpen I k (basicOpen I g))
          (thickeningOpen J k ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I g)))
          (thickeningOpen_map_le I J φ hφ k (basicOpen I g))
          (Ideal.Quotient.mk (I ^ (k + 1)) r)
        rw [levelRingHom_mk] at hc
        exact congrArg (((thickeningSheaf J k).presheaf.map
          (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g)))).hom) hc
      refine (congrArg (basicOpenLevelEquiv J (φ g) k) hval).trans ?_
      rw [basicOpenLevelEquiv_algebraMap_mk J (φ g) k (φ r)]
      -- RHS chase
      rw [basicOpenLevelEquiv_algebraMap_mk I g k r, Ideal.quotientMap_mk,
        show (Localization.awayMap φ g) (algebraMap R (Localization.Away g) r) =
            algebraMap S (Localization.Away (φ g)) (φ r)
          from RingHom.congr_fun (awayMap_comp_algebraMap φ g) r]
    -- apply the ring-hom identity `key` at `w := (basicOpenLevelEquiv I g k).symm y`
    have hw := RingHom.congr_fun key ((basicOpenLevelEquiv I g k).symm y)
    refine hw.trans ?_
    change Ideal.quotientMap ((J.map (algebraMap S (Localization.Away (φ g)))) ^ (k + 1))
        (Localization.awayMap φ g)
        (awayCompletionIdeal_pow_le_comap I J φ hφ g (k + 1))
        (basicOpenLevelEquiv I g k ((basicOpenLevelEquiv I g k).symm y)) = _
    rw [RingEquiv.apply_symm_apply]

end FormalSpectrum
