import FormalSchemes.BasicOpenImmersionSheaf

set_option linter.style.header false

/-!
# The affine basic-open chart is an open immersion (issue 163)

For an adic ring `(R, I)` with `I.FG` and `f : R`, this file completes the `c_iso` matching for the
affine basic-open chart `FormalSpectrum.basicOpenChart I f : Spf R{1/f} ⟶ Spf R`.

The merged development supplies both level-`n` readings of the chart's `c`-component on a basic open
`D(g) ⊆ D(f)`:

* the sheaf side `FormalSpectrum.evalₐ_chartComponent` (`BasicOpenImmersionSheaf.lean`), and
* the ring side `FormalSpectrum.evalₐ_awayCompletionChartEquiv` (`BasicOpenImmersion.lean`).

Matching the two, level by level, via `AdicCompletion.ext_evalₐ` identifies the sheaf-level
component `chartComponent` with the algebraic isomorphism `awayCompletionChartEquiv`
(`FormalSpectrum.chartComponent_eq_awayCompletionChartEquiv`), whence the chart's `c`-component on
each basic open `D(f * g) ⊆ D(f)` is a ring isomorphism.

## Main results

* `FormalSpectrum.chartComponent_eq_awayCompletionChartEquiv`: the sheaf `c`-component on
  `D(g) ⊆ D(f)`, conjugated by `sectionsBasicOpenEquiv`, equals the algebraic chart iso
  `awayCompletionChartEquiv`.
* `FormalSpectrum.bijective_chartComponent`: consequently that `c`-component is bijective (a ring
  isomorphism), the `c_iso`-on-basic-opens fact underlying the open-immersion property.
* `FormalSpectrum.chartComponentEquiv`: the `c`-component packaged as a `RingEquiv`.

## Remaining follow-up (issue 163)

The full `LocallyRingedSpace.IsOpenImmersion (basicOpenChart I f)` remains: transport
`bijective_chartComponent` (through the `sectionsBasicOpenEquiv` conjugation and the `eqToHom`
restriction, all isomorphisms) to `IsIso ((basicOpenChart I f).c.app (op (basicOpen I (f * g))))`
for the covering basis `{D(f * g)}` of `D(f)` (`isUnit_algebraMap_away_left` supplies the `hfg`
hypothesis), then `TopCat.Sheaf.isIso_iff_isIso_basis` on that basis gives
`PresheafedSpace.IsOpenImmersion` (via its `c_iso` field, with the base open embedding
`isOpenEmbedding_basicOpenChartBase`), and finally `SheafedSpace`/`LocallyRingedSpace` packaging
with range `basicOpen I f` (`range_basicOpenChartBase`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f g : R)

set_option linter.style.setOption false in
set_option maxHeartbeats 4000000 in
-- The section rings of the thickening/structure sheaves unfold slowly through the defining
-- `ℕᵒᵖ`-limit, so this level-matching proof needs a generous heartbeat budget.
/-- **The sheaf `c`-component of the chart on `D(g) ⊆ D(f)` is the algebraic chart iso.** For
`D(g) ⊆ D(f)` (encoded by `hfg : IsUnit (algebraMap R R_g f)`), the conjugated sheaf component
`chartComponent I f g` agrees with the completed-localization isomorphism
`awayCompletionChartEquiv I f g` (`R{1/g} ≃+* R{1/f}{1/ḡ}`). Proved by matching at every level `n`
through the defining `ℕᵒᵖ`-limit, via `AdicCompletion.ext_evalₐ`. A generous heartbeat budget is
required: these limit-sheaf files unfold the section rings of the thickening/structure sheaves. -/
theorem chartComponent_eq_awayCompletionChartEquiv (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    chartComponent I f g = (awayCompletionChartEquiv I f g hI hfg).toRingHom := by
  set J := awayCompletionIdeal I f with hJ
  set φ := awayCompletionHom I f with hφdef
  set hφ := le_comap_awayCompletionHom I f with hφle
  refine RingHom.ext fun x => ?_
  refine AdicCompletion.ext_evalₐ fun n => ?_
  cases n with
  | zero =>
    haveI : Subsingleton (Localization.Away (awayCompletionHom I f g) ⧸
        (Ideal.map (algebraMap (awayCompletion I f) (Localization.Away (awayCompletionHom I f g)))
          (awayCompletionIdeal I f)) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
    exact Subsingleton.elim _ _
  | succ k =>
    rw [show (awayCompletionChartEquiv I f g hI hfg).toRingHom x =
        awayCompletionChartEquiv I f g hI hfg x from rfl,
      evalₐ_chartComponent I f g k x,
      show AdicCompletion.evalₐ (Ideal.map (algebraMap (awayCompletion I f)
            (Localization.Away (awayCompletionHom I f g))) (awayCompletionIdeal I f)) (k + 1)
          (awayCompletionChartEquiv I f g hI hfg x) = _
        from evalₐ_awayCompletionChartEquiv I f g hI hfg (k + 1) x]
    -- reduce both sides to a ring-hom identity out of `Γ(D(g), thickeningSheaf I k)`
    set y := AdicCompletion.evalₐ (I.map (algebraMap R (Localization.Away g))) (k + 1) x with hy
    -- the load-bearing ring-hom equality, checked on `algebraMap (mk r)`
    have key :
        ((basicOpenLevelEquiv J (awayCompletionHom I f g) k).toRingHom.comp
          (((thickeningSheaf J k).presheaf.map
            (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g)))).hom.comp
            ((levelSheafHom I J φ hφ k).hom.app (op (basicOpen I g))).hom)) =
        ((Ideal.quotientMap _
            (AdicCompletion.locTransition (I.map (algebraMap R (Localization.Away f)))
              (algebraMap R (Localization.Away f) g))
            (AdicCompletion.locTransition_pow_le _ _ (k + 1))).comp
          ((Ideal.quotientMap _ (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom
              (awayAwayLocEquiv_pow_le I f g hfg (k + 1))).comp
            (basicOpenLevelEquiv I g k).toRingHom)) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (I ^ (k + 1)) g))
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun r => ?_
      -- assert the fully-applied (defeq) form of the composed ring homs on `algebraMap (mk r)`
      change basicOpenLevelEquiv J (awayCompletionHom I f g) k
          (((thickeningSheaf J k).presheaf.map
            (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g)))).hom
            (((levelSheafHom I J φ hφ k).hom.app (op (basicOpen I g))).hom
              (algebraMap (R ⧸ I ^ (k + 1))
                ((thickeningSheaf I k).presheaf.obj (op (basicOpen I g)))
                (Ideal.Quotient.mk (I ^ (k + 1)) r)))) =
        Ideal.quotientMap _
            (AdicCompletion.locTransition (I.map (algebraMap R (Localization.Away f)))
              (algebraMap R (Localization.Away f) g))
            (AdicCompletion.locTransition_pow_le _ _ (k + 1))
          (Ideal.quotientMap _ (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom
              (awayAwayLocEquiv_pow_le I f g hfg (k + 1))
            (basicOpenLevelEquiv I g k
              (algebraMap (R ⧸ I ^ (k + 1))
                ((thickeningSheaf I k).presheaf.obj (op (basicOpen I g)))
                (Ideal.Quotient.mk (I ^ (k + 1)) r))))
      -- LHS: read the `levelSheafHom` component; the `comap` + `eqToHom` restriction on
      -- `algebraMap (mk r)` is `algebraMap (mk (φ r))` over `D(φ g)` (combined, defeq via
      -- `comap_algebraMap` + `algebraMap_self_map`)
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
          algebraMap (awayCompletion I f ⧸ awayCompletionIdeal I f ^ (k + 1))
            ((thickeningSheaf J k).presheaf.obj (op (basicOpen J (awayCompletionHom I f g))))
            (Ideal.Quotient.mk (awayCompletionIdeal I f ^ (k + 1)) (φ r)) := by
        have hc := comap_algebraMap (levelRingHom I J φ hφ k)
          (thickeningOpen I k (basicOpen I g))
          (thickeningOpen J k ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I g)))
          (thickeningOpen_map_le I J φ hφ k (basicOpen I g))
          (Ideal.Quotient.mk (I ^ (k + 1)) r)
        rw [levelRingHom_mk] at hc
        exact congrArg (((thickeningSheaf J k).presheaf.map
          (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g)))).hom) hc
      refine (congrArg (basicOpenLevelEquiv J (awayCompletionHom I f g) k) hval).trans ?_
      rw [basicOpenLevelEquiv_algebraMap_mk J (awayCompletionHom I f g) k (φ r)]
      -- RHS chase
      rw [basicOpenLevelEquiv_algebraMap_mk I g k r, Ideal.quotientMap_mk,
        show (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom
            (algebraMap R (Localization.Away g) r) =
          algebraMap R (Localization.Away (algebraMap R (Localization.Away f) g)) r
          from (awayAwayLocEquiv f g hfg).commutes r,
        Ideal.quotientMap_mk,
        show algebraMap R (Localization.Away (algebraMap R (Localization.Away f) g)) r =
          algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R (Localization.Away f) g))
            (algebraMap R (Localization.Away f) r)
          from IsScalarTower.algebraMap_apply R (Localization.Away f) _ r,
        AdicCompletion.locTransition_algebraMap]
      -- both sides are `mk` of the triple `algebraMap` chain `R → R_f → R{1/f} → R{1/f}{1/ḡ}`
      rfl
    -- apply the ring-hom identity `key` at `w := (basicOpenLevelEquiv I g k).symm y`
    have hw := RingHom.congr_fun key ((basicOpenLevelEquiv I g k).symm y)
    refine hw.trans ?_
    change Ideal.quotientMap _
        (AdicCompletion.locTransition (I.map (algebraMap R (Localization.Away f)))
          (algebraMap R (Localization.Away f) g))
        (AdicCompletion.locTransition_pow_le _ _ (k + 1))
        (Ideal.quotientMap _ (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom
          (awayAwayLocEquiv_pow_le I f g hfg (k + 1))
          (basicOpenLevelEquiv I g k ((basicOpenLevelEquiv I g k).symm y))) = _
    rw [RingEquiv.apply_symm_apply]

/-- **The chart's sheaf `c`-component on `D(g) ⊆ D(f)` is a ring isomorphism.** Immediate from
`chartComponent_eq_awayCompletionChartEquiv`, since `awayCompletionChartEquiv` is a `RingEquiv`.
This is the `c_iso`-on-basic-opens statement underlying the open-immersion property of the chart:
each basic open `D(f * g)` of `D(f)` (which form a basis of `D(f)`, `isUnit_algebraMap_away_left`)
carries the isomorphism. -/
theorem bijective_chartComponent (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    Function.Bijective (chartComponent I f g) := by
  rw [chartComponent_eq_awayCompletionChartEquiv I f g hI hfg]
  exact (awayCompletionChartEquiv I f g hI hfg).bijective

/-- The chart's sheaf `c`-component on `D(g) ⊆ D(f)`, conjugated by `sectionsBasicOpenEquiv` on both
sides, packaged as a `RingEquiv` `R{1/g} ≃+* R{1/f}{1/ḡ}`; definitionally
`awayCompletionChartEquiv`, but recorded here as the sheaf-level object. -/
noncomputable def chartComponentEquiv (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    awayCompletion I g ≃+*
      awayCompletion (awayCompletionIdeal I f) (awayCompletionHom I f g) :=
  RingEquiv.ofBijective (chartComponent I f g) (bijective_chartComponent I f g hI hfg)

end FormalSpectrum
