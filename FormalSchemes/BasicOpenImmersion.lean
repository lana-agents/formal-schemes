import FormalSchemes.BasicOpenChartComponent

set_option linter.style.header false

/-!
# Towards the open immersion property of the affine basic-open chart

For an adic ring `(R, I)` with `I.FG` and `f : R`, the affine basic-open chart
`Spf R{1/f} ⟶ Spf R` (`FormalSchemes/BasicOpenChart.lean`) **is** a
`LocallyRingedSpace.IsOpenImmersion`: `FormalSpectrum.isOpenImmersion_basicOpenChart`
(`FormalSchemes.BasicOpenImmersionLRS`). The underlying map is an open topological embedding with
range `D(f)` (`FormalSpectrum.isOpenEmbedding_basicOpenChartBase`,
`FormalSpectrum.range_basicOpenChartBase`); the other ingredient is the `c_iso` field, i.e.
the sheaf component of the chart is an isomorphism on the basis of basic opens `D(g) ⊆ D(f)`.

This file packages the chart as a named morphism and develops the **level-`n` (`evalₐ`) behaviour
of its ring-level `c`-component** — the completed-localization isomorphism
`FormalSpectrum.awayCompletionChartEquiv` (`R{1/g} ≃+* R{1/f}{1/ḡ}`,
`FormalSchemes/AwayCompletionInterchange.lean`) — read level by level. This is the reusable
algebraic core of the `c_iso`-on-basis route towards `LocallyRingedSpace.IsOpenImmersion`.

The key observation is that all the completed maps in play are built from
`AdicCompletion.mapCompletion`, whose level-`n` component is the induced map of quotients
(`evalₐ_mapCompletion`). Chaining this along the two factors of `awayCompletionChartEquiv`
(the localization transitivity `awayAwayLocEquiv` and the interchange `interchangeForward`)
computes `evalₐ n (awayCompletionChartEquiv …)` as a composite of two `Ideal.quotientMap`s.

## Main results

* `AdicCompletion.evalₐ_mapCompletion`: the general functoriality rule
  `evalₐ n (mapCompletion f x) = Ideal.quotientMap (J ^ n) f _ (evalₐ n x)`; the level-`n`
  component of a completed ring map is the induced map of quotients. Reusable throughout the
  `AdicCompletion` development.
* `FormalSpectrum.basicOpenChart`: the affine basic-open chart `Spf R{1/f} ⟶ Spf R`, packaged as a
  morphism of locally ringed spaces.
* `FormalSpectrum.isUnit_algebraMap_away_left`: the containment↔unit bridge — `f` is a unit in
  `Localization.Away (f * g)`, so each basic open `D(f * g) = D(f) ⊓ D(g) ≤ D(f)` (these form a
  basis of `D(f)`) carries the interchange hypothesis of `awayCompletionChartEquiv`.
* `AdicCompletion.evalₐ_interchangeForward`, `FormalSpectrum.evalₐ_awayCompletionAwayEquiv`,
  `FormalSpectrum.evalₐ_awayCompletionChartEquiv`: the level-`n` components of the interchange
  forward map, the localization-transitivity isomorphism, and their composite the chart's
  `c`-component, each as an `Ideal.quotientMap`.

## What this file feeds

The **sheaf-side matching** that `evalₐ_awayCompletionChartEquiv` was computed for has been
carried out; it is no longer future work. The chart's sheaf component on a basic open
`D(g) ⊆ D(f)`, read through `FormalSpectrum.sectionsBasicOpenEquiv` on both sides (target open via
`map_preimage_basicOpen`), is `FormalSpectrum.chartComponent`, and its level-`n` value is
`FormalSpectrum.evalₐ_chartComponent` — the `basicOpenLevelEquiv`-conjugation of
`levelSheafHom`/`comap (levelRingHom …)`, obtained from `mapSheafHom_hom_app_pi` and
`eval_sectionsBasicOpenEquiv` in `FormalSchemes.BasicOpenChartComponent` — both in
`FormalSchemes.BasicOpenImmersionSheaf`. Matching it level by level against the composite quotient
map computed here, via `AdicCompletion.ext_evalₐ`, is
`FormalSpectrum.chartComponent_eq_awayCompletionChartEquiv`, with
`FormalSpectrum.bijective_chartComponent` and `FormalSpectrum.chartComponentEquiv`, in
`FormalSchemes.BasicOpenImmersionAssembly`. Finally `TopCat.Sheaf.isIso_iff_isIso_basis` on the
basis of basic opens below `D(f)` (using `isUnit_algebraMap_away_left` for the covering opens
`D(f * g)`) is run in `FormalSchemes.BasicOpenImmersionLRS`, giving
`FormalSpectrum.isOpenImmersion_basicOpenChart`, with range
`FormalSpectrum.range_basicOpenChart_base`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AdicCompletion

variable {R S : Type u} [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}

/-- The level-`n` component `evalₐ` of the completed ring map `mapCompletion f` is the induced
map of quotients `Ideal.quotientMap`: completion is functorial and compatible with the
truncations `R ⧸ I ^ n`. Both `I` and `J` are finitely generated so that the completions are
complete and the level maps determine the completed map. -/
theorem evalₐ_mapCompletion (f : R →+* S) (hf : I.map f ≤ J) (hJ : J.FG) (hI : I.FG) (n : ℕ)
    (hc : I ^ n ≤ (J ^ n).comap f) (x : AdicCompletion I R) :
    evalₐ J n (mapCompletion f hf hJ x) =
      Ideal.quotientMap (J ^ n) f hc (evalₐ I n x) := by
  -- represent the level-`n` component of `x` by an element `b : R`
  obtain ⟨b, hb⟩ := Submodule.mkQ_surjective (I ^ n • ⊤ : Submodule R R) (eval I R n x)
  have heval0 : eval I R n (x - AdicCompletion.of I R b) = 0 := by
    rw [map_sub, eval_of, hb, sub_self]
  have hker : x - AdicCompletion.of I R b ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I R)) := by
    rw [pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker]
    exact heval0
  -- hence `evalₐ I n x = mk b`
  have hevalₐ : evalₐ I n x = Ideal.Quotient.mk (I ^ n) b := by
    have h0 : evalₐ I n (x - AdicCompletion.of I R b) = 0 := by
      rw [← factor_eval_eq_evalₐ I (x - AdicCompletion.of I R b)
        (by simp : (I ^ n • ⊤ : Ideal R) ≤ I ^ n), heval0]
      exact _root_.map_zero _
    rw [map_sub, evalₐ_of, sub_eq_zero] at h0
    exact h0
  -- the target level component of the tail vanishes
  have htail : evalₐ J n (mapCompletion f hf hJ (x - AdicCompletion.of I R b)) = 0 := by
    have hmem : mapCompletion f hf hJ (x - AdicCompletion.of I R b) ∈ (idealOfDefinition J) ^ n :=
      mapCompletion_mem_pow f hf hJ hI n hker
    rw [mem_idealOfDefinition_pow_iff, pow_smul_top_eq_ker_eval hJ, LinearMap.mem_ker] at hmem
    rw [← factor_eval_eq_evalₐ J _ (by simp : (J ^ n • ⊤ : Ideal S) ≤ J ^ n), hmem]
    exact _root_.map_zero _
  -- assemble
  have hsplit : evalₐ J n (mapCompletion f hf hJ x) =
      evalₐ J n (mapCompletion f hf hJ (AdicCompletion.of I R b)) := by
    have := htail
    rw [map_sub, map_sub, sub_eq_zero] at this
    exact this
  rw [hsplit, mapCompletion_of, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, evalₐ_of, hevalₐ, Ideal.quotientMap_mk]

section Interchange

variable {B : Type u} [CommRing B] (K : Ideal B) (t : B)

/-- Continuity of `locTransition` at level `n`: the localization transitivity carries the ideal
`(K·B_t) ^ n` into the comap of `(K̂·B̂_{t̂}) ^ n`, so it descends to the truncations. -/
theorem locTransition_pow_le (n : ℕ) :
    (locIdeal K t) ^ n ≤ ((completionLocIdeal K t) ^ n).comap (locTransition K t) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (map_locTransition K t).le n

/-- **T1 — the level-`n` component of the interchange forward map.** Since `interchangeForward`
is the completion of `locTransition`, its `n`-th evaluation is the induced map of quotients
`Ideal.quotientMap`. -/
theorem evalₐ_interchangeForward (hK : K.FG) (n : ℕ)
    (x : AdicCompletion (locIdeal K t) (Localization.Away t)) :
    evalₐ (completionLocIdeal K t) n (interchangeForward K t hK x) =
      Ideal.quotientMap ((completionLocIdeal K t) ^ n) (locTransition K t)
        (locTransition_pow_le K t n) (evalₐ (locIdeal K t) n x) :=
  evalₐ_mapCompletion (locTransition K t) (map_locTransition K t).le
    (completionLocIdeal_fg K t hK) (locIdeal_fg K t hK) n (locTransition_pow_le K t n) x

end Interchange

end AdicCompletion

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f g : R)

/-- The affine basic-open chart `Spf R{1/f} ⟶ Spf R`, as a morphism of locally ringed spaces:
the map of formal spectra induced by the structural ring map `R → R{1/f}`. Its underlying map is
`basicOpenChartBase I f`, an open topological embedding with range `D(f)`
(`isOpenEmbedding_basicOpenChartBase`, `range_basicOpenChartBase`). It **is** a
`LocallyRingedSpace.IsOpenImmersion`: `isOpenImmersion_basicOpenChart`
(`FormalSchemes.BasicOpenImmersionLRS`). -/
def basicOpenChart : locallyRingedSpaceObj (awayCompletionIdeal I f) ⟶ locallyRingedSpaceObj I :=
  locallyRingedSpaceMap I (awayCompletionIdeal I f) (awayCompletionHom I f)
    (le_comap_awayCompletionHom I f)

/-- For any `f g : R`, the element `f` becomes a unit in `Localization.Away (f * g)`: the product
`f * g` is a unit there, and a divisor of a unit is a unit. This is the containment↔unit bridge for
the basic opens `D(f * g) = D(f) ⊓ D(g) ≤ D(f)` (which form a basis of `D(f)`), each of which then
carries the `IsUnit (algebraMap R (Localization.Away (f * g)) f)` hypothesis of
`awayCompletionChartEquiv`. -/
theorem isUnit_algebraMap_away_left :
    IsUnit (algebraMap R (Localization.Away (f * g)) f) := by
  have h : IsUnit (algebraMap R (Localization.Away (f * g)) (f * g)) :=
    IsLocalization.Away.algebraMap_isUnit (f * g)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

/-- Continuity at level `n` of the localization-transitivity ring map `φ = awayAwayLocEquiv`: it
carries `(I·R_g) ^ n` into the comap of `KC ^ n` (`KC = (I·R_f)·(R_f)_ḡ`), the ideal of
definition of the target completion. -/
theorem awayAwayLocEquiv_pow_le
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) (n : ℕ) :
    (I.map (algebraMap R (Localization.Away g))) ^ n ≤
      (((I.map (algebraMap R (Localization.Away f))).map
        (algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R (Localization.Away f) g)))) ^ n).comap
        (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  refine Ideal.pow_right_mono ?_ n
  exact le_of_eq ((map_awayAwayLocEquiv I f g hfg).trans
    (map_algebraMap_localizationAway_eq I f g).symm)

/-- **T2 — the level-`n` component of `awayCompletionAwayEquiv`.** The forward direction of the
localization-transitivity completion isomorphism is `mapCompletion φ`, so its `n`-th evaluation is
the induced map of quotients `Ideal.quotientMap` of `φ = awayAwayLocEquiv`. -/
theorem evalₐ_awayCompletionAwayEquiv (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) (n : ℕ)
    (x : awayCompletion I g) :
    AdicCompletion.evalₐ
        ((I.map (algebraMap R (Localization.Away f))).map
          (algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R (Localization.Away f) g)))) n
        (awayCompletionAwayEquiv I f g hI hfg x) =
      Ideal.quotientMap _ (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom
        (awayAwayLocEquiv_pow_le I f g hfg n)
        (AdicCompletion.evalₐ (I.map (algebraMap R (Localization.Away g))) n x) :=
  AdicCompletion.evalₐ_mapCompletion (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom
    (le_of_eq ((map_awayAwayLocEquiv I f g hfg).trans
      (map_algebraMap_localizationAway_eq I f g).symm))
    ((hI.map _).map _) (hI.map _) n (awayAwayLocEquiv_pow_le I f g hfg n) x

/-- **T3 — the level-`n` component of the chart isomorphism `awayCompletionChartEquiv`.** The
ring-level `c`-component of the affine basic-open chart on `D(g) ⊆ D(f)` is the composite
`interchangeForward ∘ awayCompletionAwayEquiv`; its `n`-th evaluation is therefore the composite of
the two induced quotient maps — that of the localization transitivity `φ = awayAwayLocEquiv`
(`R_g ⧸ (I·R_g)ⁿ → (R_f)_ḡ ⧸ (KC)ⁿ`) followed by that of `locTransition`
(`(R_f)_ḡ ⧸ (KC)ⁿ → B̂_{t̂} ⧸ (K̂·B̂_{t̂})ⁿ`). This is the concrete level-`n` behaviour of the
chart's ring-level `c`-component, the key reusable algebraic output of issue 163. -/
theorem evalₐ_awayCompletionChartEquiv (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) (n : ℕ) (x : awayCompletion I g) :
    AdicCompletion.evalₐ
        (AdicCompletion.completionLocIdeal (I.map (algebraMap R (Localization.Away f)))
          (algebraMap R (Localization.Away f) g)) n
        (awayCompletionChartEquiv I f g hI hfg x) =
      Ideal.quotientMap _
        (AdicCompletion.locTransition (I.map (algebraMap R (Localization.Away f)))
          (algebraMap R (Localization.Away f) g))
        (AdicCompletion.locTransition_pow_le _ _ n)
        (Ideal.quotientMap _ (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom
          (awayAwayLocEquiv_pow_le I f g hfg n)
          (AdicCompletion.evalₐ (I.map (algebraMap R (Localization.Away g))) n x)) := by
  have hchart : awayCompletionChartEquiv I f g hI hfg x =
      AdicCompletion.interchangeForward (I.map (algebraMap R (Localization.Away f)))
        (algebraMap R (Localization.Away f) g) (hI.map _)
        (awayCompletionAwayEquiv I f g hI hfg x) := rfl
  rw [hchart, AdicCompletion.evalₐ_interchangeForward, evalₐ_awayCompletionAwayEquiv]

end FormalSpectrum
