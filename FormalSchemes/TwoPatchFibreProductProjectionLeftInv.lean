import FormalSchemes.TwoPatchFibreProductProjectionLeft
import FormalSchemes.TateChartTransitionInvAlgEq

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The `y`-side bridge square for the 𝔾m-inversion two-patch first projection

This is the 𝔾m-**inversion** analogue of the load-bearing bridge lemma
`spfESymm_comp_spfAwayY_comp_baseBridge` of `FormalSchemes.TwoPatchFibreProductProjectionLeft`. The
swap version is keyed on the coordinate-swap chart transition `annulusChartTransitionSpf`; this
version is keyed on the geometrically-correct inversion transition `annulusChartTransitionInvSpf`.

The only mathematical content that differs is the transition: everywhere the swap proof cites
`annulusChartTransitionAlg`/`annulusChartTransitionSpf` and their algebra unfoldings, the inversion
proof cites `annulusChartTransitionInvAlg`/`annulusChartTransitionInvSpf`
(`FormalSchemes.TateChartTransitionInvAlgEq`).

## Main results

* `annulusFibreChartTransitionInvAlg_symm_toRingHom`: the inversion analogue of
  `annulusFibreChartTransitionAlg_symm_toRingHom`.
* `spfESymm_comp_spfAwayY_comp_baseBridge_inv`: the inversion analogue of
  `spfESymm_comp_spfAwayY_comp_baseBridge`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum
open CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- Continuity of a composite ring homomorphism, in `comap` form. -/
private theorem le_comap_comp' {S T U : Type u} [CommRing S] [CommRing T] [CommRing U]
    {J : Ideal S} {K : Ideal T} {L : Ideal U} (φ : S →+* T) (ψ : T →+* U)
    (hJK : J ≤ K.comap φ) (hKL : K ≤ L.comap ψ) : J ≤ L.comap (ψ.comp φ) :=
  fun _ hx => hKL (hJK hx)

/-- The underlying ring hom of the inverse base-changed inversion chart transition, unfolded through
the two ideal-convention bridges and `annulusChartTransitionInvAlg.symm`. The inversion analogue of
`annulusFibreChartTransitionAlg_symm_toRingHom`. -/
theorem annulusFibreChartTransitionInvAlg_symm_toRingHom (hI : I.FG) :
    (annulusFibreChartTransitionInvAlg R I q hI).symm.toRingHom =
      (annulusFibreChartBridgeX R I q).symm.toRingHom.comp
        ((annulusChartTransitionInvAlg R I q hI).symm.toRingHom.comp
          (annulusFibreChartBridgeY R I q).toRingHom) := by
  rw [annulusFibreChartTransitionInvAlg, AlgEquiv.symm_trans_eq, AlgEquiv.symm_trans_eq,
    AlgEquiv.symm_symm, algEquiv_trans_toRingHom, algEquiv_trans_toRingHom]

/-- **The base-changed inversion transition, followed by the `y`-first-projection into the target
convention, factors through the annulus inversion chart transition and the `y`-overlap chart.** The
inversion analogue of `spfESymm_comp_spfAwayY_comp_baseBridge`. -/
theorem spfESymm_comp_spfAwayY_comp_baseBridge_inv (hI : I.FG) :
    FormalSpectrum.locallyRingedSpaceMap
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))))
        (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom.toRingHom
        (CompletedTensorProduct.algHom_mapIdeal_isAdicHom
          (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom).le_comap ≫
      (FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (annulusAlgebra R I q)))
          (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q))))
          (awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
          (le_comap_awayCompletionHom_base I (overlapY R I q)) ≫ annulusBaseBridge R I q) =
      annulusOverlapBridgeX R I q ≫ (annulusChartTransitionInvSpf R I q hI).hom ≫
        annulusOverlapChartY R I q := by
  have hφ : (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom.toRingHom.comp
        ((awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)).comp
          (RingHom.id (annulusAlgebra R I q))) =
      (annulusFibreChartBridgeX R I q).symm.toRingHom.comp
        ((annulusChartTransitionInvAlg R I q hI).symm.toRingHom.comp
          (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q))) := by
    rw [algEquiv_toAlgHom_toRingHom, annulusFibreChartTransitionInvAlg_symm_toRingHom,
      RingHom.comp_id, RingHom.comp_assoc, RingHom.comp_assoc, awayCompletionHom_bridgeY]
  have hL_inner : annulusIdealOfDefinition R I q ≤
      (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q)))).comap
        ((awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)).comp
          (RingHom.id (annulusAlgebra R I q))) := by
    rw [RingHom.comp_id]
    exact (annulus_map_eq R I q).ge.trans
      (le_comap_awayCompletionHom_base I (overlapY R I q))
  have hR_inner : annulusIdealOfDefinition R I q ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)).comap
        ((annulusChartTransitionInvAlg R I q hI).symm.toRingHom.comp
          (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q))) :=
    le_comap_comp' _ _
      (FormalSpectrum.le_comap_awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q))
      (annulusChartTransitionInvAlg_symm_le_comap R I q hI)
  have h3 : awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q) ≤
      (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q)))).comap (annulusFibreChartBridgeX R I q).symm.toRingHom := by
    rw [CompletedTensorAwayInterchange.idealOfDef_base_eq, annulusFibreChartBridgeX,
      AdicCompletion.congrIdealₐ_symm_toRingHom]
    exact FormalSpectrum.le_comap_congrIdeal_symm _
  have hR_outer : annulusIdealOfDefinition R I q ≤
      (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q)))).comap
        ((annulusFibreChartBridgeX R I q).symm.toRingHom.comp
          ((annulusChartTransitionInvAlg R I q hI).symm.toRingHom.comp
            (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)))) :=
    le_comap_comp' _ _ hR_inner h3
  have hL_outer : annulusIdealOfDefinition R I q ≤
      (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q)))).comap
        ((annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom.toRingHom.comp
          ((awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)).comp
            (RingHom.id (annulusAlgebra R I q)))) := by
    rw [hφ]
    exact hR_outer
  rw [annulusChartTransitionInvSpf_hom_eq, annulusBaseBridge, annulusOverlapBridgeX,
    annulusOverlapChartY, FormalSpectrum.basicOpenChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hL_inner),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hL_outer),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hR_inner),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hR_outer)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ hφ

end AlgebraicGeometry
