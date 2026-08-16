import FormalSchemes.TateChartTransitionAlgEq
import FormalSchemes.TateSelfProductTransitionInv
import FormalSchemes.TateChainStructMapInv

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The geometric 𝔾m-inversion annulus chart transition is `Spf` of its `R`-algebra avatar

This is the 𝔾m-**inversion** analogue of `FormalSchemes.TateChartTransitionAlgEq`. Where that file
identifies the coordinate-swap chart transition `annulusChartTransitionSpf` with `Spf` of
`annulusChartTransitionAlg.symm`, this file identifies the geometrically-correct inversion chart
transition `annulusChartTransitionInvSpf` with `Spf` of `annulusChartTransitionInvAlg.symm`.

Everything mirrors the swap file verbatim, with the overlap transition replaced by the inversion
one (`annulusOverlapTransitionAlg`→`annulusOverlapInversionAlg`,
`annulusOverlapTransitionInv`→`(annulusOverlapInversion).symm.toRingHom`,
`annulusOverlapTransition_symm_isAdicHom`→`annulusOverlapInversion_symm_isAdicHom`,
`annulusOverlapTransitionSpf_hom_eq`→`annulusOverlapInversionSpf_hom_eq`).

## Main results

* `annulusChartTransitionInvSpf_hom_eq`: `(annulusChartTransitionInvSpf).hom` is the
  `locallyRingedSpaceMap` of `annulusChartTransitionInvAlg.symm.toRingHom`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The underlying ring hom of the inverse `R`-algebra inversion overlap transition is the
ring-level inverse inversion transition `(annulusOverlapInversion).symm.toRingHom`. -/
theorem annulusOverlapInversionAlg_symm_toRingHom (hI : I.FG) :
    (annulusOverlapInversionAlg R I q hI).symm.toRingHom =
      (annulusOverlapInversion R I q hI).symm.toRingHom :=
  RingHom.ext fun _ => rfl

/-- The underlying ring hom of the inverse `R`-algebra inversion chart transition, unfolded as the
composite `(congrIdeal _).symm ∘ (annulusOverlapInversion).symm ∘ (congrIdeal _)` of ring homs. Kept
at the `RingHom.comp` level with `congrIdeal` opaque. The inversion analogue of
`annulusChartTransitionAlg_symm_toRingHom_eq`. -/
theorem annulusChartTransitionInvAlg_symm_toRingHom_eq (hI : I.FG) :
    (annulusChartTransitionInvAlg R I q hI).symm.toRingHom =
      (AdicCompletion.congrIdeal (annulusChart_locIdeal_eq R I q)).symm.toRingHom.comp
        ((annulusOverlapInversion R I q hI).symm.toRingHom.comp
          (AdicCompletion.congrIdeal (annulusChartY_locIdeal_eq R I q)).toRingHom) := by
  rw [annulusChartTransitionInvAlg, AlgEquiv.symm_trans_eq, AlgEquiv.symm_trans_eq,
    AlgEquiv.symm_symm, algEquiv_trans_toRingHom, algEquiv_trans_toRingHom,
    annulusChartOverlapAlgX, annulusChartOverlapAlgY,
    annulusOverlapInversionAlg_symm_toRingHom,
    AdicCompletion.congrIdealₐ_symm_toRingHom, AdicCompletion.congrIdealₐ_toRingHom]

/-- The continuity witness for `annulusChartTransitionInvSpf_hom_eq`: the inverse algebra inversion
chart transition carries the `y`-ideal of definition into the `x`-ideal (in the `comap` sense). The
inversion analogue of `annulusChartTransitionAlg_symm_le_comap`. -/
theorem annulusChartTransitionInvAlg_symm_le_comap (hI : I.FG) :
    awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q) ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)).comap
        (annulusChartTransitionInvAlg R I q hI).symm.toRingHom := by
  rw [annulusChartTransitionInvAlg_symm_toRingHom_eq]
  exact le_comap_comp _ _
    (le_comap_comp _ _
      (FormalSpectrum.le_comap_congrIdeal (annulusChartY_locIdeal_eq R I q))
      (annulusOverlapInversion_symm_isAdicHom R I q hI).le_comap)
    (FormalSpectrum.le_comap_congrIdeal_symm (annulusChart_locIdeal_eq R I q))

set_option synthInstance.maxHeartbeats 400000 in
-- Unfolding `annulusChartTransitionInvSpf.hom` and collapsing the three-map composite resolves
-- algebra/`IsScalarTower` instances through the nested `AdicCompletion` towers, which is slow.
set_option maxHeartbeats 1600000 in
-- Correspondingly the elaboration heartbeat budget must be raised for those rewrites.
/-- **The geometric 𝔾m-inversion annulus chart transition is `Spf` of its `R`-algebra avatar.** The
forward map of `annulusChartTransitionInvSpf : Spf A{1/x} ≅ Spf A{1/y}` is the
locally-ringed-space map induced (contravariantly) by the inverse ring homomorphism
`annulusChartTransitionInvAlg.symm.toRingHom`. The inversion analogue of
`annulusChartTransitionSpf_hom_eq`. -/
theorem annulusChartTransitionInvSpf_hom_eq (hI : I.FG) :
    (annulusChartTransitionInvSpf R I q hI).hom =
      FormalSpectrum.locallyRingedSpaceMap
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (annulusChartTransitionInvAlg R I q hI).symm.toRingHom
        (annulusChartTransitionInvAlg_symm_le_comap R I q hI) := by
  have hInner := le_comap_comp _ _
    (FormalSpectrum.le_comap_congrIdeal (annulusChartY_locIdeal_eq R I q))
    (annulusOverlapInversion_symm_isAdicHom R I q hI).le_comap
  have hOuter := le_comap_comp _ _ hInner
    (FormalSpectrum.le_comap_congrIdeal_symm (annulusChart_locIdeal_eq R I q))
  rw [annulusChartTransitionInvSpf, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    annulusChartDomainSpfX, annulusChartDomainSpfY,
    FormalSpectrum.spfCongrIdeal_hom_eq, FormalSpectrum.spfCongrIdeal_inv_eq,
    annulusOverlapInversionSpf_hom_eq,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hInner),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hOuter)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (annulusChartTransitionInvAlg_symm_toRingHom_eq R I q hI).symm

end AlgebraicGeometry
