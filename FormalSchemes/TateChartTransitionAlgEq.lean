import FormalSchemes.TwoPatchFibreProduct

set_option linter.style.header false

/-!
# The geometric annulus chart transition is `Spf` of its `R`-algebra avatar

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ R`, and let
`A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus. The geometric overlap
transition on the annulus charts `annulusChartTransitionSpf : Spf A{1/x} ≅ Spf A{1/y}`
(`FormalSchemes.TateChartTransition`) is assembled from bare ring isomorphisms, while its
`R`-algebra upgrade `annulusChartTransitionAlg : A{1/x} ≃ₐ[R] A{1/y}`
(`FormalSchemes.TwoPatchFibreProduct`) packages the same data as an honest `R`-algebra isomorphism,
suitable for feeding to the base-change machinery `CompletedTensorProduct.mapSpfIso`.

This file identifies the two: the forward map of `annulusChartTransitionSpf` is exactly the
`locallyRingedSpaceMap` induced (contravariantly) by the inverse ring homomorphism
`annulusChartTransitionAlg.symm.toRingHom`. This is the *crux lemma* that lets the two-patch
fibre-product construction reconcile the geometrically glued first projection `pr₁` with the
`Spf` of the algebraic transition (issue 236).

## Main results

* `annulusChartTransitionSpf_hom_eq`: `(annulusChartTransitionSpf).hom` is the
  `locallyRingedSpaceMap` of `annulusChartTransitionAlg.symm.toRingHom`.

## Proof outline

`annulusChartTransitionSpf.hom` unfolds (mirroring `annulusOverlapChart_comp_structMap` in
`FormalSchemes.TateChainStructMap`) into three `locallyRingedSpaceMap`s — the two chart-domain
identifications `spfCongrIdeal` (via `spfCongrIdeal_hom_eq` / `spfCongrIdeal_inv_eq`) and the
completed-overlap transition (`annulusOverlapTransitionSpf_hom_eq`). These fuse, via
`locallyRingedSpaceMap_comp`, into a single `locallyRingedSpaceMap` of the composite ring hom
`(congrIdeal _).symm.toRingHom ∘ annulusOverlapTransitionInv ∘ (congrIdeal _).toRingHom`. On the
other side, `annulusChartTransitionAlg.symm.toRingHom` unfolds — through the algebra-level
`congrIdealₐ` and `annulusOverlapTransitionAlg` — into the *same* composite (the three bridge
lemmas `congrIdealₐ_toRingHom`, `congrIdealₐ_symm_toRingHom` and
`annulusOverlapTransitionAlg_symm_toRingHom` identify the algebra pieces with their ring
counterparts, keeping the expensive `congrIdeal` opaque
via `subst`). `locallyRingedSpaceMap_congr` then closes the goal at the bare `RingHom` level.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

/-- `symm` distributes (contravariantly) over `AlgEquiv.trans`. Stated generically so it can be used
as a black-box rewrite at the (otherwise expensive) concrete annulus completion types. -/
theorem AlgEquiv.symm_trans_eq {R A B C : Type u} [CommSemiring R] [Semiring A] [Semiring B]
    [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
    (e₁ : A ≃ₐ[R] B) (e₂ : B ≃ₐ[R] C) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  AlgEquiv.ext fun _ => rfl

/-- The underlying ring hom of `AlgEquiv.trans` is the (contravariant) composite of the underlying
ring homs. Stated (and proved by `rfl`) generically so the kernel verifies it once at abstract types
and reuses it as a black-box rewrite at the expensive concrete annulus completion types. -/
theorem algEquiv_trans_toRingHom {R A B C : Type u} [CommSemiring R] [Semiring A] [Semiring B]
    [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
    (e₁ : A ≃ₐ[R] B) (e₂ : B ≃ₐ[R] C) :
    (e₁.trans e₂).toRingHom = e₂.toRingHom.comp e₁.toRingHom :=
  rfl

namespace AdicCompletion

variable {B : Type u} [CommRing B]

/-- The underlying ring hom of the *algebra* ideal-transport `congrIdealₐ` is the *ring*
ideal-transport `congrIdeal`. Proved by `subst` so `congrIdeal` is never unfolded at concrete
completion types. -/
theorem congrIdealₐ_toRingHom (R : Type u) [CommRing R] [Algebra R B] {K₁ K₂ : Ideal B}
    (h : K₁ = K₂) :
    (AdicCompletion.congrIdealₐ R h).toRingHom = (AdicCompletion.congrIdeal h).toRingHom := by
  subst h; rfl

/-- The underlying ring hom of the inverse *algebra* ideal-transport `(congrIdealₐ).symm` is the
inverse *ring* ideal-transport `(congrIdeal).symm`. -/
theorem congrIdealₐ_symm_toRingHom (R : Type u) [CommRing R] [Algebra R B] {K₁ K₂ : Ideal B}
    (h : K₁ = K₂) :
    (AdicCompletion.congrIdealₐ R h).symm.toRingHom =
      (AdicCompletion.congrIdeal h).symm.toRingHom := by
  subst h; rfl

end AdicCompletion

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The underlying ring hom of the inverse `R`-algebra overlap transition is the ring-level inverse
transition `annulusOverlapTransitionInv`. -/
theorem annulusOverlapTransitionAlg_symm_toRingHom (hI : I.FG) :
    (annulusOverlapTransitionAlg R I q hI).symm.toRingHom =
      annulusOverlapTransitionInv R I q hI := by
  exact RingHom.ext fun x => rfl

/-- The underlying ring hom of the inverse `R`-algebra chart transition, unfolded as the composite
`(congrIdeal _).symm ∘ annulusOverlapTransitionInv ∘ (congrIdeal _)` of ring homs. Kept at the
`RingHom.comp` level with `congrIdeal` opaque. -/
theorem annulusChartTransitionAlg_symm_toRingHom_eq (hI : I.FG) :
    (annulusChartTransitionAlg R I q hI).symm.toRingHom =
      (AdicCompletion.congrIdeal (annulusChart_locIdeal_eq R I q)).symm.toRingHom.comp
        ((annulusOverlapTransitionInv R I q hI).comp
          (AdicCompletion.congrIdeal (annulusChartY_locIdeal_eq R I q)).toRingHom) := by
  rw [annulusChartTransitionAlg, AlgEquiv.symm_trans_eq, AlgEquiv.symm_trans_eq,
    AlgEquiv.symm_symm, algEquiv_trans_toRingHom, algEquiv_trans_toRingHom,
    annulusChartOverlapAlgX, annulusChartOverlapAlgY,
    annulusOverlapTransitionAlg_symm_toRingHom,
    AdicCompletion.congrIdealₐ_symm_toRingHom, AdicCompletion.congrIdealₐ_toRingHom]

/-- The continuity witness for `annulusChartTransitionSpf_hom_eq`: the inverse algebra chart
transition carries the `y`-ideal of definition into the `x`-ideal (in the `comap` sense). Obtained
by rewriting through `annulusChartTransitionAlg_symm_toRingHom_eq` and chaining the piecewise
continuities. -/
theorem annulusChartTransitionAlg_symm_le_comap (hI : I.FG) :
    awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q) ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)).comap
        (annulusChartTransitionAlg R I q hI).symm.toRingHom := by
  rw [annulusChartTransitionAlg_symm_toRingHom_eq]
  exact le_comap_comp _ _
    (le_comap_comp _ _
      (FormalSpectrum.le_comap_congrIdeal (annulusChartY_locIdeal_eq R I q))
      (annulusOverlapTransition_symm_isAdicHom R I q hI).le_comap)
    (FormalSpectrum.le_comap_congrIdeal_symm (annulusChart_locIdeal_eq R I q))

set_option synthInstance.maxHeartbeats 400000 in
-- Unfolding `annulusChartTransitionSpf.hom` and collapsing the three-map composite resolves
-- algebra/`IsScalarTower` instances through the nested `AdicCompletion` towers, which is slow.
set_option maxHeartbeats 1600000 in
-- Correspondingly the elaboration heartbeat budget must be raised for those rewrites.
/-- **The geometric annulus chart transition is `Spf` of its `R`-algebra avatar.** The forward map
of `annulusChartTransitionSpf : Spf A{1/x} ≅ Spf A{1/y}` is the locally-ringed-space map induced
(contravariantly) by the inverse ring homomorphism `annulusChartTransitionAlg.symm.toRingHom`. This
identifies the geometrically glued chart transition with the `Spf` of the algebraic transition,
unblocking the first projection of the two-patch fibre product (issue 236). -/
theorem annulusChartTransitionSpf_hom_eq (hI : I.FG) :
    (annulusChartTransitionSpf R I q hI).hom =
      FormalSpectrum.locallyRingedSpaceMap
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (annulusChartTransitionAlg R I q hI).symm.toRingHom
        (annulusChartTransitionAlg_symm_le_comap R I q hI) := by
  -- Continuity witnesses for the pairwise collapse of the three-map composite.
  have hInner := le_comap_comp _ _
    (FormalSpectrum.le_comap_congrIdeal (annulusChartY_locIdeal_eq R I q))
    (annulusOverlapTransition_symm_isAdicHom R I q hI).le_comap
  have hOuter := le_comap_comp _ _ hInner
    (FormalSpectrum.le_comap_congrIdeal_symm (annulusChart_locIdeal_eq R I q))
  rw [annulusChartTransitionSpf, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    annulusChartDomainSpfX, annulusChartDomainSpfY,
    FormalSpectrum.spfCongrIdeal_hom_eq, FormalSpectrum.spfCongrIdeal_inv_eq,
    annulusOverlapTransitionSpf_hom_eq,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hInner),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hOuter)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (annulusChartTransitionAlg_symm_toRingHom_eq R I q hI).symm

end AlgebraicGeometry
