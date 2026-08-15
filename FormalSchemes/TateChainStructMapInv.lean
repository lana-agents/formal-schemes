import FormalSchemes.TateChainStructMap
import FormalSchemes.TateOverlapInversionIso

set_option linter.style.header false

/-!
# The geometric adjacent-overlap crux for the corrected 𝔾m-inversion Tate gluing

Fix an adic base `(R, I)` with `I` finitely generated and Noetherian `R`, and a Tate parameter
`q ∈ I`. The model-fix issue 435 replaces the coordinate-**swap** overlap transition
`annulusChartTransitionSpf` (which yields the *non-separated* line-with-doubled-origin) by the
genuine 𝔾m-**inversion** transition `annulusChartTransitionInvSpf` (issue 437,
`FormalSchemes.TateOverlapInversionIso`, `X ↦ Y⁻¹`, the Néron 2-gon gluing).

This file delivers the **`Inv` analogue of the geometric adjacent-overlap crux**
(`annulusOverlapChart_comp_structMap` / `annulusOverlapChartY_comp_structMap`,
`FormalSchemes.TateChainStructMap`): on the `x`-overlap `Spf A{1/x}`, the open-immersion chart
followed by the structural morphism `Spf A ⟶ Spf R` agrees with the corrected chart transition
`annulusChartTransitionInvSpf` followed by the `y`-chart and the structural morphism. This is the
load-bearing identity that the model rewire (issue 438b) consumes to keep the rerouted
`tateCurveModelStructMap` green — it is the `Inv` replacement for the two crux lemmas the current
`tateCurveModelStructMap` cites off the diagonal.

Everything here is **purely additive**: no existing declaration is modified. The proof mirrors the
flip crux verbatim (collapse both sides to a single `FormalSpectrum.locallyRingedSpaceMap`, match by
`locallyRingedSpaceMap_congr` fed by a ring identity), with three substitutions:

* the chart transition `annulusChartTransitionSpf` ⟶ `annulusChartTransitionInvSpf`;
* the middle-transition unfolding `annulusOverlapTransitionSpf_hom_eq` ⟶
  `annulusOverlapInversionSpf_hom_eq`;
* the adic-hom continuity witness `annulusOverlapTransition_symm_isAdicHom` ⟶
  `annulusOverlapInversion_symm_isAdicHom` (issue 437);

and the underlying ring identity `annulusChartTransition_comp_awayCompletionHom` replaced by the
`Inv` analogue `annulusChartTransitionInv_comp_awayCompletionHom` below. Crucially, that ring
identity is **not** proved through the localization level (the inversion is only `R`-linear, *not*
`annulusLoc`-linear — this is exactly the geometric content of the model fix): it is built at the
`R` level from issue 437's `annulusOverlapInversion_symm_comp_algebraMap`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- Unfolding of the forward completed **inversion** overlap transition morphism as a
`locallyRingedSpaceMap`, mirroring `annulusOverlapTransitionSpf_hom_eq`. -/
theorem annulusOverlapInversionSpf_hom_eq (hI : I.FG) :
    (annulusOverlapInversionSpf R I q hI).hom =
      locallyRingedSpaceMap (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q))
        (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q))
        (annulusOverlapInversion R I q hI).symm.toRingHom
        (annulusOverlapInversion_symm_isAdicHom R I q hI).le_comap :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- The scalar-tower rewrites resolve `IsScalarTower`/algebra instances through the nested
-- completed-localization `AdicCompletion` towers `R → A → A[·⁻¹] → A[·⁻¹]^∧`, which is slow.
set_option maxHeartbeats 1600000 in
-- Correspondingly the elaboration heartbeat budget must be raised for the scalar-tower rewrites.
/-- **The 𝔾m-inversion overlap transition fixes the image of the base `R`** (ring level). The
inverse completed inversion transition `A[y⁻¹]^∧ →+* A[x⁻¹]^∧`, conjugated by the two chart-domain
completion transports and precomposed with the structural map `R → A → A{1/y}`, equals the
structural map `R → A → A{1/x}`. This is the `Inv` analogue of
`annulusChartTransition_comp_awayCompletionHom`; unlike the flip version it goes through the
`R`-level linearity `annulusOverlapInversion_symm_comp_algebraMap` (issue 437), since the inversion
is only `R`-linear, not `annulusLoc`-linear. -/
theorem annulusChartTransitionInv_comp_awayCompletionHom (hI : I.FG) :
    ((AdicCompletion.congrIdeal (annulusChart_locIdeal_eq R I q)).symm.toRingHom.comp
          (((annulusOverlapInversion R I q hI).symm.toRingHom).comp
            (AdicCompletion.congrIdeal (annulusChartY_locIdeal_eq R I q)).toRingHom)).comp
        ((awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)).comp
          (algebraMap R (annulusAlgebra R I q))) =
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)).comp
        (algebraMap R (annulusAlgebra R I q)) := by
  -- `awayCompletionHom overlapY ∘ (R → A)` collapses through the scalar tower to
  -- `(annulusLocY → A{1/y}) ∘ (R → annulusLocY)`.
  have hCY : (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)).comp
        (algebraMap R (annulusAlgebra R I q)) =
      (algebraMap (annulusLocY R I q)
        (awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q))).comp
        (algebraMap R (annulusLocY R I q)) := by
    change ((algebraMap (annulusLocY R I q)
          (awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q))).comp
        (algebraMap (annulusAlgebra R I q) (annulusLocY R I q))).comp
        (algebraMap R (annulusAlgebra R I q)) = _
    rw [RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q) (annulusLocY R I q)]
  have hL : (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)).comp
        (algebraMap R (annulusAlgebra R I q)) =
      (algebraMap (annulusLoc R I q)
        (awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q))).comp
        (algebraMap R (annulusLoc R I q)) := by
    change ((algebraMap (annulusLoc R I q)
          (awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q))).comp
        (algebraMap (annulusAlgebra R I q) (annulusLoc R I q))).comp
        (algebraMap R (annulusAlgebra R I q)) = _
    rw [RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q) (annulusLoc R I q)]
  -- `(congrIdeal chartY) ∘ (annulusLocY → A{1/y}) = (annulusLocY → A[y⁻¹]^∧)`, so composed with
  -- `R → annulusLocY` (scalar tower) it is `R → A[y⁻¹]^∧ = algebraMap R annulusOverlapY`.
  have hRY : (AdicCompletion.congrIdeal (annulusChartY_locIdeal_eq R I q)).toRingHom.comp
        ((awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)).comp
          (algebraMap R (annulusAlgebra R I q))) =
      algebraMap R (annulusOverlapY R I q) := by
    rw [hCY, ← RingHom.comp_assoc,
      AdicCompletion.congrIdeal_toRingHom_comp_algebraMap (annulusChartY_locIdeal_eq R I q),
      ← IsScalarTower.algebraMap_eq R (annulusLocY R I q) (annulusOverlapY R I q)]
  -- `(congrIdeal chartX).symm ∘ (annulusLoc → A[x⁻¹]^∧) = (annulusLoc → A{1/x})`, so composed with
  -- `R → annulusLoc` it is `R → A{1/x}` — i.e. the RHS after `hL`.
  have hRX : (AdicCompletion.congrIdeal (annulusChart_locIdeal_eq R I q)).symm.toRingHom.comp
        (algebraMap R (annulusOverlap R I q)) =
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)).comp
        (algebraMap R (annulusAlgebra R I q)) := by
    rw [hL, IsScalarTower.algebraMap_eq R (annulusLoc R I q) (annulusOverlap R I q),
      ← RingHom.comp_assoc,
      AdicCompletion.congrIdeal_symm_toRingHom_comp_algebraMap (annulusChart_locIdeal_eq R I q)]
  rw [RingHom.comp_assoc, RingHom.comp_assoc, hRY,
    annulusOverlapInversion_symm_comp_algebraMap R I q hI, hRX]

set_option synthInstance.maxHeartbeats 400000 in
-- Collapsing both sides to a single `locallyRingedSpaceMap` resolves algebra/`IsScalarTower`
-- instances through the nested `AdicCompletion` towers, which is slow.
set_option maxHeartbeats 1600000 in
-- Correspondingly the elaboration heartbeat budget must be raised for those rewrites.
/-- **The geometric adjacent-overlap crux for the 𝔾m-inversion gluing (forward step).** On the
`x`-overlap `Spf A{1/x}`, the open-immersion chart followed by the structural morphism agrees with
the corrected chart transition `Spf A{1/x} ≅ Spf A{1/y}` (`annulusChartTransitionInvSpf`) followed
by the `y`-chart and the structural morphism. `Inv` analogue of
`annulusOverlapChart_comp_structMap`: both sides collapse to a single `locallyRingedSpaceMap` and
match by `locallyRingedSpaceMap_congr` fed by `annulusChartTransitionInv_comp_awayCompletionHom`. -/
theorem annulusOverlapChart_comp_structMap_inv [TopologicalSpace R] [IsAdicRing I]
    [IsNoetherianRing R] (hI : I.FG) :
    annulusOverlapChart R I q ≫ annulusStructMap R I q hI =
      (annulusChartTransitionInvSpf R I q hI).hom ≫
        annulusOverlapChartY R I q ≫ annulusStructMap R I q hI := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  -- Continuity witnesses for each pairwise collapse of the RHS composite into a single
  -- `locallyRingedSpaceMap`, built from the piecewise continuities (only `hC` differs from the flip
  -- crux: it uses the inversion's adic-hom witness from issue 437).
  have hA := le_comap_comp (algebraMap R (annulusAlgebra R I q))
    (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q))
    (Ideal.map_le_iff_le_comap.mp (annulus_map_eq R I q).le)
    (le_comap_awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q))
  have hB := le_comap_comp _ _ hA
    (FormalSpectrum.le_comap_congrIdeal (annulusChartY_locIdeal_eq R I q))
  have hC := le_comap_comp _ _ hB
    (annulusOverlapInversion_symm_isAdicHom R I q hI).le_comap
  have hD := le_comap_comp _ _ hC
    (FormalSpectrum.le_comap_congrIdeal_symm (annulusChart_locIdeal_eq R I q))
  have hL0 := le_comap_comp (algebraMap R (annulusAlgebra R I q))
    (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q))
    (Ideal.map_le_iff_le_comap.mp (annulus_map_eq R I q).le)
    (le_comap_awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q))
  rw [annulusOverlapChart, annulusStructMap, IsTopologicallyFiniteType.structMap,
    FormalSpectrum.basicOpenChart, ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hL0)]
  rw [annulusChartTransitionInvSpf, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    annulusChartDomainSpfX, annulusChartDomainSpfY,
    FormalSpectrum.spfCongrIdeal_hom_eq, FormalSpectrum.spfCongrIdeal_inv_eq,
    annulusOverlapInversionSpf_hom_eq,
    annulusOverlapChartY, FormalSpectrum.basicOpenChart,
    Category.assoc, Category.assoc,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hA),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hB),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hC),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hD)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (by rw [← annulusChartTransitionInv_comp_awayCompletionHom R I q hI,
        RingHom.comp_assoc, RingHom.comp_assoc])

/-- **The geometric adjacent-overlap crux for the 𝔾m-inversion gluing (backward step)**, obtained
from the forward crux by pre-composing with the inverse transition. -/
theorem annulusOverlapChartY_comp_structMap_inv [TopologicalSpace R] [IsAdicRing I]
    [IsNoetherianRing R] (hI : I.FG) :
    annulusOverlapChartY R I q ≫ annulusStructMap R I q hI =
      (annulusChartTransitionInvSpf R I q hI).inv ≫
        annulusOverlapChart R I q ≫ annulusStructMap R I q hI := by
  rw [annulusOverlapChart_comp_structMap_inv R I q hI, Iso.inv_hom_id_assoc]

end AlgebraicGeometry
