import FormalSchemes.TateChainGlue
import FormalSchemes.GlueMorphisms
import FormalSchemes.TateAnnulus

set_option linter.style.header false

/-!
# Towards the structural morphism of the formal Tate chain

Fix an adic base `(R, I)` with `I` finitely generated and Noetherian `R`, and a topologically
nilpotent Tate parameter `q ∈ I`. The formal Tate chain `T = tateChain R I q hq hI`
(`FormalSchemes.TateChainGlue`) is glued from the ℤ-indexed family of formal annuli `Spf A`
(`A = R{x, y} / (x·y − q)`) along their consecutive overlaps. Each patch `Spf A` carries the affine
structural morphism `annulusStructMap : Spf A ⟶ Spf R` over the base.

The eventual goal (issue 209) is to assemble these per-patch structural morphisms into the single
glued structural morphism `tateChainStructMap : T ⟶ Spf R`, via the morphism-gluing combinator
`FormalScheme.GlueData.glueMorphisms` (`FormalSchemes.GlueMorphisms`). Its compatibility obligation
`f i j ≫ k i = t i j ≫ f j i ≫ k j` (with `k i = annulusStructMap` for every `i`) is verified by
casing on the index difference `d = j.down - i.down`:

* **diagonal** `d = 0` (`i = j`): both sides collapse to `annulusStructMap`;
* **far** `|d| ≥ 2`: the overlap `V(i, j)` is the empty (initial) locally ringed space, so any two
  morphisms out of it agree;
* **forward** `d = 1` / **backward** `d = -1`: both reduce to the geometric *crux* identity
  `annulusOverlapChart ≫ s = (annulusChartTransitionSpf).hom ≫ annulusOverlapChartY ≫ s`, which in
  turn rests on the ring identity `annulusOverlapTransitionInv_comp_algebraMap`: the coordinate-swap
  transition of the overlap ring fixes the image of the base `R`.

## What this file provides

This file lands the **ring-level and formal-spectrum infrastructure** for the adjacent-overlap crux:

* `AdicCompletion.congrIdeal_algebraMap` / `congrIdeal_symm_algebraMap`: the completion
  ideal-transport isomorphism (and its inverse) fixes the image of the base ring.
* `FormalSpectrum.spfCongrIdeal_hom_eq` / `spfCongrIdeal_inv_eq`: the geometric ideal-transport
  `spfCongrIdeal` is `Spf` of the completion transport `congrIdeal` — expressed as an honest
  `locallyRingedSpaceMap`, ready to be collapsed by `locallyRingedSpaceMap_comp`.
* `annulusOverlapTransitionInv_comp_algebraMap`: **the load-bearing ring identity** — the inverse
  completed transition `A[y⁻¹]^∧ →+* A[x⁻¹]^∧` composed with `R → A[y⁻¹]^∧` equals `R → A[x⁻¹]^∧`,
  i.e. the transition is a morphism of `R`-algebras. This is *the* reason the per-patch structural
  morphisms agree on the overlaps.
* `annulusOverlapTransitionSpf_hom_eq`: the forward completed-overlap transition as a
  `locallyRingedSpaceMap`.

## Remaining work (issue 209)

The final assembly is **not yet delivered** here:

* the combined ring-hom equality feeding `locallyRingedSpaceMap_congr` after both sides of the crux
  are collapsed to a single `locallyRingedSpaceMap` (the composite
  `R → A → A{1/y} ≅ A[y⁻¹]^∧ →(swap) A[x⁻¹]^∧ ≅ A{1/x}` equals `R → A → A{1/x}`) — the direct proof
  runs into very expensive `IsScalarTower` instance synthesis through the nested `AdicCompletion`
  towers (the same cost that already forces `synthInstance.maxHeartbeats` on the ring identity
  below), and needs a cheaper route than the naive scalar-tower rewrite chain;
* the geometric crux lemma `annulusOverlapChart ≫ s = (annulusChartTransitionSpf).hom ≫
  annulusOverlapChartY ≫ s` built from it via `locallyRingedSpaceMap_comp`/`_congr`;
* `tateChainStructMap` itself via `glueMorphisms` with the four-case `h`-obligation above.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AdicCompletion

variable {B : Type u} [CommRing B]

/-- The ideal-transport isomorphism of completions fixes the image of the base ring `B`. -/
theorem congrIdeal_algebraMap {K₁ K₂ : Ideal B} (h : K₁ = K₂) (b : B) :
    congrIdeal h (algebraMap B (AdicCompletion K₁ B) b) =
      algebraMap B (AdicCompletion K₂ B) b := by
  subst h; rfl

/-- The inverse ideal-transport isomorphism of completions fixes the image of the base ring. -/
theorem congrIdeal_symm_algebraMap {K₁ K₂ : Ideal B} (h : K₁ = K₂) (b : B) :
    (congrIdeal h).symm (algebraMap B (AdicCompletion K₂ B) b) =
      algebraMap B (AdicCompletion K₁ B) b := by
  subst h; rfl

end AdicCompletion

namespace FormalSpectrum

variable {B : Type u} [CommRing B]

/-- The ideal congruence relating `idealOfDefinition K₁` to `idealOfDefinition K₂` for `K₁ = K₂`
holds for `(congrIdeal h).toRingHom` (used to package `spfCongrIdeal` as a `locallyRingedSpaceMap`).
-/
theorem le_comap_congrIdeal {K₁ K₂ : Ideal B} (h : K₁ = K₂) :
    AdicCompletion.idealOfDefinition K₁ ≤
      (AdicCompletion.idealOfDefinition K₂).comap (AdicCompletion.congrIdeal h).toRingHom := by
  subst h; exact (Ideal.comap_id _).ge

theorem le_comap_congrIdeal_symm {K₁ K₂ : Ideal B} (h : K₁ = K₂) :
    AdicCompletion.idealOfDefinition K₂ ≤
      (AdicCompletion.idealOfDefinition K₁).comap (AdicCompletion.congrIdeal h).symm.toRingHom := by
  subst h; exact (Ideal.comap_id _).ge

/-- **The formal-spectrum ideal-transport is `Spf` of the completion transport.** The forward map of
`spfCongrIdeal h` is the locally-ringed-space map induced by the inverse ring transport
`(congrIdeal h).symm`. -/
theorem spfCongrIdeal_hom_eq {K₁ K₂ : Ideal B} (h : K₁ = K₂) :
    (spfCongrIdeal h).hom =
      locallyRingedSpaceMap (AdicCompletion.idealOfDefinition K₂)
        (AdicCompletion.idealOfDefinition K₁) (AdicCompletion.congrIdeal h).symm.toRingHom
        (le_comap_congrIdeal_symm h) := by
  subst h
  rw [locallyRingedSpaceMap_congr (AdicCompletion.idealOfDefinition K₁)
    (AdicCompletion.idealOfDefinition K₁) (AdicCompletion.congrIdeal (rfl : K₁ = K₁)).symm.toRingHom
    (RingHom.id (AdicCompletion K₁ B)) (le_comap_congrIdeal_symm rfl)
    (le_of_eq (Ideal.comap_id _).symm) rfl]
  exact (locallyRingedSpaceMap_id (AdicCompletion.idealOfDefinition K₁)).symm

/-- **The formal-spectrum ideal-transport (inverse).** The inverse map of `spfCongrIdeal h` is the
locally-ringed-space map induced by the forward ring transport `congrIdeal h`. -/
theorem spfCongrIdeal_inv_eq {K₁ K₂ : Ideal B} (h : K₁ = K₂) :
    (spfCongrIdeal h).inv =
      locallyRingedSpaceMap (AdicCompletion.idealOfDefinition K₁)
        (AdicCompletion.idealOfDefinition K₂) (AdicCompletion.congrIdeal h).toRingHom
        (le_comap_congrIdeal h) := by
  subst h
  rw [locallyRingedSpaceMap_congr (AdicCompletion.idealOfDefinition K₁)
    (AdicCompletion.idealOfDefinition K₁) (AdicCompletion.congrIdeal (rfl : K₁ = K₁)).toRingHom
    (RingHom.id (AdicCompletion K₁ B)) (le_comap_congrIdeal rfl)
    (le_of_eq (Ideal.comap_id _).symm) rfl]
  exact (locallyRingedSpaceMap_id (AdicCompletion.idealOfDefinition K₁)).symm

end FormalSpectrum

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

set_option synthInstance.maxHeartbeats 400000 in
-- The scalar-tower rewrites resolve `IsScalarTower`/algebra instances through the nested
-- completed-localization `AdicCompletion` towers `R → A → A[·⁻¹] → A[·⁻¹]^∧`, which is slow.
set_option maxHeartbeats 1600000 in
-- Correspondingly the elaboration heartbeat budget must be raised for the scalar-tower rewrites.
/-- **The coordinate-swap overlap transition fixes the image of the base `R`.** The inverse
completed transition `A[y⁻¹]^∧ →+* A[x⁻¹]^∧` composed with the structural map `R → A[y⁻¹]^∧` equals
the structural map `R → A[x⁻¹]^∧`; i.e. the transition is a morphism of `R`-algebras. This is the
ring-level reason the per-patch structural morphisms of the Tate chain agree on the overlaps. -/
theorem annulusOverlapTransitionInv_comp_algebraMap (hI : I.FG) :
    (annulusOverlapTransitionInv R I q hI).comp (algebraMap R (annulusOverlapY R I q)) =
      algebraMap R (annulusOverlap R I q) := by
  ext r
  rw [RingHom.comp_apply,
    IsScalarTower.algebraMap_apply R (annulusLocY R I q) (annulusOverlapY R I q),
    annulusOverlapTransitionInv_algebraMap, annulusLocTransition_symm_algebraMap_R,
    ← IsScalarTower.algebraMap_apply R (annulusLoc R I q) (annulusOverlap R I q)]

/-- Unfolding of the forward completed-overlap transition morphism as a `locallyRingedSpaceMap`. -/
theorem annulusOverlapTransitionSpf_hom_eq (hI : I.FG) :
    (annulusOverlapTransitionSpf R I q hI).hom =
      locallyRingedSpaceMap (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q))
        (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q))
        (annulusOverlapTransitionInv R I q hI)
        (annulusOverlapTransition_symm_isAdicHom R I q hI).le_comap :=
  rfl

end AlgebraicGeometry
