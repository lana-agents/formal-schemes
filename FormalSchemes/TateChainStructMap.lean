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

/-- `RingHom.comp` form of `congrIdeal_algebraMap`: the transport, as a ring hom, precomposed with
the structural map `B → AdicCompletion K₁ B`, is the structural map `B → AdicCompletion K₂ B`.
Stated over an abstract base `B` so that the (otherwise very expensive) `congrIdeal` never has to be
unfolded at concrete completion types — the caller uses this as a black-box `rw` lemma. -/
theorem congrIdeal_toRingHom_comp_algebraMap {K₁ K₂ : Ideal B} (h : K₁ = K₂) :
    (congrIdeal h).toRingHom.comp (algebraMap B (AdicCompletion K₁ B)) =
      algebraMap B (AdicCompletion K₂ B) :=
  RingHom.ext (congrIdeal_algebraMap h)

/-- `RingHom.comp` form of `congrIdeal_symm_algebraMap` (abstract base `B`). -/
theorem congrIdeal_symm_toRingHom_comp_algebraMap {K₁ K₂ : Ideal B} (h : K₁ = K₂) :
    (congrIdeal h).symm.toRingHom.comp (algebraMap B (AdicCompletion K₂ B)) =
      algebraMap B (AdicCompletion K₁ B) :=
  RingHom.ext (congrIdeal_symm_algebraMap h)

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

/-- `RingHom.comp` form of `annulusOverlapTransitionInv_algebraMap`: the inverse completed
transition precomposed with `annulusLocY → annulusOverlapY` equals `annulusLoc → annulusOverlap`
precomposed with the (uncompleted) inverse coordinate swap `annulusLocY → annulusLoc`. Native
completion types, no `congrIdeal`, so cheap. -/
theorem annulusOverlapTransitionInv_comp_algebraMap_locY (hI : I.FG) :
    (annulusOverlapTransitionInv R I q hI).comp
        (algebraMap (annulusLocY R I q) (annulusOverlapY R I q)) =
      (algebraMap (annulusLoc R I q) (annulusOverlap R I q)).comp
        ((annulusLocTransition R I q hI).symm : annulusLocY R I q →+* annulusLoc R I q) :=
  RingHom.ext fun c => annulusOverlapTransitionInv_algebraMap R I q hI c

set_option synthInstance.maxHeartbeats 400000 in
-- The `RingHom.comp` rewrites resolve algebra/`IsScalarTower` instances through the nested
-- completed-localization `AdicCompletion` towers, which is slow.
set_option maxHeartbeats 800000 in
-- Correspondingly the elaboration heartbeat budget must be raised for those rewrites.
/-- **The chart transition intertwines the structural maps over the base**, at the ring level.
The composite ring map underlying `annulusChartTransitionSpf.hom` — namely
`A{1/y} ≅ A[y⁻¹]^∧ →(swap) A[x⁻¹]^∧ ≅ A{1/x}` — precomposed with the structural map `R → A → A{1/y}`
equals the structural map `R → A → A{1/x}`. This is the ring-level heart of the adjacent-overlap
crux: the coordinate-swap transition of the Tate chain fixes the image of the base `R`, so the
per-patch structural morphisms agree on the overlaps.

The proof stays entirely at the `RingHom.comp` level. This is essential: `AdicCompletion.congrIdeal`
of the (propositional) chart ideal equalities is a `subst`-defined transport whose unfolding at the
concrete annulus completion types is pathologically expensive, so it must never be forced through a
`rfl`/`ext`/elementwise defeq. The generic `RingHom.comp` congrIdeal lemmas
(`congrIdeal_(symm_)toRingHom_comp_algebraMap`) are used as black-box rewrites that keep
`congrIdeal` opaque. -/
theorem annulusChartTransition_comp_awayCompletionHom (hI : I.FG) :
    ((AdicCompletion.congrIdeal (annulusChart_locIdeal_eq R I q)).symm.toRingHom.comp
          ((annulusOverlapTransitionInv R I q hI).comp
            (AdicCompletion.congrIdeal (annulusChartY_locIdeal_eq R I q)).toRingHom)).comp
        ((awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)).comp
          (algebraMap R (annulusAlgebra R I q))) =
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)).comp
        (algebraMap R (annulusAlgebra R I q)) := by
  -- The transition composite, precomposed with `annulusLocY → A{1/y}`, equals `annulusLoc → A{1/x}`
  -- precomposed with the inverse coordinate swap. Pure `RingHom.comp` rewrites, congrIdeal opaque.
  have hcore : ((AdicCompletion.congrIdeal (annulusChart_locIdeal_eq R I q)).symm.toRingHom.comp
            ((annulusOverlapTransitionInv R I q hI).comp
              (AdicCompletion.congrIdeal (annulusChartY_locIdeal_eq R I q)).toRingHom)).comp
          (algebraMap (annulusLocY R I q)
            (awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q))) =
        (algebraMap (annulusLoc R I q)
            (awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q))).comp
          ((annulusLocTransition R I q hI).symm : annulusLocY R I q →+* annulusLoc R I q) := by
    rw [RingHom.comp_assoc, RingHom.comp_assoc,
      AdicCompletion.congrIdeal_toRingHom_comp_algebraMap (annulusChartY_locIdeal_eq R I q),
      annulusOverlapTransitionInv_comp_algebraMap_locY R I q hI, ← RingHom.comp_assoc,
      AdicCompletion.congrIdeal_symm_toRingHom_comp_algebraMap (annulusChart_locIdeal_eq R I q)]
  -- `awayCompletionHom … ∘ (R → A)` collapses to `(annulusLoc/Y → A{1/·}) ∘ (R → annulusLoc/Y)`.
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
  rw [hL, hCY, ← RingHom.comp_assoc, hcore, RingHom.comp_assoc,
    annulusLocTransition_symm_comp_algebraMap R I q hI]

set_option synthInstance.maxHeartbeats 400000 in
-- Collapsing both sides to a single `locallyRingedSpaceMap` resolves algebra/`IsScalarTower`
-- instances through the nested `AdicCompletion` towers, which is slow.
set_option maxHeartbeats 1600000 in
-- Correspondingly the elaboration heartbeat budget must be raised for those rewrites.
/-- **The geometric adjacent-overlap crux (forward step).** On the `x`-overlap `Spf A{1/x}`, the
open-immersion chart followed by the structural morphism agrees with the chart transition
`Spf A{1/x} ≅ Spf A{1/y}` followed by the `y`-chart and the structural morphism. This is the
morphism-level shadow of `annulusChartTransition_comp_awayCompletionHom`: both sides collapse to a
single `locallyRingedSpaceMap` and match by `locallyRingedSpaceMap_congr` fed by that ring
identity. -/
theorem annulusOverlapChart_comp_structMap [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
    (hI : I.FG) :
    annulusOverlapChart R I q ≫ annulusStructMap R I q hI =
      (annulusChartTransitionSpf R I q hI).hom ≫
        annulusOverlapChartY R I q ≫ annulusStructMap R I q hI := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  -- Continuity witnesses for each pairwise collapse of the RHS composite `m₁ ≫ m₂ ≫ m₃ ≫ m₄ ≫ m₅`
  -- into a single `locallyRingedSpaceMap`, built from the piecewise continuities.
  have hA := le_comap_comp (algebraMap R (annulusAlgebra R I q))
    (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q))
    (Ideal.map_le_iff_le_comap.mp (annulus_map_eq R I q).le)
    (le_comap_awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q))
  have hB := le_comap_comp _ _ hA
    (FormalSpectrum.le_comap_congrIdeal (annulusChartY_locIdeal_eq R I q))
  have hC := le_comap_comp _ _ hB
    (annulusOverlapTransition_symm_isAdicHom R I q hI).le_comap
  have hD := le_comap_comp _ _ hC
    (FormalSpectrum.le_comap_congrIdeal_symm (annulusChart_locIdeal_eq R I q))
  have hL0 := le_comap_comp (algebraMap R (annulusAlgebra R I q))
    (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q))
    (Ideal.map_le_iff_le_comap.mp (annulus_map_eq R I q).le)
    (le_comap_awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q))
  rw [annulusOverlapChart, annulusStructMap, IsTopologicallyFiniteType.structMap,
    FormalSpectrum.basicOpenChart, ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hL0)]
  rw [annulusChartTransitionSpf, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    annulusChartDomainSpfX, annulusChartDomainSpfY,
    FormalSpectrum.spfCongrIdeal_hom_eq, FormalSpectrum.spfCongrIdeal_inv_eq,
    annulusOverlapTransitionSpf_hom_eq,
    annulusOverlapChartY, FormalSpectrum.basicOpenChart,
    Category.assoc, Category.assoc,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hA),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hB),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hC),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hD)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (by rw [← annulusChartTransition_comp_awayCompletionHom R I q hI,
        RingHom.comp_assoc, RingHom.comp_assoc])

/-- **The geometric adjacent-overlap crux (backward step)**, obtained from the forward crux by
pre-composing with the inverse transition. -/
theorem annulusOverlapChartY_comp_structMap [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
    (hI : I.FG) :
    annulusOverlapChartY R I q ≫ annulusStructMap R I q hI =
      (annulusChartTransitionSpf R I q hI).inv ≫
        annulusOverlapChart R I q ≫ annulusStructMap R I q hI := by
  rw [annulusOverlapChart_comp_structMap R I q hI, Iso.inv_hom_id_assoc]

/-- **The glued structural morphism of the formal Tate chain** `T ⟶ Spf R`, assembled from the
per-patch structural morphisms `annulusStructMap : Spf A ⟶ Spf R` via `glueMorphisms`. The overlap
compatibility is verified by casing on the index difference: on the diagonal both sides collapse to
`annulusStructMap`; on non-adjacent overlaps the source is the empty (initial) locally ringed space,
so any two maps out of it agree; on adjacent overlaps it is the geometric crux
`annulusOverlapChart_comp_structMap` (forward) / `annulusOverlapChartY_comp_structMap`
(backward). -/
def tateChainStructMap [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
    (hq : q ∈ I) (hI : I.FG) :
    (tateChain R I q hq hI).toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  (tateChainFormalGlueData R I q hq hI).glueMorphisms (fun _ => annulusStructMap R I q hI) (by
    intro i j
    by_cases hij : i = j
    · -- diagonal: `t i i = 𝟙`, so both sides collapse to `f i i ≫ annulusStructMap`.
      subst hij
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · -- off-diagonal: unfold the `GlueData.ofGlueData'` `if`-forms into `tateF`/`tateT`. The dite
      -- conditions live at `ULift ℤ`, so re-type the disequalities before rewriting.
      have hij' : ¬ @Eq (ULift.{u} ℤ) i j := hij
      have hji' : ¬ @Eq (ULift.{u} ℤ) j i := fun h => hij h.symm
      simp only [tateChainFormalGlueData, tateChainLRSGlueData, tateChainGlueData',
        CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij',
        dif_neg hji', Category.assoc]
      -- Clean goal: `tateF i j ≫ s = tateT i j ≫ tateF j i ≫ s`, all out of `tateV i j`.
      by_cases h1 : j.down - i.down = 1
      · -- forward step `d = 1`: reduce to the forward crux.
        rw [tateF_forward R I q h1, tateT, dif_pos h1,
          tateF_backward R I q (show i.down - j.down = -1 by omega)]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [annulusOverlapChart_comp_structMap R I q hI]
      · by_cases h2 : j.down - i.down = -1
        · -- backward step `d = -1`: reduce to the backward crux.
          rw [tateF_backward R I q h2, tateT, dif_neg h1, dif_pos h2,
            tateF_forward R I q (show i.down - j.down = 1 by omega)]
          simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          rw [annulusOverlapChartY_comp_structMap R I q hI]
        · -- far step `|d| ≥ 2`: the source `tateV i j` is empty (initial).
          haveI : IsEmpty (tateV R I q i j) := (tateV_far R I q h1 h2) ▸ inferInstance
          simp only [eqToHom_trans_assoc]
          congr 1
          exact (LocallyRingedSpace.isInitialOfIsEmpty (X := tateV R I q i j)).hom_ext _ _)

end AlgebraicGeometry
