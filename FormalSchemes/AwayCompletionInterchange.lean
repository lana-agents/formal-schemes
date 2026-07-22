import FormalSchemes.AwayCompletionAway

set_option linter.style.header false

/-!
# The completion–localization interchange for a basic-open chart

Let `B` be a commutative ring with a finitely generated ideal `K` and let `t : B`. Write
`B_t = Localization.Away t`, `B̂ = AdicCompletion K B` for the `K`-adic completion (with ideal of
definition `K̂ = idealOfDefinition K`), and `t̂ = algebraMap B B̂ t` for the image of `t` in `B̂`.
There are then two ways to build "the completed localization of `B` at `t` along `V(K)`":

* complete the localization: `AdicCompletion (K·B_t) B_t`;
* localize the completion and complete again: `AdicCompletion (K̂·B̂_{t̂}) B̂_{t̂}`.

These are canonically isomorphic (`AdicCompletion.awayCompletionInterchange`). Completion does not
change the infinitesimal thickenings (`AdicCompletion.quotientEquivPow`), so the two towers
`B_t ⧸ (K·B_t)ⁿ` and `B̂_{t̂} ⧸ (K̂·B̂_{t̂})ⁿ` agree; concretely we build the isomorphism from
the functorial completion map `AdicCompletion.mapCompletion` (forward, from the localization
transitivity `B_t → B̂_{t̂}`) and the continuous-extension engine `AdicCompletion.extendRingHom`
(backward, extending `B̂ → AdicCompletion (K·B_t) B_t` over the localization `B̂_{t̂}` and then to
its completion), proving the two composites are the identity with
`AdicCompletion.hom_ext_of_continuous`
and the universal property of localization.

Combined with `FormalSpectrum.awayCompletionAwayEquiv` (the localization transitivity
`R{1/g} ≃+* R_f{1/ḡ}` on `D(g) ⊆ D(f)`, `FormalSchemes/AwayCompletionAway.lean`) this identifies the
sections of `O_{Spf R}` on `D(g)` with those of the affine basic-open chart `Spf R{1/f}` on the
corresponding basic open (`FormalSpectrum.awayCompletionChartEquiv`): the `c`-component of the chart
`Spf R{1/f} ↪ Spf R` on basic opens is, under `sectionsBasicOpenEquiv` on both sides, a ring
isomorphism of completed localizations. This is the reusable algebraic heart of the `c_iso`
(open-immersion) route for issue 163.

## Main results

* `AdicCompletion.awayCompletionInterchange`: `AdicCompletion (K·B_t) B_t ≃+*
  AdicCompletion (K̂·B̂_{t̂}) B̂_{t̂}` for `K` finitely generated.
* `FormalSpectrum.awayCompletionChartEquiv`: `R{1/g} ≃+* R{1/f}{1/ḡ}` on `D(g) ⊆ D(f)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4), §10.8.
* Mathlib `AlgebraicGeometry.basicOpenIsoSpecAway`, `SheafedSpace.IsOpenImmersion.of_stalk_iso`.
-/

noncomputable section

open Ideal

universe u

namespace AdicCompletion

variable {B : Type u} [CommRing B] (K : Ideal B) (t : B)

/-- The image `t̂ = algebraMap B B̂ t` of `t` in the completion `B̂ = AdicCompletion K B`. -/
abbrev awayPoint : AdicCompletion K B := algebraMap B (AdicCompletion K B) t

/-- The localization `B̂_{t̂}` of the completion at the image of `t`. -/
abbrev awayCompletionLoc : Type u := Localization.Away (awayPoint K t)

/-- The ideal `K·B_t`, ideal of definition of `AdicCompletion (K·B_t) B_t`. -/
abbrev locIdeal : Ideal (Localization.Away t) := K.map (algebraMap B (Localization.Away t))

/-- The ideal `K̂·B̂_{t̂}`, ideal of definition of `AdicCompletion (K̂·B̂_{t̂}) B̂_{t̂}`. -/
abbrev completionLocIdeal : Ideal (awayCompletionLoc K t) :=
  (idealOfDefinition K).map (algebraMap (AdicCompletion K B) (awayCompletionLoc K t))

theorem locIdeal_fg (hK : K.FG) : (locIdeal K t).FG := hK.map _

theorem completionLocIdeal_fg (hK : K.FG) : (completionLocIdeal K t).FG := (hK.map _).map _

/-- The base ring homomorphism `B → B̂_{t̂}` (complete, then localize). -/
def toLocCompletion : B →+* awayCompletionLoc K t :=
  (algebraMap (AdicCompletion K B) (awayCompletionLoc K t)).comp
    (algebraMap B (AdicCompletion K B))

theorem toLocCompletion_apply (b : B) :
    toLocCompletion K t b =
      algebraMap (AdicCompletion K B) (awayCompletionLoc K t)
        (algebraMap B (AdicCompletion K B) b) :=
  rfl

theorem isUnit_toLocCompletion_t : IsUnit (toLocCompletion K t t) := by
  rw [toLocCompletion_apply]
  exact IsLocalization.Away.algebraMap_isUnit (awayPoint K t)

/-- **Localization transitivity `B_t → B̂_{t̂}`.** Since `t` maps to a unit `t̂` of `B̂_{t̂}`, the
map `B → B̂_{t̂}` factors through the localization `B_t = Localization.Away t`. -/
def locTransition : Localization.Away t →+* awayCompletionLoc K t :=
  IsLocalization.Away.lift (g := toLocCompletion K t) t (isUnit_toLocCompletion_t K t)

theorem locTransition_comp_algebraMap :
    (locTransition K t).comp (algebraMap B (Localization.Away t)) = toLocCompletion K t :=
  IsLocalization.Away.lift_comp t (isUnit_toLocCompletion_t K t)

theorem locTransition_algebraMap (b : B) :
    locTransition K t (algebraMap B (Localization.Away t) b) = toLocCompletion K t b :=
  IsLocalization.Away.lift_eq t (isUnit_toLocCompletion_t K t) b

/-- The completion map `K·B_t = (locIdeal K t)` transports along `locTransition` onto
`K̂·B̂_{t̂} = completionLocIdeal K t`. -/
theorem map_locTransition :
    (locIdeal K t).map (locTransition K t) = completionLocIdeal K t := by
  rw [locIdeal, Ideal.map_map, locTransition_comp_algebraMap, toLocCompletion,
    ← Ideal.map_map]

/-- Conversion between the completion structure map (`algebraMap`) and `AdicCompletion.of`. -/
private theorem algebraMap_completion_eq_of {A : Type u} [CommRing A] (J : Ideal A) (a : A) :
    algebraMap A (AdicCompletion J A) a = AdicCompletion.of J A a := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- The completion map `B̂ = AdicCompletion K B → AdicCompletion (K·B_t) B_t` induced by the
localization `B → B_t`. -/
def completionToLocCompletion (hK : K.FG) :
    AdicCompletion K B →+* AdicCompletion (locIdeal K t) (Localization.Away t) :=
  mapCompletion (algebraMap B (Localization.Away t)) (le_of_eq rfl) (locIdeal_fg K t hK)

theorem completionToLocCompletion_comp_algebraMap (hK : K.FG) :
    (completionToLocCompletion K t hK).comp (algebraMap B (AdicCompletion K B)) =
      (algebraMap (Localization.Away t) (AdicCompletion (locIdeal K t) (Localization.Away t))).comp
        (algebraMap B (Localization.Away t)) :=
  mapCompletion_comp_algebraMap _ _ _

theorem isUnit_completionToLocCompletion_awayPoint (hK : K.FG) :
    IsUnit (completionToLocCompletion K t hK (awayPoint K t)) := by
  rw [completionToLocCompletion, awayPoint, mapCompletion_algebraMap]
  exact (IsLocalization.Away.algebraMap_isUnit t).map _

/-- The localization `B̂_{t̂} → AdicCompletion (K·B_t) B_t` extending `completionToLocCompletion`
(possible since `t̂` maps to a unit). -/
def locCompletionLift (hK : K.FG) :
    awayCompletionLoc K t →+* AdicCompletion (locIdeal K t) (Localization.Away t) :=
  IsLocalization.Away.lift (g := completionToLocCompletion K t hK) (awayPoint K t)
    (isUnit_completionToLocCompletion_awayPoint K t hK)

theorem locCompletionLift_comp_algebraMap (hK : K.FG) :
    (locCompletionLift K t hK).comp
        (algebraMap (AdicCompletion K B) (awayCompletionLoc K t)) =
      completionToLocCompletion K t hK :=
  IsLocalization.Away.lift_comp (awayPoint K t)
    (isUnit_completionToLocCompletion_awayPoint K t hK)

/-- `locCompletionLift` transports `K̂·B̂_{t̂} = completionLocIdeal K t` into the ideal of
definition of `AdicCompletion (K·B_t) B_t`. -/
theorem map_locCompletionLift (hK : K.FG) :
    (completionLocIdeal K t).map (locCompletionLift K t hK) ≤
      idealOfDefinition (locIdeal K t) := by
  refine le_of_eq ?_
  have h1 : (completionLocIdeal K t).map (locCompletionLift K t hK) =
      (idealOfDefinition K).map (completionToLocCompletion K t hK) := by
    simp only [completionLocIdeal]
    rw [Ideal.map_map, locCompletionLift_comp_algebraMap]
  have h2 : (idealOfDefinition K).map (completionToLocCompletion K t hK) =
      idealOfDefinition (locIdeal K t) := by
    simp only [idealOfDefinition, locIdeal]
    rw [Ideal.map_map, completionToLocCompletion_comp_algebraMap, ← Ideal.map_map]
  rw [h1, h2]

/-- Continuity of `locCompletionLift` (the `hψ` hypothesis of `extendRingHom`). -/
theorem locCompletionLift_continuous (hK : K.FG) (m : ℕ) :
    (completionLocIdeal K t) ^ m ≤
      ((idealOfDefinition (locIdeal K t)) ^ m).comap (locCompletionLift K t hK) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (map_locCompletionLift K t hK) m

/-- **The forward map of the interchange**: `AdicCompletion (K·B_t) B_t →+*
AdicCompletion (K̂·B̂_{t̂}) B̂_{t̂}`, the completion of the localization transitivity. -/
def interchangeForward (hK : K.FG) :
    AdicCompletion (locIdeal K t) (Localization.Away t) →+*
      AdicCompletion (completionLocIdeal K t) (awayCompletionLoc K t) :=
  mapCompletion (locTransition K t) (map_locTransition K t).le (completionLocIdeal_fg K t hK)

/-- **The backward map of the interchange**: `AdicCompletion (K̂·B̂_{t̂}) B̂_{t̂} →+*
AdicCompletion (K·B_t) B_t`, the continuous extension of `locCompletionLift`. -/
def interchangeBackward (hK : K.FG) :
    AdicCompletion (completionLocIdeal K t) (awayCompletionLoc K t) →+*
      AdicCompletion (locIdeal K t) (Localization.Away t) :=
  haveI : IsAdicComplete (idealOfDefinition (locIdeal K t))
      (AdicCompletion (locIdeal K t) (Localization.Away t)) :=
    (isAdicRing_map (locIdeal K t) (locIdeal_fg K t hK)).toIsAdicComplete
  extendRingHom (completionLocIdeal K t) (idealOfDefinition (locIdeal K t))
    (locCompletionLift K t hK) (locCompletionLift_continuous K t hK)

theorem interchangeForward_of (hK : K.FG) (b : Localization.Away t) :
    interchangeForward K t hK (AdicCompletion.of (locIdeal K t) (Localization.Away t) b) =
      algebraMap (awayCompletionLoc K t)
        (AdicCompletion (completionLocIdeal K t) (awayCompletionLoc K t)) (locTransition K t b) :=
  mapCompletion_of _ _ _ _

theorem interchangeForward_algebraMap (hK : K.FG) (x : Localization.Away t) :
    interchangeForward K t hK
        (algebraMap (Localization.Away t)
          (AdicCompletion (locIdeal K t) (Localization.Away t)) x) =
      algebraMap (awayCompletionLoc K t)
        (AdicCompletion (completionLocIdeal K t) (awayCompletionLoc K t)) (locTransition K t x) :=
  mapCompletion_algebraMap _ _ _ _

theorem completionToLocCompletion_of (hK : K.FG) (b : B) :
    completionToLocCompletion K t hK (AdicCompletion.of K B b) =
      algebraMap (Localization.Away t) (AdicCompletion (locIdeal K t) (Localization.Away t))
        (algebraMap B (Localization.Away t) b) :=
  mapCompletion_of _ _ _ _

theorem interchangeBackward_of (hK : K.FG) (y : awayCompletionLoc K t) :
    interchangeBackward K t hK
        (AdicCompletion.of (completionLocIdeal K t) (awayCompletionLoc K t) y) =
      locCompletionLift K t hK y := by
  haveI : IsAdicComplete (idealOfDefinition (locIdeal K t))
      (AdicCompletion (locIdeal K t) (Localization.Away t)) :=
    (isAdicRing_map (locIdeal K t) (locIdeal_fg K t hK)).toIsAdicComplete
  exact extendRingHom_of _ _ _ _ y

/-- `interchangeBackward ∘ interchangeForward = id`, from the universal property of `B_t`. -/
theorem interchangeBackward_comp_interchangeForward (hK : K.FG) :
    (interchangeBackward K t hK).comp (interchangeForward K t hK) =
      RingHom.id (AdicCompletion (locIdeal K t) (Localization.Away t)) := by
  haveI : IsAdicComplete (idealOfDefinition (locIdeal K t))
      (AdicCompletion (locIdeal K t) (Localization.Away t)) :=
    (isAdicRing_map (locIdeal K t) (locIdeal_fg K t hK)).toIsAdicComplete
  -- key: `locCompletionLift ∘ locTransition = algebraMap B_t (completion)`
  have key : (locCompletionLift K t hK).comp (locTransition K t) =
      algebraMap (Localization.Away t)
        (AdicCompletion (locIdeal K t) (Localization.Away t)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers t) ?_
    rw [RingHom.comp_assoc, locTransition_comp_algebraMap, toLocCompletion, ← RingHom.comp_assoc,
      locCompletionLift_comp_algebraMap, completionToLocCompletion_comp_algebraMap]
  refine hom_ext_of_continuous (locIdeal K t) (idealOfDefinition (locIdeal K t))
    (locIdeal_fg K t hK) (fun m x hx => ?_)
    (fun m x hx => (mem_idealOfDefinition_pow_iff m x).mpr hx) (fun b => ?_)
  · -- continuity of the composite
    have h1 : interchangeForward K t hK x ∈ (idealOfDefinition (completionLocIdeal K t)) ^ m :=
      mapCompletion_mem_pow (locTransition K t) (map_locTransition K t).le
        (completionLocIdeal_fg K t hK) (locIdeal_fg K t hK) m hx
    rw [mem_idealOfDefinition_pow_iff] at h1
    exact extendRingHom_continuous (completionLocIdeal K t) (idealOfDefinition (locIdeal K t))
      (locCompletionLift K t hK) (locCompletionLift_continuous K t hK)
      (completionLocIdeal_fg K t hK) m (interchangeForward K t hK x) h1
  · -- agreement on the dense subring
    rw [RingHom.comp_apply, RingHom.id_apply, interchangeForward_of, algebraMap_completion_eq_of,
      interchangeBackward_of, ← RingHom.comp_apply, key, algebraMap_completion_eq_of]

/-- `interchangeForward ∘ interchangeBackward = id`. -/
theorem interchangeForward_comp_interchangeBackward (hK : K.FG) :
    (interchangeForward K t hK).comp (interchangeBackward K t hK) =
      RingHom.id (AdicCompletion (completionLocIdeal K t) (awayCompletionLoc K t)) := by
  haveI : IsAdicComplete (idealOfDefinition (locIdeal K t))
      (AdicCompletion (locIdeal K t) (Localization.Away t)) :=
    (isAdicRing_map (locIdeal K t) (locIdeal_fg K t hK)).toIsAdicComplete
  haveI : IsAdicComplete (idealOfDefinition (completionLocIdeal K t))
      (AdicCompletion (completionLocIdeal K t) (awayCompletionLoc K t)) :=
    (isAdicRing_map (completionLocIdeal K t) (completionLocIdeal_fg K t hK)).toIsAdicComplete
  -- key: `interchangeForward ∘ locCompletionLift = algebraMap` on `B̂_{t̂}`
  have key : (interchangeForward K t hK).comp (locCompletionLift K t hK) =
      algebraMap (awayCompletionLoc K t)
        (AdicCompletion (completionLocIdeal K t) (awayCompletionLoc K t)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (awayPoint K t)) ?_
    rw [RingHom.comp_assoc, locCompletionLift_comp_algebraMap]
    -- goal: interchangeForward ∘ completionToLocCompletion = algebraMap ∘ (algebraMap B̂ B̂ₜ)
    refine hom_ext_of_continuous K (idealOfDefinition (completionLocIdeal K t)) hK
      (fun m x hx => ?_) (fun m x hx => ?_) (fun b => ?_)
    · -- continuity of the left composite
      have h1 : completionToLocCompletion K t hK x ∈ (idealOfDefinition (locIdeal K t)) ^ m :=
        mapCompletion_mem_pow (algebraMap B (Localization.Away t)) (le_of_eq rfl)
          (locIdeal_fg K t hK) hK m hx
      rw [mem_idealOfDefinition_pow_iff] at h1
      exact mapCompletion_mem_pow (locTransition K t) (map_locTransition K t).le
        (completionLocIdeal_fg K t hK) (locIdeal_fg K t hK) m h1
    · -- continuity of `algebraMap.comp (algebraMap B̂ B̂_{t̂})`
      rw [RingHom.comp_apply]
      have hx' : x ∈ (idealOfDefinition K) ^ m := (mem_idealOfDefinition_pow_iff m x).mpr hx
      have hstep1 : algebraMap (AdicCompletion K B) (awayCompletionLoc K t) x ∈
          (completionLocIdeal K t) ^ m := by
        have h := Ideal.mem_map_of_mem
          (algebraMap (AdicCompletion K B) (awayCompletionLoc K t)) hx'
        rwa [Ideal.map_pow] at h
      have hstep2 := Ideal.mem_map_of_mem
        (algebraMap (awayCompletionLoc K t)
          (AdicCompletion (completionLocIdeal K t) (awayCompletionLoc K t))) hstep1
      rwa [Ideal.map_pow] at hstep2
    · -- agreement on the dense subring of `B̂`
      rw [RingHom.comp_apply, RingHom.comp_apply, completionToLocCompletion_of,
        interchangeForward_algebraMap, locTransition_algebraMap, toLocCompletion_apply,
        ← algebraMap_completion_eq_of]
  refine hom_ext_of_continuous (completionLocIdeal K t)
    (idealOfDefinition (completionLocIdeal K t)) (completionLocIdeal_fg K t hK)
    (fun m x hx => ?_) (fun m x hx => (mem_idealOfDefinition_pow_iff m x).mpr hx) (fun z => ?_)
  · -- continuity of the composite
    have h1 : interchangeBackward K t hK x ∈ (idealOfDefinition (locIdeal K t)) ^ m :=
      extendRingHom_continuous (completionLocIdeal K t) (idealOfDefinition (locIdeal K t))
        (locCompletionLift K t hK) (locCompletionLift_continuous K t hK)
        (completionLocIdeal_fg K t hK) m x hx
    rw [mem_idealOfDefinition_pow_iff] at h1
    exact mapCompletion_mem_pow (locTransition K t) (map_locTransition K t).le
      (completionLocIdeal_fg K t hK) (locIdeal_fg K t hK) m h1
  · -- agreement on the dense subring of `B̂_{t̂}`
    rw [RingHom.comp_apply, RingHom.id_apply, interchangeBackward_of, ← RingHom.comp_apply, key,
      algebraMap_completion_eq_of]

/-- **The completion–localization interchange.** For a finitely generated ideal `K` of `B` and
`t : B`, completing the localization `B_t` agrees with localizing the completion `B̂` at `t̂` and
completing again:
`AdicCompletion (K·B_t) B_t ≃+* AdicCompletion (K̂·B̂_{t̂}) B̂_{t̂}`. -/
def awayCompletionInterchange (hK : K.FG) :
    AdicCompletion (locIdeal K t) (Localization.Away t) ≃+*
      AdicCompletion (completionLocIdeal K t) (awayCompletionLoc K t) :=
  RingEquiv.ofRingHom (interchangeForward K t hK) (interchangeBackward K t hK)
    (interchangeForward_comp_interchangeBackward K t hK)
    (interchangeBackward_comp_interchangeForward K t hK)

end AdicCompletion

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f g : R)

/-- **Sections of the basic-open chart agree on `D(g) ⊆ D(f)`.** For `D(g) ⊆ D(f)` (encoded by
`f` being a unit in `R_g`), the completed localization `R{1/g}` — the sections of `O_{Spf R}` on
`D(g)` — is isomorphic to the completed localization `R{1/f}{1/ḡ}` — the sections of the affine
basic-open chart `Spf R{1/f}` on the corresponding basic open. This composes the localization
transitivity `awayCompletionAwayEquiv` (`R{1/g} ≃ R_f{1/ḡ}`) with the completion–localization
interchange (`R_f{1/ḡ} ≃ R{1/f}{1/ḡ}`), and is the ring-level `c`-component of the chart on basic
opens (the algebraic heart of the `c_iso` open-immersion route, issue 163). -/
def awayCompletionChartEquiv (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    awayCompletion I g ≃+*
      awayCompletion (awayCompletionIdeal I f) (awayCompletionHom I f g) :=
  (awayCompletionAwayEquiv I f g hI hfg).trans
    (AdicCompletion.awayCompletionInterchange
      (I.map (algebraMap R (Localization.Away f))) (algebraMap R (Localization.Away f) g)
      (hI.map _))

end FormalSpectrum
