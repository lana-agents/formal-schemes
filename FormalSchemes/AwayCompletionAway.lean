import FormalSchemes.BasicOpenChart
import Mathlib.RingTheory.Localization.Away.Basic

set_option linter.style.header false

/-!
# Transitivity of the completed localization along `D(g) ⊆ D(f)`

Let `R` be a commutative ring, `I : Ideal R`, and `f g : R` with `D(g) ⊆ D(f)` — encoded as the
hypothesis that `f` becomes a unit in `R_g = Localization.Away g`. Geometrically `D(g)` is then a
basic open contained in `D(f)`, so on the affine basic-open chart `Spf R{1/f} ↪ Spf R`
(`FormalSchemes/BasicOpenChart.lean`) the smaller chart `Spf R{1/g}` factors through it. At the
level of the completed localizations this is the ring isomorphism

```
R{1/g}  ≃+*  R_f{1/ḡ}
```

where `ḡ = algebraMap R R_f g` and `R_f{1/ḡ} := AdicCompletion ((I·R_f)·(R_f)_ḡ) ((R_f)_ḡ)` is the
completed localization of `R_f = Localization.Away f` away from `ḡ`. The isomorphism is the
completed-localization avatar of the elementary localization transitivity
`R_g ≅ (R_f)_ḡ` (both are localizations of `R` at the powers of `f·g`, since `f` is already a unit
in `R_g`), pushed through the completion functor `AdicCompletion.mapCompletion`.

This is the algebraic bridge underlying the identification of the structure-sheaf sections of
`Spf R` on `D(g)` with those of the chart `Spf R{1/f}` on the corresponding basic open — the
reusable step towards upgrading `basicOpenChart` to a `LocallyRingedSpace.IsOpenImmersion`
(issue 163). The remaining gap to the stalk comparison (relating the completion of the
*localization* `R_f{1/ḡ}` to the localization of the *completion* `(R{1/f})_ḡ`) is the
completion-localization interchange and is left as follow-up.

## Main definitions and results

* `FormalSpectrum.awayAwayLocEquiv`: the localization transitivity `R_g ≃ₐ[R] (R_f)_ḡ` on
  `D(g) ⊆ D(f)`.
* `FormalSpectrum.awayCompletionAwayEquiv`: its completion, `R{1/g} ≃+* R_f{1/ḡ}`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4).
* Mathlib `IsLocalization.Away.mul`, `AlgebraicGeometry.basicOpenIsoSpecAway`.
-/

noncomputable section

open TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f g : R)

/-- **Localization transitivity on `D(g) ⊆ D(f)`.** When `f` is a unit in `R_g = Localization.Away
g` (i.e. `D(g) ⊆ D(f)`), the localization `R_g` is the localization of `R_f = Localization.Away f`
away from the image `ḡ = algebraMap R R_f g`: both are localizations of `R` at the powers of
`f·g`. -/
def awayAwayLocEquiv (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    Localization.Away g ≃ₐ[R]
      Localization.Away (algebraMap R (Localization.Away f) g) :=
  haveI : IsLocalization.Away (f * g) (Localization.Away g) :=
    IsLocalization.Away.mul_of_isUnit' f g hfg
  IsLocalization.algEquiv (Submonoid.powers (f * g)) _ _

/-- The image ideal `KC := (I·R_f)·(R_f)_ḡ` of the completed-localization transitivity equals
`I·(R_f)_ḡ` (via the scalar tower `R → R_f → (R_f)_ḡ`). -/
theorem map_algebraMap_localizationAway_eq :
    (I.map (algebraMap R (Localization.Away f))).map
        (algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R (Localization.Away f) g))) =
      I.map (algebraMap R (Localization.Away (algebraMap R (Localization.Away f) g))) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- The localization transitivity equiv carries `algebraMap R R_g` to `algebraMap R (R_f)_ḡ`. -/
theorem awayAwayLocEquiv_comp_algebraMap
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom.comp
        (algebraMap R (Localization.Away g)) =
      algebraMap R (Localization.Away (algebraMap R (Localization.Away f) g)) := by
  ext r
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_ringEquiv,
    RingHom.coe_coe]
  exact (awayAwayLocEquiv f g hfg).commutes r

/-- `I·R_g` is carried onto `I·(R_f)_ḡ` by the localization transitivity equiv. -/
theorem map_awayAwayLocEquiv (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    (I.map (algebraMap R (Localization.Away g))).map
        (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom =
      I.map (algebraMap R (Localization.Away (algebraMap R (Localization.Away f) g))) := by
  rw [Ideal.map_map, awayAwayLocEquiv_comp_algebraMap]

/-- The inverse localization transitivity equiv carries `algebraMap R (R_f)_ḡ` back to
`algebraMap R R_g`. -/
theorem awayAwayLocEquiv_symm_comp_algebraMap
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    (awayAwayLocEquiv f g hfg).symm.toRingEquiv.toRingHom.comp
        (algebraMap R (Localization.Away (algebraMap R (Localization.Away f) g))) =
      algebraMap R (Localization.Away g) := by
  ext r
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_ringEquiv,
    RingHom.coe_coe]
  exact (awayAwayLocEquiv f g hfg).symm.commutes r

/-- `I·(R_f)_ḡ` is carried back onto `I·R_g` by the inverse localization transitivity equiv. -/
theorem map_awayAwayLocEquiv_symm (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    (I.map (algebraMap R (Localization.Away (algebraMap R (Localization.Away f) g)))).map
        (awayAwayLocEquiv f g hfg).symm.toRingEquiv.toRingHom =
      I.map (algebraMap R (Localization.Away g)) := by
  rw [Ideal.map_map, awayAwayLocEquiv_symm_comp_algebraMap]

set_option maxHeartbeats 400000 in
-- the kernel type-checks a nested tower of localization/completion instances, which is costly
/-- **Transitivity of the completed localization on `D(g) ⊆ D(f)`**: the ring isomorphism
`R{1/g} ≃+* R_f{1/ḡ}`, obtained by completing the localization transitivity
`awayAwayLocEquiv`. -/
def awayCompletionAwayEquiv (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    awayCompletion I g ≃+*
      awayCompletion (I.map (algebraMap R (Localization.Away f)))
        (algebraMap R (Localization.Away f) g) := by
  -- the localization transitivity equiv and its underlying ring maps
  let e := awayAwayLocEquiv f g hfg
  let φ := e.toRingEquiv.toRingHom
  let ψ := e.symm.toRingEquiv.toRingHom
  -- the two ideals of definition (`I·R_g` and `KC = (I·R_f)·(R_f)_ḡ`)
  let Kg : Ideal (Localization.Away g) := I.map (algebraMap R (Localization.Away g))
  let KC : Ideal (Localization.Away (algebraMap R (Localization.Away f) g)) :=
    (I.map (algebraMap R (Localization.Away f))).map
      (algebraMap (Localization.Away f)
        (Localization.Away (algebraMap R (Localization.Away f) g)))
  -- finite generation of both
  have hKgFG : Kg.FG := hI.map _
  have hKCFG : KC.FG := (hI.map _).map _
  -- the two ideal-comparison inequalities: `φ` sends `Kg` onto `KC` and `ψ` sends it back
  have hA : Kg.map φ ≤ KC :=
    le_of_eq ((map_awayAwayLocEquiv I f g hfg).trans
      (map_algebraMap_localizationAway_eq I f g).symm)
  have hB : KC.map ψ ≤ Kg :=
    le_of_eq ((congrArg (Ideal.map ψ) (map_algebraMap_localizationAway_eq I f g)).trans
      (map_awayAwayLocEquiv_symm I f g hfg))
  -- both completions are adically complete
  haveI : IsAdicComplete (AdicCompletion.idealOfDefinition Kg)
      (AdicCompletion Kg (Localization.Away g)) :=
    (AdicCompletion.isAdicRing_map _ hKgFG).toIsAdicComplete
  haveI : IsAdicComplete (AdicCompletion.idealOfDefinition KC)
      (AdicCompletion KC (Localization.Away (algebraMap R (Localization.Away f) g))) :=
    (AdicCompletion.isAdicRing_map _ hKCFG).toIsAdicComplete
  -- the completed maps, in both directions
  refine RingEquiv.ofRingHom
    (AdicCompletion.mapCompletion φ hA hKCFG)
    (AdicCompletion.mapCompletion ψ hB hKgFG) ?_ ?_
  · -- `F ∘ G = id` on the `(R_f)_ḡ`-completion
    refine AdicCompletion.hom_ext_of_continuous KC (AdicCompletion.idealOfDefinition KC) hKCFG
      (fun m x hx => ?_)
      (fun m x hx => (AdicCompletion.mem_idealOfDefinition_pow_iff m x).mpr hx) (fun c => ?_)
    · have h1 := AdicCompletion.mapCompletion_mem_pow ψ hB hKgFG hKCFG m hx
      rw [AdicCompletion.mem_idealOfDefinition_pow_iff] at h1
      exact AdicCompletion.mapCompletion_mem_pow φ hA hKCFG hKgFG m h1
    · rw [RingHom.comp_apply, AdicCompletion.mapCompletion_of,
        AdicCompletion.mapCompletion_algebraMap]
      have hφψ : φ (ψ c) = c := by
        simp only [φ, ψ, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_ringEquiv, RingHom.coe_coe,
          AlgEquiv.apply_symm_apply]
      rw [hφψ, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        RingHom.id_apply]
  · -- `G ∘ F = id` on the `R_g`-completion
    refine AdicCompletion.hom_ext_of_continuous Kg (AdicCompletion.idealOfDefinition Kg) hKgFG
      (fun m x hx => ?_)
      (fun m x hx => (AdicCompletion.mem_idealOfDefinition_pow_iff m x).mpr hx) (fun r => ?_)
    · have h1 := AdicCompletion.mapCompletion_mem_pow φ hA hKCFG hKgFG m hx
      rw [AdicCompletion.mem_idealOfDefinition_pow_iff] at h1
      exact AdicCompletion.mapCompletion_mem_pow ψ hB hKgFG hKCFG m h1
    · rw [RingHom.comp_apply, AdicCompletion.mapCompletion_of,
        AdicCompletion.mapCompletion_algebraMap]
      have hψφ : ψ (φ r) = r := by
        simp only [φ, ψ, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_ringEquiv, RingHom.coe_coe,
          AlgEquiv.symm_apply_apply]
      rw [hψφ, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        RingHom.id_apply]

end FormalSpectrum
