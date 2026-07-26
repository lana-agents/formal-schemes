import FormalSchemes.SpfGammaSheafComponentArbOf

set_option linter.style.header false

/-!
# Continuity of an arbitrary morphism's basic-open component (closing step (b) of EGA I 10.4.6)

For adic rings `(R, I)`, `(S, J)` and an arbitrary morphism of formal spectra
`f : Spf S ⟶ Spf R` whose global-sections map `φ = globalSectionsMap I J f` is continuous
(`hφ : I ≤ J.comap φ`), the conjugated basic-open component `arbSheafComponent I J f g`
(`FormalSchemes/SpfGammaSheafComponentArb.lean`) carries the ideal-of-definition filtration
`(I·R_g)^m • ⊤` into the powers `(J·S_{φ g})^m` of the target ideal of definition. This is the
`hcont` hypothesis isolated by `arbSheafComponent_eq_mapCompletion_of_continuous`
(`FormalSchemes/SpfGammaSheafComponentArbOf.lean`); discharging it closes the arbitrary-morphism
step (b): `arbSheafComponent I J f g = AdicCompletion.mapCompletion (awayMap φ g)`.

## The key observation

An element of `(I·R_g)^m • ⊤` is a *finite `R_g`-linear combination* `Σ aᵢ • yᵢ` whose
coefficients `aᵢ` are honest elements of the ideal `(I·R_g)^m ⊆ R_g` (NOT completion elements),
the `yᵢ` ranging over the whole completion. Since `aᵢ • yᵢ = algebraMap aᵢ * yᵢ`
(`Algebra.smul_def`) and `arbSheafComponent` is pinned on the image of the localization `R_g`
*unconditionally* by the merged `arbSheafComponent_algebraMap`, the component sends the coefficient
`algebraMap aᵢ` to `algebraMap (awayMap φ g aᵢ)`, which — using `hφ` to push `(I·R_g)^m` into
`(J·S_{φ g})^m` — lands in `(awayCompletionIdeal J (φ g))^m`; multiplying by the remaining factor
`arbSheafComponent yᵢ` stays in that ideal. No continuity of the `yᵢ` factors is required — that
was the apparent circularity — so the statement reduces to `Submodule.smul_induction_on` plus
ideal bookkeeping.

## Main results

* `FormalSpectrum.arbSheafComponent_mem_pow`: the `hcont` filtration statement.
* `FormalSpectrum.arbSheafComponent_eq_mapCompletion`: the full arbitrary-morphism identification
  (given continuity `hφ` of the global-sections map), closing step (b).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

/-- **The arbitrary-morphism basic-open component is continuous.**
With `φ = globalSectionsMap f` continuous (`hφ : I ≤ J.comap φ`), the conjugated
`arbSheafComponent I J f g` carries
the ideal-of-definition filtration `(I·R_g)^m • ⊤` into the powers `(J·S_{φ g})^m` of the target
ideal of definition. Proved by `Submodule.smul_induction_on`: on a generator `a • y`
(`a ∈ (I·R_g)^m`), `arbSheafComponent (a • y) = algebraMap (awayMap φ g a) * arbSheafComponent y`
via `Algebra.smul_def`, `map_mul` and `arbSheafComponent_algebraMap`; the first factor lies in
`(awayCompletionIdeal J (φ g))^m` because `awayMap φ g` sends `(I·R_g)^m` into `(J·S_{φ g})^m`
(`awayCompletionIdeal_map_awayMap_le` + `Ideal.map_pow` + `Ideal.pow_right_mono`), and the ideal
absorbs the remaining factor. -/
theorem arbSheafComponent_mem_pow
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (g : R)
    (hφ : I ≤ J.comap (globalSectionsMap I J f))
    (m : ℕ) (x : awayCompletion I g)
    (hx : x ∈ ((I.map (algebraMap R (Localization.Away g))) ^ m • ⊤ :
        Submodule (Localization.Away g) (awayCompletion I g))) :
    arbSheafComponent I J f g x ∈
      (awayCompletionIdeal J (globalSectionsMap I J f g)) ^ m := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · -- Generators `a • y` with `a ∈ (I·R_g)^m` and `y` arbitrary.
    intro a ha y _
    rw [Algebra.smul_def, map_mul, arbSheafComponent_algebraMap I J f g a]
    refine Ideal.mul_mem_right _ _ ?_
    -- `awayMap φ g a` lands in `(J·S_{φ g})^m` since `awayMap φ g` maps `I·R_g` into `J·S_{φ g}`.
    have haL : Localization.awayMap (globalSectionsMap I J f) g a ∈
        (J.map (algebraMap S (Localization.Away (globalSectionsMap I J f g)))) ^ m := by
      have h1 := Ideal.mem_map_of_mem (Localization.awayMap (globalSectionsMap I J f) g) ha
      rw [Ideal.map_pow] at h1
      exact Ideal.pow_right_mono
        (awayCompletionIdeal_map_awayMap_le I J (globalSectionsMap I J f) hφ g) m h1
    -- Pushing through the completion structure map keeps it in the ideal of definition power.
    have h2 := Ideal.mem_map_of_mem
      (algebraMap (Localization.Away (globalSectionsMap I J f g))
        (awayCompletion J (globalSectionsMap I J f g))) haL
    rwa [Ideal.map_pow] at h2
  · -- Additivity.
    intro z w hz hw
    rw [map_add]
    exact Ideal.add_mem _ hz hw

/-- **Full arbitrary-morphism identification of the basic-open component (step (b), EGA I 10.4.6).**
For an arbitrary morphism `f : Spf S ⟶ Spf R` with continuous global-sections map
(`hφ : I ≤ J.comap (globalSectionsMap I J f)`), the conjugated basic-open component
`arbSheafComponent I J f g` equals the completed localization
`AdicCompletion.mapCompletion (Localization.awayMap (globalSectionsMap I J f) g)` — the same value
the reconstructed model morphism gives (`modelSheafComponent_eq_mapCompletion`). Combines the merged
reduction `arbSheafComponent_eq_mapCompletion_of_continuous` with the continuity
`arbSheafComponent_mem_pow`. This closes the sheaf-component half of the Spf–Γ converse, so step (c)
(issue 158) can assemble the round-trip `locallyRingedSpaceMap (globalSectionsMap f) = f`. -/
theorem arbSheafComponent_eq_mapCompletion (hI : I.FG) (hJ : J.FG)
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (g : R)
    (hφ : I ≤ J.comap (globalSectionsMap I J f)) :
    arbSheafComponent I J f g =
      AdicCompletion.mapCompletion (Localization.awayMap (globalSectionsMap I J f) g)
        (awayCompletionIdeal_map_awayMap_le I J (globalSectionsMap I J f) hφ g) (hJ.map _) :=
  arbSheafComponent_eq_mapCompletion_of_continuous I J hI hJ f g hφ
    (arbSheafComponent_mem_pow I J f g hφ)

end FormalSpectrum

end
