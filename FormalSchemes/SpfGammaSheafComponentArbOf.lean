import FormalSchemes.SpfGammaSheafComponentArbComp

set_option linter.style.header false

/-!
# An arbitrary morphism's basic-open component on the dense image of the localization

For adic rings `(R, I)` and `(S, J)` and an **arbitrary** morphism of formal spectra
`f : Spf S ⟶ Spf R`, the sheaf `c`-component of `f` on a basic open `D(g)`, conjugated by
`FormalSpectrum.sectionsBasicOpenEquiv` on both sides (`FormalSpectrum.arbSheafComponent`), is a
ring homomorphism `R{1/g} →+* S{1/φ g}` with `φ = FormalSpectrum.globalSectionsMap I J f`.

The merged locality-free naturality square `arbSheafComponent_comp_awayCompletionHom` pins the
component only on the image of the *structure map* `awayCompletionHom I g : R → R{1/g}` — i.e. on
the image of `R`. This file sharpens that to the image of the whole **localization** `R_g`:
precomposed with the completion structure map `AdicCompletion.of : R_g → R{1/g}`,
`arbSheafComponent I J f g` agrees with `AdicCompletion.of : S_{φ g} → S{1/φ g}` composed with the
localized ring map `Localization.awayMap φ g : R_g → S_{φ g}`. The upgrade from "the image of `R`"
to "the image of `R_g`" is purely algebraic: a ring homomorphism out of the localization `R_g` is
determined by its restriction to `R` (`IsLocalization.ringHom_ext` on `Submonoid.powers g`), and the
naturality square supplies exactly that restriction.

Since `AdicCompletion.of` has dense image, this determines `arbSheafComponent I J f g` on a dense
subring. Consequently, the **only** remaining ingredient for the full identification of
`arbSheafComponent I J f g` with the completed localization
`AdicCompletion.mapCompletion (Localization.awayMap φ g)` (the model-morphism value computed in
`modelSheafComponent_eq_mapCompletion`) is *continuity* of `arbSheafComponent I J f g` — that it
carries the ideal-of-definition filtration `(I·R_g)^m` into `(J·S_{φ g})^m`. This is recorded here
as `arbSheafComponent_eq_mapCompletion_of_continuous`, isolating the still-open hard half of step
(b) of the converse of EGA I 10.4.6 (issue 157) to exactly that continuity statement — the expected
consequence of the locality (`f.prop`) of the morphism of locally ringed spaces.

## Main results

* `FormalSpectrum.arbSheafComponent_comp_algebraMap` / `arbSheafComponent_algebraMap`:
  `arbSheafComponent I J f g` precomposed with `algebraMap R_g R{1/g}` is `algebraMap S_{φ g}
  S{1/φ g}` composed with `Localization.awayMap φ g`.
* `FormalSpectrum.arbSheafComponent_eq_mapCompletion_of_continuous`: assuming `φ` is continuous
  (`I ≤ J.comap φ`) and `arbSheafComponent I J f g` carries the ideal-of-definition filtration into
  the powers of the target ideal of definition, `arbSheafComponent I J f g` equals
  `AdicCompletion.mapCompletion (Localization.awayMap φ g)`.

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

/-- **The component agrees with the completed localized map on the image of `R_g`.**
For an arbitrary morphism `f : Spf S ⟶ Spf R`, the conjugated basic-open component
`arbSheafComponent I J f g`, precomposed with the completion structure map
`algebraMap R_g R{1/g}`, equals the target structure map `algebraMap S_{φ g} S{1/φ g}` composed
with the localized ring map `Localization.awayMap φ g`, where `φ = globalSectionsMap I J f`.
Upgrades the "agrees on the image of `R`" square `arbSheafComponent_comp_awayCompletionHom` to the
whole localization `R_g`, using `IsLocalization.ringHom_ext`. -/
theorem arbSheafComponent_comp_algebraMap
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (g : R) :
    (arbSheafComponent I J f g).comp
        (algebraMap (Localization.Away g) (awayCompletion I g)) =
      (algebraMap (Localization.Away (globalSectionsMap I J f g))
          (awayCompletion J (globalSectionsMap I J f g))).comp
        (Localization.awayMap (globalSectionsMap I J f) g) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers g)
  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply]
  -- `awayMap ∘ algebraMap = algebraMap ∘ φ` in pointwise (nested-application) form.
  have e : (Localization.awayMap (globalSectionsMap I J f) g)
        (algebraMap R (Localization.Away g) r) =
      algebraMap S (Localization.Away (globalSectionsMap I J f g)) (globalSectionsMap I J f r) :=
    RingHom.congr_fun (awayMap_comp_algebraMap (globalSectionsMap I J f) g) r
  -- LHS: `algebraMap R_g R{1/g} (algebraMap R R_g r)` is definitionally `awayCompletionHom I g r`;
  -- RHS: rewrite via `e`, then read `algebraMap ∘ algebraMap` as `awayCompletionHom J (φ g)`.
  rw [show algebraMap (Localization.Away g) (awayCompletion I g)
        (algebraMap R (Localization.Away g) r) = awayCompletionHom I g r from rfl, e,
    show algebraMap (Localization.Away (globalSectionsMap I J f g))
        (awayCompletion J (globalSectionsMap I J f g))
        (algebraMap S (Localization.Away (globalSectionsMap I J f g))
          (globalSectionsMap I J f r)) =
      awayCompletionHom J (globalSectionsMap I J f g) (globalSectionsMap I J f r) from rfl]
  -- The remaining equation is the merged locality-free naturality square, applied to `r`.
  exact RingHom.congr_fun (arbSheafComponent_comp_awayCompletionHom I J f g) r

/-- Pointwise form of `arbSheafComponent_comp_algebraMap`: `arbSheafComponent I J f g` sends the
completion image `algebraMap b` of `b : R_g` to `algebraMap (awayMap φ g b)`. -/
theorem arbSheafComponent_algebraMap
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (g : R)
    (b : Localization.Away g) :
    arbSheafComponent I J f g (algebraMap (Localization.Away g) (awayCompletion I g) b) =
      algebraMap (Localization.Away (globalSectionsMap I J f g))
        (awayCompletion J (globalSectionsMap I J f g))
        (Localization.awayMap (globalSectionsMap I J f) g b) :=
  RingHom.congr_fun (arbSheafComponent_comp_algebraMap I J f g) b

/-- **Reduction of the arbitrary-morphism identification to continuity.**
Assume `φ = globalSectionsMap I J f` is continuous (`I ≤ J.comap φ`) and the conjugated basic-open
component `arbSheafComponent I J f g` carries the ideal-of-definition filtration `(I·R_g)^m` into
the powers of the target ideal of definition `(J·S_{φ g})^m`. Then `arbSheafComponent I J f g`
equals the completed localization `AdicCompletion.mapCompletion (Localization.awayMap φ g)` — the
same value
computed for the reconstructed model morphism by `modelSheafComponent_eq_mapCompletion`. The two
continuous maps agree on the dense image of the structure map (by `arbSheafComponent_algebraMap` and
`mapCompletion_of`), so `AdicCompletion.hom_ext_of_continuous` concludes. This isolates the
still-open hard half of step (b) (issue 157) to exactly the continuity hypothesis `hcont`. -/
theorem arbSheafComponent_eq_mapCompletion_of_continuous (hI : I.FG) (hJ : J.FG)
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (g : R)
    (hφ : I ≤ J.comap (globalSectionsMap I J f))
    (hcont : ∀ (m : ℕ) (x : awayCompletion I g),
      x ∈ ((I.map (algebraMap R (Localization.Away g))) ^ m • ⊤ :
          Submodule (Localization.Away g) (awayCompletion I g)) →
        arbSheafComponent I J f g x ∈
          (awayCompletionIdeal J (globalSectionsMap I J f g)) ^ m) :
    arbSheafComponent I J f g =
      AdicCompletion.mapCompletion (Localization.awayMap (globalSectionsMap I J f) g)
        (awayCompletionIdeal_map_awayMap_le I J (globalSectionsMap I J f) hφ g) (hJ.map _) := by
  haveI : IsAdicComplete
      (AdicCompletion.idealOfDefinition
        (J.map (algebraMap S (Localization.Away (globalSectionsMap I J f g)))))
      (awayCompletion J (globalSectionsMap I J f g)) :=
    (AdicCompletion.isAdicRing_map _ (hJ.map _)).toIsAdicComplete
  refine AdicCompletion.hom_ext_of_continuous
    (I.map (algebraMap R (Localization.Away g)))
    (AdicCompletion.idealOfDefinition
      (J.map (algebraMap S (Localization.Away (globalSectionsMap I J f g)))))
    (hI.map _) hcont
    (fun m x hx => AdicCompletion.mapCompletion_mem_pow
      (Localization.awayMap (globalSectionsMap I J f) g)
      (awayCompletionIdeal_map_awayMap_le I J (globalSectionsMap I J f) hφ g) (hJ.map _)
      (hI.map _) m hx)
    (fun b => ?_)
  rw [AdicCompletion.mapCompletion_of,
    show AdicCompletion.of (I.map (algebraMap R (Localization.Away g))) (Localization.Away g) b =
        algebraMap (Localization.Away g) (awayCompletion I g) b from
      by rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply],
    arbSheafComponent_algebraMap I J f g b]

end FormalSpectrum

end
