import FormalSchemes.SpfGammaSheafComponent

set_option linter.style.header false

/-!
# Functoriality of the model morphism's sheaf component on basic opens

For adic rings `(R, I)`, `(S, J)`, `(T, K)` and continuous ring homomorphisms
`φ : R →+* S` (`hφ : I ≤ J.comap φ`), `ψ : S →+* T` (`hψ : J ≤ K.comap ψ`), the reconstructed
model morphism `Spf φ`'s conjugated sheaf `c`-component on a basic open `D(g)`,
`FormalSpectrum.modelSheafComponent`, is a *functor* in the continuous ring homomorphism: it sends
the identity to the identity and composition to composition.

Both laws are read off from the identification `modelSheafComponent_eq_mapCompletion`
(`SpfGammaSheafComponent.lean`) of the component with `AdicCompletion.mapCompletion` of the
localized homomorphism `Localization.awayMap φ g : R_g →+* S_{φ g}`, together with the completion
functor laws `AdicCompletion.mapCompletion_id`/`_comp` (`Completion.lean`) and the localization
functor laws `awayMap_id`/`awayMap_comp` proved here. Because the source/target indices are
definitionally equal (`(RingHom.id R) g ≡ g`, `(ψ.comp φ) g ≡ ψ (φ g)`), the statements are
homogeneous — no `eqToHom`/`HEq` transport is needed.

Together with `globalSectionsMap_id`/`_comp` (`SpfGammaFunctorial.lean`) — the functor laws for the
global-section side — this packages the model-morphism basic-open sheaf computation as the matching
component functor, a reusable input for the `Spf`–`Γ` adjunction assembly (issues 96/158) and the
model half of step (b) of the converse of EGA I 10.4.6 (issue 157).

## Main results

* `FormalSpectrum.awayMap_id` / `FormalSpectrum.awayMap_comp`: `Localization.awayMap` is functorial
  in the ring homomorphism.
* `FormalSpectrum.modelSheafComponent_id`: the model component of the identity is the identity.
* `FormalSpectrum.modelSheafComponent_comp`: the model component of a composite is the composite of
  the components (contravariantly, as befits a component of `Spf`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable (I : Ideal R) (J : Ideal S) (K : Ideal T)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]
variable [TopologicalSpace T] [IsAdicRing K]

omit [TopologicalSpace R] in
/-- Localizing away sends the identity to the identity: `awayMap (id R) g = id (R_g)`. -/
theorem awayMap_id (g : R) :
    Localization.awayMap (RingHom.id R) g = RingHom.id (Localization.Away g) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers g)
  refine RingHom.ext fun r => ?_
  have e := RingHom.congr_fun (awayMap_comp_algebraMap (RingHom.id R) g) r
  simp only [RingHom.comp_apply, RingHom.id_apply] at e ⊢
  rw [e]

omit [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace T] in
/-- Localizing away respects composition:
`awayMap (ψ ∘ φ) g = awayMap ψ (φ g) ∘ awayMap φ g`. -/
theorem awayMap_comp (φ : R →+* S) (ψ : S →+* T) (g : R) :
    Localization.awayMap (ψ.comp φ) g =
      (Localization.awayMap ψ (φ g)).comp (Localization.awayMap φ g) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers g)
  refine RingHom.ext fun r => ?_
  have e1 := RingHom.congr_fun (awayMap_comp_algebraMap (ψ.comp φ) g) r
  have e2 := RingHom.congr_fun (awayMap_comp_algebraMap φ g) r
  have e3 := RingHom.congr_fun (awayMap_comp_algebraMap ψ (φ g)) (φ r)
  simp only [RingHom.comp_apply] at e1 e2 e3 ⊢
  rw [e1, e2, e3]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Identity law for the model sheaf component.** The reconstructed model morphism `Spf (id R)`'s
conjugated sheaf `c`-component on `D(g)` is the identity of `awayCompletion I g`. -/
theorem modelSheafComponent_id (hI : I.FG) (g : R) :
    modelSheafComponent I I (RingHom.id R) (Ideal.comap_id I).ge g =
      RingHom.id (awayCompletion I g) := by
  rw [modelSheafComponent_eq_mapCompletion I I (RingHom.id R) (Ideal.comap_id I).ge g hI hI,
    ← AdicCompletion.mapCompletion_id (I := I.map (algebraMap R (Localization.Away g))) (hI.map _)]
  congr 1
  exact awayMap_id g

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]
  [TopologicalSpace T] [IsAdicRing K] in
/-- **Composition law for the model sheaf component.** The reconstructed model morphism
`Spf (ψ ∘ φ)`'s conjugated sheaf `c`-component on `D(g)` is the composite of the components of
`Spf ψ` (on `D(φ g)`) and `Spf φ` (on `D(g)`), contravariantly. -/
theorem modelSheafComponent_comp (φ : R →+* S) (ψ : S →+* T)
    (hφ : I ≤ J.comap φ) (hψ : J ≤ K.comap ψ) (hI : I.FG) (hJ : J.FG) (hK : K.FG) (g : R) :
    modelSheafComponent I K (ψ.comp φ)
        (fun _ hx => hψ (hφ hx)) g =
      (modelSheafComponent J K ψ hψ (φ g)).comp (modelSheafComponent I J φ hφ g) := by
  rw [modelSheafComponent_eq_mapCompletion I K (ψ.comp φ) _ g hI hK,
    modelSheafComponent_eq_mapCompletion I J φ hφ g hI hJ,
    modelSheafComponent_eq_mapCompletion J K ψ hψ (φ g) hJ hK,
    AdicCompletion.mapCompletion_comp (Localization.awayMap φ g) (Localization.awayMap ψ (φ g))
      (awayCompletionIdeal_map_awayMap_le I J φ hφ g)
      (awayCompletionIdeal_map_awayMap_le J K ψ hψ (φ g)) (hJ.map _) (hK.map _) (hI.map _)]
  congr 1
  exact awayMap_comp φ ψ g

end FormalSpectrum

end
