import FormalSchemes.SpfGamma

set_option linter.style.header false

/-!
# The sheaf component of a morphism of formal spectra on basic opens

This file is **step (b)** of the converse half of the universal property of `Spf`
(EGA I, 10.4.6; issue 96/157). The faithful half `FormalSchemes/SpfGamma.lean`
(`globalSectionsMap_locallyRingedSpaceMap`) only ever inspects the *global* sections component
`f.c.app (op ⊤)`. To reconstruct a morphism of formal spectra from its global data one must be
able to read its sheaf component `f.c` on the basis of basic opens `D(g)`, level by level through
the defining limit of thickening structure sheaves.

This file lands the two reusable *materials* the reconstruction rests on (issue 157's
"Route / materials"):

1. The **level-`n` computation rule for the basic-open sections identification**
   `sectionsBasicOpenEquiv` (`FormalSchemes/Sections.lean`): modulo `(I·R_f)^(n+1)`, the
   completed-localization element attached to a section over `D(f)` is the level-`n` component of
   that section, read through `basicOpenLevelEquiv`. This is the basic-open analogue of
   `mk_globalSectionsEquiv` (which handles `⊤`, where the completion collapses to `R`).
2. The **level-`n` reconstruction of the sheaf component of a reconstructed morphism `Spf φ` on an
   arbitrary open** `V`: the level-`n` projection of `(mapSheafHom I J φ hφ).hom.app (op V)` is the
   `levelSheafHom` comap applied to the level-`n` projection of the argument. This is the
   open-general form of the `V = ⊤` calculation inside `globalSectionsMap_locallyRingedSpaceMap`;
   on basic opens, `(mapTop)⁻¹ D(f₀) = D(φ f₀)` (`map_preimage_basicOpen`).

## Remaining follow-up (issue 157/158)

Assembling these into a single characterisation of `f.c` on `D(g)` — for an *arbitrary* morphism
`f`, via locality (`f.prop`) and the step-(a) base identification — is the remaining, harder part
of step (b). Even for the model morphism `Spf φ`, packaging the two computation rules into one
completed-localization map `R{1/f₀} → S{1/φ f₀}` needs the finite-generation hypotheses of
`AdicCompletion.mapCompletion` and the `map_preimage_basicOpen` open-transport, so it is deferred.

## Main results

* `FormalSpectrum.mk_sectionsBasicOpenEquiv`: the level-`n` computation rule for
  `sectionsBasicOpenEquiv` on `D(f)`.
* `FormalSpectrum.mapSheafHom_app_π`: the level-`n` projection of
  `(mapSheafHom I J φ hφ).hom.app (op V)` (a section over the preimage `(mapTop)⁻¹ V`) is the
  `levelSheafHom` comap applied to the level-`n` projection of the argument.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S)

/-!
### The level-`n` computation rule for sections on a basic open
-/

section Computation

variable [TopologicalSpace R] [IsAdicRing I]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The identification `Γ(D(f), O_{Spf R}) ≃+* AdicCompletion (I·R_f) R_f` is computed level by
level: modulo `(I·R_f)^(n+1)`, the element attached to a section is the level-`n` component of
the section, read through `basicOpenLevelEquiv`. This is the basic-open analogue of
`mk_globalSectionsEquiv`. -/
theorem mk_sectionsBasicOpenEquiv (f : R) (n : ℕ)
    (s : (structureSheaf I).presheaf.obj (op (basicOpen I f))) :
    AdicCompletion.evalₐ (I.map (algebraMap R (Localization.Away f))) (n + 1)
        (sectionsBasicOpenEquiv I f s) =
      basicOpenLevelEquiv I f n
        (((limit.π (structureSheafFunctor I) ⟨n⟩).hom.app
          (op (basicOpen I f))).hom s) := by
  change AdicCompletion.evalₐ (I.map (algebraMap R (Localization.Away f))) (n + 1)
    (AdicCompletion.towerLimitRingEquiv (I.map (algebraMap R (Localization.Away f)))
      (sectionsTower I (basicOpen I f)) (basicOpenLevelEquiv I f)
      (fun m => by rw [sectionsTower_map_succ]; exact basicOpenLevelEquiv_step I f m)
      ((sectionsLimitIso I (op (basicOpen I f))).hom.hom s)) = _
  rw [AdicCompletion.evalₐ_towerLimitRingEquiv, AdicCompletion.towerProj_apply]
  congr 1
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (sectionsLimitIso_hom_π I (op (basicOpen I f)) n)) s

end Computation

/-!
### The sheaf component of a reconstructed morphism, level by level
-/

section Map

variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]
variable (φ : R →+* S) (hφ : I ≤ J.comap φ)

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J] in
/-- The level-`n` reconstruction of the sheaf component of `Spf φ` on an arbitrary open `V`: the
level-`n` projection of `(mapSheafHom I J φ hφ).hom.app (op V) s` (a section over the preimage
`(mapTop)⁻¹ V`) is the `levelSheafHom` comap applied to the level-`n` projection of `s`.

This is the open-general form of the level-`n` calculation that
`globalSectionsMap_locallyRingedSpaceMap` performs at `V = ⊤`; on basic opens
(`(mapTop)⁻¹ D(f₀) = D(φ f₀)`, `map_preimage_basicOpen`) it is the component needed to
reconstruct `f.c` from the basis of basic opens. -/
theorem mapSheafHom_app_π (n : ℕ) (V : Opens (FormalSpectrum I))
    (s : (structureSheaf I).presheaf.obj (op V)) :
    ((limit.π (structureSheafFunctor J) ⟨n⟩).hom.app
        (op ((Opens.map (mapTop I J φ hφ)).obj V))).hom
        (((mapSheafHom I J φ hφ).hom.app (op V)).hom s) =
      ((levelSheafHom I J φ hφ n).hom.app (op V)).hom
        (((limit.π (structureSheafFunctor I) ⟨n⟩).hom.app (op V)).hom s) :=
  DFunLike.congr_fun (congrArg (fun (α : structureSheaf I ⟶
    (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).obj (thickeningSheaf J n)) =>
      (α.hom.app (op V)).hom) (mapSheafHom_π I J φ hφ n)) s

end Map

end FormalSpectrum
