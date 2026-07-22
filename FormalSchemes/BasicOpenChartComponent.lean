import FormalSchemes.AwayCompletionInterchange
import FormalSchemes.SpfGamma

set_option linter.style.header false

/-!
# The sheaf component of the affine basic-open chart on basic opens

For an adic ring `(R, I)` with `I.FG` and `f : R`, the affine basic-open chart
`Spf R{1/f} ⟶ Spf R` (`FormalSchemes/BasicOpenChart.lean`) has a sheaf component whose value on a
basic open `D(g) ⊆ D(f)` is, under the sections identifications
`FormalSpectrum.sectionsBasicOpenEquiv` on source and target, a ring isomorphism between completed
localizations. The purely algebraic incarnation of that isomorphism, `R{1/g} ≃+* R{1/f}{1/ḡ}`, is
already available (`FormalSpectrum.awayCompletionChartEquiv`, issue 163; built on the merged
`awayCompletionAwayEquiv`/`awayCompletionInterchange`). This file provides the missing sheaf/limit
plumbing that lets one read the chart's `c`-component on basic opens level by level.

## Main results

* `FormalSpectrum.eval_sectionsBasicOpenEquiv`: the level-`n` computation rule for
  `sectionsBasicOpenEquiv` — the basic-open analogue of `FormalSpectrum.mk_globalSectionsEquiv`.
  Evaluating the completed-localization image of a section at level `n` recovers the level-`n`
  component of the section, transported by `basicOpenLevelEquiv`.
* `FormalSpectrum.mapSheafHom_hom_app_pi`: the level-`n` reduction of the sheaf component of a
  morphism of formal spectra over an arbitrary open `U` — its `n`-th tower component is the
  level map `levelSheafHom` (a `Spec`-structure-sheaf `comap`) applied to the `n`-th component of
  the argument. This is the general "read `f.c` level by level through the defining limit"
  plumbing; specialised to the affine basic-open chart it is the first half of the sheaf-level
  `c_iso` assembly (issue 163) and mirrors the value-chase reduction of `globalSectionsMap`.

## Remaining follow-up (issue 163 sheaf-level `c_iso`)

Composing `mapSheafHom_hom_app_pi` (level-`n` reduction) with `eval_sectionsBasicOpenEquiv` on
both source and target reduces the chart's `c`-component on a basic open `D(g) ⊆ D(f)` to a
level-`n` identity of `comap (levelRingHom …)` maps between localizations of quotients. Matching
that against the already-merged algebraic isomorphism `awayCompletionChartEquiv`
(`R{1/g} ≃+* R{1/f}{1/ḡ}`, `AwayCompletionInterchange.lean`) — i.e. proving the two agree at every
level via `AdicCompletion.ext_evalₐ` — is the remaining algebraic bookkeeping, after which
`TopCat.Sheaf.isIso_iff_isIso_basis` (restricted to the basis of basic opens below `D(f)`)
upgrades the chart to a `PresheafedSpace.IsOpenImmersion` (then `SheafedSpace`/`LocallyRingedSpace`
via `of_stalk_iso`'s packaging or directly through `c_iso`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.4.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I] (f : R)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The level-`n` computation rule for `sectionsBasicOpenEquiv` (the basic-open analogue of
`mk_globalSectionsEquiv`): evaluating the completed-localization image of a section `s` over
`D(f)` at level `n` recovers the level-`n` component of `s`, transported by `basicOpenLevelEquiv`.
-/
theorem eval_sectionsBasicOpenEquiv (n : ℕ)
    (s : (structureSheaf I).presheaf.obj (op (basicOpen I f))) :
    AdicCompletion.evalₐ (I.map (algebraMap R (Localization.Away f))) (n + 1)
        (sectionsBasicOpenEquiv I f s) =
      basicOpenLevelEquiv I f n
        (((limit.π (structureSheafFunctor I) ⟨n⟩).hom.app (op (basicOpen I f))).hom s) := by
  change AdicCompletion.evalₐ _ (n + 1)
    (AdicCompletion.towerLimitRingEquiv _ (sectionsTower I (basicOpen I f))
      (basicOpenLevelEquiv I f)
      (fun m => by rw [sectionsTower_map_succ]; exact basicOpenLevelEquiv_step I f m)
      ((sectionsLimitIso I (op (basicOpen I f))).hom.hom s)) = _
  rw [AdicCompletion.evalₐ_towerLimitRingEquiv, AdicCompletion.towerProj_apply]
  congr 1
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (sectionsLimitIso_hom_π I (op (basicOpen I f)) n)) s

variable {S : Type u} [CommRing S] (J : Ideal S) [TopologicalSpace S] [IsAdicRing J]
variable (φ : R →+* S) (hφ : I ≤ J.comap φ)

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J] in
/-- The level-`n` reduction of the sheaf component of a morphism of formal spectra over an
arbitrary open `U`: composing with the level-`n` tower projection turns `mapSheafHom` into the
level map `levelSheafHom` (a `Spec`-structure-sheaf `comap`) precomposed with the level-`n`
projection of the source. This is `mapSheafHom_π` read pointwise, and the general form of the
`hπ` step in `globalSectionsMap_locallyRingedSpaceMap`. -/
theorem mapSheafHom_hom_app_pi (n : ℕ) (U : Opens (FormalSpectrum I))
    (s : (structureSheaf I).presheaf.obj (op U)) :
    ((limit.π (structureSheafFunctor J) ⟨n⟩).hom.app
        (op ((Opens.map (mapTop I J φ hφ)).obj U))).hom
        (((mapSheafHom I J φ hφ).hom.app (op U)).hom s) =
      ((levelSheafHom I J φ hφ n).hom.app (op U)).hom
        (((limit.π (structureSheafFunctor I) ⟨n⟩).hom.app (op U)).hom s) :=
  DFunLike.congr_fun (congrArg (fun (α : structureSheaf I ⟶
    (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).obj (thickeningSheaf J n)) =>
      (α.hom.app (op U)).hom) (mapSheafHom_π I J φ hφ n)) s

end FormalSpectrum
