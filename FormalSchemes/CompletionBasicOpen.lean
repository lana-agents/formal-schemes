import FormalSchemes.Completion
import FormalSchemes.AwayCompletionInterchange
import FormalSchemes.BasicOpenImmersionLRS

set_option linter.style.header false

/-!
# The formal completion of a basic open as an open formal subscheme (EGA I, 10.8)

For a commutative ring `R`, a finitely generated ideal `I`, and `f : R`, the formal completion of
the localization `Spec R_f = D(f)` along `V(I·R_f)` sits inside the formal completion of `Spec R`
along `V(I)` as an **open formal subscheme**, with underlying space the basic open `D(f̂)` of the
completion — where `f̂ = algebraMap R R^ f` is the image of `f` in `R^ = AdicCompletion I R`.

This is the affine (basic-open) instance of the compatibility that the *global* formal completion
(completing an arbitrary scheme along a closed subset by gluing affine completions) consumes: for a
separated scheme, the affine charts of the completion glue along exactly such common basic opens,
where the overlaps *are* affine — sidestepping the non-affine-overlap obstruction to the general
gluing. Concretely it upgrades the functoriality morphism `formalCompletion.map` of the localization
`R → R_f` to a `LocallyRingedSpace.IsOpenImmersion` and computes its range.

The construction reuses two merged pieces of infrastructure:
* the completion–localization interchange `AdicCompletion.awayCompletionInterchange` — completing
  the localization `R_f` agrees with localizing the completion `R^` at `f̂` and completing again —
  provides the ring isomorphism identifying the source of the affine basic-open chart of `Spf R^`
  with the ring of the completion of `Spec R_f`;
* the affine basic-open chart open immersion `FormalSpectrum.basicOpenChart` of `Spf R^`
  (`FormalSpectrum.isOpenImmersion_basicOpenChart`, `FormalSpectrum.range_basicOpenChart_base`).

## Main definitions and results

* `AdicCompletion.map_interchangeForward` / `AdicCompletion.map_interchangeBackward`: the two
  directions of the interchange carry the ideal of definition into the ideal of definition.
* `formalCompletion.locCompletionChartIso`: `Spf` of the interchange ring isomorphism, identifying
  the completion of `Spec R_f` with the source of the affine basic-open chart of `Spf R^`.
* `formalCompletion.basicOpenImmersion`: the morphism of formal completions
  `formalCompletion R_f (I·R_f) ⟶ formalCompletion R I` induced by `R → R_f`.
* `formalCompletion.basicOpenImmersion_isOpenImmersion`: it is an open immersion.
* `formalCompletion.range_basicOpenImmersion`: its range is the basic open `D(f̂)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace AdicCompletion

variable {B : Type u} [CommRing B] (K : Ideal B) (t : B)

/-- The forward map of the completion–localization interchange carries the ideal of definition of
the source completion into that of the target: it is `mapCompletion` of the localization
transitivity, hence an adic ring homomorphism. -/
theorem map_interchangeForward (hK : K.FG) :
    (idealOfDefinition (locIdeal K t)).map (interchangeForward K t hK) ≤
      idealOfDefinition (completionLocIdeal K t) :=
  idealOfDefinition_map_le (locTransition K t) (map_locTransition K t).le
    (completionLocIdeal_fg K t hK)

/-- The backward map of the completion–localization interchange carries the ideal of definition of
the target completion into that of the source: on the dense image of the structure map it agrees
with `locCompletionLift`, which is adic (`map_locCompletionLift`). -/
theorem map_interchangeBackward (hK : K.FG) :
    (idealOfDefinition (completionLocIdeal K t)).map (interchangeBackward K t hK) ≤
      idealOfDefinition (locIdeal K t) := by
  have hcomp : (interchangeBackward K t hK).comp
        (algebraMap (awayCompletionLoc K t)
          (AdicCompletion (completionLocIdeal K t) (awayCompletionLoc K t))) =
      locCompletionLift K t hK := by
    ext y
    have hy : algebraMap (awayCompletionLoc K t)
          (AdicCompletion (completionLocIdeal K t) (awayCompletionLoc K t)) y =
        AdicCompletion.of (completionLocIdeal K t) (awayCompletionLoc K t) y := by
      rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [RingHom.comp_apply, hy, interchangeBackward_of]
  change ((completionLocIdeal K t).map (algebraMap (awayCompletionLoc K t)
      (AdicCompletion (completionLocIdeal K t) (awayCompletionLoc K t)))).map
      (interchangeBackward K t hK) ≤ _
  rw [Ideal.map_map, hcomp]
  exact map_locCompletionLift K t hK

end AdicCompletion

namespace formalCompletion

open FormalSpectrum AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (f : R)

/-- **The completion–localization interchange as an isomorphism of formal spectra.** `Spf` of the
ring isomorphism `AdicCompletion.awayCompletionInterchange`, identifying the underlying locally
ringed space of the completion `formalCompletion R_f (I·R_f)` of `Spec R_f` with that of the affine
basic-open chart `Spf (R^){1/f̂}` of `Spf R^`. The two `Spf`-morphisms are mutually inverse because
the interchange is a ring isomorphism, via the merged `Spf`-functor laws. -/
def locCompletionChartIso :
    locallyRingedSpaceObj (idealOfDefinition (I.map (algebraMap R (Localization.Away f)))) ≅
      locallyRingedSpaceObj (awayCompletionIdeal (idealOfDefinition I) (awayPoint I f)) where
  hom := locallyRingedSpaceMap _ _ (interchangeBackward I f hI)
    (Ideal.map_le_iff_le_comap.mp (map_interchangeBackward I f hI))
  inv := locallyRingedSpaceMap _ _ (interchangeForward I f hI)
    (Ideal.map_le_iff_le_comap.mp (map_interchangeForward I f hI))
  hom_inv_id := by
    have hIK : idealOfDefinition (locIdeal I f) ≤
        (idealOfDefinition (locIdeal I f)).comap
          ((interchangeBackward I f hI).comp (interchangeForward I f hI)) := by
      rw [interchangeBackward_comp_interchangeForward]; exact (Ideal.comap_id _).ge
    rw [← locallyRingedSpaceMap_comp (hIK := hIK),
      locallyRingedSpaceMap_congr (φ₂ := RingHom.id _)
        (hφ := interchangeBackward_comp_interchangeForward I f hI)]
    exact locallyRingedSpaceMap_id _
  inv_hom_id := by
    have hIK : idealOfDefinition (completionLocIdeal I f) ≤
        (idealOfDefinition (completionLocIdeal I f)).comap
          ((interchangeForward I f hI).comp (interchangeBackward I f hI)) := by
      rw [interchangeForward_comp_interchangeBackward]; exact (Ideal.comap_id _).ge
    rw [← locallyRingedSpaceMap_comp (hIK := hIK),
      locallyRingedSpaceMap_congr (φ₂ := RingHom.id _)
        (hφ := interchangeForward_comp_interchangeBackward I f hI)]
    exact locallyRingedSpaceMap_id _

/-- **The formal completion of a basic open** (EGA I, 10.8): the morphism of formal completions
`formalCompletion R_f (I·R_f) ⟶ formalCompletion R I` induced by the localization `R → R_f`,
realised as the interchange isomorphism followed by the affine basic-open chart of `Spf R^`. -/
def basicOpenImmersion :
    formalCompletion (Localization.Away f)
        (I.map (algebraMap R (Localization.Away f))) (hI.map _) ⟶
      formalCompletion R I hI :=
  haveI := AdicCompletion.isAdicRing_map I hI
  haveI := AdicCompletion.isAdicRing_map (I.map (algebraMap R (Localization.Away f))) (hI.map _)
  FormalScheme.Hom.mk
    ((locCompletionChartIso I hI f).hom ≫
      basicOpenChart (idealOfDefinition I) (awayPoint I f))

/-- **The formal completion of a basic open is an open immersion.** Its underlying locally ringed
space morphism is an isomorphism (`locCompletionChartIso`) followed by the affine basic-open chart
open immersion (`isOpenImmersion_basicOpenChart`). -/
instance basicOpenImmersion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (basicOpenImmersion I hI f).toLRSHom := by
  haveI hchart : LocallyRingedSpace.IsOpenImmersion
      (basicOpenChart (idealOfDefinition I) (awayPoint I f)) :=
    isOpenImmersion_basicOpenChart (idealOfDefinition I) (awayPoint I f) (hI.map _)
  change LocallyRingedSpace.IsOpenImmersion
    ((locCompletionChartIso I hI f).hom ≫ basicOpenChart (idealOfDefinition I) (awayPoint I f))
  exact LocallyRingedSpace.IsOpenImmersion.comp _ _

/-- **The range of the basic-open completion immersion is the basic open `D(f̂)`** of the space of
the completion `Spf R^`, where `f̂ = algebraMap R R^ f`. Under the homeomorphism `homeo` with
`Spec (R ⧸ I)` this is the trace of `D(f)` on the closed subset `V(I)` one completes along. -/
theorem range_basicOpenImmersion :
    Set.range (basicOpenImmersion I hI f).toLRSHom.base =
      (basicOpen (idealOfDefinition I) (awayPoint I f) :
        Set (FormalSpectrum (idealOfDefinition I))) := by
  have hsurj : Function.Surjective ⇑(locCompletionChartIso I hI f).hom.base := by
    intro x
    refine ⟨(locCompletionChartIso I hI f).inv.base x, ?_⟩
    have hx : ((locCompletionChartIso I hI f).inv ≫ (locCompletionChartIso I hI f).hom).base x
        = x := by
      rw [(locCompletionChartIso I hI f).inv_hom_id]; rfl
    simpa only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply] using hx
  change Set.range ⇑(((locCompletionChartIso I hI f).hom ≫
    basicOpenChart (idealOfDefinition I) (awayPoint I f)).base) = _
  have hcomp : ⇑(((locCompletionChartIso I hI f).hom ≫
        basicOpenChart (idealOfDefinition I) (awayPoint I f)).base) =
      ⇑(basicOpenChart (idealOfDefinition I) (awayPoint I f)).base ∘
        ⇑(locCompletionChartIso I hI f).hom.base := by
    ext x
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply]
  rw [hcomp, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
  exact range_basicOpenChart_base (idealOfDefinition I) (awayPoint I f) (hI.map _)

end formalCompletion

end
