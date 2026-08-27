import FormalSchemes.AwayCompletionAway
import FormalSchemes.CompletionBasicOpen
import FormalSchemes.CompletedTensorAwayInterchangeSpf

set_option linter.style.header false

/-!
# The formal completion of a nested basic open as an open formal subscheme (EGA I, 10.8)

For a commutative ring `R`, a finitely generated ideal `I`, and elements `f g : R` with
`D(g) ⊆ D(f)`, the formal completion of the localization `Spec R_g = D(g)` along `V(I·R_g)` sits
inside the formal completion of `Spec R_f = D(f)` along `V(I·R_f)` as an **open formal subscheme**,
with underlying space the basic open `D(ĝ)` of the completion `Spf (R_f)^` — where
`ĝ = algebraMap R_f (R_f)^ (algebraMap R R_f g)` is the image of `g` in the completed localization.

This **generalizes** the merged affine basic-open completion immersion
`formalCompletion.basicOpenImmersion` — which is the special case `f = 1`, i.e. `D(g) ⊆ Spec R` — to
nested basic opens `D(g) ⊆ D(f)`. It is exactly the chart-overlap datum a *separated* scheme's
completion-gluing consumes: the affine charts of the completion of a scheme along a closed subset
glue along common basic opens `D(g) ⊆ D(f)`, where the overlaps are again affine, sidestepping the
non-affine-overlap obstruction to the general gluing.

The hypothesis `D(g) ⊆ D(f)` is encoded (as in `FormalSchemes/AwayCompletionAway.lean`) as
`hfg : IsUnit (algebraMap R (Localization.Away g) f)`: `f` becomes a unit on `D(g)`.

The construction reuses two merged pieces of infrastructure:
* the completed-localization transitivity `FormalSpectrum.awayCompletionAwayEquiv` — the ring
  isomorphism `R{1/g} ≃+* R_f{1/ĝ}` on `D(g) ⊆ D(f)` — which identifies the underlying locally
  ringed space of `formalCompletion R_g (I·R_g)` with the source of the affine basic-open chart of
  `Spf (R_f)^` at `ĝ`;
* the affine basic-open completion immersion `formalCompletion.basicOpenImmersion` of `Spf (R_f)^`,
  which realises `formalCompletion (R_f)_ĝ (I·(R_f)_ĝ) ↪ formalCompletion R_f (I·R_f)` onto the
  basic open `D(ĝ)`.

## Main definitions and results

* `formalCompletion.isAdicHom_awayCompletionAwayEquiv`: the completed-localization transitivity
  isomorphism carries the ideal of definition of `R{1/g}^` onto that of `R_f{1/ĝ}^`.
* `formalCompletion.nestedChartIso`: `Spf` of the transitivity ring isomorphism, identifying the
  completion of `Spec R_g` with the source of the affine basic-open chart of `Spf (R_f)^` at `ĝ`.
* `formalCompletion.nestedBasicOpenImmersion`: the morphism of formal completions
  `formalCompletion R_g (I·R_g) ⟶ formalCompletion R_f (I·R_f)` induced by `R_f → R_g`.
* `formalCompletion.nestedBasicOpenImmersion_isOpenImmersion`: it is an open immersion.
* `formalCompletion.range_nestedBasicOpenImmersion`: its range is the basic open `D(ĝ)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

/-- **The range of an iso-precomposed morphism** equals the range of the morphism: precomposing a
locally ringed space morphism `h` with the `hom` leg of an isomorphism `e` (a homeomorphism on
underlying spaces, hence surjective) does not change the range of the underlying base map. Stated
with uniform source/target objects so the range decomposition avoids the defeq-presentation
mismatch between `locallyRingedSpaceObj (…)` and `(formalCompletion …).toLocallyRingedSpace`. -/
theorem range_iso_hom_comp_base {X Y Z : LocallyRingedSpace.{u}} (e : X ≅ Y) (h : Y ⟶ Z) :
    Set.range ⇑(e.hom ≫ h).base = Set.range ⇑h.base := by
  have hsurj : Function.Surjective ⇑e.hom.base := fun y =>
    ⟨e.inv.base y, LocallyRingedSpace.iso_inv_base_hom_base_apply e y⟩
  have hcomp : ⇑(e.hom ≫ h).base = ⇑h.base ∘ ⇑e.hom.base := by
    ext x
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply]
  rw [hcomp, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]

namespace formalCompletion

open FormalSpectrum AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R) (f g : R)

set_option linter.style.setOption false in
set_option maxHeartbeats 800000 in
-- Identifying the underlying forward/backward legs of `awayCompletionAwayEquiv` with the
-- `mapCompletion` maps forces the elaborator to unfold the nested localization/completion towers of
-- the completed transitivity isomorphism, which is costly for the kernel; raise the budget.
/-- **The completed-localization transitivity is an adic homomorphism.** The ring isomorphism
`awayCompletionAwayEquiv : R{1/g}^ ≃+* R_f{1/ĝ}^` carries the ideal of definition of the source
completion onto that of the target: both inequalities come from
`AdicCompletion.idealOfDefinition_map_le` applied to the two `mapCompletion` legs of the isomorphism
(mirroring `annulusOverlapTransition_isAdicHom`). -/
theorem isAdicHom_awayCompletionAwayEquiv (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    IsAdicHom (awayCompletionIdeal I g)
      (awayCompletionIdeal (I.map (algebraMap R (Localization.Away f)))
        (algebraMap R (Localization.Away f) g))
      (awayCompletionAwayEquiv I f g hI hfg).toRingHom := by
  -- the two localization-transitivity ring maps underlying `awayCompletionAwayEquiv`
  let φ := (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom
  let ψ := (awayAwayLocEquiv f g hfg).symm.toRingEquiv.toRingHom
  have hKgFG : (I.map (algebraMap R (Localization.Away g))).FG := hI.map _
  have hKCFG : ((I.map (algebraMap R (Localization.Away f))).map
      (algebraMap (Localization.Away f)
        (Localization.Away (algebraMap R (Localization.Away f) g)))).FG := (hI.map _).map _
  have hA : (I.map (algebraMap R (Localization.Away g))).map φ ≤
      (I.map (algebraMap R (Localization.Away f))).map
        (algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R (Localization.Away f) g))) :=
    le_of_eq ((map_awayAwayLocEquiv I f g hfg).trans
      (map_algebraMap_localizationAway_eq I f g).symm)
  have hB : ((I.map (algebraMap R (Localization.Away f))).map
        (algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R (Localization.Away f) g)))).map ψ ≤
      I.map (algebraMap R (Localization.Away g)) :=
    le_of_eq ((congrArg (Ideal.map ψ) (map_algebraMap_localizationAway_eq I f g)).trans
      (map_awayAwayLocEquiv_symm I f g hfg))
  -- the forward and backward ideal inclusions at the completion level
  have hfwd : (awayCompletionIdeal I g).map (awayCompletionAwayEquiv I f g hI hfg).toRingHom ≤
      awayCompletionIdeal (I.map (algebraMap R (Localization.Away f)))
        (algebraMap R (Localization.Away f) g) :=
    AdicCompletion.idealOfDefinition_map_le φ hA hKCFG
  have hinv : (awayCompletionIdeal (I.map (algebraMap R (Localization.Away f)))
        (algebraMap R (Localization.Away f) g)).map
        (awayCompletionAwayEquiv I f g hI hfg).symm.toRingHom ≤ awayCompletionIdeal I g :=
    AdicCompletion.idealOfDefinition_map_le ψ hB hKgFG
  -- the backward inclusion, via the `symm`-round-trip (as in `annulusOverlapTransition_isAdicHom`)
  have hcomp_id : (awayCompletionAwayEquiv I f g hI hfg).toRingHom.comp
      (awayCompletionAwayEquiv I f g hI hfg).symm.toRingHom =
      RingHom.id (awayCompletion (I.map (algebraMap R (Localization.Away f)))
        (algebraMap R (Localization.Away f) g)) :=
    ringEquiv_toRingHom_comp_symm _
  -- term-mode round-trip: `rw [Ideal.map_map]` would abstract the ideal inside the `awayCompletion`
  -- abbrev and break its `CommRing` instance dependency, so chain the equalities as terms instead.
  have key (J : Ideal (awayCompletion (I.map (algebraMap R (Localization.Away f)))
      (algebraMap R (Localization.Away f) g))) :
      Ideal.map (awayCompletionAwayEquiv I f g hI hfg).toRingHom
        (Ideal.map (awayCompletionAwayEquiv I f g hI hfg).symm.toRingHom J) = J := by
    refine Eq.trans (Ideal.map_map _ _) ?_
    exact (congrArg (Ideal.map · J) hcomp_id).trans (Ideal.map_id J)
  refine le_antisymm hfwd ?_
  calc awayCompletionIdeal (I.map (algebraMap R (Localization.Away f)))
          (algebraMap R (Localization.Away f) g)
      = Ideal.map (awayCompletionAwayEquiv I f g hI hfg).toRingHom
          (Ideal.map (awayCompletionAwayEquiv I f g hI hfg).symm.toRingHom
            (awayCompletionIdeal (I.map (algebraMap R (Localization.Away f)))
              (algebraMap R (Localization.Away f) g))) :=
        (key _).symm
    _ ≤ (awayCompletionIdeal I g).map (awayCompletionAwayEquiv I f g hI hfg).toRingHom :=
        Ideal.map_mono hinv

/-- **The completed-localization transitivity as an isomorphism of formal spectra.** `Spf` of the
ring isomorphism `awayCompletionAwayEquiv`, identifying the underlying locally ringed space of the
completion `formalCompletion R_g (I·R_g)` of `Spec R_g` with that of the source of the affine
basic-open chart of `Spf (R_f)^` at `ĝ`. -/
def nestedChartIso (hI : I.FG) (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    locallyRingedSpaceObj (awayCompletionIdeal I g) ≅
      locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R (Localization.Away f)))
        (algebraMap R (Localization.Away f) g)) :=
  isoOfAdicRingEquiv _ _ (awayCompletionAwayEquiv I f g hI hfg)
    (isAdicHom_awayCompletionAwayEquiv I f g hI hfg)

/-- **The formal completion of a nested basic open** (EGA I, 10.8): the morphism of formal
completions `formalCompletion R_g (I·R_g) ⟶ formalCompletion R_f (I·R_f)` induced by the
localization `R_f → R_g` on `D(g) ⊆ D(f)`, realised as the transitivity isomorphism followed by the
affine basic-open chart of `Spf (R_f)^` at `ĝ`. This generalizes `basicOpenImmersion` from
`D(g) ⊆ Spec R` to a nested basic open `D(g) ⊆ D(f)`. -/
def nestedBasicOpenImmersion (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    formalCompletion (Localization.Away g)
        (I.map (algebraMap R (Localization.Away g))) (hI.map _) ⟶
      formalCompletion (Localization.Away f)
        (I.map (algebraMap R (Localization.Away f))) (hI.map _) :=
  haveI := FormalSpectrum.isAdicRing_awayCompletionIdeal I g hI
  haveI := FormalSpectrum.isAdicRing_awayCompletionIdeal I f hI
  -- inline the raw `locCompletionChartIso.hom ≫ basicOpenChart` legs of `basicOpenImmersion`
  -- (rather than its `.toLRSHom`) so every intermediate object is presented as
  -- `locallyRingedSpaceObj`, matching `nestedChartIso`'s target syntactically (cf.
  -- `interchangeOpenImmersion`).
  FormalScheme.Hom.mk
    ((nestedChartIso I f g hI hfg).hom ≫
      (locCompletionChartIso (I.map (algebraMap R (Localization.Away f))) (hI.map _)
          (algebraMap R (Localization.Away f) g)).hom ≫
        basicOpenChart (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
          (awayPoint (I.map (algebraMap R (Localization.Away f)))
            (algebraMap R (Localization.Away f) g)))

/-- **The formal completion of a nested basic open is an open immersion.** Its underlying locally
ringed space morphism is an isomorphism (`nestedChartIso`) followed by the affine basic-open chart
open immersion (`basicOpenImmersion_isOpenImmersion`). -/
instance nestedBasicOpenImmersion_isOpenImmersion (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    LocallyRingedSpace.IsOpenImmersion (nestedBasicOpenImmersion I f g hI hfg).toLRSHom := by
  haveI : LocallyRingedSpace.IsOpenImmersion
      (basicOpenChart (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
        (awayPoint (I.map (algebraMap R (Localization.Away f)))
          (algebraMap R (Localization.Away f) g))) :=
    isOpenImmersion_basicOpenChart (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
      (awayPoint (I.map (algebraMap R (Localization.Away f)))
        (algebraMap R (Localization.Away f) g)) ((hI.map _).map _)
  change LocallyRingedSpace.IsOpenImmersion
    ((nestedChartIso I f g hI hfg).hom ≫
      (locCompletionChartIso (I.map (algebraMap R (Localization.Away f))) (hI.map _)
          (algebraMap R (Localization.Away f) g)).hom ≫
        basicOpenChart (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
          (awayPoint (I.map (algebraMap R (Localization.Away f)))
            (algebraMap R (Localization.Away f) g)))
  infer_instance

/-- **The range of the nested-basic-open completion immersion is the basic open `D(ĝ)`** of the
space of the completion `Spf (R_f)^`, where `ĝ = algebraMap R_f (R_f)^ (algebraMap R R_f g)`. The
base map factors as an isomorphism (surjective) followed by the chart's base map, whose range is
`D(ĝ)` (`range_basicOpenImmersion`). -/
theorem range_nestedBasicOpenImmersion (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    Set.range (nestedBasicOpenImmersion I f g hI hfg).toLRSHom.base =
      (basicOpen (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
        (awayPoint (I.map (algebraMap R (Localization.Away f)))
          (algebraMap R (Localization.Away f) g)) :
        Set (FormalSpectrum (idealOfDefinition (I.map (algebraMap R (Localization.Away f)))))) := by
  change Set.range ⇑(((nestedChartIso I f g hI hfg).hom ≫
    (locCompletionChartIso (I.map (algebraMap R (Localization.Away f))) (hI.map _)
        (algebraMap R (Localization.Away f) g)).hom ≫
      basicOpenChart (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
        (awayPoint (I.map (algebraMap R (Localization.Away f)))
          (algebraMap R (Localization.Away f) g))).base) = _
  rw [range_iso_hom_comp_base, range_iso_hom_comp_base]
  exact range_basicOpenChart_base (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
    (awayPoint (I.map (algebraMap R (Localization.Away f)))
      (algebraMap R (Localization.Away f) g)) ((hI.map _).map _)

end formalCompletion

end
