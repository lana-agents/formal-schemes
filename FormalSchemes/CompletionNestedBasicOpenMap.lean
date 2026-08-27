import FormalSchemes.CompletionNestedBasicOpen
import FormalSchemes.CompletionBasicOpenMap

set_option linter.style.header false

/-!
# The nested basic-open completion immersion is `formalCompletion.map` (EGA I, 10.8)

`FormalSchemes/CompletionBasicOpenMap.lean` identifies the *one-step* basic-open completion
immersion `formalCompletion.basicOpenImmersion` — the geometric morphism
`formalCompletion R_f (I·R_f) ⟶ formalCompletion R I`, built as the completion–localization
interchange followed by an affine basic-open chart — with the functorial morphism
`formalCompletion.map` of the localization `R → R_f`, and reads off the resulting `toSpec` square.

This file does the same one level down, for a *nested* basic open `D(g) ⊆ D(f)`. The morphism in
question is `formalCompletion.nestedBasicOpenImmersion`
(`FormalSchemes/CompletionNestedBasicOpen.lean`), built as the completed-localization transitivity
isomorphism followed by the affine basic-open chart of `Spf (R_f)^` at `ĝ`; the functorial morphism
is `formalCompletion.map` of the localization `R_f → R_g`. That localization has no `algebraMap`
here — there is no `Algebra (Localization.Away f) (Localization.Away g)` instance in this
situation — so it is spelled `IsLocalization.Away.lift f hfg`, the map obtained from `f` becoming a
unit on `D(g)`.

The consequence is the square

```
formalCompletion R_g (I·R_g) ──nestedBasicOpenImmersion──→ formalCompletion R_f (I·R_f)
          │ toSpec                                                    │ toSpec
          ↓                                                           ↓
       Spec R_g  ─────────── Spec (R_f → R_g) ──────────────────→ Spec R_f
```

Where the chart-level square of `CompletionBasicOpenMap.lean` is the compatibility of the affine
charts of a completion with the canonical morphism to `Spec`, this is the compatibility on their
*overlaps*: for a separated scheme the affine charts of the completion glue along common basic
opens `D(g) ⊆ D(f)`, and a global `X_{/Y} ⟶ X` glued from the local `toSpec`s needs both.

The identification is again a ring computation, one leg longer than the chart-level one.
`nestedBasicOpenImmersion` is a three-leg composite of maps of formal spectra: the transitivity
isomorphism, the interchange isomorphism, and the chart map. Its inner two legs compose to
`AdicCompletion.completionToLocCompletion`, i.e. `mapCompletion` of `R_f → (R_f)_ĝ`
(`AdicCompletion.interchangeBackward_comp_awayCompletionHom`), and the outer leg is `mapCompletion`
of the transitivity inverse `(R_f)_ĝ → R_g`, so the whole composite is `mapCompletion` of
`IsLocalization.Away.lift f hfg` by functoriality of the completion.

## Main definitions and results

* `AdicCompletion.mapCompletion_congr`: `mapCompletion` depends on its ring homomorphism only
  through its value, not through the proof that it carries the ideal.
* `FormalSpectrum.awayAwayLocEquiv_symm_comp_algebraMap_away`: the inverse of the localization
  transitivity isomorphism, precomposed with `R_f → (R_f)_ĝ`, is `IsLocalization.Away.lift f hfg` —
  this is the lemma that names the ring map `R_f → R_g`.
* `formalCompletion.nestedBasicOpenImmersion_eq_map`: the geometric nested basic-open immersion
  **is** the functorial `formalCompletion.map` of `R_f → R_g`.
* `formalCompletion.nestedBasicOpenImmersion_comp_toSpec`: the `toSpec` square over a nested basic
  open commutes.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AdicCompletion

/-- **`mapCompletion` is a congruence in its ring homomorphism**: it depends on the homomorphism
only through its value, not through the proof that the homomorphism carries the source ideal into
the target one. This is the `mapCompletion` analogue of
`FormalSpectrum.locallyRingedSpaceMap_congr`, and like it the proof is `subst` followed by `rfl`,
the two hypotheses becoming propositionally equal once the homomorphisms are identified.

`AdicCompletion.mapCompletion_congr_localizationAway`
(`FormalSchemes/AwayCompletionNestedNaturality.lean`) is the adjacent statement for a source that
is a `Localization.Away`, where agreement after precomposing with the structure map already
suffices. This one asks for the homomorphisms to be equal outright and in exchange assumes nothing
about the source, which is what a caller holding an honest equality of ring maps — such as
`FormalSpectrum.awayAwayLocEquiv_symm_comp_algebraMap_away` below — wants. -/
theorem mapCompletion_congr {A C : Type u} [CommRing A] [CommRing C] {L : Ideal A} {M : Ideal C}
    (φ₁ φ₂ : A →+* C) (h₁ : L.map φ₁ ≤ M) (h₂ : L.map φ₂ ≤ M) (hM : M.FG) (h : φ₁ = φ₂) :
    mapCompletion φ₁ h₁ hM = mapCompletion φ₂ h₂ hM := by
  subst h; rfl

end AdicCompletion

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (f g : R)

/-- **The localization transitivity inverse is the `Away.lift` localization map.** For
`D(g) ⊆ D(f)`, encoded as `hfg : IsUnit (algebraMap R (Localization.Away g) f)`, the transitivity
isomorphism `awayAwayLocEquiv f g hfg : R_g ≃+* (R_f)_ĝ` has an inverse which, precomposed with the
structural map `R_f → (R_f)_ĝ`, is the localization map `R_f → R_g` induced by `f` being a unit on
`D(g)`.

This is the statement of `FormalSpectrum.awayAwayLocEquiv_symm_comp_algebraMap` over the base
`R_f` rather than over `R`; the bridge is the universal property of `R_f` as a localization of `R`
(`IsLocalization.ringHom_ext` at `Submonoid.powers f`) together with `IsScalarTower.algebraMap_eq`.
It is what names the ring homomorphism `R_f → R_g` underlying the nested basic-open completion
immersion — note there is no `Algebra (Localization.Away f) (Localization.Away g)` instance here,
so that homomorphism has to be spelled `IsLocalization.Away.lift f hfg`. -/
theorem awayAwayLocEquiv_symm_comp_algebraMap_away
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    (awayAwayLocEquiv f g hfg).symm.toRingEquiv.toRingHom.comp
        (algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R (Localization.Away f) g))) =
      IsLocalization.Away.lift (S := Localization.Away f) f hfg := by
  refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq,
    awayAwayLocEquiv_symm_comp_algebraMap, IsLocalization.Away.lift_comp]

end FormalSpectrum

namespace formalCompletion

open FormalSpectrum AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R) (f g : R)

/-- **The nested basic-open completion immersion is the functoriality morphism of the localization
`R_f → R_g`** (EGA I, 10.8). `formalCompletion.nestedBasicOpenImmersion` is built geometrically —
the completed-localization transitivity isomorphism, then the interchange isomorphism, then the
affine basic-open chart of `Spf (R_f)^` at `ĝ` — because that is what exhibits it as an open
immersion with range `D(ĝ)`. `formalCompletion.map` is built functorially, as `Spf` of
`AdicCompletion.mapCompletion`. They are the same morphism. This is the nested (`D(g) ⊆ D(f)`)
analogue of `formalCompletion.basicOpenImmersion_eq_map`, whose proof it follows one leg longer.

Every leg of the geometric composite is a `FormalSpectrum.locallyRingedSpaceMap`: the transitivity
isomorphism because `isoOfAdicRingEquiv`'s `hom` is `Spf` of the inverse ring isomorphism, which is
here `mapCompletion` of `awayAwayLocEquiv.symm` on the nose; the other two by
`AdicCompletion.interchangeBackward_comp_awayCompletionHom`, which fuses them into `mapCompletion`
of `R_f → (R_f)_ĝ`. Two applications of `locallyRingedSpaceMap_comp` collapse the composite to a
single map of formal spectra, `AdicCompletion.mapCompletion_comp` and
`FormalSpectrum.awayAwayLocEquiv_symm_comp_algebraMap_away` identify its ring map with
`mapCompletion (IsLocalization.Away.lift f hfg)`, and `locallyRingedSpaceMap_congr` closes the
goal, the continuity witnesses being irrelevant. -/
theorem nestedBasicOpenImmersion_eq_map (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    nestedBasicOpenImmersion I f g hI hfg =
      formalCompletion.map (hI.map (algebraMap R (Localization.Away f)))
        (hI.map (algebraMap R (Localization.Away g)))
        (IsLocalization.Away.lift (S := Localization.Away f) f hfg)
        (le_of_eq (by rw [Ideal.map_map, IsLocalization.Away.lift_comp])) := by
  haveI := FormalSpectrum.isAdicRing_awayCompletionIdeal I f hI
  haveI := FormalSpectrum.isAdicRing_awayCompletionIdeal I g hI
  haveI := FormalSpectrum.isAdicRing_awayCompletionIdeal
    (I.map (algebraMap R (Localization.Away f))) (algebraMap R (Localization.Away f) g)
    (hI.map _)
  set ψ := (awayAwayLocEquiv f g hfg).symm.toRingEquiv.toRingHom
  -- the ideal-transport witness for `ψ`, re-derived from the `have` inside
  -- `awayCompletionAwayEquiv`'s own proof
  have hB : ((I.map (algebraMap R (Localization.Away f))).map
        (algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R (Localization.Away f) g)))).map ψ ≤
      I.map (algebraMap R (Localization.Away g)) :=
    le_of_eq ((congrArg (Ideal.map ψ) (map_algebraMap_localizationAway_eq I f g)).trans
      (map_awayAwayLocEquiv_symm I f g hfg))
  -- the ring-level identity: `mapCompletion ψ` after `mapCompletion (R_f → (R_f)_ĝ)` is
  -- `mapCompletion (Away.lift f hfg)`
  have hring : (mapCompletion ψ hB (hI.map (algebraMap R (Localization.Away g)))).comp
        (mapCompletion (algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R (Localization.Away f) g)))
          (le_of_eq rfl) ((hI.map (algebraMap R (Localization.Away f))).map _)) =
      mapCompletion (IsLocalization.Away.lift (S := Localization.Away f) f hfg)
        (le_of_eq (by rw [Ideal.map_map, IsLocalization.Away.lift_comp]))
        (hI.map (algebraMap R (Localization.Away g))) := by
    refine (mapCompletion_comp _ ψ _ hB ((hI.map _).map _) (hI.map _) (hI.map _)).trans ?_
    exact mapCompletion_congr _ _ _ _ _ (awayAwayLocEquiv_symm_comp_algebraMap_away f g hfg)
  apply FormalScheme.Hom.ext'
  change (nestedChartIso I f g hI hfg).hom ≫
      (locCompletionChartIso (I.map (algebraMap R (Localization.Away f))) (hI.map _)
          (algebraMap R (Localization.Away f) g)).hom ≫
        basicOpenChart (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
          (awayPoint (I.map (algebraMap R (Localization.Away f)))
            (algebraMap R (Localization.Away f) g)) = _
  have hinner := AdicCompletion.interchangeBackward_comp_awayCompletionHom
    (I.map (algebraMap R (Localization.Away f))) (algebraMap R (Localization.Away f) g) (hI.map _)
  have h23 : idealOfDefinition (I.map (algebraMap R (Localization.Away f))) ≤
      (idealOfDefinition ((I.map (algebraMap R (Localization.Away f))).map
          (algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R (Localization.Away f) g))))).comap
        ((interchangeBackward (I.map (algebraMap R (Localization.Away f)))
              (algebraMap R (Localization.Away f) g) (hI.map _)).comp
          (awayCompletionHom (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
            (awayPoint (I.map (algebraMap R (Localization.Away f)))
              (algebraMap R (Localization.Away f) g)))) := by
    rw [hinner]
    exact Ideal.map_le_iff_le_comap.mp
      (idealOfDefinition_map_le _ (le_of_eq rfl) ((hI.map _).map _))
  have htotal : (mapCompletion ψ hB (hI.map (algebraMap R (Localization.Away g)))).comp
        ((interchangeBackward (I.map (algebraMap R (Localization.Away f)))
              (algebraMap R (Localization.Away f) g) (hI.map _)).comp
          (awayCompletionHom (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
            (awayPoint (I.map (algebraMap R (Localization.Away f)))
              (algebraMap R (Localization.Away f) g)))) =
      mapCompletion (IsLocalization.Away.lift (S := Localization.Away f) f hfg)
        (le_of_eq (by rw [Ideal.map_map, IsLocalization.Away.lift_comp]))
        (hI.map (algebraMap R (Localization.Away g))) := by
    rw [hinner]; exact hring
  have hlift : (I.map (algebraMap R (Localization.Away f))).map
      (IsLocalization.Away.lift (S := Localization.Away f) f hfg) ≤
      I.map (algebraMap R (Localization.Away g)) :=
    le_of_eq (by rw [Ideal.map_map, IsLocalization.Away.lift_comp])
  have htot : idealOfDefinition (I.map (algebraMap R (Localization.Away f))) ≤
      (idealOfDefinition (I.map (algebraMap R (Localization.Away g)))).comap
        ((mapCompletion ψ hB (hI.map (algebraMap R (Localization.Away g)))).comp
          ((interchangeBackward (I.map (algebraMap R (Localization.Away f)))
                (algebraMap R (Localization.Away f) g) (hI.map _)).comp
            (awayCompletionHom (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
              (awayPoint (I.map (algebraMap R (Localization.Away f)))
                (algebraMap R (Localization.Away f) g))))) := by
    rw [htotal]
    exact Ideal.map_le_iff_le_comap.mp (idealOfDefinition_map_le _ hlift (hI.map _))
  -- fuse the interchange and the chart map into one map of formal spectra
  have hfuse23 :
      (locCompletionChartIso (I.map (algebraMap R (Localization.Away f))) (hI.map _)
            (algebraMap R (Localization.Away f) g)).hom ≫
          basicOpenChart (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
            (awayPoint (I.map (algebraMap R (Localization.Away f)))
              (algebraMap R (Localization.Away f) g)) =
        locallyRingedSpaceMap (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
          (idealOfDefinition ((I.map (algebraMap R (Localization.Away f))).map
            (algebraMap (Localization.Away f)
              (Localization.Away (algebraMap R (Localization.Away f) g)))))
          ((interchangeBackward (I.map (algebraMap R (Localization.Away f)))
                (algebraMap R (Localization.Away f) g) (hI.map _)).comp
            (awayCompletionHom (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
              (awayPoint (I.map (algebraMap R (Localization.Away f)))
                (algebraMap R (Localization.Away f) g)))) h23 :=
    (locallyRingedSpaceMap_comp _ _ _ _ _ _ _ _).symm
  -- the transitivity isomorphism is `Spf` of `mapCompletion ψ` on the nose
  have hleg1 : (nestedChartIso I f g hI hfg).hom =
      locallyRingedSpaceMap
        (idealOfDefinition ((I.map (algebraMap R (Localization.Away f))).map
          (algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R (Localization.Away f) g)))))
        (idealOfDefinition (I.map (algebraMap R (Localization.Away g))))
        (mapCompletion ψ hB (hI.map _))
        (Ideal.map_le_iff_le_comap.mp (idealOfDefinition_map_le ψ hB (hI.map _))) := rfl
  have hfuseall :
      locallyRingedSpaceMap (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
          (idealOfDefinition (I.map (algebraMap R (Localization.Away g))))
          ((mapCompletion ψ hB (hI.map (algebraMap R (Localization.Away g)))).comp
            ((interchangeBackward (I.map (algebraMap R (Localization.Away f)))
                  (algebraMap R (Localization.Away f) g) (hI.map _)).comp
              (awayCompletionHom (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
                (awayPoint (I.map (algebraMap R (Localization.Away f)))
                  (algebraMap R (Localization.Away f) g)))))
          htot =
        locallyRingedSpaceMap
            (idealOfDefinition ((I.map (algebraMap R (Localization.Away f))).map
              (algebraMap (Localization.Away f)
                (Localization.Away (algebraMap R (Localization.Away f) g)))))
            (idealOfDefinition (I.map (algebraMap R (Localization.Away g))))
            (mapCompletion ψ hB (hI.map _))
            (Ideal.map_le_iff_le_comap.mp (idealOfDefinition_map_le ψ hB (hI.map _))) ≫
          locallyRingedSpaceMap (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
            (idealOfDefinition ((I.map (algebraMap R (Localization.Away f))).map
              (algebraMap (Localization.Away f)
                (Localization.Away (algebraMap R (Localization.Away f) g)))))
            ((interchangeBackward (I.map (algebraMap R (Localization.Away f)))
                  (algebraMap R (Localization.Away f) g) (hI.map _)).comp
              (awayCompletionHom (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
                (awayPoint (I.map (algebraMap R (Localization.Away f)))
                  (algebraMap R (Localization.Away f) g)))) h23 :=
    locallyRingedSpaceMap_comp _ _ _ _ _ _ _ _
  rw [hleg1, hfuse23]
  exact hfuseall.symm.trans (locallyRingedSpaceMap_congr _ _ _ _ _ _ htotal)

/-- **The `toSpec` square over a nested basic open** (EGA I, 10.8): completing `Spec R_g = D(g)`
along `V(I·R_g)` and mapping to `Spec R_g`, then to `Spec R_f`, is the same as including the
completion of `D(g)` into the completion of `D(f)` and then mapping to `Spec R_f`.

This is the overlap-level form of the compatibility a global morphism `X_{/Y} ⟶ X` glues from: on a
separated scheme the affine charts of the completion glue along common basic opens `D(g) ⊆ D(f)`,
and this says the canonical morphisms of the two affine completions agree over such an overlap.
`formalCompletion.basicOpenImmersion_comp_toSpec` is the chart-level form; a gluing argument needs
both.

Given `nestedBasicOpenImmersion_eq_map` it is exactly `formalCompletion.map_comp_toSpec`, the
naturality of `toSpec` in the pair `(Spec R, V(I))`. -/
theorem nestedBasicOpenImmersion_comp_toSpec (hI : I.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f)) :
    (nestedBasicOpenImmersion I f g hI hfg).toLRSHom ≫
        toSpec (Localization.Away f) (I.map (algebraMap R (Localization.Away f))) (hI.map _) =
      toSpec (Localization.Away g) (I.map (algebraMap R (Localization.Away g))) (hI.map _) ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom
          (IsLocalization.Away.lift (S := Localization.Away f) f hfg)) := by
  rw [nestedBasicOpenImmersion_eq_map]
  exact map_comp_toSpec (hI.map (algebraMap R (Localization.Away f)))
    (hI.map (algebraMap R (Localization.Away g)))
    (IsLocalization.Away.lift (S := Localization.Away f) f hfg)
    (le_of_eq (by rw [Ideal.map_map, IsLocalization.Away.lift_comp]))

end formalCompletion
