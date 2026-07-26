import FormalSchemes.BasicOpenImmersion
import FormalSchemes.CofinalCompletionFunctorial

set_option linter.style.header false

/-!
# Basis-restriction naturality of the ideal-independence comparison (ring level)

For an adic ring `R` with two ideals of definition `I ≤ J` (both finitely generated, `J` cofinal in
`I`), `FormalSchemes/CofinalSheafComparison.lean` builds — on each basic open `D(f)` — the
ring-of-sections comparison isomorphism `AdicCompletion.cofinalRingEquiv` between the two structure
sheaves, and `FormalSchemes/CofinalSheafComparisonNaturality.lean` proves the naturality square for
the special restriction `D(g) ⊆ ⊤`.

Gluing those pointwise comparisons into a genuine sheaf isomorphism over the whole distinguished
basis needs the naturality square for an **arbitrary** basic inclusion `D(g) ⊆ D(f)`. There is no
canonical ring map `R_f → R_g` for such an inclusion, so the transition is carried by the
completed-localization transitivity isomorphism `FormalSpectrum.awayCompletionAwayEquiv`
(`R{1/g} ≃+* R_f{1/ḡ}`, in `FormalSchemes/AwayCompletionAway.lean`). This file supplies the
missing
ring-level compatibility: the square

```
R{1/g}     --cofinalHom hb-->    (via J·R_g) R{1/g}
   |  awayCompletionAwayEquiv I           |  awayCompletionAwayEquiv J
R_f{1/ḡ}   --cofinalHom hb'-->   (via J·R_f{1/ḡ}) R_f{1/ḡ}
```

commutes, where `hb`, `hb'` are the `K ^ 1 ≤ L` cofinality inputs coming from `I ≤ J`.

The proof is a direct instance of the already-merged naturality lemma
`AdicCompletion.mapCompletion_comp_cofinalHom`: by construction
`awayCompletionAwayEquiv X f g hX hfg` is `AdicCompletion.mapCompletion φ _ _` for the single ring
map `φ = awayAwayLocEquiv f g hfg` (independent of the ideal of definition `X`), so the square is
exactly that lemma applied to `φ`, `b = 1`, and the two ideals of definition on each side.

## Main results

* `FormalSpectrum.awayCompletionAwayEquiv_comp_cofinalHom`: the commuting square (composition form).
* `FormalSpectrum.cofinalHom_comm_awayCompletionAwayEquiv`: the same, applied to an element (the
  form consumed by the eventual sheaf gluing).

## Scope note

Only the ring-level compatibility is proved here. Assembling these squares (together with the
`⊤ → D(g)` square) through the structure-sheaf restriction maps into a single
`PresheafedSpace`/`LocallyRingedSpace` isomorphism `Spf_I R ≅ Spf_J R` over the base homeomorphism
remains the category-theoretically heavy follow-up named in `CofinalSheafComparison.lean`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], §10.3.
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

noncomputable section

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I J : Ideal R) (f g : R)

/-- **Basis-restriction naturality of the ideal-independence comparison (composition form).** For
two finitely generated ideals of definition `I`, `J` and a basic inclusion `D(g) ⊆ D(f)` (encoded
by `hfg : IsUnit (algebraMap R R_g f)`), the completed-localization transition isomorphism
`awayCompletionAwayEquiv` intertwines the cofinal comparison maps `cofinalHom` for the two ideals of
definition on `R{1/g}` and on `R_f{1/ḡ}`:
```
awayCompletionAwayEquiv J ∘ cofinalHom hb = cofinalHom hb' ∘ awayCompletionAwayEquiv I.
```
Since `awayCompletionAwayEquiv X f g hX hfg` is `AdicCompletion.mapCompletion φ _ _` for the single
ring map `φ = awayAwayLocEquiv f g hfg`, this is a direct instance of the naturality lemma
`AdicCompletion.mapCompletion_comp_cofinalHom` applied to `φ` and `b = 1`. -/
theorem awayCompletionAwayEquiv_comp_cofinalHom (hI : I.FG) (hJ : J.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f))
    (hb : (I.map (algebraMap R (Localization.Away g))) ^ 1 ≤
          J.map (algebraMap R (Localization.Away g)))
    (hb' : ((I.map (algebraMap R (Localization.Away f))).map
              (algebraMap (Localization.Away f)
                (Localization.Away (algebraMap R (Localization.Away f) g)))) ^ 1 ≤
           (J.map (algebraMap R (Localization.Away f))).map
              (algebraMap (Localization.Away f)
                (Localization.Away (algebraMap R (Localization.Away f) g)))) :
    (awayCompletionAwayEquiv J f g hJ hfg).toRingHom.comp (AdicCompletion.cofinalHom hb) =
      (AdicCompletion.cofinalHom hb').comp
        (awayCompletionAwayEquiv I f g hI hfg).toRingHom :=
  AdicCompletion.mapCompletion_comp_cofinalHom
    (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom hb hb'
    (le_of_eq ((map_awayAwayLocEquiv I f g hfg).trans
      (map_algebraMap_localizationAway_eq I f g).symm))
    (le_of_eq ((map_awayAwayLocEquiv J f g hfg).trans
      (map_algebraMap_localizationAway_eq J f g).symm))
    (hI.map _) ((hI.map _).map _) (hJ.map _) ((hJ.map _).map _)

/-- **Basis-restriction naturality of the ideal-independence comparison (applied form).** The
element-level statement of `awayCompletionAwayEquiv_comp_cofinalHom`, the form consumed by the
eventual structure-sheaf gluing on the distinguished basis. -/
theorem cofinalHom_comm_awayCompletionAwayEquiv (hI : I.FG) (hJ : J.FG)
    (hfg : IsUnit (algebraMap R (Localization.Away g) f))
    (hb : (I.map (algebraMap R (Localization.Away g))) ^ 1 ≤
          J.map (algebraMap R (Localization.Away g)))
    (hb' : ((I.map (algebraMap R (Localization.Away f))).map
              (algebraMap (Localization.Away f)
                (Localization.Away (algebraMap R (Localization.Away f) g)))) ^ 1 ≤
           (J.map (algebraMap R (Localization.Away f))).map
              (algebraMap (Localization.Away f)
                (Localization.Away (algebraMap R (Localization.Away f) g))))
    (x : awayCompletion I g) :
    awayCompletionAwayEquiv J f g hJ hfg (AdicCompletion.cofinalHom hb x) =
      AdicCompletion.cofinalHom hb' (awayCompletionAwayEquiv I f g hI hfg x) := by
  have h := RingHom.congr_fun
    (awayCompletionAwayEquiv_comp_cofinalHom I J f g hI hJ hfg hb hb') x
  rwa [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.coe_toRingHom] at h

end FormalSpectrum

end
