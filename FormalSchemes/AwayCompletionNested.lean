import FormalSchemes.AdicCompletionCongrIdealAlg
import FormalSchemes.AwayCompletionInterchange

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The nested basic-open chart, as an `R`-algebra isomorphism

Let `(R, I)` be an adic base, `A` an `R`-algebra and `f g : A` with `D(g) ⊆ D(f)`. The two ways of
reading the sections over `D(g)` — directly on `Spf A`, or through the affine basic-open chart
`Spf (A{1/f}) ↪ Spf A` — give the completed localizations

```
A{1/g}          and          A{1/f}{1/ḡ}
```

and these agree. At the **ring** level this is already on master, built for issue 163's `c_iso`
route: `FormalSpectrum.awayCompletionChartEquiv` (`FormalSchemes.AwayCompletionInterchange`),
which composes the localization transitivity `FormalSpectrum.awayCompletionAwayEquiv` with the
completion–localization interchange `AdicCompletion.awayCompletionInterchange`.

What the affine-charted glue data of EGA I §10.7 need, however, is an **`R`-algebra** isomorphism:
the `τ` field of `AlgebraicGeometry.AffineChartedFibreDatum`
(`FormalSchemes.GeneralFibreProductAffineBase`) is an `≃ₐ[R]`, not a `≃+*`. This file supplies that
upgrade, together with the ideal-convention bridge that makes the result's *type* the one a datum
consumes.

## Contents

* `FormalSpectrum.awayCompletionAwayEquiv_algebraMap` and
  `FormalSpectrum.awayCompletionChartEquiv_algebraMap`: the two existing ring isomorphisms fix the
  structural image of `A`. These are the computational content of the upgrade.
* `FormalSpectrum.awayCompletionChartAlgEquiv`: the `≃ₐ[R]` upgrade of `awayCompletionChartEquiv`,
  with `…_algebraMap` and `…_symm_algebraMap`.
* `FormalSpectrum.map_algebraMap_awayCompletion_eq`: the ideal-convention bridge
  `I·A{1/f} = awayCompletionIdeal (I·A) f`, i.e. the ideal of definition of the chart algebra is the
  one the datum's `I.map (algebraMap R (A i))` spelling produces.
* `FormalSpectrum.awayCompletionNestedAlgEquiv`, and its `g := f · g` specialisation
  `awayCompletionNestedMulAlgEquiv`: the same isomorphism with its target transported along that
  bridge — the form an affine-charted datum whose charts are `A i := A{1/f_i}` consumes, where the
  overlap of the `i`-th and `j`-th chart is `D(f_i · f_j) ⊆ D(f_i)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4), §10.7.
-/

noncomputable section

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A : Type u} [CommRing A] [Algebra R A]

/-- **The localization transitivity fixes `A`.** `awayCompletionAwayEquiv` is the completion of the
`A`-algebra equivalence `awayAwayLocEquiv`, so it carries `algebraMap A A{1/g}` to
`algebraMap A (A_f){1/ḡ}`. -/
theorem awayCompletionAwayEquiv_algebraMap (J : Ideal A) (f g : A) (hJ : J.FG)
    (hfg : IsUnit (algebraMap A (Localization.Away g) f)) (a : A) :
    awayCompletionAwayEquiv J f g hJ hfg (algebraMap A (awayCompletion J g) a) =
      algebraMap A (awayCompletion (J.map (algebraMap A (Localization.Away f)))
        (algebraMap A (Localization.Away f) g)) a := by
  have hA : (J.map (algebraMap A (Localization.Away g))).map
      (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom ≤
      (J.map (algebraMap A (Localization.Away f))).map
        (algebraMap (Localization.Away f)
          (Localization.Away (algebraMap A (Localization.Away f) g))) :=
    le_of_eq ((map_awayAwayLocEquiv J f g hfg).trans
      (map_algebraMap_localizationAway_eq J f g).symm)
  have key : (awayCompletionAwayEquiv J f g hJ hfg).toRingHom =
      AdicCompletion.mapCompletion (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom hA
        ((hJ.map _).map _) := rfl
  have happ : awayCompletionAwayEquiv J f g hJ hfg (algebraMap A (awayCompletion J g) a) =
      AdicCompletion.mapCompletion (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom hA
        ((hJ.map _).map _) (algebraMap A (awayCompletion J g) a) :=
    RingHom.congr_fun key _
  have hcomm := RingHom.congr_fun (awayAwayLocEquiv_comp_algebraMap f g hfg) a
  rw [RingHom.comp_apply] at hcomm
  rw [happ, IsScalarTower.algebraMap_apply A (Localization.Away g) (awayCompletion J g),
    AdicCompletion.mapCompletion_algebraMap, hcomm,
    ← IsScalarTower.algebraMap_apply A
      (Localization.Away (algebraMap A (Localization.Away f) g))
      (awayCompletion (J.map (algebraMap A (Localization.Away f)))
        (algebraMap A (Localization.Away f) g))]

/-- **The nested-chart ring isomorphism fixes `A`.** Both halves do: the localization transitivity
by `awayCompletionAwayEquiv_algebraMap`, and the completion–localization interchange because its
forward map is `AdicCompletion.mapCompletion` of `locTransition`, which sends the structural image
of the base ring to the structural image (`interchangeForward_algebraMap`,
`locTransition_algebraMap`). -/
theorem awayCompletionChartEquiv_algebraMap (J : Ideal A) (f g : A) (hJ : J.FG)
    (hfg : IsUnit (algebraMap A (Localization.Away g) f)) (a : A) :
    awayCompletionChartEquiv J f g hJ hfg (algebraMap A (awayCompletion J g) a) =
      algebraMap A (awayCompletion (awayCompletionIdeal J f) (awayCompletionHom J f g)) a := by
  have key : ∀ x, awayCompletionChartEquiv J f g hJ hfg x =
      AdicCompletion.interchangeForward (J.map (algebraMap A (Localization.Away f)))
        (algebraMap A (Localization.Away f) g) (hJ.map _)
        (awayCompletionAwayEquiv J f g hJ hfg x) := fun _ => rfl
  rw [key, awayCompletionAwayEquiv_algebraMap,
    IsScalarTower.algebraMap_apply A (Localization.Away (algebraMap A (Localization.Away f) g))
      (awayCompletion (J.map (algebraMap A (Localization.Away f)))
        (algebraMap A (Localization.Away f) g)),
    IsScalarTower.algebraMap_apply A (Localization.Away f)
      (Localization.Away (algebraMap A (Localization.Away f) g)),
    AdicCompletion.interchangeForward_algebraMap, AdicCompletion.locTransition_algebraMap,
    AdicCompletion.toLocCompletion_apply,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]
  rfl

/-! ### The `R`-algebra upgrade -/

/-- **The nested basic-open chart identification as an `R`-algebra isomorphism**
`A{1/g} ≃ₐ[R] A{1/f}{1/ḡ}`, for `D(g) ⊆ D(f)` (encoded as `f` being a unit in `A_g`). The upgrade
of `awayCompletionChartEquiv`: it fixes `A`, hence a fortiori the image of `R`. -/
def awayCompletionChartAlgEquiv (hI : I.FG) (f g : A)
    (hfg : IsUnit (algebraMap A (Localization.Away g) f)) :
    awayCompletion (I.map (algebraMap R A)) g ≃ₐ[R]
      awayCompletion (awayCompletionIdeal (I.map (algebraMap R A)) f)
        (awayCompletionHom (I.map (algebraMap R A)) f g) :=
  AlgEquiv.ofRingEquiv
    (f := awayCompletionChartEquiv (I.map (algebraMap R A)) f g (hI.map _) hfg)
    fun r => by
      rw [IsScalarTower.algebraMap_apply R A (awayCompletion (I.map (algebraMap R A)) g),
        awayCompletionChartEquiv_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- **The ideal-convention bridge.** The ideal of definition of the chart algebra `A{1/f}`, spelled
as an affine-charted datum spells it (`I.map (algebraMap R (A i))`), is the `awayCompletionIdeal`
of the chart. Both are the image of `I` under `R → A → A_f → A{1/f}`. -/
theorem map_algebraMap_awayCompletion_eq (f : A) :
    I.map (algebraMap R (awayCompletion (I.map (algebraMap R A)) f)) =
      awayCompletionIdeal (I.map (algebraMap R A)) f := by
  rw [IsScalarTower.algebraMap_eq R A (awayCompletion (I.map (algebraMap R A)) f),
    ← Ideal.map_map]
  exact map_awayCompletionHom (I.map (algebraMap R A)) f

/-- The `R`-algebra upgrade still fixes `A` (restatement of
`awayCompletionChartEquiv_algebraMap` at the upgraded map). -/
theorem awayCompletionChartAlgEquiv_algebraMap (hI : I.FG) (f g : A)
    (hfg : IsUnit (algebraMap A (Localization.Away g) f)) (a : A) :
    awayCompletionChartAlgEquiv I hI f g hfg (algebraMap A (awayCompletion (I.map
        (algebraMap R A)) g) a) =
      algebraMap A (awayCompletion (awayCompletionIdeal (I.map (algebraMap R A)) f)
        (awayCompletionHom (I.map (algebraMap R A)) f g)) a :=
  awayCompletionChartEquiv_algebraMap (I.map (algebraMap R A)) f g (hI.map _) hfg a

/-- The inverse of the `R`-algebra upgrade fixes `A`. -/
theorem awayCompletionChartAlgEquiv_symm_algebraMap (hI : I.FG) (f g : A)
    (hfg : IsUnit (algebraMap A (Localization.Away g) f)) (a : A) :
    (awayCompletionChartAlgEquiv I hI f g hfg).symm
        (algebraMap A (awayCompletion (awayCompletionIdeal (I.map (algebraMap R A)) f)
          (awayCompletionHom (I.map (algebraMap R A)) f g)) a) =
      algebraMap A (awayCompletion (I.map (algebraMap R A)) g) a :=
  (AlgEquiv.symm_apply_eq _).mpr (awayCompletionChartAlgEquiv_algebraMap I hI f g hfg a).symm

/-! ### The form consumed by a chart datum -/

/-- **The nested chart identification in the datum's ideal convention.** The same isomorphism as
`awayCompletionChartAlgEquiv`, with its target's ideal of definition spelled
`I.map (algebraMap R (A{1/f}))` rather than `awayCompletionIdeal (I·A) f`, transported along
`map_algebraMap_awayCompletion_eq`. This is the form consumed by an affine-charted datum whose
`i`-th chart algebra is `A{1/f_i}`. -/
def awayCompletionNestedAlgEquiv (hI : I.FG) (f g : A)
    (hfg : IsUnit (algebraMap A (Localization.Away g) f)) :
    awayCompletion (I.map (algebraMap R A)) g ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (awayCompletion (I.map (algebraMap R A)) f)))
        (awayCompletionHom (I.map (algebraMap R A)) f g) :=
  (awayCompletionChartAlgEquiv I hI f g hfg).trans
    (AdicCompletion.congrIdealₐ R
      (congrArg (Ideal.map (algebraMap (awayCompletion (I.map (algebraMap R A)) f)
          (Localization.Away (awayCompletionHom (I.map (algebraMap R A)) f g))))
        (map_algebraMap_awayCompletion_eq I f).symm))

/-- **The overlap case.** For the overlap `D(f · g) ⊆ D(f)` of two basic opens of `Spf A`, the
chart-level completed localization `A{1/f}{1/(f·g)}` is identified with `A{1/(f·g)}` as an
`R`-algebra. This is the instance an open-cover datum uses, with `f = f_i` and `g = f_j`: it turns
the two chart-local presentations of the overlap into one common `A{1/(f_i·f_j)}`. -/
def awayCompletionNestedMulAlgEquiv (hI : I.FG) (f g : A) :
    awayCompletion (I.map (algebraMap R A)) (f * g) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (awayCompletion (I.map (algebraMap R A)) f)))
        (awayCompletionHom (I.map (algebraMap R A)) f (f * g)) :=
  awayCompletionNestedAlgEquiv I hI f (f * g)
    (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (f * g)) (f * g)
      (dvd_mul_right f g))

/-- The transported isomorphism still fixes `A`; the transport contributes nothing because
`congrIdealₐ` is `subst`-built. -/
theorem awayCompletionNestedAlgEquiv_algebraMap (hI : I.FG) (f g : A)
    (hfg : IsUnit (algebraMap A (Localization.Away g) f)) (a : A) :
    awayCompletionNestedAlgEquiv I hI f g hfg
        (algebraMap A (awayCompletion (I.map (algebraMap R A)) g) a) =
      algebraMap A (awayCompletion (I.map (algebraMap R (awayCompletion
        (I.map (algebraMap R A)) f))) (awayCompletionHom (I.map (algebraMap R A)) f g)) a := by
  rw [awayCompletionNestedAlgEquiv, AlgEquiv.trans_apply, awayCompletionChartAlgEquiv_algebraMap,
    IsScalarTower.algebraMap_apply A
      (Localization.Away (awayCompletionHom (I.map (algebraMap R A)) f g))
      (awayCompletion (awayCompletionIdeal (I.map (algebraMap R A)) f)
        (awayCompletionHom (I.map (algebraMap R A)) f g)),
    AdicCompletion.congrIdealₐ_algebraMap, ← IsScalarTower.algebraMap_apply]

end FormalSpectrum

end
