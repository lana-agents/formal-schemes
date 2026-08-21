import FormalSchemes.AwayCompletionCongrEquiv
import FormalSchemes.AwayCompletionNested

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Naturality of the nested basic-open chart identification

Fix an adic base `(R, I)` and an `R`-algebra `A`. For `D(g) ⊆ D(f)` in `Spf A` the sections over
`D(g)` can be read either directly on `Spf A` or through the affine chart `Spf A{1/f}`, and the two
readings agree: that is `FormalSpectrum.awayCompletionNestedAlgEquiv` (issue 607),

```
N_{f,g} :  A{1/g}  ≃ₐ[R]  A{1/f}{1/ḡ} ,        ḡ = awayCompletionHom (I·A) f g .
```

This file proves that `N` is **natural in `g`**: for `D(h) ⊆ D(g) ⊆ D(f)` the square

```
        A{1/g}   --N_{f,g}-->   A{1/f}{1/ḡ}
           |                         |
   awayCongrHom g h            awayCongrHom ḡ h̄
           v                         v
        A{1/h}   --N_{f,h}-->   A{1/f}{1/h̄}
```

commutes (`FormalSpectrum.awayCongrHom_nested`). This is what an affine-charted glue datum whose
`i`-th chart algebra is `A{1/f_i}` needs: its `hστ` obligation compares the two chart-local
presentations of a double overlap, and both legs are comparison maps *after* transporting through
`N`.

## Why the existing rigidity does not suffice

`CompletedTensorAwayInterchange.furtherLocAlgHom_eq_awayCongrHom`
(`FormalSchemes.AwayCompletionCongrEquiv`) says that any completed localization map
`A{1/x} →ₐ[R] A{1/y}` induced by an `A`-compatible localization map is *the* comparison map. It is
phrased with source and target both of the form `awayCompletion (I·A) s`, over one fixed base ring
`A`. The square above crosses the base change `A ⇝ A{1/f}`, so it is outside that statement's
scope.

The generalisation is cheap, because the proof never used the target: it is
`IsLocalization.ringHom_ext` on the *source* localization, plus proof irrelevance in the remaining
`Prop` arguments of `AdicCompletion.mapCompletion`. That is
`AdicCompletion.mapCompletion_congr_localizationAway` below — two completed maps out of
`A{1/s}` into **any** completion agree as soon as their underlying localization maps agree on the
image of `A`.

The rest of the file makes the square's two legs literally of that shape. Every map involved is a
`mapCompletion`: `awayCompletionAwayEquiv` is `mapCompletion` of the localization transitivity
`awayAwayLocEquiv` (definitionally), `AdicCompletion.interchangeForward` is `mapCompletion` of
`AdicCompletion.locTransition` (definitionally), `awayCongrHom` is `mapCompletion` of
`IsLocalization.Away.lift`, and the ideal transport `AdicCompletion.congrIdealₐ` is absorbed by
`congrIdealₐ_mapCompletion`. So `AdicCompletion.mapCompletion_comp` collapses each leg to a
single `mapCompletion`, and the two underlying maps agree on `A` by `nestedLocHom_algebraMap`.

Note that only the **forward** direction of `N` is used: the backward direction is
`AdicCompletion.interchangeBackward`, an `AdicCompletion.extendRingHom`, which is *not* of the
shape the rigidity consumes. Consumers should arrange their goals so that only forward directions
appear (`F ∘ e.symm = G` ⟺ `F = G ∘ e`) before applying anything here.

## Main definitions and results

* `AdicCompletion.mapCompletion_congr_localizationAway`: the generalised rigidity — an arbitrary
  target.
* `AdicCompletion.congrIdealₐ_mapCompletion`: the ideal transport absorbed into a
  `mapCompletion`.
* `FormalSpectrum.nestedLocHom`, `nestedLocHom_algebraMap`: the base-ring map underlying `N`, and
  its value on the image of `A`.
* `FormalSpectrum.awayCompletionChartEquiv_toRingHom_eq`,
  `FormalSpectrum.awayCompletionNestedAlgEquiv_apply_eq`: `N` is a single `mapCompletion`.
* `FormalSpectrum.awayCongrHom_nested`: **the naturality square**.
* `FormalSpectrum.awayCongrHom_nestedCongr`: the packaged form, in which the target's away element
  is adjusted by a further comparison isomorphism — the form a three-chart open-cover datum
  consumes.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4), §10.7.
-/

noncomputable section

open FormalSpectrum CompletedTensorAwayInterchange

universe u

namespace FormalSpectrum

variable {A : Type u} [CommRing A] (J : Ideal A) (f g : A)

/-- **The base-ring map underlying the nested basic-open chart identification**
`A_g → (A{1/f})_ḡ`: the localization transitivity `A_g ≃ (A_f)_ḡ` followed by the
localize-the-completion map `AdicCompletion.locTransition`. -/
def nestedLocHom (hfg : IsUnit (algebraMap A (Localization.Away g) f)) :
    Localization.Away g →+* Localization.Away (awayCompletionHom J f g) :=
  (AdicCompletion.locTransition (J.map (algebraMap A (Localization.Away f)))
      (algebraMap A (Localization.Away f) g)).comp
    (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom

/-- **`nestedLocHom` fixes `A`**: it carries the structural image of `a : A` in `A_g` to its
structural image in `(A{1/f})_ḡ`, through the chart map `A → A{1/f}`. This is the whole
computational content of the naturality below. -/
theorem nestedLocHom_algebraMap (hfg : IsUnit (algebraMap A (Localization.Away g) f)) (a : A) :
    nestedLocHom J f g hfg (algebraMap A (Localization.Away g) a) =
      algebraMap (awayCompletion J f) (Localization.Away (awayCompletionHom J f g))
        (awayCompletionHom J f a) := by
  have h1 : (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom
      (algebraMap A (Localization.Away g) a) =
      algebraMap (Localization.Away f)
        (Localization.Away (algebraMap A (Localization.Away f) g))
        (algebraMap A (Localization.Away f) a) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact RingHom.congr_fun (awayAwayLocEquiv_comp_algebraMap f g hfg) a
  have h2 : AdicCompletion.locTransition (J.map (algebraMap A (Localization.Away f)))
        (algebraMap A (Localization.Away f) g)
        (algebraMap (Localization.Away f)
          (Localization.Away (algebraMap A (Localization.Away f) g))
          (algebraMap A (Localization.Away f) a)) =
      AdicCompletion.toLocCompletion (J.map (algebraMap A (Localization.Away f)))
        (algebraMap A (Localization.Away f) g) (algebraMap A (Localization.Away f) a) :=
    AdicCompletion.locTransition_algebraMap _ _ _
  calc nestedLocHom J f g hfg (algebraMap A (Localization.Away g) a)
      = AdicCompletion.locTransition (J.map (algebraMap A (Localization.Away f)))
          (algebraMap A (Localization.Away f) g)
          ((awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom
            (algebraMap A (Localization.Away g) a)) := rfl
    _ = _ := by rw [h1, h2, AdicCompletion.toLocCompletion_apply]; rfl

/-- `nestedLocHom` carries the ideal of definition of `A_g` into that of `(A{1/f})_ḡ`, so it
induces a map of completions. -/
theorem nestedLocHom_map_le (hfg : IsUnit (algebraMap A (Localization.Away g) f)) :
    (J.map (algebraMap A (Localization.Away g))).map (nestedLocHom J f g hfg) ≤
      (awayCompletionIdeal J f).map
        (algebraMap (awayCompletion J f) (Localization.Away (awayCompletionHom J f g))) := by
  rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, nestedLocHom_algebraMap]
  refine Ideal.mem_map_of_mem _ ?_
  have h := Ideal.mem_map_of_mem (awayCompletionHom J f) ha
  rwa [map_awayCompletionHom] at h

/-- **The nested-chart ring isomorphism is a single `mapCompletion`**, namely of `nestedLocHom`.
Both of its factors are: `awayCompletionAwayEquiv` is `mapCompletion` of `awayAwayLocEquiv` and
`AdicCompletion.interchangeForward` is `mapCompletion` of `AdicCompletion.locTransition`, both
definitionally, so `AdicCompletion.mapCompletion_comp` collapses the composite. -/
theorem awayCompletionChartEquiv_toRingHom_eq (hJ : J.FG)
    (hfg : IsUnit (algebraMap A (Localization.Away g) f))
    (hle : (J.map (algebraMap A (Localization.Away g))).map (nestedLocHom J f g hfg) ≤
      (awayCompletionIdeal J f).map
        (algebraMap (awayCompletion J f) (Localization.Away (awayCompletionHom J f g))))
    (hFG : ((awayCompletionIdeal J f).map
      (algebraMap (awayCompletion J f) (Localization.Away (awayCompletionHom J f g)))).FG) :
    (awayCompletionChartEquiv J f g hJ hfg).toRingHom =
      AdicCompletion.mapCompletion (nestedLocHom J f g hfg) hle hFG := by
  have h1 : (awayCompletionChartEquiv J f g hJ hfg).toRingHom =
      (AdicCompletion.interchangeForward (J.map (algebraMap A (Localization.Away f)))
          (algebraMap A (Localization.Away f) g) (hJ.map _)).comp
        (AdicCompletion.mapCompletion (awayAwayLocEquiv f g hfg).toRingEquiv.toRingHom
          (le_of_eq ((map_awayAwayLocEquiv J f g hfg).trans
            (map_algebraMap_localizationAway_eq J f g).symm))
          ((hJ.map _).map _)) := rfl
  rw [h1, AdicCompletion.interchangeForward, AdicCompletion.mapCompletion_comp _ _ _ _
    ((hJ.map _).map _) _ (hJ.map _)]
  rfl

end FormalSpectrum

namespace AdicCompletion

/-- **Generalised rigidity of completed localization maps.** Two completions of ring maps out of
`Localization.Away s` into an **arbitrary** completion agree as soon as the underlying maps agree
on the image of `A`. This is `CompletedTensorAwayInterchange.furtherLocAlgHom_congr` with the
target freed: that proof only ever used `IsLocalization.ringHom_ext` at the source, plus proof
irrelevance in `mapCompletion`'s remaining `Prop` arguments. -/
theorem mapCompletion_congr_localizationAway {A : Type u} [CommRing A] (s : A)
    {K : Ideal (Localization.Away s)} {C : Type u} [CommRing C] {K' : Ideal C} (hK' : K'.FG)
    (ρ₁ ρ₂ : Localization.Away s →+* C) (h₁ : K.map ρ₁ ≤ K') (h₂ : K.map ρ₂ ≤ K')
    (h : ρ₁.comp (algebraMap A (Localization.Away s)) =
      ρ₂.comp (algebraMap A (Localization.Away s))) :
    mapCompletion ρ₁ h₁ hK' = mapCompletion ρ₂ h₂ hK' := by
  obtain rfl : ρ₁ = ρ₂ := IsLocalization.ringHom_ext (Submonoid.powers s) h
  rfl

/-- **The ideal transport is absorbed into the map.** Post-composing a `mapCompletion` with the
`subst`-built transport `congrIdealₐ` along an equality of target ideals is again the same
`mapCompletion`, read with the other ideal. -/
theorem congrIdealₐ_mapCompletion {B : Type u} [CommRing B] (R : Type u) [CommRing R]
    [Algebra R B] {K₁ K₂ : Ideal B} (h : K₁ = K₂)
    {A' : Type u} [CommRing A'] {J : Ideal A'} (ρ : A' →+* B)
    (hle₁ : J.map ρ ≤ K₁) (hle₂ : J.map ρ ≤ K₂) (hK₁ : K₁.FG) (hK₂ : K₂.FG)
    (x : AdicCompletion J A') :
    congrIdealₐ R h (mapCompletion ρ hle₁ hK₁ x) = mapCompletion ρ hle₂ hK₂ x := by
  subst h; rfl

end AdicCompletion

namespace FormalSpectrum

open CompletedTensorAwayInterchange

variable {R : Type u} [CommRing R] (I : Ideal R) {A : Type u} [CommRing A] [Algebra R A]

/-- `nestedLocHom_map_le` in the ideal convention a chart datum uses (`I.map (algebraMap R A{1/f})`
in place of `awayCompletionIdeal (I·A) f`). -/
theorem nestedLocHom_map_le' (f g : A)
    (hfg : IsUnit (algebraMap A (Localization.Away g) f)) :
    ((I.map (algebraMap R A)).map (algebraMap A (Localization.Away g))).map
        (nestedLocHom (I.map (algebraMap R A)) f g hfg) ≤
      (I.map (algebraMap R (awayCompletion (I.map (algebraMap R A)) f))).map
        (algebraMap (awayCompletion (I.map (algebraMap R A)) f)
          (Localization.Away (awayCompletionHom (I.map (algebraMap R A)) f g))) := by
  rw [map_algebraMap_awayCompletion_eq I f]
  exact nestedLocHom_map_le (I.map (algebraMap R A)) f g hfg

/-- **The nested chart identification, in the datum's ideal convention, is a single
`mapCompletion`** — the `R`-algebra upgrade and the ideal transport contribute nothing. -/
theorem awayCompletionNestedAlgEquiv_apply_eq (hI : I.FG) (f g : A)
    (hfg : IsUnit (algebraMap A (Localization.Away g) f))
    (hle : ((I.map (algebraMap R A)).map (algebraMap A (Localization.Away g))).map
        (nestedLocHom (I.map (algebraMap R A)) f g hfg) ≤
      (I.map (algebraMap R (awayCompletion (I.map (algebraMap R A)) f))).map
        (algebraMap (awayCompletion (I.map (algebraMap R A)) f)
          (Localization.Away (awayCompletionHom (I.map (algebraMap R A)) f g))))
    (hFG : ((I.map (algebraMap R (awayCompletion (I.map (algebraMap R A)) f))).map
        (algebraMap (awayCompletion (I.map (algebraMap R A)) f)
          (Localization.Away (awayCompletionHom (I.map (algebraMap R A)) f g)))).FG)
    (x : awayCompletion (I.map (algebraMap R A)) g) :
    awayCompletionNestedAlgEquiv I hI f g hfg x =
      AdicCompletion.mapCompletion (nestedLocHom (I.map (algebraMap R A)) f g hfg) hle hFG x := by
  rw [awayCompletionNestedAlgEquiv, AlgEquiv.trans_apply]
  have h2 : awayCompletionChartAlgEquiv I hI f g hfg x =
      (awayCompletionChartEquiv (I.map (algebraMap R A)) f g (hI.map _) hfg).toRingHom x := rfl
  rw [h2, awayCompletionChartEquiv_toRingHom_eq (I.map (algebraMap R A)) f g (hI.map _) hfg
      (nestedLocHom_map_le _ f g hfg)
      (AdicCompletion.completionLocIdeal_fg _ _ ((hI.map (algebraMap R A)).map _))]
  exact AdicCompletion.congrIdealₐ_mapCompletion R _ _ _ _ _ _ x

/-- The comparison map is a `mapCompletion` of `IsLocalization.Away.lift` (definitionally). -/
theorem awayCongrHom_apply_eq (hI : I.FG) (f g : A)
    (hfg : IsUnit (algebraMap A (Localization.Away g) f))
    (x : awayCompletion (I.map (algebraMap R A)) f) :
    awayCongrHom I f g hI hfg x =
      AdicCompletion.mapCompletion (IsLocalization.Away.lift f hfg)
        (le_of_eq (by rw [Ideal.map_map, IsLocalization.Away.lift_comp]))
        ((hI.map (algebraMap R A)).map (algebraMap A (Localization.Away g))) x := rfl

/-- The comparison isomorphism applied to a point is the comparison map applied to it. -/
theorem awayCongrEquiv_apply_eq (hI : I.FG) (a b : A)
    (hab : IsUnit (algebraMap A (Localization.Away b) a))
    (hba : IsUnit (algebraMap A (Localization.Away a) b))
    (x : awayCompletion (I.map (algebraMap R A)) a) :
    awayCongrEquiv I a b hI hab hba x = awayCongrHom I a b hI hab x := rfl

/-- **The naturality square.** For `D(h) ⊆ D(g) ⊆ D(f)` in `Spf A`, the nested basic-open chart
identification `N_{f,·} : A{1/·} ≃ₐ[R] A{1/f}{1/·̄}` intertwines the comparison map
`A{1/g} → A{1/h}` downstairs with the comparison map `A{1/f}{1/ḡ} → A{1/f}{1/h̄}` in the chart.

Both sides are `AdicCompletion.mapCompletion` of ring maps `A_g → (A{1/f})_h̄` which agree on the
image of `A` (`nestedLocHom_algebraMap` and `IsLocalization.Away.lift_eq`), hence are equal by
`AdicCompletion.mapCompletion_congr_localizationAway`. -/
theorem awayCongrHom_nested (hI : I.FG) (f g h : A)
    (hfg : IsUnit (algebraMap A (Localization.Away g) f))
    (hfh : IsUnit (algebraMap A (Localization.Away h) f))
    (hgh : IsUnit (algebraMap A (Localization.Away h) g))
    (hbar : IsUnit (algebraMap (awayCompletion (I.map (algebraMap R A)) f)
      (Localization.Away (awayCompletionHom (I.map (algebraMap R A)) f h))
      (awayCompletionHom (I.map (algebraMap R A)) f g)))
    (x : awayCompletion (I.map (algebraMap R A)) g) :
    awayCongrHom I (awayCompletionHom (I.map (algebraMap R A)) f g)
        (awayCompletionHom (I.map (algebraMap R A)) f h) hI hbar
        (awayCompletionNestedAlgEquiv I hI f g hfg x) =
      awayCompletionNestedAlgEquiv I hI f h hfh (awayCongrHom I g h hI hgh x) := by
  have hcomp : ((IsLocalization.Away.lift (awayCompletionHom (I.map (algebraMap R A)) f g)
        hbar).comp (nestedLocHom (I.map (algebraMap R A)) f g hfg)).comp
      (algebraMap A (Localization.Away g)) =
      ((nestedLocHom (I.map (algebraMap R A)) f h hfh).comp
        (IsLocalization.Away.lift g hgh)).comp (algebraMap A (Localization.Away g)) := by
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [nestedLocHom_algebraMap, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq,
      nestedLocHom_algebraMap]
  rw [awayCompletionNestedAlgEquiv_apply_eq I hI f g hfg (nestedLocHom_map_le' I f g hfg)
      ((hI.map _).map _),
    awayCongrHom_apply_eq (A := awayCompletion (I.map (algebraMap R A)) f) I hI _ _ hbar,
    awayCongrHom_apply_eq I hI g h hgh,
    awayCompletionNestedAlgEquiv_apply_eq I hI f h hfh (nestedLocHom_map_le' I f h hfh)
      ((hI.map _).map _),
    ← RingHom.comp_apply, ← RingHom.comp_apply,
    AdicCompletion.mapCompletion_comp _ _ _ _ _ _ ((hI.map _).map _),
    AdicCompletion.mapCompletion_comp _ _ _ _ _ _ ((hI.map _).map _)]
  exact RingHom.congr_fun
    (AdicCompletion.mapCompletion_congr_localizationAway g _ _ _ _ _ hcomp) x

/-- **The packaged naturality**, with the chart-level target away element replaced by any `t`
cutting out the same basic open as `h̄`. This is the form an open-cover datum consumes: there the
double-overlap chart algebra is presented at `ḡ · ḡ'` rather than at the image of a single element
of `A`, and the two presentations are compared by `awayCongrEquiv`. -/
theorem awayCongrHom_nestedCongr (hI : I.FG) (f g h : A)
    (hfg : IsUnit (algebraMap A (Localization.Away g) f))
    (hfh : IsUnit (algebraMap A (Localization.Away h) f))
    (hgh : IsUnit (algebraMap A (Localization.Away h) g))
    (hcgh : IsUnit (algebraMap (awayCompletion (I.map (algebraMap R A)) f)
      (Localization.Away (awayCompletionHom (I.map (algebraMap R A)) f h))
      (awayCompletionHom (I.map (algebraMap R A)) f g)))
    (t : awayCompletion (I.map (algebraMap R A)) f)
    (h1 : IsUnit (algebraMap (awayCompletion (I.map (algebraMap R A)) f)
      (Localization.Away t) (awayCompletionHom (I.map (algebraMap R A)) f h)))
    (h2 : IsUnit (algebraMap (awayCompletion (I.map (algebraMap R A)) f)
      (Localization.Away (awayCompletionHom (I.map (algebraMap R A)) f h)) t))
    (hbar : IsUnit (algebraMap (awayCompletion (I.map (algebraMap R A)) f)
      (Localization.Away t) (awayCompletionHom (I.map (algebraMap R A)) f g)))
    (x : awayCompletion (I.map (algebraMap R A)) g) :
    awayCongrHom I (awayCompletionHom (I.map (algebraMap R A)) f g) t hI hbar
        (awayCompletionNestedAlgEquiv I hI f g hfg x) =
      awayCongrEquiv I (awayCompletionHom (I.map (algebraMap R A)) f h) t hI h1 h2
        (awayCompletionNestedAlgEquiv I hI f h hfh (awayCongrHom I g h hI hgh x)) := by
  rw [awayCongrEquiv_apply_eq, ← awayCongrHom_nested I hI f g h hfg hfh hgh hcgh x]
  exact (AlgHom.congr_fun (awayCongrHom_comp I _ _ _ hI hcgh h1) _).symm

/-- **The naturality square of `FormalSchemes.AwayCompletionNestedNaturality`, in `subst` form.**
When the chart-level target away element `t` is *equal* to the image of `h` — the case an
open-cover datum is in — the comparison isomorphism on the right can be replaced by the transport
`awayCongrEquivOfEq`.

Stated and proved with everything abstract, so that instantiating it at a concrete doubly nested
completion is pure substitution: the kernel never reduces `t`. Instantiating the `awayCongrEquiv`
form instead costs minutes. -/
theorem awayCongrHom_nestedCongrOfEq (hI : I.FG) (a g h : A)
    (hag : IsUnit (algebraMap A (Localization.Away g) a))
    (hah : IsUnit (algebraMap A (Localization.Away h) a))
    (hgh : IsUnit (algebraMap A (Localization.Away h) g))
    (hcgh : IsUnit (algebraMap (awayCompletion (I.map (algebraMap R A)) a)
      (Localization.Away (awayCompletionHom (I.map (algebraMap R A)) a h))
      (awayCompletionHom (I.map (algebraMap R A)) a g)))
    (t : awayCompletion (I.map (algebraMap R A)) a)
    (heq : awayCompletionHom (I.map (algebraMap R A)) a h = t)
    (hbar : IsUnit (algebraMap (awayCompletion (I.map (algebraMap R A)) a) (Localization.Away t)
      (awayCompletionHom (I.map (algebraMap R A)) a g)))
    (x : awayCompletion (I.map (algebraMap R A)) g) :
    awayCongrHom I (awayCompletionHom (I.map (algebraMap R A)) a g) t hI hbar
        (awayCompletionNestedAlgEquiv I hI a g hag x) =
      awayCongrEquivOfEq I heq
        (awayCompletionNestedAlgEquiv I hI a h hah (awayCongrHom I g h hI hgh x)) := by
  subst heq
  have hself : IsUnit (algebraMap (awayCompletion (I.map (algebraMap R A)) a)
      (Localization.Away (awayCompletionHom (I.map (algebraMap R A)) a h))
      (awayCompletionHom (I.map (algebraMap R A)) a h)) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [← awayCongrEquiv_eq_ofEq I hI rfl hself hself]
  exact awayCongrHom_nestedCongr I hI a g h hag hah hgh hcgh _ hself hself hbar x

end FormalSpectrum

end
