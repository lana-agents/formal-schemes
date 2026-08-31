import FormalSchemes.ChartedSchemeDatum
import FormalSchemes.SpecAwayOverlapLegs

set_option linter.style.header false

/-!
# A smart constructor for `ChartedSchemeDatum` from localization data (EGA I, 10.8)

`AlgebraicGeometry.ChartedSchemeDatum` (`FormalSchemes.ChartedSchemeDatum`) carries its
triple-overlap fields `t'`, `t_fac` and `cocycle` as data, in the shape
`CategoryTheory.GlueData'` demands. Its only construction there, `ChartedSchemeDatum.ofTwoPatch`,
is on `ULift Bool`, where no triple of indices is pairwise distinct and all three are `False.elim`.

This file derives the three fields from *algebra*: a family of double-overlap transitions

```
σ i j k : (C i)_{g_ij · g_ik} ≃+* (C j)_{g_jk · g_ji}
```

together with their compatibility with the single-overlap transitions `θ` and their triple
cocycle. It is the `Spec`-side mirror of
`AlgebraicGeometry.AffineChartedFibreDatumX.xAlgDataT'` and its two laws
(`FormalSchemes.GeneralFibreProductExposeXAlgebraData`), and the recipe is the same one:
transport the transition through the two overlap identifications.

## Why the `Spec` side is so much shorter than the formal side

`FormalSchemes.GeneralFibreProductExposeXAlgebraData` spends its first two thirds on a bridge
between two spellings of the further-localization map and on a threefold composition law for
`AlgebraicGeometry.awayCompletionTransition`. Both exist only because the transition there is a map
of *completions*, so composing two of them is not composing two ring maps. Here the transition is
`AlgebraicGeometry.specGlueIso`, which is `Spec` of a ring isomorphism, so the composition law is
`Spec.locallyRingedSpaceMap_comp` and nothing has to be bridged: the leg identifications
`AlgebraicGeometry.specAwayOverlapIso_hom_fst` / `_hom_snd`
(`FormalSchemes.SpecAwayOverlapLegs`) are stated with the very ring maps `σ` is composed against.

## Main definitions and results

* `AlgebraicGeometry.specGlueIso_comp₃`: three transitions whose ring isomorphisms compose to the
  identity compose to `𝟙`.
* `AlgebraicGeometry.ChartedSchemeDatum.specAlgDataT'`, and its two laws
  `specAlgDataT'_fac` and `specAlgDataT'_cocycle`: the derived triple-overlap datum.
* `AlgebraicGeometry.ChartedSchemeDatum.ofAlgebraData`: the smart constructor. The caller supplies
  the charts, the ideals, the away elements, the single-overlap transitions with their two laws,
  and `σ` with its two laws; the three geometric fields are derived.

## What is *not* done here

No datum on an index type with a pairwise-distinct triple is built in this file — it only makes one
possible. `FormalSchemes.SpecThreeChartCover` is the three-chart instance, and it is what actually
removes the vacuity.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.8.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### A threefold composition law for `specGlueIso` -/

/-- **Three overlap transitions around a triple compose to the identity** as soon as their ring
isomorphisms do. This is `Spec.locallyRingedSpaceMap_comp` twice and
`Spec.locallyRingedSpaceMap_id` once; on the completion side the corresponding statement is
`AlgebraicGeometry.awayCompletionTransition_comp₃`, which is a page long because composing two
maps of completions is not composing two ring maps. -/
theorem specGlueIso_comp₃ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (a : A) (b : B) (c : C) (e₁ : Localization.Away a ≃+* Localization.Away b)
    (e₂ : Localization.Away b ≃+* Localization.Away c)
    (e₃ : Localization.Away c ≃+* Localization.Away a)
    (h : e₁.trans (e₂.trans e₃) = RingEquiv.refl (Localization.Away a)) :
    (specGlueIso a b e₁).hom ≫ (specGlueIso b c e₂).hom ≫ (specGlueIso c a e₃).hom = 𝟙 _ := by
  have hcomp : e₁.symm.toRingHom.comp (e₂.symm.toRingHom.comp e₃.symm.toRingHom) =
      RingHom.id (Localization.Away a) := by
    refine RingHom.ext fun x => ?_
    have h2 : (e₁.trans (e₂.trans e₃)).symm x = x := by
      rw [h]; rfl
    simpa using h2
  change Spec.locallyRingedSpaceMap _ ≫ Spec.locallyRingedSpaceMap _ ≫
    Spec.locallyRingedSpaceMap _ = _
  rw [← Spec.locallyRingedSpaceMap_comp, ← Spec.locallyRingedSpaceMap_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp]
  exact Spec.locallyRingedSpaceMap_id _

namespace ChartedSchemeDatum

variable {J : Type u} (C : J → Type u) [∀ i, CommRing (C i)] (g : ∀ (i : J), J → C i)

/-! ### The derived triple-overlap transition -/

/-- **The derived triple-overlap transition.** From the double-overlap ring isomorphism
`σ i j k : (C i)_{g_ij·g_ik} ≃+* (C j)_{g_jk·g_ji}` we build the pullback-level map by transporting
`specGlueIso σ` through the two overlap identifications
`AlgebraicGeometry.specAwayOverlapIso`. -/
def specAlgDataT'
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (Localization.Away (g i j * g i k) ≃+* Localization.Away (g j k * g j i)))
    (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    pullback (specAwayMap (g i j)) (specAwayMap (g i k)) ⟶
      pullback (specAwayMap (g j k)) (specAwayMap (g j i)) :=
  (specAwayOverlapIso (g i j) (g i k)).inv ≫
    (specGlueIso (g i j * g i k) (g j k * g j i) (σ i j k hij hik hjk)).hom ≫
    (specAwayOverlapIso (g j k) (g j i)).hom

/-- **`t_fac` for the derived transition.** It reduces to the σ/θ compatibility `hσθ`: after the two
leg identifications of `FormalSchemes.SpecAwayOverlapLegs` both sides are `Spec` of a composite of
two ring maps, and `hσθ` says those composites agree. -/
theorem specAlgDataT'_fac
    (θ : ∀ (i j : J), i ≠ j → (Localization.Away (g i j) ≃+* Localization.Away (g j i)))
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (Localization.Away (g i j * g i k) ≃+* Localization.Away (g j k * g j i)))
    (hσθ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toRingHom.comp (awayFurtherRightHom (g j k) (g j i)) =
        (awayFurtherLeftHom (g i j) (g i k)).comp (θ i j hij).symm.toRingHom)
    (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    specAlgDataT' C g σ i j k hij hik hjk ≫
        pullback.snd (specAwayMap (g j k)) (specAwayMap (g j i)) =
      pullback.fst (specAwayMap (g i j)) (specAwayMap (g i k)) ≫
        (specGlueIso (g i j) (g j i) (θ i j hij)).hom := by
  rw [specAlgDataT', ← specAwayOverlapIso_inv_comp_left (g i j) (g i k), Category.assoc,
    Category.assoc, Category.assoc, specAwayOverlapIso_hom_snd, Iso.cancel_iso_inv_left]
  change Spec.locallyRingedSpaceMap _ ≫ Spec.locallyRingedSpaceMap _ =
    Spec.locallyRingedSpaceMap _ ≫ Spec.locallyRingedSpaceMap _
  rw [← Spec.locallyRingedSpaceMap_comp, ← Spec.locallyRingedSpaceMap_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hσθ i j k hij hik hjk]

/-- **`cocycle` for the derived transition.** The adjacent overlap identifications cancel, leaving
the three transitions, which compose to the identity by `specGlueIso_comp₃` and σ's cocycle. -/
theorem specAlgDataT'_cocycle
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (Localization.Away (g i j * g i k) ≃+* Localization.Away (g j k * g j i)))
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
          (σ k i j hik.symm hjk.symm hij)) =
        RingEquiv.refl (Localization.Away (g i j * g i k)))
    (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    specAlgDataT' C g σ i j k hij hik hjk ≫
        specAlgDataT' C g σ j k i hjk hij.symm hik.symm ≫
      specAlgDataT' C g σ k i j hik.symm hjk.symm hij = 𝟙 _ := by
  have hmid := specGlueIso_comp₃ (g i j * g i k) (g j k * g j i) (g k i * g k j)
    (σ i j k hij hik hjk) (σ j k i hjk hij.symm hik.symm) (σ k i j hik.symm hjk.symm hij)
    (hσc i j k hij hik hjk)
  simp only [specAlgDataT', Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, reassoc_of% hmid, Iso.inv_hom_id]

/-! ### The smart constructor -/

/-- **The smart constructor for `ChartedSchemeDatum` from localization data.** The caller supplies
the charts `C` with their ideals `K`, the away elements `g`, the single-overlap transitions `θ`
with `θ_symm` and the ideal compatibility `hθ`, and the double-overlap transitions `σ` with their
σ/θ compatibility and their cocycle; the three geometric fields are derived by `specAlgDataT'`,
`specAlgDataT'_fac` and `specAlgDataT'_cocycle`. -/
def ofAlgebraData (K : ∀ i, Ideal (C i))
    (θ : ∀ (i j : J), i ≠ j → (Localization.Away (g i j) ≃+* Localization.Away (g j i)))
    (θ_symm : ∀ (i j : J) (h : i ≠ j), θ j i h.symm = (θ i j h).symm)
    (hθ : ∀ (i j : J) (h : i ≠ j),
      ((K i).map (algebraMap (C i) (Localization.Away (g i j)))).map (θ i j h).toRingHom =
        (K j).map (algebraMap (C j) (Localization.Away (g j i))))
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (Localization.Away (g i j * g i k) ≃+* Localization.Away (g j k * g j i)))
    (hσθ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toRingHom.comp (awayFurtherRightHom (g j k) (g j i)) =
        (awayFurtherLeftHom (g i j) (g i k)).comp (θ i j hij).symm.toRingHom)
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
          (σ k i j hik.symm hjk.symm hij)) =
        RingEquiv.refl (Localization.Away (g i j * g i k))) :
    ChartedSchemeDatum.{u} where
  J := J
  C := C
  K := K
  g := g
  θ := θ
  θ_symm := θ_symm
  hθ := hθ
  t' := specAlgDataT' C g σ
  t_fac := specAlgDataT'_fac C g θ σ hσθ
  cocycle := specAlgDataT'_cocycle C g σ hσc

end ChartedSchemeDatum

end AlgebraicGeometry

end
