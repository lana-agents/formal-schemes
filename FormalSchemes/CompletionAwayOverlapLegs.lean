import FormalSchemes.CompletionBasicOpenMap
import FormalSchemes.CompletionBasicOpenOverlap

set_option linter.style.header false

/-!
# The legs of the basic-open completion overlap (EGA I, 10.8)

`formalCompletion.basicOpenOverlapIso`
(`FormalSchemes.CompletionBasicOpenOverlap`) identifies the basic-open completion at a product,
`Spf (R_{fg})^`, with the fibre product of the two chart immersions at `f` and at `g`. The two
compatibility lemmas that ship with it,
`formalCompletion.basicOpenOverlapIso_hom_fst_comp` and `..._hom_snd_comp`, state
what each projection does **after composing further into `Spf R^`**. That is the form a
`cancel_mono` argument against a common ambient object wants, and it is the form
`FormalSchemes.CompletionBasicOpenGlue` uses.

This file records the same two facts in the **uncomposed** form: each projection is, on the nose,
the completion functoriality of a further-localization ring map. That is the form needed when there
is *no* common ambient object to cancel against — which is exactly the situation of a family of
charts with unrelated coordinate rings, where the charts of `Spf ((C i)_{g_ij})^` and
`Spf ((C j)_{g_ji})^` live over different rings and nothing lies under both. It is the completion
analogue of `AlgebraicGeometry.specAwayOverlapIso_hom_fst` / `..._hom_snd`
(`FormalSchemes.SpecAwayOverlapLegs`), proved the same way: cancel the chart immersion, which is a
monomorphism, off the `_comp` form.

## The further-localization maps are Mathlib's

`IsLocalization.Away.awayToAwayRight f g : R_f →+* R_{fg}` and
`IsLocalization.Away.awayToAwayLeft g f : R_g →+* R_{fg}` are the two ring maps, together with
`IsLocalization.Away.awayToAwayRight_eq` and `IsLocalization.Away.awayToAwayLeft_eq` saying each
is a map under `R`. Nothing is redefined here.

## Main definitions and results

* `formalCompletion.map_congr`: the completion functoriality depends on its ring
  homomorphism only through its value.
* `formalCompletion.awayFurtherLeft` / `..._awayFurtherRight`: the two
  further-localization morphisms of completions `Spf (R_{fg})^ ⟶ Spf (R_f)^`, `Spf (R_{fg})^ ⟶
  Spf (R_g)^`, with `..._comp` saying each is a factorisation of the basic-open immersion at the
  product.
* `formalCompletion.basicOpenOverlapIso_hom_fst` / `..._hom_snd`: the two
  projections out of the overlap identification, uncomposed.
* `formalCompletion.basicOpenOverlapIso_inv_comp_left` / `..._right`: the same
  read backwards, which is the orientation a `t_fac` proof rewrites with.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace formalCompletion

/-- **The completion functoriality depends on its ring homomorphism only through its value**, not
through the proof that it carries one ideal into the other. Two private copies of this exist
upstream (`FormalSchemes.CompletionGlueTwoPatch`, `FormalSchemes.CompletionBasicOpenGlue`); this is
the first public one, and every `formalCompletion.map` identity below goes through it. -/
theorem map_congr {R S : Type u} [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}
    (hI : I.FG) (hJ : J.FG) {φ ψ : R →+* S} (hφ : I.map φ ≤ J) (hψ : I.map ψ ≤ J) (h : φ = ψ) :
    formalCompletion.map hI hJ φ hφ = formalCompletion.map hI hJ ψ hψ := by
  subst h; rfl

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (f g : R)

/-! ### The two further-localization ring maps, as maps under `R` -/

/-- `R_f →+* R_{fg}` is a ring map under `R`. -/
theorem awayToAwayRight_comp_algebraMap :
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away f)
          (P := Localization.Away (f * g)) f g).comp (algebraMap R (Localization.Away f)) =
      algebraMap R (Localization.Away (f * g)) :=
  RingHom.ext (IsLocalization.Away.awayToAwayRight_eq f g)

/-- `R_g →+* R_{fg}` is a ring map under `R`. -/
theorem awayToAwayLeft_comp_algebraMap :
    (IsLocalization.Away.awayToAwayLeft (S := Localization.Away g)
          (P := Localization.Away (f * g)) g f).comp (algebraMap R (Localization.Away g)) =
      algebraMap R (Localization.Away (f * g)) :=
  RingHom.ext (IsLocalization.Away.awayToAwayLeft_eq g f)

/-- The extension of `I` to `R_f`, pushed on to `R_{fg}`, is its extension to `R_{fg}`. -/
theorem map_ideal_awayToAwayRight :
    (I.map (algebraMap R (Localization.Away f))).map
        (IsLocalization.Away.awayToAwayRight (S := Localization.Away f)
          (P := Localization.Away (f * g)) f g) =
      I.map (algebraMap R (Localization.Away (f * g))) := by
  rw [Ideal.map_map, awayToAwayRight_comp_algebraMap]

/-- The extension of `I` to `R_g`, pushed on to `R_{fg}`, is its extension to `R_{fg}`. -/
theorem map_ideal_awayToAwayLeft :
    (I.map (algebraMap R (Localization.Away g))).map
        (IsLocalization.Away.awayToAwayLeft (S := Localization.Away g)
          (P := Localization.Away (f * g)) g f) =
      I.map (algebraMap R (Localization.Away (f * g))) := by
  rw [Ideal.map_map, awayToAwayLeft_comp_algebraMap]

/-! ### The two further-localization morphisms of completions -/

/-- **The overlap completion, mapped to the first chart's completion**: `Spf (R_{fg})^ ⟶
Spf (R_f)^`, the completion functoriality of `R_f →+* R_{fg}`. -/
def awayFurtherLeft :
    formalCompletion (Localization.Away (f * g))
        (I.map (algebraMap R (Localization.Away (f * g)))) (hI.map _) ⟶
      formalCompletion (Localization.Away f) (I.map (algebraMap R (Localization.Away f)))
        (hI.map _) :=
  formalCompletion.map (hI.map _) (hI.map _)
    (IsLocalization.Away.awayToAwayRight f g) (map_ideal_awayToAwayRight I f g).le

/-- **The overlap completion, mapped to the second chart's completion**: `Spf (R_{fg})^ ⟶
Spf (R_g)^`. -/
def awayFurtherRight :
    formalCompletion (Localization.Away (f * g))
        (I.map (algebraMap R (Localization.Away (f * g)))) (hI.map _) ⟶
      formalCompletion (Localization.Away g) (I.map (algebraMap R (Localization.Away g)))
        (hI.map _) :=
  formalCompletion.map (hI.map _) (hI.map _)
    (IsLocalization.Away.awayToAwayLeft g f) (map_ideal_awayToAwayLeft I f g).le

/-- **The first further-localization morphism factors the basic-open immersion at the product.** -/
theorem awayFurtherLeft_comp :
    awayFurtherLeft I hI f g ≫ formalCompletion.basicOpenImmersion I hI f =
      formalCompletion.basicOpenImmersion I hI (f * g) := by
  rw [awayFurtherLeft, formalCompletion.basicOpenImmersion_eq_map I hI f,
    formalCompletion.basicOpenImmersion_eq_map I hI (f * g),
    ← formalCompletion.map_comp I hI (hI.map _) (hI.map _)
      (algebraMap R (Localization.Away f)) (IsLocalization.Away.awayToAwayRight f g)
      (le_of_eq rfl) (map_ideal_awayToAwayRight I f g).le]
  exact map_congr hI (hI.map _) _ _ (awayToAwayRight_comp_algebraMap f g)

/-- **The second further-localization morphism factors the basic-open immersion at the product.**
-/
theorem awayFurtherRight_comp :
    awayFurtherRight I hI f g ≫ formalCompletion.basicOpenImmersion I hI g =
      formalCompletion.basicOpenImmersion I hI (f * g) := by
  rw [awayFurtherRight, formalCompletion.basicOpenImmersion_eq_map I hI g,
    formalCompletion.basicOpenImmersion_eq_map I hI (f * g),
    ← formalCompletion.map_comp I hI (hI.map _) (hI.map _)
      (algebraMap R (Localization.Away g)) (IsLocalization.Away.awayToAwayLeft g f)
      (le_of_eq rfl) (map_ideal_awayToAwayLeft I f g).le]
  exact map_congr hI (hI.map _) _ _ (awayToAwayLeft_comp_algebraMap f g)

/-! ### The uncomposed legs of the overlap identification -/

/-- **The first projection out of the overlap identification**, uncomposed: it is the completion
functoriality of `R_f →+* R_{fg}`. Proved by cancelling the chart immersion, which is a
monomorphism, off `formalCompletion.basicOpenOverlapIso_hom_fst_comp`. -/
@[reassoc]
theorem basicOpenOverlapIso_hom_fst :
    (formalCompletion.basicOpenOverlapIso I hI f g).hom ≫
        pullback.fst (formalCompletion.basicOpenImmersion I hI f).toLRSHom
          (formalCompletion.basicOpenImmersion I hI g).toLRSHom =
      (awayFurtherLeft I hI f g).toLRSHom := by
  rw [← cancel_mono (formalCompletion.basicOpenImmersion I hI f).toLRSHom, Category.assoc,
    formalCompletion.basicOpenOverlapIso_hom_fst_comp]
  exact (congrArg FormalScheme.Hom.toLRSHom (awayFurtherLeft_comp I hI f g)).symm

/-- **The second projection out of the overlap identification**, uncomposed. -/
@[reassoc]
theorem basicOpenOverlapIso_hom_snd :
    (formalCompletion.basicOpenOverlapIso I hI f g).hom ≫
        pullback.snd (formalCompletion.basicOpenImmersion I hI f).toLRSHom
          (formalCompletion.basicOpenImmersion I hI g).toLRSHom =
      (awayFurtherRight I hI f g).toLRSHom := by
  rw [← cancel_mono (formalCompletion.basicOpenImmersion I hI g).toLRSHom, Category.assoc,
    formalCompletion.basicOpenOverlapIso_hom_snd_comp]
  exact (congrArg FormalScheme.Hom.toLRSHom (awayFurtherRight_comp I hI f g)).symm

/-- **The first projection, read backwards through the overlap identification.** -/
theorem basicOpenOverlapIso_inv_comp_left :
    (formalCompletion.basicOpenOverlapIso I hI f g).inv ≫ (awayFurtherLeft I hI f g).toLRSHom =
      pullback.fst (formalCompletion.basicOpenImmersion I hI f).toLRSHom
        (formalCompletion.basicOpenImmersion I hI g).toLRSHom := by
  rw [← basicOpenOverlapIso_hom_fst, Iso.inv_hom_id_assoc]

/-- **The second projection, read backwards through the overlap identification.** -/
theorem basicOpenOverlapIso_inv_comp_right :
    (formalCompletion.basicOpenOverlapIso I hI f g).inv ≫ (awayFurtherRight I hI f g).toLRSHom =
      pullback.snd (formalCompletion.basicOpenImmersion I hI f).toLRSHom
        (formalCompletion.basicOpenImmersion I hI g).toLRSHom := by
  rw [← basicOpenOverlapIso_hom_snd, Iso.inv_hom_id_assoc]

end formalCompletion

end
