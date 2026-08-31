import FormalSchemes.ChartedSchemeDatum
import FormalSchemes.LocallyRingedSpaceGlueDesc
import FormalSchemes.SpecTwoPatchNonAffine

set_option linter.style.header false

/-!
# Mapping out of the glued scheme of a `ChartedSchemeDatum` (EGA I, 10.8)

`FormalSchemes.ChartedSchemeDatum` builds `ChartedSchemeDatum.specGlued`, the affine charts
`Spec (C i)` glued along the localization transitions `θ i j`, together with the chart inclusions
`specι i` and their joint surjectivity. Every statement there is about a morphism *into* the glued
scheme, and the missing universal property was what stopped `FormalSchemes.SpecThreeChartCover`'s
`glued` from being compared with `Spec A`. Both files now point here instead of recording the
absence.

This file supplies it. The content is `FormalSchemes.LocallyRingedSpaceGlueDesc` at
`specLRSGlueData`; what is done here is the translation of the compatibility hypothesis from the
`CategoryTheory.GlueData` built by `CategoryTheory.GlueData.ofGlueData'` — whose `f` and `t` are
`dite`s on `i = j`, wrapped in `eqToHom`s — back into the datum's own `g` and `θ`.

Discarding those `eqToHom`s on ranges is
`AlgebraicGeometry.LocallyRingedSpace.range_eqToHom_comp_base`
(`FormalSchemes.SpecTwoPatchNonAffine`), whose own docstring says it exists for exactly this
`ofGlueData'` bookkeeping. Importing that file rather than restating the two-line lemma costs this
one **+6** modules of import closure, 46 to 52; the tree already carries three copies of that
statement under two names, and a fourth is not worth six modules saved.

## The compatibility hypothesis, and why it is stated only off the diagonal

`ofGlueData'` fills the diagonal `V (i, i)` with `U i` and both `f i i` and `t i i` with `eqToHom`s,
so the diagonal instance of the gluing condition is an identity between transports and carries no
information. Accordingly `desc` below asks for

```
specAwayMap (g i j) ≫ k i =
  (specGlueIso (g i j) (g j i) (θ i j hij)).hom ≫ specAwayMap (g j i) ≫ k j
```

only for `i ≠ j`, which is the form a caller can actually supply: it is an equation between two
morphisms `Spec ((C i)_{g i j}) ⟶ Z`, both of which are `Spec` of a ring map when `Z` is affine.

## Main definitions and results

* `AlgebraicGeometry.ChartedSchemeDatum.desc`: the morphism `specGlued ⟶ Z` glued from a
  compatible family, with `specι_desc` its computation rule and `hom_ext` its uniqueness.
* `AlgebraicGeometry.ChartedSchemeDatum.range_desc`: its range is the union of the ranges of the
  chart morphisms.
* `AlgebraicGeometry.ChartedSchemeDatum.isOpenImmersion_desc`: it is an open immersion as soon as
  the chart morphisms are and they meet in `Z` only along their overlaps; and
  `AlgebraicGeometry.ChartedSchemeDatum.isIso_desc`, when it is moreover surjective.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace ChartedSchemeDatum

variable (D : ChartedSchemeDatum.{u}) {Z : LocallyRingedSpace.{u}}

/-! ### The glue datum's compatibility, in the datum's own terms -/

/-- **The datum-level compatibility implies the one the glue diagram imposes.** On the diagonal the
glue transition is the identity (`CategoryTheory.GlueData.t_id`) and the condition is trivial. Off
the diagonal, unfolding `CategoryTheory.GlueData.ofGlueData'` exposes `f i j` as
`eqToHom _ ≫ specAwayMap (g i j)` and `t i j` as `eqToHom _ ≫ specGlueIso _ _ (θ i j) ≫ eqToHom _`;
the two inner transports cancel and what is left is the hypothesis as stated, with one transport in
front of both sides.

The `(i : D.J)` ascription in the case split is load-bearing: the index of the glue datum is
`D.specLRSGlueData.J`, which is `D.J` only after unfolding two `def`s, and a `Ne` at the wrong one
of the two spellings does not match the `dite` that `ofGlueData'` produces. -/
theorem specLRSGlueData_compat
    (k : ∀ i, Spec.locallyRingedSpaceObj (CommRingCat.of (D.C i)) ⟶ Z)
    (h : ∀ (i j : D.J) (hij : i ≠ j), specAwayMap (D.g i j) ≫ k i =
      (specGlueIso (D.g i j) (D.g j i) (D.θ i j hij)).hom ≫ specAwayMap (D.g j i) ≫ k j)
    (i j : D.specLRSGlueData.J) :
    D.specLRSGlueData.toGlueData.f i j ≫ k i =
      D.specLRSGlueData.toGlueData.t i j ≫ D.specLRSGlueData.toGlueData.f j i ≫ k j := by
  obtain rfl | hij0 := eq_or_ne i j
  · rw [D.specLRSGlueData.toGlueData.t_id i, Category.id_comp]
  · have hij : @Ne D.J i j := hij0
    simp only [specLRSGlueData, specGlueData', CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', dif_neg hij, dif_neg (Ne.symm hij), Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [h i j hij]

/-! ### The universal property -/

/-- **A family of morphisms out of the charts, agreeing on the overlaps, glues.** The hypothesis is
the datum's own: over the overlap `Spec ((C i)_{g i j})`, the `i`-th chart morphism agrees with the
`j`-th read through the transition `θ i j`. -/
def desc (k : ∀ i, Spec.locallyRingedSpaceObj (CommRingCat.of (D.C i)) ⟶ Z)
    (h : ∀ (i j : D.J) (hij : i ≠ j), specAwayMap (D.g i j) ≫ k i =
      (specGlueIso (D.g i j) (D.g j i) (D.θ i j hij)).hom ≫ specAwayMap (D.g j i) ≫ k j) :
    D.specGlued ⟶ Z :=
  D.specLRSGlueData.desc k (D.specLRSGlueData_compat k h)

@[reassoc (attr := simp)]
theorem specι_desc (k : ∀ i, Spec.locallyRingedSpaceObj (CommRingCat.of (D.C i)) ⟶ Z)
    (h : ∀ (i j : D.J) (hij : i ≠ j), specAwayMap (D.g i j) ≫ k i =
      (specGlueIso (D.g i j) (D.g j i) (D.θ i j hij)).hom ≫ specAwayMap (D.g j i) ≫ k j)
    (i : D.J) : D.specι i ≫ D.desc k h = k i :=
  D.specLRSGlueData.ι_desc k _ i

/-- **Uniqueness**: two morphisms out of the glued scheme agreeing on every chart are equal. -/
theorem hom_ext {f g : D.specGlued ⟶ Z} (hfg : ∀ i, D.specι i ≫ f = D.specι i ≫ g) : f = g :=
  D.specLRSGlueData.hom_ext hfg

/-! ### Ranges, and the open-immersion criterion -/

variable (k : ∀ i, Spec.locallyRingedSpaceObj (CommRingCat.of (D.C i)) ⟶ Z)
variable (h : ∀ (i j : D.J) (hij : i ≠ j), specAwayMap (D.g i j) ≫ k i =
  (specGlueIso (D.g i j) (D.g j i) (D.θ i j hij)).hom ≫ specAwayMap (D.g j i) ≫ k j)

/-- **The range of the glued morphism is the union of the ranges of the chart morphisms.** -/
theorem range_desc : Set.range (D.desc k h).base = ⋃ i, Set.range (k i).base :=
  D.specLRSGlueData.range_desc k _

/-- **The criterion.** A morphism glued from open immersions that meet only along the overlaps
`Spec ((C i)_{g i j})` is an open immersion. The `hmeet` hypothesis is not removable: the line with
two origins is glued from two copies of `𝔸¹` whose images meet in more than the overlap accounts
for. -/
theorem isOpenImmersion_desc
    (hoi : ∀ i, LocallyRingedSpace.IsOpenImmersion (k i))
    (hmeet : ∀ (i j : D.J), i ≠ j → Set.range (k i).base ∩ Set.range (k j).base ⊆
      Set.range (specAwayMap (D.g i j) ≫ k i).base) :
    LocallyRingedSpace.IsOpenImmersion (D.desc k h) :=
  D.specLRSGlueData.isOpenImmersion_desc k _ hoi fun i j hij => by
    have hij' : @Ne D.J i j := hij
    simp only [specLRSGlueData, specGlueData', CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', dif_neg hij', Category.assoc]
    exact (hmeet i j hij').trans (LocallyRingedSpace.range_eqToHom_comp_base _ _).ge

/-- **The glued morphism is an isomorphism** when it is moreover surjective on points — which, with
`range_desc`, is the statement that the chart morphisms jointly cover `Z`. -/
theorem isIso_desc
    (hoi : ∀ i, LocallyRingedSpace.IsOpenImmersion (k i))
    (hmeet : ∀ (i j : D.J), i ≠ j → Set.range (k i).base ∩ Set.range (k j).base ⊆
      Set.range (specAwayMap (D.g i j) ≫ k i).base)
    (hsurj : ⋃ i, Set.range (k i).base = (Set.univ : Set Z)) :
    IsIso (D.desc k h) := by
  haveI := D.isOpenImmersion_desc k h hoi hmeet
  haveI : Epi (D.desc k h).base :=
    (TopCat.epi_iff_surjective _).2 (Set.range_eq_univ.1 ((D.range_desc k h).trans hsurj))
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

end ChartedSchemeDatum

end AlgebraicGeometry

end
