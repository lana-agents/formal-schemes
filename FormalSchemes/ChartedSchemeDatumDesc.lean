import FormalSchemes.ChartedSchemeDatum
import FormalSchemes.LocallyRingedSpaceGlueDesc
import FormalSchemes.LocallyRingedSpaceRange

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
(`FormalSchemes.LocallyRingedSpaceRange`), a module that sits directly on Mathlib and exists for
exactly this `CategoryTheory.GlueData.ofGlueData'` bookkeeping. Until issue 1399 it was stated
five times in five files, and this one reached it through `FormalSchemes.SpecTwoPatchNonAffine`, at
a cost this paragraph priced at **+6** modules of import closure, 46 to 52 — the only thing this
file ever took from that module. The move refunds five of the six: the import is now the leaf,
which is itself the sixth module, so the closure goes 52 to **47**.

## The compatibility hypothesis, and why it is stated only off the diagonal

`GlueData.ofGlueData'` fills the diagonal `V (i, i)` with `U i` and both `f i i` and `t i i` with
`eqToHom`s, so the diagonal instance of the gluing condition is an identity between transports and
carries no information. Accordingly `ChartedSchemeDatum.desc` below asks for

```
specAwayMap (g i j) ≫ k i =
  (specGlueIso (g i j) (g j i) (θ i j hij)).hom ≫ specAwayMap (g j i) ≫ k j
```

only for `i ≠ j`, which is the form a caller can actually supply: it is an equation between two
morphisms `Spec ((C i)_{g i j}) ⟶ Z`, both of which are `Spec` of a ring map when `Z` is affine.

## The two directions across the `GlueData.ofGlueData'` bookkeeping, and why they differ

Both are here, and the pair is easy to mistake for a duplication. `specLRSGlueData_compat` goes
**datum-level hypothesis → glue-diagram condition**, for an arbitrary family `k`; it is `desc`'s
input transformer and its hypothesis is supplied by the caller. `specAwayMap_comp_specι` goes the
other way for the **canonical** family `k = specι`, reading the datum-level statement off
`CategoryTheory.GlueData.glue_condition`; nothing supplies its hypothesis because it has none.
Neither is derivable from the other. They now share one spelling of the `dite` unfolding, the
private `specGD_f` / `specGD_t`, rather than one naming it and the other doing it inline.

## Main definitions and results

* `AlgebraicGeometry.ChartedSchemeDatum.desc`: the morphism `specGlued ⟶ Z` glued from a
  compatible family, with `specι_desc` its computation rule and `hom_ext` its uniqueness.
* `AlgebraicGeometry.ChartedSchemeDatum.specAwayMap_comp_specι`: the ambient scheme's own glue
  condition, at an arbitrary index — the chart inclusions agree over their overlaps.
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

/-- The constructed glue map of the ambient scheme, off the diagonal. -/
private theorem specGD_f (i j : D.J) (h : i ≠ j) :
    D.specLRSGlueData.toGlueData.f i j = eqToHom (dif_neg h) ≫ specAwayMap (D.g i j) :=
  dif_neg h

/-- The constructed transition of the ambient scheme, off the diagonal. -/
private theorem specGD_t (i j : D.J) (h : i ≠ j) :
    D.specLRSGlueData.toGlueData.t i j =
      eqToHom (dif_neg h) ≫ (specGlueIso (D.g i j) (D.g j i) (D.θ i j h)).hom ≫
        eqToHom (dif_neg h.symm).symm :=
  dif_neg h

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- `specGD_f` / `specGD_t` are stated at `D.J`, while the indices here are at
-- `D.specLRSGlueData.J`; the two are `D.J` only after unfolding two `def`s, so without this the
-- rewritten target is rejected as ill-typed at `instances` transparency. Same requirement as
-- `specAwayMap_comp_specι` below.
/-- **The datum-level compatibility implies the one the glue diagram imposes.** On the diagonal the
glue transition is the identity (`CategoryTheory.GlueData.t_id`) and the condition is trivial. Off
the diagonal, `specGD_f` and `specGD_t` expose `f i j` as `eqToHom _ ≫ specAwayMap (g i j)` and
`t i j` as `eqToHom _ ≫ specGlueIso _ _ (θ i j) ≫ eqToHom _`; the two inner transports cancel and
what is left is the hypothesis as stated, with one transport in front of both sides.

The `(i : D.J)` ascription in the case split is load-bearing: the index of the glue datum is
`D.specLRSGlueData.J`, which is `D.J` only after unfolding two `def`s, and a `Ne` at the wrong one
of the two spellings does not match the `dite` that `GlueData.ofGlueData'` produces. -/
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
    rw [D.specGD_f i j hij, D.specGD_t i j hij, D.specGD_f j i hij.symm]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
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

/-! ### The glue condition at the canonical family -/

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- The glue datum is a `def`, so `(D.specLRSGlueData).J` does not reduce to `D.J` at `instances`
-- transparency and the rewrites below are rejected as ill-typed without this. Same requirement as
-- in `FormalSchemes.CompletionTwoPatchToScheme`.
/-- **The affine charts of the glued scheme agree over their overlaps**: including
`Spec ((C i)_{g_ij})` into `Spec (C i)` and then into the glued scheme is the same as transporting
it along `Spec (θ i j)` and including through the `j`-th chart. This is
`CategoryTheory.GlueData.glue_condition` for `specLRSGlueData` with the `GlueData.ofGlueData'`
bookkeeping stripped, and it is `AlgebraicGeometry.specTwoPatch_glue`
(`FormalSchemes.CompletionTwoPatchToScheme`) at an arbitrary index type.

This is the **converse direction** to `specLRSGlueData_compat` above, and neither derives the
other: that lemma turns a datum-level hypothesis about an arbitrary family `k` into the condition
the glue diagram imposes, and is `desc`'s input transformer; this one has no hypothesis to be
supplied, and reads the datum-level statement off `glue_condition` for the canonical family
`k = specι`. -/
theorem specAwayMap_comp_specι (i j : D.J) (h : i ≠ j) :
    specAwayMap (D.g i j) ≫ D.specι i =
      (specGlueIso (D.g i j) (D.g j i) (D.θ i j h)).hom ≫ specAwayMap (D.g j i) ≫ D.specι j := by
  have key := D.specLRSGlueData.toGlueData.glue_condition i j
  rw [D.specGD_t i j h, D.specGD_f j i h.symm, D.specGD_f i j h] at key
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  exact ((cancel_epi (eqToHom (dif_neg h))).mp key).symm

end ChartedSchemeDatum

end AlgebraicGeometry

end
