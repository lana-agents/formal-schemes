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
which is itself the sixth module, so the closure went 52 to 47 when that was measured. It has
moved since: this file's forward closure is **48** modules (49 with itself).

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
Neither is derivable from the other. **Neither performs the `dite` unfolding any longer**: each is
one call to a lemma stated at the `CategoryTheory.GlueData'` in `FormalSchemes.GlueMorphisms` —
`ChartedSchemeDatum.specLRSGlueData_compat` to `CategoryTheory.GlueData.ofGlueData'_f_comp`, and
`ChartedSchemeDatum.specAwayMap_comp_specι` to `CategoryTheory.GlueData.ofGlueData'_ι_comp`.
Because those are stated where the two indices already carry the `CategoryTheory.GlueData'`'s own
type, neither meets the index mismatch, and the `backward.isDefEq.respectTransparency false` this
file carried until issue 2150 is gone.

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

/-- **The datum-level compatibility implies the one the glue diagram imposes.** This is
`CategoryTheory.GlueData.ofGlueData'_f_comp` (`FormalSchemes.GlueMorphisms`) at
`AlgebraicGeometry.ChartedSchemeDatum.specGlueData'`: the hypothesis asked for below *is* that
lemma's hypothesis, spelled in the datum's `g` and `θ` rather than in the
`CategoryTheory.GlueData'`'s `f` and `t`, and the two spellings are the same term.

Until issue 2150 the unfolding was performed here instead, by a private pair of `dif_neg`
one-liners exposing `f i j` and `t i j` off the diagonal and a `simp only` cancelling the two
inner transports. That route states the unfolding at `ChartedSchemeDatum.J` while the goal's
indices are at the index type of `ChartedSchemeDatum.specLRSGlueData` — the same type only after
unfolding two `def`s — and so needed `backward.isDefEq.respectTransparency false`. The general
lemma is stated where both indices already carry the `CategoryTheory.GlueData'`'s own index type,
so it never meets the mismatch and the option is gone. -/
theorem specLRSGlueData_compat
    (k : ∀ i, Spec.locallyRingedSpaceObj (CommRingCat.of (D.C i)) ⟶ Z)
    (h : ∀ (i j : D.J) (hij : i ≠ j), specAwayMap (D.g i j) ≫ k i =
      (specGlueIso (D.g i j) (D.g j i) (D.θ i j hij)).hom ≫ specAwayMap (D.g j i) ≫ k j)
    (i j : D.specLRSGlueData.J) :
    D.specLRSGlueData.toGlueData.f i j ≫ k i =
      D.specLRSGlueData.toGlueData.t i j ≫ D.specLRSGlueData.toGlueData.f j i ≫ k j :=
  CategoryTheory.GlueData.ofGlueData'_f_comp D.specGlueData' k h i j

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

/-- **The affine charts of the glued scheme agree over their overlaps**: including
`Spec ((C i)_{g_ij})` into `Spec (C i)` and then into the glued scheme is the same as transporting
it along `Spec (θ i j)` and including through the `j`-th chart. This is
`CategoryTheory.GlueData.glue_condition` for `specLRSGlueData` with the `GlueData.ofGlueData'`
bookkeeping stripped by `CategoryTheory.GlueData.ofGlueData'_ι_comp`
(`FormalSchemes.GlueMorphisms`), and it is `AlgebraicGeometry.specTwoPatch_glue`
(`FormalSchemes.CompletionTwoPatchToScheme`) at an arbitrary index type.

This is the **converse direction** to `specLRSGlueData_compat` above, and neither derives the
other: that lemma turns a datum-level hypothesis about an arbitrary family `k` into the condition
the glue diagram imposes, and is `desc`'s input transformer; this one has no hypothesis to be
supplied, and reads the datum-level statement off `glue_condition` for the canonical family
`k = specι`. -/
theorem specAwayMap_comp_specι (i j : D.J) (h : i ≠ j) :
    specAwayMap (D.g i j) ≫ D.specι i =
      (specGlueIso (D.g i j) (D.g j i) (D.θ i j h)).hom ≫ specAwayMap (D.g j i) ≫ D.specι j := by
  exact CategoryTheory.GlueData.ofGlueData'_ι_comp D.specGlueData' i j h

end ChartedSchemeDatum

end AlgebraicGeometry

end
