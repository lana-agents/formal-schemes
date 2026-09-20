import FormalSchemes.GeneralFibreProductBaseChange
import FormalSchemes.GeneralFibreProductBothAlgebraDataCocycle

set_option linter.style.header false

/-!
# The glued base change at a pair of glues the smart constructor builds

`FormalSchemes.GeneralFibreProductBaseChange` proves the two facts a consumer of the comparison
`X ×_{Spf I'} Y ⟶ X ×_{Spf I} Y` wants — the overlap square
`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_bothAlgData` and injectivity of
the glued comparison
`AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base_of_bothAlgData` — at a pair of
**abstract** `AlgebraicGeometry.DoubleChartGlue`s carrying **six hypotheses** that identify their
`V`, `f` and `t` with the dispatched `AlgebraicGeometry.bothAlgDataV` / `..bothAlgDataF` /
`..bothAlgDataT`. That shape is deliberate: `..IsBaseChangeOverlapCompatible` mentions exactly
those three of the eight geometric fields, and a statement at a literal
`AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraData` pair would name the primed `σX`, `σY` and
their four laws besides, six large parameters occurring in no statement.

**This file supplies the consumer that shape was chosen against.** It reads the smart
constructor's glue at the ambient chart family, `AlgebraicGeometry.BothChartedFibreDatum`'s own
three identifications become `rfl`, and the two theorems above are then stated at a pair of glues a
caller *constructs* rather than at abstract ones with hypotheses.

## The one thing that is not free, and it is not the import

Feeding `(AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraData … ).toDoubleChartGlue` to those
theorems directly does **not** elaborate, and the failure is not in any of the six hypotheses —
it arrives at the statement, before a hypothesis is looked at:

```
failed to synthesize instance of type class
  ∀ (i : JX), @IsScalarTower R R' (A i) … (@Algebra.toSMul R (A i) …
    (@BothChartedFibreDatum.algebraA R _ I hI (ofAlgebraData …) i))
```

**That transcript is one probe's failure, not the only one.** Write the same statement with the
two `AlgebraicGeometry.BothChartedFibreDatum.toDoubleChartGlue`s in head position — applied to the
overlap-compatibility predicate rather than to a theorem whose hypotheses are already in play — and
no `IsScalarTower` obligation is ever reached, because the datum's chart algebras fail to reduce
one step earlier:

```
failed to synthesize instance of type class
  (i : (BothChartedFibreDatum.ofAlgebraData gX gY τX' τY' … hστX' hστY').JX) →
    CommRing ((BothChartedFibreDatum.ofAlgebraData gX gY τX' τY' … hστX' hστY').A i)
```

A reader who meets that one is looking at this paragraph's wall and not at a different problem: the
mechanism below and the cure account for both, and only the class of the first unsatisfied
obligation moves with the probe.

`AlgebraicGeometry.BothChartedFibreDatum.toDoubleChartGlue`'s type `letI`-binds the datum's own
`commRingA`, `algebraA`, `commRingB`, `algebraB`, so unifying its result against the theorem's
`AlgebraicGeometry.DoubleChartGlue R I A B` assigns those fields to the theorem's instance
arguments. The chart family and the `R'`-algebra structure still come from the ambient variables,
because the primed glue is stated there; so the `IsScalarTower R R' (A i)` that instance search is
left with mixes the datum's `R`-algebra structure with the ambient `R'`-algebra one, and no
ambient instance matches it. Instance search runs at `instances` transparency and will not unfold
the `def` `..ofAlgebraData` to see that the datum's field *is* the ambient instance.

**The cure is a type ascription and nothing else.** `..ofAlgebraDataGlue` below is that same term
read at type `AlgebraicGeometry.DoubleChartGlue R I A B`: the ascription is checked at `default`
transparency, where the datum's fields do reduce to the ambient instances, so the definition is
accepted and every later mention of it carries the ambient instance signature. Nothing is made
`@[reducible]`, this file needs no `set_option` beyond `linter.style.header false`, and neither
`..ofAlgebraData` nor `..toDoubleChartGlue` is restated, generalised or weakened.

The idiom is not new here: `AlgebraicGeometry.BothChartedFibreDatumXY.diagonalDoubleChartGlue`
(`FormalSchemes.GeneralSeparatedBaseChange`) already reads a one-factor datum's glue at a fixed
chart family the same way, and says in its own docstring why — *"two data over different bases
share nothing a statement can quantify over until the family is one."* This file records that the
same sentence is what clears the instance problem, and makes the reading available for the
two-sided smart constructor rather than only for the diagonal.

## What the three identifications actually cost

`..ofAlgebraData` sets `V := bothAlgDataV hI gX gY`, `f := bothAlgDataF hI gX gY` and
`t := bothAlgDataT hI gX gY τX τY`, and `..toDoubleChartGlue` copies all eight geometric fields
verbatim, so after the ascription the three hypotheses are:

* the object one, `rfl`;
* the immersion one, `Category.id_comp` read backwards — the `eqToHom` of a `rfl` the two sides of
  which are not *syntactically* equal, so `eqToHom_refl` does not fire and the proof is the
  identity law consumed through the definitional equality instead;
* the transition one, `Category.id_comp` **and** `Category.comp_id`, because that hypothesis
  carries an `eqToHom` at each end.

`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_bothAlgData`'s docstring says
the first two of these. The third is the one correction this file makes to it: one identity law is
not enough for `t`.

## Main results

* `AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraDataGlue`: the smart constructor's glue, read
  at the ambient chart family.
* `AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraDataGlue_V` / `..ofAlgebraDataGlue_f` /
  `..ofAlgebraDataGlue_t`: the three identifications, named once, in exactly the shape the two
  theorems ask for.
* `AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_ofAlgebraDataGlue`: **the
  overlap square at a constructed pair.**
* `AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base_ofAlgebraDataGlue`: **the glued
  base change of a constructed pair is injective on points.**

## What is not proved here

* **Nothing is restated.** Both theorems are consumed through the six hypotheses; the general-tower
  statements keep their shape, which is the design
  `FormalSchemes.GeneralFibreProductBaseChange` argued for and this file endorses rather than
  replaces.
* **The transition agreement is still an input.** `AlgebraicGeometry.IsChartTransitionBaseChange`
  is a hypothesis of both corollaries, exactly as of their originals; it is discharged at an away
  base by `AlgebraicGeometry.isChartTransitionBaseChange_awayBase`
  (`FormalSchemes.AwayBaseChangeChartTransition`) and nowhere else.
* **No separatedness statement**, and nothing about
  `AlgebraicGeometry.BothChartedFibreDatumXY.diagonalDoubleChartGlue`. The two corollaries below do
  apply there — the diagonal glue is `..ofAlgebraData`'s glue of one factor taken twice, and its
  three identifications are the same three proofs — but stating that costs
  `FormalSchemes.GeneralSeparatedBaseChange`'s forward closure of **185** modules and belongs with
  the row that tightens that file's hypotheses.

## Placement

A leaf over `FormalSchemes.GeneralFibreProductBaseChange` and
`FormalSchemes.GeneralFibreProductBothAlgebraDataCocycle`: this file's forward closure is **105**
project modules besides itself, and this file's reverse closure is **0**.

The two parents are **import-incomparable**, and they share **74** modules.
`FormalSchemes.GeneralFibreProductBaseChange` contributes **20** that the other does not reach and
`FormalSchemes.GeneralFibreProductBothAlgebraDataCocycle` contributes **11** that the first does
not, so the edges are **not** priced the same and the cheap one points the wrong way.

* adding this to `FormalSchemes.GeneralFibreProductBaseChange` costs eleven modules and puts the
  two-sided smart constructor inside the closure of the file that was written to *avoid* it.
  `FormalSchemes.GeneralFibreProductBaseChange`'s reverse closure is **4**, so the eleven would be
  cheap in modules and expensive in subject — the edge would falsify the design argument that
  file's own *What is assembled* paragraph makes;
* adding it to `FormalSchemes.GeneralFibreProductBothAlgebraDataCocycle` costs twenty modules, and
  `FormalSchemes.GeneralFibreProductBothAlgebraDataCocycle`'s reverse closure is **41**, so
  forty-one modules would pay for the whole base-change cluster to reach a file about the cocycle
  law.

There is a third home that costs **no** import at all:
`FormalSchemes.GeneralSeparatedBaseChange` already reached both parents — it and
`FormalSchemes.AwayBaseChangeSeparated`, which arrived later, are the only two modules that do — so
putting these declarations there would add no import edge and move no closure figure anywhere; it
is no longer free of rebuild cost, since
`FormalSchemes.GeneralSeparatedBaseChange`'s reverse closure is **1** rather than the **0** it was
when this paragraph was written. It is declined on subject and on reach:
`FormalSchemes.GeneralSeparatedBaseChange`'s subject is §10.15 separatedness,
`FormalSchemes.GeneralSeparatedBaseChange`'s forward closure is **185**, and a consumer of the
fibre-product base change that is not about separatedness would pay eighty modules for a
statement that has nothing to do with the diagonal.

A leaf leaves all three subjects alone and moves no forward closure anywhere, at the price of the
reverse closure of every module it imports moving by one.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.14.
-/

noncomputable section

open CategoryTheory FormalSpectrum CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
variable {I : Ideal R} {I' : Ideal R'}
variable {JX JY : Type u} {A : JX → Type u} {B : JY → Type u}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]

namespace BothChartedFibreDatum

variable (gX : ∀ i _ : JX, A i) (gY : ∀ j _ : JY, B j)
variable (τX : ∀ (i i' : JX), i ≠ i' →
    (awayCompletion (I.map (algebraMap R (A i))) (gX i i') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A i'))) (gX i' i)))
variable (τY : ∀ (j j' : JY), j ≠ j' →
    (awayCompletion (I.map (algebraMap R (B j))) (gY j j') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (B j'))) (gY j' j)))
variable (σX : ∀ (i i' i'' : JX), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R (A i))) (gX i i' * gX i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A i'))) (gX i' i'' * gX i' i)))
variable (σY : ∀ (j j' j'' : JY), j ≠ j' → j ≠ j'' → j' ≠ j'' →
    (awayCompletion (I.map (algebraMap R (B j))) (gY j j' * gY j j'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (B j'))) (gY j' j'' * gY j' j)))
variable (hσcX : ∀ (i i' i'' : JX) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
      (σX i'' i i' h2.symm h3.symm h1)) = AlgEquiv.refl)
variable (hσcY : ∀ (j j' j'' : JY) (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j''),
    (σY j j' j'' h1 h2 h3).trans ((σY j' j'' j h3 h1.symm h2.symm).trans
      (σY j'' j j' h2.symm h3.symm h1)) = AlgEquiv.refl)
variable (τX_symm : ∀ (i i' : JX) (h : i ≠ i'), τX i' i h.symm = (τX i i' h).symm)
variable (τY_symm : ∀ (j j' : JY) (h : j ≠ j'), τY j' j h.symm = (τY j j' h).symm)
variable (hI : I.FG)
variable (hστX : ∀ (i i' i'' : JX) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (gX i' i'') (gX i' i) hI) =
      (furtherLocFst I (gX i i') (gX i i'') hI).comp (τX i i' h1).symm.toAlgHom)
variable (hστY : ∀ (j j' j'' : JY) (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j''),
    (σY j j' j'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (gY j' j'') (gY j' j) hI) =
      (furtherLocFst I (gY j j') (gY j j'') hI).comp (τY j j' h1).symm.toAlgHom)

/-- **The glue of the two-sided smart constructor, read at the ambient chart family.** *Reach for
this one* whenever a `AlgebraicGeometry.DoubleChartGlue` has to be *produced* rather than assumed:
this is `AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraData`'s datum passed through
`AlgebraicGeometry.BothChartedFibreDatum.toDoubleChartGlue`, and the only content of the
definition is the type it is read at.

That ascription is what makes the term usable. `..toDoubleChartGlue`'s type `letI`-binds the
datum's own `commRingA`, `algebraA`, `commRingB` and `algebraB`, and a statement that also
mentions the *primed* base takes its `R'`-algebra instances from the ambient variables; the mixed
`IsScalarTower R R' (A i)` that results matches no instance at `instances` transparency, because
that transparency will not unfold `..ofAlgebraData`. Read at `DoubleChartGlue R I A B` the same
term is checked at `default` transparency, where the datum's fields reduce to the ambient
instances, and every mention downstream then carries one instance signature instead of two.

`AlgebraicGeometry.BothChartedFibreDatumXY.diagonalDoubleChartGlue`
(`FormalSchemes.GeneralSeparatedBaseChange`) is the one-factor precedent for the same reading. -/
def ofAlgebraDataGlue : DoubleChartGlue R I A B :=
  (ofAlgebraData gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI hστX hστY).toDoubleChartGlue

/-- **The overlap objects of the smart constructor's glue are the dispatched ones**, by `rfl`.
This is the first of the three hypotheses
`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_bothAlgData` asks for, named
once so that a caller cites it instead of reproducing the `rfl`. -/
theorem ofAlgebraDataGlue_V (p p' : JX × JY) (hne : p ≠ p') :
    (ofAlgebraDataGlue gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI hστX hστY).V p p' hne =
      bothAlgDataV hI gX gY p p' hne :=
  rfl

/-- **The overlap immersions of the smart constructor's glue are the dispatched ones**, in the
`eqToHom`-conjugated shape the square's hypothesis is stated in. The `eqToHom` is that of
`AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraDataGlue_V`, whose two sides are definitionally
but not syntactically equal, so `eqToHom_refl` does not apply to it and the proof is
`Category.id_comp` consumed through the definitional equality instead. -/
theorem ofAlgebraDataGlue_f (p p' : JX × JY) (hne : p ≠ p') :
    (ofAlgebraDataGlue gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI hστX hστY).f p p' hne =
      eqToHom (ofAlgebraDataGlue_V gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI hστX hστY
        p p' hne) ≫ bothAlgDataF hI gX gY p p' hne :=
  (Category.id_comp _).symm

/-- **The overlap transitions of the smart constructor's glue are the dispatched ones**, in the
doubly `eqToHom`-conjugated shape the square's hypothesis is stated in. Both identity laws are
needed here and not only `Category.id_comp`: this hypothesis carries an `eqToHom` at each end. -/
theorem ofAlgebraDataGlue_t (p p' : JX × JY) (hne : p ≠ p') :
    (ofAlgebraDataGlue gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI hστX hστY).t p p' hne =
      eqToHom (ofAlgebraDataGlue_V gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI hστX hστY
          p p' hne) ≫
        bothAlgDataT hI gX gY τX τY p p' hne ≫
        eqToHom (ofAlgebraDataGlue_V gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI hστX hστY
          p' p hne.symm).symm :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

end BothChartedFibreDatum

namespace DoubleChartGlue

variable [∀ i, Algebra R' (A i)] [∀ i, IsScalarTower R R' (A i)]
variable [∀ j, Algebra R' (B j)] [∀ j, IsScalarTower R R' (B j)]
variable (gX : ∀ i _ : JX, A i) (gY : ∀ j _ : JY, B j)
variable (τX : ∀ (i i' : JX), i ≠ i' →
    (awayCompletion (I.map (algebraMap R (A i))) (gX i i') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A i'))) (gX i' i)))
variable (τY : ∀ (j j' : JY), j ≠ j' →
    (awayCompletion (I.map (algebraMap R (B j))) (gY j j') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (B j'))) (gY j' j)))
variable (σX : ∀ (i i' i'' : JX), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R (A i))) (gX i i' * gX i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A i'))) (gX i' i'' * gX i' i)))
variable (σY : ∀ (j j' j'' : JY), j ≠ j' → j ≠ j'' → j' ≠ j'' →
    (awayCompletion (I.map (algebraMap R (B j))) (gY j j' * gY j j'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (B j'))) (gY j' j'' * gY j' j)))
variable (hσcX : ∀ (i i' i'' : JX) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
      (σX i'' i i' h2.symm h3.symm h1)) = AlgEquiv.refl)
variable (hσcY : ∀ (j j' j'' : JY) (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j''),
    (σY j j' j'' h1 h2 h3).trans ((σY j' j'' j h3 h1.symm h2.symm).trans
      (σY j'' j j' h2.symm h3.symm h1)) = AlgEquiv.refl)
variable (τX_symm : ∀ (i i' : JX) (h : i ≠ i'), τX i' i h.symm = (τX i i' h).symm)
variable (τY_symm : ∀ (j j' : JY) (h : j ≠ j'), τY j' j h.symm = (τY j j' h).symm)
variable (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
variable (hστX : ∀ (i i' i'' : JX) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (gX i' i'') (gX i' i) hI) =
      (furtherLocFst I (gX i i') (gX i i'') hI).comp (τX i i' h1).symm.toAlgHom)
variable (hστY : ∀ (j j' j'' : JY) (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j''),
    (σY j j' j'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (gY j' j'') (gY j' j) hI) =
      (furtherLocFst I (gY j j') (gY j j'') hI).comp (τY j j' h1).symm.toAlgHom)
variable (τX' : ∀ (i i' : JX), i ≠ i' →
    (awayCompletion (I'.map (algebraMap R' (A i))) (gX i i') ≃ₐ[R']
      awayCompletion (I'.map (algebraMap R' (A i'))) (gX i' i)))
variable (τY' : ∀ (j j' : JY), j ≠ j' →
    (awayCompletion (I'.map (algebraMap R' (B j))) (gY j j') ≃ₐ[R']
      awayCompletion (I'.map (algebraMap R' (B j'))) (gY j' j)))
variable (σX' : ∀ (i i' i'' : JX), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I'.map (algebraMap R' (A i))) (gX i i' * gX i i'') ≃ₐ[R']
      awayCompletion (I'.map (algebraMap R' (A i'))) (gX i' i'' * gX i' i)))
variable (σY' : ∀ (j j' j'' : JY), j ≠ j' → j ≠ j'' → j' ≠ j'' →
    (awayCompletion (I'.map (algebraMap R' (B j))) (gY j j' * gY j j'') ≃ₐ[R']
      awayCompletion (I'.map (algebraMap R' (B j'))) (gY j' j'' * gY j' j)))
variable (hσcX' : ∀ (i i' i'' : JX) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX' i i' i'' h1 h2 h3).trans ((σX' i' i'' i h3 h1.symm h2.symm).trans
      (σX' i'' i i' h2.symm h3.symm h1)) = AlgEquiv.refl)
variable (hσcY' : ∀ (j j' j'' : JY) (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j''),
    (σY' j j' j'' h1 h2 h3).trans ((σY' j' j'' j h3 h1.symm h2.symm).trans
      (σY' j'' j j' h2.symm h3.symm h1)) = AlgEquiv.refl)
variable (τX'_symm : ∀ (i i' : JX) (h : i ≠ i'), τX' i' i h.symm = (τX' i i' h).symm)
variable (τY'_symm : ∀ (j j' : JY) (h : j ≠ j'), τY' j' j h.symm = (τY' j j' h).symm)
variable (hστX' : ∀ (i i' i'' : JX) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX' i i' i'' h1 h2 h3).symm.toAlgHom.comp
        (furtherLocSnd I' (gX i' i'') (gX i' i) (CompletedTensorProduct.fg_of_map_eq hI hII')) =
      (furtherLocFst I' (gX i i') (gX i i'')
        (CompletedTensorProduct.fg_of_map_eq hI hII')).comp (τX' i i' h1).symm.toAlgHom)
variable (hστY' : ∀ (j j' j'' : JY) (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j''),
    (σY' j j' j'' h1 h2 h3).symm.toAlgHom.comp
        (furtherLocSnd I' (gY j' j'') (gY j' j) (CompletedTensorProduct.fg_of_map_eq hI hII')) =
      (furtherLocFst I' (gY j j') (gY j j'')
        (CompletedTensorProduct.fg_of_map_eq hI hII')).comp (τY' j j' h1).symm.toAlgHom)

/-- **The overlap square of the glued base change, at a pair of glues the smart constructor
builds.** *Reach for this one* when the two glues are ones you produced rather than ones you were
handed: it is
`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_bothAlgData` with all six of
its identifications filled in by
`AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraDataGlue_V` / `..ofAlgebraDataGlue_f` /
`..ofAlgebraDataGlue_t` at each base, so the only hypothesis left is the transition agreement
`AlgebraicGeometry.IsChartTransitionBaseChange`, which is genuinely a condition on the primed
datum and stays one.

The primed base is `(R', I')` with `I' = I·R'`; its finite generation is
`CompletedTensorProduct.fg_of_map_eq hI hII'`, the same term the general statement's own
hypotheses are phrased over, so no transport along the base equation appears anywhere. -/
theorem isBaseChangeOverlapCompatible_ofAlgebraDataGlue
    (hτ : IsChartTransitionBaseChange τX τY τX' τY') :
    (BothChartedFibreDatum.ofAlgebraDataGlue gX gY τX' τY' σX' σY' hσcX' hσcY' τX'_symm τY'_symm
          (CompletedTensorProduct.fg_of_map_eq hI hII') hστX' hστY').IsBaseChangeOverlapCompatible
      (BothChartedFibreDatum.ofAlgebraDataGlue gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI
        hστX hστY) hI hII' :=
  isBaseChangeOverlapCompatible_of_bothAlgData
    (BothChartedFibreDatum.ofAlgebraDataGlue gX gY τX' τY' σX' σY' hσcX' hσcY' τX'_symm τY'_symm
      (CompletedTensorProduct.fg_of_map_eq hI hII') hστX' hστY')
    (BothChartedFibreDatum.ofAlgebraDataGlue gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI
      hστX hστY)
    hI hII' τX τY τX' τY' hτ
    (BothChartedFibreDatum.ofAlgebraDataGlue_V gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI
      hστX hστY)
    (BothChartedFibreDatum.ofAlgebraDataGlue_f gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI
      hστX hστY)
    (BothChartedFibreDatum.ofAlgebraDataGlue_t gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI
      hστX hστY)
    (BothChartedFibreDatum.ofAlgebraDataGlue_V gX gY τX' τY' σX' σY' hσcX' hσcY' τX'_symm τY'_symm
      (CompletedTensorProduct.fg_of_map_eq hI hII') hστX' hστY')
    (BothChartedFibreDatum.ofAlgebraDataGlue_f gX gY τX' τY' σX' σY' hσcX' hσcY' τX'_symm τY'_symm
      (CompletedTensorProduct.fg_of_map_eq hI hII') hστX' hστY')
    (BothChartedFibreDatum.ofAlgebraDataGlue_t gX gY τX' τY' σX' σY' hσcX' hσcY' τX'_symm τY'_symm
      (CompletedTensorProduct.fg_of_map_eq hI hII') hστX' hστY')

section Scheme

variable [TopologicalSpace R] [IsAdicRing I]
variable [∀ i, TopologicalSpace (A i)] [∀ i, IsAdicRing (I.map (algebraMap R (A i)))]
variable [∀ j, TopologicalSpace (B j)] [∀ j, IsAdicRing (I.map (algebraMap R (B j)))]
variable [∀ p : JX × JY, IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))]
variable
  [∀ p : JX × JY, IsAdicRing (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))]

/-- **The glued base change of a pair of glues the smart constructor builds is injective on
points.** *Reach for this one*: this is what the square was for, at the pair a caller actually
has. It is
`AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base_of_bothAlgData` with the same six
identifications filled in, and the square it is stated over is
`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_ofAlgebraDataGlue` above — the
two are one term, so nothing has to be re-elaborated to read this as the injectivity of *that*
comparison. -/
theorem injective_baseChange_base_ofAlgebraDataGlue
    (hτ : IsChartTransitionBaseChange τX τY τX' τY') :
    Function.Injective ⇑((BothChartedFibreDatum.ofAlgebraDataGlue gX gY τX' τY' σX' σY' hσcX'
          hσcY' τX'_symm τY'_symm (CompletedTensorProduct.fg_of_map_eq hI hII') hστX'
          hστY').baseChange
        (BothChartedFibreDatum.ofAlgebraDataGlue gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI
          hστX hστY)
        (CompletedTensorProduct.fg_of_map_eq hI hII') hI hII'
        (isBaseChangeOverlapCompatible_ofAlgebraDataGlue gX gY τX τY σX σY hσcX hσcY τX_symm
          τY_symm hI hII' hστX hστY τX' τY' σX' σY' hσcX' hσcY' τX'_symm τY'_symm hστX' hστY'
          hτ)).base :=
  injective_baseChange_base_of_bothAlgData
    (BothChartedFibreDatum.ofAlgebraDataGlue gX gY τX' τY' σX' σY' hσcX' hσcY' τX'_symm τY'_symm
      (CompletedTensorProduct.fg_of_map_eq hI hII') hστX' hστY')
    (BothChartedFibreDatum.ofAlgebraDataGlue gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI
      hστX hστY)
    hI hII' τX τY τX' τY' hτ
    (BothChartedFibreDatum.ofAlgebraDataGlue_V gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI
      hστX hστY)
    (BothChartedFibreDatum.ofAlgebraDataGlue_f gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI
      hστX hστY)
    (BothChartedFibreDatum.ofAlgebraDataGlue_t gX gY τX τY σX σY hσcX hσcY τX_symm τY_symm hI
      hστX hστY)
    (BothChartedFibreDatum.ofAlgebraDataGlue_V gX gY τX' τY' σX' σY' hσcX' hσcY' τX'_symm τY'_symm
      (CompletedTensorProduct.fg_of_map_eq hI hII') hστX' hστY')
    (BothChartedFibreDatum.ofAlgebraDataGlue_f gX gY τX' τY' σX' σY' hσcX' hσcY' τX'_symm τY'_symm
      (CompletedTensorProduct.fg_of_map_eq hI hII') hστX' hστY')
    (BothChartedFibreDatum.ofAlgebraDataGlue_t gX gY τX' τY' σX' σY' hσcX' hσcY' τX'_symm τY'_symm
      (CompletedTensorProduct.fg_of_map_eq hI hII') hστX' hστY')

end Scheme

end DoubleChartGlue

end AlgebraicGeometry

end
