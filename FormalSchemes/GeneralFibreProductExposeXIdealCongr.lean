import FormalSchemes.GeneralFibreProductExposeXAlgebraData

set_option linter.style.header false

/-!
# The glued `X` of an affine-charted datum does not see the base ring

`AlgebraicGeometry.AffineChartedFibreDatumX` (`FormalSchemes.GeneralFibreProductExposeX`) packages
a formal scheme `X` presented by basic-open charts over an adic base `(R, I)`, and
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData`
(`FormalSchemes.GeneralFibreProductExposeXAlgebraData`) builds one from pure algebra data. A change
of the base — replacing `(R, I)` by an `(R', I')` that induces the *same* ideal family on the chart
algebras — produces a second datum, and nothing on the tree could compare the two. This file
supplies the comparison:

```
AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr :
  (AffineChartedFibreDatumX.ofAlgebraData (B := B') hI' A g τ' τ'_symm σ' hστ' hσc').xGlued =
    (AffineChartedFibreDatumX.ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xGlued
```

on the hypotheses that the induced ideal families agree and that the transitions agree as
functions. The conclusion is an **equality of formal schemes**, not an isomorphism.

## The hypothesis shape, which is the design question this file answers

The families are compared by a single **function-level** equation

```
(fun i => I'.map (algebraMap R' (A i))) = fun i => I.map (algebraMap R (A i))
```

and the transitions by pointwise `HEq` of their **coercions**, `HEq (⇑(τ' i j h)) (⇑(τ i j h))` and
the same for `σ`. Four other spellings were considered and each is ruled out by a measurement:

* **A pointwise ideal hypothesis `∀ i, K i = I.map (algebraMap R (A i))`.** `subst` refuses it:
  `K i` is an application, not a variable. On this tree an ideal-indexed family has to be
  abstracted *whole* before it will move.
* **`rw` or `simp only` with the function-level equation, at the concrete families.** `rw` reports
  *motive is not type correct* and `simp only` reports no progress. The ideal occurs inside the
  `Ideal.FG` proof feeding `FormalSpectrum.isOpenImmersion_basicOpenChart`, so abstracting it
  breaks the instance that the pullbacks in the geometric fields are taken with respect to.
* **`congr`, at either depth and in its `!` form.** `congr 1` leaves a goal unsolved, and
  `congr! 2` on the transition alone reduces to a heterogeneous equation between two
  `FormalSpectrum.locallyRingedSpaceMap` applications and stops there. That residual goal is
  exactly `FormalSpectrum.locallyRingedSpaceMap_symm_heq` below, which is why the file has it.
* **An equation on the algebra equivalences themselves.** There is none to write: `τ` is
  `≃ₐ[R]` and `τ'` is `≃ₐ[R']`, and a caller with a factorisation through `Spf I'` has no reason to
  be able to compare them at that level. The coercions are the strongest thing that is both true
  and producible, and they are enough — `AlgebraicGeometry.awayCompletionTransition` reads only
  the underlying ring homomorphism of the inverse equivalence.

`HEq` rather than `Eq` is forced and is not a weakness of the statement: before the ideal families
are identified, `awayCompletion (I'·A_i) (g i j)` and `awayCompletion (I·A_i) (g i j)` are distinct
types, so there is no type in which an ordinary equation could be stated at all. Every `HEq` here
is discharged by `subst` the moment the family equation is available.

## The route

`AlgebraicGeometry.AffineChartedFibreDatumX.xGlueDataOfIdeals` repeats the body of
`AlgebraicGeometry.AffineChartedFibreDatumX.xGlueData'` with the induced family `fun i ↦ I·A_i`
replaced by a family `K` that is a **variable**, and with the geometric fields taken as arguments.
The base ring disappears from it, because it entered
`AlgebraicGeometry.AffineChartedFibreDatumX.xGlueData'` only through that family and through the
types of the transitions. Then

```
AffineChartedFibreDatumX.xGlued_eq_ofIdeals (D : AffineChartedFibreDatumX R I hI B) :
  D.xGlued = xGluedOfIdeals D.g (fun i => I.map (algebraMap R (D.A i))) _ _ _ D.xt' D.xt_fac
    D.xcocycle
```

holds **by `rfl`**, and that single `rfl` is the mathematical content of this file: it says that
`AlgebraicGeometry.AffineChartedFibreDatumX.xGlued` reads exactly five things off a datum — the
chart algebras, the away elements, the induced ideal family, the single-overlap transition *as a
morphism*, and the three geometric fields — and nothing else. With `K` a variable the congruence
is then `subst` plus two `funext`s, and the hypothesis list above is minimal by construction
rather than by inspection.

The three lemmas in `FormalSpectrum` are the transports that make the `HEq` hypotheses reachable
from the coercion level; each is the same `subst`-on-a-variable-ideal idiom as
`FormalSpectrum.locallyRingedSpaceObjCongr` (`FormalSchemes.GeneralSeparatedHomIdentity`), one
layer up.

## Equality, not an isomorphism

An isomorphism would have been enough for the intended consumer, since
`AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` transports along
`AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_of_iso`. It is not needed: the two glued objects
are literally the same term once the family equation is substituted, so the equality is available
and is strictly stronger. Nothing here constructs an isomorphism, and a consumer that wants one
should take `eqToIso` of the equality rather than have a second definition to keep in step.

## What is *not* here

* **No base change of the fibre product.** `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` is a
  statement about `X ×_{Spf I} X`, whose charts are the completed tensor products `A_i ⊗̂_R A_j`;
  those move with the base and this file says nothing about them. That comparison is a separate
  question and is the hard third of the keystone.
* **No algebra half.** Producing `Algebra R' (A i)`, the equality of induced ideal families, and
  the `R'`-linearity of `τ` and `σ` from a geometric factorisation through `Spf I'` is not done
  here; all of it is taken as hypotheses, which is what makes this file small.
* **No new smart constructor.** `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` is used
  unchanged; the definitions here re-present its output and do not replace it.

## Placement, and what this module costs

Over `FormalSchemes.GeneralFibreProductExposeXAlgebraData`: forward closure **79**, reverse closure
**5**. The three transports are general and each has a natural home earlier in the tree — the first
two beside `FormalSpectrum.locallyRingedSpaceMap` in `FormalSchemes.SpfMap`, whose reverse closure
is **504**, and the third beside `FormalSpectrum.basicOpenChartOverlapIso` in
`FormalSchemes.BasicOpenChartOverlap`, whose reverse closure is **80**, both against this file's
**5**. They are kept here on that ratio and because each has exactly one consumer in code, here;
the disposition is worth re-costing when a second appears.

`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr` has two consumers.
`FormalSchemes.AwayBaseChangeGluedX` discharges its ideal-family hypothesis along a tower, and at a
basic open of the base (issue 2028). `FormalSchemes.GeneralSeparatedBaseChange` is the §10.15
consumer this paragraph was written expecting (issue 2035): it reads the congruence at a diagonal
datum, to identify the two glued factors that a base change of separatedness compares. Reaching
this file from the §10.15 layer is cheap, as that module's own imports bear out:
`FormalSchemes.GeneralSeparatedHomLocal` has forward
closure **182**, and the union of that with this file's is **187** — five modules, of which this
one is itself.

## Main definitions and results

* `AlgebraicGeometry.AffineChartedFibreDatumX.xGlueDataOfIdeals`,
  `AlgebraicGeometry.AffineChartedFibreDatumX.xLrsGlueDataOfIdeals`,
  `AlgebraicGeometry.AffineChartedFibreDatumX.xFormalGlueDataOfIdeals` and
  `AlgebraicGeometry.AffineChartedFibreDatumX.xGluedOfIdeals`: the `X`-side glue at an arbitrary
  family of ideals.
* `AlgebraicGeometry.AffineChartedFibreDatumX.xGlueData'_eq_ofIdeals` and
  `AlgebraicGeometry.AffineChartedFibreDatumX.xGlued_eq_ofIdeals`: the two presentations agree, by
  `rfl`.
* `AlgebraicGeometry.AffineChartedFibreDatumX.xGluedOfIdeals_congr`: **the congruence**, in the
  ideal family and the two geometric data.
* `FormalSpectrum.awayRingEquiv_heq_of_coe_heq`,
  `FormalSpectrum.locallyRingedSpaceMap_symm_heq` and
  `FormalSpectrum.basicOpenChartOverlapIso_conj_heq`: the three transports along an equality of
  ideals.
* `AlgebraicGeometry.AffineChartedFibreDatumX.awayCompletionTransition_heq` and
  `AlgebraicGeometry.AffineChartedFibreDatumX.xAlgDataT'_heq`: the derived geometric data of
  `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` transport.
* `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr`: **the base change of a
  smart-constructor datum leaves `X` unmoved.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace FormalSpectrum

/-! ### Three transports along an equality of ideals -/

section Transport

variable {S T : Type u} [CommRing S] [CommRing T]

/-- **Two completed-localization ring equivalences over equal ideals are heterogeneously equal as
soon as their underlying functions are.** The ideals are *variables* here and the caller
instantiates them at the two families being compared; that is the whole reason this lemma exists,
since `Ideal.map (algebraMap R S) I` is an application and `subst` cannot reach it. -/
theorem awayRingEquiv_heq_of_coe_heq {K K' : Ideal S} {L L' : Ideal T} (hK : K = K') (hL : L = L')
    {s : S} {t : T} {e : awayCompletion K s ≃+* awayCompletion L t}
    {e' : awayCompletion K' s ≃+* awayCompletion L' t}
    (he : HEq (⇑e) (⇑e')) : HEq e e' := by
  subst hK
  subst hL
  exact heq_of_eq (DFunLike.coe_injective (eq_of_heq he))

/-- **The chart-level structural morphism transports along an equality of ideals.** This is the
`awayCompletion` analogue of `FormalSpectrum.locallyRingedSpaceObjCongr`, in `HEq` form because the
two source objects are only propositionally equal. -/
theorem locallyRingedSpaceMap_symm_heq {K K' : Ideal S} {L L' : Ideal T} (hK : K = K')
    (hL : L = L') {s : S} {t : T} {e : awayCompletion K s ≃+* awayCompletion L t}
    {e' : awayCompletion K' s ≃+* awayCompletion L' t} (he : HEq e e')
    (h : awayCompletionIdeal L t ≤ (awayCompletionIdeal K s).comap e.symm.toRingHom)
    (h' : awayCompletionIdeal L' t ≤ (awayCompletionIdeal K' s).comap e'.symm.toRingHom) :
    HEq (locallyRingedSpaceMap (awayCompletionIdeal L t) (awayCompletionIdeal K s)
        e.symm.toRingHom h)
      (locallyRingedSpaceMap (awayCompletionIdeal L' t) (awayCompletionIdeal K' s)
        e'.symm.toRingHom h') := by
  subst hK
  subst hL
  cases he
  rfl

/-- **Conjugating by the two basic-open overlap identifications preserves the transport.** The
shape is exactly the body of `AlgebraicGeometry.AffineChartedFibreDatumX.xAlgDataT'`, with the
middle map left abstract. -/
theorem basicOpenChartOverlapIso_conj_heq {K K' : Ideal S} {L L' : Ideal T} (hK : K = K')
    (hL : L = L') (hKfg : K.FG) (hK'fg : K'.FG) (hLfg : L.FG) (hL'fg : L'.FG) (a b : S) (c d : T)
    {m : locallyRingedSpaceObj (awayCompletionIdeal K (a * b)) ⟶
      locallyRingedSpaceObj (awayCompletionIdeal L (c * d))}
    {m' : locallyRingedSpaceObj (awayCompletionIdeal K' (a * b)) ⟶
      locallyRingedSpaceObj (awayCompletionIdeal L' (c * d))} (hm : HEq m m') :
    letI := isOpenImmersion_basicOpenChart K a hKfg
    letI := isOpenImmersion_basicOpenChart K b hKfg
    letI := isOpenImmersion_basicOpenChart L c hLfg
    letI := isOpenImmersion_basicOpenChart L d hLfg
    letI := isOpenImmersion_basicOpenChart K' a hK'fg
    letI := isOpenImmersion_basicOpenChart K' b hK'fg
    letI := isOpenImmersion_basicOpenChart L' c hL'fg
    letI := isOpenImmersion_basicOpenChart L' d hL'fg
    HEq ((basicOpenChartOverlapIso K a b hKfg).inv ≫ m ≫ (basicOpenChartOverlapIso L c d hLfg).hom)
      ((basicOpenChartOverlapIso K' a b hK'fg).inv ≫ m' ≫
        (basicOpenChartOverlapIso L' c d hL'fg).hom) := by
  subst hK
  subst hL
  cases hm
  rfl

end Transport

end FormalSpectrum

namespace AlgebraicGeometry

namespace AffineChartedFibreDatumX

/-! ### The `X`-side glue at an arbitrary family of ideals -/

section OfIdeals

variable {J : Type u} {A : J → Type u} [∀ i, CommRing (A i)]
variable [topology : ∀ i : J, TopologicalSpace (A i)]
variable (g : ∀ (i : J), J → A i) (K : ∀ i : J, Ideal (A i)) (hK : ∀ i : J, (K i).FG)

/-- **The `X`-side glue datum at an arbitrary family of ideals.** Term for term the body of
`AlgebraicGeometry.AffineChartedFibreDatumX.xGlueData'`, with the induced family
`fun i ↦ I·A_i` replaced by a family `K` that is a *variable*, and with the geometric fields taken
as arguments rather than read off a datum. The base ring has disappeared: it entered
`AlgebraicGeometry.AffineChartedFibreDatumX.xGlueData'` only through that family and through the
types of the transitions. -/
def xGlueDataOfIdeals
    (t : ∀ (i j : J), i ≠ j →
      (locallyRingedSpaceObj (awayCompletionIdeal (K i) (g i j)) ⟶
        locallyRingedSpaceObj (awayCompletionIdeal (K j) (g j i))))
    (t_inv : ∀ (i j : J) (h : i ≠ j), t i j h ≫ t j i h.symm = 𝟙 _)
    (t' : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      letI := isOpenImmersion_basicOpenChart (K i) (g i j) (hK i)
      letI := isOpenImmersion_basicOpenChart (K i) (g i k) (hK i)
      letI := isOpenImmersion_basicOpenChart (K j) (g j k) (hK j)
      letI := isOpenImmersion_basicOpenChart (K j) (g j i) (hK j)
      (pullback (basicOpenChart (K i) (g i j)) (basicOpenChart (K i) (g i k)) ⟶
        pullback (basicOpenChart (K j) (g j k)) (basicOpenChart (K j) (g j i))))
    (t_fac : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      letI := isOpenImmersion_basicOpenChart (K i) (g i j) (hK i)
      letI := isOpenImmersion_basicOpenChart (K i) (g i k) (hK i)
      letI := isOpenImmersion_basicOpenChart (K j) (g j k) (hK j)
      letI := isOpenImmersion_basicOpenChart (K j) (g j i) (hK j)
      t' i j k hij hik hjk ≫
          pullback.snd (basicOpenChart (K j) (g j k)) (basicOpenChart (K j) (g j i)) =
        pullback.fst (basicOpenChart (K i) (g i j)) (basicOpenChart (K i) (g i k)) ≫ t i j hij)
    (cocycle : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      letI := isOpenImmersion_basicOpenChart (K i) (g i j) (hK i)
      letI := isOpenImmersion_basicOpenChart (K i) (g i k) (hK i)
      letI := isOpenImmersion_basicOpenChart (K j) (g j k) (hK j)
      letI := isOpenImmersion_basicOpenChart (K j) (g j i) (hK j)
      letI := isOpenImmersion_basicOpenChart (K k) (g k i) (hK k)
      letI := isOpenImmersion_basicOpenChart (K k) (g k j) (hK k)
      t' i j k hij hik hjk ≫ t' j k i hjk hij.symm hik.symm ≫
        t' k i j hik.symm hjk.symm hij = 𝟙 _) :
    CategoryTheory.GlueData' LocallyRingedSpace.{u} where
  J := J
  U := fun i => locallyRingedSpaceObj (K i)
  V := fun i j _ => locallyRingedSpaceObj (awayCompletionIdeal (K i) (g i j))
  f := fun i j _ => basicOpenChart (K i) (g i j)
  f_mono := fun i j _ => by
    haveI := isOpenImmersion_basicOpenChart (K i) (g i j) (hK i)
    infer_instance
  f_hasPullback := fun i j k _ _ => by
    haveI := isOpenImmersion_basicOpenChart (K i) (g i j) (hK i)
    haveI := isOpenImmersion_basicOpenChart (K i) (g i k) (hK i)
    infer_instance
  t := t
  t' := t'
  t_fac := t_fac
  t_inv := t_inv
  cocycle := cocycle

variable [adic : ∀ i : J, IsAdicRing (K i)]
variable (t : ∀ (i j : J), i ≠ j →
  (locallyRingedSpaceObj (awayCompletionIdeal (K i) (g i j)) ⟶
    locallyRingedSpaceObj (awayCompletionIdeal (K j) (g j i))))
variable (t_inv : ∀ (i j : J) (h : i ≠ j), t i j h ≫ t j i h.symm = 𝟙 _)
variable (t' : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
  letI := isOpenImmersion_basicOpenChart (K i) (g i j) (hK i)
  letI := isOpenImmersion_basicOpenChart (K i) (g i k) (hK i)
  letI := isOpenImmersion_basicOpenChart (K j) (g j k) (hK j)
  letI := isOpenImmersion_basicOpenChart (K j) (g j i) (hK j)
  (pullback (basicOpenChart (K i) (g i j)) (basicOpenChart (K i) (g i k)) ⟶
    pullback (basicOpenChart (K j) (g j k)) (basicOpenChart (K j) (g j i))))
variable (t_fac : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
  letI := isOpenImmersion_basicOpenChart (K i) (g i j) (hK i)
  letI := isOpenImmersion_basicOpenChart (K i) (g i k) (hK i)
  letI := isOpenImmersion_basicOpenChart (K j) (g j k) (hK j)
  letI := isOpenImmersion_basicOpenChart (K j) (g j i) (hK j)
  t' i j k hij hik hjk ≫
      pullback.snd (basicOpenChart (K j) (g j k)) (basicOpenChart (K j) (g j i)) =
    pullback.fst (basicOpenChart (K i) (g i j)) (basicOpenChart (K i) (g i k)) ≫ t i j hij)
variable (cocycle : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
  letI := isOpenImmersion_basicOpenChart (K i) (g i j) (hK i)
  letI := isOpenImmersion_basicOpenChart (K i) (g i k) (hK i)
  letI := isOpenImmersion_basicOpenChart (K j) (g j k) (hK j)
  letI := isOpenImmersion_basicOpenChart (K j) (g j i) (hK j)
  letI := isOpenImmersion_basicOpenChart (K k) (g k i) (hK k)
  letI := isOpenImmersion_basicOpenChart (K k) (g k j) (hK k)
  t' i j k hij hik hjk ≫ t' j k i hjk hij.symm hik.symm ≫
    t' k i j hik.symm hjk.symm hij = 𝟙 _)

/-- **The `X`-side locally-ringed-space glue data at an arbitrary family of ideals**: the body of
`AlgebraicGeometry.AffineChartedFibreDatumX.xLrsGlueData`, with the same substitution. -/
def xLrsGlueDataOfIdeals : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData'
      (xGlueDataOfIdeals g K hK t t_inv t' t_fac cocycle) with
    f_open := by
      rintro i j
      simp only [xGlueDataOfIdeals, CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · haveI := isOpenImmersion_basicOpenChart (K i) (g i j) (hK i)
        exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
          (eqToHom _ ≫ basicOpenChart (K i) (g i j))) }

/-- **The `X`-side formal-scheme glue data at an arbitrary family of ideals**: the body of
`AlgebraicGeometry.AffineChartedFibreDatumX.xFormalGlueData`, with the same substitution. -/
def xFormalGlueDataOfIdeals : FormalScheme.GlueData.{u} :=
  { toLocallyRingedSpaceGlueData := xLrsGlueDataOfIdeals g K hK t t_inv t' t_fac cocycle
    isFormalScheme := fun i => ⟨FormalScheme.Spf (K i), ⟨Iso.refl _⟩⟩ }

/-- **The glued `X` at an arbitrary family of ideals.** -/
def xGluedOfIdeals : FormalScheme.{u} :=
  (xFormalGlueDataOfIdeals g K hK t t_inv t' t_fac cocycle).gluedFormalScheme

end OfIdeals

/-! ### The two presentations agree definitionally -/

section Compare

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable {B : Type u} [CommRing B] [Algebra R B]

/-- **The glue datum of a datum is the general one at its induced ideal family**, by `rfl`. This is
what makes the congruence below possible: it isolates *everything*
`AlgebraicGeometry.AffineChartedFibreDatumX.xGlueData'` reads off a datum — the chart algebras, the
away elements, the induced ideal family, the single-overlap transition as a morphism, and the three
geometric fields — and nothing else, in particular not the base ring. -/
theorem xGlueData'_eq_ofIdeals (D : AffineChartedFibreDatumX R I hI B) :
    letI := D.commRing
    letI := D.algebra
    letI := D.topology
    D.xGlueData' = xGlueDataOfIdeals D.g (fun i => I.map (algebraMap R (D.A i)))
      (fun _ => hI.map _)
      (fun i j h => awayCompletionTransition (D.g i j) (D.g j i) (D.τ i j h))
      (fun i j h => by
        rw [D.τ_symm i j h]
        exact awayCompletionTransition_comp (D.g i j) (D.g j i) (D.τ i j h))
      D.xt' D.xt_fac D.xcocycle :=
  rfl

/-- **The glued `X` of a datum is the general one at its induced ideal family**, by `rfl`. -/
theorem xGlued_eq_ofIdeals (D : AffineChartedFibreDatumX R I hI B) :
    letI := D.commRing
    letI := D.algebra
    letI := D.topology
    letI := D.isAdic
    D.xGlued = xGluedOfIdeals D.g (fun i => I.map (algebraMap R (D.A i))) (fun _ => hI.map _)
      (fun i j h => awayCompletionTransition (D.g i j) (D.g j i) (D.τ i j h))
      (fun i j h => by
        rw [D.τ_symm i j h]
        exact awayCompletionTransition_comp (D.g i j) (D.g j i) (D.τ i j h))
      D.xt' D.xt_fac D.xcocycle :=
  rfl

end Compare

/-! ### The congruence -/

section Congr

variable {J : Type u} {A : J → Type u} [∀ i, CommRing (A i)]
variable [topology : ∀ i : J, TopologicalSpace (A i)] {g : ∀ (i : J), J → A i}

/-- **The glued `X` at an arbitrary ideal family is a congruence in that family.** Given an
equality of the two families and pointwise heterogeneous equalities of the single- and
triple-overlap geometric data, the glued formal schemes are *equal*, not merely isomorphic. The
`HEq`s are unavoidable and not a weakness of the statement: the two transitions live over objects
that are only propositionally equal, so there is no type in which an ordinary equation could be
written. -/
theorem xGluedOfIdeals_congr {K K' : ∀ i : J, Ideal (A i)} (hK : K = K')
    {hKfg : ∀ i : J, (K i).FG} {hK'fg : ∀ i : J, (K' i).FG}
    [adic : ∀ i : J, IsAdicRing (K i)] [adic' : ∀ i : J, IsAdicRing (K' i)]
    {t : ∀ (i j : J), i ≠ j →
      (locallyRingedSpaceObj (awayCompletionIdeal (K i) (g i j)) ⟶
        locallyRingedSpaceObj (awayCompletionIdeal (K j) (g j i)))}
    {t_inv} {t'} {t_fac} {cocycle}
    {u : ∀ (i j : J), i ≠ j →
      (locallyRingedSpaceObj (awayCompletionIdeal (K' i) (g i j)) ⟶
        locallyRingedSpaceObj (awayCompletionIdeal (K' j) (g j i)))}
    {u_inv} {u'} {u_fac} {ucocycle}
    (ht : ∀ (i j : J) (h : i ≠ j), HEq (t i j h) (u i j h))
    (ht' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (t' i j k hij hik hjk) (u' i j k hij hik hjk)) :
    xGluedOfIdeals g K hKfg t t_inv t' t_fac cocycle =
      xGluedOfIdeals g K' hK'fg u u_inv u' u_fac ucocycle := by
  subst hK
  have hteq : t = u := by
    funext i j h
    exact eq_of_heq (ht i j h)
  subst hteq
  have ht'eq : t' = u' := by
    funext i j k hij hik hjk
    exact eq_of_heq (ht' i j k hij hik hjk)
  subst ht'eq
  rfl

end Congr

/-! ### The derived geometric data transport -/

section Derived

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable {R' : Type u} [CommRing R'] {I' : Ideal R'} (hI' : I'.FG)
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)]
variable [∀ i, Algebra R (A i)] [∀ i, Algebra R' (A i)]
variable (g : ∀ (i : J), J → A i)

/-- **The single-overlap transition transports.** Only the underlying function of the algebra
equivalence is used, which is why the hypothesis is an equation on `⇑τ'` and `⇑τ` and not on the
algebra equivalences themselves — those live over different scalar rings and cannot be compared at
all. -/
theorem awayCompletionTransition_heq
    {τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i))}
    {τ' : ∀ (i j : J), i ≠ j →
      (awayCompletion (I'.map (algebraMap R' (A i))) (g i j) ≃ₐ[R']
        awayCompletion (I'.map (algebraMap R' (A j))) (g j i))}
    (hK : (fun i => I'.map (algebraMap R' (A i))) = fun i => I.map (algebraMap R (A i)))
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h)))
    (i j : J) (h : i ≠ j) :
    HEq (awayCompletionTransition (g i j) (g j i) (τ' i j h))
      (awayCompletionTransition (g i j) (g j i) (τ i j h)) :=
  locallyRingedSpaceMap_symm_heq (congrFun hK i) (congrFun hK j)
    (awayRingEquiv_heq_of_coe_heq (congrFun hK i) (congrFun hK j) (hτ i j h)) _ _

/-- **The derived `X`-side triple-overlap transition transports**, on the same hypothesis one level
up: `AlgebraicGeometry.AffineChartedFibreDatumX.xAlgDataT'` conjugates
`AlgebraicGeometry.awayCompletionTransition` by the two basic-open overlap identifications, and
both conjugating isomorphisms are functions of the ideal family alone. -/
theorem xAlgDataT'_heq
    {σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i))}
    {σ' : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I'.map (algebraMap R' (A i))) (g i j * g i k) ≃ₐ[R']
        awayCompletion (I'.map (algebraMap R' (A j))) (g j k * g j i))}
    (hK : (fun i => I'.map (algebraMap R' (A i))) = fun i => I.map (algebraMap R (A i)))
    (hσ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (⇑(σ' i j k hij hik hjk)) (⇑(σ i j k hij hik hjk)))
    (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    HEq (xAlgDataT' hI' A g σ' i j k hij hik hjk) (xAlgDataT' hI A g σ i j k hij hik hjk) :=
  basicOpenChartOverlapIso_conj_heq (congrFun hK i) (congrFun hK j) _ _ _ _ (g i j) (g i k)
    (g j k) (g j i)
    (locallyRingedSpaceMap_symm_heq (congrFun hK i) (congrFun hK j)
      (awayRingEquiv_heq_of_coe_heq (congrFun hK i) (congrFun hK j) (hσ i j k hij hik hjk)) _ _)

end Derived

/-! ### The base change of a datum built from algebra data -/

section BaseChange

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable {B : Type u} [CommRing B] [Algebra R B]
variable {R' : Type u} [CommRing R'] {I' : Ideal R'} (hI' : I'.FG)
variable {B' : Type u} [CommRing B'] [Algebra R' B']
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)]
variable [∀ i, Algebra R (A i)] [∀ i, Algebra R' (A i)]
variable (g : ∀ (i : J), J → A i)
variable [topology : ∀ i : J, TopologicalSpace (A i)]
variable [isAdicA : ∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]
variable [isAdicA' : ∀ i : J, IsAdicRing (I'.map (algebraMap R' (A i)))]

/-- **The `X` of a smart-constructor datum does not see the base ring.** Two adic bases `(R, I)`
and `(R', I')`, one chart family `A` that is an algebra over both, one away family `g`, and two
sets of algebra data whose induced ideal families agree and whose transitions agree as functions:
the two glued formal schemes are **equal**.

This is the primitive a base change of an `AlgebraicGeometry.AffineChartedFibreDatumX` needs, and
the whole of its proof is `AlgebraicGeometry.AffineChartedFibreDatumX.xGlued_eq_ofIdeals` — the
`rfl` that says `AlgebraicGeometry.AffineChartedFibreDatumX.xGlued` reads only the ideal family
and the two geometric data off the datum. -/
theorem ofAlgebraData_xGlued_congr
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toAlgHom.comp
          (CompletedTensorAwayInterchange.furtherLocSnd I (g j k) (g j i) hI) =
        (CompletedTensorAwayInterchange.furtherLocFst I (g i j) (g i k) hI).comp
          (τ i j hij).symm.toAlgHom)
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))
    (τ' : ∀ (i j : J), i ≠ j →
      (awayCompletion (I'.map (algebraMap R' (A i))) (g i j) ≃ₐ[R']
        awayCompletion (I'.map (algebraMap R' (A j))) (g j i)))
    (τ'_symm : ∀ (i j : J) (h : i ≠ j), τ' j i h.symm = (τ' i j h).symm)
    (σ' : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I'.map (algebraMap R' (A i))) (g i j * g i k) ≃ₐ[R']
        awayCompletion (I'.map (algebraMap R' (A j))) (g j k * g j i)))
    (hστ' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ' i j k hij hik hjk).symm.toAlgHom.comp
          (CompletedTensorAwayInterchange.furtherLocSnd I' (g j k) (g j i) hI') =
        (CompletedTensorAwayInterchange.furtherLocFst I' (g i j) (g i k) hI').comp
          (τ' i j hij).symm.toAlgHom)
    (hσc' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ' i j k hij hik hjk).trans ((σ' j k i hjk hij.symm hik.symm).trans
        (σ' k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R')
          (A₁ := awayCompletion (I'.map (algebraMap R' (A i))) (g i j * g i k)))
    (hK : (fun i => I'.map (algebraMap R' (A i))) = fun i => I.map (algebraMap R (A i)))
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h)))
    (hσ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (⇑(σ' i j k hij hik hjk)) (⇑(σ i j k hij hik hjk))) :
    (AffineChartedFibreDatumX.ofAlgebraData (B := B') hI' A g τ' τ'_symm σ' hστ' hσc').xGlued =
      (AffineChartedFibreDatumX.ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xGlued :=
  xGluedOfIdeals_congr (hKfg := fun _ => hI'.map _) (hK'fg := fun _ => hI.map _) hK
    (awayCompletionTransition_heq A g hK hτ) (xAlgDataT'_heq hI hI' A g hK hσ)

end BaseChange

end AffineChartedFibreDatumX

end AlgebraicGeometry
