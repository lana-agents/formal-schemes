import FormalSchemes.ChartedSchemeDatumAlgebraData
import FormalSchemes.CompletionAwayOverlapLegs

set_option linter.style.header false

/-!
# The glued formal completion of a charted scheme, at an arbitrary index (EGA I, 10.8)

`FormalSchemes/CompletionGlueTwoPatch.lean` glues two affine formal completions along a common
basic open, on `ULift Bool`, where the three triple-overlap fields of a
`CategoryTheory.GlueData'` are vacuous. `FormalSchemes/CompletionBasicOpenGlue.lean` glues the
basic-open completions of a **single** affine at an arbitrary index, with a real cocycle. This file
is the remaining case, and the one EGA I 10.8 is about: an arbitrary family of affine charts with
**unrelated** coordinate rings, each carrying an ideal of its own, glued along basic opens.

It is the completion half of `AlgebraicGeometry.ChartedSchemeDatum`
(`FormalSchemes.ChartedSchemeDatum`), whose `specGlued` is the ambient scheme. The morphism
`X_{/Y} ⟶ X` between the two is `FormalSchemes.ChartedCompletionToScheme`.

## Why the input is a new structure and not a `ChartedSchemeDatum`

A `ChartedSchemeDatum` carries its triple-overlap transition `t'` as a morphism of `Spec`-pullbacks
— opaque geometric data. The completion side cannot use it: `formalCompletion.map` needs a **ring**
homomorphism, and completion is not a functor backwards, so no ring map is recoverable from a
morphism of formal spectra without full faithfulness of `Spec` and a transport through
`AlgebraicGeometry.specAwayOverlapIso`. Worse, `formalCompletion.map` also needs an *ideal*
compatibility for the triple transition, and a `ChartedSchemeDatum` contains no such datum at all.

The resolution is that the *algebra* the `Spec` side is built from is already enough.
`AlgebraicGeometry.ChartedSchemeDatum.ofAlgebraData`
(`FormalSchemes.ChartedSchemeDatumAlgebraData`) derives `t'`, `t_fac` and `cocycle` from a family
of localization isomorphisms `σ i j k` with two laws. `ChartedCompletionDatum` below carries
exactly that data, plus the finite generation `hK` that `formalCompletion` demands of its object,
and `ChartedCompletionDatum.toChartedSchemeDatum` is `ofAlgebraData` at its own fields. So one
datum produces both sides, which is what the morphism between them needs anyway.

**`ChartedSchemeDatum` itself is unchanged.** The finite-generation field is here rather than
there, which is the cheaper of the two options that file's own "What is *not* proved" section
lists.

## The ideal compatibility of the triple transition is derived, not assumed

`ChartedCompletionDatum.hσK` — that `σ i j k` carries `K i · (C i)_{g_ij·g_ik}` onto
`K j · (C j)_{g_jk·g_ji}` — is **not** a field. It follows from `hθ` and `hσθ`: the structure map of
a triple overlap factors through the double overlap by
`formalCompletion.awayToAwayLeft_comp_algebraMap`, and `hσθ` moves `σ` past that factorisation, so
three `Ideal.map_map`s reduce it to the double-overlap compatibility `hθ`.

## Why `FormalSchemes.CompletionBasicOpenGlue`'s proofs do not port

That file proves its `t_fac`, `t_inv` and `cocycle` by `cancel_mono` against the map down to the
**common ambient object** `Spf R^` that every chart of a single affine has. Here there is no such
object: the charts are completions of unrelated rings and nothing lies under all of them. The
proofs below follow the `Spec` side instead
(`AlgebraicGeometry.ChartedSchemeDatum.specAlgDataT'_fac`): strip the two overlap identifications
with the uncomposed leg lemmas of `FormalSchemes.CompletionAwayOverlapLegs`, which leaves an
equation between two `formalCompletion.map`s, and read it off `hσθ`.

## Main definitions and results

* `AlgebraicGeometry.ChartedCompletionDatum`: the datum — chart rings with their own finitely
  generated ideals, away elements, localization transitions `θ` and `σ`, and their laws.
* `AlgebraicGeometry.ChartedCompletionDatum.toChartedSchemeDatum`,
  `..specGlued`, `..specι`: the ambient scheme, by `ofAlgebraData`.
* `AlgebraicGeometry.ChartedCompletionDatum.hσK`, `..hθ_symm`: the two derived ideal
  compatibilities.
* `AlgebraicGeometry.ChartedCompletionDatum.chart`, `..overlap`, `..overlapImmersion`,
  `..overlapIso`: the completion charts, their overlaps, the basic-open immersions between them and
  the double transition.
* `AlgebraicGeometry.ChartedCompletionDatum.tripleTransition` with `..tripleTransition_fac` and
  `..tripleTransition_cocycle`: the derived triple-overlap datum.
* `AlgebraicGeometry.ChartedCompletionDatum.completionGlueData'`, `..completionLRSGlueData`,
  `..completionFormalGlueData`, `..completionGlued`: the glue datum and the glued formal scheme,
  with `..completionι` its charts, `..completionι_isOpenImmersion` and
  `..completionGlued_jointly_surjective`.
* `AlgebraicGeometry.ChartedCompletionDatum.ofTwoPatch`: the two-patch line's own input, read as a
  completion datum, with `..ofTwoPatch_K_false` and `..ofTwoPatch_K_true`. Its two ideals are
  `I : Ideal A` and `J : Ideal B`, in different rings.
* `AlgebraicGeometry.ChartedCompletionDatum.completion_glue_condition`, `..completionDesc`,
  `..completionι_comp_desc`, `..completionGlued_hom_ext`: the relation that makes morphisms *out
  of* the glued completion definable, and the descent principle it unlocks.

## What is *not* proved

* **The only datum constructed here is `ChartedCompletionDatum.ofTwoPatch`, and its triple fields
  are vacuous.** On `ULift Bool` no triple of indices is pairwise distinct, so `σ`, `hσθ` and `hσc`
  are `False.elim` and nothing exercises them. The instance that does is
  `AlgebraicGeometry.SpecThreeChartCover.completionDatum`
  (`FormalSchemes.SpecThreeChartCompletion`), on `ULift (Fin 3)`. The two are complementary:
  the three-chart datum evaluates the triple fields but takes all its ideals from one `(A, I)`,
  while `AlgebraicGeometry.projectiveLineDatum` (`FormalSchemes.ProjectiveLineCompletion`), built
  from `ofTwoPatch`, has independent chart ideals with one of them `⊤`.
* Nothing here relates `completionGlued` to `specGlued`; that is
  `FormalSchemes.ChartedCompletionToScheme`.
* No universal property is claimed for `completionGlued`. `completionDesc` is descent along the
  chart cover, not a colimit statement, and `completionGlued_hom_ext` is uniqueness among
  morphisms agreeing chart by chart.
* Nothing identifies `completionGlued` of a two-element datum with
  `AlgebraicGeometry.completionTwoPatch`. As with `ChartedSchemeDatum.ofTwoPatch` and
  `specTwoPatch`, the two glue data agree field for field but their `U` fields are not
  definitionally equal at a variable index; joining them is an isomorphism of glue data and is
  needed by nothing.
* Nothing relates this datum to `AlgebraicGeometry.AffineChartedFibreDatumX` and its
  `AlgebraicGeometry.AffineChartedFibreDatumX.xGlued`.
  That comparison is obstructed by a field, and the obstruction is recorded in
  `FormalSchemes.ChartedCompletionToScheme`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- An ideal identification along a ring isomorphism runs backwards along the inverse. -/
private theorem ccMapSymmEq {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    {K : Ideal R} {L : Ideal S} (h : K.map e.toRingHom = L) :
    L.map e.symm.toRingHom = K := by
  rw [← h, Ideal.map_map,
    show e.symm.toRingHom.comp e.toRingHom = RingHom.id R from RingHom.ext e.symm_apply_apply,
    Ideal.map_id]

/-! ### The datum -/

set_option linter.unusedVariables false in
/-- **A family of affine charts glued along basic opens, with an ideal in each chart, presented by
localization data.** -/
structure ChartedCompletionDatum where
  /-- The index type of the charts. -/
  J : Type u
  /-- The coordinate ring of the `i`-th affine chart. -/
  C : J → Type u
  [commRing : ∀ i, CommRing (C i)]
  /-- The ideal of the `i`-th chart along which it is to be completed. -/
  K : ∀ i, Ideal (C i)
  /-- Every ideal is finitely generated, which `formalCompletion` needs to name the chart. -/
  hK : ∀ i, (K i).FG
  /-- The away element cutting out the overlap of the `i`-th chart with the `j`-th. -/
  g : ∀ (i j : J), C i
  /-- The identification of the two presentations of the double overlap, at the localization. -/
  θ : ∀ (i j : J), i ≠ j →
    (Localization.Away (g i j) ≃+* Localization.Away (g j i))
  /-- The transitions are mutually inverse. -/
  θ_symm : ∀ (i j : J) (h : i ≠ j), θ j i h.symm = (θ i j h).symm
  /-- The transition carries the `i`-th ideal onto the `j`-th on the overlap. -/
  hθ : ∀ (i j : J) (h : i ≠ j),
    ((K i).map (algebraMap (C i) (Localization.Away (g i j)))).map (θ i j h).toRingHom =
      (K j).map (algebraMap (C j) (Localization.Away (g j i)))
  /-- The identification of the two presentations of the triple overlap. -/
  σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
    (Localization.Away (g i j * g i k) ≃+* Localization.Away (g j k * g j i))
  /-- The triple transition restricts to the double one. -/
  hσθ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    (σ i j k hij hik hjk).symm.toRingHom.comp
        (IsLocalization.Away.awayToAwayLeft (g j i) (g j k)) =
      (IsLocalization.Away.awayToAwayRight (g i j) (g i k)).comp (θ i j hij).symm.toRingHom
  /-- The triple cocycle, at the localizations. -/
  hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
      RingEquiv.refl (Localization.Away (g i j * g i k))

attribute [instance] ChartedCompletionDatum.commRing

namespace ChartedCompletionDatum

variable (D : ChartedCompletionDatum.{u})

/-- **The ambient scheme's datum**, by #462's smart constructor at the very same localization data.
-/
def toChartedSchemeDatum : ChartedSchemeDatum.{u} :=
  ChartedSchemeDatum.ofAlgebraData D.C D.g D.K D.θ D.θ_symm D.hθ D.σ D.hσθ D.hσc

/-- The index type is unchanged by passing to the ambient datum. -/
theorem toChartedSchemeDatum_J : D.toChartedSchemeDatum.J = D.J := rfl

/-- **The glued ambient scheme.** -/
def specGlued : LocallyRingedSpace.{u} := D.toChartedSchemeDatum.specGlued

/-- The `i`-th affine chart of the glued ambient scheme. -/
def specι (i : D.J) :
    Spec.locallyRingedSpaceObj (CommRingCat.of (D.C i)) ⟶ D.specGlued :=
  D.toChartedSchemeDatum.specι i

/-! ### The ideal compatibility of the triple transition, derived -/

/-- **The triple transition carries the `i`-th ideal onto the `j`-th**, and it is *derived*: it is
`hθ` pushed along the two further-localization maps, using `hσθ` to move `σ` past them. -/
theorem hσK (i j k : D.J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((D.K i).map (algebraMap (D.C i) (Localization.Away (D.g i j * D.g i k)))).map
        (D.σ i j k hij hik hjk).toRingHom =
      (D.K j).map (algebraMap (D.C j) (Localization.Away (D.g j k * D.g j i))) := by
  have H : ((D.K j).map (algebraMap (D.C j) (Localization.Away (D.g j k * D.g j i)))).map
      (D.σ i j k hij hik hjk).symm.toRingHom =
        (D.K i).map (algebraMap (D.C i) (Localization.Away (D.g i j * D.g i k))) := by
    rw [← formalCompletion.awayToAwayLeft_comp_algebraMap (D.g j k) (D.g j i), ← Ideal.map_map,
      Ideal.map_map, D.hσθ i j k hij hik hjk, ← Ideal.map_map,
      ccMapSymmEq (D.θ i j hij) (D.hθ i j hij), Ideal.map_map,
      formalCompletion.awayToAwayRight_comp_algebraMap (D.g i j) (D.g i k)]
  have h2 := ccMapSymmEq (D.σ i j k hij hik hjk).symm H
  rwa [RingEquiv.symm_symm] at h2


/-- **The double transition read backwards**: `θ i j` carries the `j`-th ideal back to the `i`-th
along its inverse. -/
theorem hθ_symm (i j : D.J) (h : i ≠ j) :
    ((D.K j).map (algebraMap (D.C j) (Localization.Away (D.g j i)))).map
        (D.θ i j h).symm.toRingHom =
      (D.K i).map (algebraMap (D.C i) (Localization.Away (D.g i j))) :=
  ccMapSymmEq (D.θ i j h) (D.hθ i j h)

/-! ### The completion charts, their overlaps and their transitions -/

/-- The `i`-th chart's completion `Spf (C i)^`, as a locally ringed space. -/
abbrev chart (i : D.J) : LocallyRingedSpace.{u} :=
  (formalCompletion (D.C i) (D.K i) (D.hK i)).toLocallyRingedSpace

/-- The overlap of the `i`-th chart with the `j`-th, completed: `Spf ((C i)_{g_ij})^`. -/
abbrev overlap (i j : D.J) : LocallyRingedSpace.{u} :=
  (formalCompletion (Localization.Away (D.g i j))
    ((D.K i).map (algebraMap (D.C i) (Localization.Away (D.g i j))))
    ((D.hK i).map _)).toLocallyRingedSpace

/-- The inclusion of a completed overlap into its chart, a basic-open completion immersion. -/
abbrev overlapImmersion (i j : D.J) : D.overlap i j ⟶ D.chart i :=
  (formalCompletion.basicOpenImmersion (D.K i) (D.hK i) (D.g i j)).toLRSHom

/-- **The transition of a double overlap**, `Spf ((C i)_{g_ij})^ ≅ Spf ((C j)_{g_ji})^`: `Spf` of
the localization transition `θ i j`, whose adicity is the datum's `hθ`. -/
def overlapIso (i j : D.J) (h : i ≠ j) : D.overlap i j ≅ D.overlap j i :=
  completionGlueLRSIso (D.K i) (D.hK i) (D.g i j) (D.K j) (D.hK j) (D.g j i)
    (D.θ i j h) (D.hθ i j h)

/-- **The transition of a triple overlap**, `Spf ((C i)_{g_ij·g_ik})^ ≅ Spf ((C j)_{g_jk·g_ji})^`:
`Spf` of `σ i j k`, whose adicity is the derived `hσK`. -/
private def ccGσ (i j k : D.J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (formalCompletion (Localization.Away (D.g i j * D.g i k))
        ((D.K i).map (algebraMap (D.C i) (Localization.Away (D.g i j * D.g i k))))
        ((D.hK i).map _)).toLocallyRingedSpace ≅
      (formalCompletion (Localization.Away (D.g j k * D.g j i))
        ((D.K j).map (algebraMap (D.C j) (Localization.Away (D.g j k * D.g j i))))
        ((D.hK j).map _)).toLocallyRingedSpace :=
  completionGlueLRSIso (D.K i) (D.hK i) (D.g i j * D.g i k) (D.K j) (D.hK j)
    (D.g j k * D.g j i) (D.σ i j k hij hik hjk) (D.hσK i j k hij hik hjk)

/-- **The geometric triple-overlap transition**, transported through the two overlap
identifications `formalCompletion.basicOpenOverlapIso` from `Spf` of `σ i j k`. This is the
completion-side mirror of
`AlgebraicGeometry.ChartedSchemeDatum.specAlgDataT'`. -/
def tripleTransition (i j k : D.J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    pullback (D.overlapImmersion i j) (D.overlapImmersion i k) ⟶
      pullback (D.overlapImmersion j k) (D.overlapImmersion j i) :=
  (formalCompletion.basicOpenOverlapIso (D.K i) (D.hK i) (D.g i j) (D.g i k)).inv ≫
    (D.ccGσ i j k hij hik hjk).hom ≫
      (formalCompletion.basicOpenOverlapIso (D.K j) (D.hK j) (D.g j k) (D.g j i)).hom


/-! ### The three laws of the glue datum -/

/-- **The key ring-level identity behind `t_fac`**: the triple transition, followed by the
further-localization down to the double overlap on the `j` side, is the further-localization on the
`i` side followed by the double transition. Both sides are `formalCompletion.map` of a composite of
two ring maps, and the datum's `hσθ` says those composites agree. -/
private theorem ccKey (i j k : D.J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (completionGlueIso (D.K i) (D.hK i) (D.g i j * D.g i k) (D.K j) (D.hK j)
          (D.g j k * D.g j i) (D.σ i j k hij hik hjk) (D.hσK i j k hij hik hjk)).hom ≫
        formalCompletion.awayFurtherRight (D.K j) (D.hK j) (D.g j k) (D.g j i) =
      formalCompletion.awayFurtherLeft (D.K i) (D.hK i) (D.g i j) (D.g i k) ≫
        (completionGlueIso (D.K i) (D.hK i) (D.g i j) (D.K j) (D.hK j) (D.g j i)
          (D.θ i j hij) (D.hθ i j hij)).hom := by
  change formalCompletion.map _ _ _ _ ≫ formalCompletion.map _ _ _ _ =
    formalCompletion.map _ _ _ _ ≫ formalCompletion.map _ _ _ _
  rw [← formalCompletion.map_comp, ← formalCompletion.map_comp]
  exact formalCompletion.map_congr _ _ _ _ (D.hσθ i j k hij hik hjk)

/-- **`t_fac` for the derived triple transition.** The two overlap identifications are stripped by
the leg lemmas of `FormalSchemes.CompletionAwayOverlapLegs`, leaving a ring-level identity. -/
theorem tripleTransition_fac (i j k : D.J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    D.tripleTransition i j k hij hik hjk ≫
        pullback.snd (D.overlapImmersion j k) (D.overlapImmersion j i) =
      pullback.fst (D.overlapImmersion i j) (D.overlapImmersion i k) ≫
        (D.overlapIso i j hij).hom := by
  rw [tripleTransition,
    ← formalCompletion.basicOpenOverlapIso_inv_comp_left (D.K i) (D.hK i) (D.g i j) (D.g i k),
    Category.assoc, Category.assoc, Category.assoc,
    formalCompletion.basicOpenOverlapIso_hom_snd, Iso.cancel_iso_inv_left]
  exact congrArg FormalScheme.Hom.toLRSHom (D.ccKey i j k hij hik hjk)

/-- **Two overlap transitions in opposite directions compose to the identity**, for any presentation
of the second one that is the inverse ring isomorphism of the first. -/
private theorem ccGlueHomComp {A B : Type u} [CommRing A] [CommRing B]
    (I : Ideal A) (hI : I.FG) (a : A) (J : Ideal B) (hJ : J.FG) (b : B)
    (θ : Localization.Away a ≃+* Localization.Away b)
    (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
      J.map (algebraMap B (Localization.Away b)))
    (θ' : Localization.Away b ≃+* Localization.Away a)
    (hθ' : (J.map (algebraMap B (Localization.Away b))).map θ'.toRingHom =
      I.map (algebraMap A (Localization.Away a)))
    (h : θ' = θ.symm) :
    (completionGlueIso I hI a J hJ b θ hθ).hom ≫
        (completionGlueIso J hJ b I hI a θ' hθ').hom = 𝟙 _ := by
  subst h
  have key : (completionGlueIso J hJ b I hI a θ.symm hθ').hom =
      (completionGlueIso I hI a J hJ b θ hθ).inv :=
    formalCompletion.map_congr _ _ _ _ rfl
  rw [key]
  exact (completionGlueIso I hI a J hJ b θ hθ).hom_inv_id

/-- **Three overlap transitions around a triple compose to the identity** as soon as their ring
isomorphisms do. This is the completion-side counterpart of
`AlgebraicGeometry.specGlueIso_comp₃`. -/
private theorem ccGlueComp₃ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) (hI : I.FG) (a : A) (J : Ideal B) (hJ : J.FG) (b : B)
    (L : Ideal C) (hL : L.FG) (c : C)
    (e₁ : Localization.Away a ≃+* Localization.Away b)
    (e₂ : Localization.Away b ≃+* Localization.Away c)
    (e₃ : Localization.Away c ≃+* Localization.Away a)
    (h₁ : (I.map (algebraMap A (Localization.Away a))).map e₁.toRingHom =
      J.map (algebraMap B (Localization.Away b)))
    (h₂ : (J.map (algebraMap B (Localization.Away b))).map e₂.toRingHom =
      L.map (algebraMap C (Localization.Away c)))
    (h₃ : (L.map (algebraMap C (Localization.Away c))).map e₃.toRingHom =
      I.map (algebraMap A (Localization.Away a)))
    (h : e₁.trans (e₂.trans e₃) = RingEquiv.refl (Localization.Away a)) :
    (completionGlueIso I hI a J hJ b e₁ h₁).hom ≫ (completionGlueIso J hJ b L hL c e₂ h₂).hom ≫
        (completionGlueIso L hL c I hI a e₃ h₃).hom = 𝟙 _ := by
  have hcomp : e₁.symm.toRingHom.comp (e₂.symm.toRingHom.comp e₃.symm.toRingHom) =
      RingHom.id (Localization.Away a) := by
    refine RingHom.ext fun x => ?_
    have h2 : (e₁.trans (e₂.trans e₃)).symm x = x := by rw [h]; rfl
    simpa using h2
  change formalCompletion.map _ _ _ _ ≫ formalCompletion.map _ _ _ _ ≫
    formalCompletion.map _ _ _ _ = _
  rw [← formalCompletion.map_comp, ← formalCompletion.map_comp]
  exact (formalCompletion.map_congr _ _ _ _ hcomp).trans (formalCompletion.map_id _ _)

/-- The threefold composition law above, on underlying locally ringed spaces. -/
private theorem ccGlueLRSComp₃ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) (hI : I.FG) (a : A) (J : Ideal B) (hJ : J.FG) (b : B)
    (L : Ideal C) (hL : L.FG) (c : C)
    (e₁ : Localization.Away a ≃+* Localization.Away b)
    (e₂ : Localization.Away b ≃+* Localization.Away c)
    (e₃ : Localization.Away c ≃+* Localization.Away a)
    (h₁ : (I.map (algebraMap A (Localization.Away a))).map e₁.toRingHom =
      J.map (algebraMap B (Localization.Away b)))
    (h₂ : (J.map (algebraMap B (Localization.Away b))).map e₂.toRingHom =
      L.map (algebraMap C (Localization.Away c)))
    (h₃ : (L.map (algebraMap C (Localization.Away c))).map e₃.toRingHom =
      I.map (algebraMap A (Localization.Away a)))
    (h : e₁.trans (e₂.trans e₃) = RingEquiv.refl (Localization.Away a)) :
    (completionGlueLRSIso I hI a J hJ b e₁ h₁).hom ≫
        (completionGlueLRSIso J hJ b L hL c e₂ h₂).hom ≫
          (completionGlueLRSIso L hL c I hI a e₃ h₃).hom = 𝟙 _ :=
  congrArg FormalScheme.Hom.toLRSHom
    (ccGlueComp₃ I hI a J hJ b L hL c e₁ e₂ e₃ h₁ h₂ h₃ h)

/-- The two-fold composition law above, on underlying locally ringed spaces. -/
private theorem ccGlueLRSHomComp {A B : Type u} [CommRing A] [CommRing B]
    (I : Ideal A) (hI : I.FG) (a : A) (J : Ideal B) (hJ : J.FG) (b : B)
    (θ : Localization.Away a ≃+* Localization.Away b)
    (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
      J.map (algebraMap B (Localization.Away b)))
    (θ' : Localization.Away b ≃+* Localization.Away a)
    (hθ' : (J.map (algebraMap B (Localization.Away b))).map θ'.toRingHom =
      I.map (algebraMap A (Localization.Away a)))
    (h : θ' = θ.symm) :
    (completionGlueLRSIso I hI a J hJ b θ hθ).hom ≫
        (completionGlueLRSIso J hJ b I hI a θ' hθ').hom = 𝟙 _ :=
  congrArg FormalScheme.Hom.toLRSHom (ccGlueHomComp I hI a J hJ b θ hθ θ' hθ' h)

/-- **`cocycle` for the derived triple transition.** The adjacent overlap identifications cancel,
leaving the three transitions, which compose to the identity because their ring isomorphisms do —
that is the datum's `hσc`. -/
theorem tripleTransition_cocycle (i j k : D.J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    D.tripleTransition i j k hij hik hjk ≫ D.tripleTransition j k i hjk hij.symm hik.symm ≫
        D.tripleTransition k i j hik.symm hjk.symm hij = 𝟙 _ := by
  have hmid := ccGlueLRSComp₃
    (D.K i) (D.hK i) (D.g i j * D.g i k) (D.K j) (D.hK j) (D.g j k * D.g j i)
    (D.K k) (D.hK k) (D.g k i * D.g k j)
    (D.σ i j k hij hik hjk) (D.σ j k i hjk hij.symm hik.symm)
    (D.σ k i j hik.symm hjk.symm hij)
    (D.hσK i j k hij hik hjk) (D.hσK j k i hjk hij.symm hik.symm)
    (D.hσK k i j hik.symm hjk.symm hij) (D.hσc i j k hij hik hjk)
  simp only [tripleTransition, ccGσ, Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, reassoc_of% hmid, Iso.inv_hom_id]


/-! ### The glue datum and the glued completion -/

/-- **The glue datum of the completion**, as a `CategoryTheory.GlueData'` on `D.J`: the `i`-th
patch is `Spf (C i)^`, the overlap is `Spf ((C i)_{g_ij})^`, the inclusion is the basic-open
completion immersion and the transition is `overlapIso`. This is
`AlgebraicGeometry.completionTwoPatchGlueData'` at an arbitrary index type, with its three vacuous
fields replaced by the derived `tripleTransition`. -/
def completionGlueData' : CategoryTheory.GlueData' LocallyRingedSpace.{u} where
  J := D.J
  U := D.chart
  V := fun i j _ => D.overlap i j
  f := fun i j _ => D.overlapImmersion i j
  f_mono := fun _ _ _ => inferInstance
  f_hasPullback := fun _ _ _ _ _ => inferInstance
  t := fun i j h => (D.overlapIso i j h).hom
  t' := D.tripleTransition
  t_fac := D.tripleTransition_fac
  t_inv := fun i j h =>
    ccGlueLRSHomComp (D.K i) (D.hK i) (D.g i j) (D.K j) (D.hK j) (D.g j i)
      (D.θ i j h) (D.hθ i j h) (D.θ j i h.symm) (D.hθ j i h.symm) (D.θ_symm i j h)
  cocycle := D.tripleTransition_cocycle

/-- **The glue datum as a `LocallyRingedSpace.GlueData`**, via `GlueData.ofGlueData'` and the
open-immersion field `f_open`. -/
def completionLRSGlueData : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' D.completionGlueData' with
    f_open := by
      intro i j
      simp only [completionGlueData', CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · exact inferInstanceAs
          (LocallyRingedSpace.IsOpenImmersion (eqToHom _ ≫ D.overlapImmersion i j)) }

/-- **The glue datum as a `FormalScheme.GlueData`**: every patch is a formal completion, which is
by construction an affine formal scheme. -/
def completionFormalGlueData : FormalScheme.GlueData.{u} where
  toLocallyRingedSpaceGlueData := D.completionLRSGlueData
  isFormalScheme := fun i => ⟨formalCompletion (D.C i) (D.K i) (D.hK i), ⟨Iso.refl _⟩⟩

/-- **The glued completion** `X_{/Y}`: the formal scheme obtained by gluing the completions
`Spf (C i)^` of the charts along the identifications of their overlaps. -/
def completionGlued : FormalScheme.{u} := D.completionFormalGlueData.gluedFormalScheme

/-- The `i`-th chart's completion, as an open formal subscheme of the glued completion. -/
def completionι (i : D.J) :
    (formalCompletion (D.C i) (D.K i) (D.hK i)).toLocallyRingedSpace ⟶
      D.completionGlued.toLocallyRingedSpace :=
  D.completionFormalGlueData.ι i

instance completionι_isOpenImmersion (i : D.J) :
    LocallyRingedSpace.IsOpenImmersion (D.completionι i) :=
  FormalScheme.GlueData.ι_isOpenImmersion _ _

/-- **The chart completions cover the glued completion.** -/
theorem completionGlued_jointly_surjective (x : D.completionGlued.toLocallyRingedSpace) :
    ∃ (i : D.J) (y : (formalCompletion (D.C i) (D.K i) (D.hK i)).toLocallyRingedSpace),
      (D.completionι i).base y = x :=
  D.completionFormalGlueData.ι_jointly_surjective x

/-! ### The glue condition, and morphisms out of the glued completion -/

/-- The constructed glue map, off the diagonal, in the completion vocabulary. -/
theorem completionFormalGlueData_f (i j : D.J) (h : i ≠ j) :
    D.completionFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.f i j =
      eqToHom (dif_neg h) ≫ D.overlapImmersion i j :=
  dif_neg h

/-- The constructed transition, off the diagonal, in the completion vocabulary. -/
theorem completionFormalGlueData_t (i j : D.J) (h : i ≠ j) :
    D.completionFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.t i j =
      eqToHom (dif_neg h) ≫ (D.overlapIso i j h).hom ≫ eqToHom (dif_neg h.symm).symm :=
  dif_neg h

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- The same transparency requirement as in `FormalSchemes.CompletionGlueTwoPatchCondition`: the
-- glue datum is a `def`, so its index type does not reduce to `D.J` at `instances` transparency
-- and the rewrites below are rejected as ill-typed without this.
/-- **The chart completions agree over their overlaps inside the glued completion.** This is
`CategoryTheory.GlueData.glue_condition` with the `GlueData.ofGlueData'` bookkeeping cancelled off
both sides; it is the hypothesis `FormalScheme.GlueData.glueMorphisms` consumes. -/
theorem completion_glue_condition (i j : D.J) (h : i ≠ j) :
    (D.overlapIso i j h).hom ≫ D.overlapImmersion j i ≫ D.completionι j =
      D.overlapImmersion i j ≫ D.completionι i := by
  have key := D.completionFormalGlueData.toLocallyRingedSpaceGlueData.toGlueData.glue_condition i j
  rw [D.completionFormalGlueData_t i j h, D.completionFormalGlueData_f j i h.symm,
    D.completionFormalGlueData_f i j h] at key
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  exact (cancel_epi (eqToHom (dif_neg h))).mp key

section Desc

variable {Y : LocallyRingedSpace.{u}}

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- Same transparency requirement as in `completion_glue_condition`, for the same reason.
/-- **Descent of a morphism out of the glued completion**: a family of morphisms out of the chart
completions which agree over every overlap glues to a single morphism out of `completionGlued`.
On the diagonal the obligation of `FormalScheme.GlueData.glueMorphisms` collapses because
`CategoryTheory.GlueData.t_id` makes the transition the identity. -/
def completionDesc
    (k : ∀ i : D.J, (formalCompletion (D.C i) (D.K i) (D.hK i)).toLocallyRingedSpace ⟶ Y)
    (hk : ∀ (i j : D.J) (h : i ≠ j),
      D.overlapImmersion i j ≫ k i = (D.overlapIso i j h).hom ≫ D.overlapImmersion j i ≫ k j) :
    D.completionGlued.toLocallyRingedSpace ⟶ Y :=
  D.completionFormalGlueData.glueMorphisms k (by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · rw [D.completionFormalGlueData_f i j hij, D.completionFormalGlueData_t i j hij,
        D.completionFormalGlueData_f j i (Ne.symm hij)]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact congrArg _ (hk i j hij))

/-- **The descended morphism restricts to the given morphism on each chart.** -/
theorem completionι_comp_desc
    (k : ∀ i : D.J, (formalCompletion (D.C i) (D.K i) (D.hK i)).toLocallyRingedSpace ⟶ Y)
    (hk : ∀ (i j : D.J) (h : i ≠ j),
      D.overlapImmersion i j ≫ k i =
        (D.overlapIso i j h).hom ≫ D.overlapImmersion j i ≫ k j) (i : D.J) :
    D.completionι i ≫ D.completionDesc k hk = k i :=
  D.completionFormalGlueData.ι_glueMorphisms _ _ i

/-- **Uniqueness**: a morphism out of the glued completion is determined by its restrictions to the
chart completions. -/
theorem completionGlued_hom_ext {f₁ f₂ : D.completionGlued.toLocallyRingedSpace ⟶ Y}
    (h : ∀ i : D.J, D.completionι i ≫ f₁ = D.completionι i ≫ f₂) : f₁ = f₂ :=
  D.completionFormalGlueData.hom_ext h

end Desc

end ChartedCompletionDatum

/-! ### The two-patch line, read as a completion datum -/

section TwoPatch

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (hI : I.FG) (a : A)
  (J : Ideal B) (hJ : J.FG) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

/-- **The two-patch input, as a `ChartedCompletionDatum`.** The mirror of
`AlgebraicGeometry.ChartedSchemeDatum.ofTwoPatch`, field for field, with the four extra fields a
completion datum carries: `hK` from the two finite-generation hypotheses, and `σ`, `hσθ`, `hσc`
vacuously, since no triple of `ULift Bool`-indices is pairwise distinct
(`AlgebraicGeometry.uliftBool_not_pairwise_distinct`, `FormalSchemes.Gluing`).

The ideals are `I : Ideal A` and `J : Ideal B`, **in different rings and unrelated to each other**,
which is what this datum shape exists for and what
`AlgebraicGeometry.AffineChartedFibreDatumX` cannot express. The backward `hθ` is
`FormalSpectrum.isAdicHom_ringEquiv_symm`, as on the `Spec` side. -/
def ChartedCompletionDatum.ofTwoPatch : ChartedCompletionDatum.{u} where
  J := ULift.{u} Bool
  C := fun i => cond i.down B A
  commRing := fun i => match i with
    | ⟨false⟩ => inferInstanceAs (CommRing A)
    | ⟨true⟩ => inferInstanceAs (CommRing B)
  K := fun i => match i with
    | ⟨false⟩ => I
    | ⟨true⟩ => J
  hK := fun i => match i with
    | ⟨false⟩ => hI
    | ⟨true⟩ => hJ
  g := fun i _ => match i with
    | ⟨false⟩ => a
    | ⟨true⟩ => b
  θ := fun i j h => match i, j, h with
    | ⟨false⟩, ⟨true⟩, _ => θ
    | ⟨true⟩, ⟨false⟩, _ => θ.symm
    | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
    | ⟨true⟩, ⟨true⟩, h => (h rfl).elim
  θ_symm := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ h
    · exact absurd rfl h
    · rfl
    · exact (RingEquiv.symm_symm θ).symm
    · exact absurd rfl h
  hθ := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ h
    · exact absurd rfl h
    · exact hθ
    · exact FormalSpectrum.isAdicHom_ringEquiv_symm θ hθ
    · exact absurd rfl h
  σ := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim
  hσθ := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim
  hσc := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim

/-- The `A`-side ideal of the two-patch completion datum is `I`, in `A`. -/
theorem ChartedCompletionDatum.ofTwoPatch_K_false :
    (ChartedCompletionDatum.ofTwoPatch I hI a J hJ b θ hθ).K ⟨false⟩ = I :=
  rfl

/-- The `B`-side ideal of the two-patch completion datum is `J`, in `B`: the two ideals live in
different rings and are not images of one another. -/
theorem ChartedCompletionDatum.ofTwoPatch_K_true :
    (ChartedCompletionDatum.ofTwoPatch I hI a J hJ b θ hθ).K ⟨true⟩ = J :=
  rfl

end TwoPatch

end AlgebraicGeometry

end
