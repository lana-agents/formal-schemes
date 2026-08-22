import FormalSchemes.TateFibreOverlapCompare
import FormalSchemes.TateSelfProductDSigmaInv
import FormalSchemes.TateTensorOverlapSummandAffineBoth
import FormalSchemes.TateCurveExposeXDatum
import FormalSchemes.TateXGluedIso

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000

/-!
# The transition law of the `Ψ` comparison of the two Tate self-fibre-product presentations

`FormalSchemes/TateFibreOverlapCompare.lean` (705c) supplies the **`V` and `f` layers** of the `Ψ`
comparison: for each pair of distinct product-index charts, `tateOverlapCompareIso` identifies the
generic (merged) overlap object `bothAlgDataV` with the hand-built Tate glue datum's (coproduct)
overlap object `tateSelfProductGlueV`, compatibly with the two overlap charts. This file supplies
the missing **`t` layer**: the same isomorphism intertwines the two *transitions*,

```lean
(tateOverlapCompareIso …).hom ≫ tateSelfProductGlueTInv … =
  bothAlgDataT … ≫ (tateOverlapCompareIso …).hom
```

which is the last piece of content in issue 740 (brick 4 of 601). With it, `Ψ` can be built by
`FormalScheme.GlueData.glueMorphisms`.

## The two transitions

The generic side, `bothAlgDataT`, dispatches on the difference type of the pair and is `Spf` of a
pair of `R`-algebra maps: `id ⊗̂ τ`, `τ ⊗̂ id` or `τ ⊗̂ τ`, where `τ` is the datum's chart
transition — for the Tate `X`-expose datum, `annulusFibreOverlapTransitionAlg` at every ordered
pair (`tateCurveExposeXDatum_τ`, `rfl`).

The Tate side, `tateSelfProductGlueTInv`, is an explicit sixteen-way match producing the
summand-permuting involutions `tateSelfProduct{Right,First,Both}TransitionInv` of the coproduct
overlap objects: two summands swapped by `rightSummandInv` / `firstSummandInv` in the one-sided
shapes, four summands permuted by `bothSummandDiagInv` and `bothSummandAntiInv` in the both-factor
shape.

So the whole of the geometric content is that the merged-versus-coproduct identifications of 738/739
carry `Spf` of the tensored transition to those permutations, and that is proved here summandwise
from 751/761's presentation of the summand inclusions as `mapSpf` of the splitting's projections.

## The ring-level crux, and the conjugation that reaches it

Everything reduces to one identity in the second (or first) tensor factor alone, because the other
factor carries the identity on both sides. That identity is 704's

```lean
annulusOverlapProjX_comp_transitionAlg :
  projX ∘ T = ι⁻¹ ∘ projY
```

conjugated by the ideal-convention bridges between the two spellings of the annulus ideal of
definition (`annulusIdealOfDefinition R I q` versus `I.map (algebraMap R A)`, equal by
`annulus_map_eq` but **not** definitionally so). Writing the conjugations out, every interior bridge
cancels in pairs.

**That cancellation cannot be performed on the Tate terms.** Unfolding
`annulusFibreOverlapTransitionAlg` into its three bridge factors by `rfl` exhausts `maxRecDepth` and
then times out in the kernel, and the pointwise route (`AlgHom.ext`, then `AlgEquiv.trans_apply`)
times out at `whnf`. What works is to state the conjugation **over a variable equality of ideals**
and `subst` it: `FormalSpectrum.awayCompletionCongrₐ_conj_projComp` below is proved by
`subst h; exact hc`, in which every bridge becomes `awayCompletionCongrₐ R rfl _` on a *small* term
and the remaining `AlgHom.id`/`AlgEquiv.refl` noise is defeq at default transparency.

This is #277's rule — *generalise the constant to a variable before the equation, never after* —
applied to a proof rather than to a family. Getting the Tate terms into that shape needs
`awayCompletionCongrₐ_eq_congrIdealₐ`, the small `subst` lemma 771's route analysis identified as
the only genuinely missing ingredient, which identifies 751's transport with the
`AdicCompletion.congrIdealₐ`-spelled bridges of 683 and of `TwoPatchFibreProductObject`.

## Main results

* `FormalSpectrum.awayCompletionCongrₐ_eq_congrIdealₐ`,
  `FormalSpectrum.awayCompletionCongrₐ_conj_projComp`: the transport identification and the generic
  conjugation.
* `AlgebraicGeometry.annulusTensorProjXₐ_comp_transitionAlg`,
  `annulusTensorProjYₐ_comp_transitionAlg`: 704's crux in the tensored (`I·A`) spelling, and its
  mirror.
* `AlgebraicGeometry.tensorOverlapChartIsoSecond_transition_comm`,
  `…First…`, `…Both…`: the merged-versus-coproduct identification intertwines `Spf` of the tensored
  transition with the summand permutation, in each of the three difference-type shapes.
* `AlgebraicGeometry.tateOverlapCompareIso_hom_t`: **the deliverable** — the transition law of the
  `Ψ` comparison, for every pair of distinct product indices, together with its three
  difference-type components `…_t_snd` / `…_t_fst` / `…_t_both`.

## Implementation notes

Four build-cost rules are in force here; the first three were measured by 751/761/#277 and the
fourth is new.

1. **Generalise a constant to a variable before the equation, never after** (#277). This is what
   `bothAlgDataT_{snd,fst,both}_const` are for, and it is why the conjugation lemma is stated for a
   variable `h : K₁ = K₂`.
2. **Never nest `coprod.hom_ext` inline at four-fold-coproduct size** (761). The both-factor
   transition law is assembled from four single-summand lemmas through two half-lemmas, and the
   outer step avoids `coprod.hom_ext` altogether by rewriting with 761's packaged
   `coprod_desc_tensorOverlapSummandBoth` and `coprod.desc_comp`.
3. **Ship bare** — no `@[reassoc]`, no `@[simp]` (751). `reassoc_of%` at a *spelled-out* application
   is fine and is used throughout.
4. **New: at this size, `rw` is quadratic in the goal.** `rw [coprod_inr_inr_comp_…_inv]` is instant
   when the goal is a single summand identity and times out at 3 200 000 heartbeats when the same
   rewrite is one entry of a four-way `rw` list, because `kabstract`'s keyed matching runs `isDefEq`
   against every `≫`-subterm of the goal and the competing subterms are four-fold coproducts of
   completed tensor products. The remedy is the same as (2): **one summand per declaration**, then
   `rw` with the pinned lemmas. `rw [Category.assoc, Category.assoc, lemma]` inside such a small
   goal is cheap; `rw [lemma₁, lemma₂, lemma₃, lemma₄]` in the assembled goal is not.

Two smaller ones, both hit here:

* `rw [AlgHom.id_comp]` / `[AlgHom.comp_id]` on completed-tensor-product arguments times out at
  `isDefEq`. Pin the equation as a local `have … := rfl` at the small `A →ₐ[R] A` level and rewrite
  with that (`hid` below).
* `refine (Iso.eq_inv_comp _).1 (coprod.hom_ext ?_ ?_)`, the one-liner
  `tateOverlapChartIso_transition_comm` (`TateXGluedIso.lean:285`) uses, leaves the second summand
  goal timing out in *synthesize pending MVars*. Split it into two `refine`s.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace FormalSpectrum

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

/-! ### Transport of an away completion, and conjugation by it -/

/-- **751's transport is the `AdicCompletion.congrIdealₐ` bridge.** `awayCompletionCongrₐ` and the
`annulusFibreChartBridge…` family (`TwoPatchFibreProductObject`, `TateCurveExposeXDatum`) are two
spellings of the same map — both are the identity after `subst` — but the tree had no lemma saying
so, and every ideal-convention cancellation in a transition law needs it. -/
theorem awayCompletionCongrₐ_eq_congrIdealₐ {K₁ K₂ : Ideal A} (h : K₁ = K₂) (f : A) :
    awayCompletionCongrₐ R h f =
      AdicCompletion.congrIdealₐ R
        (congrArg (Ideal.map (algebraMap A (Localization.Away f))) h) := by
  subst h; rfl

/-- **Conjugation by the transport preserves a "projection versus transition" identity.**

Given, over the ideal `K₂`, two projections `PX`, `PY` out of the away completion at `z`, an
automorphism `T₀` of it and an isomorphism `ι₀ : (·)ₓ ≃ (·)_y` satisfying `PX ∘ T₀ = ι₀⁻¹ ∘ PY`, the
same identity holds for the three maps conjugated by `awayCompletionCongrₐ R h` into the `K₁`
spelling.

The proof is `subst h; exact hc` and it is the load-bearing step of this file: doing the same
cancellation on the Tate instantiation instead — where `K₁ = I.map (algebraMap R A)` and
`K₂ = annulusIdealOfDefinition R I q` are concrete completed-localisation ideals — does not
elaborate at any heartbeat budget. Keeping the ideals variables keeps every term small, and
instantiating afterwards is substitution rather than conversion. -/
theorem awayCompletionCongrₐ_conj_projComp {K₁ K₂ : Ideal A} (h : K₁ = K₂) (x y z : A)
    (PX : awayCompletion K₂ z →ₐ[R] awayCompletion K₂ x)
    (PY : awayCompletion K₂ z →ₐ[R] awayCompletion K₂ y)
    (T₀ : awayCompletion K₂ z ≃ₐ[R] awayCompletion K₂ z)
    (ι₀ : awayCompletion K₂ x ≃ₐ[R] awayCompletion K₂ y)
    (hc : PX.comp T₀.toAlgHom = ι₀.symm.toAlgHom.comp PY) :
    ((awayCompletionCongrₐ R h.symm x).toAlgHom.comp
          (PX.comp (awayCompletionCongrₐ R h z).toAlgHom)).comp
        (((awayCompletionCongrₐ R h z).trans T₀).trans
          (awayCompletionCongrₐ R h z).symm).toAlgHom =
      (((awayCompletionCongrₐ R h x).trans
            (ι₀.trans (awayCompletionCongrₐ R h y).symm)).symm).toAlgHom.comp
        ((awayCompletionCongrₐ R h.symm y).toAlgHom.comp
          (PY.comp (awayCompletionCongrₐ R h z).toAlgHom)) := by
  subst h
  exact hc

end FormalSpectrum

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The ideal-convention bridges in the transport spelling -/

/-- The `x`-bridge of `TwoPatchFibreProductObject` is 751's transport. -/
theorem annulusFibreChartBridgeX_eq :
    annulusFibreChartBridgeX R I q =
      awayCompletionCongrₐ R (annulus_map_eq R I q) (overlapX R I q) :=
  (awayCompletionCongrₐ_eq_congrIdealₐ R (annulus_map_eq R I q) (overlapX R I q)).symm

/-- The `y`-bridge of `TwoPatchFibreProductObject` is 751's transport. -/
theorem annulusFibreChartBridgeY_eq :
    annulusFibreChartBridgeY R I q =
      awayCompletionCongrₐ R (annulus_map_eq R I q) (overlapY R I q) :=
  (awayCompletionCongrₐ_eq_congrIdealₐ R (annulus_map_eq R I q) (overlapY R I q)).symm

/-- The `x + y`-bridge of 683 is 751's transport. -/
theorem annulusFibreChartBridgeXY_eq :
    annulusFibreChartBridgeXY R I q =
      awayCompletionCongrₐ R (annulus_map_eq R I q) (overlapX R I q + overlapY R I q) :=
  (awayCompletionCongrₐ_eq_congrIdealₐ R (annulus_map_eq R I q)
    (overlapX R I q + overlapY R I q)).symm

/-! ### The ring-level crux, and its tensored spelling -/

/-- **704's crux in the `AlgHom` spelling.** `annulusOverlapProjX_comp_transitionAlg`
(`TateXGluedIso.lean:231`) is stated for `RingHom`s; `CompletedTensorProduct.mapSpf` consumes
`AlgHom`s, and both projections are already `R`-algebra maps, so the upgrade is pointwise. -/
theorem annulusOverlapProjXₐ_comp_transitionAlg (hq : q ∈ I) (hI : I.FG) :
    (annulusOverlapProjXₐ R I q hq).comp (tateOverlapTransitionAlg R I q hq hI).toAlgHom =
      (annulusChartTransitionInvAlg R I q hI).symm.toAlgHom.comp
        (annulusOverlapProjYₐ R I q hq) := by
  refine AlgHom.ext fun s => ?_
  exact DFunLike.congr_fun (annulusOverlapProjX_comp_transitionAlg R I q hq hI) s

/-- **The crux in the tensored (`I·A`) spelling**: the first projection of 644's splitting, after
the bridged overlap transition of 683, is the bridged 𝔾m-inversion applied to the second projection.

This is the single ring-theoretic input of every geometric statement below. The three players
(`annulusTensorProjXₐ`/`Yₐ` of 751, `annulusFibreOverlapTransitionAlg` of 683,
`annulusFibreChartTransitionInvAlg` of the inversion transition) are each the unbridged map
conjugated by ideal-convention transports, and the interior bridges cancel in pairs — which is
exactly what `awayCompletionCongrₐ_conj_projComp` says, once the three bridges are put into the
transport spelling. -/
theorem annulusTensorProjXₐ_comp_transitionAlg (hq : q ∈ I) (hI : I.FG) :
    (annulusTensorProjXₐ R I q hq).comp
        (annulusFibreOverlapTransitionAlg R I q hq hI).toAlgHom =
      (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom.comp
        (annulusTensorProjYₐ R I q hq) := by
  rw [annulusTensorProjXₐ, annulusTensorProjYₐ, annulusFibreOverlapTransitionAlg,
    annulusFibreChartTransitionInvAlg, annulusFibreChartBridgeX_eq,
    annulusFibreChartBridgeY_eq, annulusFibreChartBridgeXY_eq]
  exact awayCompletionCongrₐ_conj_projComp R (annulus_map_eq R I q) _ _ _ _ _ _ _
    (annulusOverlapProjXₐ_comp_transitionAlg R I q hq hI)

/-- **The mirror crux**: `projY ∘ T = ι ∘ projX`. Deduced from the `x`-statement and the fact that
the bridged transition is an involution (`annulusFibreOverlapTransitionAlg_symm`), which avoids
conjugating a second ring-level identity. -/
theorem annulusTensorProjYₐ_comp_transitionAlg (hq : q ∈ I) (hI : I.FG) :
    (annulusTensorProjYₐ R I q hq).comp
        (annulusFibreOverlapTransitionAlg R I q hq hI).toAlgHom =
      (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom.comp
        (annulusTensorProjXₐ R I q hq) := by
  have hTT : ((annulusFibreOverlapTransitionAlg R I q hq hI).toAlgHom).comp
      ((annulusFibreOverlapTransitionAlg R I q hq hI).toAlgHom) = AlgHom.id R _ := by
    have h := AlgEquiv.comp_symm (annulusFibreOverlapTransitionAlg R I q hq hI)
    rwa [annulusFibreOverlapTransitionAlg_symm] at h
  have h2 : annulusTensorProjXₐ R I q hq =
      (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom.comp
        ((annulusTensorProjYₐ R I q hq).comp
          (annulusFibreOverlapTransitionAlg R I q hq hI).toAlgHom) := by
    rw [← AlgHom.comp_assoc, ← annulusTensorProjXₐ_comp_transitionAlg, AlgHom.comp_assoc,
      hTT, AlgHom.comp_id]
  conv_rhs => rw [h2]
  rw [← AlgHom.comp_assoc, AlgEquiv.comp_symm, AlgHom.id_comp]

/-! ### The second-factor overlap: the transition permutes the two summands

Here `Spf` of the tensored transition is `mapSpfIso hI (refl A) τ`, the shape `bothAlgDataT` takes
when the two product indices share their first coordinate. -/

/-- **The `x`-summand of the tensored second-factor overlap is carried to the `y`-summand**, and the
identification is the base-changed 𝔾m-inversion `rightSummandInv`. Both sides collapse under
`← mapSpf_comp` to a single `mapSpf`, and the second components are the crux. -/
theorem tensorOverlapSummandXSecond_comp_transitionSpf (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandXSecond R I q hq hI ≫
        (CompletedTensorProduct.mapSpfIso hI
          (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q))
          (annulusFibreOverlapTransitionAlg R I q hq hI)).hom =
      (rightSummandInv R I q hI).hom ≫ tensorOverlapSummandYSecond R I q hq hI := by
  have hid : (AlgHom.id R (annulusAlgebra R I q)).comp
        (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom =
      (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom.comp
        (AlgHom.id R (annulusAlgebra R I q)) := rfl
  rw [tensorOverlapSummandXSecond, tensorOverlapSummandYSecond, rightSummandInv,
    CompletedTensorProduct.mapSpfIso_hom, CompletedTensorProduct.mapSpfIso_hom,
    ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
    annulusFibreOverlapTransitionAlg_symm, annulusTensorProjXₐ_comp_transitionAlg, hid]

/-- **The `y`-summand is carried to the `x`-summand**, through the inverse identification. -/
theorem tensorOverlapSummandYSecond_comp_transitionSpf (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandYSecond R I q hq hI ≫
        (CompletedTensorProduct.mapSpfIso hI
          (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q))
          (annulusFibreOverlapTransitionAlg R I q hq hI)).hom =
      (rightSummandInv R I q hI).inv ≫ tensorOverlapSummandXSecond R I q hq hI := by
  have hid : (AlgHom.id R (annulusAlgebra R I q)).comp
        (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom =
      (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom.comp
        (AlgHom.id R (annulusAlgebra R I q)) := rfl
  rw [tensorOverlapSummandXSecond, tensorOverlapSummandYSecond, rightSummandInv,
    CompletedTensorProduct.mapSpfIso_hom, CompletedTensorProduct.mapSpfIso_inv,
    ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
    annulusFibreOverlapTransitionAlg_symm, annulusTensorProjYₐ_comp_transitionAlg, hid]

/-- The `hom` leg of the second-factor inversion transition, as a `coprod.desc`. Needed because
`rw [coprod.inl_desc]` does not see through the structure projection. -/
theorem tateSelfProductRightTransitionInv_hom (hI : I.FG) :
    (tateSelfProductRightTransitionInv R I q hI).hom =
      coprod.desc ((rightSummandInv R I q hI).hom ≫ coprod.inr)
        ((rightSummandInv R I q hI).inv ≫ coprod.inl) := rfl

/-- **The second-factor `t` law, at the level of the overlap objects.** 738/739's identification of
the merged chart `Spf(A ⊗̂_R A{1/(x+y)}^)` with the coproduct `Spf(A ⊗̂ A{1/x}) ⨿ Spf(A ⊗̂ A{1/y})`
carries `Spf` of the tensored transition to the summand swap. The two summandwise obligations are
the laws above; the shape of the proof is `tateOverlapChartIso_transition_comm`'s, one tensor factor
up. -/
theorem tensorOverlapChartIsoSecond_transition_comm (hq : q ∈ I) (hI : I.FG) :
    (tensorOverlapChartIsoSecond R I q hq hI).hom ≫
        (tateSelfProductRightTransitionInv R I q hI).hom =
      (CompletedTensorProduct.mapSpfIso hI
          (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q))
          (annulusFibreOverlapTransitionAlg R I q hq hI)).hom ≫
        (tensorOverlapChartIsoSecond R I q hq hI).hom := by
  rw [tateSelfProductRightTransitionInv_hom]
  refine (Iso.eq_inv_comp _).1 ?_
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc, coprod_inl_comp_tensorOverlapChartIsoSecond_inv_assoc,
      reassoc_of% (tensorOverlapSummandXSecond_comp_transitionSpf R I q hq hI),
      tensorOverlapSummandYSecond_comp_tensorOverlapChartIsoSecond_hom]
  · rw [coprod.inr_desc, coprod_inr_comp_tensorOverlapChartIsoSecond_inv_assoc,
      reassoc_of% (tensorOverlapSummandYSecond_comp_transitionSpf R I q hq hI),
      tensorOverlapSummandXSecond_comp_tensorOverlapChartIsoSecond_hom]

/-! ### The first-factor overlap: the mirror

The same statements with the tensor factors exchanged; `bothAlgDataT` takes this shape when the two
product indices share their *second* coordinate. -/

/-- The first-factor mirror of `tensorOverlapSummandXSecond_comp_transitionSpf`. -/
theorem tensorOverlapSummandXFirst_comp_transitionSpf (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandXFirst R I q hq hI ≫
        (CompletedTensorProduct.mapSpfIso hI
          (annulusFibreOverlapTransitionAlg R I q hq hI)
          (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q))).hom =
      (firstSummandInv R I q hI).hom ≫ tensorOverlapSummandYFirst R I q hq hI := by
  have hid : (AlgHom.id R (annulusAlgebra R I q)).comp
        (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom =
      (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom.comp
        (AlgHom.id R (annulusAlgebra R I q)) := rfl
  rw [tensorOverlapSummandXFirst, tensorOverlapSummandYFirst, firstSummandInv,
    twoPatchFibreProductInvTransition,
    CompletedTensorProduct.mapSpfIso_hom, CompletedTensorProduct.mapSpfIso_hom,
    ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
    annulusFibreOverlapTransitionAlg_symm, annulusTensorProjXₐ_comp_transitionAlg, hid]

/-- The first-factor mirror of `tensorOverlapSummandYSecond_comp_transitionSpf`. -/
theorem tensorOverlapSummandYFirst_comp_transitionSpf (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandYFirst R I q hq hI ≫
        (CompletedTensorProduct.mapSpfIso hI
          (annulusFibreOverlapTransitionAlg R I q hq hI)
          (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q))).hom =
      (firstSummandInv R I q hI).inv ≫ tensorOverlapSummandXFirst R I q hq hI := by
  have hid : (AlgHom.id R (annulusAlgebra R I q)).comp
        (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom =
      (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom.comp
        (AlgHom.id R (annulusAlgebra R I q)) := rfl
  rw [tensorOverlapSummandXFirst, tensorOverlapSummandYFirst, firstSummandInv,
    twoPatchFibreProductInvTransition,
    CompletedTensorProduct.mapSpfIso_hom, CompletedTensorProduct.mapSpfIso_inv,
    ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
    annulusFibreOverlapTransitionAlg_symm, annulusTensorProjYₐ_comp_transitionAlg, hid]

/-- The `hom` leg of the first-factor inversion transition, as a `coprod.desc`. -/
theorem tateSelfProductFirstTransitionInv_hom (hI : I.FG) :
    (tateSelfProductFirstTransitionInv R I q hI).hom =
      coprod.desc ((firstSummandInv R I q hI).hom ≫ coprod.inr)
        ((firstSummandInv R I q hI).inv ≫ coprod.inl) := rfl

/-- **The first-factor `t` law, at the level of the overlap objects.** -/
theorem tensorOverlapChartIsoFirst_transition_comm (hq : q ∈ I) (hI : I.FG) :
    (tensorOverlapChartIsoFirst R I q hq hI).hom ≫
        (tateSelfProductFirstTransitionInv R I q hI).hom =
      (CompletedTensorProduct.mapSpfIso hI
          (annulusFibreOverlapTransitionAlg R I q hq hI)
          (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q))).hom ≫
        (tensorOverlapChartIsoFirst R I q hq hI).hom := by
  rw [tateSelfProductFirstTransitionInv_hom]
  refine (Iso.eq_inv_comp _).1 ?_
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc, coprod_inl_comp_tensorOverlapChartIsoFirst_inv_assoc,
      reassoc_of% (tensorOverlapSummandXFirst_comp_transitionSpf R I q hq hI),
      tensorOverlapSummandYFirst_comp_tensorOverlapChartIsoFirst_hom]
  · rw [coprod.inr_desc, coprod_inr_comp_tensorOverlapChartIsoFirst_inv_assoc,
      reassoc_of% (tensorOverlapSummandYFirst_comp_transitionSpf R I q hq hI),
      tensorOverlapSummandXFirst_comp_tensorOverlapChartIsoFirst_hom]

/-! ### The both-factors overlap: the transition permutes the four summands

`Spf` of the tensored transition is now `mapSpfIso hI τ τ`, and the permutation is
`(x, x) ↦ (y, y)`, `(x, y) ↦ (y, x)` and back. All four summand laws are direct: the `(x, x)` and
`(y, y)` ones use the crux twice, the two off-diagonal ones use the crux and its mirror once
each. -/

/-- The `(x, x)`-summand goes to the `(y, y)`-summand, through `bothSummandDiagInv`. -/
theorem tensorOverlapSummandXXBoth_comp_transitionSpf (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandXXBoth R I q hq hI ≫
        (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
          (annulusFibreOverlapTransitionAlg R I q hq hI)).hom =
      (bothSummandDiagInv R I q hI).hom ≫ tensorOverlapSummandYYBoth R I q hq hI := by
  rw [tensorOverlapSummandXXBoth, tensorOverlapSummandYYBoth, bothSummandDiagInv,
    CompletedTensorProduct.mapSpfIso_hom, CompletedTensorProduct.mapSpfIso_hom,
    ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
    annulusFibreOverlapTransitionAlg_symm, annulusTensorProjXₐ_comp_transitionAlg]

/-- The `(x, y)`-summand goes to the `(y, x)`-summand, through `bothSummandAntiInv`. -/
theorem tensorOverlapSummandXYBoth_comp_transitionSpf (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandXYBoth R I q hq hI ≫
        (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
          (annulusFibreOverlapTransitionAlg R I q hq hI)).hom =
      (bothSummandAntiInv R I q hI).hom ≫ tensorOverlapSummandYXBoth R I q hq hI := by
  rw [tensorOverlapSummandXYBoth, tensorOverlapSummandYXBoth, bothSummandAntiInv,
    CompletedTensorProduct.mapSpfIso_hom, CompletedTensorProduct.mapSpfIso_hom,
    ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
    annulusFibreOverlapTransitionAlg_symm, annulusTensorProjXₐ_comp_transitionAlg,
    AlgEquiv.symm_symm, annulusTensorProjYₐ_comp_transitionAlg]

/-- The `(y, x)`-summand goes to the `(x, y)`-summand, through the inverse of
`bothSummandAntiInv`. -/
theorem tensorOverlapSummandYXBoth_comp_transitionSpf (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandYXBoth R I q hq hI ≫
        (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
          (annulusFibreOverlapTransitionAlg R I q hq hI)).hom =
      (bothSummandAntiInv R I q hI).inv ≫ tensorOverlapSummandXYBoth R I q hq hI := by
  rw [tensorOverlapSummandXYBoth, tensorOverlapSummandYXBoth, bothSummandAntiInv,
    CompletedTensorProduct.mapSpfIso_hom, CompletedTensorProduct.mapSpfIso_inv,
    ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
    annulusFibreOverlapTransitionAlg_symm, annulusTensorProjXₐ_comp_transitionAlg,
    annulusTensorProjYₐ_comp_transitionAlg]

/-- The `(y, y)`-summand goes to the `(x, x)`-summand, through the inverse of
`bothSummandDiagInv`. -/
theorem tensorOverlapSummandYYBoth_comp_transitionSpf (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandYYBoth R I q hq hI ≫
        (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
          (annulusFibreOverlapTransitionAlg R I q hq hI)).hom =
      (bothSummandDiagInv R I q hI).inv ≫ tensorOverlapSummandXXBoth R I q hq hI := by
  rw [tensorOverlapSummandXXBoth, tensorOverlapSummandYYBoth, bothSummandDiagInv,
    CompletedTensorProduct.mapSpfIso_hom, CompletedTensorProduct.mapSpfIso_inv,
    ← CompletedTensorProduct.mapSpf_comp, ← CompletedTensorProduct.mapSpf_comp,
    annulusFibreOverlapTransitionAlg_symm, annulusTensorProjYₐ_comp_transitionAlg]

/-- The `hom` leg of the both-factors inversion transition, as a nested `coprod.desc`. -/
theorem tateSelfProductBothTransitionInv_hom (hI : I.FG) :
    (tateSelfProductBothTransitionInv R I q hI).hom =
      coprod.desc
        (coprod.desc ((bothSummandDiagInv R I q hI).hom ≫ coprod.inr ≫ coprod.inr)
          ((bothSummandAntiInv R I q hI).hom ≫ coprod.inl ≫ coprod.inr))
        (coprod.desc ((bothSummandAntiInv R I q hI).inv ≫ coprod.inr ≫ coprod.inl)
          ((bothSummandDiagInv R I q hI).inv ≫ coprod.inl ≫ coprod.inl)) := rfl

/-- The `(x, x)` branch of the both-factors law, pinned as its own declaration. See the module
docstring, implementation note 4: the same `rw` inside the assembled four-way goal times out. -/
theorem tateSelfProductBothTransitionInv_branch_xx (hq : q ∈ I) (hI : I.FG) :
    ((bothSummandDiagInv R I q hI).hom ≫ coprod.inr ≫ coprod.inr) ≫
        (tensorOverlapChartIsoBoth R I q hq hI).inv =
      tensorOverlapSummandXXBoth R I q hq hI ≫
        (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
          (annulusFibreOverlapTransitionAlg R I q hq hI)).hom := by
  rw [Category.assoc, Category.assoc, coprod_inr_inr_comp_tensorOverlapChartIsoBoth_inv]
  exact (tensorOverlapSummandXXBoth_comp_transitionSpf R I q hq hI).symm

/-- The `(x, y)` branch of the both-factors law. -/
theorem tateSelfProductBothTransitionInv_branch_xy (hq : q ∈ I) (hI : I.FG) :
    ((bothSummandAntiInv R I q hI).hom ≫ coprod.inl ≫ coprod.inr) ≫
        (tensorOverlapChartIsoBoth R I q hq hI).inv =
      tensorOverlapSummandXYBoth R I q hq hI ≫
        (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
          (annulusFibreOverlapTransitionAlg R I q hq hI)).hom := by
  rw [Category.assoc, Category.assoc, coprod_inl_inr_comp_tensorOverlapChartIsoBoth_inv]
  exact (tensorOverlapSummandXYBoth_comp_transitionSpf R I q hq hI).symm

/-- The `(y, x)` branch of the both-factors law. -/
theorem tateSelfProductBothTransitionInv_branch_yx (hq : q ∈ I) (hI : I.FG) :
    ((bothSummandAntiInv R I q hI).inv ≫ coprod.inr ≫ coprod.inl) ≫
        (tensorOverlapChartIsoBoth R I q hq hI).inv =
      tensorOverlapSummandYXBoth R I q hq hI ≫
        (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
          (annulusFibreOverlapTransitionAlg R I q hq hI)).hom := by
  rw [Category.assoc, Category.assoc, coprod_inr_inl_comp_tensorOverlapChartIsoBoth_inv]
  exact (tensorOverlapSummandYXBoth_comp_transitionSpf R I q hq hI).symm

/-- The `(y, y)` branch of the both-factors law. -/
theorem tateSelfProductBothTransitionInv_branch_yy (hq : q ∈ I) (hI : I.FG) :
    ((bothSummandDiagInv R I q hI).inv ≫ coprod.inl ≫ coprod.inl) ≫
        (tensorOverlapChartIsoBoth R I q hq hI).inv =
      tensorOverlapSummandYYBoth R I q hq hI ≫
        (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
          (annulusFibreOverlapTransitionAlg R I q hq hI)).hom := by
  rw [Category.assoc, Category.assoc, coprod_inl_inl_comp_tensorOverlapChartIsoBoth_inv]
  exact (tensorOverlapSummandYYBoth_comp_transitionSpf R I q hq hI).symm

/-- The `x`-row of the both-factors law. -/
theorem tateSelfProductBothTransitionInv_half_x (hq : q ∈ I) (hI : I.FG) :
    coprod.desc
        (((bothSummandDiagInv R I q hI).hom ≫ coprod.inr ≫ coprod.inr) ≫
          (tensorOverlapChartIsoBoth R I q hq hI).inv)
        (((bothSummandAntiInv R I q hI).hom ≫ coprod.inl ≫ coprod.inr) ≫
          (tensorOverlapChartIsoBoth R I q hq hI).inv) =
      coprod.desc
        (tensorOverlapSummandXXBoth R I q hq hI ≫
          (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
            (annulusFibreOverlapTransitionAlg R I q hq hI)).hom)
        (tensorOverlapSummandXYBoth R I q hq hI ≫
          (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
            (annulusFibreOverlapTransitionAlg R I q hq hI)).hom) := by
  rw [tateSelfProductBothTransitionInv_branch_xx, tateSelfProductBothTransitionInv_branch_xy]

/-- The `y`-row of the both-factors law. -/
theorem tateSelfProductBothTransitionInv_half_y (hq : q ∈ I) (hI : I.FG) :
    coprod.desc
        (((bothSummandAntiInv R I q hI).inv ≫ coprod.inr ≫ coprod.inl) ≫
          (tensorOverlapChartIsoBoth R I q hq hI).inv)
        (((bothSummandDiagInv R I q hI).inv ≫ coprod.inl ≫ coprod.inl) ≫
          (tensorOverlapChartIsoBoth R I q hq hI).inv) =
      coprod.desc
        (tensorOverlapSummandYXBoth R I q hq hI ≫
          (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
            (annulusFibreOverlapTransitionAlg R I q hq hI)).hom)
        (tensorOverlapSummandYYBoth R I q hq hI ≫
          (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
            (annulusFibreOverlapTransitionAlg R I q hq hI)).hom) := by
  rw [tateSelfProductBothTransitionInv_branch_yx, tateSelfProductBothTransitionInv_branch_yy]

/-- **The both-factors `t` law, in `inv` form.** Stated against `tensorOverlapChartIsoBoth.inv` on
both sides so that 761's packaged `coprod_desc_tensorOverlapSummandBoth` can replace the right-hand
`inv` and `coprod.desc_comp` can distribute both sides — which avoids `coprod.hom_ext` at four-fold
size altogether. -/
theorem tateSelfProductBothTransitionInv_hom_comp_inv (hq : q ∈ I) (hI : I.FG) :
    (tateSelfProductBothTransitionInv R I q hI).hom ≫
        (tensorOverlapChartIsoBoth R I q hq hI).inv =
      (tensorOverlapChartIsoBoth R I q hq hI).inv ≫
        (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
          (annulusFibreOverlapTransitionAlg R I q hq hI)).hom := by
  rw [tateSelfProductBothTransitionInv_hom]
  conv_rhs => rw [← coprod_desc_tensorOverlapSummandBoth R I q hq hI]
  simp only [coprod.desc_comp]
  rw [tateSelfProductBothTransitionInv_half_x, tateSelfProductBothTransitionInv_half_y]

/-- **The both-factors `t` law, at the level of the overlap objects.** -/
theorem tensorOverlapChartIsoBoth_transition_comm (hq : q ∈ I) (hI : I.FG) :
    (tensorOverlapChartIsoBoth R I q hq hI).hom ≫
        (tateSelfProductBothTransitionInv R I q hI).hom =
      (CompletedTensorProduct.mapSpfIso hI (annulusFibreOverlapTransitionAlg R I q hq hI)
          (annulusFibreOverlapTransitionAlg R I q hq hI)).hom ≫
        (tensorOverlapChartIsoBoth R I q hq hI).hom := by
  refine (Iso.eq_inv_comp _).1 ?_
  rw [← Category.assoc, ← tateSelfProductBothTransitionInv_hom_comp_inv R I q hq hI,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### Reducing the two dispatches by difference type

The companions of #277's `tateSelfProductGlueV_…` / `…GlueF_…` and `bothAlgDataV_…_const` /
`bothAlgDataF_…_const`, for the transition field. -/

/-- **The shared-coordinate transport of a constant chart family is the identity.** `eqAlgEquivA`
is `Eq.rec`-built, so this is not `rfl` at a variable equality, but `cases` makes it one. -/
theorem eqAlgEquivA_const {J : Type u} {C : Type u} [CommRing C] [Algebra R C] {i i' : J}
    (h : i = i') : eqAlgEquivA (R := R) (A := fun _ : J => C) h = AlgEquiv.refl := by
  cases h; rfl

/-- The `B`-side companion of `eqAlgEquivA_const`. -/
theorem eqAlgEquivB_const {J : Type u} {C : Type u} [CommRing C] [Algebra R C] {j j' : J}
    (h : j = j') : eqAlgEquivB (R := R) (B := fun _ : J => C) h = AlgEquiv.refl := by
  cases h; rfl

/-- **The Tate transition in the second-coordinate-differs shape.** -/
theorem tateSelfProductGlueTInv_snd (hI : I.FG) (i j : Bool × Bool) (h : i ≠ j)
    (h1 : i.1 = j.1) :
    tateSelfProductGlueTInv R I q hI i j h =
      eqToHom (tateSelfProductGlueV_snd hI i j h h1) ≫
        (tateSelfProductRightTransitionInv R I q hI).hom ≫
          eqToHom (tateSelfProductGlueV_snd hI j i h.symm h1.symm).symm := by
  rcases i with ⟨_ | _, _ | _⟩ <;> rcases j with ⟨_ | _, _ | _⟩ <;>
    first
      | exact (h rfl).elim
      | exact absurd h1 (by decide)
      | exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- **The Tate transition in the first-coordinate-differs shape.** -/
theorem tateSelfProductGlueTInv_fst (hI : I.FG) (i j : Bool × Bool) (h : i ≠ j)
    (h1 : i.1 ≠ j.1) (h2 : i.2 = j.2) :
    tateSelfProductGlueTInv R I q hI i j h =
      eqToHom (tateSelfProductGlueV_fst hI i j h h1 h2) ≫
        (tateSelfProductFirstTransitionInv R I q hI).hom ≫
          eqToHom (tateSelfProductGlueV_fst hI j i h.symm (fun e => h1 e.symm) h2.symm).symm := by
  rcases i with ⟨_ | _, _ | _⟩ <;> rcases j with ⟨_ | _, _ | _⟩ <;>
    first
      | exact (h rfl).elim
      | exact absurd h2 (by decide)
      | exact absurd rfl h1
      | exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- **The Tate transition in the both-coordinates-differ shape.** -/
theorem tateSelfProductGlueTInv_both (hI : I.FG) (i j : Bool × Bool) (h : i ≠ j)
    (h1 : i.1 ≠ j.1) (h2 : i.2 ≠ j.2) :
    tateSelfProductGlueTInv R I q hI i j h =
      eqToHom (tateSelfProductGlueV_both hI i j h h1 h2) ≫
        (tateSelfProductBothTransitionInv R I q hI).hom ≫
          eqToHom (tateSelfProductGlueV_both hI j i h.symm
            (fun e => h1 e.symm) (fun e => h2 e.symm)).symm := by
  rcases i with ⟨_ | _, _ | _⟩ <;> rcases j with ⟨_ | _, _ | _⟩ <;>
    first
      | exact (h rfl).elim
      | exact absurd rfl h1
      | exact absurd rfl h2
      | exact ((Category.id_comp _).trans (Category.comp_id _)).symm

section Const

variable {C : Type u} [CommRing C] [Algebra R C]

/-- `bothAlgDataT` for a constant chart family, second-coordinate-differs shape. -/
theorem bothAlgDataT_snd_const (hI : I.FG) (g : C)
    (τX τY : ∀ i i' : ULift.{u} Bool, i ≠ i' →
      (awayCompletion (I.map (algebraMap R C)) g ≃ₐ[R] awayCompletion (I.map (algebraMap R C)) g))
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') (h1 : p.1 = p'.1) :
    bothAlgDataT (A := fun _ : ULift.{u} Bool => C) (B := fun _ : ULift.{u} Bool => C) hI
        (fun _ _ => g) (fun _ _ => g) τX τY p p' h =
      eqToHom (bothAlgDataV_snd_const R I hI g p p' h h1) ≫
        (CompletedTensorProduct.mapSpfIso hI
            (eqAlgEquivA (A := fun _ : ULift.{u} Bool => C) h1)
            (τY p.2 p'.2 (fun e => h (Prod.ext h1 e)))).hom ≫
          eqToHom (bothAlgDataV_snd_const R I hI g p' p h.symm h1.symm).symm := by
  unfold bothAlgDataT
  rw [dif_pos h1]

/-- `bothAlgDataT` for a constant chart family, first-coordinate-differs shape. -/
theorem bothAlgDataT_fst_const (hI : I.FG) (g : C)
    (τX τY : ∀ i i' : ULift.{u} Bool, i ≠ i' →
      (awayCompletion (I.map (algebraMap R C)) g ≃ₐ[R] awayCompletion (I.map (algebraMap R C)) g))
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') (h1 : p.1 ≠ p'.1) (h2 : p.2 = p'.2) :
    bothAlgDataT (A := fun _ : ULift.{u} Bool => C) (B := fun _ : ULift.{u} Bool => C) hI
        (fun _ _ => g) (fun _ _ => g) τX τY p p' h =
      eqToHom (bothAlgDataV_fst_const R I hI g p p' h h1 h2) ≫
        (CompletedTensorProduct.mapSpfIso hI (τX p.1 p'.1 h1)
            (eqAlgEquivB (B := fun _ : ULift.{u} Bool => C) h2)).hom ≫
          eqToHom (bothAlgDataV_fst_const R I hI g p' p h.symm
            (fun e => h1 e.symm) h2.symm).symm := by
  unfold bothAlgDataT
  rw [dif_neg h1, dif_pos h2]

/-- `bothAlgDataT` for a constant chart family, both-coordinates-differ shape. -/
theorem bothAlgDataT_both_const (hI : I.FG) (g : C)
    (τX τY : ∀ i i' : ULift.{u} Bool, i ≠ i' →
      (awayCompletion (I.map (algebraMap R C)) g ≃ₐ[R] awayCompletion (I.map (algebraMap R C)) g))
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') (h1 : p.1 ≠ p'.1) (h2 : p.2 ≠ p'.2) :
    bothAlgDataT (A := fun _ : ULift.{u} Bool => C) (B := fun _ : ULift.{u} Bool => C) hI
        (fun _ _ => g) (fun _ _ => g) τX τY p p' h =
      eqToHom (bothAlgDataV_both_const R I hI g p p' h h1 h2) ≫
        (CompletedTensorProduct.mapSpfIso hI (τX p.1 p'.1 h1) (τY p.2 p'.2 h2)).hom ≫
          eqToHom (bothAlgDataV_both_const R I hI g p' p h.symm
            (fun e => h1 e.symm) (fun e => h2 e.symm)).symm := by
  unfold bothAlgDataT
  rw [dif_neg h1, dif_neg h2]

end Const

/-! ### The transition law of the `Ψ` comparison -/

/-- **The `t` law in the second-coordinate-differs shape.** -/
theorem tateOverlapCompareIso_hom_t_snd (hq : q ∈ I) (hI : I.FG)
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') (h1 : p.1 = p'.1) :
    (tateOverlapCompareIso R I q hq hI p p' h).hom ≫
        tateSelfProductGlueTInv R I q hI (tateFibreIdx p) (tateFibreIdx p')
          (tateFibreIdx_ne h) =
      bothAlgDataT (A := tateFibreA R I q) (B := tateFibreA R I q) hI
          (tateFibreG R I q) (tateFibreG R I q)
          (fun _ _ _ => annulusFibreOverlapTransitionAlg R I q hq hI)
          (fun _ _ _ => annulusFibreOverlapTransitionAlg R I q hq hI) p p' h ≫
        (tateOverlapCompareIso R I q hq hI p' p h.symm).hom := by
  rw [tateOverlapCompareIso, dif_pos h1, tateOverlapCompareIso, dif_pos h1.symm,
    tateSelfProductGlueTInv_snd R I q hI _ _ (tateFibreIdx_ne h) (congrArg ULift.down h1),
    bothAlgDataT_snd_const R I hI (overlapX R I q + overlapY R I q) _ _ p p' h h1,
    eqAlgEquivA_const]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [reassoc_of% (tensorOverlapChartIsoSecond_transition_comm R I q hq hI)]

/-- **The `t` law in the first-coordinate-differs shape.** -/
theorem tateOverlapCompareIso_hom_t_fst (hq : q ∈ I) (hI : I.FG)
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') (h1 : p.1 ≠ p'.1) (h2 : p.2 = p'.2) :
    (tateOverlapCompareIso R I q hq hI p p' h).hom ≫
        tateSelfProductGlueTInv R I q hI (tateFibreIdx p) (tateFibreIdx p')
          (tateFibreIdx_ne h) =
      bothAlgDataT (A := tateFibreA R I q) (B := tateFibreA R I q) hI
          (tateFibreG R I q) (tateFibreG R I q)
          (fun _ _ _ => annulusFibreOverlapTransitionAlg R I q hq hI)
          (fun _ _ _ => annulusFibreOverlapTransitionAlg R I q hq hI) p p' h ≫
        (tateOverlapCompareIso R I q hq hI p' p h.symm).hom := by
  rw [tateOverlapCompareIso, dif_neg h1, dif_pos h2, tateOverlapCompareIso,
    dif_neg (fun e => h1 e.symm), dif_pos h2.symm,
    tateSelfProductGlueTInv_fst R I q hI _ _ (tateFibreIdx_ne h)
      (fun e => h1 (ULift.ext _ _ e)) (congrArg ULift.down h2),
    bothAlgDataT_fst_const R I hI (overlapX R I q + overlapY R I q) _ _ p p' h h1 h2,
    eqAlgEquivB_const]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [reassoc_of% (tensorOverlapChartIsoFirst_transition_comm R I q hq hI)]

/-- **The `t` law in the both-coordinates-differ shape.** -/
theorem tateOverlapCompareIso_hom_t_both (hq : q ∈ I) (hI : I.FG)
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') (h1 : p.1 ≠ p'.1) (h2 : p.2 ≠ p'.2) :
    (tateOverlapCompareIso R I q hq hI p p' h).hom ≫
        tateSelfProductGlueTInv R I q hI (tateFibreIdx p) (tateFibreIdx p')
          (tateFibreIdx_ne h) =
      bothAlgDataT (A := tateFibreA R I q) (B := tateFibreA R I q) hI
          (tateFibreG R I q) (tateFibreG R I q)
          (fun _ _ _ => annulusFibreOverlapTransitionAlg R I q hq hI)
          (fun _ _ _ => annulusFibreOverlapTransitionAlg R I q hq hI) p p' h ≫
        (tateOverlapCompareIso R I q hq hI p' p h.symm).hom := by
  rw [tateOverlapCompareIso, dif_neg h1, dif_neg h2, tateOverlapCompareIso,
    dif_neg (fun e => h1 e.symm), dif_neg (fun e => h2 e.symm),
    tateSelfProductGlueTInv_both R I q hI _ _ (tateFibreIdx_ne h)
      (fun e => h1 (ULift.ext _ _ e)) (fun e => h2 (ULift.ext _ _ e)),
    bothAlgDataT_both_const R I hI (overlapX R I q + overlapY R I q) _ _ p p' h h1 h2]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [reassoc_of% (tensorOverlapChartIsoBoth_transition_comm R I q hq hI)]

/-- **The transition law of the `Ψ` comparison.** The overlap comparison isomorphism of 705c
intertwines the Tate glue datum's transition `tateSelfProductGlueTInv` with the generic datum's
`bothAlgDataT`, at every pair of distinct product indices.

Together with `tateOverlapCompareIso_hom_fac` (the `f` law) this is the whole of the glue-datum
compatibility that `FormalScheme.GlueData.glueMorphisms` needs, so `Ψ` can now be built.

The `τ` here is `annulusFibreOverlapTransitionAlg` at every ordered pair, which is the Tate
`X`-expose datum's own transition by `tateCurveExposeXDatum_τ` (an `rfl`); as in
`TateFibreOverlapCompare.lean`, the statement is against the raw algebra data so that it does not
depend on the `ofFactors` / `diagonalDatum` packaging. -/
theorem tateOverlapCompareIso_hom_t (hq : q ∈ I) (hI : I.FG)
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') :
    (tateOverlapCompareIso R I q hq hI p p' h).hom ≫
        tateSelfProductGlueTInv R I q hI (tateFibreIdx p) (tateFibreIdx p')
          (tateFibreIdx_ne h) =
      bothAlgDataT (A := tateFibreA R I q) (B := tateFibreA R I q) hI
          (tateFibreG R I q) (tateFibreG R I q)
          (fun _ _ _ => annulusFibreOverlapTransitionAlg R I q hq hI)
          (fun _ _ _ => annulusFibreOverlapTransitionAlg R I q hq hI) p p' h ≫
        (tateOverlapCompareIso R I q hq hI p' p h.symm).hom := by
  by_cases h1 : p.1 = p'.1
  · exact tateOverlapCompareIso_hom_t_snd R I q hq hI p p' h h1
  · by_cases h2 : p.2 = p'.2
    · exact tateOverlapCompareIso_hom_t_fst R I q hq hI p p' h h1 h2
    · exact tateOverlapCompareIso_hom_t_both R I q hq hI p p' h h1 h2

end AlgebraicGeometry

end
