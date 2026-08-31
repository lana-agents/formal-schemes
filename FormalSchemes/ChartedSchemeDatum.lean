import FormalSchemes.CompletionTwoPatchToScheme
import FormalSchemes.SpecAwayOverlap
import FormalSchemes.SpfRingEquivIso

set_option linter.style.header false

/-!
# The arbitrary-index charted-scheme datum, and the glued scheme (EGA I, 10.8)

`FormalSchemes/CompletionTwoPatchToScheme.lean` builds the ambient scheme
`Spec A ∪_{D(a) ≅ D(b)} Spec B` of the two-patch formal completion, on the index type
`ULift Bool`. This file is the arbitrary-index version of that construction: a datum of affine
charts glued along basic opens, and the locally ringed space it glues to.

It is the **target** half of `X_{/Y} ⟶ X` at an arbitrary index; the completion half and the
morphism are issue 60q.

## Why this needs a new datum, and not `AffineChartedFibreDatumX`

The natural guess is that `AlgebraicGeometry.AffineChartedFibreDatumX`
(`FormalSchemes.GeneralFibreProductExposeX`) — which already glues `Spf (A i)` along basic-open
charts at an arbitrary index — can be re-used with `Spec` in place of `Spf`. It cannot, and the
obstruction is in its fields rather than in the difficulty of the construction.

* Its transition field, inherited from `AlgebraicGeometry.AffineChartedFibreDatum`, is an
  isomorphism of **away completions** `A_i{1/g_ij} ≃ₐ[R] A_j{1/g_ji}`. The ambient scheme's gluing
  needs one of **localizations**, and that is exactly what the two-patch line takes as input:
  `θ : Localization.Away a ≃+* Localization.Away b`, with `AlgebraicGeometry.specGlueIso` being
  `Spec` of it. Completion does not run backwards, so `θ` is not recoverable from `τ` — it is new
  input.
* Its chart algebras are already complete: its `isAdic` field asks for `IsAdicRing (I·A_i)` on
  every chart. So `A i` plays the role of `A^` and the ambient chart `Spec A` does not occur in the
  datum either.

## What the new shape buys: independent ideals

`AffineChartedFibreDatumX` carries **one** ideal `I` in **one** base ring `R`, with every chart an
`R`-algebra and every transition an `R`-algebra map. That is a real restriction — the completion of
the projective line at a closed point is not of that shape, because the two charts want different
ideals.

`ChartedSchemeDatum` below carries an ideal `K i` in each chart ring `C i` separately, exactly as
the two-patch line does (`(A, I, a)` and `(B, J, b)`, with `I` and `J` unrelated). The projective
line completed at a closed point is then a two-chart datum with `C₀ = k[x]`, `C₁ = k[y]`,
`K₀ = (x)` and `K₁ = ⊤` — the point is not in the second chart, and `Spf` of a unit ideal is empty,
so the compatibility `hθ` reads `⊤ ↦ ⊤`. **That example is not formalised here**; the isomorphism
`k[x]_x ≃+* k[y]_y` carrying `x` to `y⁻¹` is its own piece of plumbing. What is formalised is the
datum shape that admits it, and `AlgebraicGeometry.ChartedSchemeDatum.ofTwoPatch` below, whose two
ideals genuinely live in different rings.

## Main definitions and results

* `AlgebraicGeometry.ChartedSchemeDatum`: the datum — chart rings `C i` with their own ideals
  `K i`, away elements `g i j`, localization transitions `θ i j`, the ideal compatibility `hθ`,
  and the geometric triple-overlap fields `t'`, `t_fac`, `cocycle`.
* `AlgebraicGeometry.ChartedSchemeDatum.specGlueData'`,
  `AlgebraicGeometry.ChartedSchemeDatum.specLRSGlueData`,
  `AlgebraicGeometry.ChartedSchemeDatum.specGlued`: the glue datum and the glued scheme, with
  `AlgebraicGeometry.ChartedSchemeDatum.specι` its charts,
  `AlgebraicGeometry.ChartedSchemeDatum.specι_isOpenImmersion` and
  `AlgebraicGeometry.ChartedSchemeDatum.specGlued_jointly_surjective`.
* `AlgebraicGeometry.ChartedSchemeDatum.ofTwoPatch`: the two-patch line's own input, read as a
  datum. Its two ideals are `I : Ideal A` and `J : Ideal B`, in different rings.

## The design choice, stated rather than left implicit

`t'`, `t_fac` and `cocycle` are **carried as fields**, mirroring `AffineChartedFibreDatumX` rather
than derived. Deriving them is not obviously wrong — every `f i j` here is `Spec` of a localization
map, hence a monomorphism, so `t'` is *unique* if it exists and the content is a condition on `θ`
rather than data — but Mathlib's `CategoryTheory.GlueData'` takes `t'` as a field regardless, so
deriving it would mean a smart constructor, and a smart constructor needs the `Spec`-side overlap
identification `AlgebraicGeometry.specAwayOverlapIso` (`FormalSchemes.SpecAwayOverlap`, issue 60p)
together with the triple-overlap algebra data it is fed at `g i j * g i k`. That smart constructor,
and the three-chart datum it unlocks, are deliberately not in this file.

## What is *not* proved

* **No datum with a non-vacuous triple overlap is built here.** `ofTwoPatch` is on `ULift Bool`,
  where no triple of indices is pairwise distinct, so its `t'`, `t_fac` and `cocycle` are
  `False.elim`. The construction above is stated at an arbitrary index type and the fields are
  genuine there; but nothing in this file *exercises* them, and that is the same gap
  `FormalSchemes.CompletionAsChartedGlued` had at `ULift Unit` before the three-chart datum was
  built. A `Spec`-side three-chart instance is the successor row.
* `specGlued` of `ofTwoPatch` is **not** identified with `AlgebraicGeometry.specTwoPatch`. The two
  glue data agree field for field on `f`, `t` and the three vacuous ones, but their `U` fields are
  `Spec (cond i.down B A)` here and `cond i.down (Spec B) (Spec A)` there, which are not
  definitionally equal at a variable index; joining them is an isomorphism of glue data and is not
  needed by anything.
* **The datum carries `K i` but not `(K i).FG`, and the completion side will need the latter.**
  `formalCompletion` (root-namespace) takes finite generation as an explicit argument to the
  *object* — its signature is `(R) → [CommRing R] → (I : Ideal R) → I.FG → FormalScheme` — so a
  `ChartedSchemeDatum` does not by itself name the formal charts `Spf (C i)^` that 60q glues. The
  two-patch line this datum mirrors carries `hI : I.FG` and `hJ : J.FG` alongside its ideals
  (`FormalSchemes.CompletionGlueTwoPatch`). 60q must therefore either take `∀ i, (D.K i).FG` as a
  side hypothesis or add it as a field here; adding it is cheapest now, while `ofTwoPatch` is the
  only construction.
* Nothing here relates `specGlued` to a completion, states a universal property for it, or promotes
  it to `AlgebraicGeometry.Scheme`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **The two legs of `specGlueIso` compose to the identity in the `θ`/`θ.symm` spelling.** The
glue datum's `t_inv` field arrives with `t j i` written at `θ j i`, which `θ_symm` rewrites to
`(θ i j).symm`; this is the resulting equation. -/
theorem specGlueIso_hom_comp_symm_hom {A B : Type u} [CommRing A] [CommRing B] (a : A) (b : B)
    (θ : Localization.Away a ≃+* Localization.Away b) :
    (specGlueIso a b θ).hom ≫ (specGlueIso b a θ.symm).hom = 𝟙 _ :=
  (specGlueIso a b θ).hom_inv_id

/-! ### The datum -/

set_option linter.unusedVariables false in
/-- **A family of affine charts glued along basic opens, with an ideal in each chart.**

The fields up to `hθ` are the two-patch line's input at an arbitrary index: chart rings `C i`, an
ideal `K i` in each, away elements `g i j` cutting out the overlap of the `i`-th chart with the
`j`-th, localization transitions `θ i j`, and the compatibility `hθ` saying `θ i j` carries `K i`
onto `K j` on the overlap — which is what makes the corresponding formal-completion glue adic.

The last three fields are the geometric triple-overlap data of the glue, in the shape
`CategoryTheory.GlueData'` demands. They are vacuous on a two-element index type. -/
structure ChartedSchemeDatum where
  /-- The index type of the charts. -/
  J : Type u
  /-- The coordinate ring of the `i`-th affine chart. -/
  C : J → Type u
  [commRing : ∀ i, CommRing (C i)]
  /-- The ideal of the `i`-th chart along which it is to be completed. Unrelated to the others. -/
  K : ∀ i, Ideal (C i)
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
  /-- The geometric triple-overlap transition. -/
  t' : ∀ (i j k : J) (_hij : i ≠ j) (_hik : i ≠ k) (_hjk : j ≠ k),
    (pullback (specAwayMap (g i j)) (specAwayMap (g i k)) ⟶
      pullback (specAwayMap (g j k)) (specAwayMap (g j i)))
  /-- Compatibility of `t'` with the single-overlap transition (the `t_fac` law). -/
  t_fac : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    t' i j k hij hik hjk ≫ pullback.snd (specAwayMap (g j k)) (specAwayMap (g j i)) =
      pullback.fst (specAwayMap (g i j)) (specAwayMap (g i k)) ≫
        (specGlueIso (g i j) (g j i) (θ i j hij)).hom
  /-- The triple cocycle. -/
  cocycle : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    t' i j k hij hik hjk ≫ t' j k i hjk hij.symm hik.symm ≫
      t' k i j hik.symm hjk.symm hij = 𝟙 _

attribute [instance] ChartedSchemeDatum.commRing

namespace ChartedSchemeDatum

variable (D : ChartedSchemeDatum.{u})

/-- **The glue datum of the ambient scheme**, as a `CategoryTheory.GlueData'` on `D.J`: the `i`-th
patch is `Spec (C i)`, the overlap is `Spec ((C i)_{g i j})`, the inclusion is
`specAwayMap (g i j)` and the transition is `specGlueIso` at `θ i j`. The structural fields
`f_mono` and `f_hasPullback` come from `isOpenImmersion_specAwayMap`; `t_inv` is `θ_symm` followed
by `specGlueIso_hom_comp_symm_hom`; and `t'`, `t_fac`, `cocycle` are the carried geometric data.

This is `AlgebraicGeometry.specTwoPatchGlueData'` at an arbitrary index type. -/
def specGlueData' : CategoryTheory.GlueData' LocallyRingedSpace.{u} where
  J := D.J
  U := fun i => Spec.locallyRingedSpaceObj (CommRingCat.of (D.C i))
  V := fun i j _ => Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away (D.g i j)))
  f := fun i j _ => specAwayMap (D.g i j)
  f_mono := fun i j _ => inferInstance
  f_hasPullback := fun i j k _ _ => inferInstance
  t := fun i j h => (specGlueIso (D.g i j) (D.g j i) (D.θ i j h)).hom
  t' := D.t'
  t_fac := D.t_fac
  t_inv := fun i j h => by
    rw [D.θ_symm i j h]
    exact specGlueIso_hom_comp_symm_hom (D.g i j) (D.g j i) (D.θ i j h)
  cocycle := D.cocycle

/-- **The glue datum as a `LocallyRingedSpace.GlueData`**, via `GlueData.ofGlueData'` and the
open-immersion field `f_open`. Off the diagonal each glue map is `eqToHom` followed by an affine
chart inclusion; on the diagonal it is `eqToHom`. -/
def specLRSGlueData : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' D.specGlueData' with
    f_open := by
      intro i j
      simp only [specGlueData', CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · exact inferInstanceAs
          (LocallyRingedSpace.IsOpenImmersion (eqToHom _ ≫ specAwayMap (D.g i j))) }

/-- **The glued scheme**, as a locally ringed space: the charts `Spec (C i)` glued along the
identifications `θ i j` of their overlaps. At two patches this is
`AlgebraicGeometry.specTwoPatch`. -/
def specGlued : LocallyRingedSpace.{u} :=
  D.specLRSGlueData.toGlueData.glued

/-- The `i`-th chart as an open subspace of the glued scheme. -/
def specι (i : D.J) :
    Spec.locallyRingedSpaceObj (CommRingCat.of (D.C i)) ⟶ D.specGlued :=
  D.specLRSGlueData.toGlueData.ι i

instance specι_isOpenImmersion (i : D.J) :
    LocallyRingedSpace.IsOpenImmersion (D.specι i) :=
  LocallyRingedSpace.GlueData.ι_isOpenImmersion _ _

/-- **The charts cover the glued scheme.** -/
theorem specGlued_jointly_surjective (x : D.specGlued) :
    ∃ (i : D.J) (y : Spec.locallyRingedSpaceObj (CommRingCat.of (D.C i))),
      (D.specι i).base y = x :=
  D.specLRSGlueData.ι_jointly_surjective x

end ChartedSchemeDatum

/-! ### The two-patch line, read as a datum -/

section TwoPatch

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (a : A) (J : Ideal B) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

/-- On a two-element index type no triple is pairwise distinct. -/
private theorem bool_not_pairwise_distinct {i j k : ULift.{u} Bool}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : False := by
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  obtain ⟨k⟩ := k
  cases i <;> cases j <;> cases k <;> simp_all

/-- **The two-patch input, as a `ChartedSchemeDatum`.** The charts are `Spec A` and `Spec B`, the
ideals are `I ⊆ A` and `J ⊆ B` — in different rings, and unrelated to each other, which is the
point of this datum shape — and the transition is the two-patch line's own `θ`. The three geometric
fields are vacuous, since no triple of `Bool`-indices is pairwise distinct.

The backward ideal compatibility is `FormalSpectrum.isAdicHom_ringEquiv_symm`
(`FormalSchemes.SpfRingEquivIso`): `IsAdicHom` — which is root-namespace, unlike the lemma that
consumes it — unfolds to an `Ideal.map` equation, so `hθ` *is* the forward adicity of `θ` and that
lemma turns it around. -/
def ChartedSchemeDatum.ofTwoPatch : ChartedSchemeDatum.{u} where
  J := ULift.{u} Bool
  C := fun i => cond i.down B A
  commRing := fun i => match i with
    | ⟨false⟩ => inferInstanceAs (CommRing A)
    | ⟨true⟩ => inferInstanceAs (CommRing B)
  K := fun i => match i with
    | ⟨false⟩ => I
    | ⟨true⟩ => J
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
  t' := fun _ _ _ hij hik hjk => (bool_not_pairwise_distinct hij hik hjk).elim
  t_fac := fun _ _ _ hij hik hjk => (bool_not_pairwise_distinct hij hik hjk).elim
  cocycle := fun _ _ _ hij hik hjk => (bool_not_pairwise_distinct hij hik hjk).elim

/-- The `A`-side ideal of the two-patch datum is `I`, in `A`. -/
theorem ChartedSchemeDatum.ofTwoPatch_K_false :
    (ChartedSchemeDatum.ofTwoPatch I a J b θ hθ).K ⟨false⟩ = I :=
  rfl

/-- The `B`-side ideal of the two-patch datum is `J`, in `B`: the two ideals of a
`ChartedSchemeDatum` live in different rings and are not images of one another. -/
theorem ChartedSchemeDatum.ofTwoPatch_K_true :
    (ChartedSchemeDatum.ofTwoPatch I a J b θ hθ).K ⟨true⟩ = J :=
  rfl

end TwoPatch

end AlgebraicGeometry

end
