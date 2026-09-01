import FormalSchemes.CompletionBasicOpenMap
import FormalSchemes.CompletionGlueTwoPatch
import FormalSchemes.CompletionGlueTwoPatchCondition
import FormalSchemes.GlueMorphisms
import FormalSchemes.SpecAwayOverlap

set_option linter.style.header false

/-!
# The two-patch glued scheme, and the completion morphism into it (EGA I, 10.8)

`FormalSchemes/CompletionGlueTwoPatch.lean` glues the formal completions of two affine charts
`Spec A ⊇ V(I)` and `Spec B ⊇ V(J)` along a common basic open `D(a) ≅ D(b)`, producing the formal
scheme `completionTwoPatch`. Its module docstring says that object *is* the completion of the
two-chart scheme `Spec A ∪_{D(a) ≅ D(b)} Spec B`, but nothing there mentions a scheme: the input is
ring data and the glued scheme does not exist in the development. This file builds it, and builds
the canonical morphism from the glued completion to it.

```
completionTwoPatch  ──completionTwoPatchToScheme──→  specTwoPatch
```

This is `formalCompletion.toSpec : X_{/Y} ⟶ X` for the first **non-affine** `X` in this
development. Everything before it completes an affine and maps to `Spec R`.

## How it is built, and what makes it cheap

`specTwoPatch` is glued exactly as `completionTwoPatch` is: a `CategoryTheory.GlueData'` on the
index type `ULift Bool`, with `Spec A` and `Spec B` as patches, `Spec A_a` and `Spec B_b` as
overlaps, the affine chart inclusions `Spec (A → A_a)` as the inclusions, and `Spec θ` as the
transition. That those inclusions are open immersions of locally ringed spaces —
`AlgebraicGeometry.isOpenImmersion_specAwayMap`, which the `f_mono`, `f_hasPullback` and `f_open`
fields all need — used to be stated here; it is general in the ring and the element and says
nothing about two patches, so it now lives in `FormalSchemes/SpecAwayOverlap.lean` together with
the range computation and the overlap identification that an arbitrary-index version of this glue
would consume. As there, the `t'`, `t_fac` and `cocycle` fields are vacuous because no triple of
`Bool`-indices is pairwise distinct.

The morphism is `AlgebraicGeometry.completionTwoPatchDesc`
(`FormalSchemes/CompletionGlueTwoPatchCondition.lean`) applied to the two per-chart morphisms
`formalCompletion.toSpec A I ≫ ι₀` and `formalCompletion.toSpec B J ≫ ι₁`; that is where the
`GlueData.ofGlueData'` bookkeeping of the completion datum lives, discharged once for every
compatible pair, so this file carries none of it. Its overlap obligation is precisely what
`FormalSchemes/CompletionBasicOpenMap.lean` was built to supply: on each side
`formalCompletion.basicOpenImmersion_comp_toSpec` turns the chart inclusion followed by `toSpec`
into `toSpec` on the overlap followed by `Spec` of the localization, and
`formalCompletion.map_comp_toSpec` does the same for the transition isomorphism, which is
`formalCompletion.map` of `θ.symm`. Both sides then reduce to

```
toSpec A_a (I·A_a) ≫ Spec θ.symm ≫ Spec (B → B_b) ≫ ι₁
```

and what closes the gap between the two chart inclusions is the target's own glue condition,
recorded here as `specTwoPatch_glue`.

## Main definitions and results

* `AlgebraicGeometry.specGlueIso`: `Spec` of the overlap identification `θ`.
* `AlgebraicGeometry.specTwoPatchGlueData'`, `AlgebraicGeometry.specTwoPatchLRSGlueData`,
  `AlgebraicGeometry.specTwoPatch`: the glued scheme `Spec A ∪_{D(a) ≅ D(b)} Spec B`, as a locally
  ringed space, with `AlgebraicGeometry.specTwoPatchι₀` / `..ι₁` its two affine charts and
  `AlgebraicGeometry.specTwoPatch_jointly_surjective`: they cover it.
* `AlgebraicGeometry.specTwoPatch_glue`: the two charts agree on the overlap.
* `AlgebraicGeometry.completionTwoPatch_overlapCompat₀` / `..₁`: **the overlap compatibility**, that
  the two per-chart morphisms `X_{/Y}|_{chart} ⟶ X` agree over `D(a) ≅ D(b)`.
* `AlgebraicGeometry.completionTwoPatchToScheme`: the glued morphism, with
  `AlgebraicGeometry.completionTwoPatchι₀_comp_toScheme` / `..ι₁..` characterising it chart by
  chart, `AlgebraicGeometry.completionTwoPatch_hom_ext` for uniqueness and
  `AlgebraicGeometry.completionTwoPatchToScheme_eq_desc` exhibiting it as a descent.

## Scope

The glued object is a `LocallyRingedSpace`, not an `AlgebraicGeometry.Scheme`: that is the category
`formalCompletion.toSpec` lives in, and promoting it is a separate question needing a different
Mathlib API. Nothing here claims that `completionTwoPatchToScheme` is universal, or identifies
`completionTwoPatch` with a completion of `specTwoPatch` in any sense stronger than the morphism
below — the affine case of that (the universal property of `toSpec`) is not on master either.

## The arbitrary-index version, and what the note above used to get wrong about it

Everything above is built at an arbitrary index type in
`AlgebraicGeometry.ChartedCompletionDatum.toScheme` (`FormalSchemes.ChartedCompletionToScheme`),
with `completionι_comp_toScheme` its computation rule and `toScheme_unique` its uniqueness; its
target is `AlgebraicGeometry.ChartedSchemeDatum.specGlued` (`FormalSchemes.ChartedSchemeDatum`).

The `Scope` note above used to end *"what is still missing for the arbitrary-index morphism is the
glued **target**, not the cocycle"*, and the second clause was the misleading one.
`FormalSchemes.CompletionBasicOpenGlue` does build a triple-overlap `t'` at an arbitrary index,
from the overlap-as-fibre-product input `formalCompletion.basicOpenOverlapIso`
(`FormalSchemes.CompletionBasicOpenOverlap`) — but it discharges `t_fac`, `t_inv` and `cocycle` by
`cancel_mono` against the common ambient object `Spf R^` that every basic open of a **single**
affine lies over. Charts with unrelated coordinate rings have nothing lying under all of them, so
that cocycle does not instantiate; `ChartedCompletionDatum.tripleTransition` rebuilds it, mirroring
the `Spec` side (`AlgebraicGeometry.ChartedSchemeDatum.specAlgDataT'`) instead.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section Glued

variable {A B : Type u} [CommRing A] [CommRing B] (a : A) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)

/-- **The gluing isomorphism of the overlap**, `Spec` of the identification `θ : A_a ≃+* B_b`.
Both legs are `Spec.locallyRingedSpaceMap`, of `θ.symm` and of `θ`; that they are mutually inverse
is functoriality of `Spec` (`Spec.locallyRingedSpaceMap_comp`, `_id`) applied to
`θ.symm ∘ θ = id` and `θ ∘ θ.symm = id`. Note `Spec.locallyRingedSpaceMap_comp` is contravariant,
so the `hom` of an `A_a → B_b` glue iso is built from `θ.symm`, exactly as `completionGlueIso`'s
is. -/
def specGlueIso :
    Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away a)) ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away b)) where
  hom := Spec.locallyRingedSpaceMap (CommRingCat.ofHom θ.symm.toRingHom)
  inv := Spec.locallyRingedSpaceMap (CommRingCat.ofHom θ.toRingHom)
  hom_inv_id := by
    rw [← Spec.locallyRingedSpaceMap_comp]
    convert Spec.locallyRingedSpaceMap_id (CommRingCat.of (Localization.Away a)) using 2
    ext x
    exact θ.symm_apply_apply x
  inv_hom_id := by
    rw [← Spec.locallyRingedSpaceMap_comp]
    convert Spec.locallyRingedSpaceMap_id (CommRingCat.of (Localization.Away b)) using 2
    ext x
    exact θ.apply_symm_apply x

/-- The `A`-side patch `Spec A`. -/
private abbrev spU₀ : LocallyRingedSpace.{u} := Spec.locallyRingedSpaceObj (CommRingCat.of A)

/-- The `B`-side patch `Spec B`. -/
private abbrev spU₁ : LocallyRingedSpace.{u} := Spec.locallyRingedSpaceObj (CommRingCat.of B)

/-- The `A`-side overlap `Spec A_a`. -/
private abbrev spV₀ : LocallyRingedSpace.{u} :=
  Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away a))

/-- The `B`-side overlap `Spec B_b`. -/
private abbrev spV₁ : LocallyRingedSpace.{u} :=
  Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away b))

/-- The `A`-side chart inclusion `Spec A_a ⟶ Spec A`. -/
private abbrev spF₀ : spV₀ a ⟶ spU₀ (A := A) :=
  Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap A (Localization.Away a)))

/-- The `B`-side chart inclusion `Spec B_b ⟶ Spec B`. -/
private abbrev spF₁ : spV₁ b ⟶ spU₁ (B := B) :=
  Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap B (Localization.Away b)))

/-- **The two-patch glue datum of two affine schemes**, as a `CategoryTheory.GlueData'` on the
index type `ULift Bool`: the patches are `Spec A` and `Spec B`, the overlaps are the basic opens
`Spec A_a` and `Spec B_b`, the inclusions are `Spec` of the localizations and the transition is
`specGlueIso`. The three fields `t'`, `t_fac`, `cocycle` are vacuous because no triple of
`Bool`-indices is pairwise distinct. This mirrors `completionTwoPatchGlueData'` field for
field. -/
def specTwoPatchGlueData' : CategoryTheory.GlueData' LocallyRingedSpace.{u} where
  J := ULift.{u} Bool
  U := fun i => cond i.down (spU₁ (B := B)) (spU₀ (A := A))
  V := fun i _ _ => cond i.down (spV₁ b) (spV₀ a)
  f := fun i j h => match i, j, h with
    | ⟨false⟩, ⟨true⟩, _ => spF₀ a
    | ⟨true⟩, ⟨false⟩, _ => spF₁ b
    | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
    | ⟨true⟩, ⟨true⟩, h => (h rfl).elim
  f_mono := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ h
    · exact absurd rfl h
    · exact inferInstanceAs (Mono (spF₀ a))
    · exact inferInstanceAs (Mono (spF₁ b))
    · exact absurd rfl h
  f_hasPullback := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ ⟨_ | _⟩ hij hik
    · exact absurd rfl hij
    · exact absurd rfl hij
    · exact absurd rfl hik
    · exact inferInstanceAs (HasPullback (spF₀ a) (spF₀ a))
    · exact inferInstanceAs (HasPullback (spF₁ b) (spF₁ b))
    · exact absurd rfl hik
    · exact absurd rfl hij
    · exact absurd rfl hij
  t := fun i j h => match i, j, h with
    | ⟨false⟩, ⟨true⟩, _ => (specGlueIso a b θ).hom
    | ⟨true⟩, ⟨false⟩, _ => (specGlueIso a b θ).inv
    | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
    | ⟨true⟩, ⟨true⟩, h => (h rfl).elim
  t' := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim
  t_fac := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim
  t_inv := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ h
    · exact absurd rfl h
    · exact (specGlueIso a b θ).hom_inv_id
    · exact (specGlueIso a b θ).inv_hom_id
    · exact absurd rfl h
  cocycle := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim

/-- **The two-patch scheme glue datum as a `LocallyRingedSpace.GlueData`**: the full
`CategoryTheory.GlueData` produced by `GlueData.ofGlueData'`, together with the open-immersion
field `f_open`. Off the diagonal each glue map is `eqToHom ≫ (affine chart inclusion)`, a composite
of an isomorphism with an open immersion; on the diagonal it is `eqToHom`. -/
def specTwoPatchLRSGlueData : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' (specTwoPatchGlueData' a b θ) with
    f_open := by
      rintro i j
      simp only [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
        · exact absurd rfl h
        · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _ ≫ spF₀ a))
        · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _ ≫ spF₁ b))
        · exact absurd rfl h }

/-- **The glued two-patch scheme** `Spec A ∪_{D(a) ≅ D(b)} Spec B`, as a locally ringed space.
This is the ambient object of which `completionTwoPatch` is the completion. -/
def specTwoPatch : LocallyRingedSpace.{u} :=
  (specTwoPatchLRSGlueData a b θ).toGlueData.glued

/-- The chart `Spec A` as an open subspace of the glued scheme. -/
def specTwoPatchι₀ : Spec.locallyRingedSpaceObj (CommRingCat.of A) ⟶ specTwoPatch a b θ :=
  (specTwoPatchLRSGlueData a b θ).toGlueData.ι ⟨false⟩

/-- The chart `Spec B` as an open subspace of the glued scheme. -/
def specTwoPatchι₁ : Spec.locallyRingedSpaceObj (CommRingCat.of B) ⟶ specTwoPatch a b θ :=
  (specTwoPatchLRSGlueData a b θ).toGlueData.ι ⟨true⟩

instance specTwoPatchι₀_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (specTwoPatchι₀ a b θ) :=
  LocallyRingedSpace.GlueData.ι_isOpenImmersion _ _

instance specTwoPatchι₁_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (specTwoPatchι₁ a b θ) :=
  LocallyRingedSpace.GlueData.ι_isOpenImmersion _ _

/-- **The two charts cover the glued scheme.** -/
theorem specTwoPatch_jointly_surjective (x : specTwoPatch a b θ) :
    x ∈ Set.range (specTwoPatchι₀ a b θ).base ∪ Set.range (specTwoPatchι₁ a b θ).base := by
  obtain ⟨i, y, hy⟩ := (specTwoPatchLRSGlueData a b θ).ι_jointly_surjective x
  rcases i with ⟨_ | _⟩
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

private theorem spNe : ¬ @Eq (ULift.{u} Bool) ⟨false⟩ ⟨true⟩ := by simp

private theorem spNe' : ¬ @Eq (ULift.{u} Bool) ⟨true⟩ ⟨false⟩ := by simp

private theorem spGD_t :
    (specTwoPatchLRSGlueData a b θ).toGlueData.t ⟨false⟩ ⟨true⟩ =
      eqToHom (dif_neg spNe) ≫ (specGlueIso a b θ).hom ≫ eqToHom (dif_neg spNe').symm :=
  dif_neg spNe

private theorem spGD_f₀ :
    (specTwoPatchLRSGlueData a b θ).toGlueData.f ⟨false⟩ ⟨true⟩ =
      eqToHom (dif_neg spNe) ≫ spF₀ a :=
  dif_neg spNe

private theorem spGD_f₁ :
    (specTwoPatchLRSGlueData a b θ).toGlueData.f ⟨true⟩ ⟨false⟩ =
      eqToHom (dif_neg spNe') ≫ spF₁ b :=
  dif_neg spNe'

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- The same transparency requirement as in `FormalSchemes.Gluing`: the glue datum is a `def`, so
-- `(specTwoPatchLRSGlueData ..).J` does not reduce to `ULift Bool` at `instances` transparency and
-- the rewrites below are rejected as ill-typed without this.
/-- **The two affine charts of the glued scheme agree on the overlap**: including `Spec A_a` into
`Spec A` and then into the glued object is the same as transporting it to `Spec B_b` by `Spec θ`
and including that into `Spec B` and then into the glued object. This is the target-side input to
the overlap obligation of `completionTwoPatchToScheme`; it is the glue condition of
`specTwoPatchLRSGlueData` with the `GlueData.ofGlueData'` bookkeeping stripped. -/
theorem specTwoPatch_glue :
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫
        specTwoPatchι₀ a b θ =
      (specGlueIso a b θ).hom ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap B (Localization.Away b))) ≫
          specTwoPatchι₁ a b θ := by
  have h := (specTwoPatchLRSGlueData a b θ).toGlueData.glue_condition
    (⟨false⟩ : ULift.{u} Bool) ⟨true⟩
  rw [spGD_t, spGD_f₀, spGD_f₁] at h
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at h
  exact ((cancel_epi (eqToHom (dif_neg spNe))).mp h).symm

end Glued

section Morphism

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (hI : I.FG) (a : A)
  (J : Ideal B) (hJ : J.FG) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

/-- **The overlap compatibility, `A`-side**: the two per-chart morphisms into the glued scheme
agree over `D(a) ≅ D(b)`. This is the hypothesis of `FormalScheme.GlueData.glueMorphisms`, and it
is what `FormalSchemes/CompletionBasicOpenMap.lean` exists to supply.

Both sides reduce to `toSpec A_a (I·A_a) ≫ Spec θ.symm ≫ Spec (B → B_b) ≫ ι₁`. On the left,
`formalCompletion.basicOpenImmersion_comp_toSpec` turns the chart inclusion followed by `toSpec`
into `toSpec` on the overlap followed by `Spec` of the localization, and `specTwoPatch_glue` moves
the result across the overlap. On the right, the same lemma applies on the `B` side and
`formalCompletion.map_comp_toSpec` handles the transition isomorphism, which is
`formalCompletion.map` of `θ.symm`. -/
theorem completionTwoPatch_overlapCompat₀ :
    (formalCompletion.basicOpenImmersion I hI a).toLRSHom ≫
        (formalCompletion.toSpec A I hI ≫ specTwoPatchι₀ a b θ) =
      (completionGlueLRSIso I hI a J hJ b θ hθ).hom ≫
        (formalCompletion.basicOpenImmersion J hJ b).toLRSHom ≫
          (formalCompletion.toSpec B J hJ ≫ specTwoPatchι₁ a b θ) := by
  rw [← Category.assoc, formalCompletion.basicOpenImmersion_comp_toSpec,
    Category.assoc, specTwoPatch_glue]
  rw [← Category.assoc ((formalCompletion.basicOpenImmersion J hJ b).toLRSHom),
    formalCompletion.basicOpenImmersion_comp_toSpec]
  have hsymm : (J.map (algebraMap B (Localization.Away b))).map θ.symm.toRingHom =
      I.map (algebraMap A (Localization.Away a)) := by
    rw [← hθ, Ideal.map_map,
      show θ.symm.toRingHom.comp θ.toRingHom = RingHom.id _ from RingHom.ext θ.symm_apply_apply,
      Ideal.map_id]
  have hg : (completionGlueLRSIso I hI a J hJ b θ hθ).hom =
      (formalCompletion.map (hJ.map (algebraMap B (Localization.Away b)))
        (hI.map (algebraMap A (Localization.Away a))) θ.symm.toRingHom hsymm.le).toLRSHom := rfl
  rw [hg]
  simp only [Category.assoc]
  rw [reassoc_of% (formalCompletion.map_comp_toSpec
    (hJ.map (algebraMap B (Localization.Away b)))
    (hI.map (algebraMap A (Localization.Away a))) θ.symm.toRingHom hsymm.le)]
  rfl

/-- **The overlap compatibility, `B`-side.** The mirror image of
`completionTwoPatch_overlapCompat₀`, obtained from it by composing with the inverse of the overlap
identification. -/
theorem completionTwoPatch_overlapCompat₁ :
    (formalCompletion.basicOpenImmersion J hJ b).toLRSHom ≫
        (formalCompletion.toSpec B J hJ ≫ specTwoPatchι₁ a b θ) =
      (completionGlueLRSIso I hI a J hJ b θ hθ).inv ≫
        (formalCompletion.basicOpenImmersion I hI a).toLRSHom ≫
          (formalCompletion.toSpec A I hI ≫ specTwoPatchι₀ a b θ) := by
  rw [completionTwoPatch_overlapCompat₀ I hI a J hJ b θ hθ, Iso.inv_hom_id_assoc]

/-- **The canonical morphism from the glued completion to the glued scheme** (EGA I, 10.8):
`X_{/Y} ⟶ X` for the two-chart scheme `X = Spec A ∪_{D(a) ≅ D(b)} Spec B` completed along the
closed subset glued from `V(I)` and `V(J)`. It is the descent
(`AlgebraicGeometry.completionTwoPatchDesc`) of the two affine `formalCompletion.toSpec`s along the
overlap compatibility `completionTwoPatch_overlapCompat₀`. -/
def completionTwoPatchToScheme :
    (completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace ⟶ specTwoPatch a b θ :=
  completionTwoPatchDesc I hI a J hJ b θ hθ
    (formalCompletion.toSpec A I hI ≫ specTwoPatchι₀ a b θ)
    (formalCompletion.toSpec B J hJ ≫ specTwoPatchι₁ a b θ)
    (completionTwoPatch_overlapCompat₀ I hI a J hJ b θ hθ)

/-- **The canonical morphism is a descent**, definitionally. Stated so that the general results
about `completionTwoPatchDesc` — in particular
`AlgebraicGeometry.completionTwoPatchDesc_unique` — can be applied to it by rewriting rather than
by unfolding a `def`. -/
theorem completionTwoPatchToScheme_eq_desc :
    completionTwoPatchToScheme I hI a J hJ b θ hθ =
      completionTwoPatchDesc I hI a J hJ b θ hθ
        (formalCompletion.toSpec A I hI ≫ specTwoPatchι₀ a b θ)
        (formalCompletion.toSpec B J hJ ≫ specTwoPatchι₁ a b θ)
        (completionTwoPatch_overlapCompat₀ I hI a J hJ b θ hθ) :=
  rfl

/-- **The glued morphism restricts to the `A`-chart's `toSpec`.** Together with its `B`-side twin
this characterises `completionTwoPatchToScheme` chart by chart. -/
theorem completionTwoPatchι₀_comp_toScheme :
    completionTwoPatchι₀ I hI a J hJ b θ hθ ≫ completionTwoPatchToScheme I hI a J hJ b θ hθ =
      formalCompletion.toSpec A I hI ≫ specTwoPatchι₀ a b θ :=
  completionTwoPatchι₀_comp_desc I hI a J hJ b θ hθ _ _
    (completionTwoPatch_overlapCompat₀ I hI a J hJ b θ hθ)

/-- **The glued morphism restricts to the `B`-chart's `toSpec`.** -/
theorem completionTwoPatchι₁_comp_toScheme :
    completionTwoPatchι₁ I hI a J hJ b θ hθ ≫ completionTwoPatchToScheme I hI a J hJ b θ hθ =
      formalCompletion.toSpec B J hJ ≫ specTwoPatchι₁ a b θ :=
  completionTwoPatchι₁_comp_desc I hI a J hJ b θ hθ _ _
    (completionTwoPatch_overlapCompat₀ I hI a J hJ b θ hθ)

/-- **Uniqueness**: a morphism out of the glued completion is determined by its restrictions to
the two charts. With the two lemmas above this says `completionTwoPatchToScheme` is the *only*
morphism restricting to the affine `formalCompletion.toSpec`s. -/
theorem completionTwoPatch_hom_ext
    {g₁ g₂ : (completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace ⟶ specTwoPatch a b θ}
    (h₀ : completionTwoPatchι₀ I hI a J hJ b θ hθ ≫ g₁ =
      completionTwoPatchι₀ I hI a J hJ b θ hθ ≫ g₂)
    (h₁ : completionTwoPatchι₁ I hI a J hJ b θ hθ ≫ g₁ =
      completionTwoPatchι₁ I hI a J hJ b θ hθ ≫ g₂) :
    g₁ = g₂ :=
  (completionTwoPatchFormalGlueData I hI a J hJ b θ hθ).hom_ext (by
    rintro ⟨_ | _⟩
    · exact h₀
    · exact h₁)

/-- **The hypothesis stack is satisfiable.** Taking both charts to be the same `Spec R` completed
along the same `V(K)`, both overlap elements to be the same `f : R` and the overlap identification
to be the identity discharges every hypothesis at once, for an arbitrary `f`. Geometrically this
glues `Spec R` to itself along `D(f)`, so it is trivial as geometry; the point is that the glued
scheme, the glued completion and the morphism between them all exist. -/
example (R : Type u) [CommRing R] (K : Ideal R) (hK : K.FG) (f : R) :
    (completionTwoPatch K hK f K hK f (RingEquiv.refl _) (Ideal.map_id _)).toLocallyRingedSpace ⟶
      specTwoPatch f f (RingEquiv.refl _) :=
  completionTwoPatchToScheme K hK f K hK f (RingEquiv.refl _) (Ideal.map_id _)

end Morphism

end AlgebraicGeometry

end
