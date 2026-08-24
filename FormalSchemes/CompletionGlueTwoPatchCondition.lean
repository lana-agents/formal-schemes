import FormalSchemes.CompletionGlueTwoPatch
import FormalSchemes.GlueMorphisms

set_option linter.style.header false

/-!
# The two-patch completion's glue condition, and morphisms out of it (EGA I, 10.8)

`FormalSchemes/CompletionGlueTwoPatch.lean` builds `completionTwoPatch`, the formal scheme glued
from two affine formal completions `formalCompletion A I` and `formalCompletion B J` along the
identification `completionGlueLRSIso` of their basic-open completions at `a` and at `b`, together
with the two chart inclusions `completionTwoPatchι₀` and `completionTwoPatchι₁`. What it does not
say is **how those two charts overlap inside the glued object** — and without that relation nothing
can be defined *out of* `completionTwoPatch`, which is the direction every consumer needs (the
canonical morphism `X_{/Y} ⟶ X` of 10.8 is a morphism out of the completion).

This file supplies that relation and the descent principle it unlocks.

* The **glue condition**, `completionTwoPatch_glue_condition₀` / `..₁`: the two chart inclusions
  agree over the overlap, after the identification `completionGlueLRSIso`. This is
  `CategoryTheory.GlueData.glue_condition` at the two `ULift Bool` indices, unfolded through
  `CategoryTheory.GlueData.ofGlueData'` so that it reads in the completion vocabulary rather than
  in the implementation's `eqToHom`-decorated `GlueData'.f'`.
* The **descent**, `completionTwoPatchDesc`: a pair of morphisms out of the two charts that agree
  over the overlap glues to a single morphism out of `completionTwoPatch`, restricting to the given
  pair on each chart (`completionTwoPatchι₀_comp_desc`, `..ι₁_comp_desc`) and being the only such
  morphism (`completionTwoPatchDesc_unique`).

The four unfolding lemmas `completionTwoPatchFormalGlueData_f_false_true` and friends are stated
publicly rather than kept private, because they are the dictionary between the constructed glue
data and the completion vocabulary, and anything else reasoning about `completionTwoPatch` needs
the same translation.

## The `⟨false⟩ = A`, `⟨true⟩ = B` convention

The index type is `ULift Bool`, with `⟨false⟩` the `A`-side chart and `⟨true⟩` the `B`-side one, as
in `CompletionGlueTwoPatch.lean`. The datum is **not** symmetric — the two patches are different
rings — so each statement below is given at both index pairs rather than parametrised over a
`b : Bool`. The `₁`-orientations follow from the `₀`-ones by cancelling the overlap isomorphism, so
only the `₀`-orientations pay for the `ofGlueData'` unfolding.

## Main definitions and results

* `completionTwoPatchFormalGlueData_f_false_true` and its three siblings: the constructed glue
  maps and transitions in terms of `formalCompletion.basicOpenImmersion` and
  `completionGlueLRSIso`.
* `completionTwoPatch_glue_condition₀`, `completionTwoPatch_glue_condition₁`: the glued object is
  glued — the two charts agree over the overlap.
* `completionTwoPatchDesc`: a morphism out of the glued completion from a compatible pair.
* `completionTwoPatchι₀_comp_desc`, `completionTwoPatchι₁_comp_desc`,
  `completionTwoPatchDesc_unique`: it is characterised chart by chart.
* `completionTwoPatchDesc_ι`: descending the two chart inclusions themselves gives the identity.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (hI : I.FG) (a : A)
  (J : Ideal B) (hJ : J.FG) (b : B) (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

/-- The two indices of the two-patch datum are distinct. Stated with the index type ascribed: the
`dite`s of `CategoryTheory.GlueData'.f'` live at `ULift Bool`, and `dif_neg` will not fire against
a disequality elaborated at `Bool`. -/
private theorem cgcNe : ¬ @Eq (ULift.{u} Bool) ⟨false⟩ ⟨true⟩ := by simp

/-- The two indices of the two-patch datum are distinct, the other way round. -/
private theorem cgcNe' : ¬ @Eq (ULift.{u} Bool) ⟨true⟩ ⟨false⟩ := by simp

/-- **The `A`-side glue map of the two-patch completion datum** is the `A`-side basic-open
completion immersion, up to the transport `GlueData.ofGlueData'` inserts because its `V` is a
`dite`. Off the diagonal that transport is `eqToHom (dif_neg _)`, so this is `dif_neg` itself. -/
theorem completionTwoPatchFormalGlueData_f_false_true :
    (completionTwoPatchFormalGlueData I hI a J hJ b θ
      hθ).toLocallyRingedSpaceGlueData.toGlueData.f ⟨false⟩ ⟨true⟩ =
      eqToHom (dif_neg cgcNe) ≫ (formalCompletion.basicOpenImmersion I hI a).toLRSHom :=
  dif_neg cgcNe

/-- **The `B`-side glue map of the two-patch completion datum** is the `B`-side basic-open
completion immersion, up to the same transport. -/
theorem completionTwoPatchFormalGlueData_f_true_false :
    (completionTwoPatchFormalGlueData I hI a J hJ b θ
      hθ).toLocallyRingedSpaceGlueData.toGlueData.f ⟨true⟩ ⟨false⟩ =
      eqToHom (dif_neg cgcNe') ≫ (formalCompletion.basicOpenImmersion J hJ b).toLRSHom :=
  dif_neg cgcNe'

/-- **The transition of the two-patch completion datum, `A` to `B`**, is the overlap identification
`completionGlueLRSIso`, conjugated by the two transports. -/
theorem completionTwoPatchFormalGlueData_t_false_true :
    (completionTwoPatchFormalGlueData I hI a J hJ b θ
      hθ).toLocallyRingedSpaceGlueData.toGlueData.t ⟨false⟩ ⟨true⟩ =
      eqToHom (dif_neg cgcNe) ≫ (completionGlueLRSIso I hI a J hJ b θ hθ).hom ≫
        eqToHom (dif_neg cgcNe').symm :=
  dif_neg cgcNe

/-- **The transition of the two-patch completion datum, `B` to `A`**, is the inverse of the overlap
identification, conjugated the other way. -/
theorem completionTwoPatchFormalGlueData_t_true_false :
    (completionTwoPatchFormalGlueData I hI a J hJ b θ
      hθ).toLocallyRingedSpaceGlueData.toGlueData.t ⟨true⟩ ⟨false⟩ =
      eqToHom (dif_neg cgcNe') ≫ (completionGlueLRSIso I hI a J hJ b θ hθ).inv ≫
        eqToHom (dif_neg cgcNe).symm :=
  dif_neg cgcNe'

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- The index type of the constructed glue data is
-- `(completionTwoPatchFormalGlueData ..).toLocallyRingedSpaceGlueData.J`, which reduces to
-- `ULift Bool` only by unfolding the three `def`s `completionTwoPatchFormalGlueData`,
-- `completionTwoPatchLRSGlueData` and `completionTwoPatchGlueData'` — past `instances`
-- transparency. Rewriting with the unfolding lemmas above therefore leaves a term Lean will not
-- re-typecheck at that level. Same requirement as in `FormalScheme.GlueData.gluedFormalScheme`.
/-- **The two charts of the glued completion agree over their overlap** (EGA I, 10.8): including the
overlap `formalCompletion A_a (I·A_a)` into the `A`-chart and then into the glued completion is the
same as identifying it with `formalCompletion B_b (J·B_b)` along `completionGlueLRSIso`, including
that into the `B`-chart, and then into the glued completion.

This is the relation that makes `completionTwoPatch` usable: it is exactly the hypothesis of
`FormalScheme.GlueData.glueMorphisms`, so with it in hand morphisms out of the glued completion can
be defined (`completionTwoPatchDesc` below). It is `CategoryTheory.GlueData.glue_condition` at
`(⟨false⟩, ⟨true⟩)`, with the `GlueData.ofGlueData'` transports cancelled off both sides. -/
theorem completionTwoPatch_glue_condition₀ :
    (completionGlueLRSIso I hI a J hJ b θ hθ).hom ≫
        (formalCompletion.basicOpenImmersion J hJ b).toLRSHom ≫
          completionTwoPatchι₁ I hI a J hJ b θ hθ =
      (formalCompletion.basicOpenImmersion I hI a).toLRSHom ≫
        completionTwoPatchι₀ I hI a J hJ b θ hθ := by
  have key := (completionTwoPatchFormalGlueData I hI a J hJ b θ
    hθ).toLocallyRingedSpaceGlueData.toGlueData.glue_condition ⟨false⟩ ⟨true⟩
  rw [completionTwoPatchFormalGlueData_t_false_true,
    completionTwoPatchFormalGlueData_f_true_false,
    completionTwoPatchFormalGlueData_f_false_true] at key
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  exact (cancel_epi (eqToHom (dif_neg cgcNe))).mp key

/-- **The two charts of the glued completion agree over their overlap, read from the `B` side.**
This is `completionTwoPatch_glue_condition₀` with the overlap isomorphism moved across, so it needs
none of the `ofGlueData'` bookkeeping. -/
theorem completionTwoPatch_glue_condition₁ :
    (completionGlueLRSIso I hI a J hJ b θ hθ).inv ≫
        (formalCompletion.basicOpenImmersion I hI a).toLRSHom ≫
          completionTwoPatchι₀ I hI a J hJ b θ hθ =
      (formalCompletion.basicOpenImmersion J hJ b).toLRSHom ≫
        completionTwoPatchι₁ I hI a J hJ b θ hθ := by
  rw [← completionTwoPatch_glue_condition₀ I hI a J hJ b θ hθ, Iso.inv_hom_id_assoc]

section Desc

variable {Y : LocallyRingedSpace.{u}}

/-- The per-chart family a compatible pair of morphisms out of the two charts assembles into: the
input to `FormalScheme.GlueData.glueMorphisms`, whose target type is stated in terms of the
constructed glue data's `U`. -/
private def cgcK (k₀ : (formalCompletion A I hI).toLocallyRingedSpace ⟶ Y)
    (k₁ : (formalCompletion B J hJ).toLocallyRingedSpace ⟶ Y) (i : ULift.{u} Bool) :
    (completionTwoPatchFormalGlueData I hI a J hJ b θ
      hθ).toLocallyRingedSpaceGlueData.toGlueData.U i ⟶ Y :=
  match i with
  | ⟨false⟩ => k₀
  | ⟨true⟩ => k₁

private theorem cgcK_false (k₀ : (formalCompletion A I hI).toLocallyRingedSpace ⟶ Y)
    (k₁ : (formalCompletion B J hJ).toLocallyRingedSpace ⟶ Y) :
    cgcK I hI a J hJ b θ hθ k₀ k₁ ⟨false⟩ = k₀ := rfl

private theorem cgcK_true (k₀ : (formalCompletion A I hI).toLocallyRingedSpace ⟶ Y)
    (k₁ : (formalCompletion B J hJ).toLocallyRingedSpace ⟶ Y) :
    cgcK I hI a J hJ b θ hθ k₀ k₁ ⟨true⟩ = k₁ := rfl

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- Same transparency requirement as in `completionTwoPatch_glue_condition₀` above, for the same
-- reason: the obligation is quantified over the constructed glue data's own index type.
/-- **Descent of a morphism out of the glued completion** (EGA I, 10.8): a morphism `k₀` out of the
`A`-chart and a morphism `k₁` out of the `B`-chart which agree over the overlap glue to a single
morphism out of `completionTwoPatch`.

This is `FormalScheme.GlueData.glueMorphisms` with its obligation discharged. That obligation is
quantified over all four index pairs and stated in terms of the constructed glue data: on the
diagonal it collapses because `CategoryTheory.GlueData.t_id` makes the transition the identity, and
off the diagonal the two cases are `hk` and `hk` read backwards through the overlap isomorphism.

Since `completionTwoPatch` is not affine in general, this is the general way to produce a morphism
out of it; the canonical `X_{/Y} ⟶ X` of 10.8 for a two-chart scheme is the instance where `k₀` and
`k₁` are the affine `formalCompletion.toSpec`s composed with the charts of the glued target, and
`hk` comes from `formalCompletion.basicOpenImmersion_comp_toSpec`. -/
def completionTwoPatchDesc (k₀ : (formalCompletion A I hI).toLocallyRingedSpace ⟶ Y)
    (k₁ : (formalCompletion B J hJ).toLocallyRingedSpace ⟶ Y)
    (hk : (formalCompletion.basicOpenImmersion I hI a).toLRSHom ≫ k₀ =
      (completionGlueLRSIso I hI a J hJ b θ hθ).hom ≫
        (formalCompletion.basicOpenImmersion J hJ b).toLRSHom ≫ k₁) :
    (completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace ⟶ Y :=
  (completionTwoPatchFormalGlueData I hI a J hJ b θ hθ).glueMorphisms
    (cgcK I hI a J hJ b θ hθ k₀ k₁) (by
      intro i j
      by_cases hij : i = j
      · subst hij
        simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
      · rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
        · exact absurd rfl hij
        · rw [completionTwoPatchFormalGlueData_f_false_true,
            completionTwoPatchFormalGlueData_t_false_true,
            completionTwoPatchFormalGlueData_f_true_false, cgcK_false, cgcK_true]
          simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          exact congrArg _ hk
        · rw [completionTwoPatchFormalGlueData_f_true_false,
            completionTwoPatchFormalGlueData_t_true_false,
            completionTwoPatchFormalGlueData_f_false_true, cgcK_false, cgcK_true]
          simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          exact congrArg _ (by rw [hk, Iso.inv_hom_id_assoc])
        · exact absurd rfl hij)

variable (k₀ : (formalCompletion A I hI).toLocallyRingedSpace ⟶ Y)
  (k₁ : (formalCompletion B J hJ).toLocallyRingedSpace ⟶ Y)
  (hk : (formalCompletion.basicOpenImmersion I hI a).toLRSHom ≫ k₀ =
    (completionGlueLRSIso I hI a J hJ b θ hθ).hom ≫
      (formalCompletion.basicOpenImmersion J hJ b).toLRSHom ≫ k₁)

/-- **The descended morphism restricts to `k₀` on the `A`-chart.** -/
theorem completionTwoPatchι₀_comp_desc :
    completionTwoPatchι₀ I hI a J hJ b θ hθ ≫
        completionTwoPatchDesc I hI a J hJ b θ hθ k₀ k₁ hk = k₀ :=
  (completionTwoPatchFormalGlueData I hI a J hJ b θ hθ).ι_glueMorphisms _ _ ⟨false⟩

/-- **The descended morphism restricts to `k₁` on the `B`-chart.** -/
theorem completionTwoPatchι₁_comp_desc :
    completionTwoPatchι₁ I hI a J hJ b θ hθ ≫
        completionTwoPatchDesc I hI a J hJ b θ hθ k₀ k₁ hk = k₁ :=
  (completionTwoPatchFormalGlueData I hI a J hJ b θ hθ).ι_glueMorphisms _ _ ⟨true⟩

/-- **The descended morphism is the only one with those restrictions**: the two charts cover the
glued completion, so a morphism out of it is determined by what it does on each. Together with the
two lemmas above this says `completionTwoPatchDesc k₀ k₁ hk` *is* the morphism restricting to `k₀`
and `k₁`. -/
theorem completionTwoPatchDesc_unique
    (g : (completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace ⟶ Y)
    (h₀ : completionTwoPatchι₀ I hI a J hJ b θ hθ ≫ g = k₀)
    (h₁ : completionTwoPatchι₁ I hI a J hJ b θ hθ ≫ g = k₁) :
    g = completionTwoPatchDesc I hI a J hJ b θ hθ k₀ k₁ hk :=
  (completionTwoPatchFormalGlueData I hI a J hJ b θ hθ).hom_ext (by
    rintro ⟨_ | _⟩
    · exact h₀.trans (completionTwoPatchι₀_comp_desc I hI a J hJ b θ hθ k₀ k₁ hk).symm
    · exact h₁.trans (completionTwoPatchι₁_comp_desc I hI a J hJ b θ hθ k₀ k₁ hk).symm)

end Desc

/-- **Descending the two chart inclusions themselves gives the identity.** The compatible pair is
the glue condition, so this needs no input beyond the two results above — and it exhibits
`completionTwoPatchDesc` as non-vacuous for arbitrary `A`, `B`, `I`, `J`, `a`, `b`, `θ`, not only
at a degenerate gluing. -/
theorem completionTwoPatchDesc_ι :
    completionTwoPatchDesc I hI a J hJ b θ hθ (completionTwoPatchι₀ I hI a J hJ b θ hθ)
        (completionTwoPatchι₁ I hI a J hJ b θ hθ)
        (completionTwoPatch_glue_condition₀ I hI a J hJ b θ hθ).symm =
      𝟙 (completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace :=
  (completionTwoPatchDesc_unique I hI a J hJ b θ hθ _ _ _ (𝟙 _)
    (Category.comp_id _) (Category.comp_id _)).symm

/-- **The hypothesis stack of the descent is satisfiable at a concrete gluing, with a target other
than the glued object itself.** Gluing `Spec R` completed along `V(K)` to itself along `D(f)` — the
witness `CompletionGlueTwoPatch.lean` already provides — the overlap identification is the identity
(`formalCompletion.map_id`), so the two identity morphisms are a compatible pair and the descent
retracts the gluing onto the single chart. -/
example (R : Type u) [CommRing R] (K : Ideal R) (hK : K.FG) (f : R) :
    (completionTwoPatch K hK f K hK f (RingEquiv.refl _) (Ideal.map_id _)).toLocallyRingedSpace ⟶
      (formalCompletion R K hK).toLocallyRingedSpace :=
  completionTwoPatchDesc K hK f K hK f (RingEquiv.refl _) (Ideal.map_id _) (𝟙 _) (𝟙 _) (by
    have h : (completionGlueLRSIso K hK f K hK f (RingEquiv.refl _) (Ideal.map_id _)).hom =
        𝟙 (formalCompletion (Localization.Away f)
          (K.map (algebraMap R (Localization.Away f))) (hK.map _)).toLocallyRingedSpace :=
      congrArg FormalScheme.Hom.toLRSHom
        (formalCompletion.map_id (K.map (algebraMap R (Localization.Away f))) (hK.map _))
    rw [h, Category.id_comp])

end AlgebraicGeometry

end
