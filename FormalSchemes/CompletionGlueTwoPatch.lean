import FormalSchemes.CompletionBasicOpen
import FormalSchemes.Gluing

set_option linter.style.header false

/-!
# Gluing two affine formal completions along a common basic open (EGA I, 10.8)

Everything on master completes an *affine* scheme: `formalCompletion R I` is `Spf R^`, and the
basic-open charts `formalCompletion.basicOpenImmersion` exhibit the completions of the basic opens
`D(f) ⊆ Spec R` as open formal subschemes of it. This file assembles those local pieces into the
first `AlgebraicGeometry.FormalScheme.GlueData` of *completions*, and hence produces the first
formal scheme in this development that is the completion of a genuinely non-affine scheme.

The slice taken here is the two-patch one, on the index type `ULift Bool`. The input is a pair of
affine charts together with an identification of their overlap:

* rings `A`, `B` with finitely generated ideals `I : Ideal A`, `J : Ideal B` — the two affine
  charts of the scheme and the closed subsets one completes along;
* elements `a : A`, `b : B` cutting out the overlap `D(a) ⊆ Spec A`, `D(b) ⊆ Spec B`;
* a ring isomorphism `θ : A_a ≃+* B_b` identifying the two overlaps;
* the hypothesis `hθ : (I·A_a).map θ = J·B_b`, saying that the two closed subsets agree on the
  overlap. Without it the two completions would be unrelated and the glued object would not be a
  completion of anything; it is what makes the datum below the completion of a *scheme along a
  closed subset*.

Gluing the basic-open completions of a single affine `Spec A` back together only re-presents
`formalCompletion A I` — no longer an assertion: `AlgebraicGeometry.completionBasicOpenGluedIso`
(`FormalSchemes/CompletionBasicOpenGlue.lean`) proves it, for an arbitrary index type, whenever the
chosen elements generate the unit ideal. Two *different* charts glued along a common basic open is
the first
non-vacuous case, and it is exactly the chart-overlap situation
`FormalSchemes/CompletionNestedBasicOpen.lean` was built for — the overlaps of the affine charts of
a completion are again affine, sidestepping the non-affine-overlap obstruction to the general
gluing.

Because the index type has only **two** elements, no triple `(i, j, k)` of indices can be pairwise
distinct, so the `t'`, `t_fac` and `cocycle` fields of a `CategoryTheory.GlueData'` are vacuous
(`cpBool_not_pairwise_distinct`). That is what made this slice tractable first, and the same device
carries the Tate two-patch prototype (`FormalSchemes/TateGlueTwoPatch.lean`), whose shape this file
mirrors. Those three fields are discharged by genuine proofs, at an arbitrary index type, in
`FormalSchemes/CompletionBasicOpenGlue.lean`, over a single affine — the first *completion* glue
datum on this tree whose cocycle condition has content. (`FormalSchemes/ThreeChartDatum.lean`
discharges the analogous fields of an `AffineChartedFibreDatumX` on `ULift (Fin 3)`.)

## Main definitions and results

* `AlgebraicGeometry.completionGlueIso`: `Spf` of `θ`, as an isomorphism of formal schemes
  `formalCompletion A_a (I·A_a) ≅ formalCompletion B_b (J·B_b)` — the gluing datum on the overlap,
  built from the functoriality `formalCompletion.map` in both directions.
* `AlgebraicGeometry.completionGlueLRSIso`: the same isomorphism, on the underlying locally ringed
  spaces.
* `AlgebraicGeometry.completionTwoPatchGlueData'`: the `CategoryTheory.GlueData'`
  on `LocallyRingedSpace`, with the two completions as patches, their basic-open completions as
  overlaps, `formalCompletion.basicOpenImmersion` as the inclusions and `completionGlueLRSIso` as
  the transition.
* `AlgebraicGeometry.completionTwoPatchLRSGlueData`: the induced
  `AlgebraicGeometry.LocallyRingedSpace.GlueData`, via `CategoryTheory.GlueData.ofGlueData'`
  together with the open-immersion field `f_open`.
* `AlgebraicGeometry.completionTwoPatchFormalGlueData`: the
  `AlgebraicGeometry.FormalScheme.GlueData`, each patch being a formal completion, which is a
  formal scheme.
* `AlgebraicGeometry.completionTwoPatch`: the glued formal scheme, the completion of the two-chart
  scheme along its closed subset.
* `AlgebraicGeometry.completionTwoPatchι₀` / `..ι₁`: the two patches as open formal subschemes of
  the glued object, and `AlgebraicGeometry.completionTwoPatch_jointly_surjective`: they cover it.

## What this is a slice of

The triple-overlap `t'` this slice sidesteps is built, at an arbitrary index type and by an actual
cocycle proof, in `FormalSchemes/CompletionBasicOpenGlue.lean`; it consumes exactly the
overlap-as-fibre-product identifications `formalCompletion.basicOpenOverlapIso` and its two chart
compatibilities (`FormalSchemes/CompletionBasicOpenOverlap.lean`).

This paragraph used to continue *"what that file does not carry is the second ring and the overlap
identification `θ` of this one, so the two together — an arbitrary affine cover of an arbitrary
scheme, completed along a closed subset — remain the rest of EGA I, 10.8."* **The formal-scheme
half of that is already built, under a name from a different subject area.**
`AffineChartedFibreDatumX` (`FormalSchemes/GeneralFibreProductExposeX.lean`) glues adic charts
`Spf (A i)` at an arbitrary index, with chart algebras that genuinely differ and transitions
`τ i j : A_i{1/g_ij} ≃ₐ[R] A_j{1/g_ji}` — `τ` *is* the `θ` of this file — over a real triple
cocycle; its glued object is `AffineChartedFibreDatumX.xGlued`, and
`FormalSchemes/CompletionAsChartedGlued.lean` proves that the completion line's objects are
`xGlued`s.

That same section then named the glued *scheme* and the morphism `X_{/Y} ⟶ X` as what genuinely
remained of EGA I 10.8 at an arbitrary index. **Both are now built, and neither is here.** The
glued scheme is `AlgebraicGeometry.ChartedSchemeDatum.specGlued`
(`FormalSchemes.ChartedSchemeDatum`), the arbitrary-index analogue of `specTwoPatch`; the morphism
is `AlgebraicGeometry.ChartedCompletionDatum.toScheme`
(`FormalSchemes.ChartedCompletionToScheme`), the arbitrary-index analogue of
`completionTwoPatchToScheme` (`FormalSchemes/CompletionTwoPatchToScheme.lean`) generalising
`formalCompletion.toSpec` (`FormalSchemes/CompletionToSpec.lean`). Both take the localization data
this file's `θ` is an instance of, at an arbitrary index and over a triple overlap that is
genuinely inhabited.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (hI : I.FG) (a : A)
  (J : Ideal B) (hJ : J.FG) (b : B)

/-- An ideal identification along a ring isomorphism runs backwards along the inverse. -/
private theorem cpMap_symm_eq {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    {K : Ideal R} {L : Ideal S} (h : K.map e.toRingHom = L) :
    L.map e.symm.toRingHom = K := by
  rw [← h, Ideal.map_map,
    show e.symm.toRingHom.comp e.toRingHom = RingHom.id R from RingHom.ext e.symm_apply_apply,
    Ideal.map_id]

variable (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

/-- **The gluing isomorphism of the overlap**: an isomorphism of formal schemes
`formalCompletion A_a (I·A_a) ≅ formalCompletion B_b (J·B_b)`, namely `Spf` of the overlap
identification `θ`. Both legs are the completion functoriality `formalCompletion.map`, of `θ` and
of `θ.symm`; that they are mutually inverse is the functoriality of the completion
(`formalCompletion.map_comp`, `formalCompletion.map_id`) applied to `θ.symm ∘ θ = id` and
`θ ∘ θ.symm = id`. The ideal hypothesis `hθ` is what makes both legs adic. -/
def completionGlueIso :
    formalCompletion (Localization.Away a)
        (I.map (algebraMap A (Localization.Away a))) (hI.map _) ≅
      formalCompletion (Localization.Away b)
        (J.map (algebraMap B (Localization.Away b))) (hJ.map _) where
  hom := formalCompletion.map (hJ.map _) (hI.map _) θ.symm.toRingHom (cpMap_symm_eq θ hθ).le
  inv := formalCompletion.map (hI.map _) (hJ.map _) θ.toRingHom hθ.le
  hom_inv_id :=
    ((formalCompletion.map_comp (I.map (algebraMap A (Localization.Away a))) (hI.map _)
      (hJ.map _) (hI.map _) θ.toRingHom θ.symm.toRingHom hθ.le
      (cpMap_symm_eq θ hθ).le).symm.trans
        (formalCompletion.map_congr _ _ _ _
          (show θ.symm.toRingHom.comp θ.toRingHom = RingHom.id _ from
            RingHom.ext θ.symm_apply_apply))).trans
      (formalCompletion.map_id (I.map (algebraMap A (Localization.Away a))) (hI.map _))
  inv_hom_id :=
    ((formalCompletion.map_comp (J.map (algebraMap B (Localization.Away b))) (hJ.map _)
      (hI.map _) (hJ.map _) θ.symm.toRingHom θ.toRingHom (cpMap_symm_eq θ hθ).le
      hθ.le).symm.trans
        (formalCompletion.map_congr _ _ _ _
          (show θ.toRingHom.comp θ.symm.toRingHom = RingHom.id _ from
            RingHom.ext θ.apply_symm_apply))).trans
      (formalCompletion.map_id (J.map (algebraMap B (Localization.Away b))) (hJ.map _))

/-- **The gluing isomorphism of the overlap, on underlying locally ringed spaces.** Morphisms of
formal schemes are morphisms of locally ringed spaces, so this is `completionGlueIso` leg by leg;
the inverse laws transport along `FormalScheme.Hom.toLRSHom` because composition and identities in
`FormalScheme` are those of `LocallyRingedSpace`. -/
def completionGlueLRSIso :
    (formalCompletion (Localization.Away a)
        (I.map (algebraMap A (Localization.Away a))) (hI.map _)).toLocallyRingedSpace ≅
      (formalCompletion (Localization.Away b)
        (J.map (algebraMap B (Localization.Away b))) (hJ.map _)).toLocallyRingedSpace where
  hom := (completionGlueIso I hI a J hJ b θ hθ).hom.toLRSHom
  inv := (completionGlueIso I hI a J hJ b θ hθ).inv.toLRSHom
  hom_inv_id :=
    congrArg FormalScheme.Hom.toLRSHom (completionGlueIso I hI a J hJ b θ hθ).hom_inv_id
  inv_hom_id :=
    congrArg FormalScheme.Hom.toLRSHom (completionGlueIso I hI a J hJ b θ hθ).inv_hom_id

/-- The `A`-side patch `formalCompletion A I`, as a locally ringed space. -/
private abbrev cpU₀ : LocallyRingedSpace.{u} := (formalCompletion A I hI).toLocallyRingedSpace

/-- The `B`-side patch `formalCompletion B J`, as a locally ringed space. -/
private abbrev cpU₁ : LocallyRingedSpace.{u} := (formalCompletion B J hJ).toLocallyRingedSpace

/-- The `A`-side overlap `formalCompletion A_a (I·A_a)`, as a locally ringed space. -/
private abbrev cpV₀ : LocallyRingedSpace.{u} :=
  (formalCompletion (Localization.Away a)
    (I.map (algebraMap A (Localization.Away a))) (hI.map _)).toLocallyRingedSpace

/-- The `B`-side overlap `formalCompletion B_b (J·B_b)`, as a locally ringed space. -/
private abbrev cpV₁ : LocallyRingedSpace.{u} :=
  (formalCompletion (Localization.Away b)
    (J.map (algebraMap B (Localization.Away b))) (hJ.map _)).toLocallyRingedSpace

/-- On a two-element index type no triple is pairwise distinct: this discharges the vacuous
`t'`, `t_fac` and `cocycle` fields of the two-patch glue data. -/
private theorem cpBool_not_pairwise_distinct {i j k : ULift.{u} Bool}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : False := by
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  obtain ⟨k⟩ := k
  cases i <;> cases j <;> cases k <;> simp_all

/-- **The two-patch glue datum of two affine formal completions** (EGA I, 10.8), as a
`CategoryTheory.GlueData'` on the index type `ULift Bool`: the patches are the completions
`formalCompletion A I` and `formalCompletion B J`, the overlaps are their basic-open completions at
`a` and at `b`, the inclusions are the basic-open completion immersions
`formalCompletion.basicOpenImmersion`, and the transition is the overlap identification
`completionGlueLRSIso`. The three fields `t'`, `t_fac`, `cocycle` are vacuous because no triple of
`Bool`-indices is pairwise distinct. -/
def completionTwoPatchGlueData' : CategoryTheory.GlueData' LocallyRingedSpace.{u} where
  J := ULift.{u} Bool
  U := fun i => cond i.down (cpU₁ J hJ) (cpU₀ I hI)
  V := fun i _ _ => cond i.down (cpV₁ J hJ b) (cpV₀ I hI a)
  f := fun i j h => match i, j, h with
    | ⟨false⟩, ⟨true⟩, _ => (formalCompletion.basicOpenImmersion I hI a).toLRSHom
    | ⟨true⟩, ⟨false⟩, _ => (formalCompletion.basicOpenImmersion J hJ b).toLRSHom
    | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
    | ⟨true⟩, ⟨true⟩, h => (h rfl).elim
  f_mono := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ h
    · exact absurd rfl h
    · exact inferInstanceAs (Mono (formalCompletion.basicOpenImmersion I hI a).toLRSHom)
    · exact inferInstanceAs (Mono (formalCompletion.basicOpenImmersion J hJ b).toLRSHom)
    · exact absurd rfl h
  f_hasPullback := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ ⟨_ | _⟩ hij hik
    · exact absurd rfl hij
    · exact absurd rfl hij
    · exact absurd rfl hik
    · exact inferInstanceAs (HasPullback (formalCompletion.basicOpenImmersion I hI a).toLRSHom
        (formalCompletion.basicOpenImmersion I hI a).toLRSHom)
    · exact inferInstanceAs (HasPullback (formalCompletion.basicOpenImmersion J hJ b).toLRSHom
        (formalCompletion.basicOpenImmersion J hJ b).toLRSHom)
    · exact absurd rfl hik
    · exact absurd rfl hij
    · exact absurd rfl hij
  t := fun i j h => match i, j, h with
    | ⟨false⟩, ⟨true⟩, _ => (completionGlueLRSIso I hI a J hJ b θ hθ).hom
    | ⟨true⟩, ⟨false⟩, _ => (completionGlueLRSIso I hI a J hJ b θ hθ).inv
    | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
    | ⟨true⟩, ⟨true⟩, h => (h rfl).elim
  t' := fun _ _ _ hij hik hjk => (cpBool_not_pairwise_distinct hij hik hjk).elim
  t_fac := fun _ _ _ hij hik hjk => (cpBool_not_pairwise_distinct hij hik hjk).elim
  t_inv := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ h
    · exact absurd rfl h
    · exact (completionGlueLRSIso I hI a J hJ b θ hθ).hom_inv_id
    · exact (completionGlueLRSIso I hI a J hJ b θ hθ).inv_hom_id
    · exact absurd rfl h
  cocycle := fun _ _ _ hij hik hjk => (cpBool_not_pairwise_distinct hij hik hjk).elim

/-- **The two-patch completion glue datum as a `LocallyRingedSpace.GlueData`**: the full
`CategoryTheory.GlueData` produced by `GlueData.ofGlueData'`, together with the open-immersion
field `f_open`. Off the diagonal each glue map is `eqToHom ≫ (basic-open completion immersion)`, a
composite of an isomorphism with an open immersion; on the diagonal it is `eqToHom`, an
isomorphism. -/
def completionTwoPatchLRSGlueData : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' (completionTwoPatchGlueData' I hI a J hJ b θ hθ) with
    f_open := by
      rintro i j
      simp only [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
        · exact absurd rfl h
        · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
            (eqToHom _ ≫ (formalCompletion.basicOpenImmersion I hI a).toLRSHom))
        · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
            (eqToHom _ ≫ (formalCompletion.basicOpenImmersion J hJ b).toLRSHom))
        · exact absurd rfl h }

/-- **The two-patch completion glue datum as a `FormalScheme.GlueData`**: each patch is a formal
completion `formalCompletion _ _`, which is by construction the affine formal scheme
`Spf` of the completed ring, so the `isFormalScheme` field is witnessed by the patch itself. -/
def completionTwoPatchFormalGlueData : FormalScheme.GlueData.{u} where
  toLocallyRingedSpaceGlueData := completionTwoPatchLRSGlueData I hI a J hJ b θ hθ
  isFormalScheme := by
    rintro ⟨_ | _⟩
    · exact ⟨formalCompletion A I hI, ⟨Iso.refl _⟩⟩
    · exact ⟨formalCompletion B J hJ, ⟨Iso.refl _⟩⟩

/-- **The glued two-patch formal completion** (EGA I, 10.8): the formal scheme obtained by gluing
the completions of two affine charts along the completion of their common basic open. This is the
completion of the two-chart scheme `Spec A ∪_{D(a) ≅ D(b)} Spec B` along the closed subset glued
from `V(I)` and `V(J)`, and — unlike every formal completion on master before it — it is not
affine in general. -/
def completionTwoPatch : FormalScheme.{u} :=
  (completionTwoPatchFormalGlueData I hI a J hJ b θ hθ).gluedFormalScheme

/-- The `A`-side patch as an open formal subscheme of the glued completion. -/
def completionTwoPatchι₀ :
    (formalCompletion A I hI).toLocallyRingedSpace ⟶
      (completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace :=
  (completionTwoPatchFormalGlueData I hI a J hJ b θ hθ).ι ⟨false⟩

/-- The `B`-side patch as an open formal subscheme of the glued completion. -/
def completionTwoPatchι₁ :
    (formalCompletion B J hJ).toLocallyRingedSpace ⟶
      (completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace :=
  (completionTwoPatchFormalGlueData I hI a J hJ b θ hθ).ι ⟨true⟩

instance completionTwoPatchι₀_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (completionTwoPatchι₀ I hI a J hJ b θ hθ) :=
  FormalScheme.GlueData.ι_isOpenImmersion _ _

instance completionTwoPatchι₁_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (completionTwoPatchι₁ I hI a J hJ b θ hθ) :=
  FormalScheme.GlueData.ι_isOpenImmersion _ _

/-- **The two patches cover the glued completion**: every point of `completionTwoPatch` is in the
image of one of the two completions. Together with the two open-immersion instances this exhibits
the glued object as covered by two affine formal charts. -/
theorem completionTwoPatch_jointly_surjective
    (x : (completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace) :
    x ∈ Set.range (completionTwoPatchι₀ I hI a J hJ b θ hθ).base ∪
      Set.range (completionTwoPatchι₁ I hI a J hJ b θ hθ).base := by
  obtain ⟨i, y, hy⟩ :=
    (completionTwoPatchFormalGlueData I hI a J hJ b θ hθ).ι_jointly_surjective x
  rcases i with ⟨_ | _⟩
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

/-- **The hypothesis stack of the two-patch completion glue datum is satisfiable.** Taking both
charts to be the same `Spec R` completed along the same `V(K)`, both overlap elements to be the
same `f : R`, and the overlap identification to be the identity, every hypothesis is discharged
simultaneously and the glued formal scheme exists. Geometrically this glues `Spec R` to itself
along `D(f)` and recovers `formalCompletion R K`, so it is trivial as geometry; it is stated for
an arbitrary `f`, so it covers both the degenerate case `f = 1` and a non-unit `f`, where the
overlap `V`/`f` fields of the datum are not degenerate. -/
example (R : Type u) [CommRing R] (K : Ideal R) (hK : K.FG) (f : R) : FormalScheme.{u} :=
  completionTwoPatch K hK f K hK f (RingEquiv.refl _) (Ideal.map_id _)

end AlgebraicGeometry

end
