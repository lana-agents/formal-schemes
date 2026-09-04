import FormalSchemes.CompletionTwoPatchClosed
import FormalSchemes.OpenImmersionIsoOfRangeEq

set_option linter.style.header false

/-!
# The completion of the two-patch scheme is a closed embedding (EGA I, 10.8)

For the two-patch glued scheme `X = Spec A ∪_{D(a) ≅ D(b)} Spec B` and its formal completion
`X_{/Y}` along the closed subset `Y` glued from `V(I)` and `V(J)`, this file proves that the
canonical morphism `X_{/Y} ⟶ X` is a **closed embedding on underlying spaces**.

That is the statement EGA I 10.8 makes, and `FormalSchemes/CompletionToSpec.lean` has had it for
**affine** `X` since the beginning, as `formalCompletion.isClosedEmbedding_toSpec_base`. Nothing
between the two existed until now: `FormalSchemes/CompletionTwoPatchRange.lean` computed the
image, `FormalSchemes/CompletionTwoPatchSupport.lean` read it chart by chart, and
`FormalSchemes/CompletionTwoPatchClosed.lean` showed it is closed — but none of them says the map
is injective, let alone a homeomorphism onto that image. This file does, for the first non-affine
`X` in this development.

## The argument

`Topology.IsClosedEmbedding` is `Topology.IsEmbedding` together with a closed range, and the
closed range is already available (`isClosed_range_completionTwoPatchToScheme_base`). So the whole
content is `Topology.IsEmbedding`, and it is obtained from
`Topology.isEmbedding_of_iSup_eq_top_of_preimage_subset_range` rather than by proving injectivity
and the inducing property separately. That lemma asks for

* an open cover `U` of the **target** — here the two chart ranges of `specTwoPatch`, open because
  the charts are open immersions and covering by `specTwoPatch_jointly_surjective`;
* a family of maps into the **source** whose ranges cover the corresponding preimages — here the
  two chart maps of `completionTwoPatch`; that the preimage of the `A`-chart of `X` lies in the
  `A`-chart of `X_{/Y}` is `preimage_range_specTwoPatchι₀_subset` below;
* and that each composite is an embedding — here an open embedding after a closed embedding,
  because `X_{/Y} ⟶ X` restricted to a chart *is* the affine `formalCompletion.toSpec`
  (`completionTwoPatchToScheme_base_ι₀`).

Injectivity is then `.injective` of the result, and never has to be proved by hand. This matters:
the mixed-chart case — two points in *different* charts of `X_{/Y}` with the same image in `X` —
is the only hard one, and the covering lemma discharges it as part of the same bookkeeping that
handles the cover.

The two chart preimages, which are what the covering lemma really needs, are the interesting step
and they run: a point of `X_{/Y}` lying over the `A`-chart of `X` is either already in the
`A`-chart of `X_{/Y}`, or it is in the `B`-chart, in which case its image in `Spec B` lies in
`D(b)` (`preimage_range_specTwoPatchι₀`), so the point itself lies in the completed basic open
`D(b̂)` (`formalCompletion.mem_range_basicOpenImmersion`), and the glue condition
(`completionTwoPatch_glue_condition₁`) carries it over into the `A`-chart.

`formalCompletion.mem_range_basicOpenImmersion` is the converse of
`formalCompletion.notMem_range_basicOpenImmersion`, and both are one line off the shared
`formalCompletion.mem_range_basicOpenImmersion_iff` in `FormalSchemes.CompletionBasicOpenMap`,
which is where the basic-open immersion first meets `formalCompletion.toSpec`. That iff is
available at all because `formalCompletion.range_basicOpenImmersion` computes the range of the
immersion **exactly**, as `D(f̂)`.

## Non-vacuity

`Topology.IsClosedEmbedding` of a map out of an empty space is trivially true, and a closed
embedding onto the whole space says nothing, so two things are recorded. The hypothesis stack is
satisfiable, in this cluster's usual idiom — gluing `Spec R` to itself along `D(f)`, for arbitrary
`K` and `f` — and `not_surjective_completionTwoPatchToScheme_base` says the closed subset is
**proper** as soon as `Spec A` has a prime containing `a` but not `I`.

That last statement is general rather than an instance on purpose. The concrete geometry in which
the image is neither `∅` nor everything — `𝔸¹_ℚ` doubled along `D(X)` and completed at the point
`1` on each chart — is in `FormalSchemes/CompletionTwoPatchClosed.lean`'s witness section, which
exhibits both halves: the image contains the centre of the completion and misses the origin. The
`ℚ[X]` scaffolding it runs on is `FormalSchemes/TwoPatchWitness.lean`, shared with
`FormalSchemes/CompletionTwoPatchRange.lean`, `FormalSchemes/CompletionTwoPatchSupport.lean` and
`FormalSchemes/SpecTwoPatchNonAffine.lean`; see the scope note below.

## Scope

**The scheme-theoretic closed immersion is not attempted here.** Everything in this file is about
underlying topological spaces. A closed immersion additionally asks for surjectivity of the map of
structure sheaves on stalks, and `AlgebraicGeometry.FormalScheme.IsClosedImmersion`
(`FormalSchemes.ClosedImmersion`) is a predicate on morphisms of *formal* schemes, whose target
here is an honest scheme — so that predicate does not apply.

**That is a fact about the predicate and not about the question**, which needs no packaging to be
asked: both conjuncts are statements about a morphism of `AlgebraicGeometry.LocallyRingedSpace`,
which `completionTwoPatchToScheme` is. At the affine index the conjunction is written out as
`formalCompletion.IsClosedImmersionToSpec` (`FormalSchemes.CompletionToSpecStalk`), where
`formalCompletion.toStalk_comp_stalkMap_toSpec` computes the stalk map on the image of
`AlgebraicGeometry.StructureSheaf.toStalk` and
`formalCompletion.isClosedImmersionToSpec_iff_surjective_stalkMap` records that the topological
half is free. Whether it holds is open there and is not expected to hold in general; the two-patch
form of the question is not written down anywhere yet.

**No `ℚ[X]` witness is used here, deliberately.** `not_surjective_completionTwoPatchToScheme_base`
states properness of the closed subset for an arbitrary two-patch datum, which is stronger than an
instance would be, so this file needs nothing from `FormalSchemes/TwoPatchWitness.lean` and does
not import it.

Also out of scope: the arbitrary-index completion glue datum, the universal property of the
completion, and the stalk half of 10.8.

## Main results

* `AlgebraicGeometry.preimage_range_specTwoPatchι₀_subset` and `..._ι₁_subset`: **a point of
  `X_{/Y}` lying over a chart of `X` is in the corresponding chart of `X_{/Y}`.**
* `AlgebraicGeometry.isEmbedding_completionTwoPatchToScheme_base`,
  `AlgebraicGeometry.isClosedEmbedding_completionTwoPatchToScheme_base` and
  `AlgebraicGeometry.injective_completionTwoPatchToScheme_base`: **`X_{/Y} ⟶ X` is a closed
  embedding**, and in particular injective.
* `AlgebraicGeometry.not_surjective_completionTwoPatchToScheme_base`: and the closed subset it
  embeds onto is proper.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

section Embedding

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (hI : I.FG) (a : A)
  (J : Ideal B) (hJ : J.FG) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

include hθ

/-! ### The overlap of the glued completion, seen from either chart -/

/-- **The `B`-chart of the glued completion, restricted to the overlap, lands in the `A`-chart.**
This is `completionTwoPatch_glue_condition₁` evaluated at a point; it is that glue condition's
first point-level consumer. -/
theorem completionTwoPatchι₁_base_basicOpenImmersion_mem_range
    (w : (formalCompletion (Localization.Away b)
      (J.map (algebraMap B (Localization.Away b))) (hJ.map _)).toLocallyRingedSpace) :
    (completionTwoPatchι₁ I hI a J hJ b θ hθ).base
        ((formalCompletion.basicOpenImmersion J hJ b).toLRSHom.base w) ∈
      Set.range (completionTwoPatchι₀ I hI a J hJ b θ hθ).base := by
  refine ⟨(formalCompletion.basicOpenImmersion I hI a).toLRSHom.base
    ((completionGlueLRSIso I hI a J hJ b θ hθ).inv.base w), ?_⟩
  have h := congrArg (fun m : (formalCompletion (Localization.Away b)
      (J.map (algebraMap B (Localization.Away b))) (hJ.map _)).toLocallyRingedSpace ⟶
      (completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace => m.base w)
    (completionTwoPatch_glue_condition₁ I hI a J hJ b θ hθ)
  simpa only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
    Function.comp_apply] using h

/-- **The `A`-chart of the glued completion, restricted to the overlap, lands in the `B`-chart.**
This is `completionTwoPatch_glue_condition₀` evaluated at a point. -/
theorem completionTwoPatchι₀_base_basicOpenImmersion_mem_range
    (w : (formalCompletion (Localization.Away a)
      (I.map (algebraMap A (Localization.Away a))) (hI.map _)).toLocallyRingedSpace) :
    (completionTwoPatchι₀ I hI a J hJ b θ hθ).base
        ((formalCompletion.basicOpenImmersion I hI a).toLRSHom.base w) ∈
      Set.range (completionTwoPatchι₁ I hI a J hJ b θ hθ).base := by
  refine ⟨(formalCompletion.basicOpenImmersion J hJ b).toLRSHom.base
    ((completionGlueLRSIso I hI a J hJ b θ hθ).hom.base w), ?_⟩
  have h := congrArg (fun m : (formalCompletion (Localization.Away a)
      (I.map (algebraMap A (Localization.Away a))) (hI.map _)).toLocallyRingedSpace ⟶
      (completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace => m.base w)
    (completionTwoPatch_glue_condition₀ I hI a J hJ b θ hθ)
  simpa only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
    Function.comp_apply] using h

/-! ### The chart preimages of `X_{/Y} ⟶ X` -/

/-- **A point of `X_{/Y}` lying over the `A`-chart of `X` is in the `A`-chart of `X_{/Y}`.** The
`B`-chart case goes through `preimage_range_specTwoPatchι₀` — its image in `Spec B` lies in `D(b)`
— then through `formalCompletion.mem_range_basicOpenImmersion` and the glue condition. -/
theorem preimage_range_specTwoPatchι₀_subset :
    ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base ⁻¹'
        Set.range ⇑(specTwoPatchι₀ a b θ).base ⊆
      Set.range ⇑(completionTwoPatchι₀ I hI a J hJ b θ hθ).base := by
  intro u hu
  rcases completionTwoPatch_jointly_surjective I hI a J hJ b θ hθ u with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact ⟨x, rfl⟩
  · rw [Set.mem_preimage, completionTwoPatchToScheme_base_ι₁ I hI a J hJ b θ hθ] at hu
    have hb : (formalCompletion.toSpec B J hJ).base y ∈
        (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) := by
      rw [← preimage_range_specTwoPatchι₀ a b θ]
      exact hu
    obtain ⟨w, hw⟩ := formalCompletion.mem_range_basicOpenImmersion J hJ b y
      ((PrimeSpectrum.mem_basicOpen b _).mp hb)
    rw [← hw]
    exact completionTwoPatchι₁_base_basicOpenImmersion_mem_range I hI a J hJ b θ hθ w

/-- **A point of `X_{/Y}` lying over the `B`-chart of `X` is in the `B`-chart of `X_{/Y}`.** -/
theorem preimage_range_specTwoPatchι₁_subset :
    ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base ⁻¹'
        Set.range ⇑(specTwoPatchι₁ a b θ).base ⊆
      Set.range ⇑(completionTwoPatchι₁ I hI a J hJ b θ hθ).base := by
  intro u hu
  rcases completionTwoPatch_jointly_surjective I hI a J hJ b θ hθ u with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · rw [Set.mem_preimage, completionTwoPatchToScheme_base_ι₀ I hI a J hJ b θ hθ] at hu
    have ha : (formalCompletion.toSpec A I hI).base x ∈
        (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
      rw [← preimage_range_specTwoPatchι₁ a b θ]
      exact hu
    obtain ⟨w, hw⟩ := formalCompletion.mem_range_basicOpenImmersion I hI a x
      ((PrimeSpectrum.mem_basicOpen a _).mp ha)
    rw [← hw]
    exact completionTwoPatchι₀_base_basicOpenImmersion_mem_range I hI a J hJ b θ hθ w
  · exact ⟨y, rfl⟩

/-! ### The two-chart data, and the closed embedding

`isEmbedding_of_iSup_eq_top_of_preimage_subset_range` wants a family of *types* indexed by the
cover, so the two charts have to be presented as a genuinely dependent `Bool`-indexed family. -/

omit hθ in
/-- The two affine formal charts of `X_{/Y}`, as a `Bool`-indexed family of types. -/
private def cChart : Bool → Type u
  | false => ↥(formalCompletion A I hI).toLocallyRingedSpace
  | true => ↥(formalCompletion B J hJ).toLocallyRingedSpace

omit hθ in
private instance cChartTopologicalSpace (i : Bool) :
    TopologicalSpace (cChart I hI J hJ i) := by
  cases i
  · exact inferInstanceAs (TopologicalSpace ↥(formalCompletion A I hI).toLocallyRingedSpace)
  · exact inferInstanceAs (TopologicalSpace ↥(formalCompletion B J hJ).toLocallyRingedSpace)

/-- The two chart maps of `X_{/Y}`, as a family over `cChart`. -/
private def cChartι : ∀ i : Bool, cChart I hI J hJ i →
    ↥(completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace
  | false => ⇑(completionTwoPatchι₀ I hI a J hJ b θ hθ).base
  | true => ⇑(completionTwoPatchι₁ I hI a J hJ b θ hθ).base

omit hθ in
/-- The two chart ranges of `X`, as opens: the open cover the embedding criterion runs over. -/
private def cU : Bool → Opens ↥(specTwoPatch a b θ)
  | false => LocallyRingedSpace.IsOpenImmersion.opensRange (specTwoPatchι₀ a b θ)
  | true => LocallyRingedSpace.IsOpenImmersion.opensRange (specTwoPatchι₁ a b θ)

/-- **The canonical morphism `X_{/Y} ⟶ X` is a topological embedding** (EGA I, 10.8), for the
two-patch glued scheme `X = Spec A ∪_{D(a) ≅ D(b)} Spec B`.

Over each of the two charts of `X` the morphism is the affine `formalCompletion.toSpec`
(`completionTwoPatchToScheme_base_ι₀`), which is a closed embedding, followed by an open
immersion; the two chart preimages are covered by the two charts of `X_{/Y}`
(`preimage_range_specTwoPatchι₀_subset`); so
`Topology.isEmbedding_of_iSup_eq_top_of_preimage_subset_range` applies. -/
theorem isEmbedding_completionTwoPatchToScheme_base :
    IsEmbedding ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base := by
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range _
    (completionTwoPatchToScheme I hI a J hJ b θ hθ).base.hom.continuous
    (cU a b θ) ?_ (cChart I hI J hJ) (cChartι I hI a J hJ b θ hθ) ?_ ?_ ?_
  · intro z _
    rcases specTwoPatch_jointly_surjective a b θ z with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · exact Opens.mem_iSup.mpr ⟨false, ⟨p, rfl⟩⟩
    · exact Opens.mem_iSup.mpr ⟨true, ⟨q, rfl⟩⟩
  · intro i
    cases i
    · exact (completionTwoPatchι₀ I hI a J hJ b θ hθ).base.hom.continuous
    · exact (completionTwoPatchι₁ I hI a J hJ b θ hθ).base.hom.continuous
  · intro i
    cases i
    · exact preimage_range_specTwoPatchι₀_subset I hI a J hJ b θ hθ
    · exact preimage_range_specTwoPatchι₁_subset I hI a J hJ b θ hθ
  · intro i
    cases i
    · have h : ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base ∘
          cChartι I hI a J hJ b θ hθ false =
        ⇑(specTwoPatchι₀ a b θ).base ∘ ⇑(formalCompletion.toSpec A I hI).base :=
        funext fun x => completionTwoPatchToScheme_base_ι₀ I hI a J hJ b θ hθ x
      rw [h]
      exact (specTwoPatchι₀_isOpenImmersion a b θ).base_open.isEmbedding.comp
        (formalCompletion.isClosedEmbedding_toSpec_base A I hI).isEmbedding
    · have h : ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base ∘
          cChartι I hI a J hJ b θ hθ true =
        ⇑(specTwoPatchι₁ a b θ).base ∘ ⇑(formalCompletion.toSpec B J hJ).base :=
        funext fun y => completionTwoPatchToScheme_base_ι₁ I hI a J hJ b θ hθ y
      rw [h]
      exact (specTwoPatchι₁_isOpenImmersion a b θ).base_open.isEmbedding.comp
        (formalCompletion.isClosedEmbedding_toSpec_base B J hJ).isEmbedding

/-- **The completion of the glued scheme is a closed subspace of it** (EGA I, 10.8): the canonical
morphism `X_{/Y} ⟶ X` is a closed embedding, for the first non-affine `X` in this development.

This is `isEmbedding_completionTwoPatchToScheme_base` paired with
`isClosed_range_completionTwoPatchToScheme_base`; the affine case is
`formalCompletion.isClosedEmbedding_toSpec_base`. -/
theorem isClosedEmbedding_completionTwoPatchToScheme_base :
    IsClosedEmbedding ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base :=
  ⟨isEmbedding_completionTwoPatchToScheme_base I hI a J hJ b θ hθ,
    isClosed_range_completionTwoPatchToScheme_base I hI a J hJ b θ hθ⟩

/-- **`X_{/Y} ⟶ X` is injective.** Two points of the glued completion with the same image in the
glued scheme are equal — including the case where they lie in *different* charts, which is the
only one with any content and which the embedding criterion discharges. -/
theorem injective_completionTwoPatchToScheme_base :
    Function.Injective ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base :=
  (isEmbedding_completionTwoPatchToScheme_base I hI a J hJ b θ hθ).injective

/-- **The closed subspace is a proper one**, as soon as `Spec A` has a prime containing `a` but
not containing `I`: such a prime is in the `A`-chart and outside the image
(`notMem_range_completionTwoPatchToScheme_base`). Without this the closed embedding above would be
compatible with `X_{/Y} ⟶ X` being a homeomorphism. -/
theorem not_surjective_completionTwoPatchToScheme_base {p : PrimeSpectrum A}
    (hp : a ∈ p.asIdeal) (hpI : p ∉ PrimeSpectrum.zeroLocus (I : Set A)) :
    ¬ Function.Surjective ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base := by
  intro hsurj
  exact notMem_range_completionTwoPatchToScheme_base I hI a J hJ b θ hθ hp hpI
    (hsurj ((specTwoPatchι₀ a b θ).base p))

end Embedding

/-- **The hypothesis stack is satisfiable.** Gluing `Spec R` to itself along `D(f)` and completing
along `V(K)` on both charts discharges every hypothesis at once, for an arbitrary ideal `K` and an
arbitrary `f`. The concrete geometry in which the image is neither `∅` nor everything is the
`𝔸¹_ℚ` instance in `FormalSchemes/CompletionTwoPatchClosed.lean`. -/
example (R : Type u) [CommRing R] (K : Ideal R) (hK : K.FG) (f : R) :
    IsClosedEmbedding ⇑(completionTwoPatchToScheme K hK f K hK f (RingEquiv.refl _)
      (Ideal.map_id _)).base :=
  isClosedEmbedding_completionTwoPatchToScheme_base K hK f K hK f (RingEquiv.refl _)
    (Ideal.map_id _)

end AlgebraicGeometry

end
