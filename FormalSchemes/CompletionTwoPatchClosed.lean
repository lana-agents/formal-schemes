import FormalSchemes.CompletionTwoPatchSupport

set_option linter.style.header false

/-!
# The completion of the two-patch scheme is supported on a closed subset (EGA I, 10.8)

`FormalSchemes/CompletionTwoPatchRange.lean` computed the image of the canonical morphism
`X_{/Y} ⟶ X` for the two-patch glued scheme `X = Spec A ∪_{D(a) ≅ D(b)} Spec B`:

```
range (completionTwoPatchToScheme …).base = ι₀ '' V(I) ∪ ι₁ '' V(J)
```

and `FormalSchemes/CompletionTwoPatchSupport.lean` read that image on each chart:

```
ι₀⁻¹(range) = V(I)          ι₁⁻¹(range) = V(J)
```

This file draws the topological conclusion: **the image is closed**. That is the statement EGA I
10.8 actually makes — *the completion of `X` along `Y` is supported on the closed subset `Y`* —
and this is the first non-affine `X` in this development for which it is available. Everything on
master before it says only that the image *equals* a certain set.

## The argument

Closedness is local on an open cover, and the two charts of `specTwoPatch` are open immersions
that cover it. So it suffices that each chart preimage be closed, which is what the two lemmas
above give: both are zero loci.

The proof below runs that argument on the **complement**, which is why no covering machinery
appears. `Sᶜ` is the union of the images of its own two chart preimages — that is joint
surjectivity, and nothing more — and each of those preimages is the complement of a zero locus,
hence open, so its image under an open map is open.

`TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage` (`Mathlib/Topology/LocalAtTarget.lean`)
is the "right" lemma in the abstract and is deliberately **not** used: it is stated for
`U : ι → Opens β` and *subtype* preimages, so consuming it means assembling an `IsOpenCover` from
the two chart ranges and then transporting each preimage across the homeomorphism `Spec A ≃ range
ι₀`. The complement argument is an open map applied to an open set, twice, and needs no bridging.

Two shortcuts that cannot work are recorded in `FormalSchemes/CompletionTwoPatchSupport.lean`:
the source is quasi-compact but `specTwoPatch` is not T1, so compact does not give closed; and
`ι₀ '' V(I)` is not closed on its own, `ι₀` being an *open* immersion. Any correct argument must
use `hθ`, and this one does — through the two chart preimages.

## Scope

**`IsClosedEmbedding` is not attempted.** It is `IsEmbedding` plus closed range, and `IsEmbedding`
needs **injectivity** of `completionTwoPatchToScheme.base` together with the inducing property.
The mixed-chart case of injectivity needs the converse of
`FormalSchemes/CompletionTwoPatchDoubled.lean`'s overlap analysis — *a point of `Spf A^` lying
over `D(a)` is in the overlap chart*. `SpecTwoPatchNonAffine.lean`'s
`preimage_range_specTwoPatchι₁` is the scheme-side analogue of exactly that statement, so the
completion-side version should now be transcribable rather than invented; but it is unmeasured and
belongs in its own carve.

The affine `formalCompletion.isClosedEmbedding_toSpec_base` (`FormalSchemes/CompletionToSpec.lean`)
is already on master and is *not* used here: this proof goes through the chart preimages, not
through the affine embedding.

## Main results

* `AlgebraicGeometry.isClosed_range_completionTwoPatchToScheme_base`: **the image of `X_{/Y} ⟶ X`
  is closed in `X`.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Support

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (hI : I.FG) (a : A)
  (J : Ideal B) (hJ : J.FG) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

include hθ

/-- **The completion of the glued scheme is supported on a closed subset** (EGA I, 10.8): the
image of `X_{/Y} ⟶ X` is closed in `X = Spec A ∪_{D(a) ≅ D(b)} Spec B`.

Both chart preimages of the image are zero loci
(`preimage_range_completionTwoPatchToScheme_base_ι₀` and its `ι₁` twin), so both preimages of the
*complement* are open; the complement is the union of their images under the two open immersions,
by joint surjectivity, hence open. -/
theorem isClosed_range_completionTwoPatchToScheme_base :
    IsClosed (Set.range ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base) := by
  set S := Set.range ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base with hS
  rw [← isOpen_compl_iff]
  have h0 : ⇑(specTwoPatchι₀ a b θ).base ⁻¹' Sᶜ =
      (PrimeSpectrum.zeroLocus (I : Set A))ᶜ := by
    rw [Set.preimage_compl, hS,
      preimage_range_completionTwoPatchToScheme_base_ι₀ I hI a J hJ b θ hθ]
    rfl
  have h1 : ⇑(specTwoPatchι₁ a b θ).base ⁻¹' Sᶜ =
      (PrimeSpectrum.zeroLocus (J : Set B))ᶜ := by
    rw [Set.preimage_compl, hS,
      preimage_range_completionTwoPatchToScheme_base_ι₁ I hI a J hJ b θ hθ]
    rfl
  have hcover : Sᶜ = ⇑(specTwoPatchι₀ a b θ).base '' (⇑(specTwoPatchι₀ a b θ).base ⁻¹' Sᶜ) ∪
      ⇑(specTwoPatchι₁ a b θ).base '' (⇑(specTwoPatchι₁ a b θ).base ⁻¹' Sᶜ) := by
    ext x
    constructor
    · intro hx
      rcases specTwoPatch_jointly_surjective a b θ x with ⟨p, rfl⟩ | ⟨q, rfl⟩
      · exact Or.inl ⟨p, hx, rfl⟩
      · exact Or.inr ⟨q, hx, rfl⟩
    · rintro (⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩) <;> assumption
  rw [hcover, h0, h1]
  exact ((specTwoPatchι₀_isOpenImmersion a b θ).base_open.isOpenMap _
      (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl).union
    ((specTwoPatchι₁_isOpenImmersion a b θ).base_open.isOpenMap _
      (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl)

end Support

/-! ### A concrete witness

`IsClosed` is true of `∅` and of the whole space, so the theorem above says nothing until an
instance is exhibited in which the image is neither. Doubling `𝔸¹_ℚ` along `D(X)` and completing
along the point `1` on each chart — the instance
`FormalSchemes/CompletionTwoPatchRange.lean` and `FormalSchemes/CompletionTwoPatchSupport.lean`
already use, so the three witnesses are visibly the same geometry — the image is `V(X - 1)` on
each chart: it contains the centre `1` of the completion and misses the origin.

Note `X ∉ (X - 1)`, so the overlap `D(X) ∩ V(X - 1)` is **nonempty**: this is the nondegenerate
case, in which the two charts genuinely contribute to each other. -/

section Witness

open Polynomial

/-- The image of the canonical morphism, for the doubled `𝔸¹_ℚ` completed at `1`. The geometry —
the ideal `(X - 1)`, the origin and the centre `1` — is shared with
`FormalSchemes/CompletionTwoPatchRange.lean` and `FormalSchemes/CompletionTwoPatchSupport.lean`
and lives in `FormalSchemes/TwoPatchWitness.lean`. -/
private abbrev wRange := Set.range ⇑(completionTwoPatchToScheme twoPatchWitnessIdeal
  twoPatchWitnessIdeal_fg (X : ℚ[X]) twoPatchWitnessIdeal twoPatchWitnessIdeal_fg
  (X : ℚ[X]) (RingEquiv.refl (Localization.Away (X : ℚ[X]))) (Ideal.map_id _)).base

/-- **The image is closed**, concretely. -/
example : IsClosed wRange :=
  isClosed_range_completionTwoPatchToScheme_base twoPatchWitnessIdeal twoPatchWitnessIdeal_fg
    (X : ℚ[X]) twoPatchWitnessIdeal twoPatchWitnessIdeal_fg (X : ℚ[X])
    (RingEquiv.refl (Localization.Away (X : ℚ[X]))) (Ideal.map_id _)

/-- **The image is not empty**: it contains the centre of the completion. -/
example : (specTwoPatchι₀ (X : ℚ[X]) X
    (RingEquiv.refl (Localization.Away (X : ℚ[X])))).base twoPatchWitnessOne ∈ wRange :=
  (Set.ext_iff.mp (preimage_range_completionTwoPatchToScheme_base_ι₀ twoPatchWitnessIdeal
    twoPatchWitnessIdeal_fg (X : ℚ[X]) twoPatchWitnessIdeal twoPatchWitnessIdeal_fg (X : ℚ[X])
    (RingEquiv.refl (Localization.Away (X : ℚ[X]))) (Ideal.map_id _)) twoPatchWitnessOne).mpr
    twoPatchWitnessOne_mem_zeroLocus

/-- **The image is not everything**: the origin of the first chart lies outside it. -/
example : (specTwoPatchι₀ (X : ℚ[X]) X
    (RingEquiv.refl (Localization.Away (X : ℚ[X])))).base twoPatchWitnessOrigin ∉ wRange :=
  notMem_range_completionTwoPatchToScheme_base _ twoPatchWitnessIdeal_fg _ _
    twoPatchWitnessIdeal_fg _ _ _ X_mem_twoPatchWitnessOrigin
    twoPatchWitnessOrigin_notMem_zeroLocus

end Witness

end AlgebraicGeometry
