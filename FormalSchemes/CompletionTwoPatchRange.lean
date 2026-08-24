import FormalSchemes.CompletionTwoPatchToScheme
import FormalSchemes.SpecTwoPatchNonAffine
import FormalSchemes.TwoPatchWitness

set_option linter.style.header false

/-!
# The underlying set of `X_{/Y}` inside `X` (EGA I, 10.8)

`FormalSchemes/CompletionTwoPatchToScheme.lean` builds the canonical morphism

```
completionTwoPatch  ──completionTwoPatchToScheme──→  specTwoPatch
```

from the glued formal completion to the glued scheme `Spec A ∪_{D(a) ≅ D(b)} Spec B`, and
characterises it *categorically*: chart by chart (`completionTwoPatchι₀_comp_toScheme`), and
uniquely so (`completionTwoPatch_hom_ext`). Nothing there says what it does to **points**.

For an affine `X` that question is settled in `FormalSchemes/CompletionToSpec.lean`:
`formalCompletion.range_toSpec_base` says the image of `Spf R^ ⟶ Spec R` is the zero locus `V(I)`,
and `formalCompletion.isClosedEmbedding_toSpec_base` says the map is a closed topological
embedding. This file lifts the first of those to the glued case, which is the geometric content of
EGA I 10.8 — *the completion of `X` along `Y` is supported on `Y`* — for the first non-affine `X`
in this development.

## What is proved

The image of `completionTwoPatchToScheme` is exactly the closed subset glued from `V(I)` and
`V(J)`:

```
range = ι₀ '' V(I) ∪ ι₁ '' V(J)
```

(`range_completionTwoPatchToScheme_base`), off joint surjectivity of the two completion charts and
the affine range lemma on each. Note that the compatibility hypothesis `hθ` plays no part in the
proof: it is what makes the two glued objects exist, not what computes this image.

The equality is worth little on its own — it is compatible with the image being *everything*, in
which case it says nothing about completion at all. So
`notMem_range_completionTwoPatchToScheme_base` comes with it: a prime of `A` containing `a` but not
containing `I` maps to a point of `specTwoPatch` the completion does not reach, so the image is a
**proper** subset. Concretely,
doubling `𝔸¹_ℚ` along `D(X)` and completing along the point `1` on each chart, the origin of the
first chart is outside the completion.

## Scope

The **closed-embedding** half is not attempted. Closedness of the range is local on the two-chart
cover and reduces to

```
ι₀⁻¹(ι₀ '' V(I) ∪ ι₁ '' V(J)) = V(I) ∪ (V(I) ∩ D(a)) = V(I),
```

whose middle equality is the first place the compatibility hypothesis `hθ` would actually be used:
a prime of `V(J) ∩ D(b)` corresponds under `θ` to one of `V(I·A_a) = V(I) ∩ D(a)`. That transport
— from `hθ`, an equality of ideals in the localizations, to a statement about primes — does not
exist in this development. Injectivity of the base map is likewise left open; its mixed-chart case
needs a converse to the overlap analysis of `FormalSchemes.CompletionTwoPatchDoubled`, namely that
a point of `Spf A^` lying over `D(a)` is in the overlap chart.

That the glued completion is *genuinely* glued — its two charts meet only over `D(â)`, so a point
outside the overlap is doubled — is `FormalSchemes.CompletionTwoPatchDoubled` and is deliberately
not repeated here.

## Main results

* `AlgebraicGeometry.completionTwoPatchToScheme_base_ι₀` and `..._ι₁`: the base map of the
  canonical morphism on each completion chart.
* `AlgebraicGeometry.range_completionTwoPatchToScheme_base`: **the image is the glued closed
  subset.**
* `AlgebraicGeometry.notMem_range_completionTwoPatchToScheme_base`: **and it is a proper subset.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (hI : I.FG) (a : A)
  (J : Ideal B) (hJ : J.FG) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

/-! ### The base map of the canonical morphism, chart by chart -/

/-- **On the `A`-chart, the canonical morphism is the affine `formalCompletion.toSpec`.** This is
`completionTwoPatchι₀_comp_toScheme` evaluated at a point. -/
theorem completionTwoPatchToScheme_base_ι₀ (z : (formalCompletion A I hI).toLocallyRingedSpace) :
    (completionTwoPatchToScheme I hI a J hJ b θ hθ).base
        ((completionTwoPatchι₀ I hI a J hJ b θ hθ).base z) =
      (specTwoPatchι₀ a b θ).base ((formalCompletion.toSpec A I hI).base z) := by
  simpa using congrArg (fun m : (formalCompletion A I hI).toLocallyRingedSpace ⟶
      specTwoPatch a b θ => m.base z)
      (completionTwoPatchι₀_comp_toScheme I hI a J hJ b θ hθ)

/-- **On the `B`-chart, the canonical morphism is the affine `formalCompletion.toSpec`.** -/
theorem completionTwoPatchToScheme_base_ι₁ (z : (formalCompletion B J hJ).toLocallyRingedSpace) :
    (completionTwoPatchToScheme I hI a J hJ b θ hθ).base
        ((completionTwoPatchι₁ I hI a J hJ b θ hθ).base z) =
      (specTwoPatchι₁ a b θ).base ((formalCompletion.toSpec B J hJ).base z) := by
  simpa using congrArg (fun m : (formalCompletion B J hJ).toLocallyRingedSpace ⟶
      specTwoPatch a b θ => m.base z)
      (completionTwoPatchι₁_comp_toScheme I hI a J hJ b θ hθ)

/-! ### The range -/

/-- **The formal completion of the glued scheme is supported on the glued closed subset**
(EGA I, 10.8). The image of `completionTwoPatchToScheme` is the union of the two charts' images of
the zero loci `V(I)` and `V(J)`.

Both inclusions are the same two facts used twice: the completion charts cover
(`completionTwoPatch_jointly_surjective`), and on each of them the morphism is the affine
`formalCompletion.toSpec`, whose range is the zero locus
(`formalCompletion.range_toSpec_base`). In particular the compatibility hypothesis `hθ` plays no
part — it is needed to *build* the glued objects, not to compute this image. -/
theorem range_completionTwoPatchToScheme_base :
    Set.range ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base =
      ⇑(specTwoPatchι₀ a b θ).base '' PrimeSpectrum.zeroLocus (I : Set A) ∪
        ⇑(specTwoPatchι₁ a b θ).base '' PrimeSpectrum.zeroLocus (J : Set B) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rcases completionTwoPatch_jointly_surjective I hI a J hJ b θ hθ y with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact Or.inl ⟨_, by rw [← formalCompletion.range_toSpec_base A I hI]; exact ⟨z, rfl⟩,
        (completionTwoPatchToScheme_base_ι₀ I hI a J hJ b θ hθ z).symm⟩
    · exact Or.inr ⟨_, by rw [← formalCompletion.range_toSpec_base B J hJ]; exact ⟨z, rfl⟩,
        (completionTwoPatchToScheme_base_ι₁ I hI a J hJ b θ hθ z).symm⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · rw [← formalCompletion.range_toSpec_base A I hI] at hp
      obtain ⟨z, rfl⟩ := hp
      exact ⟨_, completionTwoPatchToScheme_base_ι₀ I hI a J hJ b θ hθ z⟩
    · rw [← formalCompletion.range_toSpec_base B J hJ] at hp
      obtain ⟨z, rfl⟩ := hp
      exact ⟨_, completionTwoPatchToScheme_base_ι₁ I hI a J hJ b θ hθ z⟩

/-- **The completion is a proper part of the ambient glued scheme.** A prime `p` of `A` that
contains `a` but does not contain `I` maps, under the `A`-chart, to a point of `specTwoPatch`
outside the image of `completionTwoPatchToScheme`: it misses `ι₀ '' V(I)` because `ι₀` is
injective, and it misses `ι₁ '' V(J)` because a point outside `D(a)` is outside the `B`-chart
altogether (`specTwoPatchι₀_base_notMem_range_specTwoPatchι₁`). -/
theorem notMem_range_completionTwoPatchToScheme_base {p : PrimeSpectrum A} (hp : a ∈ p.asIdeal)
    (hpI : p ∉ PrimeSpectrum.zeroLocus (I : Set A)) :
    (specTwoPatchι₀ a b θ).base p ∉
      Set.range ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base := by
  rw [range_completionTwoPatchToScheme_base I hI a J hJ b θ hθ]
  rintro (⟨q, hq, hqe⟩ | ⟨q, hq, hqe⟩)
  · exact hpI (((specTwoPatchι₀_isOpenImmersion a b θ).base_open.injective hqe) ▸ hq)
  · exact specTwoPatchι₀_base_notMem_range_specTwoPatchι₁ a b θ p
      (notMem_range_specAwayMap a hp) ⟨q, hqe⟩

/-! ### A concrete witness

Doubling `𝔸¹_ℚ` along `D(X)` and completing along the point `1` on each chart. The *origin* of the
first chart then lies outside the completion, so the image really is a proper subset. -/

section Witness

open Polynomial

/-- **The completion is a proper part of the glued scheme**, concretely. The scaffolding — the
ideal `(X - 1)`, the origin, and the fact that the origin is off `V(X - 1)` — is shared with
`FormalSchemes/CompletionTwoPatchSupport.lean` and `FormalSchemes/CompletionTwoPatchClosed.lean`
and lives in `FormalSchemes/TwoPatchWitness.lean`. -/
example : (specTwoPatchι₀ (X : ℚ[X]) X (RingEquiv.refl (Localization.Away (X : ℚ[X])))).base
      twoPatchWitnessOrigin ∉
    Set.range ⇑(completionTwoPatchToScheme twoPatchWitnessIdeal twoPatchWitnessIdeal_fg
      (X : ℚ[X]) twoPatchWitnessIdeal twoPatchWitnessIdeal_fg (X : ℚ[X])
      (RingEquiv.refl (Localization.Away (X : ℚ[X]))) (Ideal.map_id _)).base :=
  notMem_range_completionTwoPatchToScheme_base _ twoPatchWitnessIdeal_fg _ _
    twoPatchWitnessIdeal_fg _ _ _ X_mem_twoPatchWitnessOrigin
    twoPatchWitnessOrigin_notMem_zeroLocus

end Witness

end AlgebraicGeometry
