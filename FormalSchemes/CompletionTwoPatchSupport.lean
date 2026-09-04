import FormalSchemes.CompletionTwoPatchRange

set_option linter.style.header false

/-!
# `hθ` becomes a statement about primes: `X_{/Y}` chart by chart (EGA I, 10.8)

`FormalSchemes/CompletionTwoPatchRange.lean` computed the image of the canonical morphism
`X_{/Y} ⟶ X` for the two-patch glued scheme `X = Spec A ∪_{D(a) ≅ D(b)} Spec B`:

```
range (completionTwoPatchToScheme …).base = ι₀ '' V(I) ∪ ι₁ '' V(J)
```

and stopped there, pricing the closed-embedding half and naming the obstruction: closedness is
local on the two-chart cover and reduces to `ι₀⁻¹(ι₀''V(I) ∪ ι₁''V(J)) = V(I)`, whose middle step
is the first place the compatibility hypothesis `hθ` is actually used. This file supplies that
step, on both charts:

```
ι₀⁻¹(range) = V(I)          ι₁⁻¹(range) = V(J)
```

That is *"the completion of `X` along `Y` is supported on `Y`"* read on each chart of `X`, and it
is the last **mathematical** input to closedness; what remains is topology (see Scope).

## Why `hθ` had to appear here and nowhere earlier

`hθ` — that `θ` carries `I·A_a` onto `J·B_b` — is threaded as a hypothesis through
`completionTwoPatch`, `completionTwoPatchToScheme`, `CompletionCompact`,
`CompletionTwoPatchDoubled` and `CompletionTwoPatchRange`, and **used by none of them**;
`range_completionTwoPatchToScheme_base` says so explicitly. Every glued-completion theorem before
this file is therefore equally true of an *incompatible* gluing. It cannot stay that way here: the
chart preimage above is false without `hθ`, because `ι₀⁻¹(ι₁''V(J))` is then some other subset of
`D(a)` entirely.

What `hθ` needs of the gluing is not merely that a prime of `D(a)` lies in the `B`-chart, but
**which** prime of `B` it is. That refinement is not proved here and is not about two patches:
`AlgebraicGeometry.preimage_image_specTwoPatchι₁` (`FormalSchemes.SpecTwoPatchNonAffine`) says that
`ι₀⁻¹(ι₁''U)` is the image, under the chart of `D(a)`, of the `θ`-translate of the overlap's
preimage of `U`, for an arbitrary subset `U` of `Spec B` and with no ideal in it. It comes from
`LocallyRingedSpace.GlueData.preimage_image_ι` without touching this datum's fields. That is not
independence from the glue condition — Mathlib's `TopCat.GlueData.preimage_image_eq_image` rests
on `CategoryTheory.GlueData.glue_condition_apply` through `TopCat.GlueData.preimage_range` and
`TopCat.GlueData.image_inter` — but it is independence from anything about *two patches*.

What is left for this file is the three rewrites that put the ideals back in, and **`hθ` is spent
on the middle one**: the innermost preimage is `V(J·B_b)`, its `θ`-translate is `V(I·A_a)`, and the
image of that is `V(I) ∩ D(a)`.

The `CategoryTheory.GlueData.glue_condition` **field** itself is opened upstream of this file, not
here, as `AlgebraicGeometry.specTwoPatch_glue` (`FormalSchemes.CompletionTwoPatchToScheme`) —
discharged there from `(specTwoPatchLRSGlueData a b θ).toGlueData.glue_condition ⟨false⟩ ⟨true⟩`,
which is what that file's own overlap obligation required. **This file does not name it either.**
Worth saying, because the same statement used to be proved here a second time under a different
name, and three successive rows read the resulting sentence as evidence that the field was
untouched upstream.

## The two layers

**Localization.** `zeroLocus_map_away_eq_preimage` and `image_zeroLocus_map_away`: `V(I·A_a)` is
the preimage of `V(I)`, and its image in `Spec A` is `V(I) ∩ D(a)`. General facts about
`Localization.Away`, kept local until a second consumer appears.

**Transport.** `comap_θ_preimage_zeroLocus` and its `θ.symm` twin turn `hθ` — an equality of
*ideals* in the localizations — into an equality of *sets of primes*, through
`PrimeSpectrum.preimage_comap_zeroLocus`. `map_θ_symm_ideal` is the ideal-level inverse of `hθ`,
obtained from `Ideal.map_map` and `θ.symm ∘ θ = id`.

**There is no third, glue-condition layer, and that is a decision rather than an omission.** This
file used to carry a `B`-side morphism-level companion to `AlgebraicGeometry.specTwoPatch_glue`
together with the reading of both at a point; the `Support` section below ran on them until it was
rerouted through `AlgebraicGeometry.preimage_image_specTwoPatchι₁` and its mirror, which say the
same of an arbitrary subset and come from the topological gluing rather than from this datum.
Nothing consumed them afterwards and all three are gone. The policy that disposed of them, and the
reason, are stated once in `FormalSchemes/ChartedSchemeDatumChartOverlap.lean`, where the
arbitrary-index one lived.

The chart preimages themselves — `preimage_range_specTwoPatchι₁`, `preimage_range_specTwoPatchι₀`
and their image-shaped refinements — are **not** proved here either: they need none of this and
live in `FormalSchemes/SpecTwoPatchNonAffine.lean`, beside the properness statements they now
prove.

## Scope

**`IsClosed` and `Topology.IsClosedEmbedding` are not attempted *here*, and neither is open.**
With this file, closedness of the range is `V(I)` and `V(J)` being closed plus *"a subset of a
space is closed when its preimage under each member of an open cover is closed"* — true, and still
not stated anywhere in this development for the `LocallyRingedSpace` carrier, but the carve it was
waiting for happened: `AlgebraicGeometry.isClosed_range_completionTwoPatchToScheme_base`
(`FormalSchemes.CompletionTwoPatchClosed`) runs that argument off the statement below.
`Topology.IsClosedEmbedding` additionally needs **injectivity** of the base map of
`completionTwoPatchToScheme`, whose mixed-chart case needs the converse of
`FormalSchemes.CompletionTwoPatchDoubled`'s overlap analysis (a point of `Spf A^` lying over
`D(a)` is in the overlap chart); that converse is
`formalCompletion.mem_range_basicOpenImmersion` (`FormalSchemes.CompletionBasicOpenMap`), and the
embedding is `AlgebraicGeometry.isClosedEmbedding_completionTwoPatchToScheme_base`
(`FormalSchemes.CompletionTwoPatchEmbedding`).

Two shortcuts to closedness that cannot work, recorded so they are not retried: the source is
quasi-compact (`FormalSchemes/CompletionCompact.lean`) so its image is compact — but `specTwoPatch`
is not T1, so compact does not give closed; and `ι₀''V(I)` is not closed in `specTwoPatch` on its
own, since `ι₀` is an *open* immersion. Any correct argument must use `hθ`.

## Main results

* `AlgebraicGeometry.zeroLocus_map_away_eq_preimage`, `AlgebraicGeometry.image_zeroLocus_map_away`:
  `V(I·A_a)` as a preimage of `V(I)`, and its image `V(I) ∩ D(a)`.
* `AlgebraicGeometry.comap_θ_preimage_zeroLocus`,
  `AlgebraicGeometry.comap_θ_symm_preimage_zeroLocus`: **`hθ` as a statement about primes.**
* `AlgebraicGeometry.preimage_range_completionTwoPatchToScheme_base_ι₀` and `..._ι₁`: **the
  completion is supported on `V(I)`, chart by chart.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Localization

variable {A : Type u} [CommRing A] (I : Ideal A) (a : A)

/-- **`V(I·A_a)` is the preimage of `V(I)`.** A prime of the localization contains `I·A_a` exactly
when the prime of `A` below it contains `I`. -/
theorem zeroLocus_map_away_eq_preimage :
    PrimeSpectrum.zeroLocus (I.map (algebraMap A (Localization.Away a)) : Set _) =
      PrimeSpectrum.comap (algebraMap A (Localization.Away a)) ⁻¹'
        PrimeSpectrum.zeroLocus (I : Set A) := by
  rw [PrimeSpectrum.preimage_comap_zeroLocus, Ideal.map, PrimeSpectrum.zeroLocus_span]

/-- **The image of `V(I·A_a)` in `Spec A` is `V(I) ∩ D(a)`.** The chart `Spec A_a ⟶ Spec A` is
injective with image `D(a)`, so the image of a preimage is the intersection with `D(a)`. This is
the `V(I·A_a) = V(I) ∩ D(a)` that the closed-embedding pricing on
`FormalSchemes/CompletionTwoPatchRange.lean` calls for. -/
theorem image_zeroLocus_map_away :
    PrimeSpectrum.comap (algebraMap A (Localization.Away a)) ''
        (PrimeSpectrum.zeroLocus (I.map (algebraMap A (Localization.Away a)) : Set _)) =
      PrimeSpectrum.zeroLocus (I : Set A) ∩ PrimeSpectrum.basicOpen a := by
  rw [zeroLocus_map_away_eq_preimage, Set.image_preimage_eq_inter_range,
    PrimeSpectrum.localization_away_comap_range _ a]

end Localization

section Transport

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (a : A) (J : Ideal B) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

include hθ

/-- **`hθ` read backwards at the level of ideals**: `θ.symm` carries `J·B_b` onto `I·A_a`. Push
`hθ` forward along `θ.symm` and collapse `θ.symm ∘ θ` to the identity with `Ideal.map_map`. -/
theorem map_θ_symm_ideal :
    (J.map (algebraMap B (Localization.Away b))).map θ.symm.toRingHom =
      I.map (algebraMap A (Localization.Away a)) := by
  have hcomp : θ.symm.toRingHom.comp θ.toRingHom =
      RingHom.id (Localization.Away a) := by
    ext x
    exact θ.symm_apply_apply x
  rw [← hθ, Ideal.map_map, hcomp, Ideal.map_id]

/-- **`hθ` as a statement about primes.** Under the identification `Spec θ : Spec B_b ≅ Spec A_a`
of the two overlaps, `V(I·A_a)` pulls back to `V(J·B_b)`. This is the transport that
`FormalSchemes/CompletionTwoPatchRange.lean` records as missing, and it is the first use of `hθ`
anywhere in this development. -/
theorem comap_θ_preimage_zeroLocus :
    PrimeSpectrum.comap θ.toRingHom ⁻¹'
        PrimeSpectrum.zeroLocus (I.map (algebraMap A (Localization.Away a)) : Set _) =
      PrimeSpectrum.zeroLocus (J.map (algebraMap B (Localization.Away b)) : Set _) := by
  rw [PrimeSpectrum.preimage_comap_zeroLocus, ← hθ, ← PrimeSpectrum.zeroLocus_span,
    ← Ideal.map, Ideal.map]

/-- **`hθ` as a statement about primes, in the other direction**: `V(J·B_b)` pulls back to
`V(I·A_a)` along `Spec θ.symm`. -/
theorem comap_θ_symm_preimage_zeroLocus :
    PrimeSpectrum.comap θ.symm.toRingHom ⁻¹'
        PrimeSpectrum.zeroLocus (J.map (algebraMap B (Localization.Away b)) : Set _) =
      PrimeSpectrum.zeroLocus (I.map (algebraMap A (Localization.Away a)) : Set _) := by
  rw [PrimeSpectrum.preimage_comap_zeroLocus, ← PrimeSpectrum.zeroLocus_span, ← Ideal.map,
    map_θ_symm_ideal I a J b θ hθ]

end Transport

section Support

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (hI : I.FG) (a : A)
  (J : Ideal B) (hJ : J.FG) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

include hθ

/-- **The part of `Spec A` lying over the `B`-side of the completion is `V(I) ∩ D(a)`.**

`AlgebraicGeometry.preimage_image_specTwoPatchι₁` (`FormalSchemes.SpecTwoPatchNonAffine`) already
says that the left-hand side is the image, under the chart of `D(a)`, of the `θ`-translate of the
overlap's preimage of `V(J)` — a statement about the glued **scheme**, with no ideal in it. Three
rewrites finish: the innermost preimage is `V(J·B_b)` (`zeroLocus_map_away_eq_preimage`); `hθ`
turns its `θ`-translate into `V(I·A_a)` (`comap_θ_symm_preimage_zeroLocus`); and the image of that
is `V(I) ∩ D(a)` (`image_zeroLocus_map_away`).

**The middle step is where the compatibility hypothesis does its work**, exactly as
`AlgebraicGeometry.ChartedCompletionDatum.preimage_image_zeroLocus_specι` does at an arbitrary
index. Rerouting the set-theoretic bookkeeping around it through the topological gluing does not
move it: `hθ` is still the only reason a prime of `D(a)` lands where it does. -/
theorem preimage_image_zeroLocus_specTwoPatchι₁ :
    ⇑(specTwoPatchι₀ a b θ).base ⁻¹'
        (⇑(specTwoPatchι₁ a b θ).base '' PrimeSpectrum.zeroLocus (J : Set B)) =
      PrimeSpectrum.zeroLocus (I : Set A) ∩ PrimeSpectrum.basicOpen a := by
  rw [preimage_image_specTwoPatchι₁ a b θ, ← zeroLocus_map_away_eq_preimage J b,
    comap_θ_symm_preimage_zeroLocus I a J b θ hθ, image_zeroLocus_map_away I a]

/-- **The part of `Spec B` lying over the `A`-side of the completion is `V(J) ∩ D(b)`**, the mirror
of `preimage_image_zeroLocus_specTwoPatchι₁`. -/
theorem preimage_image_zeroLocus_specTwoPatchι₀ :
    ⇑(specTwoPatchι₁ a b θ).base ⁻¹'
        (⇑(specTwoPatchι₀ a b θ).base '' PrimeSpectrum.zeroLocus (I : Set A)) =
      PrimeSpectrum.zeroLocus (J : Set B) ∩ PrimeSpectrum.basicOpen b := by
  rw [preimage_image_specTwoPatchι₀ a b θ, ← zeroLocus_map_away_eq_preimage I a,
    comap_θ_preimage_zeroLocus I a J b θ hθ, image_zeroLocus_map_away J b]

/-- **The completion is supported on `V(J)`, seen on the `B`-chart** (EGA I, 10.8). -/
theorem preimage_range_completionTwoPatchToScheme_base_ι₁ :
    ⇑(specTwoPatchι₁ a b θ).base ⁻¹'
        Set.range ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base =
      PrimeSpectrum.zeroLocus (J : Set B) := by
  have hinj : Function.Injective ⇑(specTwoPatchι₁ a b θ).base :=
    (specTwoPatchι₁_isOpenImmersion a b θ).base_open.injective
  rw [range_completionTwoPatchToScheme_base, Set.preimage_union,
    preimage_image_zeroLocus_specTwoPatchι₀ I a J b θ hθ, Set.preimage_image_eq _ hinj]
  exact Set.union_eq_self_of_subset_left Set.inter_subset_left

/-- **The completion is supported on `V(I)`, seen on the `A`-chart** (EGA I, 10.8). The image of
`X_{/Y} ⟶ X` meets the `A`-chart exactly in the closed set `V(I)`: the `A`-side contributes `V(I)`
by injectivity of `ι₀`, and the `B`-side contributes `V(I) ∩ D(a)`, which is already inside it. -/
theorem preimage_range_completionTwoPatchToScheme_base_ι₀ :
    ⇑(specTwoPatchι₀ a b θ).base ⁻¹'
        Set.range ⇑(completionTwoPatchToScheme I hI a J hJ b θ hθ).base =
      PrimeSpectrum.zeroLocus (I : Set A) := by
  have hinj : Function.Injective ⇑(specTwoPatchι₀ a b θ).base :=
    (specTwoPatchι₀_isOpenImmersion a b θ).base_open.injective
  rw [range_completionTwoPatchToScheme_base, Set.preimage_union,
    preimage_image_zeroLocus_specTwoPatchι₁ I a J b θ hθ, Set.preimage_image_eq _ hinj]
  exact Set.union_eq_self_of_subset_right Set.inter_subset_left

end Support

/-! ### A concrete witness

Doubling `𝔸¹_ℚ` along `D(X)` and completing along the point `1` on each chart — the instance
`FormalSchemes/CompletionTwoPatchRange.lean` already uses. The chart preimage is then `V(X − 1)`,
which contains the point `1` and misses the origin, so the identity is neither `∅` nor everything.

Note `X ∉ (X − 1)`, so the overlap `D(X) ∩ V(X − 1)` is **nonempty**: this is the nondegenerate
case, in which the `B`-side of the range genuinely contributes to the `A`-chart. At `a ∈ I` that
contribution is empty and the identity would hold for a trivial reason. -/

section Witness

open Polynomial

/-- The `A`-chart preimage of the image of `X_{/Y} ⟶ X`, for the standing witness. The geometry —
the ideal `(X - 1)`, the origin and the centre `1` — is shared with
`FormalSchemes/CompletionTwoPatchRange.lean` and `FormalSchemes/CompletionTwoPatchClosed.lean`
and lives in `FormalSchemes/TwoPatchWitness.lean`. -/
private def wPre : Set (PrimeSpectrum ℚ[X]) :=
  ⇑(specTwoPatchι₀ (X : ℚ[X]) X (RingEquiv.refl (Localization.Away (X : ℚ[X])))).base ⁻¹'
    Set.range ⇑(completionTwoPatchToScheme twoPatchWitnessIdeal twoPatchWitnessIdeal_fg
      (X : ℚ[X]) twoPatchWitnessIdeal twoPatchWitnessIdeal_fg (X : ℚ[X])
      (RingEquiv.refl (Localization.Away (X : ℚ[X]))) (Ideal.map_id _)).base

private theorem wPre_eq :
    wPre = PrimeSpectrum.zeroLocus (twoPatchWitnessIdeal : Set ℚ[X]) :=
  preimage_range_completionTwoPatchToScheme_base_ι₀ twoPatchWitnessIdeal twoPatchWitnessIdeal_fg
    (X : ℚ[X]) twoPatchWitnessIdeal twoPatchWitnessIdeal_fg (X : ℚ[X])
    (RingEquiv.refl (Localization.Away (X : ℚ[X]))) (Ideal.map_id _)

/-- **The chart preimage contains the centre of the completion.** -/
example : twoPatchWitnessOne ∈ wPre := by
  rw [wPre_eq]
  exact twoPatchWitnessOne_mem_zeroLocus

/-- **The chart preimage is a proper subset**: the origin of the first chart is outside it. -/
example : twoPatchWitnessOrigin ∉ wPre := by
  rw [wPre_eq]
  exact twoPatchWitnessOrigin_notMem_zeroLocus

end Witness

end AlgebraicGeometry
