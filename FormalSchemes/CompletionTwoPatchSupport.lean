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

Correspondingly this file is where the glue condition is first read **at a point**. What the
earlier files needed of the gluing is only *where* the charts meet, and that holds for any glue
datum whatever: `FormalSchemes/SpecTwoPatchNonAffine.lean` gets `ι₀⁻¹(range ι₁) = D(a)` from
`LocallyRingedSpace.GlueData.preimage_range_ι` without touching the datum's fields. That is not
independence from the glue condition — Mathlib's `TopCat.GlueData.preimage_range` rests on
`CategoryTheory.GlueData.glue_condition_apply` one level down — but it is independence from
anything about *two patches*.
Here we need more: not merely that a prime of `D(a)` lies in the `B`-chart, but **which** prime of
`B` it is, since that is what `hθ` is a statement about. That is
`AlgebraicGeometry.specTwoPatchι₀_base_comap_algebraMap` below, and it is the first statement in
this development that names the correspondence rather than asserting that one exists.

The `CategoryTheory.GlueData.glue_condition` **field** itself is opened one file earlier, not
here. `AlgebraicGeometry.specTwoPatch_glue` (`FormalSchemes.CompletionTwoPatchToScheme`) is
already exactly the morphism-level identity this section needs — discharged from
`(specTwoPatchLRSGlueData a b θ).toGlueData.glue_condition ⟨false⟩ ⟨true⟩`, which is what that
file's own overlap obligation required — and this file consumes it by import. Worth saying,
because the same statement used to be proved here a second time under a different name, and three
successive rows read the resulting sentence as evidence that the field was untouched upstream.

## The three layers

**Localization.** `zeroLocus_map_away_eq_preimage` and `image_zeroLocus_map_away`: `V(I·A_a)` is
the preimage of `V(I)`, and its image in `Spec A` is `V(I) ∩ D(a)`. General facts about
`Localization.Away`, kept local until a second consumer appears.

**Transport.** `comap_θ_preimage_zeroLocus` and its `θ.symm` twin turn `hθ` — an equality of
*ideals* in the localizations — into an equality of *sets of primes*, through
`PrimeSpectrum.preimage_comap_zeroLocus`. `map_θ_symm_ideal` is the ideal-level inverse of `hθ`,
obtained from `Ideal.map_map` and `θ.symm ∘ θ = id`.

**Glue.** The glue condition in usable form — the two ways of mapping `Spec A_a` into the glued
scheme agree — is `AlgebraicGeometry.specTwoPatch_glue`, and it is **not** proved here; it comes in
from `FormalSchemes.CompletionTwoPatchToScheme`, which needed it for the overlap obligation of
`completionTwoPatchToScheme`. What this file adds is its `ι₁` twin, a two-line consequence obtained
by composing with `specGlueIso.inv` rather than by redoing the `eqToHom` bookkeeping, and the
reading of both at a point (`specTwoPatchι₀_base_comap_algebraMap` and its twin): a prime of `A_a`
and its `θ`-translate have the *same* image in the glued scheme, which is the identification the
`Support` section below feeds `hθ`. The chart preimages themselves —
`preimage_range_specTwoPatchι₁` and `preimage_range_specTwoPatchι₀` — are **not** proved here
either: they need none of this and live in `FormalSchemes/SpecTwoPatchNonAffine.lean`, beside the
properness statements they now prove.

## Scope

**`IsClosed` and `IsClosedEmbedding` are not attempted.** With this file, closedness of the range
is `V(I)` and `V(J)` being closed plus *"a subset of a space is closed when its preimage under
each member of an open cover is closed"* — true, but not stated anywhere in this development for
the `LocallyRingedSpace` carrier, and worth its own carve. `IsClosedEmbedding` additionally needs
**injectivity** of `completionTwoPatchToScheme.base`, whose mixed-chart case needs the converse of
`FormalSchemes/CompletionTwoPatchDoubled.lean`'s overlap analysis (a point of `Spf A^` lying over
`D(a)` is in the overlap chart) and is unpriced.

Two shortcuts to closedness that cannot work, recorded so they are not retried: the source is
quasi-compact (`FormalSchemes/CompletionCompact.lean`) so its image is compact — but `specTwoPatch`
is not T1, so compact does not give closed; and `ι₀''V(I)` is not closed in `specTwoPatch` on its
own, since `ι₀` is an *open* immersion. Any correct argument must use `hθ`.

## Main results

* `AlgebraicGeometry.zeroLocus_map_away_eq_preimage`, `AlgebraicGeometry.image_zeroLocus_map_away`:
  `V(I·A_a)` as a preimage of `V(I)`, and its image `V(I) ∩ D(a)`.
* `AlgebraicGeometry.comap_θ_preimage_zeroLocus`,
  `AlgebraicGeometry.comap_θ_symm_preimage_zeroLocus`: **`hθ` as a statement about primes.**
* `AlgebraicGeometry.specAwayMap_comp_specTwoPatchι₁`: the `B`-side glue condition, off
  `AlgebraicGeometry.specTwoPatch_glue`, with
  `AlgebraicGeometry.specTwoPatchι₀_base_comap_algebraMap` and its twin reading both at a point.
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

section Glue

variable {A B : Type u} [CommRing A] [CommRing B] (a : A) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)

/-- The glue condition at a point: a prime of `A_a`, pushed into the glued scheme through the
`A`-chart, is the image through the `B`-chart of its `θ`-translate. -/
theorem specTwoPatchι₀_base_comap_algebraMap (y : PrimeSpectrum (Localization.Away a)) :
    (specTwoPatchι₀ a b θ).base
        (PrimeSpectrum.comap (algebraMap A (Localization.Away a)) y) =
      (specTwoPatchι₁ a b θ).base
        (PrimeSpectrum.comap (algebraMap B (Localization.Away b))
          (PrimeSpectrum.comap θ.symm.toRingHom y)) := by
  have h := congrArg
    (fun m : Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away a)) ⟶
      specTwoPatch a b θ => m.base y) (specTwoPatch_glue a b θ)
  simp only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
    Function.comp_apply] at h
  exact h

/-- **The glue condition from the `B` side.** Compose `AlgebraicGeometry.specTwoPatch_glue`
(`FormalSchemes.CompletionTwoPatchToScheme`) with `specGlueIso.inv`; there is no need to redo the
`eqToHom` bookkeeping. -/
theorem specAwayMap_comp_specTwoPatchι₁ :
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap B (Localization.Away b))) ≫
        specTwoPatchι₁ a b θ =
      (specGlueIso a b θ).inv ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫
          specTwoPatchι₀ a b θ := by
  rw [specTwoPatch_glue a b θ, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- The glue condition at a point, from the `B` side. -/
theorem specTwoPatchι₁_base_comap_algebraMap (z : PrimeSpectrum (Localization.Away b)) :
    (specTwoPatchι₁ a b θ).base
        (PrimeSpectrum.comap (algebraMap B (Localization.Away b)) z) =
      (specTwoPatchι₀ a b θ).base
        (PrimeSpectrum.comap (algebraMap A (Localization.Away a))
          (PrimeSpectrum.comap θ.toRingHom z)) := by
  have h := congrArg
    (fun m : Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away b)) ⟶
      specTwoPatch a b θ => m.base z) (specAwayMap_comp_specTwoPatchι₁ a b θ)
  simp only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
    Function.comp_apply] at h
  exact h

end Glue

section Support

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (hI : I.FG) (a : A)
  (J : Ideal B) (hJ : J.FG) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

include hθ

/-- **The part of `Spec A` lying over the `B`-side of the completion is `V(I) ∩ D(a)`.** A prime
`p` of `A` with `ι₀(p) ∈ ι₁''V(J)` lies in `D(a)` by `preimage_range_specTwoPatchι₁`, hence comes
from a prime `y` of `A_a`; the glue condition identifies the corresponding prime of `B` as the
image of the `θ`-translate of `y`, and `hθ` turns "that translate lies in `V(J·B_b)`" into "`y`
lies in `V(I·A_a)`". This is where the compatibility hypothesis does its work. -/
theorem preimage_image_zeroLocus_specTwoPatchι₁ :
    ⇑(specTwoPatchι₀ a b θ).base ⁻¹'
        (⇑(specTwoPatchι₁ a b θ).base '' PrimeSpectrum.zeroLocus (J : Set B)) =
      PrimeSpectrum.zeroLocus (I : Set A) ∩ PrimeSpectrum.basicOpen a := by
  ext p
  constructor
  · rintro ⟨q, hq, hqe⟩
    have hpa : p ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
      rw [← preimage_range_specTwoPatchι₁ a b θ]
      exact ⟨q, hqe⟩
    obtain ⟨y, rfl⟩ :
        p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away a))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]
      exact hpa
    have hqy : q = PrimeSpectrum.comap (algebraMap B (Localization.Away b))
        (PrimeSpectrum.comap θ.symm.toRingHom y) :=
      (specTwoPatchι₁_isOpenImmersion a b θ).base_open.injective
        (hqe.trans (specTwoPatchι₀_base_comap_algebraMap a b θ y))
    rw [hqy] at hq
    have hy : y ∈ PrimeSpectrum.zeroLocus
        (I.map (algebraMap A (Localization.Away a)) : Set _) := by
      rw [← comap_θ_symm_preimage_zeroLocus I a J b θ hθ, Set.mem_preimage,
        zeroLocus_map_away_eq_preimage]
      exact hq
    rw [← image_zeroLocus_map_away I a]
    exact ⟨y, hy, rfl⟩
  · intro hp
    rw [← image_zeroLocus_map_away I a] at hp
    obtain ⟨y, hy, rfl⟩ := hp
    refine ⟨PrimeSpectrum.comap (algebraMap B (Localization.Away b))
      (PrimeSpectrum.comap θ.symm.toRingHom y), ?_,
      (specTwoPatchι₀_base_comap_algebraMap a b θ y).symm⟩
    have hmem : PrimeSpectrum.comap θ.symm.toRingHom y ∈
        PrimeSpectrum.zeroLocus (J.map (algebraMap B (Localization.Away b)) : Set _) := by
      rw [← Set.mem_preimage, comap_θ_symm_preimage_zeroLocus I a J b θ hθ]
      exact hy
    rw [zeroLocus_map_away_eq_preimage J b] at hmem
    exact hmem

/-- **The part of `Spec B` lying over the `A`-side of the completion is `V(J) ∩ D(b)`**, the mirror
of `preimage_image_zeroLocus_specTwoPatchι₁`. -/
theorem preimage_image_zeroLocus_specTwoPatchι₀ :
    ⇑(specTwoPatchι₁ a b θ).base ⁻¹'
        (⇑(specTwoPatchι₀ a b θ).base '' PrimeSpectrum.zeroLocus (I : Set A)) =
      PrimeSpectrum.zeroLocus (J : Set B) ∩ PrimeSpectrum.basicOpen b := by
  ext q
  constructor
  · rintro ⟨p, hp, hpe⟩
    have hqb : q ∈ (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) := by
      rw [← preimage_range_specTwoPatchι₀ a b θ]
      exact ⟨p, hpe⟩
    obtain ⟨z, rfl⟩ :
        q ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b]
      exact hqb
    have hpz : p = PrimeSpectrum.comap (algebraMap A (Localization.Away a))
        (PrimeSpectrum.comap θ.toRingHom z) :=
      (specTwoPatchι₀_isOpenImmersion a b θ).base_open.injective
        (hpe.trans (specTwoPatchι₁_base_comap_algebraMap a b θ z))
    rw [hpz] at hp
    have hz : z ∈ PrimeSpectrum.zeroLocus
        (J.map (algebraMap B (Localization.Away b)) : Set _) := by
      rw [← comap_θ_preimage_zeroLocus I a J b θ hθ, Set.mem_preimage,
        zeroLocus_map_away_eq_preimage]
      exact hp
    rw [← image_zeroLocus_map_away J b]
    exact ⟨z, hz, rfl⟩
  · intro hq
    rw [← image_zeroLocus_map_away J b] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    refine ⟨PrimeSpectrum.comap (algebraMap A (Localization.Away a))
      (PrimeSpectrum.comap θ.toRingHom z), ?_,
      (specTwoPatchι₁_base_comap_algebraMap a b θ z).symm⟩
    have hmem : PrimeSpectrum.comap θ.toRingHom z ∈
        PrimeSpectrum.zeroLocus (I.map (algebraMap A (Localization.Away a)) : Set _) := by
      rw [← Set.mem_preimage, comap_θ_preimage_zeroLocus I a J b θ hθ]
      exact hz
    rw [zeroLocus_map_away_eq_preimage I a] at hmem
    exact hmem

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
