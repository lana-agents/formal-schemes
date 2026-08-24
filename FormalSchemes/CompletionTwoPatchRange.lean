import FormalSchemes.CompletionTwoPatchToScheme
import FormalSchemes.SpecTwoPatchNonAffine

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
the affine range lemma on each. Two non-degeneracy statements come with it, and neither is
optional — without them the displayed equality is compatible both with the range being everything
and with `completionTwoPatch` being secretly a single chart:

* the image is a **proper** subset: a prime of `A` containing `a` but not containing `I` gives a
  point of `specTwoPatch` outside it (`notMem_range_completionTwoPatchToScheme_base`), and the
  affine line over `ℚ` completed along the point `1` is a concrete instance;
* the glued completion really is glued from **two** pieces: its charts meet only over their
  overlap (`completionTwoPatchι₀_base_notMem_range_completionTwoPatchι₁`), so a point outside the
  overlap has two distinct images — the *doubled formal point*, the completion-side analogue of
  `specTwoPatchSchemeι₀_base_ne_specTwoPatchSchemeι₁_base` in
  `FormalSchemes.SpecTwoPatchNonAffine`.

Along the way, `range_basicOpenImmersion_eq_empty` records that the overlap chart of the glued
completion is *empty* as soon as `a ∈ I`: if the gluing locus `D(a)` misses the closed subset
`V(I)`, the glued formal completion is the disjoint union of the two affine ones. That is what
makes the doubled formal point cheap to exhibit.

## Scope

The **closed-embedding** half is not attempted. Closedness of the range is local on the two-chart
cover and reduces to

```
ι₀⁻¹(ι₀ '' V(I) ∪ ι₁ '' V(J)) = V(I) ∪ (V(I) ∩ D(a)) = V(I),
```

whose middle equality is the first place the compatibility hypothesis `hθ` would actually be used:
a prime of `V(J) ∩ D(b)` corresponds under `θ` to one of `V(I·A_a) = V(I) ∩ D(a)`. That transport
— from `hθ`, an equality of ideals in the localizations, to a statement about primes — does not
exist in this development, and none of the results below need it: the proof of
`range_completionTwoPatchToScheme_base` never mentions `hθ`. Injectivity of the base map is
likewise left open; its mixed-chart case needs the converse of
`completionTwoPatchι₀_base_notMem_range_completionTwoPatchι₁`, which is a separate compatibility.

## Main results

* `AlgebraicGeometry.completionTwoPatchToScheme_base_ι₀` and `..._ι₁`: the base map of the
  canonical morphism on each completion chart.
* `AlgebraicGeometry.range_completionTwoPatchToScheme_base`: **the image is the glued closed
  subset.**
* `AlgebraicGeometry.notMem_range_completionTwoPatchToScheme_base`: **and it is a proper subset.**
* `AlgebraicGeometry.range_completionTwoPatchFormalGlueData_f_false_true` and
  `AlgebraicGeometry.completionTwoPatchι₀_base_notMem_range_completionTwoPatchι₁`: the two charts
  of the glued completion meet only over the overlap.
* `formalCompletion.basicOpen_awayPoint_eq_bot` and
  `formalCompletion.range_basicOpenImmersion_eq_empty`: the overlap chart is empty when `a ∈ I`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace formalCompletion

variable {R : Type u} [CommRing R] (I : Ideal R) (f : R)

/-- **An element of the ideal has empty basic open in the formal spectrum.** The residue of
`awayPoint I f = algebraMap R R^ f` modulo the ideal of definition is `0` precisely because
`f` lies in the kernel of `formalCompletion.residueMap`, which is `I`. -/
theorem basicOpen_awayPoint_eq_bot (hI : I.FG) (hf : f ∈ I) :
    FormalSpectrum.basicOpen (AdicCompletion.idealOfDefinition I)
      (AdicCompletion.awayPoint I f) = ⊥ := by
  have h0 : Ideal.Quotient.mk (AdicCompletion.idealOfDefinition I)
      (AdicCompletion.awayPoint I f) = 0 := by
    have h : residueMap R I f = 0 := by
      rw [← RingHom.mem_ker, ker_residueMap R I hI]
      exact hf
    exact h
  change PrimeSpectrum.basicOpen (Ideal.Quotient.mk (AdicCompletion.idealOfDefinition I)
    (AdicCompletion.awayPoint I f)) = ⊥
  rw [h0]
  exact PrimeSpectrum.basicOpen_zero

/-- **If the basic open `D(f)` misses the closed subset `V(I)`, the basic-open chart of the
completion is empty.** Its range is `D(f̂)` (`range_basicOpenImmersion`), and `f ∈ I` makes `f̂`
residually zero. Geometrically: completing along `V(I)` sees nothing of `D(f)`. -/
theorem range_basicOpenImmersion_eq_empty (hI : I.FG) (hf : f ∈ I) :
    Set.range (basicOpenImmersion I hI f).toLRSHom.base = ∅ := by
  rw [range_basicOpenImmersion, basicOpen_awayPoint_eq_bot I f hI hf]
  simp
  rfl

end formalCompletion

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

/-! ### The glued completion is glued from two pieces -/

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- The same transparency requirement as `completionTwoPatch_glue_condition₀` in
-- `FormalSchemes.CompletionGlueTwoPatchCondition`: the datum's index type reduces to `ULift Bool`
-- only past `instances` transparency, so the rewrite below is otherwise rejected as ill-typed.
/-- **The `A`-side overlap inclusion of the completion glue datum is the basic-open chart.** Its
range on underlying spaces is that of `formalCompletion.basicOpenImmersion`; the `eqToHom` that
`GlueData.ofGlueData'` inserts is invisible to a range. -/
theorem range_completionTwoPatchFormalGlueData_f_false_true :
    Set.range ((completionTwoPatchFormalGlueData I hI a J hJ b θ
        hθ).toLocallyRingedSpaceGlueData.toGlueData.f ⟨false⟩ ⟨true⟩).base =
      Set.range (formalCompletion.basicOpenImmersion I hI a).toLRSHom.base := by
  rw [completionTwoPatchFormalGlueData_f_false_true,
    LocallyRingedSpace.range_eqToHom_comp_base]
  rfl

/-- **The two charts of the glued completion meet only over the overlap.** A point of `Spf A^`
outside the basic-open chart `D(â)` maps into `completionTwoPatch` outside the range of the
`B`-chart. This is the completion-side analogue of
`specTwoPatchι₀_base_notMem_range_specTwoPatchι₁`, and together with
`completionTwoPatch_jointly_surjective` it pins the gluing down: it happens along `D(â) ≅ D(b̂)`
and nowhere else. -/
theorem completionTwoPatchι₀_base_notMem_range_completionTwoPatchι₁
    (x : (formalCompletion A I hI).toLocallyRingedSpace)
    (hx : x ∉ Set.range (formalCompletion.basicOpenImmersion I hI a).toLRSHom.base) :
    (completionTwoPatchι₀ I hI a J hJ b θ hθ).base x ∉
      Set.range (completionTwoPatchι₁ I hI a J hJ b θ hθ).base := by
  rintro ⟨y, hy⟩
  obtain ⟨w, hw⟩ := (completionTwoPatchFormalGlueData I hI a J hJ b θ
      hθ).toLocallyRingedSpaceGlueData.range_ι_inter_subset ⟨false⟩ ⟨true⟩
    (⟨⟨x, rfl⟩, ⟨y, hy⟩⟩ :
      (completionTwoPatchι₀ I hI a J hJ b θ hθ).base x ∈
        Set.range (completionTwoPatchι₀ I hI a J hJ b θ hθ).base ∩
          Set.range (completionTwoPatchι₁ I hI a J hJ b θ hθ).base)
  refine hx ?_
  rw [← range_completionTwoPatchFormalGlueData_f_false_true I hI a J hJ b θ hθ]
  exact ⟨w, (completionTwoPatchι₀_isOpenImmersion I hI a J hJ b θ hθ).base_open.injective hw⟩

/-- **The doubled formal point.** When the gluing element lies in the ideal one completes along,
the overlap of the glued completion is empty (`formalCompletion.range_basicOpenImmersion_eq_empty`)
and hence *every* point of the `A`-chart has two distinct images in `completionTwoPatch`. So the
glued formal completion is not a single chart in disguise. -/
theorem completionTwoPatchι₀_base_ne_completionTwoPatchι₁_base (ha : a ∈ I)
    (x : (formalCompletion A I hI).toLocallyRingedSpace) :
    (completionTwoPatchι₀ I hI a I hI a (RingEquiv.refl (Localization.Away a))
        (Ideal.map_id _)).base x ≠
      (completionTwoPatchι₁ I hI a I hI a (RingEquiv.refl (Localization.Away a))
        (Ideal.map_id _)).base x := fun h =>
  completionTwoPatchι₀_base_notMem_range_completionTwoPatchι₁ I hI a I hI a _ _ x
    (by rw [formalCompletion.range_basicOpenImmersion_eq_empty I a hI ha]; exact Set.notMem_empty x)
    ⟨x, h.symm⟩

/-! ### Two concrete witnesses

Both take `A = B = ℚ[X]`, so that the ambient glued scheme is a doubling of the affine line over
`ℚ`, and both are non-degeneracy checks on the results above rather than new mathematics. -/

section Witnesses

open Polynomial

/-- The origin of `𝔸¹_ℚ`, as a point of `Spec ℚ[X]`. -/
private def originQX : PrimeSpectrum (ℚ[X]) :=
  ⟨Ideal.span {(X : ℚ[X])}, (Ideal.span_singleton_prime X_ne_zero).mpr prime_X⟩

private theorem span_X_fg : (Ideal.span {(X : ℚ[X])}).FG :=
  Submodule.fg_span (Set.finite_singleton _)

private theorem span_X_sub_C_fg : (Ideal.span {(X - C (1 : ℚ))}).FG :=
  Submodule.fg_span (Set.finite_singleton _)

/-- The origin does not lie on `V(X - 1)`: evaluating a putative factorisation at `0` gives
`-1 = 0` in `ℚ`. -/
private theorem originQX_notMem_zeroLocus :
    originQX ∉
      PrimeSpectrum.zeroLocus ((Ideal.span {(X - C (1 : ℚ))} : Ideal ℚ[X]) : Set ℚ[X]) := by
  intro hmem
  have hdvd : (X : ℚ[X]) ∣ X - C (1 : ℚ) :=
    Ideal.mem_span_singleton.mp (hmem (Ideal.mem_span_singleton_self _))
  obtain ⟨q, hq⟩ := hdvd
  have := congrArg (Polynomial.eval (0 : ℚ)) hq
  simp at this

/-- **The completion is a proper part of the glued scheme**, concretely: doubling `𝔸¹_ℚ` along
`D(X)` and completing along the point `1` on each chart, the origin of the first chart is a point
of the glued scheme that the formal completion does not reach. -/
example : (specTwoPatchι₀ (X : ℚ[X]) X (RingEquiv.refl (Localization.Away (X : ℚ[X])))).base
      originQX ∉
    Set.range ⇑(completionTwoPatchToScheme (Ideal.span {(X - C (1 : ℚ))}) span_X_sub_C_fg
      (X : ℚ[X]) (Ideal.span {(X - C (1 : ℚ))}) span_X_sub_C_fg (X : ℚ[X])
      (RingEquiv.refl (Localization.Away (X : ℚ[X]))) (Ideal.map_id _)).base :=
  notMem_range_completionTwoPatchToScheme_base _ span_X_sub_C_fg _ _ span_X_sub_C_fg _ _ _
    (Ideal.mem_span_singleton_self _) originQX_notMem_zeroLocus

/-- **The glued completion really has two charts**, concretely: doubling `𝔸¹_ℚ` along `D(X)` and
completing along the origin `V(X)` — where the gluing locus misses the closed subset entirely —
every point of the first chart is doubled. -/
example (x : (formalCompletion ℚ[X] (Ideal.span {(X : ℚ[X])}) span_X_fg).toLocallyRingedSpace) :
    (completionTwoPatchι₀ (Ideal.span {(X : ℚ[X])}) span_X_fg (X : ℚ[X])
        (Ideal.span {(X : ℚ[X])}) span_X_fg (X : ℚ[X])
        (RingEquiv.refl (Localization.Away (X : ℚ[X]))) (Ideal.map_id _)).base x ≠
      (completionTwoPatchι₁ (Ideal.span {(X : ℚ[X])}) span_X_fg (X : ℚ[X])
        (Ideal.span {(X : ℚ[X])}) span_X_fg (X : ℚ[X])
        (RingEquiv.refl (Localization.Away (X : ℚ[X]))) (Ideal.map_id _)).base x :=
  completionTwoPatchι₀_base_ne_completionTwoPatchι₁_base _ span_X_fg _
    (Ideal.mem_span_singleton_self _) x

end Witnesses

end AlgebraicGeometry
