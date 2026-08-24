import FormalSchemes.CompletionToSpec
import FormalSchemes.SpecTwoPatchNonAffine

set_option linter.style.header false

/-!
# The glued two-patch formal completion is genuinely glued (EGA I, 10.8)

`FormalSchemes/CompletionGlueTwoPatch.lean` glues the formal completions of two affine charts
`Spec A ⊇ V(I)` and `Spec B ⊇ V(J)` along the completion of their common basic open `D(a) ≅ D(b)`,
producing the formal scheme `completionTwoPatch`. `FormalSchemes/CompletionCompact.lean` records
that the result is quasi-compact and — as soon as `A ⧸ I` is nontrivial — nonempty. What neither
file says is that the glued object is any **bigger** than one of its patches.

This file supplies that. Its two statements are the completion-side counterparts of the first half
of `FormalSchemes/SpecTwoPatchNonAffine.lean`, and they are built from the same two bricks:
`LocallyRingedSpace.GlueData.range_ι_inter_subset` (`FormalSchemes.GlueDataImageInter`) and
`LocallyRingedSpace.range_eqToHom_comp_base`, which that file stated generally on the argument that
every `GlueData.ofGlueData'` consumer meets the same `eqToHom`. This is its second consumer.

## The two steps

**The gluing is proper.** `completionTwoPatchι₀_base_notMem_range_completionTwoPatchι₁`: a point of
`Spf A^` lying **outside** the completed basic open `D(â)` maps into the glued object outside the
range of the `B`-chart. So the two charts meet exactly over `D(â) ≅ D(b̂)` and nowhere else. This
holds for arbitrary `A`, `B`, `I`, `J`, `a`, `b`, `θ`. The hypothesis is supplied in
ring-theoretic form by `formalCompletion.notMem_range_basicOpenImmersion`: it is enough that the
point lie over a prime of `Spec A` containing `a`.

**The doubled formal point.** Taking `A = B`, `I = J`, `a = b`, `θ = RingEquiv.refl` gives
`completionDouble I hI a`, in which both charts are morphisms out of *the same* `Spf A^`. A point
outside `D(â)` then has two distinct images
(`completionDoubleι₀_base_ne_completionDoubleι₁_base`), and such a point exists as soon as
`I + (a)` is a proper ideal (`exists_completionDoubleι₀_base_ne_completionDoubleι₁_base`). This is
the first statement in this development that distinguishes a glued *formal* scheme from a single
chart.

## Scope: this does not prove `completionTwoPatch` is non-affine, and cannot yet

`FormalSchemes/SpecTwoPatchNonAffine.lean` gets from "the charts meet only over the overlap" to
"not affine" through `AlgebraicGeometry.ext_of_isDominant` and the instance
`[IsAffine X] → X.IsSeparated`. Both are Mathlib facts about **schemes**, and neither has a
counterpart here:

* there is no `IsAffine` predicate on `FormalScheme` at all;
* the only separatedness in this development is `BothChartedFibreDatumXY.IsSeparated`
  (`FormalSchemes/GeneralSeparated.lean`), which is relative to a chosen fibre-product
  presentation — one would have to be constructed for `completionDouble` first;
* and no topological argument can substitute. `Spf` of an adic ring is a spectral space
  (`FormalSpectrum.instSpectralSpace`), a finite gluing of spectral spaces along quasi-compact
  opens is again one, and every spectral space is homeomorphic to some `Spec`. **The underlying
  space cannot detect non-affineness.**

So `CompletionGlueTwoPatch.lean`'s claim that the glued completion "is not affine in general"
remains unsupported; this file narrows the gap without closing it. What is established is the
geometric fact underneath that claim.

## Main results

* `formalCompletion.notMem_range_basicOpenImmersion`: a point of `Spf R^` lying over a prime of
  `Spec R` containing `f` is outside the completed basic open `D(f̂)`.
* `formalCompletion.exists_toSpec_base_eq`: every prime of `Spec R` containing `I` is hit by
  `formalCompletion.toSpec`.
* `AlgebraicGeometry.range_completionTwoPatchLRSGlueData_f_false_true`: the `A`-side overlap
  inclusion of the two-patch completion glue datum has the same range as the basic-open completion
  immersion.
* `AlgebraicGeometry.completionTwoPatchι₀_base_notMem_range_completionTwoPatchι₁` and
  `..._of_mem`: **the charts meet only over the overlap**, for arbitrary `A`, `B`, `θ`.
* `AlgebraicGeometry.completionDouble`: `Spf A^` doubled along `D(â)`.
* `AlgebraicGeometry.completionDoubleι₀_base_ne_completionDoubleι₁_base` and
  `AlgebraicGeometry.exists_completionDoubleι₀_base_ne_completionDoubleι₁_base`: **the doubled
  formal point**, and a criterion for its existence.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 01KP](https://stacks.math.columbia.edu/tag/01KP) (the line with doubled
  origin, whose formal-scheme avatar is the `I = ⊥` witness at the end of this file).
-/

noncomputable section

open CategoryTheory

universe u

namespace formalCompletion

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (f : R)

/-- **A point of `Spf R^` lying over a prime containing `f` is outside `D(f̂)`.** The range of the
basic-open completion immersion is `D(f̂)` (`range_basicOpenImmersion`), and the base map of
`toSpec` is `Spec` of the residue map `R →+* R^ ⧸ I·R^` (`toSpec_base_eq_comap`), which sends `f`
to the residue of `f̂`; so lying over a prime containing `f` is exactly failing to be in `D(f̂)`. -/
theorem notMem_range_basicOpenImmersion
    (x : FormalSpectrum (AdicCompletion.idealOfDefinition I))
    (hx : f ∈ ((toSpec R I hI).base x).asIdeal) :
    x ∉ Set.range (basicOpenImmersion I hI f).toLRSHom.base := by
  rw [range_basicOpenImmersion]
  rw [toSpec_base_eq_comap] at hx
  intro hmem
  exact (FormalSpectrum.mem_basicOpen _ _ _).mp hmem hx

/-- **Every prime of `Spec R` containing `I` comes from a point of the completion.** This is
`range_toSpec_base` — the image of `toSpec` is `V(I)` — read as an existence statement. -/
theorem exists_toSpec_base_eq {p : PrimeSpectrum R} (hp : I ≤ p.asIdeal) :
    ∃ x : FormalSpectrum (AdicCompletion.idealOfDefinition I), (toSpec R I hI).base x = p := by
  have hmem : p ∈ Set.range ⇑(toSpec R I hI).base := by
    rw [range_toSpec_base R I hI]
    exact hp
  exact hmem

end formalCompletion

namespace AlgebraicGeometry

section TwoCharts

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (hI : I.FG) (a : A)
  (J : Ideal B) (hJ : J.FG) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

/-- The two indices of the two-patch completion glue datum are distinct. -/
private theorem cpIdxNe : ¬ @Eq (ULift.{u} Bool) ⟨false⟩ ⟨true⟩ := by simp

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- The transparency requirement is the one documented on the `Spec` side: the glue datum is a
-- `def`, so its index type does not reduce to `ULift Bool` at `instances` transparency and the
-- rewrite below is otherwise rejected as ill-typed.
/-- **The `A`-side overlap inclusion of the two-patch completion glue datum is the basic-open
completion immersion.** The `eqToHom` that `GlueData.ofGlueData'` inserts is invisible to the
range. -/
theorem range_completionTwoPatchLRSGlueData_f_false_true :
    Set.range ((completionTwoPatchLRSGlueData I hI a J hJ b θ hθ).toGlueData.f
        ⟨false⟩ ⟨true⟩).base =
      Set.range (formalCompletion.basicOpenImmersion I hI a).toLRSHom.base := by
  have h : (completionTwoPatchLRSGlueData I hI a J hJ b θ hθ).toGlueData.f ⟨false⟩ ⟨true⟩ =
      eqToHom (dif_neg cpIdxNe) ≫ (formalCompletion.basicOpenImmersion I hI a).toLRSHom :=
    dif_neg cpIdxNe
  rw [h, LocallyRingedSpace.range_eqToHom_comp_base]
  rfl

/-- **The two charts of the glued completion meet only over the overlap.** A point of `Spf A^`
outside the completed basic open `D(â)` maps into `completionTwoPatch` outside the range of the
`B`-chart. Together with `completionTwoPatch_jointly_surjective` this pins down the gluing: it
happens along `D(â) ≅ D(b̂)` and nowhere else. -/
theorem completionTwoPatchι₀_base_notMem_range_completionTwoPatchι₁
    (x : (formalCompletion A I hI).toLocallyRingedSpace)
    (hx : x ∉ Set.range (formalCompletion.basicOpenImmersion I hI a).toLRSHom.base) :
    (completionTwoPatchι₀ I hI a J hJ b θ hθ).base x ∉
      Set.range (completionTwoPatchι₁ I hI a J hJ b θ hθ).base := by
  rintro ⟨y, hy⟩
  obtain ⟨w, hw⟩ := (completionTwoPatchLRSGlueData I hI a J hJ b θ hθ).range_ι_inter_subset
    ⟨false⟩ ⟨true⟩
    (⟨⟨x, rfl⟩, ⟨y, hy⟩⟩ :
      (completionTwoPatchι₀ I hI a J hJ b θ hθ).base x ∈
        Set.range (completionTwoPatchι₀ I hI a J hJ b θ hθ).base ∩
          Set.range (completionTwoPatchι₁ I hI a J hJ b θ hθ).base)
  refine hx ?_
  rw [← range_completionTwoPatchLRSGlueData_f_false_true I hI a J hJ b θ hθ]
  exact ⟨w, (completionTwoPatchι₀_isOpenImmersion I hI a J hJ b θ hθ).base_open.injective hw⟩

/-- **The two charts of the glued completion meet only over the overlap**, phrased
ring-theoretically: a point of `Spf A^` lying over a prime of `Spec A` containing `a` maps outside
the range of the `B`-chart. -/
theorem completionTwoPatchι₀_base_notMem_range_completionTwoPatchι₁_of_mem
    (x : FormalSpectrum (AdicCompletion.idealOfDefinition I))
    (hx : a ∈ ((formalCompletion.toSpec A I hI).base x).asIdeal) :
    (completionTwoPatchι₀ I hI a J hJ b θ hθ).base x ∉
      Set.range (completionTwoPatchι₁ I hI a J hJ b θ hθ).base :=
  completionTwoPatchι₀_base_notMem_range_completionTwoPatchι₁ I hI a J hJ b θ hθ x
    (formalCompletion.notMem_range_basicOpenImmersion I hI a x hx)

end TwoCharts

section Double

variable {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG) (a : A)

/-- **`Spf A^` doubled along the completed basic open `D(â)`**: the two-patch glued completion with
both charts equal to `Spf A^`, glued along the identity of `A_a`. For `A = ℚ[X]`, `I = ⊥`, `a = X`
this is the affine line with a doubled origin, as a formal scheme. -/
abbrev completionDouble : FormalScheme.{u} :=
  completionTwoPatch I hI a I hI a (RingEquiv.refl (Localization.Away a)) (Ideal.map_id _)

/-- **The doubled formal point.** A point of `Spf A^` lying over a prime of `Spec A` containing `a`
has two distinct images in `completionDouble I hI a`, one from each chart. -/
theorem completionDoubleι₀_base_ne_completionDoubleι₁_base
    (x : FormalSpectrum (AdicCompletion.idealOfDefinition I))
    (hx : a ∈ ((formalCompletion.toSpec A I hI).base x).asIdeal) :
    (completionTwoPatchι₀ I hI a I hI a (RingEquiv.refl (Localization.Away a))
        (Ideal.map_id _)).base x ≠
      (completionTwoPatchι₁ I hI a I hI a (RingEquiv.refl (Localization.Away a))
        (Ideal.map_id _)).base x := fun h =>
  completionTwoPatchι₀_base_notMem_range_completionTwoPatchι₁_of_mem I hI a I hI a _ _ x hx
    ⟨x, h.symm⟩

/-- **A doubled point exists whenever `I + (a)` is a proper ideal**: it is then contained in a
maximal ideal, which is a prime containing both `I` — so that it comes from a point of `Spf A^` —
and `a`. -/
theorem exists_completionDoubleι₀_base_ne_completionDoubleι₁_base
    (h : I ⊔ Ideal.span {a} ≠ ⊤) :
    ∃ x : FormalSpectrum (AdicCompletion.idealOfDefinition I),
      (completionTwoPatchι₀ I hI a I hI a (RingEquiv.refl (Localization.Away a))
          (Ideal.map_id _)).base x ≠
        (completionTwoPatchι₁ I hI a I hI a (RingEquiv.refl (Localization.Away a))
          (Ideal.map_id _)).base x := by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  obtain ⟨x, hx⟩ := formalCompletion.exists_toSpec_base_eq I hI
    (p := ⟨m, hm.isPrime⟩) (le_sup_left.trans hle)
  refine ⟨x, completionDoubleι₀_base_ne_completionDoubleι₁_base I hI a x ?_⟩
  rw [hx]
  exact hle ((le_sup_right : Ideal.span {a} ≤ I ⊔ Ideal.span {a})
    (Ideal.mem_span_singleton_self a))

end Double

/-! ### Two witnesses, of deliberately different geometry

Both are `A = ℚ[X]`, `a = X`. They differ in the ideal one completes along, and hence in whether
the gluing is along a nonempty overlap: at `I = ⊥` the completion is `Spec ℚ[X]` itself and `D(X̂)`
is nonempty, so `completionDouble` is the affine line with a doubled origin; at `I = (X)` the
completion is the one-point space `Spf ℚ[[X]]` and `D(X̂)` is empty, so `completionDouble` is a
disjoint union of two formal discs. The doubled point exists in both cases, and a reader who saw
only the second would take the result to be about disjoint unions. -/

section Witnesses

open Polynomial

/-- **The affine line over `ℚ` with a doubled origin, as a formal scheme.** Completing along
`V(⊥) = Spec ℚ[X]` changes nothing, so this is the same object
`FormalSchemes.SpecTwoPatchNonAffine` exhibits as a scheme — here the two halves of the doubled
origin are seen to be distinct points, over a **nonempty** overlap `D(X̂)`. -/
example : ∃ x : FormalSpectrum (AdicCompletion.idealOfDefinition (⊥ : Ideal ℚ[X])),
    (completionTwoPatchι₀ (⊥ : Ideal ℚ[X]) Submodule.fg_bot X (⊥ : Ideal ℚ[X]) Submodule.fg_bot X
        (RingEquiv.refl _) (Ideal.map_id _)).base x ≠
      (completionTwoPatchι₁ (⊥ : Ideal ℚ[X]) Submodule.fg_bot X (⊥ : Ideal ℚ[X]) Submodule.fg_bot X
        (RingEquiv.refl _) (Ideal.map_id _)).base x :=
  exists_completionDoubleι₀_base_ne_completionDoubleι₁_base _ Submodule.fg_bot X (by
    rw [bot_sup_eq]
    exact (Ideal.span_singleton_eq_top (x := (X : ℚ[X]))).not.mpr not_isUnit_X)

/-- **The doubled formal disc.** Completing `ℚ[X]` along `V(X)` gives the one-point space
`Spf ℚ[[X]]`, on which `D(X̂)` is **empty**; the glued object is the disjoint union of two formal
discs, and its two points are the two images of the unique point of `Spf ℚ[[X]]`. -/
example : ∃ x : FormalSpectrum (AdicCompletion.idealOfDefinition (Ideal.span {(X : ℚ[X])})),
    (completionTwoPatchι₀ (Ideal.span {(X : ℚ[X])}) (Submodule.fg_span (Set.finite_singleton _)) X
        (Ideal.span {(X : ℚ[X])}) (Submodule.fg_span (Set.finite_singleton _)) X
        (RingEquiv.refl _) (Ideal.map_id _)).base x ≠
      (completionTwoPatchι₁ (Ideal.span {(X : ℚ[X])}) (Submodule.fg_span (Set.finite_singleton _)) X
        (Ideal.span {(X : ℚ[X])}) (Submodule.fg_span (Set.finite_singleton _)) X
        (RingEquiv.refl _) (Ideal.map_id _)).base x :=
  exists_completionDoubleι₀_base_ne_completionDoubleι₁_base _
    (Submodule.fg_span (Set.finite_singleton _)) X (by
      rw [sup_idem]
      exact (Ideal.span_singleton_eq_top (x := (X : ℚ[X]))).not.mpr not_isUnit_X)

end Witnesses

end AlgebraicGeometry
