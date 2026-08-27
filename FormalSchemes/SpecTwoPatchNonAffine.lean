import FormalSchemes.GlueDataImageInter
import FormalSchemes.SpecTwoPatchScheme
import FormalSchemes.TwoPatchWitness
import Mathlib.AlgebraicGeometry.Morphisms.Separated

set_option linter.style.header false

/-!
# The two-patch glued scheme is genuinely glued, and the doubled `Spec A` is not affine

`FormalSchemes/CompletionTwoPatchToScheme.lean` builds `specTwoPatch a b θ`, the locally ringed
space `Spec A ∪_{D(a) ≅ D(b)} Spec B`, and `FormalSchemes/SpecTwoPatchScheme.lean` promotes it to
an `AlgebraicGeometry.Scheme` with a two-chart affine open cover. Both files' module docstrings
stop short of calling the result a **non-affine** scheme, and say why: the only witness either of
them instantiates is `A = B`, `a = b`, `θ = RingEquiv.refl`, the "doubled" `Spec A`, which for
`A = k[t]`, `a = t` is the affine line with a doubled origin — genuinely non-affine and
non-separated, but nothing there proves it. This file closes that gap.

## The two steps

**The gluing is proper.** `specTwoPatchι₀_base_notMem_range_specTwoPatchι₁`: a point of `Spec A`
lying **outside** the basic open `D(a)` maps into the glued space outside the range of the
`B`-chart. So the two charts meet exactly over `D(a) ≅ D(b)` and nowhere else, and — taking
`A = B`, `a = b`, `θ = refl` — the two images of such a point are **two distinct points** of the
glued scheme (`specTwoPatchSchemeι₀_base_ne_specTwoPatchSchemeι₁_base`). This is the doubled
origin, and it is the first statement in this development that distinguishes the glued object from
a single chart. The input is `LocallyRingedSpace.GlueData.range_ι_inter_subset`
(`FormalSchemes.GlueDataImageInter`) together with the identification of the glue datum's overlap
inclusion with `Spec` of the localization map, `range_specTwoPatchLRSGlueData_f_false_true`. Both
statements are available in either index order; the `B`-side mirrors carry the primed index
distinctness `spidxNe'` and are otherwise line-for-line the same proofs.

**Hence not separated, hence not affine.** Write `specDouble a` for `specTwoPatchScheme a a
(RingEquiv.refl _)`. The two charts `specTwoPatchSchemeι₀`, `specTwoPatchSchemeι₁` are then two
morphisms `Spec A ⟶ specDouble a` *with the same source*, and `specTwoPatch_glue` at `θ = refl`
says they agree after restriction along `Spec A_a ⟶ Spec A`. For `A` a domain and `a ≠ 0` that
restriction is **dominant** (its range is `D(a)`, dense because the kernel of `A → A_a` is
trivial), and `Spec A` is reduced. Mathlib's `AlgebraicGeometry.ext_of_isDominant` — two morphisms
out of a reduced scheme into a **separated** scheme agreeing along a dominant map are equal — would
therefore force the two charts to coincide, contradicting the doubled point. So `specDouble a` is
not separated (`not_isSeparated_specDouble`), and since affine schemes are separated it is not
affine (`not_isAffine_specDouble`).

The concrete witness at the end of the file is `A = ℚ[X]`, `a = X`: **the affine line over `ℚ`
with a doubled origin is a scheme that is not separated and not affine.**

## Scope

The non-affineness argument needs the two charts to have a **common source**, so it is stated for
the doubled case `A = B`, `a = b`, `θ = refl` only. That is not a defect of the proof: for general
`A`, `B`, `θ` there need be no morphism `Spec A ⟶ specTwoPatch a b θ` extending the `B`-chart, and
the glued scheme can perfectly well be affine (take `a` a unit, so that `D(a) = Spec A` and the
gluing is an isomorphism). The *first* half — that the charts meet only over the overlap — is
proved at full generality in `A`, `B`, `θ`.

Nothing here computes `Γ(specDouble a, 𝒪)`, and nothing here is needed to: the separatedness route
avoids global sections entirely. The classical argument via `Γ` (sections glue to `A`, so an
isomorphism with `Spec A` would have to identify the two doubled points) remains unformalised and
is not required for the conclusion.

## Main results

* `AlgebraicGeometry.range_specTwoPatchLRSGlueData_f_false_true` and
  `AlgebraicGeometry.range_specTwoPatchLRSGlueData_f_true_false`: the two overlap inclusions of the
  two-patch glue datum have the same ranges as `Spec` of `A → A_a` and of `B → B_b`, i.e. `D(a)`
  and `D(b)`.
* `AlgebraicGeometry.specTwoPatchι₀_base_notMem_range_specTwoPatchι₁` and
  `AlgebraicGeometry.specTwoPatchι₁_base_notMem_range_specTwoPatchι₀`: **the charts meet only over
  the overlap**, at the level of locally ringed spaces, for arbitrary `A`, `B`, `θ`, from either
  side.
* `AlgebraicGeometry.specTwoPatchSchemeι₀_base_notMem_range_specTwoPatchSchemeι₁`,
  `AlgebraicGeometry.specTwoPatchSchemeι₁_base_notMem_range_specTwoPatchSchemeι₀` and
  `..._base_ne_specTwoPatchSchemeι₁_base`: the same at the level of schemes, and **the doubled
  point**.
* `AlgebraicGeometry.specDouble`: `Spec A` doubled along `D(a)`.
* `AlgebraicGeometry.not_isSeparated_specDouble`, `AlgebraicGeometry.not_isAffine_specDouble` and
  their `¬ IsUnit a` corollaries: **the doubled `Spec A` is neither separated nor affine.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 01KP](https://stacks.math.columbia.edu/tag/01KP) (the line with doubled
  origin).
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- Precomposing with an `eqToHom` does not change the range on underlying spaces: the `eqToHom` is
an isomorphism, so its base map is surjective. Used to discard the `GlueData.ofGlueData'`
bookkeeping in `range_specTwoPatchLRSGlueData_f_false_true`. -/
theorem LocallyRingedSpace.range_eqToHom_comp_base {X Y Z : LocallyRingedSpace.{u}} (e : X = Y)
    (φ : Y ⟶ Z) : Set.range (eqToHom e ≫ φ).base = Set.range φ.base := by
  subst e
  simp

section TwoCharts

variable {A B : Type u} [CommRing A] [CommRing B] (a : A) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)

/-- The two indices of the two-patch glue datum are distinct. -/
private theorem spidxNe : ¬ @Eq (ULift.{u} Bool) ⟨false⟩ ⟨true⟩ := by simp

/-- …and in the other order, for the `B`-side statements. -/
private theorem spidxNe' : ¬ @Eq (ULift.{u} Bool) ⟨true⟩ ⟨false⟩ := by simp

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- The same transparency requirement as `specTwoPatch_glue` in
-- `FormalSchemes.CompletionTwoPatchToScheme`: the glue datum is a `def`, so its index type does not
-- reduce to `ULift Bool` at `instances` transparency and the rewrite below is otherwise rejected as
-- ill-typed.
/-- **The `A`-side overlap inclusion of the two-patch glue datum is the localization chart.**
Its range on underlying spaces is that of `Spec` of `A → A_a`, namely the basic open `D(a)`; the
`eqToHom` that `GlueData.ofGlueData'` inserts is invisible to the range. -/
theorem range_specTwoPatchLRSGlueData_f_false_true :
    Set.range ((specTwoPatchLRSGlueData a b θ).toGlueData.f ⟨false⟩ ⟨true⟩).base =
      Set.range (Spec.locallyRingedSpaceMap
        (CommRingCat.ofHom (algebraMap A (Localization.Away a)))).base := by
  have h : (specTwoPatchLRSGlueData a b θ).toGlueData.f ⟨false⟩ ⟨true⟩ =
      eqToHom (dif_neg spidxNe) ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap A (Localization.Away a))) :=
    dif_neg spidxNe
  rw [h, LocallyRingedSpace.range_eqToHom_comp_base]
  rfl

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- The transparency requirement is the same one `range_specTwoPatchLRSGlueData_f_false_true` needs,
-- and for the same reason: the glue datum is a `def`, so its index type does not reduce to
-- `ULift Bool` at `instances` transparency.
/-- **The `B`-side overlap inclusion of the two-patch glue datum is the localization chart.**
The mirror of `range_specTwoPatchLRSGlueData_f_false_true` with the two indices exchanged: the
range of `f ⟨true⟩ ⟨false⟩` on underlying spaces is that of `Spec` of `B → B_b`, namely `D(b)`. -/
theorem range_specTwoPatchLRSGlueData_f_true_false :
    Set.range ((specTwoPatchLRSGlueData a b θ).toGlueData.f ⟨true⟩ ⟨false⟩).base =
      Set.range (Spec.locallyRingedSpaceMap
        (CommRingCat.ofHom (algebraMap B (Localization.Away b)))).base := by
  have h : (specTwoPatchLRSGlueData a b θ).toGlueData.f ⟨true⟩ ⟨false⟩ =
      eqToHom (dif_neg spidxNe') ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap B (Localization.Away b))) :=
    dif_neg spidxNe'
  rw [h, LocallyRingedSpace.range_eqToHom_comp_base]
  rfl

/-- **The two charts of the glued object meet only over the overlap.** A point of `Spec A` outside
the range of `Spec A_a ⟶ Spec A` — that is, outside the basic open `D(a)` — maps into
`specTwoPatch a b θ` outside the range of the `B`-chart. Together with
`specTwoPatch_jointly_surjective` this pins down the gluing: it happens along `D(a) ≅ D(b)` and
nowhere else. -/
theorem specTwoPatchι₀_base_notMem_range_specTwoPatchι₁ (x : PrimeSpectrum A)
    (hx : x ∉ Set.range (Spec.locallyRingedSpaceMap
      (CommRingCat.ofHom (algebraMap A (Localization.Away a)))).base) :
    (specTwoPatchι₀ a b θ).base x ∉ Set.range (specTwoPatchι₁ a b θ).base := by
  rintro ⟨y, hy⟩
  obtain ⟨w, hw⟩ := (specTwoPatchLRSGlueData a b θ).range_ι_inter_subset ⟨false⟩ ⟨true⟩
    (⟨⟨x, rfl⟩, ⟨y, hy⟩⟩ :
      (specTwoPatchι₀ a b θ).base x ∈
        Set.range (specTwoPatchι₀ a b θ).base ∩ Set.range (specTwoPatchι₁ a b θ).base)
  refine hx ?_
  rw [← range_specTwoPatchLRSGlueData_f_false_true a b θ]
  exact ⟨w, (specTwoPatchι₀_isOpenImmersion a b θ).base_open.injective hw⟩

/-- **…and from the other side**: a point of `Spec B` outside `D(b)` maps into
`specTwoPatch a b θ` outside the range of the `A`-chart. The mirror of
`specTwoPatchι₀_base_notMem_range_specTwoPatchι₁`, proved the same way from
`range_specTwoPatchLRSGlueData_f_true_false`. -/
theorem specTwoPatchι₁_base_notMem_range_specTwoPatchι₀ (x : PrimeSpectrum B)
    (hx : x ∉ Set.range (Spec.locallyRingedSpaceMap
      (CommRingCat.ofHom (algebraMap B (Localization.Away b)))).base) :
    (specTwoPatchι₁ a b θ).base x ∉ Set.range (specTwoPatchι₀ a b θ).base := by
  rintro ⟨y, hy⟩
  obtain ⟨w, hw⟩ := (specTwoPatchLRSGlueData a b θ).range_ι_inter_subset ⟨true⟩ ⟨false⟩
    (⟨⟨x, rfl⟩, ⟨y, hy⟩⟩ :
      (specTwoPatchι₁ a b θ).base x ∈
        Set.range (specTwoPatchι₁ a b θ).base ∩ Set.range (specTwoPatchι₀ a b θ).base)
  refine hx ?_
  rw [← range_specTwoPatchLRSGlueData_f_true_false a b θ]
  exact ⟨w, (specTwoPatchι₁_isOpenImmersion a b θ).base_open.injective hw⟩

/-- The range of `Spec A_a ⟶ Spec A` is the basic open `D(a)`, so a prime containing `a` is not in
it. -/
theorem notMem_range_specAwayMap {x : PrimeSpectrum A} (hx : a ∈ x.asIdeal) :
    x ∉ Set.range (Spec.locallyRingedSpaceMap
      (CommRingCat.ofHom (algebraMap A (Localization.Away a)))).base := by
  change x ∉ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away a)))
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]
  simpa using hx

/-- **The two charts of the glued scheme meet only over the overlap**, in the `Scheme` layer and
phrased ring-theoretically: a prime of `A` containing `a` maps outside the range of the
`B`-chart. -/
theorem specTwoPatchSchemeι₀_base_notMem_range_specTwoPatchSchemeι₁ {x : PrimeSpectrum A}
    (hx : a ∈ x.asIdeal) :
    (specTwoPatchSchemeι₀ a b θ).base x ∉ Set.range (specTwoPatchSchemeι₁ a b θ).base :=
  specTwoPatchι₀_base_notMem_range_specTwoPatchι₁ a b θ x (notMem_range_specAwayMap a hx)

/-- **The two charts of the glued scheme meet only over the overlap**, from the other side: a prime
of `B` containing `b` maps outside the range of the `A`-chart. The mirror of
`specTwoPatchSchemeι₀_base_notMem_range_specTwoPatchSchemeι₁`; `notMem_range_specAwayMap` is
symmetric in the data and applies unchanged at `b`. -/
theorem specTwoPatchSchemeι₁_base_notMem_range_specTwoPatchSchemeι₀ {x : PrimeSpectrum B}
    (hx : b ∈ x.asIdeal) :
    (specTwoPatchSchemeι₁ a b θ).base x ∉ Set.range (specTwoPatchSchemeι₀ a b θ).base :=
  specTwoPatchι₁_base_notMem_range_specTwoPatchι₀ a b θ x (notMem_range_specAwayMap b hx)

/-- **Neither chart is surjective** once there is a prime of `A` containing `a`: the `B`-chart
misses the image of such a prime. -/
theorem not_surjective_specTwoPatchSchemeι₁_base {x : PrimeSpectrum A} (hx : a ∈ x.asIdeal) :
    ¬ Function.Surjective (specTwoPatchSchemeι₁ a b θ).base := fun h =>
  specTwoPatchSchemeι₀_base_notMem_range_specTwoPatchSchemeι₁ a b θ hx (h _)

end TwoCharts

section Double

variable {A : Type u} [CommRing A] (a : A)

/-- **`Spec A` doubled along the basic open `D(a)`**: the two-patch glued scheme with both charts
equal to `Spec A`, glued along the identity of `A_a`. For `A = k[t]`, `a = t` this is the affine
line with a doubled origin. -/
abbrev specDouble : Scheme.{u} :=
  specTwoPatchScheme a a (RingEquiv.refl (Localization.Away a))

/-- **The doubled point.** A prime `x` of `A` containing `a` has two distinct images in
`specDouble a`, one from each chart. -/
theorem specTwoPatchSchemeι₀_base_ne_specTwoPatchSchemeι₁_base {x : PrimeSpectrum A}
    (hx : a ∈ x.asIdeal) :
    (specTwoPatchSchemeι₀ a a (RingEquiv.refl (Localization.Away a))).base x ≠
      (specTwoPatchSchemeι₁ a a (RingEquiv.refl (Localization.Away a))).base x := fun h =>
  specTwoPatchSchemeι₀_base_notMem_range_specTwoPatchSchemeι₁ a a _ hx ⟨x, h.symm⟩

/-- At `θ = RingEquiv.refl` the gluing isomorphism of the overlap is the identity: it is `Spec` of
`(RingEquiv.refl _).symm`, which is the identity ring homomorphism. -/
theorem specGlueIso_refl_hom :
    (specGlueIso a a (RingEquiv.refl (Localization.Away a))).hom = 𝟙 _ := by
  change Spec.locallyRingedSpaceMap
    (CommRingCat.ofHom (RingHom.id (Localization.Away a))) = 𝟙 _
  rw [CommRingCat.ofHom_id]
  exact Spec.locallyRingedSpaceMap_id _

/-- **The two charts of `specDouble a` agree over `D(a)`**: this is `specTwoPatch_glue` at
`θ = RingEquiv.refl`, where the gluing isomorphism disappears, transported to the `Scheme`
layer. -/
theorem specAwayMap_comp_specTwoPatchSchemeι₀ :
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫
        specTwoPatchSchemeι₀ a a (RingEquiv.refl (Localization.Away a)) =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫
        specTwoPatchSchemeι₁ a a (RingEquiv.refl (Localization.Away a)) := by
  have h := specTwoPatch_glue a a (RingEquiv.refl (Localization.Away a))
  rw [specGlueIso_refl_hom a, Category.id_comp] at h
  apply Scheme.Hom.ext'
  change Spec.locallyRingedSpaceMap _ ≫
      (specTwoPatchSchemeι₀ a a (RingEquiv.refl (Localization.Away a))).toLRSHom =
    Spec.locallyRingedSpaceMap _ ≫
      (specTwoPatchSchemeι₁ a a (RingEquiv.refl (Localization.Away a))).toLRSHom
  rw [specTwoPatchSchemeι₀_toLRSHom, specTwoPatchSchemeι₁_toLRSHom]
  exact h

/-- **`Spec A_a ⟶ Spec A` is dominant** for `A` a domain and `a ≠ 0`: the kernel of `A → A_a` is
trivial, hence contained in the nilradical, which is Mathlib's criterion for the range of `comap`
to be dense. -/
theorem isDominant_specAwayMap [IsDomain A] (ha : a ≠ 0) :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))) := by
  have hinj : Function.Injective (algebraMap A (Localization.Away a)) :=
    IsLocalization.injective (Localization.Away a)
      (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  rw [isDominant_iff]
  change DenseRange (PrimeSpectrum.comap (algebraMap A (Localization.Away a)))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp hinj]
  exact bot_le

/-- **The two charts of `specDouble a` are different morphisms**, as soon as some prime of `A`
contains `a`: they take that prime to the two halves of the doubled point. -/
theorem specTwoPatchSchemeι₀_ne_specTwoPatchSchemeι₁ {x : PrimeSpectrum A} (hx : a ∈ x.asIdeal) :
    specTwoPatchSchemeι₀ a a (RingEquiv.refl (Localization.Away a)) ≠
      specTwoPatchSchemeι₁ a a (RingEquiv.refl (Localization.Away a)) := fun h =>
  specTwoPatchSchemeι₀_base_ne_specTwoPatchSchemeι₁_base a hx (by rw [h])

/-- **The doubled `Spec A` is not separated.** For `A` a domain, `a ≠ 0` and some prime containing
`a`, the two charts `Spec A ⟶ specDouble a` agree along the dominant map `Spec A_a ⟶ Spec A` but
are different; over a separated target `ext_of_isDominant` would force them to be equal. -/
theorem not_isSeparated_specDouble [IsDomain A] (ha : a ≠ 0) {x : PrimeSpectrum A}
    (hx : a ∈ x.asIdeal) : ¬ (specDouble a).IsSeparated := by
  intro hsep
  haveI := hsep
  haveI := isDominant_specAwayMap a ha
  exact specTwoPatchSchemeι₀_ne_specTwoPatchSchemeι₁ a hx
    (ext_of_isDominant (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))))
      (specAwayMap_comp_specTwoPatchSchemeι₀ a))

/-- **The doubled `Spec A` is not affine** — affine schemes are separated. This is the first
non-affine scheme exhibited in this development, and the witness the scope notes of
`FormalSchemes.CompletionTwoPatchToScheme` and `FormalSchemes.SpecTwoPatchScheme` were missing. -/
theorem not_isAffine_specDouble [IsDomain A] (ha : a ≠ 0) {x : PrimeSpectrum A}
    (hx : a ∈ x.asIdeal) : ¬ IsAffine (specDouble a) := by
  intro haff
  haveI := haff
  exact not_isSeparated_specDouble a ha hx inferInstance

/-- **The doubled `Spec A` is not separated**, in the form that needs no prime supplied: a non-zero
non-unit of a domain lies in some maximal ideal. -/
theorem not_isSeparated_specDouble_of_not_isUnit [IsDomain A] (ha : a ≠ 0) (ha' : ¬ IsUnit a) :
    ¬ (specDouble a).IsSeparated := by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {a})
    ((Ideal.span_singleton_eq_top (x := a)).not.mpr ha')
  exact not_isSeparated_specDouble (x := ⟨m, hm.isPrime⟩) a ha
    (hle (Ideal.mem_span_singleton_self a))

/-- **The doubled `Spec A` is not affine**, in the form that needs no prime supplied. -/
theorem not_isAffine_specDouble_of_not_isUnit [IsDomain A] (ha : a ≠ 0) (ha' : ¬ IsUnit a) :
    ¬ IsAffine (specDouble a) := by
  intro haff
  haveI := haff
  exact not_isSeparated_specDouble_of_not_isUnit a ha ha' inferInstance

end Double

/-! ### A concrete non-affine scheme

`specDouble (X : ℚ[X])` — the affine line over `ℚ` with the origin doubled, the standard first
example of a non-affine (indeed non-separated) scheme. -/

section AffineLineDoubledOrigin

open Polynomial

/-- **The two halves of the doubled origin really are two points** of the doubled affine line. The
origin is `twoPatchWitnessOrigin` (`FormalSchemes/TwoPatchWitness.lean`), shared with the
completion-side witnesses so that they are visibly the same point. -/
example : (specTwoPatchSchemeι₀ (X : ℚ[X]) X (RingEquiv.refl (Localization.Away (X : ℚ[X])))).base
      twoPatchWitnessOrigin ≠
    (specTwoPatchSchemeι₁ (X : ℚ[X]) X (RingEquiv.refl (Localization.Away (X : ℚ[X])))).base
      twoPatchWitnessOrigin :=
  specTwoPatchSchemeι₀_base_ne_specTwoPatchSchemeι₁_base (X : ℚ[X])
    X_mem_twoPatchWitnessOrigin

/-- **The affine line with a doubled origin is not separated.** -/
example : ¬ (specDouble (X : ℚ[X])).IsSeparated :=
  not_isSeparated_specDouble_of_not_isUnit (X : ℚ[X]) X_ne_zero not_isUnit_X

/-- **The affine line with a doubled origin is not affine**: a scheme in this development that is
provably not the spectrum of a ring. -/
example : ¬ IsAffine (specDouble (X : ℚ[X])) :=
  not_isAffine_specDouble_of_not_isUnit (X : ℚ[X]) X_ne_zero not_isUnit_X

end AffineLineDoubledOrigin

end AlgebraicGeometry
