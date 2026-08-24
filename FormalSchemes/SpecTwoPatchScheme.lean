import Mathlib.AlgebraicGeometry.AffineScheme
import FormalSchemes.CompletionTwoPatchToScheme

set_option linter.style.header false

/-!
# The two-patch glued object is a scheme (EGA I, 10.8)

`FormalSchemes/CompletionTwoPatchToScheme.lean` glues `Spec A` and `Spec B` along the
identification `Spec θ` of their basic opens `D(a)` and `D(b)`, producing `specTwoPatch`, and builds
the canonical morphism `completionTwoPatchToScheme` from the glued formal completion into it. Both
live in `LocallyRingedSpace`, because that is the category `formalCompletion.toSpec` lands in, and
that file's scope section records the promotion to `AlgebraicGeometry.Scheme` as a separate carve.

This file is that carve.

```
completionTwoPatch  ──completionTwoPatchToSchemeHom──→  specTwoPatchScheme : Scheme
```

`specTwoPatchScheme` is `specTwoPatch` with a `Scheme` structure on top, and the two are equal by
`rfl` (`specTwoPatchScheme_toLocallyRingedSpace`), so everything already proved about
`specTwoPatch` transfers with no transport. What the promotion buys is the whole `Scheme` API: an
affine open cover, affine-open chart ranges, and quasi-compactness, all of which are established
below and none of which was available one layer down.

## How it is built

Not as an `AlgebraicGeometry.Scheme.GlueData`. That route would glue the two `Spec`s afresh in
`Scheme` and then owe an identification of the resulting locally ringed space glue datum with
`specTwoPatchLRSGlueData`. Instead we use `LocallyRingedSpace.IsOpenImmersion.scheme`, which turns
a locally ringed space covered by open immersions out of affines into a scheme *on the same
carrier*: the two charts `specTwoPatchι₀` and `specTwoPatchι₁` are open immersions and jointly
surjective, which is exactly its hypothesis, and its `toLocallyRingedSpace` field is the input
space on the nose.

## Main definitions and results

* `AlgebraicGeometry.specTwoPatchScheme`: the glued object `Spec A ∪_{D(a) ≅ D(b)} Spec B` as a
  scheme, with `AlgebraicGeometry.specTwoPatchScheme_toLocallyRingedSpace` identifying its
  underlying locally ringed space with `specTwoPatch`.
* `AlgebraicGeometry.specTwoPatchSchemeι₀` / `..ι₁`: the two charts as morphisms of schemes, open
  immersions, jointly surjective.
* `AlgebraicGeometry.specTwoPatchSchemeCover`: the two charts as a
  `AlgebraicGeometry.Scheme.OpenCover`, affine by
  `AlgebraicGeometry.specTwoPatchSchemeCover_isAffine`.
* `AlgebraicGeometry.isAffineOpen_specTwoPatchSchemeι₀` / `..ι₁`: the chart ranges are affine opens.
* `AlgebraicGeometry.specTwoPatchScheme_compactSpace`: the glued scheme is quasi-compact, being
  covered by two spectra.
* `AlgebraicGeometry.completionTwoPatchToSchemeHom`: the completion morphism `X_{/Y} ⟶ X` of
  EGA I, 10.8 with `X` an actual scheme, characterised chart by chart by
  `AlgebraicGeometry.completionTwoPatchι₀_comp_toSchemeHom` and its twin.

## Scope

`specTwoPatchScheme` is a scheme glued from two affine charts. Whether it is *non-affine* is a
different question and is not addressed here: the only witness this development instantiates the
construction at is `A = B = R`, `a = b = f`, `θ = RingEquiv.refl`, which glues `Spec R` to itself
along `D(f)` — geometrically a doubled scheme, and genuinely non-affine for e.g. `R = k[t]`,
`f = t`, but nothing here proves that. Likewise nothing here claims `completionTwoPatch` is *the*
completion of `specTwoPatchScheme` in any sense beyond the morphism, and nothing here is separated:
the doubled line is not, so no `IsSeparated` statement could hold at this generality.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section Glued

variable {A B : Type u} [CommRing A] [CommRing B] (a : A) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)

/-- **The two-patch glued object as a scheme**, `Spec A ∪_{D(a) ≅ D(b)} Spec B`.

`LocallyRingedSpace.IsOpenImmersion.scheme` promotes a locally ringed space to a scheme given, at
each point, an open immersion from a `Spec` whose range contains it. The two charts of
`specTwoPatch` supply exactly that, by `specTwoPatch_jointly_surjective`.

The `IsOpenImmersion` witnesses have to be named rather than left to `inferInstance`: inside the
anonymous constructor the chart is ascribed at `Spec.toLocallyRingedSpace.obj (op R) ⟶ _`, which is
defeq but not *reducibly* defeq to `Spec.locallyRingedSpaceObj R ⟶ _`, so instance search does not
see through it. -/
def specTwoPatchScheme : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme (specTwoPatch a b θ) (by
    intro x
    rcases specTwoPatch_jointly_surjective a b θ x with h | h
    · exact ⟨CommRingCat.of A, specTwoPatchι₀ a b θ, h, specTwoPatchι₀_isOpenImmersion a b θ⟩
    · exact ⟨CommRingCat.of B, specTwoPatchι₁ a b θ, h, specTwoPatchι₁_isOpenImmersion a b θ⟩)

/-- **The promotion changes nothing underneath.** `LocallyRingedSpace.IsOpenImmersion.scheme` sets
its `toLocallyRingedSpace` field to the space it was given, so this is `rfl` — which is what lets
every result about `specTwoPatch` be reused at the scheme without transport. -/
theorem specTwoPatchScheme_toLocallyRingedSpace :
    (specTwoPatchScheme a b θ).toLocallyRingedSpace = specTwoPatch a b θ := rfl

/-- The chart `Spec A` of the glued scheme, as a morphism of schemes. -/
def specTwoPatchSchemeι₀ : Spec (CommRingCat.of A) ⟶ specTwoPatchScheme a b θ :=
  ⟨specTwoPatchι₀ a b θ⟩

/-- The chart `Spec B` of the glued scheme, as a morphism of schemes. -/
def specTwoPatchSchemeι₁ : Spec (CommRingCat.of B) ⟶ specTwoPatchScheme a b θ :=
  ⟨specTwoPatchι₁ a b θ⟩

/-- The `A`-chart of the glued scheme is the `A`-chart of the glued locally ringed space. -/
theorem specTwoPatchSchemeι₀_toLRSHom :
    (specTwoPatchSchemeι₀ a b θ).toLRSHom = specTwoPatchι₀ a b θ := rfl

/-- The `B`-chart of the glued scheme is the `B`-chart of the glued locally ringed space. -/
theorem specTwoPatchSchemeι₁_toLRSHom :
    (specTwoPatchSchemeι₁ a b θ).toLRSHom = specTwoPatchι₁ a b θ := rfl

instance specTwoPatchSchemeι₀_isOpenImmersion : IsOpenImmersion (specTwoPatchSchemeι₀ a b θ) :=
  specTwoPatchι₀_isOpenImmersion a b θ

instance specTwoPatchSchemeι₁_isOpenImmersion : IsOpenImmersion (specTwoPatchSchemeι₁ a b θ) :=
  specTwoPatchι₁_isOpenImmersion a b θ

/-- **The two charts cover the glued scheme.** -/
theorem specTwoPatchScheme_jointly_surjective (x : specTwoPatchScheme a b θ) :
    x ∈ Set.range (specTwoPatchSchemeι₀ a b θ).base ∪
      Set.range (specTwoPatchSchemeι₁ a b θ).base :=
  specTwoPatch_jointly_surjective a b θ x

/-- **The two charts as an open cover of the glued scheme**, indexed by `ULift Bool` as the glue
datum is: `⟨false⟩` is the `A`-chart and `⟨true⟩` the `B`-chart.

The final argument is the instance argument `∀ j, IsOpenImmersion (map j)`, and `infer_instance`
does not discharge it: the `match` on `⟨false⟩` does not reduce during instance search, so the
reduced form has to be spelled out with `inferInstanceAs`. -/
def specTwoPatchSchemeCover : (specTwoPatchScheme a b θ).OpenCover :=
  Scheme.Cover.mkOfCovers (ULift.{u} Bool)
    (fun i => cond i.down (Spec (CommRingCat.of B)) (Spec (CommRingCat.of A)))
    (fun i => match i with
      | ⟨false⟩ => specTwoPatchSchemeι₀ a b θ
      | ⟨true⟩ => specTwoPatchSchemeι₁ a b θ)
    (by
      intro x
      rcases specTwoPatch_jointly_surjective a b θ x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨⟨false⟩, y, hy⟩
      · exact ⟨⟨true⟩, y, hy⟩)
    (by
      rintro ⟨_ | _⟩
      · exact inferInstanceAs (IsOpenImmersion (specTwoPatchSchemeι₀ a b θ))
      · exact inferInstanceAs (IsOpenImmersion (specTwoPatchSchemeι₁ a b θ)))

theorem specTwoPatchSchemeCover_X_false :
    (specTwoPatchSchemeCover a b θ).X ⟨false⟩ = Spec (CommRingCat.of A) := rfl

theorem specTwoPatchSchemeCover_X_true :
    (specTwoPatchSchemeCover a b θ).X ⟨true⟩ = Spec (CommRingCat.of B) := rfl

theorem specTwoPatchSchemeCover_f_false :
    (specTwoPatchSchemeCover a b θ).f ⟨false⟩ = specTwoPatchSchemeι₀ a b θ := rfl

theorem specTwoPatchSchemeCover_f_true :
    (specTwoPatchSchemeCover a b θ).f ⟨true⟩ = specTwoPatchSchemeι₁ a b θ := rfl

/-- **The two-chart cover is an affine cover**: both its members are spectra. -/
theorem specTwoPatchSchemeCover_isAffine (i : ULift.{u} Bool) :
    IsAffine ((specTwoPatchSchemeCover a b θ).X i) := by
  rcases i with ⟨_ | _⟩
  · exact inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  · exact inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))

/-- **The `A`-chart's range is an affine open** of the glued scheme. -/
theorem isAffineOpen_specTwoPatchSchemeι₀ :
    IsAffineOpen (specTwoPatchSchemeι₀ a b θ).opensRange :=
  isAffineOpen_opensRange _

/-- **The `B`-chart's range is an affine open** of the glued scheme. -/
theorem isAffineOpen_specTwoPatchSchemeι₁ :
    IsAffineOpen (specTwoPatchSchemeι₁ a b θ).opensRange :=
  isAffineOpen_opensRange _

instance specTwoPatchSchemeCover_finite_I₀ : Finite (specTwoPatchSchemeCover a b θ).I₀ :=
  inferInstanceAs (Finite (ULift.{u} Bool))

/-- **The glued scheme is quasi-compact**, being covered by two spectra. -/
instance specTwoPatchScheme_compactSpace : CompactSpace (specTwoPatchScheme a b θ) := by
  refine (specTwoPatchSchemeCover a b θ).compactSpace (H := ?_)
  rintro ⟨_ | _⟩
  · exact inferInstanceAs (CompactSpace (Spec (CommRingCat.of A)))
  · exact inferInstanceAs (CompactSpace (Spec (CommRingCat.of B)))

end Glued

section Morphism

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (hI : I.FG) (a : A)
  (J : Ideal B) (hJ : J.FG) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

/-- **The completion morphism `X_{/Y} ⟶ X` of EGA I, 10.8, with `X` an actual scheme.** This is
`completionTwoPatchToScheme` retyped along `specTwoPatchScheme_toLocallyRingedSpace`, which is
`rfl`, so it is the same morphism; the point is that its target is now the underlying space of a
`Scheme` rather than a bare locally ringed space. -/
def completionTwoPatchToSchemeHom :
    (completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace ⟶
      (specTwoPatchScheme a b θ).toLocallyRingedSpace :=
  completionTwoPatchToScheme I hI a J hJ b θ hθ

/-- **The completion morphism restricts to the `A`-chart's `formalCompletion.toSpec`.** -/
theorem completionTwoPatchι₀_comp_toSchemeHom :
    completionTwoPatchι₀ I hI a J hJ b θ hθ ≫ completionTwoPatchToSchemeHom I hI a J hJ b θ hθ =
      formalCompletion.toSpec A I hI ≫ (specTwoPatchSchemeι₀ a b θ).toLRSHom :=
  completionTwoPatchι₀_comp_toScheme I hI a J hJ b θ hθ

/-- **The completion morphism restricts to the `B`-chart's `formalCompletion.toSpec`.** Together
with its `A`-side twin this characterises `completionTwoPatchToSchemeHom` chart by chart. -/
theorem completionTwoPatchι₁_comp_toSchemeHom :
    completionTwoPatchι₁ I hI a J hJ b θ hθ ≫ completionTwoPatchToSchemeHom I hI a J hJ b θ hθ =
      formalCompletion.toSpec B J hJ ≫ (specTwoPatchSchemeι₁ a b θ).toLRSHom :=
  completionTwoPatchι₁_comp_toScheme I hI a J hJ b θ hθ

/-- **The hypothesis stack is satisfiable.** Taking both charts to be the same `Spec R` completed
along the same `V(K)`, both overlap elements to be the same `f : R` and the overlap identification
to be the identity discharges every hypothesis at once, for an arbitrary `f`. Geometrically this
glues `Spec R` to itself along `D(f)`; the point is that the glued *scheme*, the glued completion
and the morphism between them all exist. -/
example (R : Type u) [CommRing R] (K : Ideal R) (hK : K.FG) (f : R) :
    (completionTwoPatch K hK f K hK f (RingEquiv.refl _) (Ideal.map_id _)).toLocallyRingedSpace ⟶
      (specTwoPatchScheme f f (RingEquiv.refl _)).toLocallyRingedSpace :=
  completionTwoPatchToSchemeHom K hK f K hK f (RingEquiv.refl _) (Ideal.map_id _)

end Morphism

end AlgebraicGeometry

end
