import FormalSchemes.IndSchemeColimitEquiv
import FormalSchemes.SpfHomOfFamily

set_option linter.style.header false

/-!
# The colimit property of `Spf R` as a bijection, for a general target (EGA I, 10.6.10)

`FormalSchemes/IndSchemeColimitEquiv.lean` packages the colimit property of `Spf R` as an
`Equiv` for an **affine** target:

```
(Spf R ⟶ Spec B)  ≃  ThickeningFamily I B
```

`FormalSchemes/SpfHomOfFamily.lean` proves the same mathematics for a general target, but in
`∃!` form: `existsUnique_hom_thickeningMap` says that every compatible family of morphisms
`Spec (R ⧸ Iⁿ⁺¹) ⟶ X` comes from a unique `Spf R ⟶ X`. This file turns that `∃!` into the
bijection

```
(Spf R ⟶ X)  ≃  ThickeningFamilyLRS I X
```

as `FormalSpectrum.thickeningRestrictionEquivLRS`.

## The hypotheses on `X`, in one sentence

`X` is a locally ringed space carrying a family of opens `U i` with `⨆ i, U i = ⊤`, each
*equipped* with an identification `X|_{U i} ≅ Spec (B i)`. The identifications are data and not a
property because `X` is a bare locally ringed space, so `IsAffineOpen` is not available to it; a
scheme supplies them from its own affine cover, as `existsUnique_hom_thickeningMap_formalLine`
(`FormalSchemes/SpfHomOfFamily.lean`) does for `Spec ℤ` covered by `D(2)` and `D(3)`.

## Why the cover appears in the definition and not in the object

`thickeningRestrictionEquivLRS` takes the cover data as arguments, because the inverse map is
built by gluing over a cover. It does **not** depend on them:
`thickeningRestrictionEquivLRS_symm_eq` says two arbitrary sets of cover data give the same
inverse, and the forward map `restrictToThickeningsLRS` does not mention the cover at all. So the
general universal property is canonical, and the cover is scaffolding — which is the fact a reader
needs before citing this file, since an `Equiv` that secretly depended on a chosen cover would not
be a universal property at all.

## `ThickeningFamilyLRS` is not a duplicate of `ThickeningFamily`

`ThickeningFamily I B` is *the same type* as `ThickeningFamilyLRS I (Spec B)`, on the nose:
`thickeningFamily_eq_thickeningFamilyLRS` proves it by `rfl`, and
`restrictToThickeningsLRS_eq_restrictToThickenings` says the two forward maps are the same
function. `ThickeningFamily` is therefore left alone rather than redefined — redefining it would
change a statement with consumers (`IndSchemeFamilyLimit.lean`,
`ThickeningChartSpfHom.lean`) and buy nothing that the two `rfl`s above do not already give.
`thickeningRestrictionEquivLRS_eq_thickeningRestrictionEquiv` closes the loop: at an affine target
the new `Equiv` **is** the old one, for any cover data whatsoever.

## Scope

Not attempted here: the `limit` form of EGA I 10.6.7, `(Spf R ⟶ X) ≃ lim_n Hom(Spec (R ⧸ Iⁿ), X)`.
The affine case gets it from `specHomLimitEquiv` (`FormalSchemes/IndSchemeLimit.lean`), which is
built on the ring-side bijection `specHomEquiv` and on `R = lim_n R ⧸ Iⁿ` in `CommRingCat`; a
general `X` has no ring side, so the limit has to be compared with `ThickeningFamilyLRS` directly,
through `CategoryTheory.Limits.Types.limitEquivSections`. Two things are then needed that the
affine route never has to state: the successor-only compatibility of a `ThickeningFamilyLRS`
promoted to every morphism of `ℕᵒᵖ`, and the level-`0` leg `Hom(Spec (R ⧸ I⁰), X)` shown to be a
subsingleton. Neither is missing mathematics — `R ⧸ I⁰` is the zero ring
(`subsingleton_quotient_pow_zero`, `FormalSchemes/IndSchemeLimitComponents.lean`), so its `Spec` is
empty, and Mathlib carries `LocallyRingedSpace.emptyIsInitial` and `Scheme.isInitialOfIsEmpty` —
but no bridge from those to this tower exists here. That is a separate row.

Likewise not attempted: a `CategoryTheory.Limits.IsColimit` for the tower of thickenings. It does
not follow from what is here, because `existsUnique_hom_thickeningMap` is not stated for *every*
locally ringed space `X` — only for those carrying the cover data above — while `IsColimit`
quantifies over arbitrary cocones. Restricted to schemes it should follow; that too is a separate
row.

## Main definitions and results

* `FormalSpectrum.ThickeningFamilyLRS`: compatible families out of the thickenings, into a general
  locally ringed space.
* `FormalSpectrum.thickeningRestrictionEquivLRS`: **the bijection**, EGA I 10.6.10 in `Equiv` form.
* `FormalSpectrum.thickeningRestrictionEquivLRS_apply` and
  `FormalSpectrum.thickeningMap_comp_thickeningRestrictionEquivLRS_symm`: the two computation
  rules, which downstream should cite rather than unfolding the `Equiv`.
* `FormalSpectrum.thickeningRestrictionEquivLRS_symm_eq`: **the inverse does not depend on the
  cover.**
* `FormalSpectrum.thickeningFamily_eq_thickeningFamilyLRS` and
  `FormalSpectrum.thickeningRestrictionEquivLRS_eq_thickeningRestrictionEquiv`: the affine case is
  an instance of this one, not a parallel construction.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.7–10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (X : LocallyRingedSpace.{u})

/-- **A compatible family of morphisms out of the infinitesimal thickenings of `Spf R`**, into a
general locally ringed space: a morphism `Spec (R ⧸ Iⁿ⁺¹) ⟶ X` for every `n`, compatible with the
transition maps of the tower.

This is `ThickeningFamily` (`FormalSchemes/IndSchemeColimitEquiv.lean`) with the affine target
`Spec B` replaced by `X`; at `X = Spec B` it is not merely isomorphic to it but *equal*, see
`thickeningFamily_eq_thickeningFamilyLRS`. The compatibility is phrased through `stepRingHom`, in
the same direction as `existsUnique_hom_thickeningMap`'s hypothesis. -/
def ThickeningFamilyLRS : Type u :=
  { f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X //
    ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n }

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The general family type extends the affine one on the nose.** No transport, no `Equiv`: at
an affine target the two subtypes are the same type, so nothing that consumes `ThickeningFamily`
needs adapting to consume this one. -/
theorem thickeningFamily_eq_thickeningFamilyLRS (B : Type u) [CommRing B] :
    ThickeningFamily I B =
      ThickeningFamilyLRS I (Spec.locallyRingedSpaceObj (CommRingCat.of B)) := rfl

/-- **Restricting a morphism out of `Spf R` to the thickenings.** The forward map of the
bijection; that the resulting family is compatible is `thickeningMap_comp`, the cocone equation of
`FormalSchemes/ThickeningCocone.lean`. Note that it needs no hypothesis on `X` at all — only the
inverse does. -/
def restrictToThickeningsLRS (g : locallyRingedSpaceObj I ⟶ X) : ThickeningFamilyLRS I X :=
  ⟨fun n => thickeningMap I n ≫ g, fun n => by rw [← Category.assoc, thickeningMap_comp]⟩

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The forward maps agree.** At an affine target `restrictToThickeningsLRS` is
`restrictToThickenings`, as functions and not up to anything. -/
theorem restrictToThickeningsLRS_eq_restrictToThickenings (B : Type u) [CommRing B]
    (g : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B)) :
    restrictToThickeningsLRS I _ g = restrictToThickenings I B g := rfl

section Cover

variable (hI : I.FG) {ι : Type u} (U : ι → Opens X.toTopCat) (hU : ⨆ i, U i = ⊤)
    (B : ι → Type u) [∀ i, CommRing (B i)]
    (e : ∀ i, X.restrict (U i).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (B i)))

/-- **`Spf R` is the colimit of its infinitesimal thickenings** (EGA I, 10.6.10), for a target
carrying an affine open cover: restriction to the thickenings is a bijection from `Spf R ⟶ X` onto
the compatible families. This is umbrella 97's headline shape for a general target, and it is
`existsUnique_hom_thickeningMap` repackaged — both directions come out of that `∃!`.

The cover data `U`, `hU`, `B`, `e` is needed to construct the inverse and cannot influence it; see
`thickeningRestrictionEquivLRS_symm_eq`.

Note that `ExistsUnique` unfolds to `∃ x, p x ∧ ∀ y, p y → y = x`, so the uniqueness clause proves
`g = choose` and the round trip on the left needs the symmetric form. -/
def thickeningRestrictionEquivLRS : (locallyRingedSpaceObj I ⟶ X) ≃ ThickeningFamilyLRS I X where
  toFun := restrictToThickeningsLRS I X
  invFun f := (existsUnique_hom_thickeningMap I f.1 f.2 hI U hU B e).choose
  left_inv g := ((existsUnique_hom_thickeningMap I _ (restrictToThickeningsLRS I X g).2 hI U hU B e
    ).choose_spec.2 g fun _ => rfl).symm
  right_inv f := Subtype.ext (funext fun n =>
    (existsUnique_hom_thickeningMap I f.1 f.2 hI U hU B e).choose_spec.1 n)

/-- **Computation rule, forward**: the `n`-th member of the family attached to `g` is the
restriction of `g` to the `n`-th thickening. Cite this rather than unfolding the `Equiv`. -/
theorem thickeningRestrictionEquivLRS_apply (g : locallyRingedSpaceObj I ⟶ X) (n : ℕ) :
    (thickeningRestrictionEquivLRS I X hI U hU B e g).1 n = thickeningMap I n ≫ g := rfl

/-- **Computation rule, backwards**: the morphism glued from a compatible family restricts on the
`n`-th thickening to the family's `n`-th member. This is the existence clause of
`existsUnique_hom_thickeningMap`, and it is the rule downstream will actually use. -/
theorem thickeningMap_comp_thickeningRestrictionEquivLRS_symm (f : ThickeningFamilyLRS I X)
    (n : ℕ) :
    thickeningMap I n ≫ (thickeningRestrictionEquivLRS I X hI U hU B e).symm f = f.1 n :=
  (existsUnique_hom_thickeningMap I f.1 f.2 hI U hU B e).choose_spec.1 n

/-- **The bijection does not depend on the cover.** Two arbitrary choices of cover data — different
index types, different opens, different affine identifications — invert a compatible family to the
same morphism, because `existsUnique_hom_thickeningMap`'s uniqueness clause pins it down from the
restrictions alone.

This is what makes `thickeningRestrictionEquivLRS` a universal property rather than an artefact of
a chosen cover; the forward direction needs no such statement, since `restrictToThickeningsLRS`
never mentions the cover. -/
theorem thickeningRestrictionEquivLRS_symm_eq {ι' : Type u} (U' : ι' → Opens X.toTopCat)
    (hU' : ⨆ i, U' i = ⊤) (B' : ι' → Type u) [∀ i, CommRing (B' i)]
    (e' : ∀ i, X.restrict (U' i).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (B' i)))
    (f : ThickeningFamilyLRS I X) :
    (thickeningRestrictionEquivLRS I X hI U hU B e).symm f =
      (thickeningRestrictionEquivLRS I X hI U' hU' B' e').symm f :=
  ((existsUnique_hom_thickeningMap I f.1 f.2 hI U hU B e).choose_spec.2 _
    (thickeningMap_comp_thickeningRestrictionEquivLRS_symm I X hI U' hU' B' e' f)).symm

end Cover

/-- **The affine case is an instance of this one.** For an affine target and *any* cover data, the
general bijection is `thickeningRestrictionEquiv` (`FormalSchemes/IndSchemeColimitEquiv.lean`).
Both are determined by their forward maps, which agree by
`restrictToThickeningsLRS_eq_restrictToThickenings`.

Together with `thickeningFamily_eq_thickeningFamilyLRS` this says the affine packaging is not a
parallel construction that happens to have the same source: it is this one, read at `Spec B`. -/
theorem thickeningRestrictionEquivLRS_eq_thickeningRestrictionEquiv (hI : I.FG) (B' : Type u)
    [CommRing B'] {ι : Type u} (U : ι → Opens
      (Spec.locallyRingedSpaceObj (CommRingCat.of B')).toTopCat) (hU : ⨆ i, U i = ⊤)
    (B : ι → Type u) [∀ i, CommRing (B i)]
    (e : ∀ i, (Spec.locallyRingedSpaceObj (CommRingCat.of B')).restrict (U i).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (B i))) :
    thickeningRestrictionEquivLRS I (Spec.locallyRingedSpaceObj (CommRingCat.of B')) hI U hU B e =
      thickeningRestrictionEquiv I B' :=
  Equiv.coe_fn_injective rfl

end FormalSpectrum
