import FormalSchemes.IndSchemeFamilyLimitLRS
import Mathlib.AlgebraicGeometry.Scheme

set_option linter.style.header false

/-!
# EGA I, 10.6.7 and 10.6.10 for an arbitrary scheme

Every general-target statement in this cluster carries the affine cover of the target as **four
explicit arguments** on top of `hI : I.FG`:

```
{ι : Type u} (U : ι → Opens X.toTopCat) (hU : ⨆ i, U i = ⊤)
(B : ι → Type u) [∀ i, CommRing (B i)]
(e : ∀ i, X.restrict (U i).isOpenEmbedding ≅ Spec.locallyRingedSpaceObj (CommRingCat.of (B i)))
```

— `existsUnique_hom_thickeningMap` (`FormalSchemes/SpfHomOfFamily.lean`),
`thickeningRestrictionEquivLRS` (`FormalSchemes/IndSchemeColimitEquivLRS.lean`) and
`spfHomLimitEquivLRS` (`FormalSchemes/IndSchemeFamilyLimitLRS.lean`) all take them.

This file discharges them for `X : Scheme`, leaving

```
spfHomLimitEquivScheme :
  (Spf R ⟶ X)  ≃  lim_n Hom(Spec (R ⧸ Iⁿ), X)
```

with nothing in the statement but `I`, `hI` and `X`. That is umbrella 97's goal sentence in the
umbrella's own words, at the target it names.

## Why the cover is data for a locally ringed space and a field for a scheme

For a bare `LocallyRingedSpace` the affine identifications have to be *data*: `IsAffineOpen` is a
predicate about a `Scheme`, so there is no property to quantify over, only isomorphisms to carry.
A `Scheme` **is** a locally ringed space together with exactly that data —
`Mathlib/AlgebraicGeometry/Scheme.lean`:

```lean
structure Scheme extends LocallyRingedSpace where
  local_affine : ∀ x : toLocallyRingedSpace, ∃ (U : OpenNhds x) (R : CommRingCat),
    Nonempty (toLocallyRingedSpace.restrict U.isOpenEmbedding ≅
      Spec.toLocallyRingedSpace.obj (op R))
```

so for a scheme the four arguments are not something a caller should be asked for. The general
statements keep them, and this file is a corollary layer over them: nothing existing is narrowed
to `Scheme`, which is the decision `FormalSchemes/ThickeningChartSpfHom.lean` records for issue
1047 and which stands.

## The two hops that were expected to cost a transport, and do not

`local_affine` gives an iso into `Spec.toLocallyRingedSpace.obj (op R)` for `R : CommRingCat`,
while the cluster asks for `Spec.locallyRingedSpaceObj (CommRingCat.of (B i))` with `B i : Type u`
carrying a `CommRing` instance. Both hops are definitional, so `schemeCoverIso` is the structure
field with a different type ascription and there is no `eqToIso` anywhere in this file:

* `Spec.toLocallyRingedSpace.obj (op R)` and `Spec.locallyRingedSpaceObj R` are the same term;
* `CommRingCat.of (schemeCoverRing X x)` is accepted where `CommRingCat.of (B x)` is wanted for
  `B x : Type u`, and the `[∀ i, CommRing (B i)]` instance resolves off the `CommRingCat`
  coercion with no help.

## The cover is chosen, and that is why the agreement theorems matter

`schemeCoverOpen` picks one affine neighbourhood **per point** by `Classical.choice` on
`local_affine`. That cover is maximally redundant — as many pieces as `X` has points, and one
point may be covered by many of them — and it is an arbitrary choice besides. Neither costs
anything, because the cover cannot influence the result: `thickeningRestrictionEquivScheme_eq` and
`spfHomLimitEquivScheme_eq` say that for *any* cover data whatsoever the discharged equivalence is
**equal, as an `Equiv`,** to the cover-carrying one. So these are not a second, parallel
equivalence that happens to have the same source and target; they are the same map, and a caller
holding a better cover than `local_affine`'s can go on using the cover-carrying form and cite the
agreement.

That is also why the cover-carrying forms are kept rather than replaced. `Spec ℤ` covered by
`D(2)` and `D(3)` (`FormalSchemes/SpfHomOfFamily.lean`) and the doubled affine line covered by its
two charts (`FormalSchemes/SpfHomNonAffineWitness.lean`) are witnesses precisely because their
covers are exhibited by hand — `formalLineOpen_ne` and `nonAffineOpen_ne` prove the two pieces
distinct, which is a statement about *that* cover and not about the one chosen here.

## Main definitions and results

* `FormalSpectrum.schemeCoverNhds`, `FormalSpectrum.schemeCoverOpen`,
  `FormalSpectrum.schemeCoverRing`, `FormalSpectrum.schemeCoverIso`: the four cover arguments,
  read off `Scheme.local_affine` at the point `x`, with `FormalSpectrum.mem_schemeCoverOpen` and
  `FormalSpectrum.iSup_schemeCoverOpen`. Indexed by the points of `X`.
* `FormalSpectrum.existsUnique_hom_thickeningMap_scheme`: **EGA I, 10.6.10 for a scheme.** A
  compatible family `Spec (R ⧸ Iⁿ⁺¹) ⟶ X` comes from a unique `Spf R ⟶ X`; only `hI : I.FG`
  remains as a hypothesis.
* `FormalSpectrum.thickeningRestrictionEquivScheme`: the same as a bijection onto
  `ThickeningFamilyLRS`, with `FormalSpectrum.thickeningRestrictionEquivScheme_apply` and
  `FormalSpectrum.thickeningMap_comp_thickeningRestrictionEquivScheme_symm` as its two
  computation rules.
* `FormalSpectrum.spfHomLimitEquivScheme`: **the headline**,
  `(Spf R ⟶ X) ≃ lim_n Hom(Spec (R ⧸ Iⁿ), X)` for an arbitrary scheme `X`, with
  `FormalSpectrum.limit_π_spfHomLimitEquivScheme` as its component rule.
* `FormalSpectrum.thickeningRestrictionEquivScheme_eq`,
  `FormalSpectrum.spfHomLimitEquivScheme_eq`,
  `FormalSpectrum.thickeningRestrictionEquivScheme_symm_eq`: **agreement with the cover-carrying
  forms**, for arbitrary cover data.
* `FormalSpectrum.thickeningRestrictionEquivScheme_eq_thickeningRestrictionEquiv`: at an affine
  scheme this is the affine bijection of `FormalSchemes/IndSchemeColimitEquiv.lean`, on the nose.

## Scope

Naturality in `X` is not proved here: `spfHomLimitEquivScheme` is stated one scheme at a time, and
whether the two sides assemble into isomorphic functors on `Schemeᵒᵖ` is a separate question with
a separate obstruction (the cover is chosen per object, so functoriality is not automatic from
these definitions). It is not claimed to be impossible; it is simply not done here.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.7–10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (X : Scheme.{u})

/-! ### The cover data of a scheme

`Scheme.local_affine` is an `∃` over an `OpenNhds` of each point, a `CommRingCat`, and a
`Nonempty` of the identification. The four definitions below are its three witnesses and the
chosen element of the `Nonempty`, indexed by the points of `X`.
-/

/-- The chosen affine neighbourhood of `x`, as an `OpenNhds`: the first witness of
`Scheme.local_affine`. -/
def schemeCoverNhds (x : X.toLocallyRingedSpace) : OpenNhds x := (X.local_affine x).choose

/-- The ring the chosen neighbourhood of `x` is the spectrum of: the second witness of
`Scheme.local_affine`. -/
def schemeCoverRing (x : X.toLocallyRingedSpace) : CommRingCat.{u} :=
  (X.local_affine x).choose_spec.choose

/-- **The chosen affine open cover of a scheme**, indexed by its own points. -/
def schemeCoverOpen (x : X.toLocallyRingedSpace) : Opens X.toLocallyRingedSpace.toTopCat :=
  (schemeCoverNhds X x).1

/-- **The affine identification over the chosen neighbourhood of `x`**, in exactly the form the
general statements ask for. This is the structure field with a different type ascription: the
codomain `Spec.toLocallyRingedSpace.obj (op (schemeCoverRing X x))` that `local_affine` supplies
and the codomain `Spec.locallyRingedSpaceObj (CommRingCat.of (schemeCoverRing X x))` written here
are the same term, so no transport is involved. -/
def schemeCoverIso (x : X.toLocallyRingedSpace) :
    X.toLocallyRingedSpace.restrict (schemeCoverOpen X x).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (schemeCoverRing X x)) :=
  (X.local_affine x).choose_spec.choose_spec.some

/-- Each point lies in the neighbourhood chosen for it — the `OpenNhds` membership field. -/
theorem mem_schemeCoverOpen (x : X.toLocallyRingedSpace) : x ∈ schemeCoverOpen X x :=
  (schemeCoverNhds X x).2

/-- **The chosen opens cover `X`**, which is the covering hypothesis the general statements take.
It holds for the cheapest possible reason: the cover is indexed by the points, and `x` is in its
own piece. -/
theorem iSup_schemeCoverOpen : (⨆ x, schemeCoverOpen X x) = ⊤ := by
  refine Opens.ext (Set.eq_univ_of_forall fun x => ?_)
  rw [Opens.coe_iSup]
  exact Set.mem_iUnion.2 ⟨x, mem_schemeCoverOpen X x⟩

/-! ### The universal property with the cover discharged -/

section Discharged

variable {X}
variable (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶
    X.toLocallyRingedSpace)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)

include hf in
/-- **`Spf R` is the colimit of its infinitesimal thickenings, for an arbitrary scheme** (EGA I,
10.6.10): a compatible family of morphisms `Spec (R ⧸ Iⁿ⁺¹) ⟶ X` comes from a unique morphism
`Spf R ⟶ X`.

This is `existsUnique_hom_thickeningMap` with its four cover arguments supplied from
`Scheme.local_affine`. The only hypothesis left is `hI : I.FG`. -/
theorem existsUnique_hom_thickeningMap_scheme (hI : I.FG) :
    ∃! g : locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace,
      ∀ n : ℕ, thickeningMap I n ≫ g = f n :=
  existsUnique_hom_thickeningMap I f hf hI (schemeCoverOpen X) (iSup_schemeCoverOpen X)
    (fun x => schemeCoverRing X x) (fun x => schemeCoverIso X x)

end Discharged

/-- **EGA I, 10.6.10 for an arbitrary scheme, as a bijection**: restriction to the thickenings is
a bijection from `Spf R ⟶ X` onto the compatible families.

This is `thickeningRestrictionEquivLRS` with the cover discharged from `Scheme.local_affine`; it
is *equal* to that bijection for every choice of cover data, see
`thickeningRestrictionEquivScheme_eq`. The computation rules are
`thickeningRestrictionEquivScheme_apply` and
`thickeningMap_comp_thickeningRestrictionEquivScheme_symm`; cite those rather than unfolding. -/
def thickeningRestrictionEquivScheme (hI : I.FG) :
    (locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace) ≃
      ThickeningFamilyLRS I X.toLocallyRingedSpace :=
  thickeningRestrictionEquivLRS I X.toLocallyRingedSpace hI (schemeCoverOpen X)
    (iSup_schemeCoverOpen X) (fun x => schemeCoverRing X x) (fun x => schemeCoverIso X x)

/-- **Umbrella 97's headline, at an arbitrary scheme** (EGA I, 10.6.7):

```
(Spf R ⟶ X)  ≃  lim_n Hom(Spec (R ⧸ Iⁿ), X)
```

Nothing but `I`, `hI : I.FG` and `X : Scheme` appears in the statement — no index type, no opens,
no affine identifications. The component rule is `limit_π_spfHomLimitEquivScheme`, and
`spfHomLimitEquivScheme_eq` identifies this with the cover-carrying `spfHomLimitEquivLRS` for
every choice of cover. -/
def spfHomLimitEquivScheme (hI : I.FG) :
    (locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace) ≃
      (limit (homTowerLRS I X.toLocallyRingedSpace) : Type u) :=
  spfHomLimitEquivLRS I X.toLocallyRingedSpace hI (schemeCoverOpen X) (iSup_schemeCoverOpen X)
    (fun x => schemeCoverRing X x) (fun x => schemeCoverIso X x)

/-- **Computation rule, forward**: the `n`-th member of the family attached to `g` is the
restriction of `g` to the `n`-th thickening. -/
theorem thickeningRestrictionEquivScheme_apply (hI : I.FG)
    (g : locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace) (n : ℕ) :
    (thickeningRestrictionEquivScheme I X hI g).1 n = thickeningMap I n ≫ g := rfl

/-- **Computation rule, backwards**: the morphism glued from a compatible family restricts on the
`n`-th thickening to the family's `n`-th member. -/
theorem thickeningMap_comp_thickeningRestrictionEquivScheme_symm (hI : I.FG)
    (f : ThickeningFamilyLRS I X.toLocallyRingedSpace) (n : ℕ) :
    thickeningMap I n ≫ (thickeningRestrictionEquivScheme I X hI).symm f = f.1 n :=
  thickeningMap_comp_thickeningRestrictionEquivLRS_symm I X.toLocallyRingedSpace hI _ _ _ _ f n

/-- **Component rule**: the `(n + 1)`-st leg of the cone attached to `g` is the restriction of `g`
to the `n`-th thickening. Without this the `Equiv` would be opaque. -/
theorem limit_π_spfHomLimitEquivScheme (hI : I.FG)
    (g : locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace) (n : ℕ) :
    limit.π (homTowerLRS I X.toLocallyRingedSpace) ⟨n + 1⟩ (spfHomLimitEquivScheme I X hI g) =
      thickeningMap I n ≫ g :=
  limit_π_spfHomLimitEquivLRS I X.toLocallyRingedSpace hI _ _ _ _ g n

/-! ### Agreement with the cover-carrying forms

The point-per-point cover of `iSup_schemeCoverOpen` is an arbitrary choice, so the statements
below are what makes the discharged forms canonical rather than an artefact of it. Each is one
step from the corresponding `_eq_of_cover` lemma, which in turn holds because an `Equiv` is
determined by its forward map and no forward map in this cluster mentions the cover.
-/

section Agreement

variable (hI : I.FG) {ι : Type u} (U : ι → Opens X.toLocallyRingedSpace.toTopCat)
    (hU : ⨆ i, U i = ⊤) (B : ι → Type u) [∀ i, CommRing (B i)]
    (e : ∀ i, X.toLocallyRingedSpace.restrict (U i).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (B i)))

/-- **The discharged bijection is the cover-carrying one**, for arbitrary cover data on `X` — as
an equality of `Equiv`s, not merely pointwise. So `thickeningRestrictionEquivScheme` adds no new
content: it is `thickeningRestrictionEquivLRS` with a cover the caller no longer has to name. -/
theorem thickeningRestrictionEquivScheme_eq :
    thickeningRestrictionEquivScheme I X hI =
      thickeningRestrictionEquivLRS I X.toLocallyRingedSpace hI U hU B e :=
  thickeningRestrictionEquivLRS_eq_of_cover I X.toLocallyRingedSpace hI _ _ _ _ U hU B e

/-- The pointwise form of `thickeningRestrictionEquivScheme_eq` on the inverse: the morphism glued
from a family by the discharged bijection is the one glued using any cover the caller supplies. -/
theorem thickeningRestrictionEquivScheme_symm_eq
    (f : ThickeningFamilyLRS I X.toLocallyRingedSpace) :
    (thickeningRestrictionEquivScheme I X hI).symm f =
      (thickeningRestrictionEquivLRS I X.toLocallyRingedSpace hI U hU B e).symm f :=
  congrArg (fun q => q.symm f) (thickeningRestrictionEquivScheme_eq I X hI U hU B e)

/-- **The discharged headline is the cover-carrying one**, for arbitrary cover data on `X`. This
is what stops `spfHomLimitEquivScheme` being a second, unrelated equivalence, and it is why the
`Classical.choice` in `schemeCoverNhds` is harmless. -/
theorem spfHomLimitEquivScheme_eq :
    spfHomLimitEquivScheme I X hI = spfHomLimitEquivLRS I X.toLocallyRingedSpace hI U hU B e :=
  spfHomLimitEquivLRS_eq_of_cover I X.toLocallyRingedSpace hI _ _ _ _ U hU B e

end Agreement

/-- **The affine case is an instance of this one.** At `X = Spec B` the discharged bijection is
`thickeningRestrictionEquiv` (`FormalSchemes/IndSchemeColimitEquiv.lean`), on the nose: the two
are determined by their forward maps, and `(Scheme.Spec.obj (op (CommRingCat.of B)))`'s underlying
locally ringed space is `Spec.locallyRingedSpaceObj (CommRingCat.of B)` definitionally.

This is the affine comparison, not a re-derivation of the concrete witnesses: `Spec ℤ` with its
hand-built `D(2)`, `D(3)` cover keeps its own statements in `FormalSchemes/SpfHomOfFamily.lean`,
whose point is that *that* cover is genuinely two-piece. -/
theorem thickeningRestrictionEquivScheme_eq_thickeningRestrictionEquiv (hI : I.FG) (B : Type u)
    [CommRing B] :
    thickeningRestrictionEquivScheme I (Scheme.Spec.obj (op (CommRingCat.of B))) hI =
      thickeningRestrictionEquiv I B :=
  Equiv.coe_fn_injective rfl

end FormalSpectrum
