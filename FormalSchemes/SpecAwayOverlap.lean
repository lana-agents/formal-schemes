import FormalSchemes.PullbackRangeLRS
import Mathlib.AlgebraicGeometry.OpenImmersion

set_option linter.style.header false

/-!
# The overlap of two affine basic-open charts (EGA I, 10.8)

For a commutative ring `R` and elements `f g : R`, the two affine basic-open charts
`Spec R_f` and `Spec R_g` sit inside `Spec R` as open subspaces with ranges the basic opens
`D(f)` and `D(g)`. Their **overlap** is the basic open `D(f) ∩ D(g) = D(f·g)`, again an affine
basic-open chart `Spec R_{fg}`. This file records that overlap datum, in the category
`AlgebraicGeometry.LocallyRingedSpace`.

It is the `Spec`-side mirror of `FormalSchemes/CompletionBasicOpenOverlap.lean`, declaration for
declaration, and it exists for the same reason that file does. A glue datum at an **arbitrary**
index type has to discharge the triple-overlap fields `t'`, `t_fac` and `cocycle` of a
`CategoryTheory.GlueData'`, and what those fields consume is an identification of
`pullback (chart i j) (chart i k)` with a concrete object. On the completion side that
identification is `formalCompletion.basicOpenOverlapIso`, and it is what let
`FormalSchemes/CompletionBasicOpenGlue.lean` discharge those three fields at an arbitrary index;
the two-patch scheme glue `AlgebraicGeometry.specTwoPatchGlueData'`
(`FormalSchemes/CompletionTwoPatchToScheme.lean`) escapes them instead, because no triple of
`ULift Bool`-indices is pairwise distinct, and that escape does not generalise.

## Main definitions and results

* `AlgebraicGeometry.specAwayMap`: the affine chart inclusion `Spec R_f ⟶ Spec R`, as a morphism
  of locally ringed spaces, with `AlgebraicGeometry.isOpenImmersion_specAwayMap` making it an open
  immersion. The instance was previously stated inside
  `FormalSchemes/CompletionTwoPatchToScheme.lean`; it is general in `R` and `f` and says nothing
  about two patches, so it lives here now and that file imports it.
* `AlgebraicGeometry.range_specAwayMap`: its range is the basic open `D(f)`. This is Mathlib's
  `PrimeSpectrum.localization_away_comap_range` with no bridging: the base map of
  `Spec.locallyRingedSpaceMap` of a ring homomorphism *is* `PrimeSpectrum.comap` of it.
* `AlgebraicGeometry.range_specAwayMap_inter`: the two ranges meet in the range at the product,
  `im (specAwayMap f) ∩ im (specAwayMap g) = im (specAwayMap (f * g))` — the set-theoretic core
  `D(f) ⊓ D(g) = D(fg)`.
* `AlgebraicGeometry.specAwayOverlapIso`: hence the overlap object `Spec R_{fg}` identifies with
  the fibre product `pullback (specAwayMap f) (specAwayMap g)` of the two chart inclusions, via
  `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq`.
* `AlgebraicGeometry.specAwayOverlapIso_hom_fst_comp` / `..._hom_snd_comp`: the two chart
  compatibilities — the overlap identification followed by either projection and the corresponding
  chart inclusion is the chart inclusion at the product.
* `AlgebraicGeometry.specAwayOverlap_nonempty_iff`: the overlap is non-empty exactly when `f · g`
  is not nilpotent. This is what makes the identification above non-vacuous: an overlap
  identification between two empty objects would be `Subsingleton`-true, and the two-patch glue
  data on the tree never exercise it, since `specTwoPatchGlueData'` discharges its triple-overlap
  fields from `AlgebraicGeometry.uliftBool_not_pairwise_distinct` (`FormalSchemes.Gluing`).
  Instantiated at `R = ℤ`, `f = 2`, `g = 3` below.

## A coercion to know about

`range_specAwayMap`'s right-hand side is ascribed `(… : Set (PrimeSpectrum R))`. Writing the bare
`↑(PrimeSpectrum.basicOpen f)` there does **not** elaborate: the left-hand side's ambient type is
the carrier of `Spec.locallyRingedSpaceObj (CommRingCat.of R)`, and the elaborator reports
`PrimeSpectrum.basicOpen f has type Opens (PrimeSpectrum R) but is expected to have type
Set ↑↑(Spec.locallyRingedSpaceObj (CommRingCat.of R)).toPresheafedSpace`. There is no missing
lemma behind that message — the two types are the same one and the ascription is all that is
needed.

## Scope

Nothing here is stated at `AlgebraicGeometry.Scheme`: the consumers this is built for
(`specTwoPatch` and the arbitrary-index glue that succeeds it) live in `LocallyRingedSpace`,
because that is the category `formalCompletion.toSpec` lives in.

No glue datum is built here, at any index — this is the two-index input such a datum consumes at
a triple, exactly as `formalCompletion.basicOpenOverlapIso` is stated for two elements and used
at triples by instantiating one of them at a product.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] (f g : R)

/-- **The affine chart inclusion `Spec R_f ⟶ Spec R`**, as a morphism of locally ringed spaces:
`Spec.locallyRingedSpaceMap` of the localization map. -/
abbrev specAwayMap : Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away f)) ⟶
    Spec.locallyRingedSpaceObj (CommRingCat.of R) :=
  Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap R (Localization.Away f)))

/-- **The affine chart inclusion of a basic open is an open immersion of locally ringed spaces.**
Mathlib supplies this for schemes (`Scheme.instIsOpenImmersionMapOfHomAwayAlgebraMap`); the
underlying locally ringed space morphism of `Spec.map` is `Spec.locallyRingedSpaceMap` on the nose,
so the scheme-level instance transports through `SheafedSpace.isOpenImmersion_iff_hom`. Every glue
datum whose charts are basic opens of an affine needs it in this form for its `f_mono`,
`f_hasPullback` and `f_open` fields. -/
instance isOpenImmersion_specAwayMap : LocallyRingedSpace.IsOpenImmersion (specAwayMap f) :=
  (SheafedSpace.isOpenImmersion_iff_hom
    (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))))))).mp inferInstance

/-- **The range of the affine chart inclusion is the basic open `D(f)`.** Mathlib's
`PrimeSpectrum.localization_away_comap_range` applies with no transport, since the base map of
`Spec.locallyRingedSpaceMap` of a ring homomorphism is `PrimeSpectrum.comap` of it. See this
file's module docstring for why the right-hand side is ascribed. -/
theorem range_specAwayMap :
    Set.range (specAwayMap f).base = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
  PrimeSpectrum.localization_away_comap_range _ f

/-- **The ranges of two affine chart inclusions intersect in the range of the inclusion at the
product**: `im (specAwayMap f) ∩ im (specAwayMap g) = im (specAwayMap (f * g))`. On underlying
spaces this is the basic-open identity `D(f) ⊓ D(g) = D(fg)`
(`PrimeSpectrum.basicOpen_mul`). Compare `formalCompletion.range_basicOpenImmersion_inter`, which
is the same statement one completion further up and needs `map_mul` to get there. -/
theorem range_specAwayMap_inter :
    Set.range (specAwayMap f).base ∩ Set.range (specAwayMap g).base =
      Set.range (specAwayMap (f * g)).base := by
  rw [range_specAwayMap, range_specAwayMap, range_specAwayMap, PrimeSpectrum.basicOpen_mul,
    Opens.coe_inf]
  rfl

/-- **The overlap object of two affine basic-open charts is their fibre product.** The chart
`Spec R_{fg}` at the product, whose range in `Spec R` is `D(f) ∩ D(g)`
(`range_specAwayMap_inter`), identifies with the pullback of the two chart inclusions
`specAwayMap f`, `specAwayMap g`, via the open-immersion pullback identification
`LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq`. -/
def specAwayOverlapIso :
    Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away (f * g))) ≅
      pullback (specAwayMap f) (specAwayMap g) :=
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq (specAwayMap f) (specAwayMap g)
    (specAwayMap (f * g)) (range_specAwayMap_inter f g).symm

/-- The overlap identification is compatible with the first chart inclusion: mapping the overlap
object to the fibre product, projecting to the first factor, and including into `Spec R` recovers
the chart inclusion at the product. -/
@[reassoc]
theorem specAwayOverlapIso_hom_fst_comp :
    (specAwayOverlapIso f g).hom ≫
        pullback.fst (specAwayMap f) (specAwayMap g) ≫ specAwayMap f =
      specAwayMap (f * g) :=
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_fst_comp _ _ _ _

/-- The overlap identification is compatible with the second chart inclusion: mapping the overlap
object to the fibre product, projecting to the second factor, and including into `Spec R` recovers
the chart inclusion at the product. -/
@[reassoc]
theorem specAwayOverlapIso_hom_snd_comp :
    (specAwayOverlapIso f g).hom ≫
        pullback.snd (specAwayMap f) (specAwayMap g) ≫ specAwayMap g =
      specAwayMap (f * g) :=
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_snd_comp _ _ _ _

/-! ### Non-vacuity -/

/-- **The overlap of two affine basic-open charts is non-empty exactly when `f · g` is not
nilpotent.** `range_specAwayMap_inter` turns the intersection into the basic open at the product,
and `PrimeSpectrum.basicOpen_eq_bot_iff` is Mathlib's criterion for that to be `⊥`.

The `Opens`-to-`Set` step is an `exact` rather than a `rw` on purpose: after the two rewrites the
ambient type of the coercion is the carrier of `Spec.locallyRingedSpaceObj (CommRingCat.of R)`, and
`rw [← Opens.ne_bot_iff_nonempty]` fails to see through it ("did not find an occurrence of the
pattern") although the two types are defeq. The same coercion is the subject of this file's
module docstring. -/
theorem specAwayOverlap_nonempty_iff :
    (Set.range (specAwayMap f).base ∩ Set.range (specAwayMap g).base).Nonempty ↔
      ¬ IsNilpotent (f * g) := by
  rw [range_specAwayMap_inter, range_specAwayMap]
  exact (Opens.ne_bot_iff_nonempty _).symm.trans
    (not_congr (PrimeSpectrum.basicOpen_eq_bot_iff _))

/-- **A worked overlap that is not empty**: `D(2) ∩ D(3) ⊆ Spec ℤ`, whose chart is
`Spec ℤ[1/6]`. So `specAwayOverlapIso` identifies the pullback of two chart inclusions with a
non-empty object, and is not a statement about empty spaces. -/
example : (Set.range (specAwayMap (2 : ℤ)).base ∩
    Set.range (specAwayMap (3 : ℤ)).base).Nonempty := by
  rw [specAwayOverlap_nonempty_iff]
  simp [isNilpotent_iff_eq_zero]

end AlgebraicGeometry

end
