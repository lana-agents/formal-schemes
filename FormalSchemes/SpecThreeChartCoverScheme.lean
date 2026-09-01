import FormalSchemes.ChartedSchemeDatumScheme
import FormalSchemes.SpecThreeChartCoverToSpec

set_option linter.style.header false

/-!
# The three-chart cover as a scheme, and its affineness (EGA I, 10.8)

`FormalSchemes.ChartedSchemeDatumScheme` promotes the glued object of an arbitrary
`AlgebraicGeometry.ChartedSchemeDatum` to a `AlgebraicGeometry.Scheme`. This file instantiates that
at `AlgebraicGeometry.SpecThreeChartCover.datum` — `Spec A` presented by three basic opens
`D(f₀)`, `D(f₁)`, `D(f₂)` — and identifies the result with `Spec A` when the charts cover.

## Why this witness and not the two-patch one

The promotion is a construction on a datum, so instantiating it at
`AlgebraicGeometry.ChartedSchemeDatum.ofTwoPatch` would prove nothing that
`FormalSchemes.SpecTwoPatchScheme` did not already prove: that datum lives on `ULift Bool`, where
no triple of indices is pairwise distinct, so its `t'`, `t_fac` and `cocycle` fields are
`False.elim` and the arbitrary-index machinery is never exercised beyond two charts.

`SpecThreeChartCover.datum` is the tree's only datum whose triple-overlap fields are **not**
vacuous: `AlgebraicGeometry.SpecThreeChartCover.datum_t'_zero_one_two` evaluates `t'` at the
inhabited triple `⟨0⟩, ⟨1⟩, ⟨2⟩` and gets `ChartedSchemeDatum.specAlgDataT'`, and
`AlgebraicGeometry.SpecThreeChartCover.intCover_overlap_nonempty` says the double overlap it
transports is non-empty. So `gluedScheme` below is a scheme glued from a datum that genuinely uses
the cocycle data.

## The statement the two-patch line could not make

`FormalSchemes.SpecTwoPatchNonAffine` shows the two-patch glued scheme is, at the doubled origin,
**neither separated nor affine**. So no general affineness statement is available one file up, and
none is attempted there. Here there is a hypothesis that makes one true:
`AlgebraicGeometry.SpecThreeChartCover.isAffine_gluedScheme` says that when
`Ideal.span (Set.range f) = ⊤` — the three basic opens cover `Spec A` — the glued scheme is affine.

The content is entirely `AlgebraicGeometry.SpecThreeChartCover.isIso_toSpec`, which is landed at
`LocallyRingedSpace`. Lifting it to `Scheme` is not a transport: `Scheme.forgetToLocallyRingedSpace`
is fully faithful, hence reflects isomorphisms, so the locally ringed space statement *is* the
scheme statement. The one place that needs care is that the `IsIso` hypothesis must be supplied at
the functor's spelling `Scheme.forgetToLocallyRingedSpace.map g` rather than at `g.toLRSHom`: the
two are defeq but instance search does not unfold `Functor.map`, and supplying the latter leaves
`isIso_of_reflects_iso`'s instance argument unsynthesised. This is the same shape as the ascription
trap `FormalSchemes.ChartedSchemeDatumScheme` documents, one layer out.

## Main definitions and results

* `AlgebraicGeometry.SpecThreeChartCover.gluedScheme`: the three-chart glued object as a scheme,
  with `..gluedScheme_toLocallyRingedSpace` identifying its space with
  `AlgebraicGeometry.SpecThreeChartCover.glued` by `rfl`, and quasi-compact by
  `..compactSpace_gluedScheme` since the index type is `ULift (Fin 3)`.
* `AlgebraicGeometry.SpecThreeChartCover.gluedSchemeToSpec`: the cover map as a morphism of
  schemes, with `..isIso_gluedSchemeToSpec` and `..gluedSchemeIsoSpec` under the covering
  hypothesis.
* `AlgebraicGeometry.SpecThreeChartCover.isAffine_gluedScheme`: **the glued scheme is affine when
  the charts cover.**
* `AlgebraicGeometry.SpecThreeChartCover.gluedSchemeIsoSpec_intCover`: the isomorphism exhibited at
  `Spec ℤ` covered by `D(2)`, `D(3)`, `D(5)`, so the capstone is not a statement about an empty
  cover.

## Scope

Nothing here is claimed about `gluedScheme` **without** the covering hypothesis. Under it the
scheme is `Spec A`; without it `AlgebraicGeometry.SpecThreeChartCover.isOpenImmersion_toSpec` still
gives an open immersion into `Spec A`, but that statement is at `LocallyRingedSpace` and is not
restated here — nothing needs it, and restating it would be a second name for one fact.

No separatedness statement is attempted, here or anywhere at this generality, for the reason given
above.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace SpecThreeChartCover

variable {A : Type u} [CommRing A] (I : Ideal A) (f : ULift.{u} (Fin 3) → A)

/-- **The three-chart glued object as a scheme**, `D(f₀) ∪ D(f₁) ∪ D(f₂)`. -/
def gluedScheme : Scheme.{u} := (datum I f).specScheme

/-- The promotion changes nothing underneath: this is `glued I f` with a `Scheme` structure on top.
-/
theorem gluedScheme_toLocallyRingedSpace :
    (gluedScheme I f).toLocallyRingedSpace = glued I f := rfl

/-- The datum's index type is `ULift (Fin 3)`, so it is finite — which is the hypothesis
`ChartedSchemeDatum.specScheme_compactSpace` takes, and it has to be stated here because instance
search will not unfold the projection `(datum I f).J`. -/
instance finite_datum_J : Finite (datum I f).J :=
  inferInstanceAs (Finite (ULift.{u} (Fin 3)))

/-- **The glued scheme is quasi-compact**, with no hypothesis: `finite_datum_J` above supplies
`ChartedSchemeDatum.specScheme_compactSpace`'s `[Finite D.J]`.

Restating it at `gluedScheme` is not redundant. `gluedScheme` is a plain `def`, and instance search
matches only up to reducible transparency, so `CompactSpace (gluedScheme I f)` is **not**
synthesised from the instance at `(datum I f).specScheme` — the same class of gap as the two defeq
traps this cluster documents, here between a `def` and its body rather than between two spellings
of one term. -/
instance compactSpace_gluedScheme : CompactSpace (gluedScheme I f) :=
  inferInstanceAs (CompactSpace ((datum I f).specScheme))

/-- **The cover map to `Spec A` as a morphism of schemes.** -/
def gluedSchemeToSpec : gluedScheme I f ⟶ Spec (CommRingCat.of A) :=
  ⟨toSpec I f⟩

theorem gluedSchemeToSpec_toLRSHom : (gluedSchemeToSpec I f).toLRSHom = toSpec I f := rfl

/-- **When the three basic opens cover `Spec A`, the cover map is an isomorphism of schemes.**

`isIso_toSpec` is the same statement at `LocallyRingedSpace`, and
`Scheme.forgetToLocallyRingedSpace` is fully faithful, so it reflects the isomorphism. The `haveI`
is stated at `Scheme.forgetToLocallyRingedSpace.map _` and not at `_.toLRSHom` on purpose: the two
are defeq, but instance search does not unfold `Functor.map`, so the latter spelling leaves
`isIso_of_reflects_iso`'s instance argument unsynthesised. -/
theorem isIso_gluedSchemeToSpec (hcov : Ideal.span (Set.range f) = ⊤) :
    IsIso (gluedSchemeToSpec I f) := by
  haveI : IsIso (Scheme.forgetToLocallyRingedSpace.map (gluedSchemeToSpec I f)) :=
    isIso_toSpec I f hcov
  exact isIso_of_reflects_iso _ Scheme.forgetToLocallyRingedSpace

/-- **The glued scheme is `Spec A`** when the three basic opens cover it. The `Scheme`-level twin of
`AlgebraicGeometry.SpecThreeChartCover.gluedIsoSpec`. -/
def gluedSchemeIsoSpec (hcov : Ideal.span (Set.range f) = ⊤) :
    gluedScheme I f ≅ Spec (CommRingCat.of A) :=
  letI := isIso_gluedSchemeToSpec I f hcov
  asIso (gluedSchemeToSpec I f)

theorem gluedSchemeIsoSpec_hom (hcov : Ideal.span (Set.range f) = ⊤) :
    (gluedSchemeIsoSpec I f hcov).hom = gluedSchemeToSpec I f := rfl

/-- **The glued scheme is affine when the charts cover.** This is the statement the two-patch line
cannot make: its glued scheme is provably non-affine at the doubled origin
(`FormalSchemes.SpecTwoPatchNonAffine`). Here the covering hypothesis rules that out, and the glued
object is `Spec A` on the nose. -/
theorem isAffine_gluedScheme (hcov : Ideal.span (Set.range f) = ⊤) :
    IsAffine (gluedScheme I f) :=
  letI := isIso_gluedSchemeToSpec I f hcov
  IsAffine.of_isIso (gluedSchemeToSpec I f)

/-- **The isomorphism at a concrete cover**: `Spec ℤ` presented by `D(2)`, `D(3)`, `D(5)`, glued
back to `Spec ℤ` as a scheme. The `Scheme`-level twin of
`AlgebraicGeometry.SpecThreeChartCover.gluedIsoSpec_intCover`, and the reason the capstone above is
not a statement about an empty cover. -/
def gluedSchemeIsoSpec_intCover (I : Ideal ℤ) :
    gluedScheme I intCover ≅ Spec (CommRingCat.of ℤ) :=
  gluedSchemeIsoSpec I intCover span_range_intCover

/-- **The concrete three-chart scheme is affine.** -/
theorem isAffine_gluedScheme_intCover (I : Ideal ℤ) : IsAffine (gluedScheme I intCover) :=
  isAffine_gluedScheme I intCover span_range_intCover

end SpecThreeChartCover

end AlgebraicGeometry

end
