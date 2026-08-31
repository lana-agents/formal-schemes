import Mathlib.AlgebraicGeometry.AffineScheme
import FormalSchemes.ChartedCompletionToScheme

set_option linter.style.header false

/-!
# The glued object of a charted datum is a scheme, at an arbitrary index (EGA I, 10.8)

`FormalSchemes/ChartedSchemeDatum.lean` glues the affine charts `Spec (C i)` of a
`AlgebraicGeometry.ChartedSchemeDatum` along the identifications `θ i j` of their basic opens,
producing `AlgebraicGeometry.ChartedSchemeDatum.specGlued`, and
`FormalSchemes/ChartedCompletionToScheme.lean` builds the canonical morphism
`AlgebraicGeometry.ChartedCompletionDatum.toScheme` from the glued formal completion into it. Both
live in `LocallyRingedSpace`, because that is the category `formalCompletion.toSpec` lands in, and
both files' scope sections recorded the promotion to `AlgebraicGeometry.Scheme` as a separate
carve.

This file is that carve, at an arbitrary index type. `FormalSchemes/SpecTwoPatchScheme.lean` is the
same carve on `ULift Bool`; this file is its arbitrary-index generalisation and takes the same
route for the same stated reason.

```
completionGlued  ──toSchemeHom──→  specScheme : Scheme
```

## How it is built

Not as an `AlgebraicGeometry.Scheme.GlueData`. That route would glue the `Spec (C i)` afresh in
`Scheme` and then owe an identification of the resulting locally ringed space glue datum with
`AlgebraicGeometry.ChartedSchemeDatum.specLRSGlueData`. Instead we use
`LocallyRingedSpace.IsOpenImmersion.scheme`, which turns a locally ringed space covered by open
immersions out of affines into a scheme *on the same carrier*: the charts
`AlgebraicGeometry.ChartedSchemeDatum.specι` are open immersions
(`AlgebraicGeometry.ChartedSchemeDatum.specι_isOpenImmersion`) and jointly surjective
(`AlgebraicGeometry.ChartedSchemeDatum.specGlued_jointly_surjective`, already in the
`∃ i, ∃ y, (specι i).base y = x` shape the hypothesis wants), and its `toLocallyRingedSpace` field
is the input space on the nose.

`AlgebraicGeometry.ChartedSchemeDatum.specScheme_toLocallyRingedSpace` is therefore `rfl`, which is
what lets every landed result about `specGlued` be reused at the scheme with no transport. In
particular `AlgebraicGeometry.ChartedCompletionDatum.toSchemeHom` below is a **retyping** of
`toScheme` and not a transport along an equality — there is no `eqToHom` in this file.

At an arbitrary index the two-patch file's two `match`-reduction annoyances do not arise. Its
`specTwoPatchSchemeCover` has to spell out `inferInstanceAs` per constructor because instance
search does not reduce the `match` on `⟨false⟩`; here the chart family is a plain `fun i => …` and
one `inferInstanceAs` at a variable `i` does it. The *other* trap it documents — that inside
`LocallyRingedSpace.IsOpenImmersion.scheme`'s anonymous constructor the chart is ascribed at
`Spec.toLocallyRingedSpace.obj (op R) ⟶ _`, which is defeq but not *reducibly* defeq to
`Spec.locallyRingedSpaceObj R ⟶ _`, so `inferInstance` does not see through it — does still apply,
and the `IsOpenImmersion` witness is named here for that reason.

## Main definitions and results

* `AlgebraicGeometry.ChartedSchemeDatum.specScheme`: the glued object as a scheme, with
  `..specScheme_toLocallyRingedSpace` identifying its underlying locally ringed space with
  `specGlued` by `rfl`.
* `AlgebraicGeometry.ChartedSchemeDatum.specSchemeι`: the charts as morphisms of schemes, open
  immersions by `..specSchemeι_isOpenImmersion`, jointly surjective by
  `..specScheme_jointly_surjective`, with affine ranges by `..isAffineOpen_specSchemeι`.
* `AlgebraicGeometry.ChartedSchemeDatum.specSchemeCover`: the charts as a
  `AlgebraicGeometry.Scheme.OpenCover` on the datum's own index type, affine by
  `..specSchemeCover_isAffine`.
* `AlgebraicGeometry.ChartedSchemeDatum.specScheme_compactSpace`: the glued scheme is
  quasi-compact **when the index type is finite**.
* `AlgebraicGeometry.ChartedCompletionDatum.specScheme` and
  `AlgebraicGeometry.ChartedCompletionDatum.toSchemeHom`: the ambient scheme and the completion
  morphism `X_{/Y} ⟶ X` of EGA I, 10.8 with `X` an actual scheme, characterised chart by chart by
  `..completionι_comp_toSchemeHom`.

## Scope

**Finiteness is a hypothesis on one declaration, not on the datum.** An arbitrary-index datum has
no reason to have a finite index type, and `specScheme` is defined without one; only
`..specScheme_compactSpace` and the `Finite` instance it consumes take `[Finite D.J]`.

**Nothing here decides whether `specScheme` is affine or separated, and nothing general is true.**
`FormalSchemes.SpecTwoPatchNonAffine` settles the two-patch doubled-origin case in the negative —
the affine line over `ℚ` with a doubled origin is neither separated nor affine — so no statement at
this generality could hold. A datum whose glued scheme *is* affine is exhibited in
`FormalSchemes.SpecThreeChartCoverScheme`, under the hypothesis that the charts cover.

Nothing here promotes `completionGlued` to a `FormalScheme`, or claims it is *the* formal
completion of `specScheme` in any sense beyond the morphism; `toScheme_unique` one layer down is
all the tree has.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace ChartedSchemeDatum

variable (D : ChartedSchemeDatum.{u})

/-- **The glued object of a charted datum as a scheme.**

`LocallyRingedSpace.IsOpenImmersion.scheme` promotes a locally ringed space to a scheme given, at
each point, an open immersion from a `Spec` whose range contains it. The charts of `specGlued`
supply exactly that, by `specGlued_jointly_surjective`.

The `IsOpenImmersion` witness has to be named rather than left to `inferInstance`: inside the
anonymous constructor the chart is ascribed at `Spec.toLocallyRingedSpace.obj (op R) ⟶ _`, which is
defeq but not *reducibly* defeq to `Spec.locallyRingedSpaceObj R ⟶ _`, so instance search does not
see through it. -/
def specScheme : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme D.specGlued (by
    intro x
    obtain ⟨i, y, hy⟩ := D.specGlued_jointly_surjective x
    exact ⟨CommRingCat.of (D.C i), D.specι i, ⟨y, hy⟩, D.specι_isOpenImmersion i⟩)

/-- **The promotion changes nothing underneath.** `LocallyRingedSpace.IsOpenImmersion.scheme` sets
its `toLocallyRingedSpace` field to the space it was given, so this is `rfl` — which is what lets
every result about `specGlued` be reused at the scheme without transport, and what makes
`ChartedCompletionDatum.toSchemeHom` a retyping rather than a transport. -/
theorem specScheme_toLocallyRingedSpace : D.specScheme.toLocallyRingedSpace = D.specGlued := rfl

/-- The `i`-th chart of the glued scheme, as a morphism of schemes. -/
def specSchemeι (i : D.J) : Spec (CommRingCat.of (D.C i)) ⟶ D.specScheme :=
  ⟨D.specι i⟩

/-- The `i`-th chart of the glued scheme is the `i`-th chart of the glued locally ringed space. -/
theorem specSchemeι_toLRSHom (i : D.J) : (D.specSchemeι i).toLRSHom = D.specι i := rfl

instance specSchemeι_isOpenImmersion (i : D.J) : IsOpenImmersion (D.specSchemeι i) :=
  D.specι_isOpenImmersion i

/-- **The charts cover the glued scheme.** This is `specGlued_jointly_surjective` read at the
scheme; the two statements have the same proof term because the carriers are the same. -/
theorem specScheme_jointly_surjective (x : D.specScheme) :
    ∃ (i : D.J) (y : Spec (CommRingCat.of (D.C i))), (D.specSchemeι i).base y = x :=
  D.specGlued_jointly_surjective x

/-- **The charts as an open cover of the glued scheme**, indexed by the datum's own index type.

The final argument is the instance argument `∀ j, IsOpenImmersion (map j)`. Unlike the two-patch
case (`AlgebraicGeometry.specTwoPatchSchemeCover`), where the chart family is a `match` that
instance search will not reduce, here it is a plain `fun i => …` and one `inferInstanceAs` at a
variable index discharges it. -/
def specSchemeCover : D.specScheme.OpenCover :=
  Scheme.Cover.mkOfCovers D.J (fun i => Spec (CommRingCat.of (D.C i)))
    (fun i => D.specSchemeι i)
    (fun x => D.specScheme_jointly_surjective x)
    (fun i => inferInstanceAs (IsOpenImmersion (D.specSchemeι i)))

theorem specSchemeCover_X (i : D.J) :
    D.specSchemeCover.X i = Spec (CommRingCat.of (D.C i)) := rfl

theorem specSchemeCover_f (i : D.J) : D.specSchemeCover.f i = D.specSchemeι i := rfl

/-- **The chart cover is an affine cover**: every member is a spectrum. -/
theorem specSchemeCover_isAffine (i : D.J) : IsAffine (D.specSchemeCover.X i) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (D.C i))))

/-- **Each chart's range is an affine open** of the glued scheme. -/
theorem isAffineOpen_specSchemeι (i : D.J) : IsAffineOpen (D.specSchemeι i).opensRange :=
  isAffineOpen_opensRange _

/-- The cover's index type is the datum's, so it is finite exactly when that is. The hypothesis is
taken here and not on the datum: an arbitrary-index `ChartedSchemeDatum` has no reason to be
finite. -/
instance specSchemeCover_finite_I₀ [Finite D.J] : Finite D.specSchemeCover.I₀ :=
  inferInstanceAs (Finite D.J)

/-- **A datum with finitely many charts glues to a quasi-compact scheme**, being covered by
finitely many spectra. At two patches this is `AlgebraicGeometry.specTwoPatchScheme_compactSpace`.
-/
instance specScheme_compactSpace [Finite D.J] : CompactSpace D.specScheme := by
  refine D.specSchemeCover.compactSpace (H := ?_)
  intro i
  exact inferInstanceAs (CompactSpace (Spec (CommRingCat.of (D.C i))))

end ChartedSchemeDatum

/-! ### The completion morphism, with a genuine scheme on the right -/

namespace ChartedCompletionDatum

variable (D : ChartedCompletionDatum.{u})

/-- **The ambient scheme of a completion datum**, mirroring
`AlgebraicGeometry.ChartedCompletionDatum.specGlued` and `..specι`, which forget to the underlying
`ChartedSchemeDatum` in the same way. -/
def specScheme : Scheme.{u} := D.toChartedSchemeDatum.specScheme

/-- The ambient scheme sits on the glued locally ringed space, by `rfl` twice over. -/
theorem specScheme_toLocallyRingedSpace :
    D.specScheme.toLocallyRingedSpace = D.specGlued := rfl

/-- The `i`-th chart of the ambient scheme, as a morphism of schemes. -/
def specSchemeι (i : D.J) : Spec (CommRingCat.of (D.C i)) ⟶ D.specScheme :=
  D.toChartedSchemeDatum.specSchemeι i

theorem specSchemeι_toLRSHom (i : D.J) : (D.specSchemeι i).toLRSHom = D.specι i := rfl

/-- **The completion morphism `X_{/Y} ⟶ X` of EGA I, 10.8, with `X` an actual scheme**, at an
arbitrary index. This is `AlgebraicGeometry.ChartedCompletionDatum.toScheme` retyped along
`specScheme_toLocallyRingedSpace`, which is `rfl`, so it is literally the same morphism; what the
promotion buys is that the target is now the underlying space of a `Scheme`, together with the
whole `Scheme` API on that target. At two patches this is
`AlgebraicGeometry.completionTwoPatchToSchemeHom`. -/
def toSchemeHom :
    D.completionGlued.toLocallyRingedSpace ⟶ D.specScheme.toLocallyRingedSpace :=
  D.toScheme

/-- **The computation rule**: on the `i`-th chart the completion morphism is the affine
`formalCompletion.toSpec` followed by the `i`-th chart of the ambient scheme. This is
`..completionι_comp_toScheme` with the chart read as a scheme morphism, and it characterises
`toSchemeHom` chart by chart because `..toScheme_unique` does. -/
theorem completionι_comp_toSchemeHom (i : D.J) :
    D.completionι i ≫ D.toSchemeHom =
      formalCompletion.toSpec (D.C i) (D.K i) (D.hK i) ≫ (D.specSchemeι i).toLRSHom :=
  D.completionι_comp_toScheme i

end ChartedCompletionDatum

end AlgebraicGeometry

end
