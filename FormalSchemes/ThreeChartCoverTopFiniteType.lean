import FormalSchemes.AwayTopFiniteType
import FormalSchemes.ChartedDatumTopFiniteType
import FormalSchemes.ThreeChartCoverSeparatedScheme

set_option linter.style.header false

/-!
# The three-chart open cover is of finite type over `Spf R`, and separated (EGA I §10.13, §10.15)

`FormalSchemes.ThreeChartCoverSeparatedScheme` (issue 852) put the open cover
`D(f₀) ∪ D(f₁) ∪ D(f₂) ⊆ Spf A` into the scheme-level separatedness vocabulary. This file supplies
its **other** EGA property — that its structural morphism is topologically of finite type — and
then states the two together, as `FormalSchemes.AffineSeparatedTopFiniteType` and
`FormalSchemes.TateSeparatedScheme` (issue 856) do for `Spf L` and for `𝔈_q`.

Both ingredients are general and neither is new mathematics here:

* `AffineChartedFibreDatumX.xStructMap_isRelativelyTopFiniteType`
  (`FormalSchemes.ChartedDatumTopFiniteType`) reduces the finite-type half to a statement about the
  chart algebras alone;
* `IsTopologicallyFiniteType.awayCompletion` (`FormalSchemes.AwayTopFiniteType`, issue 807) says
  each chart `A{1/f_i}^` is tf-type as soon as `A` is.

So the only work is the ideal-of-definition bookkeeping between the two conventions, which is
`map_algebraMap_awayCompletion` — see `chart_isTopologicallyFiniteType` below.

## The hypothesis, and what it is not

The separatedness half `datumX_isSeparatedOverSpf` holds for **every** `A` and every `f`: it is
proved from surjectivity of the chart codiagonals and needs nothing of `A`. The finite-type half
does need `A` topologically of finite type over `(R, I)` — as it must, since `Spf A` itself is not
of finite type over `Spf R` for a general adic `A`. The conjunction below therefore carries exactly
one hypothesis, and it is doing real work.

## What this is not: a chart-free statement

As in `FormalSchemes.ThreeChartCoverSeparatedScheme`, the object is named here through its own
presentation, as `(datumX I f B hI).xGlued`, because at the time this file was written the
three-chart cover had no gluing isomorphism onto an independently constructed formal scheme. The
genuinely chart-free form is about the open formal subscheme `D(f₀) ∪ D(f₁) ∪ D(f₂)` of `Spf A`;
that object and the identification of `xGlued` with it now exist, in
`FormalSchemes.ThreeChartCoverOpenSubscheme`, where both results below are restated with no
presentation in the statement (`coverSubscheme_isRelativelyTopFiniteType`,
`coverSubscheme_isSeparatedOverSpf`). Unlike `𝔈_q` (issue 856), this pairing is therefore a
statement about a presentation's glued object, not about a named formal scheme, and the module
docstring of the separatedness file says the same thing for the same reason.

## Main results

* `AlgebraicGeometry.ThreeChartCover.chart_isTopologicallyFiniteType`: each chart `A{1/f_i}^` is
  tf-type over `(R, I)` at the ideal spelling the datum uses.
* `AlgebraicGeometry.ThreeChartCover.datumX_isRelativelyTopFiniteType`,
  `AlgebraicGeometry.ThreeChartCover.gluedX_isRelativelyTopFiniteType`: **the open cover is
  topologically of finite type over `Spf R`**, in both spellings of the glued object.
* `AlgebraicGeometry.ThreeChartCover.datumX_isSeparatedOverSpf_and_isRelativelyTopFiniteType`:
  **both EGA properties of the open cover, in one statement.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7 (admissible formal `R`-schemes).
-/

noncomputable section

open CategoryTheory FormalSpectrum

universe u

namespace AlgebraicGeometry

namespace ThreeChartCover

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A]
variable (f : ULift.{u} (Fin 3) → A)
variable (B : Type u) [CommRing B] [Algebra R B]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Each chart of the open cover is topologically of finite type over `(R, I)`.**

`IsTopologicallyFiniteType.awayCompletion` (issue 807) proves this at the ideal
`awayCompletionIdeal (I·A) (f i)` — the extension of an ideal of the ring being localized, which is
that file's convention. The charted datum instead uses the canonical `I.map (algebraMap R _)`
spelling. `map_algebraMap_awayCompletion` is the bridge between the two, and it is needed
explicitly: `Ideal.map` unfolds to a `span` of an image, so no unifier identifies them. -/
theorem chart_isTopologicallyFiniteType (hI : I.FG)
    (hA : IsTopologicallyFiniteType R I A (I.map (algebraMap R A)))
    (i : ULift.{u} (Fin 3)) :
    IsTopologicallyFiniteType R I (chartAlgebra I f i)
      (I.map (algebraMap R (chartAlgebra I f i))) := by
  rw [map_algebraMap_awayCompletion (f i) rfl]
  exact IsTopologicallyFiniteType.awayCompletion (f i) hI hA

/-- **`D(f₀) ∪ D(f₁) ∪ D(f₂) ⊆ Spf A` is topologically of finite type over `Spf R`**
(EGA I §10.13), when `A` is.

The hypothesis is stated at an arbitrary ideal of definition `L`, since that is the form a tf-type
presentation comes in; `IsTopologicallyFiniteType.map_eq` moves it to the canonical spelling the
charts are built at. -/
theorem datumX_isRelativelyTopFiniteType (hI : I.FG) {L : Ideal A}
    (hA : IsTopologicallyFiniteType R I A L) :
    FormalScheme.IsRelativelyTopFiniteType R I
      (FormalScheme.Hom.mk (datumX I f B hI).xStructMap) := by
  have hA' : IsTopologicallyFiniteType R I A (I.map (algebraMap R A)) := by
    rw [IsTopologicallyFiniteType.map_eq hA]; exact hA
  exact (datumX I f B hI).xStructMap_isRelativelyTopFiniteType
    (fun i => chart_isTopologicallyFiniteType I f hI hA' i)

/-- **`gluedX` is topologically of finite type over `Spf R`**: `datumX_isRelativelyTopFiniteType`
at the tree's name for the glued object, which is `(datumX I f B hI).xGlued` by definition. -/
theorem gluedX_isRelativelyTopFiniteType (hI : I.FG) {L : Ideal A}
    (hA : IsTopologicallyFiniteType R I A L) :
    FormalScheme.IsRelativelyTopFiniteType R I
      (FormalScheme.Hom.mk (X := gluedX I f B hI) (datumX I f B hI).xStructMap) :=
  datumX_isRelativelyTopFiniteType I f B hI hA

/-- **The open cover `D(f₀) ∪ D(f₁) ∪ D(f₂) ⊆ Spf A` is separated over `Spf R` and topologically of
finite type over it** (EGA I §10.15 and §10.13), when `A` is tf-type — both EGA properties of the
same structural morphism `(datumX I f B hI).xStructMap`, in one statement.

The two halves read that morphism through different wrappers, `IsSeparatedOverSpf` taking the
locally-ringed-space morphism and `IsRelativelyTopFiniteType` its `FormalScheme.Hom.mk`, because
the separatedness API is stated at `LocallyRingedSpace` to match `fibreLiftAdic`. They are the same
morphism; `FormalScheme.Hom` is a structure extending `LocallyRingedSpace.Hom`.

Only the finite-type half consumes `hA`: separatedness of this cover holds for every `A`. -/
theorem datumX_isSeparatedOverSpf_and_isRelativelyTopFiniteType (hI : I.FG) {L : Ideal A}
    (hA : IsTopologicallyFiniteType R I A L) :
    FormalScheme.IsSeparatedOverSpf hI (datumX I f B hI).xGlued
        (datumX I f B hI).xStructMap ∧
      FormalScheme.IsRelativelyTopFiniteType R I
        (FormalScheme.Hom.mk (datumX I f B hI).xStructMap) :=
  ⟨datumX_isSeparatedOverSpf I f B hI, datumX_isRelativelyTopFiniteType I f B hI hA⟩

end ThreeChartCover

end AlgebraicGeometry

end
