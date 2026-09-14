import FormalSchemes.GeneralSeparatedScheme
import FormalSchemes.BasicOpenCoverSeparated

set_option linter.style.header false

/-!
# A basic-open cover of a formal affine is separated, as a formal scheme (EGA I §10.15)

`FormalSchemes/BasicOpenCoverSeparated.lean` (issue 779) proves
`AlgebraicGeometry.BasicOpenCover.datumX_isSeparated`: the basic-open cover datum presenting the
union of a family `D(f_i) ⊆ Spf A` satisfies `BothChartedFibreDatumXY.IsSeparated`, a predicate on
a **presentation**. Issue 842 (`FormalSchemes/GeneralSeparatedScheme.lean`) introduced
`FormalScheme.IsSeparatedOverSpf`, the same property stated of a formal scheme and its structural
morphism, with no chart data. This file carries that value across, completing the family of sequels
that issue 844 named: `Spf A` (issue 844), `𝔈_q` (issue 847), and the open cover here. The index
type is arbitrary, as it is in the modules this one sits on.

## What is new here, and what is not

The transport itself is `FormalScheme.isSeparatedOverSpf_of_isSeparated` applied once, and it needs
no gluing isomorphism: unlike `𝔈_q` and `Spf A`, the object of interest *is* the datum's glued
object — `BasicOpenCover.gluedX` is by definition `(datumX I f B hI).xGlued`. So no analogue of
`oneChartXGluedIso_hom_comp_structMap` (issue 844) or of
`tateXGluedHom_comp_tateCurveModelStructMap` (issue 813) is required, and none exists.

The consequence is worth stating plainly, because it bounds what this file claims: the open cover
has no construction independent of its presentation, so the structural morphism can only be named
as `(datumX I f B hI).xStructMap`. This is **not** the chart-free headline that
`tateCurveModel_isSeparatedOverSpf` is. Making it one would mean identifying `gluedX` with an open
formal subscheme of `Spf A` — the identification that `FormalSchemes.BasicOpenCoverSeparated`'s
own module docstring records as deliberately avoided, since the separatedness proof does not need
it.

That identification has since been made, at an arbitrary index type like this file's:
`FormalSchemes.BasicOpenCoverOpenSubscheme` builds the open formal subscheme `⋃ D(f_i)` of
`Spf A` and restates the theorem below about it, as
`BasicOpenCover.coverSubscheme_isSeparatedOverSpf`, with no presentation in the statement. What is
above stays true of *this* file, which still names the datum; the chart-free form is downstream.

## Why the third value is worth having anyway

It is the first inhabitant of `FormalScheme.IsSeparatedOverSpf` whose witnessing presentation has
**non-vacuous triple-overlap data**. The two existing values are separated for reasons that never
reach a triple overlap: `oneChart_isSeparated` (`FormalSchemes.AffineSeparatedValue`) is indexed by
`ULift Unit` and `tate_isSeparated` (`FormalSchemes.TateSeparatedValue`) by `ULift Bool`, so in both
the `σ`/`hστ`/`hσc` arguments are the vacuous `fun _ _ _ h _ _ => (…).elim` family — there is no
triple of pairwise distinct indices to supply. Here the index type is a variable, the cocycle
data is `ThreeChart.sigma` and its two laws, and `datumX_t'_eq`
(`FormalSchemes.BasicOpenCoverDatum`) proves that the derived geometric transition at a pairwise
distinct triple really is that data and not `False.elim`. That the hypotheses of those statements
are satisfiable at all is where three indices are still wanted:
`ThreeChart.exists_pairwise_distinct` and `BasicOpenCover.datumX_xt'_zero_one_two` supply a
pairwise distinct triple in `ULift (Fin 3)`, which `ULift Bool` has none of.

So this is the first evidence that `IsSeparatedOverSpf`'s existential quantifier ranges over
presentations whose triple-overlap obligations are actually discharged, rather than only over ones
where they are vacuous. That matters for the open question of whether the presentation-level
predicate should eventually be retired in favour of this one: 842's review asked for several real
consumers first, and a third value that exercises a part of the definition the other two skip is
worth more towards that than a third vacuous one.

## Main results

* `AlgebraicGeometry.BasicOpenCover.datumX_isSeparatedOverSpf`: the glued object of the
  basic-open cover datum is separated over `Spf R`, in the scheme-level vocabulary.
* `AlgebraicGeometry.BasicOpenCover.gluedX_isSeparatedOverSpf`: the same, stated at the tree's name
  `gluedX` for that object.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

namespace BasicOpenCover

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A]
variable {J : Type u} (f : J → A)
variable (B : Type u) [CommRing B] [Algebra R B]

/-- **The glued object of the basic-open cover datum is separated over `Spf R`** (EGA I §10.15), as
a property of the formal scheme and its structural morphism rather than of the presentation.

The third inhabitant of `FormalScheme.IsSeparatedOverSpf`, and the first whose witnessing
presentation discharges a non-vacuous triple-overlap obligation. -/
theorem datumX_isSeparatedOverSpf (hI : I.FG) :
    FormalScheme.IsSeparatedOverSpf hI (datumX I f B hI).xGlued
      (datumX I f B hI).xStructMap :=
  FormalScheme.isSeparatedOverSpf_of_isSeparated hI _ _ _ _ (datumX_isSeparated I f B hI)

/-- **`gluedX` is separated over `Spf R`**: `datumX_isSeparatedOverSpf` at the tree's name for the
glued object. `BasicOpenCover.gluedX` is `(datumX I f B hI).xGlued` by definition, so the two
statements are the same up to unfolding one `def`; both spellings are provided because consumers of
`FormalSchemes.BasicOpenCoverDatum` use `AlgebraicGeometry.BasicOpenCover.gluedX` while the general
theory speaks of `AlgebraicGeometry.AffineChartedFibreDatumX.xGlued`. -/
theorem gluedX_isSeparatedOverSpf (hI : I.FG) :
    FormalScheme.IsSeparatedOverSpf hI (gluedX I f B hI) (datumX I f B hI).xStructMap :=
  datumX_isSeparatedOverSpf I f B hI

end BasicOpenCover

end AlgebraicGeometry

end
