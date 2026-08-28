import FormalSchemes.AffineSeparatedIso
import FormalSchemes.CompletionBasicOpenGlue

set_option linter.style.header false

/-!
# The formal completion is an `AffineChartedFibreDatumX.xGlued` (EGA I, 10.8)

Two lines on this tree build formal schemes by gluing adic charts, and until this file nothing
related them.

* The **completion line** — `formalCompletion R I hI` (`FormalSchemes/Completion.lean`),
  `completionBasicOpenGlued` and `completionBasicOpenGluedIso`
  (`FormalSchemes/CompletionBasicOpenGlue.lean`), `completionTwoPatch`
  (`FormalSchemes/CompletionGlueTwoPatch.lean`). Its objects are completions by construction.
* The **charted line** — `AffineChartedFibreDatumX` and its glued object
  `AffineChartedFibreDatumX.xGlued` (`FormalSchemes/GeneralFibreProductExposeX.lean`): an
  arbitrary index type, chart algebras `A i` that genuinely differ, transitions
  `τ i j : A_i{1/g_ij} ≃ₐ[R] A_j{1/g_ji}`, and a real triple cocycle. Its objects are adic charts
  glued along basic opens, with no completion anywhere in the statement.

Three module docstrings used to describe the second line's object as *future* work of EGA I 10.8 —
"the second ring and the overlap identification `θ`" — while it had been on the tree since the
`GeneralFibreProduct*` chain. This file supplies the missing link in the smallest honest form: the
formal completion of `Spec R` along `V(I)` **is** an `xGlued`, for the one-chart datum at the chart
algebra `R^`.

## Why the identification is definitional, and what that settles

`AdicCompletion.idealOfDefinition I` is an `abbrev` for `I.map (algebraMap R (AdicCompletion I R))`
(`FormalSchemes/Completion.lean`), which is *exactly* the ideal the charted line puts on a chart
algebra: the datum's field `isAdic` asks for `IsAdicRing (I.map (algebraMap R (A i)))`. So at
`A := AdicCompletion I R` the two lines are talking about the same ideal on the nose, and
`formalCompletion_eq_Spf_map` below is `rfl`.

That answers the question this file was written for. The charted line's ideal is pulled back from
the base ring `R` while the completion line's is `AdicCompletion.idealOfDefinition`; those look
different, and they are not.

## What this does **not** say

The one-chart datum has a vacuous overlap structure — `ULift Unit` has no two distinct indices — so
`completionXDatum` exercises none of the cocycle machinery. It identifies the two lines' *objects*,
not their gluing. The statement that would exercise the cocycle is the three-chart one: at
`A := R^` and three elements `f₀, f₁, f₂ ∈ R^` whose basic opens cover, `ThreeChartCover.gluedX`
should be `formalCompletion R I hI` too, by `ThreeChartCover.gluedXIsoSpf`. It is not stated here,
and the obstruction is recorded rather than guessed: `gluedXIsoSpf` carries `[TopologicalSpace R]`
and `[IsAdicRing I]` on the **base**, inherited through `gluedXToBase` and `chartToBase_naturality`
from `ThreeChartCover.tau_symm_algebraMap` (`FormalSchemes/ThreeChartCoverSeparated.lean`), and a
base that is already a complete adic ring is the case in which `R^` is not a completion of
anything. Whether those binders are removable is a hypothesis-weakening sweep over three files, not
a fact about completions.

## Main definitions and results

* `AlgebraicGeometry.formalCompletion_eq_Spf_map`: `formalCompletion R I hI` is `Spf` of
  `I.map (algebraMap R R^)` — the two lines' ideals agree definitionally.
* `AlgebraicGeometry.completionXDatum`: the one-chart `AffineChartedFibreDatumX` whose chart
  algebra is `R^`.
* `AlgebraicGeometry.completionXDatumGluedIso`: **the connection** —
  `(completionXDatum I hI).xGlued ≅ formalCompletion R I hI`.
* `AlgebraicGeometry.completionBasicOpenGluedIsoXGlued`: the same for the arbitrary-index
  basic-open glued completion — `completionBasicOpenGlued I hI f ≅ (completionXDatum I hI).xGlued`
  when the `f i` generate the unit ideal.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)

/-- **The completion line's ideal is the charted line's ideal.** `formalCompletion R I hI` is
`Spf (I·R^)`, and `I·R^` is spelled the way `AffineChartedFibreDatumX.isAdic` spells it — as the
extension along `algebraMap R R^`, not as an opaque `idealOfDefinition`. True by `rfl`; stated so
that the two lines can be compared without unfolding an `abbrev` at the call site. -/
theorem formalCompletion_eq_Spf_map :
    letI := AdicCompletion.isAdicRing_map I hI
    formalCompletion R I hI =
      FormalScheme.Spf (I.map (algebraMap R (AdicCompletion I R))) :=
  rfl

/-- **The formal completion as a one-chart affine-charted datum.** The single chart algebra is the
completion `R^` itself, with its ideal of definition `I·R^`; every overlap and cocycle field is
vacuous because `ULift Unit` has no two distinct indices.

The base ring `R` is arbitrary — in particular it is not assumed complete, which is the whole point
of a completion. -/
def completionXDatum : AffineChartedFibreDatumX R I hI (AdicCompletion I R) :=
  letI := AdicCompletion.isAdicRing_map I hI
  oneChartExposeXDatum R I hI (AdicCompletion I R)

/-- **The formal completion of `Spec R` along `V(I)` is an `xGlued`.**

This is `oneChartXGluedIso` at the chart algebra `R^`, transported along nothing at all:
`FormalScheme.Spf (I.map (algebraMap R R^))` *is* `formalCompletion R I hI`
(`formalCompletion_eq_Spf_map`), so the two lines meet without a comparison map.

The first declaration on this tree with a completion-line object on one side and a
charted-line object on the other. -/
def completionXDatumGluedIso :
    (completionXDatum I hI).xGlued ≅ formalCompletion R I hI :=
  letI := AdicCompletion.isAdicRing_map I hI
  oneChartXGluedIso hI

variable {ι : Type u} (f : ι → R)

/-- **The arbitrary-index basic-open glued completion is an `xGlued` too.** Issue 1123 proved that
`completionBasicOpenGlued I hI f`, glued from the completions of the basic opens `D(f i)`, is
`formalCompletion R I hI` when the `f i` generate the unit ideal; composing with
`completionXDatumGluedIso` puts a completion-line object built from a *genuine* cocycle on one side
and a charted-line object on the other.

The charted side is still the one-chart datum: what this says is that the two lines have the same
objects, not that they have the same presentations. -/
def completionBasicOpenGluedIsoXGlued (hcov : Ideal.span (Set.range f) = ⊤) :
    completionBasicOpenGlued I hI f ≅ (completionXDatum I hI).xGlued :=
  completionBasicOpenGluedIso I hI f hcov ≪≫ (completionXDatumGluedIso I hI).symm

end AlgebraicGeometry

end
