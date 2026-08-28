import FormalSchemes.AffineSeparatedIso
import FormalSchemes.CompletionBasicOpenGlue
import FormalSchemes.ThreeChartCoverOpenImmersion

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

## The gluing, not only the objects

The one-chart datum has a vacuous overlap structure — `ULift Unit` has no two distinct indices — so
`completionXDatum` exercises none of the cocycle machinery, and on its own it identifies the two
lines' *objects* rather than their gluing. `threeChartCoverGluedXIsoCompletion` closes that gap: at
`A := R^` and three elements `f₀, f₁, f₂ ∈ R^` whose basic opens cover, `ThreeChartCover.gluedX`
**is** `formalCompletion R I hI`, and `ThreeChartCover.datumX_xt'_eq` pins that datum's `xt'` to
the derived transition at every pairwise-distinct triple, so the identification runs through a real
triple overlap.

An earlier version of this section recorded the three-chart statement as blocked: `gluedXIsoSpf`
carried `[TopologicalSpace R]` and `[IsAdicRing I]` on the **base**, and a base that is already a
complete adic ring is the case in which `R^` is not a completion of anything. Those binders were
ambient-`variable` inclusion — the same defect `oneChartXGluedIso` had one level up — and are now
`omit`ted at eighteen declarations across five `ThreeChartCover*` files. Eleven of those lie on the
path from `ThreeChartCover.tau_symm_algebraMap` to `gluedXIsoSpf`; the other seven are downstream
consumers that `linter.unusedSectionVars` flagged once the binders stopped arriving from below. No
proof changed.

## What this still does **not** say

Both statements below present a *single* `Spf` — of `R^` in one case, of `R^` again in the other —
so the chart algebras are all localizations of one ring. The genuinely different-rings case of
EGA I 10.8, an arbitrary affine cover of an arbitrary scheme, is a further step; and
`AffineChartedFibreDatumX` completes along `V(I)` pulled back from a single base ring `R`, which is
a real restriction rather than a gap — see the frontier note on issue 60.

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
* `AlgebraicGeometry.threeChartCoverGluedXIsoCompletion`: **the connection at a non-vacuous
  datum** — the three-chart basic-open cover of `Spf (I·R^)` glues to `formalCompletion R I hI`.
* `AlgebraicGeometry.threeChartCoverGluedXIsoCompletionOne`: that its covering hypothesis is
  satisfiable over every `(R, I)` with `I.FG`.

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

/-! ### At a datum with a genuine triple overlap -/

section ThreeChart

variable (f : ULift.{u} (Fin 3) → AdicCompletion I R)

/-- **The three-chart cover of the formal completion glues back to it.** `ThreeChartCover.datumX`
presents `Spf (I·R^)` by three basic opens `D(f₀)`, `D(f₁)`, `D(f₂)`; when those cover, the glued
object is `formalCompletion R I hI` on the nose — the right-hand side of
`ThreeChartCover.gluedXIsoSpf` at `A := R^` *is* the completion, by `formalCompletion_eq_Spf_map`,
so no `eqToHom` appears.

This is `completionXDatumGluedIso` at a datum that is not vacuous: `ULift (Fin 3)` has
pairwise-distinct triples, and `ThreeChartCover.datumX_xt'_eq` (concretely
`ThreeChartCover.datumX_xt'_zero_one_two`) identifies the datum's `xt'` there with the transition
derived from `sigma`, not with `False.elim`. So the two lines agree through a real triple overlap
and not only on objects.

The base-change factor is `B := R` — the datum's `B` records which affine base the fibre product
is taken over and plays no part in `xGlued`. -/
def threeChartCoverGluedXIsoCompletion
    (hcov : basicOpen (I.map (algebraMap R (AdicCompletion I R))) (f ⟨0⟩) ⊔
      basicOpen (I.map (algebraMap R (AdicCompletion I R))) (f ⟨1⟩) ⊔
      basicOpen (I.map (algebraMap R (AdicCompletion I R))) (f ⟨2⟩) = ⊤) :
    ThreeChartCover.gluedX I f R hI ≅ formalCompletion R I hI :=
  letI := AdicCompletion.isAdicRing_map I hI
  ThreeChartCover.gluedXIsoSpf I f R hI hcov

/-- **The covering hypothesis is satisfiable**, so the theorem above is not vacuous: taking
`f₀ = f₁ = f₂ = 1` covers `Spf (I·R^)` by `basicOpen_one`, for every `(R, I)` with `I` finitely
generated. The three charts are then `R^{1/1}^`, and `ThreeChartCover.datumX_xt'_eq` still pins
`xt'` to the derived transition at `0, 1, 2` — the datum is degenerate in its *elements*, not in
its overlap structure. -/
def threeChartCoverGluedXIsoCompletionOne :
    ThreeChartCover.gluedX I (fun _ : ULift.{u} (Fin 3) => (1 : AdicCompletion I R)) R hI ≅
      formalCompletion R I hI :=
  threeChartCoverGluedXIsoCompletion I hI _ (by
    letI := AdicCompletion.isAdicRing_map I hI
    simp [basicOpen_one])

end ThreeChart

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
