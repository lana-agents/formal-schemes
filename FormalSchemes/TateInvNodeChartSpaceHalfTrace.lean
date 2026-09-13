import FormalSchemes.TateInvNodeChartSpaceHalf
import FormalSchemes.TateInvNodeChartPatchChartTrace

set_option linter.style.header false

/-!
# The space half of hypothesis 4, with no germ in it

`FormalSchemes.TateInvNodeChartSpaceHalf` put all three clauses of the space half of hypothesis 4
of `AlgebraicGeometry.exists_formalScheme_of_adicSections` on the chain
(`AlgebraicGeometry.isIso_base_nodeChartQuotientHom_iff`), and
`FormalSchemes.TateInvNodeChartPatchChartTrace` replaced the first of those clauses — orbit
separation, stated through the germ-invertibility pattern of
`AlgebraicGeometry.nodeChartPsi` — by the equality of the traces of two primes on
`AlgebraicGeometry.tateInvNodeChartAwaySubring`
(`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff_forall_mem_asIdeal_iff`).

This file is the composite of the two, and it is the whole point of the pair:

> `AlgebraicGeometry.isIso_base_nodeChartQuotientHom_iff_forall_mem_asIdeal_iff`: the space half
> holds **iff** any two primes of `A{1/(x + y − 1)}` with the same trace on the away subring give,
> through any two patch charts, points with the same image under the restricted projection, **and**
> `(AlgebraicGeometry.nodeChartAdicHom …).base` is surjective, **and** it is open.

No germ, no `AlgebraicGeometry.nodeChartPsi` and no
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` occurs in the first conjunct. A reader
of the space half no longer has to hold the germ formalism in order to read the clause that is
open; only `AlgebraicGeometry.nodeChartAdicHom` — the morphism out of the chain, which the other
two conjuncts are about anyway — survives on the right-hand side, and it survives only there.

## Why the proof's middle step is not redundant

The proof is three rewrites and the middle one runs **backwards**. That is not an oversight and
removing it does not simplify anything: the first conjunct of
`AlgebraicGeometry.isIso_base_nodeChartQuotientHom_iff` is the *unfolded* germ-pattern condition,
a `∀ x y, (∀ g, IsUnit … ↔ IsUnit …) → …`, and not the term
`Function.Injective (AlgebraicGeometry.nodeChartQuotientHom …).base`. Rewriting backwards by
`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff` folds it back up so that the forward
rewrite by the trace form has a `Function.Injective …` to fire on. Dropping either of the two outer
rewrites makes the remaining one fail to find its pattern; both failures were checked rather than
assumed.

The two other conjuncts are carried through untouched and are not restated:
`AlgebraicGeometry.surjective_base_nodeChartQuotientHom_iff` and
`AlgebraicGeometry.isOpenMap_base_nodeChartQuotientHom_iff` already put them on the chain, and this
file moves exactly one conjunct.

## Main results

* `AlgebraicGeometry.isIso_base_nodeChartQuotientHom_iff_forall_mem_asIdeal_iff`: **the space half
  of hypothesis 4 with the germ formalism eliminated from its orbit-separation clause.**

## What is *not* proved here

**No clause of hypothesis 4 is decided.** Not orbit separation, not surjectivity of
`(AlgebraicGeometry.nodeChartAdicHom …).base`, not its openness, and not the sheaf half. The one
statement below is a restatement, both of whose sides are undecided, and no `w`, no `w'`, no pair
of indices and no point of the chain is exhibited at which any conjunct holds or fails.

**There is no instantiation at which the right-hand side has a known truth value**, so no example
witnessing the equivalence is given below and none should be read into it. Nothing on the tree
decides any of the three conjuncts.

**Same trace does not imply same orbit anywhere on the tree.** Only the converse is proved
(`AlgebraicGeometry.forall_mem_asIdeal_iff_of_base_restrictπ_eq`,
`FormalSchemes.TateInvNodeChartPatchChartTrace`), and the residual of the whole cluster is
unchanged by this file: *two primes with the same trace produce points in the same orbit*. That is
where a property of the `σ`-action has to be supplied for the first time, and nothing below
supplies one — the only fact about the action used here is the invariance that makes
`AlgebraicGeometry.nodeChartQuotientHom` exist at all. **Nothing below may be described as progress
on it.** One is supplied downstream, in
`FormalSchemes.TateInvNodeChartOrbitSeparation`: the shift moves the chart index and fixes the
prime, which gives a sufficient criterion for the clause but does not decide it. That file then
refutes the criterion's own hypothesis for `I ≠ ⊤`, so the criterion is vacuous throughout the
regime it is stated in and the clause is left exactly where this file leaves it.

**`hnode` is undecided in both directions and nothing here moves it.** The chain back to it runs
through `AlgebraicGeometry.exists_formalScheme_of_iso_restrict_tateInvNodeChartQuotientOpens`,
which is **one-way**: even all four hypotheses would give the existence of the formal scheme and
not the converse. And **refuting hypothesis 4 would not refute `hnode`**, because the hypothesis of
`AlgebraicGeometry.exists_formalScheme_of_isIso_desc` is existential while hypothesis 4 is that
condition at a *named* morphism, so it is a priori strictly stronger.

**The sheaf half and `AlgebraicGeometry.nonvanishingSectionsHom` are untouched**, and the space
half is only half of hypothesis 4: `AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_chain` is not
restated below with the new first conjunct, because the sheaf half's two clauses would be carried
along unchanged and the composite would say nothing this statement does not.

**`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` is still a `Classical.choice`**, and
`AlgebraicGeometry.nodeChartAdicHom` is still built from it, so `Classical.choice` appears in
`#print axioms` of the statement below, which mentions `hX`. That is the ambient one and not a new
one.

## Placement

Over `FormalSchemes.TateInvNodeChartSpaceHalf` and
`FormalSchemes.TateInvNodeChartPatchChartTrace`: forward closure **267** project modules besides
itself, reverse closure **1** — `FormalSchemes.TateInvNodeChartOrbitSeparation`, which supplies the
property of the `σ`-action the residual below asks for — counted by walking every
`^import FormalSchemes.` line over the modules under `FormalSchemes/` (a module is not counted in
its own closure; the aggregator at the repository root is outside the walk).

**Neither input reaches the other**, checked in both directions, so the second import is genuinely
new wherever this statement is put.

The two are incomparable rather than nested, and the difference between them is not symmetric.
`FormalSchemes.TateInvNodeChartSpaceHalf`'s forward closure is **263** and holds exactly one module
the other does not, `FormalSchemes.TopCatIsoOpenMap`;
`FormalSchemes.TateInvNodeChartPatchChartTrace`'s forward closure is **264** and holds two the
first does not, `FormalSchemes.ChartGermCriterion` and
`FormalSchemes.TateInvNodeChartPatchChartGerm`. So the choice is not about the cost of an import;
it is about which file the statement belongs to.

Appending to `FormalSchemes.TateInvNodeChartPatchChartTrace` was the alternative and is cheaper by
a module. It is not taken for the reason that file states about itself: its *What is not proved
here* says **"What is produced is a restatement of one clause"**, and that sentence is doing work —
it is what stops a reader taking the trace translation for a statement about the space half.
Appending the space half there would falsify it, and the repair would be a rewrite of a paragraph
rather than an addition. That is the same argument
`FormalSchemes.TateInvNodeChartPatchChartTrace` itself made for not appending to
`FormalSchemes.TateInvNodeChartPatchChartGerm`, and it applies again one module down.

**The germ module's forward pointer does not need a second hop.**
`FormalSchemes.TateInvNodeChartPatchChartGerm` says that nothing in it compares two charts and that
the comparison of two charts is `FormalSchemes.TateInvNodeChartPatchChartTrace`, one module
downstream. That stays exactly right: the comparison of two charts is still made there and not
here, and this file only substitutes the resulting `↔` into an assembly that was already on the
tree. A pointer from the germ module to this one would name a file that compares nothing.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4 (10.4.6), §10.6.
* [Deligne–Rapoport], II.1 — the Néron 1-gon.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open AlgebraicGeometry.LocallyRingedSpace Opposite

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)
variable [TopologicalSpace ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
  (op (tateInvNodeChartQuotientOpens R I q hq hI)))]
variable [IsAdicRing (tateInvNodeChartQuotientIdeal R I q hq hI)]
variable (hfgI : (tateInvNodeChartQuotientIdeal R I q hq hI).FG)
variable (hX : FormalScheme.AdicSectionsLocallyFG (tateInvNodeChartQuotientIdeal R I q hq hI)
  (nodeChartPsi R I q hq hI))

/-- **The space half of hypothesis 4, with no germ in it.** The base map of
`AlgebraicGeometry.nodeChartQuotientHom` is an isomorphism exactly when

* for every pair of indices and every pair of primes of `A{1/(x + y − 1)}` whose traces on
  `AlgebraicGeometry.tateInvNodeChartAwaySubring` agree, the two points the patch charts produce
  have the same image under the restricted projection, **and**
* `(AlgebraicGeometry.nodeChartAdicHom …).base` is surjective, **and**
* that same map is open.

`AlgebraicGeometry.isIso_base_nodeChartQuotientHom_iff` with its first conjunct replaced by
`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff_forall_mem_asIdeal_iff`. The middle
rewrite runs backwards by `AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff` and is
**load-bearing**: the first conjunct is the unfolded germ-pattern condition rather than the term
`Function.Injective …`, so it has to be folded back up before the trace form has anything to fire
on. Dropping either outer rewrite makes the other fail.

**This is a restatement and decides nothing**; both sides are undecided and no instantiation is
known at which either holds. What it buys is that the space half can now be read without the germ
formalism, and that the only conjunct anyone has to think about is orbit separation against an
equality of traces — one direction of which is free
(`AlgebraicGeometry.forall_mem_asIdeal_iff_of_base_restrictπ_eq`) while the other is where a
property of the `σ`-action has to enter. -/
theorem isIso_base_nodeChartQuotientHom_iff_forall_mem_asIdeal_iff :
    IsIso (nodeChartQuotientHom R I q hq hI hfgI hX).base ↔
      (∀ (i j : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
        (w w' : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q))),
        (∀ a : tateInvNodeChartAwaySubring R I q hq hI,
            (Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
                (annulusNodeChartCoord R I q))
                (a : awayCompletion (annulusIdealOfDefinition R I q)
                  (annulusNodeChartCoord R I q)) ∈ w.asIdeal ↔
              Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
                (annulusNodeChartCoord R I q))
                (a : awayCompletion (annulusIdealOfDefinition R I q)
                  (annulusNodeChartCoord R I q)) ∈ w'.asIdeal)) →
        (LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
              (tateInvNodeChartQuotientOpens R I q hq hI)).base
            ((nodeChartPatchChartLift R I q hq hI i).base w) =
          (LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
              (tateInvNodeChartQuotientOpens R I q hq hI)).base
            ((nodeChartPatchChartLift R I q hq hI j).base w')) ∧
        Function.Surjective (nodeChartAdicHom R I q hq hI hfgI hX).base ∧
        IsOpenMap ⇑(ConcreteCategory.hom (nodeChartAdicHom R I q hq hI hfgI hX).base) := by
  rw [isIso_base_nodeChartQuotientHom_iff R I q hq hI hfgI hX,
    ← injective_base_nodeChartQuotientHom_iff R I q hq hI hfgI hX,
    injective_base_nodeChartQuotientHom_iff_forall_mem_asIdeal_iff R I q hq hI hfgI hX]

end AlgebraicGeometry

end
