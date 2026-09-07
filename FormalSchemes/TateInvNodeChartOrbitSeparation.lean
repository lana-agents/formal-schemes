import FormalSchemes.TateInvNodeChartAmbientNotInjective
import FormalSchemes.TateInvNodeChartSpaceHalfTrace

set_option linter.style.header false

/-!
# The `σ`-action moves the chart index and fixes the prime

Seven rows reduced hypothesis 4 of `AlgebraicGeometry.exists_formalScheme_of_adicSections` to one
sentence, and `FormalSchemes.TateInvNodeChartPatchChartTrace` and
`FormalSchemes.TateInvNodeChartSpaceHalfTrace` both record it:

> two primes with the same trace on `AlgebraicGeometry.tateInvNodeChartAwaySubring` produce points
> in the same orbit — the first point at which a property of the `σ`-action has to be supplied.

**This file supplies one.** It is a single geometric fact and it is not a restatement:

> `AlgebraicGeometry.base_tateInvNodeChartRestrictedAction_nodeChartPatchChartLift`: the `n`-fold
> shift carries the point the patch-`i` chart produces at a prime `w` to the point the
> patch-`(i + n)` chart produces at **the same** `w`.

The action moves the chart index and leaves the prime alone. That is the cover-shift law
`AlgebraicGeometry.ι_tateInvShiftAut_zpow` — `σⁿ` restricts along the inclusion of the patch at
index `i` to the inclusion of the patch at index `i + n` — read at a point, transported to the
saturated locus, and it is the only property of the action any statement below uses.

## What it buys

**A sufficient criterion for the orbit-separation clause, whose hypothesis is commutative
algebra.** `AlgebraicGeometry.injective_base_nodeChartQuotientHom_of_forall_mem_asIdeal_iff`: if
the trace separates the primes of the away completion modulo
`FormalSpectrum.awayCompletionIdeal`, the clause holds. Given `w = w'`, the shift by `j − i` is a
witness for the orbit, so the whole clause follows with no further geometry. That hypothesis names
no formal scheme, no action, no chart and no germ — it is the injectivity of one `Spec` map, for
the ring inclusion `AlgebraicGeometry.tateInvNodeChartAwaySubring` sits in.

**And that hypothesis is false, so the criterion is vacuous for every `I ≠ ⊤`.**
`AlgebraicGeometry.not_forall_mem_asIdeal_iff_imp_eq` is the criterion's hypothesis negated with
nothing else changed, proved throughout the regime the criterion is stated in: the section's
finite generation of `AlgebraicGeometry.tateInvNodeChartQuotientIdeal`, the section's
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` witness, and additionally `I ≠ ⊤`. The two
branch generic points of `FormalSchemes.TateInvNodeChartAmbientNotInjective` are two distinct
primes with equal traces, so the criterion has no instantiation at which its hypothesis holds and
it cannot be the route by which the clause is settled. **It is nonetheless a true theorem and
stays**: its proof is the content of the crux, and it is what makes the shape of what is left
legible. Both it and the refutation are restated at the map the trace condition is a fibre of —
`AlgebraicGeometry.tateInvNodeChartAwaySpfMap` (`FormalSchemes.TateInvNodeChartAmbient`), `Spf` of
the inclusion of the chart ring — where the hypothesis is the injectivity of one map of formal
spectra and the refutation is `¬ Function.Injective` of it.

**And, from that spelling, a fact of commutative algebra with nothing geometric in it.** Contraposed
through `PrimeSpectrum.comap_injective_of_surjective`, the refutation says the chart ring does
**not** surject onto the ambient ring modulo the ideal of definition
(`AlgebraicGeometry.not_surjective_quotientMap_tateInvNodeChartAwaySubring`) and hence that it is a
**proper** subring of `A{1/(x + y − 1)}` (`AlgebraicGeometry.tateInvNodeChartAwaySubring_ne_top`),
for `I ≠ ⊤` and in this section's regime. The second of those decides a question the cluster had
recorded as open in both directions; the first is a statement about two explicit rings, and
`AlgebraicGeometry.injective_quotientMap_tateInvNodeChartAwaySubring`
(`FormalSchemes.TateInvNodeChartAmbient`) is its unconditional companion in the other direction.

**And the exact size of what the criterion leaves — which is what survives.**
`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff_exists_index` states the clause with the
action eliminated: the orbit condition becomes a bare integer index `k`, and — the part worth
noticing — the source index `i` **no longer occurs on the right-hand side** at all. Against that
statement the criterion is visibly one-way: it discharges the `∃ k` by taking `k` to be the target
index, and the gap is exactly the pairs `w ≠ w'` for which some *other* `k` works, i.e. for which
two different patch charts hit one point of the saturated locus carrying different primes. Adjacent
patches of the chain do overlap — `AlgebraicGeometry.tateChainInv_ι_range_disjoint` gives
disjointness only at index distance two or more — so that set is not obviously empty and nothing
below says it is.

## The three steps to the crux

Each is one line of content, and they are separated because the first two are about the *inclusion*
of the saturated locus and only the third is about the action.

1. `AlgebraicGeometry.base_restrictOpenι_tateInvNodeChartRestrictedAction` — the inclusion
   intertwines the restricted action with `σⁿ`. Term mode, no tactic:
   `AlgebraicGeometry.FormalScheme.restrictOpenι` is
   `AlgebraicGeometry.LocallyRingedSpace.ofRestrict` by definition and
   `AlgebraicGeometry.nodeChartSaturationOpens` is the preimage of
   `AlgebraicGeometry.tateInvNodeChartQuotientOpens` by definition, so
   `AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom_base_apply` applies on the nose.
2. `AlgebraicGeometry.base_restrictOpenι_nodeChartPatchChartLift` — the lift's value read on the
   chain. This is the `congrFun (congrArg …)` idiom already written twice inside
   `FormalSchemes.TateInvNodeChartPatchChartTrace`, extracted rather than written a third time.
3. `AlgebraicGeometry.base_tateInvPeriodAction_basicOpenChart_ι` — the cover-shift law at a point.

The crux is the three of them under injectivity of the inclusion.

## Two mechanical facts a successor should not rediscover

**The last step of step 3 has to be `congrArg` and not `rw`.**
`AlgebraicGeometry.ι_tateInvShiftAut_zpow` is stated with target
`(AlgebraicGeometry.tateChainInvFormalGlueData …).gluedFormalScheme`, definitionally but not
syntactically the goal's `AlgebraicGeometry.tateChainInv`, and `rw` reports the pattern as not
found with an application type mismatch underneath — an error that reads like the statement being
wrong.

**The `set_option backward.isDefEq.respectTransparency false` on the crux was tested and is
needed.** Without it the two `inferInstance` calls fail to see that a composite of the basic-open
chart with a patch inclusion is an open immersion at a bound index. It is the same option, for the
same reason, that `FormalSchemes.TateInvNodeChartPatchChartAdic` and
`AlgebraicGeometry.isUnit_germ_nodeChartPsi_nodeChartPatchChartLift_iff` carry.

## Main results

* `AlgebraicGeometry.base_restrictOpenι_tateInvNodeChartRestrictedAction`,
  `AlgebraicGeometry.base_restrictOpenι_nodeChartPatchChartLift`,
  `AlgebraicGeometry.base_tateInvPeriodAction_basicOpenChart_ι`: the three steps.
* `AlgebraicGeometry.base_tateInvNodeChartRestrictedAction_nodeChartPatchChartLift`: **the shift
  moves the chart index and fixes the prime.**
* `AlgebraicGeometry.injective_base_nodeChartQuotientHom_of_forall_mem_asIdeal_iff`: **if the trace
  separates primes, the orbit-separation clause holds.**
* `AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff_exists_index`: **the clause with the
  action eliminated** — an integer index, and no dependence on the source chart.
* `AlgebraicGeometry.not_forall_mem_asIdeal_iff_imp_eq`: **the criterion's hypothesis is false**
  for `I ≠ ⊤`, so the criterion is vacuous; and
  `AlgebraicGeometry.exists_ne_and_forall_mem_asIdeal_iff`, its positive form — two distinct
  primes with the same trace.
* `AlgebraicGeometry.injective_base_nodeChartQuotientHom_of_injective_tateInvNodeChartAwaySpfMap`
  and `AlgebraicGeometry.not_injective_tateInvNodeChartAwaySpfMap`: **the same criterion and the
  same refutation at `Spf` of the inclusion**, which is what both are about.
* `AlgebraicGeometry.not_surjective_quotientMap_tateInvNodeChartAwaySubring` and
  `AlgebraicGeometry.tateInvNodeChartAwaySubring_ne_top`: **the chart ring does not surject onto
  the ambient ring modulo the ideal of definition, and is a proper subring of it**, for `I ≠ ⊤`.

## What is *not* proved here

**The orbit-separation clause is not decided, in either direction.** The criterion is one-way, the
statement after it says how far one-way, and the refutation of its hypothesis bears on the
criterion and not on the clause. Nothing here computes the trace of any prime or shows that the
traces separate the primes.

**Two primes with equal traces are exhibited, and they do not refute the clause.**
`AlgebraicGeometry.not_forall_mem_asIdeal_iff_imp_eq` and its positive form
`AlgebraicGeometry.exists_ne_and_forall_mem_asIdeal_iff` produce, for `I ≠ ⊤`, two distinct primes
with the same trace — so the criterion's hypothesis fails and the criterion is vacuous throughout
the regime it is stated in. The pair produced lies in **one** orbit, which is what the clause asks
of it, so this is an instance of the clause rather than a counterexample to it;
`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff_exists_index` is what makes the
difference precise, the clause asking for *some* index `k` where the criterion supplies the target
index. Nothing here decides the clause at the pair it exhibits or anywhere else.

**The other two conjuncts of the space half are untouched** — surjectivity and openness of
`(AlgebraicGeometry.nodeChartAdicHom …).base` — and so is **the whole sheaf half**, including
`AlgebraicGeometry.nonvanishingSectionsHom`.

**Only one property of the `σ`-action is used, and it is the cover-shift law.** Freeness, proper
discontinuity and the structure of the orbits of the node locus are all untouched;
`AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction` stands and nothing here
bears on it.

**`hnode` is undecided in both directions and nothing here moves it.** The chain back to it runs
through `AlgebraicGeometry.exists_formalScheme_of_iso_restrict_tateInvNodeChartQuotientOpens`,
which is **one-way**: even all four hypotheses would give the existence of the formal scheme and
not the converse. And **refuting hypothesis 4 would not refute `hnode`**, because the hypothesis of
`AlgebraicGeometry.exists_formalScheme_of_isIso_desc` is existential while hypothesis 4 is that
condition at a *named* morphism, so it is a priori strictly stronger.

**`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` is still a `Classical.choice`**, and
`AlgebraicGeometry.nodeChartAdicHom` is still built from it, so `Classical.choice` appears in
`#print axioms` of every statement below that mentions `hX`. That is the ambient one and not a new
one.

**Nothing here bears on `AlgebraicGeometry.tateInvNodeChartAmbientHom`**, whose refutation as an
open immersion (`AlgebraicGeometry.not_isOpenImmersion_tateInvNodeChartAmbientHom_of_ne_top`) is
untouched.

**Properness of `AlgebraicGeometry.tateInvNodeChartAwaySubring` *is* decided here, and only in
this section's regime.** It is a proper subring for `I ≠ ⊤`, under the same finite generation of
`AlgebraicGeometry.tateInvNodeChartQuotientIdeal` and the same
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` witness as everything else in this section
— a question `FormalSchemes.TateInvNodeChartPatchChartAdic` had
recorded as open in both directions, and the sentence there is repaired to match. What travels
with it does **not** follow:
`AlgebraicGeometry.tateInvNodeChartAwayIdeal` is still not shown to be an ideal of definition —
`FormalSchemes.TateInvNodeChartAmbient` proves it Hausdorff and nothing more — and the subring is
not shown closed, complete or finitely generated over anything.

**No element outside the chart ring is exhibited, here or anywhere on the tree.** Both negative
statements above are contrapositions and produce no witness; an explicit element of
`A{1/(x + y − 1)}` congruent modulo `FormalSpectrum.awayCompletionIdeal` to nothing in the chart
ring would be a strictly stronger fact and is not proved.

**None of the four statements at the map is unconditional.**
`AlgebraicGeometry.tateInvNodeChartAwaySpfMap` is defined with neither of this section's two
hypotheses and without `I ≠ ⊤` — that is what makes it the right noun — while the non-injectivity,
the non-surjectivity and the properness all carry all three, and the criterion carries the two.
At `I = ⊤` nothing here says anything in either direction, and the map's injectivity outside this
section's regime is untouched.

## Placement

Over `FormalSchemes.TateInvNodeChartSpaceHalfTrace` and
`FormalSchemes.TateInvNodeChartAmbientNotInjective`: forward closure **269** project modules
besides itself, reverse closure **0**, counted by walking every `^import FormalSchemes.` line over
the 559 modules under `FormalSchemes/` (a module is not counted in its own closure; the aggregator
at the repository root is outside the walk).

**The first import suffices for the crux and that was measured rather than assumed.** Its three
inputs are `FormalSchemes.TateInvNodeChartSpaceHalfTrace` (for the `↔` the two consequences
rewrite by), `FormalSchemes.TateActionInv` (for the cover-shift law) and
`FormalSchemes.ActionQuotientCarrier` (for the points of an action quotient). The forward closure
of `FormalSchemes.TateInvNodeChartSpaceHalfTrace` is **267**, and the walk puts the other two
inside it, so the crux pays for one import and gets all three.

**The second import is what the refutation costs, and it costs exactly one module.**
`FormalSchemes.TateInvNodeChartAmbientNotInjective` has forward closure **203**, and the walk puts
every one of those inside the 268 this file had before the import, so the whole price is that
module itself and the figure above is that 268 plus one.
`FormalSchemes.TateInvNodeChartAmbientNotInjective` now has reverse closure **1** where it had
none. Nothing else on the tree moves in either direction: no module is added, and nothing imports
this file. Re-running `scripts/closure_audit.py --tree` with the import added and no other edit
reports exactly one MISMATCH, the figure above — measured, not inferred, and it settles for the
import case a question the tree's earlier measurement of this cost left open, that one having
covered only the addition of a new module.

**The refutation belongs beside the criterion it refutes rather than in a new module importing
both**, and the comparison was made rather than assumed. A new module costs a 560th entry in the
walk, and re-running the audit with one such module present reports **40** MISMATCHes over 25
sentences in 22 files — 15 of them project-module totals and 25 of them figures counting how many
modules sit above a given one — against the single figure the import moves. A new module would
also leave the criterion's own docstring saying that its hypothesis is not known to fail, with the
refutation in a file the reader has no reason to open; that sentence is the defect this row
repairs, so a placement that leaves a pointer where the falsehood was is not a repair. The
argument that kept the crux out of `FormalSchemes.TateInvNodeChartPatchChartGerm` does not run in
reverse here: what this file says about itself is rewritten above rather than falsified, which is
what an addition is allowed to do to the prose of the file it is added to.

**`Spf` of the inclusion is not here**, and this file pays no import for it.
`AlgebraicGeometry.tateInvNodeChartAwaySpfMap` and the `↔` its fibres satisfy need only the two
rings and the contraction between them, all of which
`FormalSchemes.TateInvNodeChartAmbient` already has, so they are stated there and this file uses
them across an import it already had. Only the four statements above — which need this section's
this section's two hypotheses and the refutation — are here.

**The crux does not belong in `FormalSchemes.TateInvNodeChartPatchChartGerm` beside
`AlgebraicGeometry.nodeChartPatchChartLift`**, which is where a reader would first look for it.
That file's *What is not proved here* says **"nothing below compares two charts, or a chart with
its `σ`-translates"**, and the crux is exactly a chart against its `σ`-translates. It is the
sentence that made `FormalSchemes.TateInvNodeChartPatchChartTrace` a separate module rather than an
addition, and the same argument applies here one module further down. The same reasoning rules out
`FormalSchemes.TateInvNodeChartSpaceHalfTrace`, whose *What is not proved here* says *"nothing
below supplies one"* of a property of the action.

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

/-! ### The three steps -/

/-- **The inclusion of the saturated locus intertwines the restricted action with `σⁿ`.**

Term mode with no tactic, because both spellings are definitional:
`AlgebraicGeometry.FormalScheme.restrictOpenι` is
`AlgebraicGeometry.LocallyRingedSpace.ofRestrict` of the open, and
`AlgebraicGeometry.nodeChartSaturationOpens` is the preimage of
`AlgebraicGeometry.tateInvNodeChartQuotientOpens` along the projection. So this is
`AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom_base_apply` at the invariance of that
preimage, and the invariance is formal
(`AlgebraicGeometry.LocallyRingedSpace.isInvariantOpen_preimage`). -/
theorem base_restrictOpenι_tateInvNodeChartRestrictedAction (n : Multiplicative ℤ)
    (z : (nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace) :
    ((tateChainInv R I q hq hI).restrictOpenι (tateChainInv_locallyFG R I q hq hI)
        (nodeChartSaturationOpens R I q hq hI)).base
        ((tateInvNodeChartRestrictedAction R I q hq hI n).hom.base z)
      = ((tateInvPeriodAction R I q hq hI) n).hom.base
          (((tateChainInv R I q hq hI).restrictOpenι (tateChainInv_locallyFG R I q hq hI)
            (nodeChartSaturationOpens R I q hq hI)).base z) :=
  LocallyRingedSpace.restrictOpensHom_base_apply _ _ _
    ((LocallyRingedSpace.isInvariantOpen_preimage
      (isActionQuotient_actionQuotientπ (tateInvPeriodAction R I q hq hI)).isInvariant
      (tateInvNodeChartQuotientOpens R I q hq hI)).image_hom_subset n) z

/-- **The value of the lifted patch chart, read on the chain.**
`AlgebraicGeometry.nodeChartPatchChartLift_comp` applied to a point.

This is the `congrFun (congrArg …)` idiom already written inside
`AlgebraicGeometry.exists_base_nodeChartPatchChartLift_eq` and inside
`AlgebraicGeometry.isUnit_germ_nodeChartPsi_nodeChartPatchChartLift_iff`
(`FormalSchemes.TateInvNodeChartPatchChartTrace`), extracted rather than written a third time. The
two existing uses are left alone: rerouting them would rebuild a module with a forward closure of
264 for no change of content. -/
theorem base_restrictOpenι_nodeChartPatchChartLift
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
    [LocallyRingedSpace.IsOpenImmersion
      (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι i)]
    (w : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q))) :
    ((tateChainInv R I q hq hI).restrictOpenι (tateChainInv_locallyFG R I q hq hI)
        (nodeChartSaturationOpens R I q hq hI)).base
        ((nodeChartPatchChartLift R I q hq hI i).base w)
      = (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
          (tateChainInvFormalGlueData R I q hq hI).ι i).base w :=
  congrFun (congrArg (fun m : FormalSpectrum.locallyRingedSpaceObj
      (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) ⟶ (tateChainInv R I q hq hI).toLocallyRingedSpace =>
    ⇑(ConcreteCategory.hom m.base)) (nodeChartPatchChartLift_comp R I q hq hI i)) w

/-- **The cover-shift law at a point.** `σⁿ` carries the point the patch-`i` basic-open chart
produces at `w` to the point the patch-`(i + n)` chart produces at the same `w`; that the prime is
unchanged is the whole content, and it is `AlgebraicGeometry.ι_tateInvShiftAut_zpow` with the
basic-open chart precomposed.

**The final step must be `congrArg` and not `rw [h]`.**
`AlgebraicGeometry.ι_tateInvShiftAut_zpow` is stated with target
`(AlgebraicGeometry.tateChainInvFormalGlueData …).gluedFormalScheme`, which is definitionally but
not syntactically this goal's `AlgebraicGeometry.tateChainInv`; `rw` reports the pattern as not
found, with an application type mismatch underneath, which reads like the statement being wrong. -/
theorem base_tateInvPeriodAction_basicOpenChart_ι (n : Multiplicative ℤ)
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
    (w : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q))) :
    ((tateInvPeriodAction R I q hq hI) n).hom.base
        ((basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
          (tateChainInvFormalGlueData R I q hq hI).ι i).base w)
      = (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
          (tateChainInvFormalGlueData R I q hq hI).ι
            ⟨i.down + (Multiplicative.toAdd n)⟩).base w := by
  have h := ι_tateInvShiftAut_zpow R I q hq hI (Multiplicative.toAdd n) i
  have h' : (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
      (tateChainInvFormalGlueData R I q hq hI).ι i) ≫
      ((tateInvPeriodAction R I q hq hI) n).hom
      = basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι ⟨i.down + (Multiplicative.toAdd n)⟩ := by
    rw [Category.assoc, tateInvPeriodAction_apply]
    exact congrArg (fun m => basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q) ≫ m) h
  exact congrFun (congrArg (fun m : FormalSpectrum.locallyRingedSpaceObj
      (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) ⟶ (tateChainInv R I q hq hI).toLocallyRingedSpace =>
    ⇑(ConcreteCategory.hom m.base)) h') w

/-! ### The shift moves the chart index and fixes the prime -/

set_option backward.isDefEq.respectTransparency false in
/-- **The `n`-fold shift moves the chart index and fixes the prime.** On the saturated node-chart
locus, `σⁿ` carries the point the patch-`i` chart produces at a prime `w` to the point the
patch-`(i + n)` chart produces at **the same** `w`.

The three steps above under injectivity of the inclusion of the locus: push the equation forward
along `AlgebraicGeometry.FormalScheme.restrictOpenι`, where the restricted action becomes
`σⁿ` and both lifts become basic-open charts of patches, and there it is the cover-shift law.

**This is the first property of the `σ`-action to reach the trace residual**: every restatement
from `FormalSchemes.TateInvNodeChartPatchChartTrace` down uses only the invariance that makes
`AlgebraicGeometry.nodeChartQuotientHom` exist. The cover-shift law itself is not new to the
cluster — `FormalSchemes.TateInvNodeChartGlue` and `FormalSchemes.TateInvNodeChartRing` both use
it, and both sit upstream of this file — so what is new is reading it at a *point*. It is the only
property of the action used below.

The `set_option` was tested rather than copied: without it the two `inferInstance` calls fail to
synthesize `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion` for a composite of the basic-open
chart with a patch inclusion at a bound index. It is the option
`FormalSchemes.TateInvNodeChartPatchChartAdic` and
`AlgebraicGeometry.isUnit_germ_nodeChartPsi_nodeChartPatchChartLift_iff` carry for the same
failure. -/
theorem base_tateInvNodeChartRestrictedAction_nodeChartPatchChartLift (n : Multiplicative ℤ)
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
    (w : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q))) :
    (tateInvNodeChartRestrictedAction R I q hq hI n).hom.base
        ((nodeChartPatchChartLift R I q hq hI i).base w)
      = (nodeChartPatchChartLift R I q hq hI ⟨i.down + (Multiplicative.toAdd n)⟩).base w := by
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) :=
    isOpenImmersion_basicOpenChart _ _ (annulusIdealOfDefinition_fg R I q hI)
  have hinj : Function.Injective ((tateChainInv R I q hq hI).restrictOpenι
      (tateChainInv_locallyFG R I q hq hI) (nodeChartSaturationOpens R I q hq hI)).base :=
    (FormalScheme.isOpenImmersion_restrictOpenι _ (tateChainInv_locallyFG R I q hq hI)
      (nodeChartSaturationOpens R I q hq hI)).base_open.injective
  haveI := (tateChainInvFormalGlueData R I q hq hI).ι_isOpenImmersion i
  haveI := (tateChainInvFormalGlueData R I q hq hI).ι_isOpenImmersion
    (⟨i.down + (Multiplicative.toAdd n)⟩ :
      (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
  haveI : LocallyRingedSpace.IsOpenImmersion
      (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι i) := inferInstance
  haveI : LocallyRingedSpace.IsOpenImmersion
      (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι
          (⟨i.down + (Multiplicative.toAdd n)⟩ :
            (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)) :=
    inferInstance
  apply hinj
  rw [base_restrictOpenι_tateInvNodeChartRestrictedAction R I q hq hI n,
    base_restrictOpenι_nodeChartPatchChartLift R I q hq hI i w,
    base_tateInvPeriodAction_basicOpenChart_ι R I q hq hI n i w,
    base_restrictOpenι_nodeChartPatchChartLift R I q hq hI
      ⟨i.down + (Multiplicative.toAdd n)⟩ w]

/-! ### The orbit-separation clause -/

section Clause

variable [TopologicalSpace ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
  (op (tateInvNodeChartQuotientOpens R I q hq hI)))]
variable [IsAdicRing (tateInvNodeChartQuotientIdeal R I q hq hI)]
variable (hfgI : (tateInvNodeChartQuotientIdeal R I q hq hI).FG)
variable (hX : FormalScheme.AdicSectionsLocallyFG (tateInvNodeChartQuotientIdeal R I q hq hI)
  (nodeChartPsi R I q hq hI))

/-- **If the trace separates primes, the orbit-separation clause holds.**

The hypothesis is that two primes of the away completion modulo
`FormalSpectrum.awayCompletionIdeal` agreeing on `AlgebraicGeometry.tateInvNodeChartAwaySubring`
are equal — the injectivity of one `Spec` map, a statement with no formal scheme, no action, no
chart and no germ in it. Given it, the clause is immediate: the two primes coincide, and the shift
by the difference of the two indices carries the point one chart produces to the point the other
produces, so the two lie in one orbit
(`AlgebraicGeometry.LocallyRingedSpace.base_eq_iff_of_isActionQuotient` at
`AlgebraicGeometry.isActionQuotient_restrictπ_tateInvNodeChartQuotientOpens`).

**This is a sufficient condition and not a characterisation**, and its hypothesis is **false** for
`I ≠ ⊤` — `AlgebraicGeometry.not_forall_mem_asIdeal_iff_imp_eq` is that hypothesis negated, with
nothing else changed — so this criterion is vacuous throughout the regime it is stated in. That
leaves the clause open rather than refuting it;
`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff_exists_index` is what says how much room
is left. The statement is kept because it is true, because its proof is the crux above, and
because the refutation is only legible against it. -/
theorem injective_base_nodeChartQuotientHom_of_forall_mem_asIdeal_iff
    (htr : ∀ w w' : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)),
      (∀ a : tateInvNodeChartAwaySubring R I q hq hI,
        (Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q))
            (a : awayCompletion (annulusIdealOfDefinition R I q)
              (annulusNodeChartCoord R I q)) ∈ w.asIdeal ↔
          Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q))
            (a : awayCompletion (annulusIdealOfDefinition R I q)
              (annulusNodeChartCoord R I q)) ∈ w'.asIdeal)) → w = w') :
    Function.Injective (nodeChartQuotientHom R I q hq hI hfgI hX).base := by
  rw [injective_base_nodeChartQuotientHom_iff_forall_mem_asIdeal_iff R I q hq hI hfgI hX]
  intro i j w w' h
  obtain rfl := htr w w' h
  refine (LocallyRingedSpace.base_eq_iff_of_isActionQuotient
    (isActionQuotient_restrictπ_tateInvNodeChartQuotientOpens R I q hq hI) _ _).mpr
    ⟨Multiplicative.ofAdd (j.down - i.down), ?_⟩
  have hidx : (⟨i.down + (Multiplicative.toAdd (Multiplicative.ofAdd (j.down - i.down)))⟩ :
      (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) = j :=
    ULift.ext _ _ (by simp)
  rw [base_tateInvNodeChartRestrictedAction_nodeChartPatchChartLift R I q hq hI
    (Multiplicative.ofAdd (j.down - i.down)) i w, hidx]

/-- **The orbit-separation clause with the action eliminated.** The orbit condition of
`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff_forall_mem_asIdeal_iff` becomes the
existence of an integer index `k` with the patch-`k` chart carrying `w` to the point the patch-`j`
chart carries `w'` to: no quotient, no projection and no action occurs on the right-hand side.

**The source index has disappeared from the statement**, which is the substance rather than a
cosmetic. The clause quantifies over a *pair* of charts; after the shift law it is insensitive to
which chart the first point came from, because any chart can be shifted to any other, so only the
second index survives and what replaces the first is a bare integer. The `∀ i` of the clause is
discharged by instantiating it at the target index, which the shift law makes harmless.

Read against this, the criterion above is visibly one-way: it produces `k` equal to the target
index from `w = w'`, and the room it leaves is exactly the pairs `w ≠ w'` for which some other `k`
works — two patch charts hitting one point of the saturated locus carrying different primes. That
set is not shown empty here and is not obviously empty:
`AlgebraicGeometry.tateChainInv_ι_range_disjoint` gives disjointness of two patches only at index
distance two or more, so adjacent patches overlap. -/
theorem injective_base_nodeChartQuotientHom_iff_exists_index :
    Function.Injective (nodeChartQuotientHom R I q hq hI hfgI hX).base ↔
      ∀ (j : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
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
        ∃ k : ℤ, (nodeChartPatchChartLift R I q hq hI ⟨k⟩).base w
          = (nodeChartPatchChartLift R I q hq hI j).base w' := by
  rw [injective_base_nodeChartQuotientHom_iff_forall_mem_asIdeal_iff R I q hq hI hfgI hX]
  constructor
  · intro h j w w' ht
    obtain ⟨n, hn⟩ := (LocallyRingedSpace.base_eq_iff_of_isActionQuotient
      (isActionQuotient_restrictπ_tateInvNodeChartQuotientOpens R I q hq hI) _ _).mp
      (h j j w w' ht)
    refine ⟨j.down + (Multiplicative.toAdd n), ?_⟩
    rw [← base_tateInvNodeChartRestrictedAction_nodeChartPatchChartLift R I q hq hI n j w]
    exact hn
  · intro h i j w w' ht
    obtain ⟨k, hk⟩ := h j w w' ht
    refine (LocallyRingedSpace.base_eq_iff_of_isActionQuotient
      (isActionQuotient_restrictπ_tateInvNodeChartQuotientOpens R I q hq hI) _ _).mpr
      ⟨Multiplicative.ofAdd (k - i.down), ?_⟩
    have hidx : (⟨i.down + (Multiplicative.toAdd (Multiplicative.ofAdd (k - i.down)))⟩ :
        (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J) = ⟨k⟩ :=
      ULift.ext _ _ (by simp)
    rw [base_tateInvNodeChartRestrictedAction_nodeChartPatchChartLift R I q hq hI
      (Multiplicative.ofAdd (k - i.down)) i w, hidx]
    exact hk

/-! ### The hypothesis of the criterion is false -/

include hfgI hX in
set_option backward.isDefEq.respectTransparency false in
/-- **The trace does not separate the primes.** The hypothesis of
`AlgebraicGeometry.injective_base_nodeChartQuotientHom_of_forall_mem_asIdeal_iff`, negated and
with nothing else changed, for every `I ≠ ⊤`. So the criterion above, true as it is, has no
instantiation inside the section it is stated in at which its hypothesis holds, and it cannot be
the route by which the orbit-separation clause is settled.

The two halves were both on the tree and neither is new here.
`AlgebraicGeometry.exists_ne_and_base_actionQuotientπ_ι_eq`
(`FormalSchemes.TateInvNodeChartAmbientNotInjective`) gives two **distinct** points of
`D(x + y − 1)` with **one** image in `T_inv/⟨σ⟩` — the generic points of the two branches of the
special fibre, which the `σ`-shift identifies exactly as the Néron 1-gon glues `0` to `∞`. They
lie in the range of `FormalSpectrum.basicOpenChart`
(`FormalSpectrum.range_basicOpenChart_base`), so they are two distinct primes `w ≠ w'` of the
away completion; and `AlgebraicGeometry.forall_mem_asIdeal_iff_of_base_restrictπ_eq`
(`FormalSchemes.TateInvNodeChartPatchChartTrace`) — *same orbit implies same trace*, the free
direction — says the two have the **same** trace.

**This does not refute the orbit-separation clause and must not be read as doing so.** The pair it
produces lies in **one** orbit, which is what the clause asks of it;
`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff_exists_index` is the statement that
says why the criterion is nevertheless not the clause, and the pair here is precisely a pair for
which the index `k` the clause asks for is not the target index.

Three mechanical points, each of which is a defeq the tactic layer will not close for you.
`AlgebraicGeometry.LocallyRingedSpace.restrictπ_base_apply` has to be used through `refine` and
not `rw`, because after `Subtype.ext` the goal's left-hand side is the coercion only
definitionally. `AlgebraicGeometry.base_restrictOpenι_nodeChartPatchChartLift` is stated at
`AlgebraicGeometry.FormalScheme.restrictOpenι` while the goal carries
`AlgebraicGeometry.LocallyRingedSpace.ofRestrict`, so the two equations are stated in the first
spelling and fed in through `show`. And the last step is `simp only` then `exact` rather than
a single closing step with `using`, because the residual difference is a coercion normal form
that `exact` closes and that closing step does not. The `set_option` is the one the crux above
carries, for the same
`inferInstance` failure, and it was tested here rather than copied. -/
theorem not_forall_mem_asIdeal_iff_imp_eq (hItop : I ≠ ⊤) :
    ¬ (∀ w w' : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)),
      (∀ a : tateInvNodeChartAwaySubring R I q hq hI,
        (Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q))
            (a : awayCompletion (annulusIdealOfDefinition R I q)
              (annulusNodeChartCoord R I q)) ∈ w.asIdeal ↔
          Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q))
            (a : awayCompletion (annulusIdealOfDefinition R I q)
              (annulusNodeChartCoord R I q)) ∈ w'.asIdeal)) → w = w') := by
  intro htr
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) :=
    isOpenImmersion_basicOpenChart _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI := (tateChainInvFormalGlueData R I q hq hI).ι_isOpenImmersion
    (⟨(0 : ℤ)⟩ : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
  haveI : LocallyRingedSpace.IsOpenImmersion
      (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι
          (⟨(0 : ℤ)⟩ : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)) :=
    inferInstance
  obtain ⟨a, b, hab, ha, hb, heq⟩ :=
    exists_ne_and_base_actionQuotientπ_ι_eq R I q hq hI hItop
      (isActionQuotient_actionQuotientπ (tateInvPeriodAction R I q hq hI))
  have hrange : Set.range ⇑(ConcreteCategory.hom
      (basicOpenChart (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)).base) = tateInvNodeChartLocus R I q :=
    range_basicOpenChart_base _ _ (annulusIdealOfDefinition_fg R I q hI)
  obtain ⟨w, hw⟩ : a ∈ Set.range ⇑(ConcreteCategory.hom
      (basicOpenChart (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)).base) := by rw [hrange]; exact ha
  obtain ⟨w', hw'⟩ : b ∈ Set.range ⇑(ConcreteCategory.hom
      (basicOpenChart (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)).base) := by rw [hrange]; exact hb
  have hne : w ≠ w' := by
    rintro rfl; exact hab (hw.symm.trans hw')
  have hstep : (LocallyRingedSpace.restrictπ
        (actionQuotientπ (tateInvPeriodAction R I q hq hI))
        (tateInvNodeChartQuotientOpens R I q hq hI)).base
        ((nodeChartPatchChartLift R I q hq hI ⟨0⟩).base w)
      = (LocallyRingedSpace.restrictπ
        (actionQuotientπ (tateInvPeriodAction R I q hq hI))
        (tateInvNodeChartQuotientOpens R I q hq hI)).base
        ((nodeChartPatchChartLift R I q hq hI ⟨0⟩).base w') := by
    refine Subtype.ext ?_
    refine (LocallyRingedSpace.restrictπ_base_apply _ _ _).trans
      (Eq.trans ?_ (LocallyRingedSpace.restrictπ_base_apply _ _ _).symm)
    have e1 : (ConcreteCategory.hom ((tateChainInv R I q hq hI).restrictOpenι
        (tateChainInv_locallyFG R I q hq hI) (nodeChartSaturationOpens R I q hq hI)).base)
        ((ConcreteCategory.hom (nodeChartPatchChartLift R I q hq hI ⟨0⟩).base) w)
      = (ConcreteCategory.hom (basicOpenChart (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q) ≫
          (tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩).base) w :=
      base_restrictOpenι_nodeChartPatchChartLift R I q hq hI ⟨0⟩ w
    have e2 : (ConcreteCategory.hom ((tateChainInv R I q hq hI).restrictOpenι
        (tateChainInv_locallyFG R I q hq hI) (nodeChartSaturationOpens R I q hq hI)).base)
        ((ConcreteCategory.hom (nodeChartPatchChartLift R I q hq hI ⟨0⟩).base) w')
      = (ConcreteCategory.hom (basicOpenChart (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q) ≫
          (tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩).base) w' :=
      base_restrictOpenι_nodeChartPatchChartLift R I q hq hI ⟨0⟩ w'
    rw [show (ConcreteCategory.hom ((tateChainInv R I q hq hI).toLocallyRingedSpace.ofRestrict
        ((Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).base).obj
          (tateInvNodeChartQuotientOpens R I q hq hI)).isOpenEmbedding).base)
        ((ConcreteCategory.hom (nodeChartPatchChartLift R I q hq hI ⟨0⟩).base) w) = _ from e1,
      show (ConcreteCategory.hom ((tateChainInv R I q hq hI).toLocallyRingedSpace.ofRestrict
        ((Opens.map (actionQuotientπ (tateInvPeriodAction R I q hq hI)).base).obj
          (tateInvNodeChartQuotientOpens R I q hq hI)).isOpenEmbedding).base)
        ((ConcreteCategory.hom (nodeChartPatchChartLift R I q hq hI ⟨0⟩).base) w') = _ from e2]
    simp only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply,
      hw, hw']
    exact heq
  exact hne (htr w w' (forall_mem_asIdeal_iff_of_base_restrictπ_eq R I q hq hI hfgI hX
    ⟨0⟩ ⟨0⟩ w w' hstep))

include hfgI hX in
/-- **Two distinct primes with the same trace exist**, for every `I ≠ ⊤`: the positive form of
`AlgebraicGeometry.not_forall_mem_asIdeal_iff_imp_eq`, which is the form a reader wants, since the
negation of a `∀ ∀ →` does not display what it produces.

This is the first pair of primes with equal traces exhibited anywhere on this tree. It is **not** a
counterexample to anything: the two lie in one orbit, so they satisfy the orbit-separation clause,
and what they refute is only the identification of that clause's `∃ k` with the target index. -/
theorem exists_ne_and_forall_mem_asIdeal_iff (hItop : I ≠ ⊤) :
    ∃ w w' : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)),
      (∀ a : tateInvNodeChartAwaySubring R I q hq hI,
        (Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q))
            (a : awayCompletion (annulusIdealOfDefinition R I q)
              (annulusNodeChartCoord R I q)) ∈ w.asIdeal ↔
          Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q))
            (a : awayCompletion (annulusIdealOfDefinition R I q)
              (annulusNodeChartCoord R I q)) ∈ w'.asIdeal)) ∧ w ≠ w' := by
  by_contra h
  refine not_forall_mem_asIdeal_iff_imp_eq R I q hq hI hfgI hX hItop fun w w' ht => ?_
  by_contra hne
  exact h ⟨w, w', ht, hne⟩

/-! ### The criterion and its refutation, at `Spf` of the inclusion -/

include hfgI hX in
/-- **The criterion with the primes eliminated: it is the injectivity of `Spf` of the inclusion.**
`AlgebraicGeometry.injective_base_nodeChartQuotientHom_of_forall_mem_asIdeal_iff` read through
`AlgebraicGeometry.tateInvNodeChartAwaySpfMap_eq_iff`
(`FormalSchemes.TateInvNodeChartAmbient`), which says the trace condition **is** a fibre of
`AlgebraicGeometry.tateInvNodeChartAwaySpfMap`. Nothing is lost in either direction: that
statement is an `↔`.

This is the shape the criterion was always in and the shape it should be read in — a map of formal
spectra induced by a ring inclusion, with no prime, no trace, no chart and no action in the
hypothesis. **It is nonetheless vacuous**, by the next theorem, throughout the regime this section
fixes and for `I ≠ ⊤`. -/
theorem injective_base_nodeChartQuotientHom_of_injective_tateInvNodeChartAwaySpfMap
    (h : Function.Injective (tateInvNodeChartAwaySpfMap R I q hq hI)) :
    Function.Injective (nodeChartQuotientHom R I q hq hI hfgI hX).base :=
  injective_base_nodeChartQuotientHom_of_forall_mem_asIdeal_iff R I q hq hI hfgI hX
    fun w w' ht => h ((tateInvNodeChartAwaySpfMap_eq_iff R I q hq hI w w').mpr ht)

include hfgI hX in
/-- **`Spf` of the inclusion is not injective**, for `I ≠ ⊤`:
`AlgebraicGeometry.not_forall_mem_asIdeal_iff_imp_eq` in one line instead of a negated `∀ ∀ →`,
through the same `↔`. The two say the same thing and carry the same three hypotheses; the content
is entirely the earlier one's, and this is the spelling a reader can hold.

**The hypotheses are not decoration.** `AlgebraicGeometry.tateInvNodeChartAwaySpfMap` is defined
with none of them, and this is not a statement that it fails to be injective in general: the two
branch points exist only for `I ≠ ⊤`, and the trace half of the earlier theorem is only available
under this section's finite generation of `AlgebraicGeometry.tateInvNodeChartQuotientIdeal` and
its `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` witness. At `I = ⊤` nothing here
applies. -/
theorem not_injective_tateInvNodeChartAwaySpfMap (hItop : I ≠ ⊤) :
    ¬ Function.Injective (tateInvNodeChartAwaySpfMap R I q hq hI) := fun h =>
  not_forall_mem_asIdeal_iff_imp_eq R I q hq hI hfgI hX hItop
    fun w w' ht => h ((tateInvNodeChartAwaySpfMap_eq_iff R I q hq hI w w').mpr ht)

include hfgI hX in
/-- **The chart ring does not surject onto the ambient ring modulo the ideal of definition**, for
`I ≠ ⊤`. `PrimeSpectrum.comap_injective_of_surjective` contraposed against the theorem above,
which applies because `FormalSpectrum.map` **is** `PrimeSpectrum.comap` of
`Ideal.quotientMap`.

In words: there is an element of `A{1/(x + y − 1)}` congruent modulo
`FormalSpectrum.awayCompletionIdeal` to nothing in
`AlgebraicGeometry.tateInvNodeChartAwaySubring`. That is a statement about two explicit rings with
no formal scheme, no action, no chart and no prime in it, and it is the first measurement on this
tree of how the chart ring sits inside the ambient one from **above**;
`AlgebraicGeometry.injective_quotientMap_tateInvNodeChartAwaySubring`
(`FormalSchemes.TateInvNodeChartAmbient`) is the companion from below, and needs no hypothesis.

**No such element is exhibited.** This is a negation obtained by contraposition and it produces no
witness; see this file's module docstring. -/
theorem not_surjective_quotientMap_tateInvNodeChartAwaySubring (hItop : I ≠ ⊤) :
    ¬ Function.Surjective (Ideal.quotientMap
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q))
      (tateInvNodeChartAwaySubring R I q hq hI).subtype
      (le_rfl : tateInvNodeChartAwayIdeal R I q hq hI ≤ _)) := fun hsurj =>
  not_injective_tateInvNodeChartAwaySpfMap R I q hq hI hfgI hX hItop
    (PrimeSpectrum.comap_injective_of_surjective _ hsurj)

include hfgI hX in
/-- **The chart ring is a proper subring of `A{1/(x + y − 1)}`**, for `I ≠ ⊤`. If it were the
whole ring its inclusion would be surjective, hence so would the induced map of quotients
(`Ideal.quotientMap_surjective`), which the theorem above refutes.

**This decides a question the cluster records as open**, in this section's regime and nowhere
else: `FormalSchemes.TateInvNodeChartPatchChartAdic` said that nothing on the tree decides whether
`AlgebraicGeometry.tateInvNodeChartAwaySubring` is the whole of the ambient ring or a proper
subring of it, and that sentence is repaired by this theorem rather than by anything about the
action. What is *not* decided is everything else that question travels with: no element outside
the subring is produced, `AlgebraicGeometry.tateInvNodeChartAwayIdeal` is still not shown to be an
ideal of definition, and `I = ⊤` is untouched.

The properness of the **global** subring in `A` is a different statement about different rings and
is proved elsewhere and unconditionally in `I ≠ ⊤`, with a witness
(`AlgebraicGeometry.tateInvGlobalSubring_ne_top`, `FormalSchemes.TateInvGlobalProperness`). -/
theorem tateInvNodeChartAwaySubring_ne_top (hItop : I ≠ ⊤) :
    tateInvNodeChartAwaySubring R I q hq hI ≠ ⊤ := fun htop =>
  not_surjective_quotientMap_tateInvNodeChartAwaySubring R I q hq hI hfgI hX hItop
    (Ideal.quotientMap_surjective fun a => ⟨⟨a, htop ▸ Subring.mem_top a⟩, rfl⟩)

end Clause

end AlgebraicGeometry

end
