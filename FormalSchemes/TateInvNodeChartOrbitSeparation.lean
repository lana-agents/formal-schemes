import FormalSchemes.TateInvNodeChartAmbientNotInjective
import FormalSchemes.TateInvNodeChartLegGeneral
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

**And, by a second and independent argument, the element that is missed.** The two statements
above are contrapositions and produce no witness. The last section of this file produces one, and
it is the coordinate `x`: `AlgebraicGeometry.notMem_range_quotientMap_tateInvNodeChartAwaySubring`
says the residue of the image of `x` in `A{1/(x + y − 1)}` is congruent to nothing in the chart
ring, `AlgebraicGeometry.notMem_tateInvNodeChartAwaySubring_overlapX` says `x` itself is outside
it, and `AlgebraicGeometry.tateInvNodeChartAwaySubring_ne_top'` is the properness that follows.
**Those three carry `I ≠ ⊤` and nothing else** — not this file's clause-section hypotheses, and
not the action, which their proof never mentions. What they use instead is the pair of forward
legs read at `x`: the `x` leg sends `x` to `x`, the transition-then-`y` leg sends it to `q·x`
(`AlgebraicGeometry.tateInvGlobalLegYX_overlapX`, `FormalSchemes.TateInvGlobalProperness`), leg
continuity keeps a congruence modulo the ideal of definition
(`FormalSchemes.TateInvNodeChartLegContinuous`), and `q` dies in the residue while `x` does not —
the last because `AlgebraicGeometry.annulusBranchXPoint` is a point of `Spf A` in `D(x)` and in
`D(x + y − 1)`, which is where `I ≠ ⊤` is spent. It is the same witness the **global** subring
misses (`AlgebraicGeometry.notMem_tateInvGlobalSubring_overlapX`), read one ring down.

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
* `AlgebraicGeometry.tateInvNodeChartAwayLegYX_awayCompletionHom` and
  `AlgebraicGeometry.tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegYX`: the `YX` companions
  of the two leg computations of `FormalSchemes.TateInvNodeChartLegGeneral`, which had only the
  `X` and `Y` legs. These are what let the two forward legs be compared at one element.
* `AlgebraicGeometry.notMem_annulusBranchXPoint_overlapX`,
  `AlgebraicGeometry.notMem_annulusBranchXPoint_annulusNodeChartCoord` and
  `AlgebraicGeometry.exists_mem_asIdeal_iff_mem_annulusBranchXPoint`: **the `x`-branch generic
  point lifts to a prime of `A{1/x}{1/(x + y − 1)}`**, and that prime sees `A` through the two
  structural maps. This is the only use of the branch points in the witness argument.
* `AlgebraicGeometry.notMem_range_quotientMap_tateInvNodeChartAwaySubring`,
  `AlgebraicGeometry.notMem_tateInvNodeChartAwaySubring_overlapX`,
  `AlgebraicGeometry.exists_notMem_tateInvNodeChartAwaySubring` and
  `AlgebraicGeometry.tateInvNodeChartAwaySubring_ne_top'`: **the witness — the coordinate `x` is
  outside the chart ring, and its residue is outside the image of the chart ring** — for `I ≠ ⊤`
  and with none of this file's clause-section hypotheses.

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

**Properness of `AlgebraicGeometry.tateInvNodeChartAwaySubring` *is* decided here, for every
`I ≠ ⊤`.** The clause section proves it in that section's regime, under the finite generation of
`AlgebraicGeometry.tateInvNodeChartQuotientIdeal` and the
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` witness; the witness section proves it
again with neither, as `AlgebraicGeometry.tateInvNodeChartAwaySubring_ne_top'`. Both statements
stay, and the pair differs only in binders — the conditional one is the end of the route through
the refutation and is where the clause section's other statements sit. It is a question
`FormalSchemes.TateInvNodeChartPatchChartAdic` had recorded as open in both directions, and the
sentence there is repaired to match. What travels with it does **not** follow:
`AlgebraicGeometry.tateInvNodeChartAwayIdeal` is still not shown to be an ideal of definition —
`FormalSchemes.TateInvNodeChartAmbient` proves it Hausdorff and nothing more — and the subring is
not shown closed, complete or finitely generated over anything. **At `I = ⊤` nothing here decides
properness in either direction.**

**One element outside the chart ring is exhibited and no more.** It is the image of the coordinate
`x`, and what is shown of it is exactly that its residue modulo
`FormalSpectrum.awayCompletionIdeal` is not in the image of the chart ring. **No description of
the missed residues as a set is given**, nothing says how much of the ambient ring is missed, and
the coordinate `y` is not treated — the argument is written on the `x` side and its mirror is not
proved. The two contrapositions in the clause section still produce no witness of their own; they
are not repaired by the witness section, they are complemented by it.

**None of the four statements at the map is unconditional.**
`AlgebraicGeometry.tateInvNodeChartAwaySpfMap` is defined with neither of this section's two
hypotheses and without `I ≠ ⊤` — that is what makes it the right noun — while the non-injectivity,
the non-surjectivity and the properness all carry all three, and the criterion carries the two.
That is a statement about those four; the witness section's statements are separate and carry only
`I ≠ ⊤`. At `I = ⊤` nothing here says anything in either direction, and the map's injectivity
outside this
section's regime is untouched.

## Placement

Over `FormalSchemes.TateInvNodeChartSpaceHalfTrace`,
`FormalSchemes.TateInvNodeChartAmbientNotInjective` and
`FormalSchemes.TateInvNodeChartLegGeneral`: forward closure **270** project modules besides
itself, reverse closure **0**, counted by walking every `^import FormalSchemes.` line over the 559
modules under `FormalSchemes/` (a module is not counted in its own closure; the aggregator at the
repository root is outside the walk).

**The first import suffices for the crux and that was measured rather than assumed.** Its three
inputs are `FormalSchemes.TateInvNodeChartSpaceHalfTrace` (for the `↔` the two consequences
rewrite by), `FormalSchemes.TateActionInv` (for the cover-shift law) and
`FormalSchemes.ActionQuotientCarrier` (for the points of an action quotient). The forward closure
of `FormalSchemes.TateInvNodeChartSpaceHalfTrace` is **267**, and the walk puts the other two
inside it, so the crux pays for one import and gets all three.

**The second import is what the refutation costs, and it costs exactly one module.**
`FormalSchemes.TateInvNodeChartAmbientNotInjective` has forward closure **203**, and the walk puts
every one of those inside the 268 this file had before that import, so the whole price was that
module itself and the count went from 268 to 269.
`FormalSchemes.TateInvNodeChartAmbientNotInjective` now has reverse closure **1** where it had
none. Nothing else on the tree moved in either direction: no module was added, and nothing imports
this file. Re-running `scripts/closure_audit.py --tree` with that import added and no other edit
reported exactly one MISMATCH, this file's own figure — measured, not inferred, and it settles for
the import case a question the tree's earlier measurement of this cost left open, that one having
covered only the addition of a new module.

**The third import is what the witness costs, and it costs exactly one module too.**
`FormalSchemes.TateInvNodeChartLegGeneral` has forward closure **214**, and the walk puts every one
of those inside the 269 this file had before it, so again the whole price is that module itself:
the figure above is 269 plus one. `FormalSchemes.TateInvNodeChartLegGeneral` now has reverse
closure **1** where it had none, and it quotes no closure figure of its own, so nothing there needs
repairing. The witness section needs it for the two `X`-side leg computations at an arbitrary
element of `A`; the `YX` companions of those two are proved here rather than there because they are
what the witness needs and nothing else on the tree asks for them, and because adding them there
would rebuild that module's consumers for a statement with one consumer. **That is a judgement and
not a measurement**: a successor that wants the four legs uniformly should move all of the `YX` and
`XY` companions into `FormalSchemes.TateInvNodeChartLegGeneral` in one step.

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
two hypotheses and the refutation — are here.

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

**No such element is exhibited by this proof.** It is a negation obtained by contraposition and it
produces no witness. One is exhibited below, by an argument that shares nothing with this one:
`AlgebraicGeometry.notMem_range_quotientMap_tateInvNodeChartAwaySubring`, the image of the
coordinate `x`, for `I ≠ ⊤` and without this section's two hypotheses. -/
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

**This decides a question the cluster records as open**, in this section's regime:
`FormalSchemes.TateInvNodeChartPatchChartAdic` said that nothing on the tree decides whether
`AlgebraicGeometry.tateInvNodeChartAwaySubring` is the whole of the ambient ring or a proper
subring of it, and that sentence is repaired by this theorem rather than by anything about the
action. `AlgebraicGeometry.tateInvNodeChartAwaySubring_ne_top'` below decides it again outside
this section's regime, by an argument that shares nothing with this one; both statements stay.
What is *not* decided is everything else that question travels with: this proof produces no
element outside the subring — `AlgebraicGeometry.notMem_tateInvNodeChartAwaySubring_overlapX`
below does — `AlgebraicGeometry.tateInvNodeChartAwayIdeal` is still not shown to be an ideal of
definition, and `I = ⊤` is untouched.

The properness of the **global** subring in `A` is a different statement about different rings and
is proved elsewhere and unconditionally in `I ≠ ⊤`, with a witness
(`AlgebraicGeometry.tateInvGlobalSubring_ne_top`, `FormalSchemes.TateInvGlobalProperness`). -/
theorem tateInvNodeChartAwaySubring_ne_top (hItop : I ≠ ⊤) :
    tateInvNodeChartAwaySubring R I q hq hI ≠ ⊤ := fun htop =>
  not_surjective_quotientMap_tateInvNodeChartAwaySubring R I q hq hI hfgI hX hItop
    (Ideal.quotientMap_surjective fun a => ⟨⟨a, htop ▸ Subring.mem_top a⟩, rfl⟩)

end Clause

/-! ### The witness: the coordinate `x` is outside the chart ring -/

section Legs

variable [IsAdicRing (annulusIdealOfDefinition R I q)]
variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))]
variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))]

/-- **The transition-then-`y` leg on the structural image, still in the presheaf spelling** — the
`YX` companion of `AlgebraicGeometry.tateInvNodeChartAwayLegX_awayCompletionHom`
(`FormalSchemes.TateInvNodeChartLegGeneral`), proved the same way from
`AlgebraicGeometry.tateInvNodeChartAmbientEquiv_symm_awayCompletionHom` and
`AlgebraicGeometry.tateInvChartLegYX_sectionsOpenHom`.

The `X` companion carries `omit [TopologicalSpace R] [IsAdicRing I]` and this one cannot, and that
is a fact about the two legs rather than about the two proofs: `#check` shows
`AlgebraicGeometry.tateInvChartLegX` with neither binder in its signature and
`AlgebraicGeometry.tateInvChartLegYX` with both, because the latter goes through the geometric
inversion transition `annulusChartTransitionInvSpf` (root namespace,
`FormalSchemes.TateOverlapInversionIso`). **Restoring the `omit` here does not fail at elaboration
— it fails in the kernel**, after four and a half minutes, on the `congrArg` below. -/
theorem tateInvNodeChartAwayLegYX_awayCompletionHom (a : annulusAlgebra R I q) :
    tateInvNodeChartAwayLegYX R I q hq hI
        (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a) =
      sectionsOpenHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        ((Opens.map (annulusOverlapChart R I q).base).obj
          (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)))
        (tateInvGlobalLegYX hI a) :=
  Eq.trans
    (congrArg (tateInvChartLegYX (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q))
      (tateInvNodeChartAmbientEquiv_symm_awayCompletionHom R I q hq hI a))
    (tateInvChartLegYX_sectionsOpenHom (isOpen_tateInvNodeChartLocus R I q) a)

/-- **The transition-then-`y` leg on the structural image, read in `A{1/x}{1/(x + y − 1)}`** — the
`YX` companion of `AlgebraicGeometry.tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX`
(`FormalSchemes.TateInvNodeChartLegGeneral`). The inner map is
`AlgebraicGeometry.tateInvGlobalLegYX` and **not** a `FormalSpectrum.awayCompletionHom`: the
transition is there, and that is the whole difference between the two legs. -/
theorem tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegYX (a : annulusAlgebra R I q) :
    tateInvNodeChartTargetEquivX R I q hq hI
        (tateInvNodeChartAwayLegYX R I q hq hI
          (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a)) =
      awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q))
        (tateInvGlobalLegYX hI a) :=
  Eq.trans
    (congrArg (tateInvNodeChartTargetEquivX R I q hq hI)
      (tateInvNodeChartAwayLegYX_awayCompletionHom R I q hq hI a))
    (tateInvNodeChartTargetEquivX_sectionsOpenHom R I q hq hI (tateInvGlobalLegYX hI a))

end Legs

section Witness

variable (𝔭 : Ideal R) [𝔭.IsPrime] (h𝔭 : I ≤ 𝔭)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
include h𝔭 hq in
/-- **The coordinate `x` does not vanish at the `x`-branch generic point.** The evaluation sends it
to `Polynomial.X`, and `(R ⧸ 𝔭)[X]` is a domain. This is the half of
`AlgebraicGeometry.annulusBranchXPoint_ne_annulusBranchYPoint` that carries the witness, stated on
its own because everything below is that witness travelling. -/
theorem notMem_annulusBranchXPoint_overlapX :
    Ideal.Quotient.mk (annulusIdealOfDefinition R I q) (overlapX R I q) ∉
      (annulusBranchXPoint R I q 𝔭 h𝔭 hq).asIdeal := by
  rw [show Ideal.Quotient.mk (annulusIdealOfDefinition R I q) (overlapX R I q)
      = fibreX R I q from rfl, mem_annulusBranchXPoint_iff, annulusBranchX_fibreX]
  exact Polynomial.X_ne_zero

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
include h𝔭 hq in
/-- **The chart coordinate `x + y − 1` does not vanish at the `x`-branch generic point either** —
`AlgebraicGeometry.annulusBranchXPoint_mem_tateInvNodeChartLocus` with the locus replaced by the
residue it is defined from, which is the spelling that
`FormalSpectrum.mem_asIdeal_basicOpenChartBase_iff` consumes. -/
theorem notMem_annulusBranchXPoint_annulusNodeChartCoord :
    Ideal.Quotient.mk (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ∉
      (annulusBranchXPoint R I q 𝔭 h𝔭 hq).asIdeal := by
  rw [show Ideal.Quotient.mk (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)
      = fibreX R I q + fibreY R I q - 1 by simp [annulusNodeChartCoord, fibreX, fibreY],
    mem_annulusBranchXPoint_iff]
  simp only [map_sub, map_add, map_one, annulusBranchX_fibreX, annulusBranchX_fibreY, add_zero]
  simpa using Polynomial.X_sub_C_ne_zero (1 : R ⧸ 𝔭)

set_option maxHeartbeats 1000000 in
-- `FormalSpectrum` is a `def` for `PrimeSpectrum (R ⧸ I)` and not an `abbrev`, so placing
-- `annulusBranchXPoint`, whose type is written `PrimeSpectrum (annulusFibre R I q)`, in the range
-- of `FormalSpectrum.basicOpenChartBase` unfolds `annulusAlgebra` inside the elaborator
omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
include h𝔭 hq hI in
/-- **The `x`-branch generic point lifts to `Spf A{1/x}{1/(x + y − 1)}`, and the lift sees `A`
through the two structural maps.** The point lies in `D(x)` by
`notMem_annulusBranchXPoint_overlapX` and its lift lies in `D(x + y − 1)` by
`notMem_annulusBranchXPoint_annulusNodeChartCoord`, so `FormalSpectrum.range_basicOpenChartBase`
produces a preimage twice; the displayed equivalence is
`FormalSpectrum.mem_asIdeal_basicOpenChartBase_iff` applied along the same two steps.

This is the only place below where the branch point is used, and what it delivers is a **prime of
the twice-completed localization at which the coordinate `x` is invertible** — the reason the two
legs can be told apart there.

The `set_option` is for a defeq the elaborator has to close and not for the mathematics:
`FormalSpectrum` is a `def` for `PrimeSpectrum (R ⧸ I)` and not an `abbrev`, so stating that
`AlgebraicGeometry.annulusBranchXPoint`, whose type is written `PrimeSpectrum (annulusFibre R I q)`,
lies in the range of `FormalSpectrum.basicOpenChartBase` costs an unfolding of `annulusAlgebra`. -/
theorem exists_mem_asIdeal_iff_mem_annulusBranchXPoint :
    ∃ v : FormalSpectrum (awayCompletionIdeal
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q))),
      ∀ b : annulusAlgebra R I q,
        Ideal.Quotient.mk _
            (awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q)
                (overlapX R I q))
              (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
                (annulusNodeChartCoord R I q))
              (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q) b)) ∈
            v.asIdeal ↔
          Ideal.Quotient.mk (annulusIdealOfDefinition R I q) b ∈
            (annulusBranchXPoint R I q 𝔭 h𝔭 hq).asIdeal := by
  have hIAfg := annulusIdealOfDefinition_fg R I q hI
  obtain ⟨u, hu⟩ : annulusBranchXPoint R I q 𝔭 h𝔭 hq ∈
      Set.range (basicOpenChartBase (annulusIdealOfDefinition R I q) (overlapX R I q)) := by
    rw [range_basicOpenChartBase _ _ hIAfg]
    exact notMem_annulusBranchXPoint_overlapX R I q hq 𝔭 h𝔭
  obtain ⟨v, hv⟩ : u ∈ Set.range (basicOpenChartBase
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
        (annulusNodeChartCoord R I q))) := by
    rw [range_basicOpenChartBase _ _ (awayCompletionIdeal_fg _ _ hIAfg)]
    change _ ∉ _
    rw [← mem_asIdeal_basicOpenChartBase_iff, hu]
    exact notMem_annulusBranchXPoint_annulusNodeChartCoord R I q hq 𝔭 h𝔭
  refine ⟨v, fun b => ?_⟩
  rw [← mem_asIdeal_basicOpenChartBase_iff, hv, ← mem_asIdeal_basicOpenChartBase_iff, hu]

set_option maxHeartbeats 4000000 in
-- the same `def`-not-`abbrev` unfolding as above, over a proof that also rewrites twice inside the
-- twice-completed localization and applies leg continuity at these concrete rings
include hq hI h𝔭 in
/-- **The residue of the coordinate `x` is not in the image of the chart ring**, at any prime
`𝔭 ⊇ I` of the base. This is the whole content of this section; everything after it is packaging.

The argument is the two forward legs read at `x`, and it uses the action nowhere. If the residue
of `x` were the residue of some `a` in the chart ring, then `a − x` lies in
`FormalSpectrum.awayCompletionIdeal`, so leg continuity
(`AlgebraicGeometry.tateInvNodeChartAwayLegX_mem_pow` and its `YX` companion,
`FormalSchemes.TateInvNodeChartLegContinuous`, at exponent `1`) puts the two legs of `x` in the
same residue class of `A{1/x}{1/(x + y − 1)}`, because they agree at `a`. But the `x` leg sends `x`
to `x` and the `YX` leg sends it to `q·x`
(`AlgebraicGeometry.tateInvGlobalLegYX_overlapX`, `FormalSchemes.TateInvGlobalProperness`), and
`q` dies in the residue while `x` does not — the second by
`exists_mem_asIdeal_iff_mem_annulusBranchXPoint`, which is where `I ≠ ⊤` is spent. -/
theorem notMem_range_quotientMap_tateInvNodeChartAwaySubring_of_le :
    Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)
          (overlapX R I q)) ∉
      Set.range (Ideal.quotientMap (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) (tateInvNodeChartAwaySubring R I q hq hI).subtype
        (le_rfl : tateInvNodeChartAwayIdeal R I q hq hI ≤ _)) := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hawX : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hawY : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  rintro ⟨z, hz⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha⟩ := a
  rw [Ideal.quotientMap_mk] at hz
  obtain ⟨v, hv⟩ := exists_mem_asIdeal_iff_mem_annulusBranchXPoint R I q hq hI 𝔭 h𝔭
  set α := awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)
    (overlapX R I q) with hα
  have hd : a - α ∈
      (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) ^ 1 := by
    rw [pow_one]; exact Ideal.Quotient.eq.mp hz
  have h1 := tateInvNodeChartAwayLegX_mem_pow R I q hq hI 1 hd
  have h2 := tateInvNodeChartAwayLegYX_mem_pow R I q hq hI 1 hd
  rw [pow_one] at h1 h2
  have hae : tateInvNodeChartAwayLegX R I q hq hI a = tateInvNodeChartAwayLegYX R I q hq hI a := by
    rw [tateInvNodeChartAwaySubring_eq_inf_eqLocus] at ha
    exact (Subring.mem_inf.mp ha).1
  have hdiff : tateInvNodeChartAwayLegX R I q hq hI α -
      tateInvNodeChartAwayLegYX R I q hq hI α ∈ tateInvNodeChartTargetIdealX R I q hq hI := by
    have hrw : tateInvNodeChartAwayLegX R I q hq hI α -
        tateInvNodeChartAwayLegYX R I q hq hI α =
        tateInvNodeChartAwayLegYX R I q hq hI (a - α) -
          tateInvNodeChartAwayLegX R I q hq hI (a - α) := by
      rw [map_sub, map_sub, hae]; ring
    rw [hrw]
    exact Ideal.sub_mem _ h2 h1
  have hdiff2 : tateInvNodeChartTargetEquivX R I q hq hI
        (tateInvNodeChartAwayLegX R I q hq hI α) -
      tateInvNodeChartTargetEquivX R I q hq hI (tateInvNodeChartAwayLegYX R I q hq hI α) ∈
      awayCompletionIdeal (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q)) := by
    rw [← map_sub]
    exact hdiff
  rw [hα, tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX R I q hq hI (overlapX R I q),
    tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegYX R I q hq hI (overlapX R I q),
    tateInvGlobalLegYX_overlapX R I q hI,
    show tateInvGlobalLegX (R := R) (I := I) (q := q)
        (algebraMap R (annulusAlgebra R I q) q * overlapX R I q) =
      awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
        (algebraMap R (annulusAlgebra R I q) q * overlapX R I q) from rfl] at hdiff2
  have hqmem : algebraMap R (annulusAlgebra R I q) q ∈ annulusIdealOfDefinition R I q := by
    rw [← annulus_map_eq]; exact Ideal.mem_map_of_mem _ hq
  have hzero : Ideal.Quotient.mk (awayCompletionIdeal
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
        (annulusNodeChartCoord R I q)))
      (awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (algebraMap R (annulusAlgebra R I q) q * overlapX R I q))) ∈ v.asIdeal := by
    rw [hv]
    rw [show Ideal.Quotient.mk (annulusIdealOfDefinition R I q)
        (algebraMap R (annulusAlgebra R I q) q * overlapX R I q) = 0 by
      rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hqmem, zero_mul]]
    exact Ideal.zero_mem _
  rw [← Ideal.Quotient.eq.mpr hdiff2] at hzero
  exact notMem_annulusBranchXPoint_overlapX R I q hq 𝔭 h𝔭 ((hv _).mp hzero)

end Witness

include hq hI in
/-- **The witness: the residue of the coordinate `x` in `A{1/(x + y − 1)}` is congruent to no
element of the chart ring**, for `I ≠ ⊤`.
`AlgebraicGeometry.not_surjective_quotientMap_tateInvNodeChartAwaySubring` says that some residue
is missed and produces none; this names one, and it names the same one the global case misses
(`AlgebraicGeometry.notMem_tateInvGlobalSubring_overlapX`,
`FormalSchemes.TateInvGlobalProperness`).

**It is strictly stronger than the statement it refines in a second way.** That one is proved by
contraposing a fact about primes and carries this cluster's two standing hypotheses — the finite
generation of `AlgebraicGeometry.tateInvNodeChartQuotientIdeal` and its
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` witness. This one carries neither: nothing
in its proof mentions the action, the quotient or a chart. -/
theorem notMem_range_quotientMap_tateInvNodeChartAwaySubring (hItop : I ≠ ⊤) :
    Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)
          (overlapX R I q)) ∉
      Set.range (Ideal.quotientMap (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) (tateInvNodeChartAwaySubring R I q hq hI).subtype
        (le_rfl : tateInvNodeChartAwayIdeal R I q hq hI ≤ _)) := by
  obtain ⟨𝔪, h𝔪, h𝔪le⟩ := Ideal.exists_le_maximal I hItop
  haveI : 𝔪.IsPrime := h𝔪.isPrime
  exact notMem_range_quotientMap_tateInvNodeChartAwaySubring_of_le R I q hq hI 𝔪 h𝔪le

include hq hI in
/-- **The coordinate `x` is an explicit element of `A{1/(x + y − 1)}` outside the chart ring**, for
`I ≠ ⊤`: if it were inside, its own residue would be in the image of the chart ring. -/
theorem notMem_tateInvNodeChartAwaySubring_overlapX (hItop : I ≠ ⊤) :
    awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)
        (overlapX R I q) ∉ tateInvNodeChartAwaySubring R I q hq hI := fun hmem =>
  notMem_range_quotientMap_tateInvNodeChartAwaySubring R I q hq hI hItop
    ⟨Ideal.Quotient.mk _ ⟨_, hmem⟩, Ideal.quotientMap_mk⟩

include hq hI in
/-- The existential form of `notMem_tateInvNodeChartAwaySubring_overlapX`, with the witness named —
the mirror of `AlgebraicGeometry.exists_notMem_tateInvGlobalSubring` one ring down. -/
theorem exists_notMem_tateInvNodeChartAwaySubring (hItop : I ≠ ⊤) :
    ∃ a : awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q),
      a ∉ tateInvNodeChartAwaySubring R I q hq hI :=
  ⟨_, notMem_tateInvNodeChartAwaySubring_overlapX R I q hq hI hItop⟩

include hq hI in
/-- **The chart ring is a proper subring of `A{1/(x + y − 1)}` for `I ≠ ⊤`, with no hypothesis on
the quotient.** This is `AlgebraicGeometry.tateInvNodeChartAwaySubring_ne_top` with the finite
generation of `AlgebraicGeometry.tateInvNodeChartQuotientIdeal` and its
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` witness dropped, and with the missing
element exhibited. **Both statements stay.** The conditional one is the end of the route through
row 1849's refutation, is what the clause section's other statements sit beside, and is what the
`Spf`-of-the-inclusion spelling delivers; this one is a different proof of a stronger statement and
does not supersede that route. A duplicate-statement scan will report the pair as differing only in
binders, and that is what it is. -/
theorem tateInvNodeChartAwaySubring_ne_top' (hItop : I ≠ ⊤) :
    tateInvNodeChartAwaySubring R I q hq hI ≠ ⊤ := fun htop =>
  notMem_tateInvNodeChartAwaySubring_overlapX R I q hq hI hItop (htop ▸ Subring.mem_top _)

end AlgebraicGeometry

end
