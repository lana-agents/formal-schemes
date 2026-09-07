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

**And the exact size of what the criterion leaves.**
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

## What is *not* proved here

**The orbit-separation clause is not decided, in either direction.** The criterion is one-way and
the statement below it says how far one-way. Nothing here computes the trace of any prime, exhibits
two primes with equal traces, or shows that the traces separate the primes.

**The criterion's hypothesis is not known to hold and is not known to fail.** There is no
instantiation on this tree at which its truth value is known, so no example is given below and none
should be read into the criterion's existence. In particular a refutation of that hypothesis would
**not** refute the clause, for the reason the second statement makes precise.

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
untouched, and nothing here decides whether `AlgebraicGeometry.tateInvNodeChartAwaySubring` is
proper in the ambient ring.

## Placement

Over `FormalSchemes.TateInvNodeChartSpaceHalfTrace`: forward closure **268** project modules
besides itself, reverse closure **0**, counted by walking every `^import FormalSchemes.` line over
the 559 modules under `FormalSchemes/` (a module is not counted in its own closure; the aggregator
at the repository root is outside the walk).

**One import suffices and that was measured rather than assumed.** The three inputs are
`FormalSchemes.TateInvNodeChartSpaceHalfTrace` (for the `↔` the two consequences rewrite by),
`FormalSchemes.TateActionInv` (for the cover-shift law) and `FormalSchemes.ActionQuotientCarrier`
(for the points of an action quotient). The forward closure of
`FormalSchemes.TateInvNodeChartSpaceHalfTrace` is **267**, and the walk puts the other two inside
it, so this file pays for one import and gets all three.

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

**This is the first property of the `σ`-action used anywhere in this cluster** beyond the
invariance that makes `AlgebraicGeometry.nodeChartQuotientHom` exist, and it is the only one used
below.

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

**This is a sufficient condition and not a characterisation**, and the hypothesis is not known to
hold or to fail at any instantiation on this tree. Refuting it would leave the clause open;
`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff_exists_index` is what says how much room
is left. -/
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

end Clause

end AlgebraicGeometry

end
