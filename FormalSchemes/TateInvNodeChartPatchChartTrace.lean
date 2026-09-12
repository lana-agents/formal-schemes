import FormalSchemes.TateInvNodeChartPatchChartGerm

set_option linter.style.header false

/-!
# The germ-invertibility pattern is the trace of a prime on the away subring

`FormalSchemes.TateInvNodeChartBasicOpenPreimage` restated the injectivity clause of the space
half of hypothesis 4 of `AlgebraicGeometry.exists_formalScheme_of_adicSections` as

> for all `x y` in the chain: if `AlgebraicGeometry.nodeChartPsi g` has an invertible germ at `x`
> exactly when it has one at `y`, for every `g`, then `x` and `y` have the same image under the
> restricted projection

(`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff`), and
`FormalSchemes.TateInvNodeChartPatchChartGerm` computed each of those germs on the patch-`i`
basic-open chart (`AlgebraicGeometry.isUnit_germ_nodeChartPsi_iff`), recording that it **compares
no two of them**. This file compares them.

> `AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff_forall_mem_asIdeal_iff`: the clause
> holds **iff** for all indices `i j` and all primes `w w'` of `A{1/(x + y − 1)}` whose traces on
> `AlgebraicGeometry.tateInvNodeChartAwaySubring` agree, the two points the charts produce have the
> same image under the restricted projection.

No germ, no chart and no `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` appears on
the right-hand side. What is left is a question about **two primes of one ring**.

## Why it is one ring, and why that is the useful part

Every patch chart of the saturated locus has the *same* ring and the *same* ideal of definition —
`FormalSpectrum.awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)` and
`FormalSpectrum.awayCompletionIdeal` of the same — on the nose, because
`AlgebraicGeometry.FormalScheme.AffineChart.ofPatchBasicOpen` sets them that way and the index
enters only through the patch inclusion. That is
`AlgebraicGeometry.nodeChartPatchChart_R`, `AlgebraicGeometry.nodeChartPatchChart_I` and
`AlgebraicGeometry.nodeChartPatchChart_I_eq`, all three by `rfl`, and it is what makes the
right-hand side above a statement about two primes of one ring rather than a comparison across two
rings. The type of `AlgebraicGeometry.nodeChartPatchChartLift` already says it — it mentions no
index — so the content of these three is that the reading is not an accident of notation.

## What the comparison costs, and what it does not buy

The `↔` between the two patterns is **not** an implication in disguise:
`AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv` is a `RingEquiv` onto
`AlgebraicGeometry.tateInvNodeChartAwaySubring`, so quantifying over the sections `g` *is*
quantifying over the elements `a` of that subring, and the germ formula's two sides are both
negations, so the polarity is fixed by `not_iff_not` once.

**One direction of the residual condition is free and is landed.**
`AlgebraicGeometry.forall_mem_asIdeal_iff_of_base_restrictπ_eq`: two points with the same image
under the restricted projection have the same trace. That is the projection coequalising the
action, read through the germ formula.

**The other direction is the whole content and is not delivered here.** Nothing below says that two
primes with the same trace produce points in the same orbit, and nothing below uses any property of
the `σ`-action beyond the invariance already on the tree
(`AlgebraicGeometry.isActionInvariant_nodeChartAdicHom`). **This is the first point in this cluster
at which a property of the action has to be supplied**, and supplying it is a different row —
`FormalSchemes.TateInvNodeChartOrbitSeparation`, which proves that the shift moves the chart index
and fixes the prime, and derives from it a sufficient criterion for the clause — a criterion whose
hypothesis that same file then refutes for `I ≠ ⊤`, leaving the clause open. Nothing below uses
that, and the sentences above stay true of this file.

**The condition is stated pointwise and is deliberately not shipped a second time as an equality of
contracted ideals.** The two spellings do agree — `Ideal.comap` of the two primes along the same
map are equal exactly when the pointwise condition holds — but that agreement is not a fact about
this cluster: the general statement
`Ideal.comap f I = Ideal.comap f J ↔ ∀ a, f a ∈ I ↔ f a ∈ J`, for any ring hom `f`, **is**
Mathlib's `Submodule.ext_iff`, which proves it as a term with no tactic at all, `Ideal.mem_comap`
being definitional. So the contracted-ideal form is a notation for the pointwise one, it belongs to
the `Ideal` API and not to a node-chart module, and stating it here would put a fully general
triviality where nobody wanting it would look.

## Main definitions and results

* `AlgebraicGeometry.nodeChartPatchChart_R`, `AlgebraicGeometry.nodeChartPatchChart_I`,
  `AlgebraicGeometry.nodeChartPatchChart_I_eq`: **the index does not change the ring**, by `rfl`.
* `AlgebraicGeometry.exists_base_nodeChartPatchChartLift_eq`: **the charts exhaust the saturated
  locus**, so a pairwise statement over charts is not a partial one.
* `AlgebraicGeometry.isUnit_germ_nodeChartPsi_nodeChartPatchChartLift_iff`: the germ formula, with
  its hypothesis repackaged as *the point is what the lift produces at `w`*.
* `AlgebraicGeometry.forall_isUnit_germ_nodeChartPsi_iff_forall_mem_asIdeal_iff`: **the pattern is
  a trace.**
* `AlgebraicGeometry.forall_mem_asIdeal_iff_of_base_restrictπ_eq`: **same orbit implies same
  trace** — the free direction.
* `AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff_forall_mem_asIdeal_iff`: **the
  injectivity clause, with no germ and no chart in it.**

## What is *not* proved here

**No clause of hypothesis 4 is decided.** Not injectivity, not surjectivity of
`(AlgebraicGeometry.nodeChartQuotientHom …).base`, not its openness, and not the sheaf half. What
is produced is a restatement of one clause; the condition on the right-hand side is undecided in
both directions and no `g`, no `w` and no pair of primes is exhibited at which it fails.

**Same trace does not imply same orbit anywhere below.** Only the converse is proved
(`AlgebraicGeometry.forall_mem_asIdeal_iff_of_base_restrictπ_eq`), and a one-directional result
must not be read as the clause. Nothing below computes the trace of any prime, exhibits two primes
with equal traces, or shows that the traces separate the orbits.

**`hnode` is undecided in both directions and nothing here moves it.** The chain back to it runs
through `AlgebraicGeometry.exists_formalScheme_of_iso_restrict_tateInvNodeChartQuotientOpens`,
which is **one-way**: even all four hypotheses would give the existence of the formal scheme and
not the converse. And **refuting hypothesis 4 would not refute `hnode`**, because the hypothesis of
`AlgebraicGeometry.exists_formalScheme_of_isIso_desc` is existential while hypothesis 4 is that
condition at a *named* morphism.

**No property of the `σ`-action is established.** The action enters the statement — that is the
point of the restatement — but the only fact about it used below is the invariance already on the
tree, through `AlgebraicGeometry.nodeChartQuotientHom` being defined at all. Freeness, proper
discontinuity and the structure of the orbits of the node locus are untouched.

**The sheaf half and `AlgebraicGeometry.nonvanishingSectionsHom` are untouched.**

**`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` is still a `Classical.choice`**, and
`AlgebraicGeometry.nodeChartAdicHom` is still built from it, so `Classical.choice` still appears in
`#print axioms` of every statement below that mentions `hX`. That is the ambient one and not a new
one.

**Nothing here bears on `AlgebraicGeometry.tateInvNodeChartAmbientHom`**, whose refutation as an
open immersion (`AlgebraicGeometry.not_isOpenImmersion_tateInvNodeChartAmbientHom_of_ne_top`) is
untouched, and nothing here decides whether `AlgebraicGeometry.tateInvNodeChartAwaySubring` is
proper in the ambient ring.

## Placement

Over `FormalSchemes.TateInvNodeChartPatchChartGerm`, which already imports
`FormalSchemes.TateInvNodeChartBasicOpenPreimage`, so both inputs are reached by one import:
forward closure **264** project modules besides itself, reverse closure **2** —
`FormalSchemes.TateInvNodeChartSpaceHalfTrace`, which substitutes the restatement below into the
space half, and `FormalSchemes.TateInvNodeChartOrbitSeparation` above it — counted by walking every
`^import FormalSchemes.` line over the 563 modules under
`FormalSchemes/` (a module is not counted in its own closure; the aggregator at the repository
root is outside the walk).

Appending to `FormalSchemes.TateInvNodeChartPatchChartGerm` was the alternative and is cheaper by a
module. It is not taken for a reason that file states about itself: its *What is not proved here*
says *"nothing below compares two charts, or a chart with its `σ`-translates"*, and that sentence
is doing work — it is what tells a reader of the germ formula that the formula alone decides
nothing about orbits. Appending would falsify it and the repair would have to be a rewrite rather
than an addition. Keeping the comparison one module away leaves the sentence true and lets it carry
a forward pointer instead. Both closures were 0 when that choice was made, so nothing downstream
paid for it; the one consumer above arrived afterwards and sits over this file either way.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4 (10.4.6), §10.6.
* [Deligne–Rapoport], II.1 — the Néron 1-gon.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-! ### The index does not change the ring -/

section Index

variable [IsAdicRing (annulusIdealOfDefinition R I q)]
variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
  (annulusNodeChartCoord R I q))]
variable (i j : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
variable [LocallyRingedSpace.IsOpenImmersion
    (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
      (tateChainInvFormalGlueData R I q hq hI).ι i)]
variable [LocallyRingedSpace.IsOpenImmersion
    (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
      (tateChainInvFormalGlueData R I q hq hI).ι j)]

omit [TopologicalSpace R] [IsAdicRing I] [IsAdicRing (annulusIdealOfDefinition R I q)] in
/-- **The patch-`i` chart's ring is the annulus algebra, whatever `i` is.** By `rfl`:
`AlgebraicGeometry.FormalScheme.AffineChart.ofPatchBasicOpen` takes the ring from the basic-open
chart of the patch, and the index enters only through the patch inclusion. -/
theorem nodeChartPatchChart_R {y : (tateChainInv R I q hq hI)}
    (hy : y ∈ Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q) ≫ (tateChainInvFormalGlueData R I q hq hI).ι i).base) :
    (nodeChartPatchChart R I q hq hI i hy).R
      = awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) := rfl

omit [TopologicalSpace R] [IsAdicRing I] [IsAdicRing (annulusIdealOfDefinition R I q)] in
/-- **Its ideal of definition is `FormalSpectrum.awayCompletionIdeal` of the same, whatever `i`
is.** By `rfl`, for the same reason as `AlgebraicGeometry.nodeChartPatchChart_R`; that this
statement typechecks at all is that theorem. -/
theorem nodeChartPatchChart_I {y : (tateChainInv R I q hq hI)}
    (hy : y ∈ Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q) ≫ (tateChainInvFormalGlueData R I q hq hI).ι i).base) :
    (nodeChartPatchChart R I q hq hI i hy).I
      = awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q) := rfl

omit [TopologicalSpace R] [IsAdicRing I] [IsAdicRing (annulusIdealOfDefinition R I q)] in
/-- **Two patch charts at different indices have the same ideal of definition**, and — since
`AlgebraicGeometry.FormalScheme.AffineChart.I` is an ideal of the chart's own ring — the statement
typechecking is the assertion that they have the same ring.

This is the fact that makes
`AlgebraicGeometry.forall_isUnit_germ_nodeChartPsi_iff_forall_mem_asIdeal_iff` a statement about
**two primes of one ring** and not a comparison across two rings. -/
theorem nodeChartPatchChart_I_eq {y : (tateChainInv R I q hq hI)}
    (hy : y ∈ Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q) ≫ (tateChainInvFormalGlueData R I q hq hI).ι i).base)
    {y' : (tateChainInv R I q hq hI)}
    (hy' : y' ∈ Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q) ≫ (tateChainInvFormalGlueData R I q hq hI).ι j).base) :
    (nodeChartPatchChart R I q hq hI i hy).I
      = (nodeChartPatchChart R I q hq hI j hy').I := rfl

end Index

/-! ### The charts exhaust the saturated locus -/

/-- **Every point of the saturated node-chart locus is produced by a patch chart.** The chain's
patches are jointly surjective (`CategoryTheory.GlueData.ι_jointly_surjective`), the patch-`i`
preimage of the locus is the basic open `D(x + y − 1)`
(`AlgebraicGeometry.map_tateChainInvι_nodeChartSaturationOpens`) whose points are the range of the
basic-open chart (`FormalSpectrum.range_basicOpenChart_base`), and the inclusion of the locus is
injective, so the point produced on the locus is the one asked for.

This is the argument already inside
`AlgebraicGeometry.exists_affineChart_le_comap_tateInvNodeChartAwayIdeal`, extracted and stated at
`AlgebraicGeometry.nodeChartPatchChartLift` rather than re-derived at each use. It is what makes a
statement quantified over charts a statement about the whole locus, so that
`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff_forall_mem_asIdeal_iff` is an `↔` and
not one implication. -/
theorem exists_base_nodeChartPatchChartLift_eq
    (x : (nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace) :
    ∃ (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
      (w : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q))),
      (nodeChartPatchChartLift R I q hq hI i).base w = x := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) := isAdicRing_tateInvNodeChartAmbient R I q hI
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) :=
    isOpenImmersion_basicOpenChart _ _ (annulusIdealOfDefinition_fg R I q hI)
  have hy : ((tateChainInv R I q hq hI).restrictOpenι (tateChainInv_locallyFG R I q hq hI)
      (nodeChartSaturationOpens R I q hq hI)).base x ∈
      Set.range ((tateChainInv R I q hq hI).restrictOpenι (tateChainInv_locallyFG R I q hq hI)
        (nodeChartSaturationOpens R I q hq hI)).base := ⟨x, rfl⟩
  rw [FormalScheme.range_restrictOpenι_base] at hy
  obtain ⟨i, z, hz⟩ := (tateChainInvFormalGlueData R I q hq hI).ι_jointly_surjective
    (((tateChainInv R I q hq hI).restrictOpenι (tateChainInv_locallyFG R I q hq hI)
      (nodeChartSaturationOpens R I q hq hI)).base x)
  have hz' : z ∈ Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)).base := by
    rw [range_basicOpenChart_base _ _ (annulusIdealOfDefinition_fg R I q hI),
      ← map_tateChainInvι_nodeChartSaturationOpens R I q hq hI i]
    rw [← hz] at hy
    exact hy
  obtain ⟨w, hw⟩ := hz'
  refine ⟨i, w, ?_⟩
  have hinj : Function.Injective ((tateChainInv R I q hq hI).restrictOpenι
      (tateChainInv_locallyFG R I q hq hI) (nodeChartSaturationOpens R I q hq hI)).base :=
    (FormalScheme.isOpenImmersion_restrictOpenι _ (tateChainInv_locallyFG R I q hq hI)
      (nodeChartSaturationOpens R I q hq hI)).base_open.injective
  apply hinj
  have hc := nodeChartPatchChartLift_comp R I q hq hI i
  have := congrFun (congrArg (fun m : FormalSpectrum.locallyRingedSpaceObj
      (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) ⟶ (tateChainInv R I q hq hI).toLocallyRingedSpace =>
    ⇑(ConcreteCategory.hom m.base)) hc) w
  refine this.trans ?_
  rw [← hz, ← hw]
  rfl

/-! ### The germ pattern at a point of a chart -/

set_option backward.isDefEq.respectTransparency false in
/-- **The germ formula, with its hypothesis repackaged.**
`AlgebraicGeometry.isUnit_germ_nodeChartPsi_iff` states its conclusion at a point `x` of the
saturated locus together with a proof that the patch chart hits it at `w`; this states it at the
point the chart produces, which is the form every statement below consumes.

The `set_option` is the one `FormalSchemes.TateInvNodeChartPatchChartAdic` uses for the same
purpose: without it, instance synthesis does not see that a composite of the basic-open chart with
a patch inclusion is an open immersion at a bound index. -/
theorem isUnit_germ_nodeChartPsi_nodeChartPatchChartLift_iff
    (i : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
    (w : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q))) (g) :
    IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤
        ((nodeChartPatchChartLift R I q hq hI i).base w) trivial
        (nodeChartPsi R I q hq hI g)) ↔
      Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q))
        ((tateInvNodeChartAwaySubring R I q hq hI).subtype
          (tateInvNodeChartQuotientRingEquiv R I q hq hI g)) ∉ w.asIdeal := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) := isAdicRing_tateInvNodeChartAmbient R I q hI
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) :=
    isOpenImmersion_basicOpenChart _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI := (tateChainInvFormalGlueData R I q hq hI).ι_isOpenImmersion i
  haveI : LocallyRingedSpace.IsOpenImmersion
      (basicOpenChart (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) ≫
        (tateChainInvFormalGlueData R I q hq hI).ι i) := inferInstance
  have hy : (basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q) ≫ (tateChainInvFormalGlueData R I q hq hI).ι i).base w ∈
      Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q) ≫
          (tateChainInvFormalGlueData R I q hq hI).ι i).base := ⟨w, rfl⟩
  have hw : (nodeChartPatchChart R I q hq hI i hy).map.base w
      = ((tateChainInv R I q hq hI).restrictOpenι (tateChainInv_locallyFG R I q hq hI)
        (nodeChartSaturationOpens R I q hq hI)).base
        ((nodeChartPatchChartLift R I q hq hI i).base w) := by
    have h := nodeChartPatchChartLift_comp R I q hq hI i
    exact (congrFun (congrArg (fun m : FormalSpectrum.locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q)) ⟶ (tateChainInv R I q hq hI).toLocallyRingedSpace =>
      ⇑(ConcreteCategory.hom m.base)) h) w).symm
  exact isUnit_germ_nodeChartPsi_iff R I q hq hI i hy _ w hw g

/-! ### The pattern is a trace -/

/-- **The germ-invertibility patterns of two points of two patch charts agree exactly when the two
primes have the same trace on the away subring.**

Both sides of the germ formula are memberships-of-a-prime negated, so the polarity is fixed by
`not_iff_not` once and not twice, and the passage from *for every section `g`* to *for every
element `a` of the subring* is not an argument:
`AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv` is a `RingEquiv` onto
`AlgebraicGeometry.tateInvNodeChartAwaySubring`, so the two quantifiers range over the same things.
That is why this is an `↔` and not an implication.

`w` and `w'` are primes of **one** ring even when `i ≠ j`; see
`AlgebraicGeometry.nodeChartPatchChart_I_eq`. -/
theorem forall_isUnit_germ_nodeChartPsi_iff_forall_mem_asIdeal_iff
    (i j : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
    (w w' : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q))) :
    (∀ g, IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤
          ((nodeChartPatchChartLift R I q hq hI i).base w) trivial
          (nodeChartPsi R I q hq hI g)) ↔
        IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤
          ((nodeChartPatchChartLift R I q hq hI j).base w') trivial
          (nodeChartPsi R I q hq hI g))) ↔
      ∀ a : tateInvNodeChartAwaySubring R I q hq hI,
        (Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q)) (a : awayCompletion (annulusIdealOfDefinition R I q)
              (annulusNodeChartCoord R I q)) ∈ w.asIdeal ↔
          Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q)) (a : awayCompletion (annulusIdealOfDefinition R I q)
              (annulusNodeChartCoord R I q)) ∈ w'.asIdeal) := by
  constructor
  · intro h a
    obtain ⟨g, rfl⟩ := (tateInvNodeChartQuotientRingEquiv R I q hq hI).surjective a
    exact not_iff_not.mp
      (((isUnit_germ_nodeChartPsi_nodeChartPatchChartLift_iff R I q hq hI i w g).symm.trans
        (h g)).trans (isUnit_germ_nodeChartPsi_nodeChartPatchChartLift_iff R I q hq hI j w' g))
  · intro h g
    exact ((isUnit_germ_nodeChartPsi_nodeChartPatchChartLift_iff R I q hq hI i w g).trans
      (not_iff_not.mpr (h (tateInvNodeChartQuotientRingEquiv R I q hq hI g)))).trans
      (isUnit_germ_nodeChartPsi_nodeChartPatchChartLift_iff R I q hq hI j w' g).symm

/-! ### The injectivity clause, with no germ and no chart -/

section Restatement

variable [TopologicalSpace ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
  (op (tateInvNodeChartQuotientOpens R I q hq hI)))]
variable [IsAdicRing (tateInvNodeChartQuotientIdeal R I q hq hI)]
variable (hfgI : (tateInvNodeChartQuotientIdeal R I q hq hI).FG)
variable (hX : FormalScheme.AdicSectionsLocallyFG (tateInvNodeChartQuotientIdeal R I q hq hI)
  (nodeChartPsi R I q hq hI))

/-- **Same orbit implies same trace: the free direction.** Two points of the saturated locus with
the same image under the restricted projection have the same image under it followed by
`AlgebraicGeometry.nodeChartQuotientHom`, so their germ patterns agree
(`AlgebraicGeometry.base_nodeChartQuotientHom_restrictπ_eq_iff`), so their traces agree. That is
the projection coequalising the action, read through the germ formula, and it uses no property of
the `σ`-action beyond the invariance that makes
`AlgebraicGeometry.nodeChartQuotientHom` exist at all.

**The converse is the whole content of the clause and is not proved anywhere below.** Nothing here
says that two primes with the same trace produce points in the same orbit.

The two hypotheses about the node chart's ideal of definition and its adic sections are hypotheses
that the conclusion does not mention, and that is deliberate rather than an oversight: the only
route on the tree from *same image under the restricted projection* to
*same germ pattern* is
`AlgebraicGeometry.base_nodeChartQuotientHom_restrictπ_eq_iff`, which is stated at
`AlgebraicGeometry.nodeChartQuotientHom`. Whether the implication holds without them is not
addressed here. -/
theorem forall_mem_asIdeal_iff_of_base_restrictπ_eq
    (hfgI : (tateInvNodeChartQuotientIdeal R I q hq hI).FG)
    (hX : FormalScheme.AdicSectionsLocallyFG (tateInvNodeChartQuotientIdeal R I q hq hI)
      (nodeChartPsi R I q hq hI))
    (i j : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
    (w w' : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)))
    (h : (LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
            (tateInvNodeChartQuotientOpens R I q hq hI)).base
          ((nodeChartPatchChartLift R I q hq hI i).base w) =
        (LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
            (tateInvNodeChartQuotientOpens R I q hq hI)).base
          ((nodeChartPatchChartLift R I q hq hI j).base w')) (a) :
    Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q))
        ((tateInvNodeChartAwaySubring R I q hq hI).subtype a) ∈ w.asIdeal ↔
      Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q))
        ((tateInvNodeChartAwaySubring R I q hq hI).subtype a) ∈ w'.asIdeal :=
  (forall_isUnit_germ_nodeChartPsi_iff_forall_mem_asIdeal_iff R I q hq hI i j w w').mp
    ((base_nodeChartQuotientHom_restrictπ_eq_iff R I q hq hI hfgI hX _ _).mp
      (congrArg (nodeChartQuotientHom R I q hq hI hfgI hX).base h)) a

/-- **The injectivity clause of the space half, with no germ and no chart in it.** The base map of
`AlgebraicGeometry.nodeChartQuotientHom` is injective exactly when, for every pair of indices and
every pair of primes of `A{1/(x + y − 1)}` with the same trace on
`AlgebraicGeometry.tateInvNodeChartAwaySubring`, the two points the charts produce have the same
image under the restricted projection.

`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff` with the germ pattern replaced by the
trace (`AlgebraicGeometry.forall_isUnit_germ_nodeChartPsi_iff_forall_mem_asIdeal_iff`) and the
quantifier over points of the locus replaced by one over charts
(`AlgebraicGeometry.exists_base_nodeChartPatchChartLift_eq`). Neither step loses anything: the
first is an `↔` and the second is a surjectivity, which is why this is an `↔` and not one
implication.

**This is a restatement and decides nothing.** It is one of the two conditions in `IsIso …base`,
the other two being `AlgebraicGeometry.surjective_base_nodeChartQuotientHom_iff` and
`AlgebraicGeometry.isOpenMap_base_nodeChartQuotientHom_iff`, and its right-hand side is undecided
in both directions. What it buys is that the undecided thing is now **orbit separation against an
equality of traces of two primes of one ring**: one direction is free
(`AlgebraicGeometry.forall_mem_asIdeal_iff_of_base_restrictπ_eq`), and the other is where a
property of the `σ`-action has to enter. -/
theorem injective_base_nodeChartQuotientHom_iff_forall_mem_asIdeal_iff :
    Function.Injective (nodeChartQuotientHom R I q hq hI hfgI hX).base ↔
      ∀ (i j : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.J)
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
            ((nodeChartPatchChartLift R I q hq hI j).base w') := by
  rw [injective_base_nodeChartQuotientHom_iff R I q hq hI hfgI hX]
  constructor
  · intro h i j w w' ha
    exact h _ _ ((forall_isUnit_germ_nodeChartPsi_iff_forall_mem_asIdeal_iff
      R I q hq hI i j w w').mpr ha)
  · intro h x y hg
    obtain ⟨i, w, rfl⟩ := exists_base_nodeChartPatchChartLift_eq R I q hq hI x
    obtain ⟨j, w', rfl⟩ := exists_base_nodeChartPatchChartLift_eq R I q hq hI y
    exact h i j w w' ((forall_isUnit_germ_nodeChartPsi_iff_forall_mem_asIdeal_iff
      R I q hq hI i j w w').mp hg)

end Restatement

end AlgebraicGeometry

end
