import FormalSchemes.TateInvNodeChartAmbient
import FormalSchemes.AdicSubringComplete

set_option linter.style.header false

/-!
# The node chart ring inside `A{1/(x + y − 1)}`: closedness, and what completeness costs

`FormalSchemes.TateInvNodeChartAmbient` displays the node chart's candidate ring as a `Subring`
`AlgebraicGeometry.tateInvNodeChartAwaySubring` of `A{1/(x + y − 1)}`, proves the ambient ring is
a complete adic ring (`AlgebraicGeometry.isAdicRing_tateInvNodeChartAmbient`), and proves the
candidate ideal `AlgebraicGeometry.tateInvNodeChartAwayIdeal` is Hausdorff. It leaves
**completeness** open.

`FormalSchemes.AdicSubringComplete` splits that residue into a topological half — adic closedness
of the subring, which gives `Subring.IsInducedPrecomplete` with no further hypothesis — and an
algebraic half, `Subring.HasCofinalInducedFiltration`, comparing the power filtration of the
contracted ideal with the induced one. This file runs that split at the node chart, and closes as
much of the closedness half as the tree currently supports.

## What is proved here

* **The chart ring is an intersection of two equalizers inside `A{1/(x + y − 1)}`.**
  `AlgebraicGeometry.tateInvNodeChartAwaySubring_eq_inf_eqLocus` transports
  `AlgebraicGeometry.tateInvChartAnnulusSubring`'s description across
  `AlgebraicGeometry.tateInvNodeChartAmbientEquiv`, so the four legs become four ring
  homomorphisms out of `A{1/(x + y − 1)}`:
  `AlgebraicGeometry.tateInvNodeChartAwayLegX`, `…LegYX`, `…LegY`, `…LegXY`.
* **Both leg targets are sections over a *basic* open, and both are Hausdorff.** This is the
  question 1284's goal 2 flagged as unknown, and the answer is yes:
  `AlgebraicGeometry.tateInvNodeChartTargetOpensX_eq_basicOpen` and its `y`-side mirror identify
  the target opens as `D` of the image of the chart coordinate, by the general
  `FormalSpectrum.preimage_basicOpen_basicOpenChart` (which is `rfl`). So each target is a
  twice-completed localization `A{1/x}{1/(x + y − 1)}` resp. `A{1/y}{1/(x + y − 1)}`
  (`AlgebraicGeometry.tateInvNodeChartTargetEquivX`, `…Y`), it carries the ideal
  `AlgebraicGeometry.tateInvNodeChartTargetIdealX`, `…Y`, and
  `AlgebraicGeometry.isHausdorff_tateInvNodeChartTargetIdealX` and its mirror hold with no
  hypothesis beyond `I.FG`.
* **Continuity of the four legs makes the chart ring adically closed**, and closedness alone
  makes it complete for the induced filtration:
  `AlgebraicGeometry.isAdicallyClosed_tateInvNodeChartAwaySubring` and
  `AlgebraicGeometry.isInducedPrecomplete_tateInvNodeChartAwaySubring`.
* **Adic completeness of `tateInvNodeChartAwayIdeal`, from closedness plus the filtration
  bridge**: `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal`, and its form starting
  from leg continuity, `…_of_legContinuous`.

## What is *not* proved

* **`AlgebraicGeometry.IsTateInvNodeChartLegContinuous` is not proved for the node chart's legs,
  and it is not exhibited as false either.** It is stated here as a `Prop` so that the conditional
  results have a single named hypothesis. The obstruction is isolated: the legs are `.c.app`s of
  morphisms of formal spectra, and both of this file's identifications of a section ring — the
  ambient one through `AlgebraicGeometry.tateInvNodeChartAmbientEquiv` and the target ones through
  `AlgebraicGeometry.tateInvNodeChartTargetEquivX` — go through
  `FormalSpectrum.sectionsBasicOpenEquiv`, which the tree states as a bare `RingEquiv`. Whether it
  is a map of `A`-algebras, equivalently whether it carries `FormalSpectrum.awayCompletionIdeal`
  to the extension of `annulusIdealOfDefinition` along `A → Γ(D(f))`, is what a proof of leg
  continuity would need, and this tree does not say.
* **`Subring.HasCofinalInducedFiltration` is not proved for this subring**, and no `(A, K, S)` at
  which it fails is exhibited. `FormalSchemes.AdicSubringComplete` proves two sufficient
  conditions for it; neither is checked here.
* **`AlgebraicGeometry.tateInvNodeChartAwayIdeal` is not shown to be finitely generated**, which
  is a separate obligation from completeness and is not implied by it. So nothing here says the
  chart ring is an adic ring in this tree's sense.
* **Nothing here is a chart.** No open immersion `Spf J ⟶ Q` is constructed, `hnode` is untouched,
  and no claim is made about `AlgebraicGeometry.tateInvNodeChartAmbientHom` being an open
  immersion. Nothing here says the chart ring is nonzero, proper, or larger than the base.

Nothing here weakens `LocallyRingedSpace.IsProperlyDiscontinuousOn`,
`LocallyRingedSpace.IsFreeProperlyDiscontinuous` or
`LocallyRingedSpace.freeActionQuotientFormalScheme`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.4.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
-/
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

namespace FormalSpectrum

/-- **The preimage of a basic open under a basic-open chart is a basic open**, cut out by the
image of the same element under the chart's structural ring map. Both sides are, by definition,
`PrimeSpectrum.basicOpen` of the residue of that element, so this is `rfl`. -/
theorem preimage_basicOpen_basicOpenChart {R : Type u} [CommRing R] [TopologicalSpace R]
    (I : Ideal R) [IsAdicRing I] (f : R) [IsAdicRing (awayCompletionIdeal I f)] (c : R) :
    (Opens.map (basicOpenChart I f).base).obj (basicOpen I c) =
      basicOpen (awayCompletionIdeal I f) (awayCompletionHom I f c) :=
  rfl

/-- **The ideal of definition of `R{1/f}` is finitely generated** when `I` is: it is the image of
`I` under `FormalSpectrum.awayCompletionHom`. -/
theorem awayCompletionIdeal_fg {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R)
    [IsAdicRing I] (f : R) (hI : I.FG) : (awayCompletionIdeal I f).FG := by
  rw [← map_awayCompletionHom I f]
  exact hI.map _

end FormalSpectrum

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- The common target of the node chart's two forward legs: sections of `O_{Spf A{1/x}}` over the
preimage of the chart's domain. -/
abbrev tateInvNodeChartTargetX : Type u :=
  ((locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapX R I q))).presheaf.obj
    (op ((Opens.map (annulusOverlapChart R I q).base).obj
      (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)))) : Type u)

/-- The common target of the node chart's two backward legs. -/
abbrev tateInvNodeChartTargetY : Type u :=
  ((locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapY R I q))).presheaf.obj
    (op ((Opens.map (annulusOverlapChartY R I q).base).obj
      (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)))) : Type u)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `x`-side target open is a basic open of `Spf A{1/x}`**, cut out by the image of the
node chart's coordinate. It is `FormalSpectrum.preimage_basicOpen_basicOpenChart` after
`AlgebraicGeometry.tateInvNodeChartOpens_eq_basicOpen` identifies the source open. -/
theorem tateInvNodeChartTargetOpensX_eq_basicOpen :
    (Opens.map (annulusOverlapChart R I q).base).obj
        (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)) =
      basicOpen (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q)) := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _haw : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  rw [tateInvNodeChartOpens_eq_basicOpen R I q hq hI]
  exact FormalSpectrum.preimage_basicOpen_basicOpenChart _ _ _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `y`-side target open is a basic open of `Spf A{1/y}`**, by the same argument. -/
theorem tateInvNodeChartTargetOpensY_eq_basicOpen :
    (Opens.map (annulusOverlapChartY R I q).base).obj
        (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)) =
      basicOpen (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
          (annulusNodeChartCoord R I q)) := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _haw : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  rw [tateInvNodeChartOpens_eq_basicOpen R I q hq hI]
  exact FormalSpectrum.preimage_basicOpen_basicOpenChart _ _ _

/-- **The `x`-side target is the twice-completed localization `A{1/x}{1/(x + y − 1)}`**, by
`FormalSpectrum.sectionsEquivOfEqBasicOpen` at the previous theorem. -/
def tateInvNodeChartTargetEquivX : tateInvNodeChartTargetX R I q hq hI ≃+*
    awayCompletion (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
        (annulusNodeChartCoord R I q)) :=
  FormalSpectrum.sectionsEquivOfEqBasicOpen _
    (tateInvNodeChartTargetOpensX_eq_basicOpen R I q hq hI)

/-- **The `y`-side target is `A{1/y}{1/(x + y − 1)}`.** -/
def tateInvNodeChartTargetEquivY : tateInvNodeChartTargetY R I q hq hI ≃+*
    awayCompletion (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
        (annulusNodeChartCoord R I q)) :=
  FormalSpectrum.sectionsEquivOfEqBasicOpen _
    (tateInvNodeChartTargetOpensY_eq_basicOpen R I q hq hI)

/-- The `x`-side target's ideal of definition, pulled back to the presheaf-section spelling. -/
def tateInvNodeChartTargetIdealX : Ideal (tateInvNodeChartTargetX R I q hq hI) :=
  (awayCompletionIdeal (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
        (annulusNodeChartCoord R I q))).comap
    (tateInvNodeChartTargetEquivX R I q hq hI).toRingHom

/-- The `y`-side target's ideal of definition, pulled back to the presheaf-section spelling. -/
def tateInvNodeChartTargetIdealY : Ideal (tateInvNodeChartTargetY R I q hq hI) :=
  (awayCompletionIdeal (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
        (annulusNodeChartCoord R I q))).comap
    (tateInvNodeChartTargetEquivY R I q hq hI).toRingHom

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `x`-side target is Hausdorff for that ideal**:
`FormalSpectrum.isHausdorff_awayCompletionIdeal` at the twice-completed localization, transported
along `tateInvNodeChartTargetEquivX` by `isHausdorff_comap`. -/
theorem isHausdorff_tateInvNodeChartTargetIdealX :
    IsHausdorff (tateInvNodeChartTargetIdealX R I q hq hI)
      (tateInvNodeChartTargetX R I q hq hI) :=
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  isHausdorff_comap _ _ (tateInvNodeChartTargetEquivX R I q hq hI).injective
    (FormalSpectrum.isHausdorff_awayCompletionIdeal _ _
      (FormalSpectrum.awayCompletionIdeal_fg _ _ (annulusIdealOfDefinition_fg R I q hI)))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `y`-side target is Hausdorff for that ideal.** -/
theorem isHausdorff_tateInvNodeChartTargetIdealY :
    IsHausdorff (tateInvNodeChartTargetIdealY R I q hq hI)
      (tateInvNodeChartTargetY R I q hq hI) :=
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  isHausdorff_comap _ _ (tateInvNodeChartTargetEquivY R I q hq hI).injective
    (FormalSpectrum.isHausdorff_awayCompletionIdeal _ _
      (FormalSpectrum.awayCompletionIdeal_fg _ _ (annulusIdealOfDefinition_fg R I q hI)))

/-- The `x`-chart leg of the node chart, read on `A{1/(x + y − 1)}`. -/
def tateInvNodeChartAwayLegX :
    awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) →+*
      tateInvNodeChartTargetX R I q hq hI :=
  (tateInvChartLegX (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q)).comp
    (tateInvNodeChartAmbientEquiv R I q hq hI).symm.toRingHom

/-- The transition-then-`y`-chart leg of the node chart, read on `A{1/(x + y − 1)}`. -/
def tateInvNodeChartAwayLegYX :
    awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) →+*
      tateInvNodeChartTargetX R I q hq hI :=
  (tateInvChartLegYX (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q)).comp
    (tateInvNodeChartAmbientEquiv R I q hq hI).symm.toRingHom

/-- The `y`-chart leg of the node chart, read on `A{1/(x + y − 1)}`. -/
def tateInvNodeChartAwayLegY :
    awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) →+*
      tateInvNodeChartTargetY R I q hq hI :=
  (tateInvChartLegY (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q)).comp
    (tateInvNodeChartAmbientEquiv R I q hq hI).symm.toRingHom

/-- The inverse-transition-then-`x`-chart leg of the node chart, read on `A{1/(x + y − 1)}`. -/
def tateInvNodeChartAwayLegXY :
    awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) →+*
      tateInvNodeChartTargetY R I q hq hI :=
  (tateInvChartLegXY (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q)).comp
    (tateInvNodeChartAmbientEquiv R I q hq hI).symm.toRingHom

/-- **The node chart ring is an intersection of two equalizers inside `A{1/(x + y − 1)}`.** -/
theorem tateInvNodeChartAwaySubring_eq_inf_eqLocus :
    tateInvNodeChartAwaySubring R I q hq hI =
      (tateInvNodeChartAwayLegX R I q hq hI).eqLocus (tateInvNodeChartAwayLegYX R I q hq hI) ⊓
        (tateInvNodeChartAwayLegY R I q hq hI).eqLocus
          (tateInvNodeChartAwayLegXY R I q hq hI) := by
  rw [tateInvNodeChartAwaySubring, tateInvNodeChartSubring, tateInvChartAnnulusSubring,
    Subring.map_ringEquiv_inf, Subring.map_ringEquiv_eqLocus, Subring.map_ringEquiv_eqLocus]
  rfl


/-- **The four legs are adically continuous** — the hypothesis this cluster still owes. Each leg
is required to carry the `n`-th power of the ambient ring's ideal of definition into the `n`-th
power of the target's, in the `RingHom`-level spelling of "continuous" that
`RingHom.mem_eqLocus_of_forall_sub_mem_pow` (`FormalSchemes.AdicSubringComplete`) consumes.

**This is not proved for the node chart's legs**; see this file's module docstring. -/
def IsTateInvNodeChartLegContinuous : Prop :=
  (∀ (m : ℕ) {v : awayCompletion (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)},
      v ∈ (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) ^ m →
      tateInvNodeChartAwayLegX R I q hq hI v ∈ tateInvNodeChartTargetIdealX R I q hq hI ^ m) ∧
  (∀ (m : ℕ) {v : awayCompletion (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)},
      v ∈ (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) ^ m →
      tateInvNodeChartAwayLegYX R I q hq hI v ∈ tateInvNodeChartTargetIdealX R I q hq hI ^ m) ∧
  (∀ (m : ℕ) {v : awayCompletion (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)},
      v ∈ (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) ^ m →
      tateInvNodeChartAwayLegY R I q hq hI v ∈ tateInvNodeChartTargetIdealY R I q hq hI ^ m) ∧
  (∀ (m : ℕ) {v : awayCompletion (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)},
      v ∈ (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) ^ m →
      tateInvNodeChartAwayLegXY R I q hq hI v ∈ tateInvNodeChartTargetIdealY R I q hq hI ^ m)

/-- **Continuity of the four legs makes the node chart ring adically closed in
`A{1/(x + y − 1)}`.** `RingHom.isAdicallyClosed_inf_eqLocus`
(`FormalSchemes.AdicSubringComplete`) at the description
`tateInvNodeChartAwaySubring_eq_inf_eqLocus`, with the two targets shown Hausdorff by
`isHausdorff_tateInvNodeChartTargetIdealX` and its `y`-side mirror. -/
theorem isAdicallyClosed_tateInvNodeChartAwaySubring
    (hcont : IsTateInvNodeChartLegContinuous R I q hq hI) :
    (tateInvNodeChartAwaySubring R I q hq hI).IsAdicallyClosed
      (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hcont
  rw [tateInvNodeChartAwaySubring_eq_inf_eqLocus R I q hq hI]
  exact RingHom.isAdicallyClosed_inf_eqLocus h1 h2 h3 h4
    (isHausdorff_tateInvNodeChartTargetIdealX R I q hq hI)
    (isHausdorff_tateInvNodeChartTargetIdealY R I q hq hI)

/-- **Adic closedness gives completeness for the induced filtration, unconditionally.** The
ambient ring `A{1/(x + y − 1)}` is complete by
`AlgebraicGeometry.isAdicRing_tateInvNodeChartAmbient`, so
`Subring.isInducedPrecomplete_of_isAdicallyClosed` applies with no further hypothesis.

This is the whole of the topological content: what remains between it and
`IsAdicComplete (tateInvNodeChartAwayIdeal …)` is the comparison of filtrations,
`Subring.HasCofinalInducedFiltration`. -/
theorem isInducedPrecomplete_tateInvNodeChartAwaySubring
    (hcl : (tateInvNodeChartAwaySubring R I q hq hI).IsAdicallyClosed
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q))) :
    (tateInvNodeChartAwaySubring R I q hq hI).IsInducedPrecomplete
      (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) :=
  haveI _hpre : IsPrecomplete (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q))
      (awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) :=
    (isAdicRing_tateInvNodeChartAmbient R I q hI).toIsAdicComplete.toIsPrecomplete
  Subring.isInducedPrecomplete_of_isAdicallyClosed hcl

/-- **The node chart ring is `tateInvNodeChartAwayIdeal`-adically complete**, given adic
closedness and the filtration bridge. The Hausdorff half is #438's
`AlgebraicGeometry.isHausdorff_tateInvNodeChartAwayIdeal`, which needs neither hypothesis.

`tateInvNodeChartAwayIdeal` is by definition the contraction of the ambient ideal of definition,
so this is `Subring.isAdicComplete_comap_subtype` at that ideal. -/
theorem isAdicComplete_tateInvNodeChartAwayIdeal
    (hcl : (tateInvNodeChartAwaySubring R I q hq hI).IsAdicallyClosed
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)))
    (hbr : (tateInvNodeChartAwaySubring R I q hq hI).HasCofinalInducedFiltration
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q))) :
    IsAdicComplete (tateInvNodeChartAwayIdeal R I q hq hI)
      (tateInvNodeChartAwaySubring R I q hq hI) :=
  Subring.isAdicComplete_comap_subtype (isHausdorff_tateInvNodeChartAwayIdeal R I q hq hI)
    (isInducedPrecomplete_tateInvNodeChartAwaySubring R I q hq hI hcl) hbr

/-- **The same, from continuity of the four legs and the filtration bridge.** -/
theorem isAdicComplete_tateInvNodeChartAwayIdeal_of_legContinuous
    (hcont : IsTateInvNodeChartLegContinuous R I q hq hI)
    (hbr : (tateInvNodeChartAwaySubring R I q hq hI).HasCofinalInducedFiltration
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q))) :
    IsAdicComplete (tateInvNodeChartAwayIdeal R I q hq hI)
      (tateInvNodeChartAwaySubring R I q hq hI) :=
  isAdicComplete_tateInvNodeChartAwayIdeal R I q hq hI
    (isAdicallyClosed_tateInvNodeChartAwaySubring R I q hq hI hcont) hbr

end AlgebraicGeometry
