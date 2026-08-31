import FormalSchemes.AwayCompletionRegular
import FormalSchemes.RegularMulEquiv
import FormalSchemes.TateInvNodeChartBaseGenerator

set_option linter.style.header false

/-!
# The node chart's two forward legs on the base generator, with the presheaf removed

`FormalSchemes.TateInvNodeChartPrincipal` reduces adic completeness and finite generation of the
node chart's candidate ideal of definition, over a base with `I = Ideal.span {t}`, to three
hypotheses. `FormalSchemes.TateInvChartBaseImage` discharged the first of them
(`AlgebraicGeometry.algebraMap_mem_tateInvNodeChartAwaySubring`) and
`FormalSchemes.TateInvNodeChartBaseGenerator` fed it in. The other two are left-regularity of

```
tateInvNodeChartAwayLegX R I q hq hI (algebraMap R _ t)
tateInvNodeChartAwayLegY R I q hq hI (algebraMap R _ t)
```

and they are the reason those results are still conditional.

**This file does not prove them. It removes the presheaf from their statement**, which is what
makes them attackable at all.

## Why the statement had to move

`AlgebraicGeometry.tateInvNodeChartAwayLegX` lands in `AlgebraicGeometry.tateInvNodeChartTargetX`,
which is a **presheaf section ring** —
`((locallyRingedSpaceObj (awayCompletionIdeal …)).presheaf.obj (op …) : Type u)`. `IsLeftRegular`
in such a ring is not something a commutative-algebra argument can reach: its elements have no
normal form and no hypothesis on `R` bears on them.
`AlgebraicGeometry.tateInvNodeChartTargetEquivX` identifies that ring with

```
awayCompletion (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
  (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
    (annulusNodeChartCoord R I q))
```

i.e. with `A{1/x}{1/(x + y − 1)}` for `A = R{x, y}/(x·y − q)` — a completion of a localization of a
ring, where flatness and torsion-freeness *are* available.

## What is proved

* `AlgebraicGeometry.tateInvGlobalLegX_algebraMap` and its `Y` companion — the two global chart
  legs are `R`-algebra maps. This computation is already inside
  `AlgebraicGeometry.algebraMap_mem_tateInvGlobalSubring`'s proof
  (`FormalSchemes.TateInvGlobalSections`) as its `hx`/`hy`; it is named here because two proofs
  below want it as a rewrite rather than as a step.
* `AlgebraicGeometry.tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX_algebraMap` and its `Y`
  companion — **the two forward legs carry the base image to the base image**:

  ```
  tateInvNodeChartTargetEquivX R I q hq hI (tateInvNodeChartAwayLegX R I q hq hI (algebraMap R _ r))
    = algebraMap R (A{1/x}{1/(x + y − 1)}) r
  ```

  for every `r : R`, with no hypothesis beyond the standing ones.
* `AlgebraicGeometry.isLeftRegular_tateInvNodeChartAwayLegX_algebraMap_iff` and its `Y` companion —
  the same statement in the form the consumers want: left-regularity of the leg image **is**
  left-regularity of `algebraMap R (A{1/x}{1/(x + y − 1)}) t`, with no presheaf, no `Opens`, no
  `eqToHom` and no glue datum in it.
* `AlgebraicGeometry.hasCofinalInducedFiltration_tateInvNodeChartAwaySubring''`,
  `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_principal''` and
  `AlgebraicGeometry.fg_tateInvNodeChartAwayIdeal_of_principal''` — the three results of
  `FormalSchemes.TateInvNodeChartBaseGenerator` with their two remaining hypotheses restated in the
  presheaf-free form.
* `AlgebraicGeometry.isLeftRegular_algebraMap_awayCompletion_overlapX` and its `Y` mirror —
  regularity of the base generator **in `A` itself** implies both of those, because a completed
  localization of a Noetherian ring is flat over it.
* `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular` and
  its two companions — the same three results carrying **one** hypothesis, about `A` alone.

## What the obstruction has become, exactly

**One statement about `A`, with no completion, no localization and no presheaf in it:**

> is `algebraMap R (annulusAlgebra R I q) t` left-regular — i.e. is the base generator a
> nonzerodivisor in `A = R{x, y}/(x·y − q)`?

`AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular` and its
two companions are #445's three principal-base results carrying exactly that hypothesis and nothing
else. The reduction is `AlgebraicGeometry.isLeftRegular_algebraMap_awayCompletion_overlapX` and its
`Y` mirror: regularity **rises** along `A → A{1/x} → A{1/x}{1/(x + y − 1)}` because a localization
is flat and an adic completion of a Noetherian ring is flat over it
(`FormalSpectrum.isLeftRegular_algebraMap_awayCompletion`,
`FormalSchemes.AwayCompletionRegular`), and `A` is Noetherian because
`RestrictedPowerSeries.instIsNoetherianRing` is.

Only the *rising* direction is available, and that is the direction needed: nothing here says the
converse, and an element can become regular in a localization without being regular downstairs.

**No `(R, I, q, t)` with `t ≠ 0` at which the regularity holds is exhibited here, and no
counterexample either.** At `t = 0` the hypothesis is unsatisfiable in a nonzero ring, and `I = ⊥`
remains the only unconditional case, through
`AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_bot` rather than through the principal
criterion. What is gained is that the question is now about one explicit quotient of a restricted
power series ring, where `R`-level hypotheses — `R` a domain, `R` `t`-torsion-free — can bear on it
at all.

## What is *not* touched

Nothing here is a chart: no adic structure on the node chart ring beyond what
`FormalSchemes.TateInvNodeChartComplete` already proves, and no open immersion. The `hmem`
hypothesis stays in `FormalSchemes.TateInvNodeChartPrincipal`'s signatures, where #446 deliberately
left it so those results remain usable at a `c` other than the base generator.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-! ### The global legs on the base image -/

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The `x`-chart global leg is an `R`-algebra map.** `AlgebraicGeometry.tateInvGlobalLegX` is
`FormalSpectrum.awayCompletionHom` by definition, so this is
`FormalSpectrum.awayCompletionHom_comp_algebraMap` read at `r`. -/
theorem tateInvGlobalLegX_algebraMap (r : R) :
    tateInvGlobalLegX (algebraMap R (annulusAlgebra R I q) r) =
      algebraMap R (awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q)) r :=
  congrArg (fun φ : R →+* _ => φ r)
    (FormalSpectrum.awayCompletionHom_comp_algebraMap (R := R) (overlapX R I q))

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The `y`-chart global leg is an `R`-algebra map.** -/
theorem tateInvGlobalLegY_algebraMap (r : R) :
    tateInvGlobalLegY (algebraMap R (annulusAlgebra R I q) r) =
      algebraMap R (awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q)) r :=
  congrArg (fun φ : R →+* _ => φ r)
    (FormalSpectrum.awayCompletionHom_comp_algebraMap (R := R) (overlapY R I q))

/-! ### The two forward legs on the base image -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `x`-side forward leg carries the base image to the base image.** Read through
`AlgebraicGeometry.tateInvNodeChartTargetEquivX`, the leg image of `algebraMap R _ r` is
`algebraMap R (A{1/x}{1/(x + y − 1)}) r`.

The chain is: the leg is `AlgebraicGeometry.tateInvChartLegX` after
`(tateInvNodeChartAmbientEquiv R I q hq hI).symm` by definition;
`AlgebraicGeometry.tateInvNodeChartAmbientEquiv_sectionsOpenHom_algebraMap` puts that inverse image
in `FormalSpectrum.sectionsOpenHom` form; `AlgebraicGeometry.tateInvChartLegX_sectionsOpenHom`
computes the leg there; `FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom` evaluates the
target identification, which is a `FormalSpectrum.sectionsEquivOfEqBasicOpen` at
`AlgebraicGeometry.tateInvNodeChartTargetOpensX_eq_basicOpen`; and `tateInvGlobalLegX_algebraMap`
with `FormalSpectrum.awayCompletionHom_comp_algebraMap` finish in the ring.

Written as a `.trans` chain rather than with `rw`: the sides of these equations differ only in
instance arguments, where `rw` hits a `(deterministic) timeout at isDefEq`. See
`FormalSchemes.AdicOnOpenSectionsPointwise` for the measurement behind that. -/
theorem tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX_algebraMap (r : R) :
    tateInvNodeChartTargetEquivX R I q hq hI
        (tateInvNodeChartAwayLegX R I q hq hI
          (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q)) r)) =
      algebraMap R (awayCompletion (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (overlapX R I q)) (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q))) r := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hawX : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  have hsym : (tateInvNodeChartAmbientEquiv R I q hq hI).symm
      (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) r) =
      sectionsOpenHom (annulusIdealOfDefinition R I q)
        (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q))
        (algebraMap R (annulusAlgebra R I q) r) :=
    (RingEquiv.symm_apply_eq _).2
      (tateInvNodeChartAmbientEquiv_sectionsOpenHom_algebraMap (hq := hq) (hI := hI) r).symm
  have hlegdef : tateInvNodeChartAwayLegX R I q hq hI
      (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) r) =
      tateInvChartLegX (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q)
        ((tateInvNodeChartAmbientEquiv R I q hq hI).symm
          (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q)) r)) := rfl
  have hleg := (hlegdef.trans (congrArg
      (⇑(tateInvChartLegX (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q))) hsym)).trans
    (tateInvChartLegX_sectionsOpenHom (hq := hq) (hI := hI)
      (isOpen_tateInvNodeChartLocus R I q) (algebraMap R (annulusAlgebra R I q) r))
  have hlast : awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (overlapX R I q)) (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q))
        (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q)) r) =
      algebraMap R (awayCompletion (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (overlapX R I q)) (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q))) r :=
    congrArg (fun φ : R →+* _ => φ r)
      (FormalSpectrum.awayCompletionHom_comp_algebraMap
        (R := R) (A := awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q))
        (L := awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q)))
  exact (congrArg (⇑(tateInvNodeChartTargetEquivX R I q hq hI)) hleg).trans
    ((FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom _
        (tateInvNodeChartTargetOpensX_eq_basicOpen R I q hq hI) _).trans
      ((congrArg (⇑(awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q)
          (overlapX R I q)) (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
            (annulusNodeChartCoord R I q)))) (tateInvGlobalLegX_algebraMap R I q r)).trans
        hlast))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `y`-side forward leg carries the base image to the base image.** The mirror of
`tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX_algebraMap`, along
`AlgebraicGeometry.tateInvChartLegY_sectionsOpenHom`,
`AlgebraicGeometry.tateInvNodeChartTargetOpensY_eq_basicOpen` and `tateInvGlobalLegY_algebraMap`. -/
theorem tateInvNodeChartTargetEquivY_tateInvNodeChartAwayLegY_algebraMap (r : R) :
    tateInvNodeChartTargetEquivY R I q hq hI
        (tateInvNodeChartAwayLegY R I q hq hI
          (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q)) r)) =
      algebraMap R (awayCompletion (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (overlapY R I q)) (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
          (annulusNodeChartCoord R I q))) r := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hawY : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  have hsym : (tateInvNodeChartAmbientEquiv R I q hq hI).symm
      (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) r) =
      sectionsOpenHom (annulusIdealOfDefinition R I q)
        (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q))
        (algebraMap R (annulusAlgebra R I q) r) :=
    (RingEquiv.symm_apply_eq _).2
      (tateInvNodeChartAmbientEquiv_sectionsOpenHom_algebraMap (hq := hq) (hI := hI) r).symm
  have hlegdef : tateInvNodeChartAwayLegY R I q hq hI
      (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) r) =
      tateInvChartLegY (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q)
        ((tateInvNodeChartAmbientEquiv R I q hq hI).symm
          (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q)) r)) := rfl
  have hleg := (hlegdef.trans (congrArg
      (⇑(tateInvChartLegY (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q))) hsym)).trans
    (tateInvChartLegY_sectionsOpenHom (hq := hq) (hI := hI)
      (isOpen_tateInvNodeChartLocus R I q) (algebraMap R (annulusAlgebra R I q) r))
  have hlast : awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (overlapY R I q)) (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
          (annulusNodeChartCoord R I q))
        (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q)) r) =
      algebraMap R (awayCompletion (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (overlapY R I q)) (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
          (annulusNodeChartCoord R I q))) r :=
    congrArg (fun φ : R →+* _ => φ r)
      (FormalSpectrum.awayCompletionHom_comp_algebraMap
        (R := R) (A := awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q))
        (L := awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
          (annulusNodeChartCoord R I q)))
  exact (congrArg (⇑(tateInvNodeChartTargetEquivY R I q hq hI)) hleg).trans
    ((FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom _
        (tateInvNodeChartTargetOpensY_eq_basicOpen R I q hq hI) _).trans
      ((congrArg (⇑(awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q)
          (overlapY R I q)) (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
            (annulusNodeChartCoord R I q)))) (tateInvGlobalLegY_algebraMap R I q r)).trans
        hlast))

/-! ### Left-regularity, transported off the presheaf -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Left-regularity of the `x`-side leg image is left-regularity in `A{1/x}{1/(x + y − 1)}`.**
`AlgebraicGeometry.tateInvNodeChartTargetEquivX` is a `RingEquiv`, hence a `MulEquiv`, and
`MulEquiv.isLeftRegular_apply_iff` transports the property across it; the leg image is computed by
`tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX_algebraMap`.

This is the statement of one half of the node chart's remaining obstruction with no presheaf in
it. -/
theorem isLeftRegular_tateInvNodeChartAwayLegX_algebraMap_iff (t : R) :
    IsLeftRegular (tateInvNodeChartAwayLegX R I q hq hI
        (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q)) t)) ↔
      IsLeftRegular (algebraMap R (awayCompletion
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q))) t) :=
  ((tateInvNodeChartTargetEquivX R I q hq hI).toMulEquiv.isLeftRegular_apply_iff).symm.trans
    (iff_of_eq (congrArg IsLeftRegular
      (tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX_algebraMap R I q hq hI t)))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Left-regularity of the `y`-side leg image is left-regularity in `A{1/y}{1/(x + y − 1)}`.** -/
theorem isLeftRegular_tateInvNodeChartAwayLegY_algebraMap_iff (t : R) :
    IsLeftRegular (tateInvNodeChartAwayLegY R I q hq hI
        (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q)) t)) ↔
      IsLeftRegular (algebraMap R (awayCompletion
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
          (annulusNodeChartCoord R I q))) t) :=
  ((tateInvNodeChartTargetEquivY R I q hq hI).toMulEquiv.isLeftRegular_apply_iff).symm.trans
    (iff_of_eq (congrArg IsLeftRegular
      (tateInvNodeChartTargetEquivY_tateInvNodeChartAwayLegY_algebraMap R I q hq hI t)))

/-! ### The principal-base results with presheaf-free hypotheses -/

/-- **The filtration bridge over a principal base ideal, with both hypotheses presheaf-free.**
`AlgebraicGeometry.hasCofinalInducedFiltration_tateInvNodeChartAwaySubring'` with its two
`IsLeftRegular` hypotheses rewritten by
`isLeftRegular_tateInvNodeChartAwayLegX_algebraMap_iff` and its `Y` companion. -/
theorem hasCofinalInducedFiltration_tateInvNodeChartAwaySubring'' (t : R)
    (ht : I = Ideal.span {t})
    (hregX : IsLeftRegular (algebraMap R (awayCompletion
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
        (annulusNodeChartCoord R I q))) t))
    (hregY : IsLeftRegular (algebraMap R (awayCompletion
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
        (annulusNodeChartCoord R I q))) t)) :
    (tateInvNodeChartAwaySubring R I q hq hI).HasCofinalInducedFiltration
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) :=
  hasCofinalInducedFiltration_tateInvNodeChartAwaySubring' R I q hq hI t ht
    ((isLeftRegular_tateInvNodeChartAwayLegX_algebraMap_iff R I q hq hI t).2 hregX)
    ((isLeftRegular_tateInvNodeChartAwayLegY_algebraMap_iff R I q hq hI t).2 hregY)

/-- **Adic completeness of the node chart ring over a principal base ideal, with both hypotheses
presheaf-free.** -/
theorem isAdicComplete_tateInvNodeChartAwayIdeal_of_principal'' (t : R) (ht : I = Ideal.span {t})
    (hregX : IsLeftRegular (algebraMap R (awayCompletion
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
        (annulusNodeChartCoord R I q))) t))
    (hregY : IsLeftRegular (algebraMap R (awayCompletion
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
        (annulusNodeChartCoord R I q))) t)) :
    IsAdicComplete (tateInvNodeChartAwayIdeal R I q hq hI)
      (tateInvNodeChartAwaySubring R I q hq hI) :=
  isAdicComplete_tateInvNodeChartAwayIdeal_of_principal' R I q hq hI t ht
    ((isLeftRegular_tateInvNodeChartAwayLegX_algebraMap_iff R I q hq hI t).2 hregX)
    ((isLeftRegular_tateInvNodeChartAwayLegY_algebraMap_iff R I q hq hI t).2 hregY)

/-- **Finite generation of the candidate ideal of definition over a principal base ideal, with both
hypotheses presheaf-free.** -/
theorem fg_tateInvNodeChartAwayIdeal_of_principal'' (t : R) (ht : I = Ideal.span {t})
    (hregX : IsLeftRegular (algebraMap R (awayCompletion
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
        (annulusNodeChartCoord R I q))) t))
    (hregY : IsLeftRegular (algebraMap R (awayCompletion
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
        (annulusNodeChartCoord R I q))) t)) :
    (tateInvNodeChartAwayIdeal R I q hq hI).FG :=
  fg_tateInvNodeChartAwayIdeal_of_principal' R I q hq hI t ht
    ((isLeftRegular_tateInvNodeChartAwayLegX_algebraMap_iff R I q hq hI t).2 hregX)
    ((isLeftRegular_tateInvNodeChartAwayLegY_algebraMap_iff R I q hq hI t).2 hregY)

/-! ### The obstruction, reduced to the annulus algebra -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Left-regularity in `A` rises to `A{1/x}{1/(x + y − 1)}`.**
`FormalSpectrum.isLeftRegular_algebraMap_awayCompletion` applied twice — once at
`overlapX` (root namespace) and once at `AlgebraicGeometry.annulusNodeChartCoord` — with
`FormalSpectrum.isNoetherianRing_awayCompletion` supplying the Noetherianity the second application
needs, and `IsScalarTower.algebraMap_apply` composing the three structural maps.

`annulusAlgebra R I q` is Noetherian because it is a quotient of `RestrictedPowerSeries`, which is
(`RestrictedPowerSeries.instIsNoetherianRing`). -/
theorem isLeftRegular_algebraMap_awayCompletion_overlapX (t : R)
    (ht : IsLeftRegular (algebraMap R (annulusAlgebra R I q) t)) :
    IsLeftRegular (algebraMap R (awayCompletion
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
        (annulusNodeChartCoord R I q))) t) := by
  haveI : IsNoetherianRing (awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q)) :=
    FormalSpectrum.isNoetherianRing_awayCompletion _ _
  have h1 : IsLeftRegular (algebraMap (annulusAlgebra R I q)
      (awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q))
      (algebraMap R (annulusAlgebra R I q) t)) :=
    FormalSpectrum.isLeftRegular_algebraMap_awayCompletion _ _ ht
  rw [← IsScalarTower.algebraMap_apply] at h1
  have h2 := FormalSpectrum.isLeftRegular_algebraMap_awayCompletion
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
    (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
      (annulusNodeChartCoord R I q)) h1
  rw [← IsScalarTower.algebraMap_apply] at h2
  exact h2

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Left-regularity in `A` rises to `A{1/y}{1/(x + y − 1)}`**, the mirror of
`isLeftRegular_algebraMap_awayCompletion_overlapX` at `overlapY` (root namespace). -/
theorem isLeftRegular_algebraMap_awayCompletion_overlapY (t : R)
    (ht : IsLeftRegular (algebraMap R (annulusAlgebra R I q) t)) :
    IsLeftRegular (algebraMap R (awayCompletion
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
        (annulusNodeChartCoord R I q))) t) := by
  haveI : IsNoetherianRing (awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q)) :=
    FormalSpectrum.isNoetherianRing_awayCompletion _ _
  have h1 : IsLeftRegular (algebraMap (annulusAlgebra R I q)
      (awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q))
      (algebraMap R (annulusAlgebra R I q) t)) :=
    FormalSpectrum.isLeftRegular_algebraMap_awayCompletion _ _ ht
  rw [← IsScalarTower.algebraMap_apply] at h1
  have h2 := FormalSpectrum.isLeftRegular_algebraMap_awayCompletion
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
    (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
      (annulusNodeChartCoord R I q)) h1
  rw [← IsScalarTower.algebraMap_apply] at h2
  exact h2

/-! ### The principal-base results, on one hypothesis about `A` -/

/-- **The filtration bridge over a principal base ideal, on one hypothesis about `A`.**
Both left-regularity hypotheses of
`hasCofinalInducedFiltration_tateInvNodeChartAwaySubring''` follow from left-regularity of
`algebraMap R (annulusAlgebra R I q) t`, by
`isLeftRegular_algebraMap_awayCompletion_overlapX` and its `Y` mirror. -/
theorem hasCofinalInducedFiltration_tateInvNodeChartAwaySubring_of_isLeftRegular (t : R)
    (ht : I = Ideal.span {t})
    (hreg : IsLeftRegular (algebraMap R (annulusAlgebra R I q) t)) :
    (tateInvNodeChartAwaySubring R I q hq hI).HasCofinalInducedFiltration
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) :=
  hasCofinalInducedFiltration_tateInvNodeChartAwaySubring'' R I q hq hI t ht
    (isLeftRegular_algebraMap_awayCompletion_overlapX R I q t hreg)
    (isLeftRegular_algebraMap_awayCompletion_overlapY R I q t hreg)

/-- **Adic completeness of the node chart ring over a principal base ideal, on one hypothesis about
`A`.** The node chart's candidate ring is a complete adic ring as soon as the base generator is a
nonzerodivisor in `A = R{x, y}/(x·y − q)`.

This is the whole of #445's obstruction (b), reduced: no presheaf, no completion and no
localization occurs in `hreg`. -/
theorem isAdicComplete_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular (t : R)
    (ht : I = Ideal.span {t})
    (hreg : IsLeftRegular (algebraMap R (annulusAlgebra R I q) t)) :
    IsAdicComplete (tateInvNodeChartAwayIdeal R I q hq hI)
      (tateInvNodeChartAwaySubring R I q hq hI) :=
  isAdicComplete_tateInvNodeChartAwayIdeal_of_principal'' R I q hq hI t ht
    (isLeftRegular_algebraMap_awayCompletion_overlapX R I q t hreg)
    (isLeftRegular_algebraMap_awayCompletion_overlapY R I q t hreg)

/-- **Finite generation of the candidate ideal of definition over a principal base ideal, on one
hypothesis about `A`.** Finite generation is not implied by completeness; this is the second
consequence of the same reduction. -/
theorem fg_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular (t : R)
    (ht : I = Ideal.span {t})
    (hreg : IsLeftRegular (algebraMap R (annulusAlgebra R I q) t)) :
    (tateInvNodeChartAwayIdeal R I q hq hI).FG :=
  fg_tateInvNodeChartAwayIdeal_of_principal'' R I q hq hI t ht
    (isLeftRegular_algebraMap_awayCompletion_overlapX R I q t hreg)
    (isLeftRegular_algebraMap_awayCompletion_overlapY R I q t hreg)

end AlgebraicGeometry
