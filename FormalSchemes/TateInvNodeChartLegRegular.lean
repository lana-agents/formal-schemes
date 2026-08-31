import FormalSchemes.AwayCompletionFlat
import FormalSchemes.TateInvNodeChartBaseGenerator

set_option linter.style.header false

/-!
# The node chart's forward legs on the structural image, and left-regularity from the annulus

`FormalSchemes.TateInvNodeChartPrincipal` (issue 1284) reduces adic completeness and finite
generation of the node chart's candidate ideal of definition, over a base with `I = (t)`, to three
hypotheses. `FormalSchemes.TateInvNodeChartBaseGenerator` discharges the first of them, the
membership `hmem`. The other two are

```
hregX : IsLeftRegular (tateInvNodeChartAwayLegX R I q hq hI (algebraMap R _ t))
hregY : IsLeftRegular (tateInvNodeChartAwayLegY R I q hq hI (algebraMap R _ t))
```

and they are opaque as written: `AlgebraicGeometry.tateInvNodeChartAwayLegX` is a `.c.app` of a
chart morphism precomposed with a presheaf-section identification, so *which* element of the target
its hypothesis is about is not visible in the statement. This file makes it visible and then
discharges both from a single condition on the annulus algebra `A = R{x, y}/(x·y − q)` itself.

## What is proved

* `AlgebraicGeometry.tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX` and its `y`-side
  companion: **the forward leg on the structural image of `a : A` is the two-step completed
  localization of `a`.** Read through `AlgebraicGeometry.tateInvNodeChartTargetEquivX`, the leg
  sends `A → A{1/(x + y − 1)}` to `A → A{1/x} → A{1/x}{1/(x + y − 1)}`, both steps
  `FormalSpectrum.awayCompletionHom`. No presheaf, no glue datum and no `eqToHom` survives.
* `AlgebraicGeometry.isLeftRegular_tateInvNodeChartAwayLegX_algebraMap` and its `y`-side companion:
  **a left-regular element of `A` has left-regular image under either forward leg.** Each step of
  the tower is flat over a Noetherian base (`FormalSchemes.AwayCompletionFlat`), and a flat
  extension preserves regularity.
* `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular` and
  its two companions: **the three principal-base results of
  `FormalSchemes.TateInvNodeChartBaseGenerator` with the two leg hypotheses replaced by the single
  hypothesis `IsLeftRegular (algebraMap R (annulusAlgebra R I q) t)`.**

## What this does and does not settle

**It does not prove the hypothesis at any base with `t ≠ 0`.** `IsLeftRegular (algebraMap R A t)`
is not exhibited here at a single `(R, I, q, t)` with `t ≠ 0`, and no counterexample is given
either. What changes is *where* the question lives: it is now a statement about the image of `t` in
`R{x, y}/(x·y − q)` — one ring, one element, no completion of a localization and no chart — rather
than about an element of a twice-completed localization reached through a presheaf identification.

Two further honest limits:

* **The reduction is one-way.** Regularity in `A` implies regularity of both leg images; the
  converse is not proved and does not follow from flatness, which is not faithful here (`x` and
  `x + y − 1` both become units).
* **`t = 0` remains excluded, and for the same reason as before.** `IsLeftRegular 0` fails in any
  nonzero ring, so at `I = ⊥` the hypothesis is unsatisfiable and these results say nothing there.
  `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_bot` and
  `AlgebraicGeometry.fg_tateInvNodeChartAwayIdeal_bot`
  (`FormalSchemes.TateInvNodeChartPrincipal`) remain the only unconditional case, and they do not
  come from the principal criterion.

Nothing here is a chart: no open immersion is built, no adic structure beyond what is stated is
claimed, and nothing is said about the chart ring being nonzero, proper, or larger than the image
of the base.

## References

* [Atiyah–Macdonald, *Introduction to Commutative Algebra*], Prop. 10.14.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-! ### The two forward legs on the structural image -/

section Legs

variable [IsAdicRing (annulusIdealOfDefinition R I q)]
variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))]
variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))]

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] in
/-- **The node chart's ambient identification, inverted on the structural image.**
`AlgebraicGeometry.tateInvNodeChartAmbientEquiv` is
`FormalSpectrum.sectionsEquivOfEqBasicOpen`, which carries `FormalSpectrum.sectionsOpenHom` to
`FormalSpectrum.awayCompletionHom`
(`FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom`, in
`FormalSchemes.TateInvChartBaseImage`); this is that equation read backwards through the
isomorphism. -/
theorem tateInvNodeChartAmbientEquiv_symm_awayCompletionHom (a : annulusAlgebra R I q) :
    (tateInvNodeChartAmbientEquiv R I q hq hI).symm
        (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a) =
      sectionsOpenHom (annulusIdealOfDefinition R I q)
        (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)) a := by
  apply (tateInvNodeChartAmbientEquiv R I q hq hI).injective
  rw [RingEquiv.apply_symm_apply, tateInvNodeChartAmbientEquiv,
    FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom]

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] in
/-- **The `x`-side forward leg on the structural image, still in the presheaf spelling.**
`AlgebraicGeometry.tateInvNodeChartAwayLegX` is `AlgebraicGeometry.tateInvChartLegX` precomposed
with the ambient identification, so this is the previous theorem followed by
`AlgebraicGeometry.tateInvChartLegX_sectionsOpenHom` (`FormalSchemes.TateInvChartBaseImage`). -/
theorem tateInvNodeChartAwayLegX_awayCompletionHom (a : annulusAlgebra R I q) :
    tateInvNodeChartAwayLegX R I q hq hI
        (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a) =
      sectionsOpenHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        ((Opens.map (annulusOverlapChart R I q).base).obj
          (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)))
        (tateInvGlobalLegX a) :=
  (congrArg (tateInvChartLegX (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q))
      (tateInvNodeChartAmbientEquiv_symm_awayCompletionHom R I q hq hI a)).trans
    (tateInvChartLegX_sectionsOpenHom (isOpen_tateInvNodeChartLocus R I q) a)

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))] in
/-- **The `y`-side forward leg on the structural image, still in the presheaf spelling.** The
mirror image of `tateInvNodeChartAwayLegX_awayCompletionHom`, along
`AlgebraicGeometry.tateInvChartLegY_sectionsOpenHom`. -/
theorem tateInvNodeChartAwayLegY_awayCompletionHom (a : annulusAlgebra R I q) :
    tateInvNodeChartAwayLegY R I q hq hI
        (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a) =
      sectionsOpenHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        ((Opens.map (annulusOverlapChartY R I q).base).obj
          (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)))
        (tateInvGlobalLegY a) :=
  (congrArg (tateInvChartLegY (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q))
      (tateInvNodeChartAmbientEquiv_symm_awayCompletionHom R I q hq hI a)).trans
    (tateInvChartLegY_sectionsOpenHom (isOpen_tateInvNodeChartLocus R I q) a)

omit [TopologicalSpace R] [IsAdicRing I] [IsAdicRing (annulusIdealOfDefinition R I q)]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] in
/-- **The `x`-side target identification on the structural image.**
`AlgebraicGeometry.tateInvNodeChartTargetEquivX` is `FormalSpectrum.sectionsEquivOfEqBasicOpen` at
`AlgebraicGeometry.tateInvNodeChartTargetOpensX_eq_basicOpen`, so this is
`FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom` at the once-completed ring `A{1/x}`. -/
theorem tateInvNodeChartTargetEquivX_sectionsOpenHom
    (b : awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q)) :
    tateInvNodeChartTargetEquivX R I q hq hI
        (sectionsOpenHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
          ((Opens.map (annulusOverlapChart R I q).base).obj
            (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q))) b) =
      awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q)) b :=
  FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom _
    (tateInvNodeChartTargetOpensX_eq_basicOpen R I q hq hI) b

omit [TopologicalSpace R] [IsAdicRing I] [IsAdicRing (annulusIdealOfDefinition R I q)]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))] in
/-- **The `y`-side target identification on the structural image.** -/
theorem tateInvNodeChartTargetEquivY_sectionsOpenHom
    (b : awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q)) :
    tateInvNodeChartTargetEquivY R I q hq hI
        (sectionsOpenHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
          ((Opens.map (annulusOverlapChartY R I q).base).obj
            (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q))) b) =
      awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
          (annulusNodeChartCoord R I q)) b :=
  FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom _
    (tateInvNodeChartTargetOpensY_eq_basicOpen R I q hq hI) b

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] in
/-- **The `x`-side forward leg on the structural image is a two-step completed localization.**
Read through `AlgebraicGeometry.tateInvNodeChartTargetEquivX`, the leg carries the image of
`a : A` in `A{1/(x + y − 1)}` to its image in `A{1/x}{1/(x + y − 1)}` under the two structural maps
`FormalSpectrum.awayCompletionHom`. The inner one is `AlgebraicGeometry.tateInvGlobalLegX`, which
is that map on the nose.

**This is what makes the leg hypothesis of `FormalSchemes.TateInvNodeChartPrincipal` legible**: it
is a statement about the image of one element of `A` under a tower of two completed localizations,
with no presheaf and no chart in it. -/
theorem tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX (a : annulusAlgebra R I q) :
    tateInvNodeChartTargetEquivX R I q hq hI
        (tateInvNodeChartAwayLegX R I q hq hI
          (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a)) =
      awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q) a) :=
  (congrArg (tateInvNodeChartTargetEquivX R I q hq hI)
      (tateInvNodeChartAwayLegX_awayCompletionHom R I q hq hI a)).trans
    (tateInvNodeChartTargetEquivX_sectionsOpenHom R I q hq hI (tateInvGlobalLegX a))

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))] in
/-- **The `y`-side forward leg on the structural image is a two-step completed localization**, with
`A{1/y}` in place of `A{1/x}`. -/
theorem tateInvNodeChartTargetEquivY_tateInvNodeChartAwayLegY (a : annulusAlgebra R I q) :
    tateInvNodeChartTargetEquivY R I q hq hI
        (tateInvNodeChartAwayLegY R I q hq hI
          (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a)) =
      awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
          (annulusNodeChartCoord R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q) a) :=
  (congrArg (tateInvNodeChartTargetEquivY R I q hq hI)
      (tateInvNodeChartAwayLegY_awayCompletionHom R I q hq hI a)).trans
    (tateInvNodeChartTargetEquivY_sectionsOpenHom R I q hq hI (tateInvGlobalLegY a))

end Legs

/-! ### Left-regularity, transported from the annulus algebra -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **A left-regular element of `A` has left-regular image under the `x`-side forward leg.**
`tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX` exhibits that image as a two-step completed
localization of `a`, and each step is flat over its Noetherian source
(`FormalSpectrum.isLeftRegular_awayCompletionHom`, `FormalSchemes.AwayCompletionFlat`); the
identification back to the presheaf spelling is `FormalSpectrum.isLeftRegular_of_ringEquiv`.

`A` is Noetherian because `R` is (`RestrictedPowerSeries.instIsNoetherianRing` and a quotient), and
`A{1/x}` is then Noetherian by `FormalSpectrum.instIsNoetherianRingAwayCompletion`, which is what
lets the second step reuse the first step's lemma. -/
theorem isLeftRegular_tateInvNodeChartAwayLegX {a : annulusAlgebra R I q} (ha : IsLeftRegular a) :
    IsLeftRegular (tateInvNodeChartAwayLegX R I q hq hI
      (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a)) := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hawX : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hawY : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  refine FormalSpectrum.isLeftRegular_of_ringEquiv
    (tateInvNodeChartTargetEquivX R I q hq hI) ?_
  rw [tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX]
  exact FormalSpectrum.isLeftRegular_awayCompletionHom _ _
    (FormalSpectrum.isLeftRegular_awayCompletionHom _ _ ha)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **A left-regular element of `A` has left-regular image under the `y`-side forward leg.** -/
theorem isLeftRegular_tateInvNodeChartAwayLegY {a : annulusAlgebra R I q} (ha : IsLeftRegular a) :
    IsLeftRegular (tateInvNodeChartAwayLegY R I q hq hI
      (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a)) := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hawX : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hawY : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  refine FormalSpectrum.isLeftRegular_of_ringEquiv
    (tateInvNodeChartTargetEquivY R I q hq hI) ?_
  rw [tateInvNodeChartTargetEquivY_tateInvNodeChartAwayLegY]
  exact FormalSpectrum.isLeftRegular_awayCompletionHom _ _
    (FormalSpectrum.isLeftRegular_awayCompletionHom _ _ ha)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The structural image of `r : R` in `A{1/(x + y − 1)}` is `algebraMap R _ r`.**
`FormalSpectrum.awayCompletionHom_comp_algebraMap`, applied at `r`; the leg hypotheses of
`FormalSchemes.TateInvNodeChartPrincipal` are spelled with `algebraMap R _` and the two theorems
above with `FormalSpectrum.awayCompletionHom`, and this is the bridge. -/
theorem awayCompletionHom_algebraMap_annulusAlgebra (r : R) :
    awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)
        (algebraMap R (annulusAlgebra R I q) r) =
      algebraMap R
        (awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) r :=
  congrArg (fun φ : R →+* _ => φ r)
    (FormalSpectrum.awayCompletionHom_comp_algebraMap (R := R) (annulusNodeChartCoord R I q))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **`x`-side left-regularity, in exactly the form `FormalSchemes.TateInvNodeChartPrincipal` asks
for**: it is enough that the image of `r` in `A` be left-regular. -/
theorem isLeftRegular_tateInvNodeChartAwayLegX_algebraMap {r : R}
    (hr : IsLeftRegular (algebraMap R (annulusAlgebra R I q) r)) :
    IsLeftRegular (tateInvNodeChartAwayLegX R I q hq hI
      (algebraMap R
        (awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) r)) := by
  rw [← awayCompletionHom_algebraMap_annulusAlgebra R I q r]
  exact isLeftRegular_tateInvNodeChartAwayLegX R I q hq hI hr

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **`y`-side left-regularity, in exactly the form `FormalSchemes.TateInvNodeChartPrincipal` asks
for.** -/
theorem isLeftRegular_tateInvNodeChartAwayLegY_algebraMap {r : R}
    (hr : IsLeftRegular (algebraMap R (annulusAlgebra R I q) r)) :
    IsLeftRegular (tateInvNodeChartAwayLegY R I q hq hI
      (algebraMap R
        (awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) r)) := by
  rw [← awayCompletionHom_algebraMap_annulusAlgebra R I q r]
  exact isLeftRegular_tateInvNodeChartAwayLegY R I q hq hI hr

/-! ### The principal-base results, with one hypothesis in the annulus algebra -/

/-- **The filtration bridge over a principal base ideal, from left-regularity in `A`.**
`AlgebraicGeometry.hasCofinalInducedFiltration_tateInvNodeChartAwaySubring'` fed the two leg
regularities of the previous section.

The hypothesis is `IsLeftRegular (algebraMap R (annulusAlgebra R I q) t)` and **is not proved here
at any `t ≠ 0`**; see this file's module docstring. -/
theorem hasCofinalInducedFiltration_tateInvNodeChartAwaySubring_of_isLeftRegular (t : R)
    (ht : I = Ideal.span {t}) (hreg : IsLeftRegular (algebraMap R (annulusAlgebra R I q) t)) :
    (tateInvNodeChartAwaySubring R I q hq hI).HasCofinalInducedFiltration
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) :=
  hasCofinalInducedFiltration_tateInvNodeChartAwaySubring' R I q hq hI t ht
    (isLeftRegular_tateInvNodeChartAwayLegX_algebraMap R I q hq hI hreg)
    (isLeftRegular_tateInvNodeChartAwayLegY_algebraMap R I q hq hI hreg)

/-- **Adic completeness of the node chart ring over a principal base ideal, from left-regularity in
`A`.** `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_principal'` fed the two leg
regularities of the previous section. -/
theorem isAdicComplete_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular (t : R)
    (ht : I = Ideal.span {t}) (hreg : IsLeftRegular (algebraMap R (annulusAlgebra R I q) t)) :
    IsAdicComplete (tateInvNodeChartAwayIdeal R I q hq hI)
      (tateInvNodeChartAwaySubring R I q hq hI) :=
  isAdicComplete_tateInvNodeChartAwayIdeal_of_principal' R I q hq hI t ht
    (isLeftRegular_tateInvNodeChartAwayLegX_algebraMap R I q hq hI hreg)
    (isLeftRegular_tateInvNodeChartAwayLegY_algebraMap R I q hq hI hreg)

/-- **Finite generation of the candidate ideal of definition over a principal base ideal, from
left-regularity in `A`.** `AlgebraicGeometry.fg_tateInvNodeChartAwayIdeal_of_principal'` fed the
two leg regularities of the previous section. -/
theorem fg_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular (t : R)
    (ht : I = Ideal.span {t}) (hreg : IsLeftRegular (algebraMap R (annulusAlgebra R I q) t)) :
    (tateInvNodeChartAwayIdeal R I q hq hI).FG :=
  fg_tateInvNodeChartAwayIdeal_of_principal' R I q hq hI t ht
    (isLeftRegular_tateInvNodeChartAwayLegX_algebraMap R I q hq hI hreg)
    (isLeftRegular_tateInvNodeChartAwayLegY_algebraMap R I q hq hI hreg)

end AlgebraicGeometry
