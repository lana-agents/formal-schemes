import FormalSchemes.AdicSubringPrincipal
import FormalSchemes.TateInvNodeChartLegContinuous

set_option linter.style.header false

/-!
# The node chart ring over a principal base ideal: the filtration bridge and finite generation

`FormalSchemes.TateInvNodeChartLegContinuous` (issue 1284 goal 2) discharged leg continuity, so
`AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal'` carries exactly one hypothesis left:
`Subring.HasCofinalInducedFiltration` for the node chart ring. Finite generation of
`AlgebraicGeometry.tateInvNodeChartAwayIdeal` is a second, independent obligation.

This file reduces **both** to the same short list, over a **principal** base ideal
`I = (t)`.

## The reduction

`FormalSchemes.AdicSubringPrincipal` proves that for a subring `S ⊆ A` saturated under
multiplication by `c`, the contracted ideal of `Ideal.span {c}` is principal on `⟨c, hc⟩` — hence
finitely generated — and the filtration bridge holds. The Tate input is therefore:

1. **The ambient ideal is principal on the image of `t`.**
   `AlgebraicGeometry.awayCompletionIdeal_annulusNodeChartCoord_eq_span`, proved here with no
   hypothesis beyond `I = Ideal.span {t}`: the ideal of definition of `A{1/(x + y − 1)}` is the
   extension of `I` along `R → A → A{1/(x + y − 1)}`, and extension carries a span to a span.
2. **That image lies in the chart ring** — carried here as a hypothesis, not proved; see
   *What is not proved*.
3. **Its images under the two forward legs are left-regular** — also carried as hypotheses.
   `RingHom.mem_eqLocus_of_mul_mem` (`FormalSchemes.AdicSubringComplete`) turns them into the
   saturation of the two equalizers whose intersection the chart ring is
   (`AlgebraicGeometry.tateInvNodeChartAwaySubring_eq_inf_eqLocus`).

## Main results

* `AlgebraicGeometry.awayCompletionIdeal_annulusNodeChartCoord_eq_span` — (1), unconditional.
* `AlgebraicGeometry.mem_tateInvNodeChartAwaySubring_of_mul_mem` — the saturation of the chart
  ring from (2) and (3).
* `AlgebraicGeometry.hasCofinalInducedFiltration_tateInvNodeChartAwaySubring`,
  `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_principal` and
  `AlgebraicGeometry.fg_tateInvNodeChartAwayIdeal_of_principal` — the bridge, adic completeness
  and finite generation, each from (1)–(3).
* `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_bot` and
  `AlgebraicGeometry.fg_tateInvNodeChartAwayIdeal_bot` — **the degenerate base is
  unconditional**: over any discrete Noetherian `R`, at `I = ⊥` and `q = 0`, the node chart ring
  is adically complete for `AlgebraicGeometry.tateInvNodeChartAwayIdeal` and that ideal is
  finitely generated. Nothing is assumed beyond the instances, and the instances are inhabited —
  `R = ℤ` with the discrete topology, through
  `instIsAdicRingBotOfDiscreteTopology` (`FormalSchemes.AdicRing`, root namespace).

  **Read these two as statements about `⊥`, not about the chain.** At `I = ⊥` the contracted
  ideal *is* `⊥` (`Ideal.comap_bot_of_injective` at the injective `Subring.subtype`, on top of
  `AlgebraicGeometry.awayCompletionIdeal_annulusNodeChartCoord_bot`), and both conclusions then
  hold for **any** subring of **any** commutative ring: `IsAdicComplete ⊥ S` is a Mathlib
  instance and `(⊥ : Ideal S).FG` is `Submodule.fg_bot`. The whole content of the two results is
  therefore the identification of the ideal as `⊥`. The proofs below do route through
  `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal'`, and hence through leg continuity
  and closedness, but nothing in the conclusions depends on them — so **this is not evidence that
  the chain of this cluster composes**, and no `(R, I, q)` with `q ≠ 0` is reached here.

## What is *not* proved

* **That `algebraMap R (A{1/(x + y − 1)}) t` lies in the chart ring is no longer open.** It is
  `AlgebraicGeometry.algebraMap_mem_tateInvNodeChartAwaySubring`
  (`FormalSchemes.TateInvChartBaseImage`), for every `r : R` and with no hypothesis beyond the
  standing ones. The statements below still take it as the hypothesis `hmem`, so that they stay
  usable at a `c` other than the base generator;
  `FormalSchemes.TateInvNodeChartBaseGenerator` is where it is fed in, and
  `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_principal'` and its two
  companions there are these results without it.

  The route is the expected one — all four legs fix the image of `R` at the level of global
  sections (`AlgebraicGeometry.algebraMap_mem_tateInvGlobalSubring`), and each leg is the `.c.app`
  of a morphism of formal spectra composed with a transport, so
  `FormalSpectrum.comp_sectionsOpenHom` computes it on the image of the structural map. What
  blocked it was a **defeq between two spellings of the same section ring**
  (`FormalSpectrum.structureSheaf K` against `(FormalSpectrum.locallyRingedSpaceObj K).presheaf`).
  **That cost is the kernel's, not the elaborator's** — profiling shows the elaboration finishing
  in well under a second and `[Kernel] typechecking declarations` failing after it, which is why
  raising `maxHeartbeats` never helped. `FormalSchemes.AdicOnOpenSectionsPointwise` removes it by
  stating the reconciliation while the ring, the ideal, the morphism and the open are still
  variables, with the equation's type pinned by ascription.
* **Left-regularity is not supplied *here*.** Both hypotheses are explicit arguments of every
  statement below, and neither is shown necessary. They are discharged elsewhere:
  `FormalSchemes.TateInvNodeChartBaseRegular` reduces both to left-regularity of
  `algebraMap R (annulusAlgebra R I q) t`, and
  `AlgebraicGeometry.isLeftRegular_algebraMap_annulusAlgebra`
  (`FormalSchemes.TateAnnulusRegular`) supplies that from left-regularity of `t` in `R`, so
  `FormalSchemes.TateInvNodeChartPrincipalRegularBase` carries these results with no regularity
  hypothesis beyond `IsLeftRegular t` — at `R = ℤ⟦X⟧`, `I = (X)`, `q = t = X` with none at all. At
  `I = ⊥` the results above do not use them — the `⊥` case goes through
  `Subring.hasCofinalInducedFiltration_bot`, whose saturation-free proof exists precisely because
  the `Ideal.span {c}` criterion is vacuous at `c = 0`.
* **Nothing here is a chart.** No open immersion is constructed, `hnode` is untouched, and no
  claim is made about `AlgebraicGeometry.tateInvNodeChartAmbientHom`. Nothing here says the chart
  ring is nonzero, proper, or larger than the base — at `I = ⊥` in particular, nothing below rules
  out the chart ring being everything.
* **No `IsAdicRing` instance is produced.** `IsAdicRing` fixes a topology on the subring; the
  results here are in the `IsAdicComplete` + `FG` form, which is what this tree's consumers of an
  ideal of definition actually take.

Nothing here weakens `LocallyRingedSpace.IsProperlyDiscontinuousOn`,
`LocallyRingedSpace.IsFreeProperlyDiscontinuous` or
`LocallyRingedSpace.freeActionQuotientFormalScheme`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.4.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-!
### The ambient ideal of definition is principal when the base ideal is
-/

/-- **The ideal of definition of `A{1/(x + y − 1)}` is principal on the image of a generator of
`I`.** Three extensions compose: `I ↦ I·A` (`annulus_map_eq`), `I·A ↦ (I·A)·A{1/(x+y−1)}`
(`FormalSpectrum.map_awayCompletionHom`), and the composite is the extension along the structural
map `R → A{1/(x + y − 1)}` (`FormalSpectrum.awayCompletionHom_comp_algebraMap`). Extension carries
a span to the span of the images, so a principal `I` gives a principal ideal of definition. -/
theorem awayCompletionIdeal_annulusNodeChartCoord_eq_span (t : R) (ht : I = Ideal.span {t}) :
    awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) =
      Ideal.span {algebraMap R
        (awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) t} :=
  calc awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)
      = Ideal.map (awayCompletionHom (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q)) (annulusIdealOfDefinition R I q) :=
        (map_awayCompletionHom _ _).symm
    _ = Ideal.map (awayCompletionHom (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q)) (Ideal.map (algebraMap R (annulusAlgebra R I q)) I) :=
        congrArg _ (annulus_map_eq R I q).symm
    _ = Ideal.map ((awayCompletionHom (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q)).comp (algebraMap R (annulusAlgebra R I q))) I :=
        Ideal.map_map _ _
    _ = Ideal.map (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q))) I :=
        congrArg (fun φ : R →+* _ => Ideal.map φ I)
          (awayCompletionHom_comp_algebraMap (R := R) (annulusNodeChartCoord R I q))
    _ = Ideal.map (algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q))) (Ideal.span {t}) := congrArg _ ht
    _ = Ideal.span {algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q)) t} := by
        rw [Ideal.map_span, Set.image_singleton]

/-- **The ideal of definition of `A{1/(x + y − 1)}` is `⊥` over a base with `I = ⊥`.** The `t = 0`
case of `awayCompletionIdeal_annulusNodeChartCoord_eq_span`. -/
theorem awayCompletionIdeal_annulusNodeChartCoord_bot :
    awayCompletionIdeal (annulusIdealOfDefinition R (⊥ : Ideal R) 0)
        (annulusNodeChartCoord R (⊥ : Ideal R) 0) = ⊥ := by
  rw [awayCompletionIdeal_annulusNodeChartCoord_eq_span R ⊥ 0 0
      (Ideal.span_singleton_eq_bot.mpr rfl).symm, map_zero]
  exact Ideal.span_singleton_eq_bot.mpr rfl

variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-!
### Saturation of the chart ring, and the two consequences
-/

/-- **The chart ring is saturated under multiplication by an element with left-regular leg
images.** `RingHom.mem_inf_eqLocus_of_mul_mem` (`FormalSchemes.AdicSubringPrincipal`) at the
description `AlgebraicGeometry.tateInvNodeChartAwaySubring_eq_inf_eqLocus`. -/
theorem mem_tateInvNodeChartAwaySubring_of_mul_mem
    {c : awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)}
    (hc : c ∈ tateInvNodeChartAwaySubring R I q hq hI)
    (hregX : IsLeftRegular (tateInvNodeChartAwayLegX R I q hq hI c))
    (hregY : IsLeftRegular (tateInvNodeChartAwayLegY R I q hq hI c))
    {a : awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)}
    (hca : c * a ∈ tateInvNodeChartAwaySubring R I q hq hI) :
    a ∈ tateInvNodeChartAwaySubring R I q hq hI := by
  rw [tateInvNodeChartAwaySubring_eq_inf_eqLocus] at hc hca ⊢
  exact RingHom.mem_inf_eqLocus_of_mul_mem hc hregX hregY hca

/-- **The filtration bridge for the node chart ring over a principal base ideal.**
`Subring.hasCofinalInducedFiltration_span_singleton` at the generator supplied by
`awayCompletionIdeal_annulusNodeChartCoord_eq_span` and the saturation
`mem_tateInvNodeChartAwaySubring_of_mul_mem`.

This is the hypothesis `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal'` still
carries. -/
theorem hasCofinalInducedFiltration_tateInvNodeChartAwaySubring (t : R) (ht : I = Ideal.span {t})
    (hmem : algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) t ∈ tateInvNodeChartAwaySubring R I q hq hI)
    (hregX : IsLeftRegular (tateInvNodeChartAwayLegX R I q hq hI
      (algebraMap R _ t)))
    (hregY : IsLeftRegular (tateInvNodeChartAwayLegY R I q hq hI
      (algebraMap R _ t))) :
    (tateInvNodeChartAwaySubring R I q hq hI).HasCofinalInducedFiltration
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) := by
  rw [awayCompletionIdeal_annulusNodeChartCoord_eq_span R I q t ht]
  exact Subring.hasCofinalInducedFiltration_span_singleton hmem fun _ hca =>
    mem_tateInvNodeChartAwaySubring_of_mul_mem R I q hq hI hmem hregX hregY hca

/-- **Adic completeness of the node chart ring over a principal base ideal.**
`AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal'`
(`FormalSchemes.TateInvNodeChartLegContinuous`), whose only remaining hypothesis is the bridge. -/
theorem isAdicComplete_tateInvNodeChartAwayIdeal_of_principal (t : R) (ht : I = Ideal.span {t})
    (hmem : algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) t ∈ tateInvNodeChartAwaySubring R I q hq hI)
    (hregX : IsLeftRegular (tateInvNodeChartAwayLegX R I q hq hI (algebraMap R _ t)))
    (hregY : IsLeftRegular (tateInvNodeChartAwayLegY R I q hq hI (algebraMap R _ t))) :
    IsAdicComplete (tateInvNodeChartAwayIdeal R I q hq hI)
      (tateInvNodeChartAwaySubring R I q hq hI) :=
  isAdicComplete_tateInvNodeChartAwayIdeal' R I q hq hI
    (hasCofinalInducedFiltration_tateInvNodeChartAwaySubring R I q hq hI t ht hmem hregX hregY)

/-- **Finite generation of the candidate ideal of definition over a principal base ideal.**
`Subring.fg_comap_span_singleton` at the same generator and the same saturation: the contracted
ideal is principal on `⟨c, hmem⟩`.

Finite generation is *not* implied by completeness; this is a second consequence of the same
saturation hypothesis, and it is the other half of what makes `tateInvNodeChartAwayIdeal` an ideal
of definition in this tree's sense. -/
theorem fg_tateInvNodeChartAwayIdeal_of_principal (t : R) (ht : I = Ideal.span {t})
    (hmem : algebraMap R (awayCompletion (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) t ∈ tateInvNodeChartAwaySubring R I q hq hI)
    (hregX : IsLeftRegular (tateInvNodeChartAwayLegX R I q hq hI (algebraMap R _ t)))
    (hregY : IsLeftRegular (tateInvNodeChartAwayLegY R I q hq hI (algebraMap R _ t))) :
    (tateInvNodeChartAwayIdeal R I q hq hI).FG := by
  rw [tateInvNodeChartAwayIdeal, awayCompletionIdeal_annulusNodeChartCoord_eq_span R I q t ht]
  exact Subring.fg_comap_span_singleton hmem fun _ hca =>
    mem_tateInvNodeChartAwaySubring_of_mul_mem R I q hq hI hmem hregX hregY hca

end AlgebraicGeometry

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsAdicRing (⊥ : Ideal R)]
  [IsNoetherianRing R]

/-!
### The degenerate base, unconditionally
-/

/-- **At `I = ⊥` the filtration bridge is free**, by `Subring.hasCofinalInducedFiltration_bot`:
the ambient ideal of definition is `⊥` (`awayCompletionIdeal_annulusNodeChartCoord_bot`), and both
filtrations then collapse. No regularity and no membership hypothesis is used. -/
theorem hasCofinalInducedFiltration_tateInvNodeChartAwaySubring_bot :
    (tateInvNodeChartAwaySubring R ⊥ 0 (Submodule.zero_mem _) Submodule.fg_bot
      ).HasCofinalInducedFiltration
      (awayCompletionIdeal (annulusIdealOfDefinition R (⊥ : Ideal R) 0)
        (annulusNodeChartCoord R (⊥ : Ideal R) 0)) := by
  rw [awayCompletionIdeal_annulusNodeChartCoord_bot R]
  exact Subring.hasCofinalInducedFiltration_bot _

/-- **The node chart ring is adically complete over a discrete Noetherian base at `I = ⊥`,
unconditionally.** Leg continuity (`AlgebraicGeometry.isTateInvNodeChartLegContinuous_tateInv`)
and closedness are already unconditional; this supplies the last hypothesis.

**It is a statement about `⊥`, not about the node chart.** At `I = ⊥` the ideal
`AlgebraicGeometry.tateInvNodeChartAwayIdeal` is `⊥` — that is
`AlgebraicGeometry.awayCompletionIdeal_annulusNodeChartCoord_bot` followed by
`Ideal.comap_bot_of_injective` — and `IsAdicComplete ⊥ S` is a Mathlib instance for every
commutative ring `S`. So the conclusion holds for any subring of any ring once the ideal is known
to be `⊥`, and that identification is the whole content. The proof below goes through
`AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal'`, and so through leg continuity and
closedness, but the statement does not need them: this **does not** exhibit an `(R, I, q)` at
which the chain of this cluster is tested. It also says nothing about a base with `q ≠ 0` — at
`I = ⊥` the Tate parameter is `0` and the annulus is `R[x, y]/(x·y)`. -/
theorem isAdicComplete_tateInvNodeChartAwayIdeal_bot :
    IsAdicComplete
      (tateInvNodeChartAwayIdeal R ⊥ 0 (Submodule.zero_mem _) Submodule.fg_bot)
      (tateInvNodeChartAwaySubring R ⊥ 0 (Submodule.zero_mem _) Submodule.fg_bot) :=
  isAdicComplete_tateInvNodeChartAwayIdeal' R ⊥ 0 (Submodule.zero_mem _) Submodule.fg_bot
    (hasCofinalInducedFiltration_tateInvNodeChartAwaySubring_bot R)

/-- **The candidate ideal of definition is `⊥`, hence finitely generated, at `I = ⊥`.** The
companion of `isAdicComplete_tateInvNodeChartAwayIdeal_bot`: completeness does not imply finite
generation, and both are needed for an ideal of definition. As there, the content is the
identification of the ideal as `⊥`; `Submodule.fg_bot` then applies to any ring, so this says
nothing specific to the node chart beyond that identification. -/
theorem fg_tateInvNodeChartAwayIdeal_bot :
    (tateInvNodeChartAwayIdeal R ⊥ 0 (Submodule.zero_mem _) Submodule.fg_bot).FG := by
  rw [tateInvNodeChartAwayIdeal, awayCompletionIdeal_annulusNodeChartCoord_bot R,
    Ideal.comap_bot_of_injective
      (tateInvNodeChartAwaySubring R ⊥ 0 (Submodule.zero_mem _) Submodule.fg_bot).subtype
      (Subring.subtype_injective _)]
  exact Submodule.fg_bot

end AlgebraicGeometry
