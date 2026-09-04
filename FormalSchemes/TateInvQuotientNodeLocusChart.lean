import FormalSchemes.TateInvPeriodQuotientCharts
import FormalSchemes.TateInvQuotientColimitTarget

set_option linter.style.header false

/-!
# `T_inv/⟨σ⟩` is a formal scheme **iff** it has a chart at the node-locus image

Row 1197's residue is one morphism. Its sharpest recorded form,
`AlgebraicGeometry.exists_formalScheme_of_openImmersion_spf_quotientIdeal_of_isLeftRegular_base`
(`FormalSchemes.TateInvNodeChartQuotientSpf`), asks for an open immersion out of `Spf` of **one
named ring**, and to make that ring adic at all it carries three hypotheses the question itself
does not mention: a generator `t` of `I`, `ht : I = Ideal.span {t}` and `hreg : IsLeftRegular t`,
and through them the completeness and finite-generation chain of
`FormalSchemes.TateInvNodeChartPrincipalRegularBase`.

This file removes all three, and turns the reduction into an equivalence.

## What is here

`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart`
(`FormalSchemes.TateInvPeriodQuotientCharts`) states the reduction in the *model patch's*
coordinates: a chart at `π (ι ⟨0⟩ y)` for every `y` of `Spf A` outside the ranges of the two
overlap charts. `AlgebraicGeometry.hasAffineChartAt_or_mem_image_base_tateInvSaturate_compl`
(`FormalSchemes.TateInvSaturation`) already performs its case analysis once, as a dichotomy on the
quotient's own points. Reading that dichotomy as an implication gives

* `AlgebraicGeometry.hasAffineChartAt_of_nodeLocus` and its `Iff` form
  `AlgebraicGeometry.forall_hasAffineChartAt_iff_nodeLocus`;
* `AlgebraicGeometry.exists_formalScheme_iff_hasAffineChartAt_nodeLocus` — **the headline**, through
  the general `LocallyRingedSpace.exists_formalScheme_iff_forall_hasAffineChartAt`. So issue 69's
  question for the period-`q` quotient *is* a question about the image of
  `AlgebraicGeometry.tateInvNodeLocus`, in both directions and with no residue elsewhere.

`LocallyRingedSpace.HasAffineChartAt` is by definition an open immersion out of `Spf` of **some**
adic ring, so feeding the equivalence costs nothing beyond producing one:

* `AlgebraicGeometry.exists_formalScheme_of_isOpenImmersion_of_nodeLocus_subset` — an open
  immersion `Spf L ⟶ T_inv/⟨σ⟩` at an *arbitrary* adic `(C, L)` whose range contains that image;
* `AlgebraicGeometry.exists_formalScheme_of_hasAffineChartAt_restrict_of_nodeLocus_subset` — or a
  chart at every point of **any** open containing it, through
  `LocallyRingedSpace.hasAffineChartAt_of_restrict`. The open need not be affine, which is the
  `HasAffineChartAt` analogue of what
  `AlgebraicGeometry.isThickeningColimitTarget_iff_restrict_of_nodeLocus_subset`
  (`FormalSchemes.TateInvQuotientColimitTarget`) does for the colimit property;
* `AlgebraicGeometry.exists_formalScheme_of_isoRestrict_of_nodeLocus_subset` — the affine case of
  the previous one, through `LocallyRingedSpace.hasAffineChartAt_of_isoRestrict`;
* `AlgebraicGeometry.exists_formalScheme_actionQuotient_of_isoRestrict_nodeChart` and
  `AlgebraicGeometry.exists_formalScheme_actionQuotient_of_exists_openImmersion_nodeChart`, the two
  at the named node-chart open `AlgebraicGeometry.tateInvNodeChartQuotientOpens`.

The last of those is
`exists_formalScheme_of_openImmersion_spf_quotientIdeal_of_isLeftRegular_base` with `t`, `ht` and
`hreg` deleted and the ring left free: its range hypothesis is that one's, verbatim, and its
conclusion is that one's. So those three were never hypotheses of the reduction — they were the
price of insisting the chart's ring be `Γ (T_inv/⟨σ⟩, V)` rather than any ring at all.

## What this does **not** settle

**`hnode` is still open.** Nothing here produces a chart, an open immersion or an isomorphism; the
node-locus image is exactly where the tree has no chart and, by
`AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction`
(`FormalSchemes.TateInvPeriodNodePoint`), cannot get one from a separating open. What the
equivalence adds is that a successor may pick **any** ring and **any** open containing that image,
and owes no completeness, finite-generation or regularity statement about
`AlgebraicGeometry.tateInvNodeChartAwaySubring` on the way.

Nor is the node-locus image small: `AlgebraicGeometry.tateInvNodeLocus` is a homeomorphic copy of
`Spf R` (`AlgebraicGeometry.tateInvNodeLocusHomeomorph`, `FormalSchemes.TateInvNodeLocus`), not a
point, and `AlgebraicGeometry.image_base_tateInvSaturate_nodeLocus_nonempty` records that for
`I ≠ ⊤` the right-hand side of the equivalence quantifies over a nonempty set — so the equivalence
does not hold because there is nothing to check.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron 1-gon.
-/

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

open FormalSpectrum LocallyRingedSpace

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

variable {R I q}
variable {Q : LocallyRingedSpace.{u}}
variable {π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q}

/-! ### The reduction, on the quotient's own points -/

/-- **A chart at every point of the node-locus image is a chart everywhere.**
`AlgebraicGeometry.hasAffineChartAt_or_mem_image_base_tateInvSaturate_compl` already says every
point of the quotient either carries a chart or lies in that image, and
`AlgebraicGeometry.tateInvNodeLocus` is by definition the complement of
`AlgebraicGeometry.tateInvChartLocus`; so this is that dichotomy with its second alternative
discharged.

It is `AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart` with the hypothesis moved
off the model patch, and it is weaker than
`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChartLocus`
(`FormalSchemes.TateInvNodeChartDomain`), which asks for charts on the image of the saturation of
the whole of `D(x + y − 1)` rather than of the node locus inside it. -/
theorem hasAffineChartAt_of_nodeLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (hnode : ∀ z ∈ ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q),
      HasAffineChartAt Q z) (z : Q) : HasAffineChartAt Q z :=
  (hasAffineChartAt_or_mem_image_base_tateInvSaturate_compl hq hI h z).elim id (hnode z)

/-- **So having a chart everywhere is having one on the node-locus image.** The forward direction
is a restriction of the quantifier; the content is `hasAffineChartAt_of_nodeLocus`. -/
theorem forall_hasAffineChartAt_iff_nodeLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    (∀ z : Q, HasAffineChartAt Q z) ↔
      ∀ z ∈ ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q),
        HasAffineChartAt Q z :=
  ⟨fun H z _ => H z, hasAffineChartAt_of_nodeLocus hq hI h⟩

/-- **The headline: `T_inv/⟨σ⟩` is a formal scheme exactly when it has an affine formal chart at
every point of the node-locus image.**

`LocallyRingedSpace.exists_formalScheme_iff_forall_hasAffineChartAt`
(`FormalSchemes.ActionQuotientChartAt`) turns the pointwise criterion into a statement about the
object; `forall_hasAffineChartAt_iff_nodeLocus` cuts the quantifier down to the node locus. Being
an equivalence rather than a one-way reduction is what says issue 69's question for the period-`q`
quotient carries no residue away from there. -/
theorem exists_formalScheme_iff_hasAffineChartAt_nodeLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    (∃ X : FormalScheme.{u}, X.toLocallyRingedSpace = Q) ↔
      ∀ z ∈ ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q),
        HasAffineChartAt Q z :=
  (exists_formalScheme_iff_forall_hasAffineChartAt Q).trans
    (forall_hasAffineChartAt_iff_nodeLocus hq hI h)

/-! ### Feeding the equivalence: any ring, any open -/

/-- **An open immersion out of `Spf` of an arbitrary adic ring, covering the node-locus image, is
enough.** `LocallyRingedSpace.HasAffineChartAt` *is* the statement that a point lies in the range
of such an open immersion, so this is the equivalence with its right-hand side read off.

Compare
`AlgebraicGeometry.exists_formalScheme_of_openImmersion_spf_quotientIdeal_of_isLeftRegular_base`
(`FormalSchemes.TateInvNodeChartQuotientSpf`): the same conclusion from the same kind of datum, but
there the ring is fixed to the carrier of `AlgebraicGeometry.tateInvNodeChartQuotientIdeal`, and
the statement therefore carries `t`, `ht : I = Ideal.span {t}` and `hreg : IsLeftRegular t` solely
to make that ring adic. Here there is nothing to make adic. -/
theorem exists_formalScheme_of_isOpenImmersion_of_nodeLocus_subset
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    {C : Type u} [CommRing C] [TopologicalSpace C] (L : Ideal C) [IsAdicRing L]
    (f : FormalSpectrum.locallyRingedSpaceObj L ⟶ Q)
    (hf : LocallyRingedSpace.IsOpenImmersion f)
    (hrange : ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q) ⊆
      Set.range f.base) :
    ∃ X : FormalScheme.{u}, X.toLocallyRingedSpace = Q :=
  (exists_formalScheme_iff_hasAffineChartAt_nodeLocus hq hI h).mpr fun _ hz =>
    ⟨C, inferInstance, inferInstance, L, inferInstance, f, hrange hz, hf⟩

/-- **Or a chart at every point of any open containing that image.** The open is arbitrary and is
not required to be affine; the bridge is `LocallyRingedSpace.hasAffineChartAt_of_restrict`
(`FormalSchemes.Gluing`).

This is the `LocallyRingedSpace.HasAffineChartAt` analogue of
`AlgebraicGeometry.isThickeningColimitTarget_iff_restrict_of_nodeLocus_subset`: the whole question
may be asked on one open around the node image, and the answer transfers. Only one direction is
stated, because an open of a formal scheme is not known on this tree to be one without a
`AlgebraicGeometry.FormalScheme.LocallyFG` hypothesis, which the colimit property does not need. -/
theorem exists_formalScheme_of_hasAffineChartAt_restrict_of_nodeLocus_subset
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (V : Opens Q)
    (hV : ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q) ⊆ (V : Set Q))
    (hVchart : ∀ w : Q.restrict V.isOpenEmbedding,
      HasAffineChartAt (Q.restrict V.isOpenEmbedding) w) :
    ∃ X : FormalScheme.{u}, X.toLocallyRingedSpace = Q :=
  (exists_formalScheme_iff_hasAffineChartAt_nodeLocus hq hI h).mpr fun _ hz =>
    hasAffineChartAt_of_restrict V (hV hz) (hVchart _)

/-- **The affine case**, through `LocallyRingedSpace.hasAffineChartAt_of_isoRestrict` rather than
through `hasAffineChartAt_of_restrict`, which would need the identification transported across
`X.restrict ⊤ ≅ X` first. This is the shape the node chart is expected to come in: `T_inv/⟨σ⟩`
restricted to one open around the node image, identified with a formal spectrum. -/
theorem exists_formalScheme_of_isoRestrict_of_nodeLocus_subset
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (V : Opens Q)
    (hV : ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q) ⊆ (V : Set Q))
    {C : Type u} [CommRing C] [TopologicalSpace C] (L : Ideal C) [IsAdicRing L]
    (e : Q.restrict V.isOpenEmbedding ≅ FormalSpectrum.locallyRingedSpaceObj L) :
    ∃ X : FormalScheme.{u}, X.toLocallyRingedSpace = Q :=
  (exists_formalScheme_iff_hasAffineChartAt_nodeLocus hq hI h).mpr fun _ hz =>
    hasAffineChartAt_of_isoRestrict V L e (hV hz)

/-! ### Non-vacuity -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The node-locus image is nonempty for `I ≠ ⊤`**, so the right-hand side of
`exists_formalScheme_iff_hasAffineChartAt_nodeLocus` is a condition on a nonempty set and the
equivalence does not hold because there is nothing to check. The witness is
`AlgebraicGeometry.annulusNodePoint`, through `AlgebraicGeometry.tateInvNodeLocus_nonempty` and
`AlgebraicGeometry.image_ι_subset_tateInvSaturate` at the model patch. -/
theorem image_base_tateInvSaturate_nodeLocus_nonempty (hItop : I ≠ ⊤) :
    (⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q)).Nonempty := by
  obtain ⟨z, hz⟩ := tateInvNodeLocus_nonempty R I q hq hI hItop
  exact ⟨_, _, image_ι_subset_tateInvSaturate hq hI _ ⟨0⟩ ⟨z, hz, rfl⟩, rfl⟩

/-! ### At the node-chart open -/

variable (R I q)

/-- **At the open row 1197 chose.** `AlgebraicGeometry.tateInvNodeChartQuotientOpens` contains the
node-locus image, by `AlgebraicGeometry.tateInvNodeLocus_subset_tateInvNodeChartLocus`, so
`exists_formalScheme_of_isoRestrict_of_nodeLocus_subset` applies to it — with the ring left free
and with no hypothesis on `I` beyond `hq` and `hI`. -/
theorem exists_formalScheme_actionQuotient_of_isoRestrict_nodeChart
    {C : Type u} [CommRing C] [TopologicalSpace C] (L : Ideal C) [IsAdicRing L]
    (e : (actionQuotient (tateInvPeriodAction R I q hq hI)).restrict
        (tateInvNodeChartQuotientOpens R I q hq hI).isOpenEmbedding ≅
      FormalSpectrum.locallyRingedSpaceObj L) :
    ∃ X : FormalScheme.{u},
      X.toLocallyRingedSpace = actionQuotient (tateInvPeriodAction R I q hq hI) :=
  exists_formalScheme_of_isoRestrict_of_nodeLocus_subset hq hI
    (isActionQuotient_actionQuotientπ _) _
    (Set.image_mono (tateInvSaturate_mono hq hI
      (tateInvNodeLocus_subset_tateInvNodeChartLocus hI))) L e

/-- **The same in the open-immersion spelling the row's residue uses.** The range hypothesis is
`AlgebraicGeometry.exists_formalScheme_of_openImmersion_spf_quotientIdeal_of_isLeftRegular_base`'s
verbatim — the range of `AlgebraicGeometry.tateInvNodeChartAmbientHom`, which
`AlgebraicGeometry.range_tateInvNodeChartAmbientHom` computes as the image of the saturation of
`D(x + y − 1)` and which therefore contains the node-locus image.

Read against that residue this says its `t`, `ht` and `hreg` are removable: they were the cost of
naming the chart's ring, not a condition on the existence of a chart. -/
theorem exists_formalScheme_actionQuotient_of_exists_openImmersion_nodeChart
    {C : Type u} [CommRing C] [TopologicalSpace C] (L : Ideal C) [IsAdicRing L]
    (hex : ∃ f : FormalSpectrum.locallyRingedSpaceObj L ⟶
        actionQuotient (tateInvPeriodAction R I q hq hI),
      LocallyRingedSpace.IsOpenImmersion f ∧
        Set.range (tateInvNodeChartAmbientHom R I q hq hI
            (π := actionQuotientπ (tateInvPeriodAction R I q hq hI))).base ⊆
          Set.range f.base) :
    ∃ X : FormalScheme.{u},
      X.toLocallyRingedSpace = actionQuotient (tateInvPeriodAction R I q hq hI) := by
  obtain ⟨f, hf, hrange⟩ := hex
  exact exists_formalScheme_of_isOpenImmersion_of_nodeLocus_subset hq hI
    (isActionQuotient_actionQuotientπ _) L f hf
    ((Set.image_mono (tateInvSaturate_mono hq hI
        (tateInvNodeLocus_subset_tateInvNodeChartLocus hI))).trans
      ((range_tateInvNodeChartAmbientHom R I q hq hI
        (isActionQuotient_actionQuotientπ _)).ge.trans hrange))

end AlgebraicGeometry
