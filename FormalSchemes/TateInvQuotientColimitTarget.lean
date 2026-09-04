import FormalSchemes.TateChainInvColimitTarget
import FormalSchemes.TateInvNodeChartQuotientOpen

set_option linter.style.header false

/-!
# The colimit property of `T_inv/⟨σ⟩` is a question about one open around the node

Row 1197's remaining obstruction is a morphism `Spf S ⟶ T_inv/⟨σ⟩`. The only producers of such a
morphism on this tree are `FormalSpectrum.existsUnique_hom_thickeningMap` and its relatives, and
each of them asks for the target to be **covered** by opens with
`FormalSpectrum.IsThickeningColimitTarget` — which, at `T_inv/⟨σ⟩`, is exactly the cover that is
missing the chart being built. PR #508 closed the attempt to weaken that covering hypothesis and
left behind a different question:

> is there an open of `T_inv/⟨σ⟩` containing a node image whose restriction has
> `IsThickeningColimitTarget` without being known to be a formal scheme?

This file answers the *shape* of that question rather than the question itself. With
`FormalSpectrum.IsThickeningColimitTarget.restrict` (`FormalSchemes.ThickeningColimitTarget`) the
property is local (`FormalSpectrum.isThickeningColimitTarget_iff_forall_exists_mem`), and the
charted locus of the quotient carries it for a reason that never mentions a chart: each overlap
`W_i` separates `σ`, so `W_i ⟶ T_inv/⟨σ⟩` is an open immersion, and its source is an open of the
chain — which has the property because the chain does
(`AlgebraicGeometry.isThickeningColimitTarget_tateChainInv`) and the property restricts. Hence

* `AlgebraicGeometry.isThickeningColimitTarget_iff_restrict_of_nodeLocus_subset`: for **any** open
  `V` of the quotient containing the image of the node locus,
  `IsThickeningColimitTarget (T_inv/⟨σ⟩)` holds **iff** it holds on `V`;
* `AlgebraicGeometry.isThickeningColimitTarget_actionQuotient_iff_restrict_nodeChart`: the same at
  the named node-chart open `AlgebraicGeometry.tateInvNodeChartQuotientOpens`, the domain row 1197
  chose in `FormalSchemes.TateInvNodeChartDomain`.

## What this settles, and what it does not

**Settled.** The colimit property of the quotient is not a global question: everything outside one
open around the node image is discharged, and discharged without a formal-affine chart there. So a
successor may work on `T_inv/⟨σ⟩ |_{V}` alone, and the answer transfers.

**Not settled — `hnode` is still open, and this file does not attempt it.** Two gaps remain
between the right-hand side of these equivalences and row 1197's residue:

* nothing here proves `IsThickeningColimitTarget` of the node-chart open. It is now an equivalent
  of the same property for the whole quotient, which is a reduction, not an answer. In particular
  the answer to #508's residue question as literally posed is still unknown — what is new is that
  it may be asked at the *whole* quotient, where every producer on the tree can be brought to bear,
  instead of at an open nobody has a handle on.
* the colimit property alone does not give an *open immersion*.
  `AlgebraicGeometry.exists_formalScheme_of_openImmersion_spf_quotientIdeal_of_isLeftRegular_base`
  (`FormalSchemes.TateInvNodeChartQuotientSpf`) needs `LocallyRingedSpace.IsOpenImmersion` of the
  morphism and a containment of ranges; a morphism out of `Spf S` is one hypothesis of three.

## Main results

* `AlgebraicGeometry.tateInvOverlapHom`: the projection restricted to an overlap, and
  `AlgebraicGeometry.isOpenImmersion_tateInvOverlapHom`, that it is an open immersion.
* `AlgebraicGeometry.tateInvOverlapQuotientOpens`: its range, as an open of the quotient, with
  `AlgebraicGeometry.isThickeningColimitTarget_restrict_tateInvOverlapQuotientOpens` — **the
  charted locus carries the colimit property, with no chart and no finite generation**.
* `AlgebraicGeometry.isThickeningColimitTarget_of_restrict_of_nodeLocus_subset` and its
  equivalence form.
* `AlgebraicGeometry.isThickeningColimitTarget_actionQuotient_iff_restrict_nodeChart`.
* `AlgebraicGeometry.exists_mem_tateInvNodeChartQuotientOpens_notMem_chartLocus`: for `I ≠ ⊤` the
  node-chart open is not contained in the charted locus, so the equivalences above are not the
  cover theorem in disguise.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
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

/-! ### The charted locus, without a chart -/

/-- **The quotient projection restricted to an overlap.** The composite
`T_inv|_{W_i} ⟶ T_inv ⟶ T_inv/⟨σ⟩`. -/
def tateInvOverlapHom (π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q)
    (i : ULift.{u} ℤ) :
    (tateChainInv R I q hq hI).toLocallyRingedSpace.restrict
      (tateInvOverlapOpens R I q hq hI i).isOpenEmbedding ⟶ Q :=
  (tateChainInv R I q hq hI).toLocallyRingedSpace.ofRestrict
    (tateInvOverlapOpens R I q hq hI i).isOpenEmbedding ≫ π

/-- **It is an open immersion**, because `W_i` separates `σ`
(`AlgebraicGeometry.tateInvOverlap_isProperlyDiscontinuousOn`). This is the morphism whose
existence `AlgebraicGeometry.hasAffineChartAt_of_mem_tateInvOverlap` uses to build a chart; here it
is kept as a morphism instead, which is what lets the colimit property be transported along it
without producing a ring. -/
theorem isOpenImmersion_tateInvOverlapHom
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (i : ULift.{u} ℤ) :
    LocallyRingedSpace.IsOpenImmersion (tateInvOverlapHom hq hI π i) :=
  haveI := isIso_stalkMap_ofRestrict_comp h (tateInvOverlapOpens R I q hq hI i)
    (tateInvOverlap_isProperlyDiscontinuousOn R I q hq hI i)
  isOpenImmersion_ofRestrict_comp_of_stalk_iso h
    (tateInvOverlap_isProperlyDiscontinuousOn R I q hq hI i)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Its range is the image of the overlap, which is how it meets the set-level description of the
charted locus in `FormalSchemes.TateInvSaturation`. -/
theorem range_tateInvOverlapHom (i : ULift.{u} ℤ) :
    Set.range (tateInvOverlapHom hq hI π i).base = ⇑π.base '' tateInvOverlap R I q hq hI i := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- **The image of an overlap in the quotient, as an open.** Open because `π` is an open map for
every action quotient (`LocallyRingedSpace.isOpenMap_base_of_isActionQuotient`), with no hypothesis
on the action. -/
def tateInvOverlapQuotientOpens (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (i : ULift.{u} ℤ) : Opens Q :=
  ⟨⇑π.base '' tateInvOverlap R I q hq hI i,
    isOpenMap_base_of_isActionQuotient h _ (isOpen_tateInvOverlap R I q hq hI i)⟩

/-- **The charted locus carries the colimit property, piece by piece, with no chart.** The open
`π '' W_i` of the quotient is isomorphic to the open `W_i` of the chain, and the chain has the
property (`AlgebraicGeometry.isThickeningColimitTarget_tateChainInv`), so
`FormalSpectrum.IsThickeningColimitTarget.restrict` gives it for `W_i` and
`FormalSpectrum.IsThickeningColimitTarget.of_iso` carries it across.

Nothing here produces an affine formal chart of the quotient, and nothing here needs one — in
particular no finite generation of a chart ideal is used, which is what a route through
`FormalSpectrum.isThickeningColimitTarget_spf` would have needed and what
`AlgebraicGeometry.LocallyRingedSpace.HasAffineChartAt` does not carry. -/
theorem isThickeningColimitTarget_restrict_tateInvOverlapQuotientOpens
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (i : ULift.{u} ℤ) :
    IsThickeningColimitTarget
      (Q.restrict (tateInvOverlapQuotientOpens hq hI h i).isOpenEmbedding) :=
  haveI := isOpenImmersion_tateInvOverlapHom hq hI h i
  IsThickeningColimitTarget.of_iso
    (IsThickeningColimitTarget.restrict (isThickeningColimitTarget_tateChainInv R I q hq hI)
      (tateInvOverlapOpens R I q hq hI i))
    (IsOpenImmersion.isoRestrictOfRangeEq (tateInvOverlapHom hq hI π i)
      (tateInvOverlapQuotientOpens hq hI h i) (range_tateInvOverlapHom hq hI i))

/-! ### The reduction to one open around the node -/

/-- **The colimit property of the quotient follows from the colimit property of any open
containing the image of the node locus.** The cover is that open together with the images of the
overlaps: `AlgebraicGeometry.image_base_tateInvSaturate_union_compl_eq_univ` says the charted locus
and the node locus image cover the quotient, and
`AlgebraicGeometry.tateInvSaturate_chartLocus_eq_iUnion_tateInvOverlap` breaks the first of them
into the overlaps. -/
theorem isThickeningColimitTarget_of_restrict_of_nodeLocus_subset
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (V : Opens Q)
    (hV : ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q) ⊆ (V : Set Q))
    (hVcol : IsThickeningColimitTarget (Q.restrict V.isOpenEmbedding)) :
    IsThickeningColimitTarget Q := by
  rw [isThickeningColimitTarget_iff_forall_exists_mem]
  intro z
  have hz : z ∈ ⇑π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q) ∪
      ⇑π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q)ᶜ := by
    rw [image_base_tateInvSaturate_union_compl_eq_univ hq hI h]
    trivial
  rcases hz with hz | hz
  · rw [tateInvSaturate_chartLocus_eq_iUnion_tateInvOverlap hq hI] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨_, ⟨m, rfl⟩, hxm⟩ := hx
    exact ⟨tateInvOverlapQuotientOpens hq hI h m, ⟨x, hxm, rfl⟩,
      isThickeningColimitTarget_restrict_tateInvOverlapQuotientOpens hq hI h m⟩
  · exact ⟨V, hV hz, hVcol⟩

/-- **And conversely**, by `FormalSpectrum.IsThickeningColimitTarget.restrict`. So the colimit
property of `T_inv/⟨σ⟩` is *equivalent* to its colimit property on one open around the node image:
the question is local at the node, and every open containing that image asks the same question. -/
theorem isThickeningColimitTarget_iff_restrict_of_nodeLocus_subset
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (V : Opens Q)
    (hV : ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q) ⊆ (V : Set Q)) :
    IsThickeningColimitTarget Q ↔ IsThickeningColimitTarget (Q.restrict V.isOpenEmbedding) :=
  ⟨fun hQ => IsThickeningColimitTarget.restrict hQ V,
    isThickeningColimitTarget_of_restrict_of_nodeLocus_subset hq hI h V hV⟩

variable (R I q)

/-- **At the node-chart open row 1197 chose.** `AlgebraicGeometry.tateInvNodeChartQuotientOpens` is
the image of the saturation of `D(x + y − 1) ⊆ Spf A`, which contains the node locus
(`AlgebraicGeometry.tateInvNodeLocus_subset_tateInvNodeChartLocus`), so the previous theorem
applies to it. This is the open whose sections
`AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv` identifies with
`AlgebraicGeometry.tateInvNodeChartAwaySubring`, and `Spf` of which
`AlgebraicGeometry.exists_formalScheme_of_openImmersion_spf_quotientIdeal_of_isLeftRegular_base`
asks for an open immersion out of. -/
theorem isThickeningColimitTarget_actionQuotient_iff_restrict_nodeChart :
    IsThickeningColimitTarget (actionQuotient (tateInvPeriodAction R I q hq hI)) ↔
      IsThickeningColimitTarget
        ((actionQuotient (tateInvPeriodAction R I q hq hI)).restrict
          (tateInvNodeChartQuotientOpens R I q hq hI).isOpenEmbedding) :=
  isThickeningColimitTarget_iff_restrict_of_nodeLocus_subset hq hI
    (isActionQuotient_actionQuotientπ _) _
    (Set.image_mono (tateInvSaturate_mono hq hI
      (tateInvNodeLocus_subset_tateInvNodeChartLocus hI)))

/-- **Non-vacuity: the node-chart open is not part of the charted locus.** Inherited from
`AlgebraicGeometry.exists_notMem_image_base_tateInvSaturate_chartLocus`, whose witness is the image
of `AlgebraicGeometry.annulusNodePoint` — the point 1168 built to refute free proper
discontinuity. So the right-hand side of
`isThickeningColimitTarget_actionQuotient_iff_restrict_nodeChart` is a statement about an open on
which the overlap route says nothing, and the equivalence is not
`FormalSpectrum.isThickeningColimitTarget_of_cover` restated. -/
theorem exists_mem_tateInvNodeChartQuotientOpens_notMem_chartLocus (hItop : I ≠ ⊤) :
    ∃ z ∈ tateInvNodeChartQuotientOpens R I q hq hI,
      z ∉ ⇑(actionQuotientπ (tateInvPeriodAction R I q hq hI)).base ''
        tateInvSaturate R I q hq hI (tateInvChartLocus R I q) := by
  obtain ⟨z, hz⟩ := exists_notMem_image_base_tateInvSaturate_chartLocus R I q hq hI hItop
    (isActionQuotient_actionQuotientπ (tateInvPeriodAction R I q hq hI))
  refine ⟨z, ?_, hz⟩
  have hcov : z ∈ ⇑(actionQuotientπ (tateInvPeriodAction R I q hq hI)).base ''
      tateInvSaturate R I q hq hI (tateInvChartLocus R I q) ∪
      ⇑(actionQuotientπ (tateInvPeriodAction R I q hq hI)).base ''
        tateInvSaturate R I q hq hI (tateInvChartLocus R I q)ᶜ := by
    rw [image_base_tateInvSaturate_union_compl_eq_univ hq hI
      (isActionQuotient_actionQuotientπ _)]
    trivial
  exact Set.image_mono (tateInvSaturate_mono hq hI
    (tateInvNodeLocus_subset_tateInvNodeChartLocus hI)) (hcov.resolve_left hz)

end AlgebraicGeometry

end
