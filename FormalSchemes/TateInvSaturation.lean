import FormalSchemes.TateInvPeriodQuotientCharts

set_option linter.style.header false

/-!
# `σ`-invariant opens of the inversion-glued Tate chain, and the charted locus of `T_inv/⟨σ⟩`

`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart`
(`FormalSchemes.TateInvPeriodQuotientCharts`) reduced "is `T_inv/⟨σ⟩` a formal scheme?" to a
hypothesis about the node locus of a single patch. That reduction is stated one point at a time.
This file re-packages it as a statement about **sets**, which is the form a construction of the
missing chart has to work against: the points of the quotient that already carry an affine formal
chart form an **open** subset, and it and the image of the node loci cover the quotient.

## Saturations

Every subset of the chain that arises here is a saturation. The patches of `T_inv` are all the
same formal annulus `Spf A`, and the shift permutes the patch inclusions
(`ι_tateInvShiftAut_zpow`, `FormalSchemes.TateActionInv`) rather than acting inside a patch, so
for any `S ⊆ Spf A` the union of the `ι m`-images of `S` over all patch indices is `σ`-invariant —
for **every** `S`, with no condition on `S` at all.

That is `image_tateInvShiftAut_zpow_tateInvSaturate`, and it is why the construction is worth a
name. A `σ`-invariant open of the chain is awkward to write down directly, because the patches
overlap and a subset of one patch is not in general a subset of its neighbour; the saturation
produces one from an arbitrary open of the model patch. `tateInvSaturate_subset_of_invariant` is
the matching universal property — the saturation is contained in every `σ`-stable set containing
any *one* of the patch images — which is what makes "saturation" the right word rather than
merely "union of translates".

## The charted locus

`tateInvChartLocus` is the union of the ranges of the two overlap charts of the annulus. Its
saturation is exactly the union of the chain's overlaps `W_m`
(`tateInvSaturate_chartLocus_eq_iUnion_tateInvOverlap`), and each `W_m` separates `σ`, so every
point of its image in the quotient has an affine formal chart. Two things follow that the
point-by-point form of the reduction did not give:

* `isOpen_image_base_tateInvSaturate_chartLocus`: **the charted locus of the quotient is open.**
  The projection of an action quotient is an open map with no hypothesis on the action
  (`LocallyRingedSpace.isOpenMap_base_of_isActionQuotient`, `FormalSchemes.ActionDiscontinuous`),
  so the failure of proper discontinuity at the nodes does not obstruct this.
* `image_base_tateInvSaturate_union_compl_eq_univ` and
  `hasAffineChartAt_or_mem_image_base_tateInvSaturate_compl`: the charted locus and the image of
  the node loci **cover** the quotient. Every point of `T_inv/⟨σ⟩` either already has a chart or
  is the image of a point of `Spf A` lying in neither overlap chart.

## What is *not* proved here

Whether the missing charts exist. That is still open, and nothing here moves it:
`AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction`
(`FormalSchemes.TateInvPeriodNodePoint`) still says the `σ`-action is not free and properly
discontinuous — some point of the chain has no separating open neighbourhood, and the witness
its proof supplies is a node. So the route by which every chart below is produced, a separating
open fed to `LocallyRingedSpace.hasAffineChartAt_of_isProperlyDiscontinuousOn`, is not available
at every point, and the missing chart has to come from somewhere else. What this file adds is
that the chart has to be glued to an **open** already-charted locus, and that the set it has to
cover is the image of a single saturation.

Also not proved, and deliberately: that the two sets of
`image_base_tateInvSaturate_union_compl_eq_univ` are **disjoint**. Only that they cover. A chain
point lying in two patches can be in both saturations, and disjointness is not what the reduction
consumes.

Nothing here weakens `LocallyRingedSpace.IsProperlyDiscontinuousOn`,
`LocallyRingedSpace.IsFreeProperlyDiscontinuous` or
`LocallyRingedSpace.freeActionQuotientFormalScheme`. Every chart produced below comes from
`LocallyRingedSpace.hasAffineChartAt_of_isProperlyDiscontinuousOn`
(`FormalSchemes.ActionQuotientChartAt`) applied to an overlap, exactly as in
`FormalSchemes.TateInvPeriodQuotientCharts`.

## Main definitions and results

* `AlgebraicGeometry.tateInvSaturate`: the union of the patch images of a subset of the model
  patch, and `image_tateInvShiftAut_zpow_tateInvSaturate`, `isOpen_tateInvSaturate`,
  `tateInvSaturate_subset_of_invariant`: it is `σ`-invariant, open when `S` is, and least.
* `AlgebraicGeometry.tateInvChartLocus` and
  `tateInvSaturate_chartLocus_eq_iUnion_tateInvOverlap`: the two overlap charts, and the
  identification of their saturation with the union of the chain's overlaps.
* `AlgebraicGeometry.preimage_image_base_tateInvSaturate`: nothing outside a saturation maps into
  its image.
* `AlgebraicGeometry.isOpen_image_base_tateInvSaturate_chartLocus`: **the charted locus of the
  quotient is open.**
* `AlgebraicGeometry.hasAffineChartAt_or_mem_image_base_tateInvSaturate_compl`: **the
  dichotomy** — a chart, or a node image.
* `AlgebraicGeometry.exists_mem_image_base_tateInvSaturate_chartLocus`: non-vacuity for `I ≠ ⊤`.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- **The `σ`-saturation of a subset of the model patch.** The patches of the inversion-glued
chain are all the same formal annulus `Spf A`; this is the union of the `ι m`-images of `S` over
all patch indices.

It is `σ`-invariant for **every** `S` (`image_tateInvShiftAut_zpow_tateInvSaturate`), because the
shift permutes the patch inclusions rather than acting inside a patch. That is the point of the
construction: it turns an arbitrary subset of `Spf A` into a `σ`-invariant subset of the chain,
and an arbitrary open into a `σ`-invariant open. -/
def tateInvSaturate (S : Set (FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q))) :
    Set (tateChainInv R I q hq hI).toLocallyRingedSpace :=
  ⋃ m : ULift.{u} ℤ, ⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' S

/-- **The union of the two overlap charts of the annulus** — the part of `Spf A` that meets a
neighbouring patch. Its complement is the node locus, in the sense in which
`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart`
(`FormalSchemes.TateInvPeriodQuotientCharts`) uses the phrase: a point lying in the range of
neither chart. Its saturation is the union of the chain's overlaps
(`tateInvSaturate_chartLocus_eq_iUnion_tateInvOverlap`). -/
def tateInvChartLocus : Set (FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q)) :=
  Set.range (annulusOverlapChart R I q).base ∪ Set.range (annulusOverlapChartY R I q).base

include hI in
omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- The chart locus is open, both overlap charts being open immersions. -/
theorem isOpen_tateInvChartLocus : IsOpen (tateInvChartLocus R I q) :=
  (isOpenImmersion_annulusOverlapChart R I q hI).base_open.isOpen_range.union
    (isOpenImmersion_annulusOverlapChartY R I q hI).base_open.isOpen_range

variable {R I q}

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Membership in a saturation: a point of the chain lies in it exactly when some patch carries a
point of `S` onto it. Definitional; stated because every proof below opens with it. -/
theorem mem_tateInvSaturate_iff {S : Set (FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q))} {x : (tateChainInv R I q hq hI).toLocallyRingedSpace} :
    x ∈ tateInvSaturate R I q hq hI S ↔
      ∃ m : ULift.{u} ℤ, ∃ y ∈ S,
        ((tateChainInvFormalGlueData R I q hq hI).ι m).base y = x :=
  Set.mem_iUnion

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Each patch image of `S` sits inside the saturation. -/
theorem image_ι_subset_tateInvSaturate (S : Set (FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q))) (m : ULift.{u} ℤ) :
    ⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' S ⊆
      tateInvSaturate R I q hq hI S :=
  Set.subset_iUnion (fun m : ULift.{u} ℤ =>
    ⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' S) m

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Saturation is monotone. -/
theorem tateInvSaturate_mono {S T : Set (FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q))} (hST : S ⊆ T) :
    tateInvSaturate R I q hq hI S ⊆ tateInvSaturate R I q hq hI T :=
  Set.iUnion_mono fun _ => Set.image_mono hST

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The saturation of an open is open**: each patch inclusion is an open immersion, hence an
open map, and a union of opens is open. -/
theorem isOpen_tateInvSaturate {S : Set (FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q))} (hS : IsOpen S) :
    IsOpen (tateInvSaturate R I q hq hI S) :=
  isOpen_iUnion fun m =>
    ((tateChainInvFormalGlueData R I q hq hI).ι_isOpenImmersion m).base_open.isOpenMap _ hS

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The saturation of an open of the model patch, as an open of the chain.**
`AlgebraicGeometry.tateInvSaturate` bundled with `AlgebraicGeometry.isOpen_tateInvSaturate`.

It lives here, beside its two ingredients, rather than in a consumer. It was originally declared in
`FormalSchemes.TateInvNodeChartGlue`, which forced any file wanting the wrapper to take that
module's whole import closure — 183 modules against this one's 166 — and a second copy of it was
duly declared in `FormalSchemes.TateInvInvariantSectionCollapse`, under a name one character away
from this one and in the same namespace. Both of those are gone; this is the only one. -/
def tateInvSaturateOpens {S : Set (FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q))} (hq : q ∈ I) (hI : I.FG) (hS : IsOpen S) :
    TopologicalSpace.Opens (tateChainInv R I q hq hI).toLocallyRingedSpace :=
  ⟨tateInvSaturate R I q hq hI S, isOpen_tateInvSaturate hq hI hS⟩

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The saturation of the whole model patch is the whole chain, the patch inclusions being
jointly surjective. -/
theorem tateInvSaturate_univ : tateInvSaturate R I q hq hI Set.univ = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨m, y, rfl⟩ := (tateChainInvFormalGlueData R I q hq hI).ι_jointly_surjective x
  exact mem_tateInvSaturate_iff hq hI |>.mpr ⟨m, y, trivial, rfl⟩

/-- **The shift carries the `m`-th patch image of `S` onto the `(m + k)`-th.** The image form of the
cover-shift law `ι_tateInvShiftAut_zpow` (`FormalSchemes.TateActionInv`), assembled at term level
rather than by `rw`: the glue datum's index type is `ULift ℤ` only after unfolding a semireducible
definition, so a rewrite inside `.ι m` fails with a spurious "did not find an occurrence".

This is the per-index step of both lemmas below, and it used to be written out inside each of them.
-/
theorem image_ι_tateInvShiftAut_zpow (k : ℤ) (m : ULift.{u} ℤ)
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    ⇑((tateInvShiftAut R I q hq hI ^ k).hom).base ''
        (⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' S) =
      ⇑((tateChainInvFormalGlueData R I q hq hI).ι ⟨m.down + k⟩).base '' S :=
  (image_comp_base ((tateChainInvFormalGlueData R I q hq hI).ι m)
      ((tateInvShiftAut R I q hq hI ^ k).hom) S).trans
    (congrArg (fun φ : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.U m ⟶
        (tateChainInv R I q hq hI).toLocallyRingedSpace => ⇑φ.base '' S)
      (ι_tateInvShiftAut_zpow R I q hq hI k m))

/-- **A saturation is `σ`-invariant**, with no hypothesis on `S` whatsoever. The cover-shift law
`ι_tateInvShiftAut_zpow` (`FormalSchemes.TateActionInv`) turns `ι m ≫ σ ^ k` into `ι (m + k)`, and
the union is then reindexed along the bijection `m ↦ m + k` of `ULift ℤ`.

The per-index identity is assembled at term level rather than by `rw`: `σ ^ k` is an element of
`Aut T_inv`, so `(σ ^ k).hom` is an `Iso` field only after an unfolding that `rw` does not perform
at `instances` transparency, and the rewrite fails with a spurious "did not find an occurrence".
`FormalSchemes.TateInvOverlapDiscontinuous` records the same rule for the glue datum. -/
theorem image_tateInvShiftAut_zpow_tateInvSaturate (k : ℤ)
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    ⇑((tateInvShiftAut R I q hq hI) ^ k).hom.base '' tateInvSaturate R I q hq hI S =
      tateInvSaturate R I q hq hI S := by
  have step₁ : ⇑((tateInvShiftAut R I q hq hI) ^ k).hom.base '' tateInvSaturate R I q hq hI S =
      ⋃ m : ULift.{u} ℤ, ⇑((tateInvShiftAut R I q hq hI) ^ k).hom.base ''
        (⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' S) := Set.image_iUnion
  have step₂ : ∀ m : ULift.{u} ℤ,
      ⇑((tateInvShiftAut R I q hq hI) ^ k).hom.base ''
          (⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' S) =
        ⇑((tateChainInvFormalGlueData R I q hq hI).ι ⟨m.down + k⟩).base '' S := fun m =>
    image_ι_tateInvShiftAut_zpow hq hI k m S
  rw [step₁, Set.iUnion_congr step₂]
  exact Set.iUnion_congr_of_surjective (fun m : ULift.{u} ℤ => (⟨m.down + k⟩ : ULift.{u} ℤ))
    (fun n => ⟨⟨n.down - k⟩, ULift.down_injective (by simp)⟩) fun _ => rfl

/-- **The universal property that justifies the name.** A set stable under every `σ ^ k` and
containing *one* patch image of `S` contains the whole saturation, the other patch images being
its translates.

So `tateInvSaturate S` is the smallest `σ`-stable set containing `ι m '' S`, for any single `m` —
which is the sense in which it is a saturation rather than merely a union of translates. -/
theorem tateInvSaturate_subset_of_invariant
    {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}
    {V : Set (tateChainInv R I q hq hI).toLocallyRingedSpace}
    (hV : ∀ k : ℤ, ⇑((tateInvShiftAut R I q hq hI) ^ k).hom.base '' V ⊆ V) (m : ULift.{u} ℤ)
    (hSm : ⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' S ⊆ V) :
    tateInvSaturate R I q hq hI S ⊆ V := by
  refine Set.iUnion_subset fun n => ?_
  have hidx : (⟨m.down + (n.down - m.down)⟩ : ULift.{u} ℤ) = n :=
    ULift.down_injective (by change m.down + (n.down - m.down) = n.down; omega)
  have key : ⇑((tateInvShiftAut R I q hq hI) ^ (n.down - m.down)).hom.base ''
        (⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' S) =
      ⇑((tateChainInvFormalGlueData R I q hq hI).ι n).base '' S :=
    (image_ι_tateInvShiftAut_zpow hq hI (n.down - m.down) m S).trans
      (congrArg (fun idx : ULift.{u} ℤ =>
        ⇑((tateChainInvFormalGlueData R I q hq hI).ι idx).base '' S) hidx)
  exact key ▸ (Set.image_mono hSm).trans (hV (n.down - m.down))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Saturation commutes with binary unions. -/
theorem tateInvSaturate_union (S T : Set (FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q))) :
    tateInvSaturate R I q hq hI (S ∪ T) =
      tateInvSaturate R I q hq hI S ∪ tateInvSaturate R I q hq hI T :=
  (Set.iUnion_congr fun m =>
    Set.image_union ⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base S T).trans
      (Set.iUnion_union_distrib _ _)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **A set and its complement saturate to a cover of the chain.** Note this is a cover and not a
partition: a chain point lying in two patches can be in both saturations, since the two patches
see it at two different points of `Spf A`. -/
theorem tateInvSaturate_union_compl (S : Set (FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q))) :
    tateInvSaturate R I q hq hI S ∪ tateInvSaturate R I q hq hI Sᶜ = Set.univ := by
  rw [← tateInvSaturate_union hq hI, Set.union_compl_self, tateInvSaturate_univ]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The saturation of the chart locus is the union of the chain's overlaps.** The `ι m`-image of
the `x`-chart is the overlap `W_m` by definition, and the `ι m`-image of the `y`-chart is
`W_{m-1}` by the glue condition (`tateInvOverlap_eq_image_chartY`,
`FormalSchemes.TateInvOverlapDiscontinuous`), so the two families of images run over the same
family of sets. -/
theorem tateInvSaturate_chartLocus_eq_iUnion_tateInvOverlap :
    tateInvSaturate R I q hq hI (tateInvChartLocus R I q) =
      ⋃ m : ULift.{u} ℤ, tateInvOverlap R I q hq hI m := by
  refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun m => ?_)
  · rintro x hx
    obtain ⟨m, y, hy, rfl⟩ := (mem_tateInvSaturate_iff hq hI).mp hx
    rcases hy with hy | hy
    · exact Set.mem_iUnion.mpr ⟨m, Set.mem_image_of_mem _ hy⟩
    · refine Set.mem_iUnion.mpr ⟨⟨m.down - 1⟩, ?_⟩
      rw [tateInvOverlap_eq_image_chartY R I q hq hI
        (i := (⟨m.down - 1⟩ : ULift.{u} ℤ)) (j := m) (by simp)]
      exact Set.mem_image_of_mem _ hy
  · exact (Set.image_mono Set.subset_union_left).trans
      (image_ι_subset_tateInvSaturate hq hI (tateInvChartLocus R I q) m)

section Quotient

variable {Q : LocallyRingedSpace.{u}}
variable {π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q}

/-- **Nothing outside a saturation maps into its image.** The preimage of the image of any set is
the union of that set's translates (`LocallyRingedSpace.preimage_image_base_of_isActionQuotient`,
`FormalSchemes.ActionDiscontinuous`), and a saturation is fixed by each of them.

This is what makes the images below well behaved: `π '' tateInvSaturate S` and
`π '' tateInvSaturate Sᶜ` are the images of `π`-saturated sets, so a statement about either pulls
back to a statement about the chain without loss. -/
theorem preimage_image_base_tateInvSaturate
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    π.base ⁻¹' (π.base '' tateInvSaturate R I q hq hI S) = tateInvSaturate R I q hq hI S := by
  rw [LocallyRingedSpace.preimage_image_base_of_isActionQuotient h]
  exact (Set.iUnion_congr fun g =>
    image_tateInvShiftAut_zpow_tateInvSaturate hq hI (Multiplicative.toAdd g) S).trans
      (Set.iUnion_const _)

/-- **The image of an open saturation is open.**
`LocallyRingedSpace.isOpenMap_base_of_isActionQuotient` needs no hypothesis on the action, so this
holds at the nodes too, where the action is not properly discontinuous. -/
theorem isOpen_image_base_tateInvSaturate
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}
    (hS : IsOpen S) : IsOpen (π.base '' tateInvSaturate R I q hq hI S) :=
  LocallyRingedSpace.isOpenMap_base_of_isActionQuotient h _ (isOpen_tateInvSaturate hq hI hS)

/-- **Every point of the image of the chart locus has an affine formal chart.** The saturation of
the chart locus is the union of the overlaps, each of which separates `σ`, so
`hasAffineChartAt_of_mem_tateInvOverlap` (`FormalSchemes.TateInvPeriodQuotientCharts`) applies at
whichever overlap the point comes from. -/
theorem hasAffineChartAt_of_mem_image_tateInvSaturate_chartLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) {z : Q}
    (hz : z ∈ π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q)) :
    LocallyRingedSpace.HasAffineChartAt Q z := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [tateInvSaturate_chartLocus_eq_iUnion_tateInvOverlap hq hI] at hx
  obtain ⟨_, ⟨m, rfl⟩, hxm⟩ := hx
  exact hasAffineChartAt_of_mem_tateInvOverlap R I q hq hI h hxm

/-- **The charted locus of the quotient is open.** With the previous result: the points of
`T_inv/⟨σ⟩` at which this file exhibits charts do not merely form a set, they form an open
subspace — which is the shape a chart at the remaining points would have to be glued to. -/
theorem isOpen_image_base_tateInvSaturate_chartLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    IsOpen (π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q)) :=
  isOpen_image_base_tateInvSaturate hq hI h (isOpen_tateInvChartLocus R I q hI)

/-- **The charted locus and the image of the node loci cover the quotient.** The projection is
surjective on points (`LocallyRingedSpace.base_surjective_of_isActionQuotient`) and the two
saturations cover the chain. -/
theorem image_base_tateInvSaturate_union_compl_eq_univ
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q) ∪
        π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q)ᶜ = Set.univ :=
  ((Set.image_union (⇑π.base) (tateInvSaturate R I q hq hI (tateInvChartLocus R I q))
          (tateInvSaturate R I q hq hI (tateInvChartLocus R I q)ᶜ)).symm.trans
        (congrArg (fun T => ⇑π.base '' T)
          (tateInvSaturate_union_compl hq hI (tateInvChartLocus R I q)))).trans
    (Set.image_univ.trans
      (Set.range_eq_univ.mpr (LocallyRingedSpace.base_surjective_of_isActionQuotient h)))

/-- **The dichotomy.** Every point of the quotient either already carries an affine formal chart,
or is the image of a point of `Spf A` lying in the range of neither overlap chart. This is
`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart`'s case analysis performed once,
as a statement about the quotient rather than as a hypothesis to be discharged.

A dichotomy, not a partition: the two alternatives are not proved exclusive and are not expected
to be, since a node image would carry a chart as well if the missing chart existed. -/
theorem hasAffineChartAt_or_mem_image_base_tateInvSaturate_compl
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (z : Q) :
    LocallyRingedSpace.HasAffineChartAt Q z ∨
      z ∈ π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q)ᶜ := by
  have hz : z ∈ π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q) ∪
      π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q)ᶜ := by
    rw [image_base_tateInvSaturate_union_compl_eq_univ hq hI h]
    trivial
  exact hz.imp (hasAffineChartAt_of_mem_image_tateInvSaturate_chartLocus hq hI h) id

/-- **Non-vacuity, as an application rather than a restatement.** For `I ≠ ⊤` the charted locus is
nonempty *and* its points carry charts: the overlap `W_0` contains `annulusOverlapGenericPoint`,
the point built for 1168's refutation (`FormalSchemes.TateInvPeriodNodePoint`), and the chart
theorem then fires at it. `I ≠ ⊤` is the same standing hypothesis the refutation needs, and for
the same reason. -/
theorem exists_mem_image_base_tateInvSaturate_chartLocus (hItop : I ≠ ⊤)
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    ∃ z ∈ π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q),
      LocallyRingedSpace.HasAffineChartAt Q z := by
  obtain ⟨x, hx⟩ := tateInvOverlap_nonempty R I q hq hI hItop ⟨0⟩
  have hmem : π.base x ∈ π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q) :=
    Set.mem_image_of_mem _ (image_ι_subset_tateInvSaturate hq hI
      (tateInvChartLocus R I q) ⟨0⟩ (Set.image_mono Set.subset_union_left hx))
  exact ⟨π.base x, hmem, hasAffineChartAt_of_mem_image_tateInvSaturate_chartLocus hq hI h hmem⟩

end Quotient

end AlgebraicGeometry
