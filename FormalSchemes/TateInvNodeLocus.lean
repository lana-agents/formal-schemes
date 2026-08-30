import FormalSchemes.TateInvSaturation

set_option linter.style.header false

/-!
# The uncharted locus of `T_inv/⟨σ⟩` is closed, and is the node locus of a single patch

`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart`
(`FormalSchemes.TateInvPeriodQuotientCharts`) reduced "is `T_inv/⟨σ⟩` a formal scheme?" to a
hypothesis `hnode` about the points of the model patch `Spf A` lying in the range of neither
overlap chart, and `FormalSchemes.TateInvSaturation` re-packaged the reduction as a **cover** of
the quotient by two sets: the images of the saturations of the chart locus and of its complement.
That file states, and deliberately does not prove, that those two sets are disjoint.

This file proves it, and everything that follows from it. The one theorem doing the work is
`eq_of_base_ι_eq_of_mem_tateInvNodeLocus`: if a point `z` of `Spf A` is in the node locus, then
`π (ι m z) = π (ι n z')` forces `z = z'`, for **all** patch indices `m`, `n` and all `z'`. So a
node point is identified with nothing but itself, not even with a point of another patch and not
even with a point of the chart locus.

## What that buys

* **The dichotomy of `FormalSchemes.TateInvSaturation` is a partition**
  (`disjoint_image_base_tateInvSaturate_nodeLocus`), so the uncharted set is exactly the
  complement of the charted one (`image_base_tateInvSaturate_nodeLocus_eq_compl`) and is therefore
  **closed** (`isClosed_image_base_tateInvSaturate_nodeLocus`). Before this the two alternatives
  were only known to cover, and "uncharted" was not known to be a closed condition.
* **The uncharted set is a copy of the node locus of one patch.** The map `z ↦ π (ι m z)` is a
  bijection from `tateInvNodeLocus` onto it (`bijOn_base_ι_tateInvNodeLocus`), and it is a
  homeomorphism (`tateInvNodeLocusHomeomorph`): the sets `π (ι m '' O)` for `O` open in `Spf A`
  cut out exactly the opens of the node locus (`preimage_image_base_ι_inter_tateInvNodeLocus`,
  `image_base_ι_inter_image_base_tateInvSaturate_nodeLocus`).
* **The residue is not vacuous** (`exists_notMem_image_base_tateInvSaturate_chartLocus`): for
  `I ≠ ⊤` the node of the special fibre over a prime of the base
  (`AlgebraicGeometry.annulusNodePoint`, `FormalSchemes.TateInvPeriodNodePoint`) is a node point,
  so the charts already produced from the overlaps genuinely fail to cover the quotient.

Read geometrically: on the special fibre the chain is `⋯ — C_n — C_{n+1} — ⋯` with one node
between consecutive components, and the quotient by the shift is the Néron 1-gon, with a **single**
node. The results above are that statement, made precise on the formal model and without assuming
the quotient is a formal scheme: whatever `T_inv/⟨σ⟩` is, its uncharted part is one closed copy of
`V(x, y) ⊆ Spf A`, i.e. of `Spf R`'s spectrum, and the missing chart has to be produced at those
points and nowhere else.

## What is *not* proved here

`hnode` itself. Nothing below produces a chart at a node, and
`AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction`
(`FormalSchemes.TateInvPeriodNodePoint`) still stands in the way of the only route the tree has
for producing one: `LocallyRingedSpace.hasAffineChartAt_of_isProperlyDiscontinuousOn` needs a
separating open, and that route is not available at every point — *some* point of the chain has no
separating open neighbourhood, and the witness the proof of that theorem supplies is a node. In
particular
`bijOn_base_ι_tateInvNodeLocus` is **not** an open immersion statement and must not be read as
one — it is a bijection of sets, promoted to a homeomorphism of spaces, with no claim about
structure sheaves. The chart still has to come from invariant sections
(`CategoryTheory.exists_actionQuotientπ_c_app_eq_iff_forall`,
`FormalSchemes.ActionQuotientInvariantSections`).

Nothing here weakens `LocallyRingedSpace.IsProperlyDiscontinuousOn`,
`LocallyRingedSpace.IsFreeProperlyDiscontinuous` or
`LocallyRingedSpace.freeActionQuotientFormalScheme`, and no chart is produced by any route other
than the one `FormalSchemes.TateInvPeriodQuotientCharts` already uses.

## Main definitions and results

* `AlgebraicGeometry.tateInvNodeLocus`: the node locus `V(x, y)` of the model patch, as the
  complement of `AlgebraicGeometry.tateInvChartLocus`; `isClosed_tateInvNodeLocus`.
* `AlgebraicGeometry.annulusNodePoint_mem_tateInvNodeLocus` and
  `AlgebraicGeometry.tateInvNodeLocus_nonempty`: it is nonempty for `I ≠ ⊤`.
* `AlgebraicGeometry.image_base_tateInvSaturate_eq_image_base_ι`: the image of a saturation in the
  quotient is the image of a single patch's copy of the set.
* `AlgebraicGeometry.eq_of_base_ι_eq_of_mem_tateInvNodeLocus`: **the key theorem** — a node point
  is identified with nothing but itself.
* `AlgebraicGeometry.disjoint_image_base_tateInvSaturate_nodeLocus`,
  `AlgebraicGeometry.image_base_tateInvSaturate_nodeLocus_eq_compl`,
  `AlgebraicGeometry.isClosed_image_base_tateInvSaturate_nodeLocus`: **the cover is a partition**,
  and the uncharted set is closed.
* `AlgebraicGeometry.bijOn_base_ι_tateInvNodeLocus` and
  `AlgebraicGeometry.tateInvNodeLocusHomeomorph`: **one node of the quotient per node of one
  patch**, as a bijection and as a homeomorphism.
* `AlgebraicGeometry.exists_notMem_image_base_tateInvSaturate_chartLocus`: the overlap charts do
  not cover the quotient.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon
  and the quotient of the infinite chain by the shift.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- **The node locus of the model patch**: the points of `Spf A` lying in the range of neither
overlap chart, i.e. the complement of `AlgebraicGeometry.tateInvChartLocus`.

Under `range_annulusOverlapChart_base` (`FormalSchemes.TateOverlapImmersion`) the chart locus is
`D(x) ∪ D(y)`, so this is the closed set `V(x, y)` of the special fibre `A ⧸ I·A`. It is exactly
the set of points at which `AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart`
(`FormalSchemes.TateInvPeriodQuotientCharts`) asks for a chart, and
`tateInvNodeLocus_nonempty` says it is not empty. -/
def tateInvNodeLocus : Set (FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q)) :=
  (tateInvChartLocus R I q)ᶜ

variable {R I q}

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- Membership in the node locus, in the two-hypothesis form
`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart` states its residue in. -/
theorem mem_tateInvNodeLocus_iff {z : FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q)} :
    z ∈ tateInvNodeLocus R I q ↔ z ∉ Set.range (annulusOverlapChart R I q).base ∧
      z ∉ Set.range (annulusOverlapChartY R I q).base :=
  not_or

variable (R I q)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The node locus is closed**, being the complement of the open chart locus
(`AlgebraicGeometry.isOpen_tateInvChartLocus`). -/
theorem isClosed_tateInvNodeLocus (hI : I.FG) : IsClosed (tateInvNodeLocus R I q) :=
  isClosed_compl_iff.mpr (isOpen_tateInvChartLocus R I q hI)

/-! ### Non-vacuity -/

include hI in
omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The node of the special fibre over a prime of the base is a point of the node locus.**
`AlgebraicGeometry.annulusNodePoint` (`FormalSchemes.TateInvPeriodNodePoint`) is the kernel of
evaluation at `x = y = 0`, so both coordinates lie in it and it is in neither basic open `D(x)`,
`D(y)`. This is the non-vacuity input for everything below, and it is the same point 1168's
refutation was built around. -/
theorem annulusNodePoint_mem_tateInvNodeLocus (𝔭 : Ideal R) [𝔭.IsPrime] (h𝔭 : I ≤ 𝔭) :
    annulusNodePoint R I q 𝔭 h𝔭 hq ∈ tateInvNodeLocus R I q := by
  have hx0 : annulusNode R I q 𝔭 h𝔭 hq (fibreX R I q) = 0 := by
    simp only [annulusNode, annulusFibreEval_fibreX]
    rfl
  have hy0 : annulusNode R I q 𝔭 h𝔭 hq (fibreY R I q) = 0 := by
    simp only [annulusNode, annulusFibreEval_fibreY]
    rfl
  have hx : fibreX R I q ∈ (annulusNodePoint R I q 𝔭 h𝔭 hq).asIdeal :=
    Ideal.mem_comap.mpr (Ideal.mem_bot.mpr hx0)
  have hy : fibreY R I q ∈ (annulusNodePoint R I q 𝔭 h𝔭 hq).asIdeal :=
    Ideal.mem_comap.mpr (Ideal.mem_bot.mpr hy0)
  refine mem_tateInvNodeLocus_iff.mpr ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [range_annulusOverlapChart_base R I q hI] at hc
    exact ((mem_basicOpen _ _ _).mp hc) hx
  · rw [show annulusOverlapChartY R I q =
        FormalSpectrum.basicOpenChart _ (overlapY R I q) from rfl,
      range_basicOpenChart_base _ (overlapY R I q) (annulusIdealOfDefinition_fg R I q hI)] at hc
    exact ((mem_basicOpen _ _ _).mp hc) hy

include hq hI in
omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The node locus is nonempty** whenever `Spf R` is. `I ≠ ⊤` supplies a maximal ideal above
`I`, and `annulusNodePoint_mem_tateInvNodeLocus` supplies the point over it — the same standing
hypothesis, for the same reason, as `AlgebraicGeometry.tateInvOverlap_nonempty`. -/
theorem tateInvNodeLocus_nonempty (hItop : I ≠ ⊤) : (tateInvNodeLocus R I q).Nonempty := by
  obtain ⟨𝔪, h𝔪, h𝔪le⟩ := Ideal.exists_le_maximal I hItop
  haveI : 𝔪.IsPrime := h𝔪.isPrime
  exact ⟨_, annulusNodePoint_mem_tateInvNodeLocus R I q hq hI 𝔪 h𝔪le⟩

section Quotient

variable {Q : LocallyRingedSpace.{u}}
variable {π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q}

/-- **The projection of a patch image does not depend on the patch.** The image form of
`AlgebraicGeometry.base_ι_eq_of_isActionQuotient`: the cover-shift law moves `ι n` to `ι m`
through `σ^{n−m}`, and `π` is invariant under `σ`. -/
theorem image_base_ι_eq_of_isActionQuotient
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)))
    (m n : ULift.{u} ℤ) :
    ⇑π.base '' (⇑((tateChainInvFormalGlueData R I q hq hI).ι n).base '' S) =
      ⇑π.base '' (⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' S) := by
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr' (fun y => base_ι_eq_of_isActionQuotient R I q hq hI h
    (m := m) (n := n) (n.down - m.down) (by omega) y)

/-- **The image of a saturation is the image of a single patch.** All the patch images of `S` are
`σ`-translates of one another, and `π` does not see a translation, so the union defining
`AlgebraicGeometry.tateInvSaturate` collapses in the quotient. This is what makes every set below
describable by one subset of `Spf A`.

The `⋃` is untangled at term level: `rw`ing the definition of the saturation inside an expression
mentioning `.ι n` produces a term that is not type-correct at `instances` transparency, because
the glue datum's index type is `ULift ℤ` only after unfolding a semireducible definition
(`FormalSchemes.TateInvOverlapDiscontinuous` records the same rule). -/
theorem image_base_tateInvSaturate_eq_image_base_ι
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)))
    (m : ULift.{u} ℤ) :
    ⇑π.base '' tateInvSaturate R I q hq hI S =
      ⇑π.base '' (⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' S) :=
  (Set.image_iUnion (f := ⇑π.base)
        (s := fun n : ULift.{u} ℤ =>
          ⇑((tateChainInvFormalGlueData R I q hq hI).ι n).base '' S)).trans
    ((Set.iUnion_congr fun n =>
      image_base_ι_eq_of_isActionQuotient R I q hq hI h S m n).trans (Set.iUnion_const _))

/-- **A node point is identified with nothing but itself.** If `z` lies in the node locus and
`π (ι m z) = π (ι n z')`, then `z = z'` — with no hypothesis on `z'`, and with `m` and `n`
arbitrary and independent.

This is the theorem the rest of the file is made of, and the proof is the three-case analysis of
the chain's geometry. The quotient's points are the orbits
(`LocallyRingedSpace.base_eq_iff_of_isActionQuotient`), so the hypothesis says
`ι p z = ι n z'` for `p = m + k` and some `k : ℤ`. If `p = n` the patch inclusion is injective and
`z = z'`. If `p` and `n` are not adjacent their patches are disjoint
(`AlgebraicGeometry.tateChainInv_ι_range_disjoint`) and there is no such point. If they are
adjacent, the common point lies in the overlap `W`
(`AlgebraicGeometry.tateInvOverlap_eq_range_ι_inter`), which inside the patch `p` is the range of
one of the two overlap charts — so `z` is in the chart locus, contradicting `hz`. -/
theorem eq_of_base_ι_eq_of_mem_tateInvNodeLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) {m n : ULift.{u} ℤ}
    {z z' : FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)}
    (hz : z ∈ tateInvNodeLocus R I q)
    (heq : π.base (((tateChainInvFormalGlueData R I q hq hI).ι m).base z) =
      π.base (((tateChainInvFormalGlueData R I q hq hI).ι n).base z')) :
    z = z' := by
  obtain ⟨g, hg⟩ := (LocallyRingedSpace.base_eq_iff_of_isActionQuotient h _ _).mp heq
  rw [tateInvPeriodAction_apply] at hg
  set k : ℤ := Multiplicative.toAdd g with hkdef
  set p : ULift.{u} ℤ := ⟨m.down + k⟩ with hpdef
  have hshift : ⇑((tateChainInvFormalGlueData R I q hq hI).ι p).base z =
      ((tateInvShiftAut R I q hq hI) ^ k).hom.base
        (((tateChainInvFormalGlueData R I q hq hI).ι m).base z) := by
    have hmor := ι_tateInvShiftAut_zpow R I q hq hI k m
    have := congrArg
      (fun φ : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.U m ⟶
        (tateChainInv R I q hq hI).toLocallyRingedSpace => ⇑φ.base z) hmor
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply] at this
    exact this.symm
  have hzz : ⇑((tateChainInvFormalGlueData R I q hq hI).ι p).base z =
      ⇑((tateChainInvFormalGlueData R I q hq hI).ι n).base z' := hshift.trans hg
  by_cases hpn : p = n
  · subst hpn
    exact tateChainInv_ι_injective R I q hq hI p hzz
  · exfalso
    by_cases h1 : n.down - p.down = 1
    · have hmem : ⇑((tateChainInvFormalGlueData R I q hq hI).ι p).base z ∈
          tateInvOverlap R I q hq hI p := by
        rw [tateInvOverlap_eq_range_ι_inter R I q hq hI h1]
        exact ⟨Set.mem_range_self z, hzz ▸ Set.mem_range_self z'⟩
      obtain ⟨w, hw, hwz⟩ := hmem
      exact (mem_tateInvNodeLocus_iff.mp hz).1
        (tateChainInv_ι_injective R I q hq hI p hwz ▸ hw)
    · by_cases h2 : n.down - p.down = -1
      · have hp1 : p.down - n.down = 1 := by omega
        have hmem : ⇑((tateChainInvFormalGlueData R I q hq hI).ι p).base z ∈
            tateInvOverlap R I q hq hI n := by
          rw [tateInvOverlap_eq_range_ι_inter R I q hq hI hp1]
          exact ⟨hzz ▸ Set.mem_range_self z', Set.mem_range_self z⟩
        rw [tateInvOverlap_eq_image_chartY R I q hq hI (i := n) (j := p) hp1] at hmem
        obtain ⟨w, hw, hwz⟩ := hmem
        exact (mem_tateInvNodeLocus_iff.mp hz).2
          (tateChainInv_ι_injective R I q hq hI p hwz ▸ hw)
      · exact Set.disjoint_left.mp (tateChainInv_ι_range_disjoint R I q hq hI hpn h1 h2)
          (Set.mem_range_self z) (hzz ▸ Set.mem_range_self z')

/-- **The projection is injective on the node locus of a patch**, the case `m = n` of
`eq_of_base_ι_eq_of_mem_tateInvNodeLocus`. Note this is not an instance of
`LocallyRingedSpace.injOn_base_of_isProperlyDiscontinuousOn`: the node locus is closed, not open,
so it is not a separating open. And
`AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction` is weaker than it may
read — it negates a `∀`, so it says only that *some* point of the chain has no separating open
neighbourhood — so it does not on its own rule out a separating neighbourhood of this set. The
injectivity is proved directly from
`eq_of_base_ι_eq_of_mem_tateInvNodeLocus` instead. -/
theorem injOn_base_ι_tateInvNodeLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (m : ULift.{u} ℤ) :
    Set.InjOn (fun z => π.base (((tateChainInvFormalGlueData R I q hq hI).ι m).base z))
      (tateInvNodeLocus R I q) :=
  fun _ hz _ _ heq => eq_of_base_ι_eq_of_mem_tateInvNodeLocus R I q hq hI h hz heq

/-- **The charted locus and the node locus of the quotient are disjoint.** This is the statement
`FormalSchemes.TateInvSaturation` names and leaves unproved: its
`image_base_tateInvSaturate_union_compl_eq_univ` gives a cover, and this gives that the cover is a
partition. Both images collapse to a single patch by
`image_base_tateInvSaturate_eq_image_base_ι`, and the two representatives are then equal by
`eq_of_base_ι_eq_of_mem_tateInvNodeLocus`, which is absurd. -/
theorem disjoint_image_base_tateInvSaturate_nodeLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    Disjoint (⇑π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q))
      (⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q)) := by
  refine Set.disjoint_left.mpr fun z hz1 hz2 => ?_
  rw [image_base_tateInvSaturate_eq_image_base_ι R I q hq hI h _ (⟨0⟩ : ULift.{u} ℤ)] at hz1
  rw [image_base_tateInvSaturate_eq_image_base_ι R I q hq hI h _ (⟨0⟩ : ULift.{u} ℤ)] at hz2
  obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hz1
  obtain ⟨_, ⟨b, hb, rfl⟩, heq⟩ := hz2
  exact (eq_of_base_ι_eq_of_mem_tateInvNodeLocus R I q hq hI h hb heq) ▸ hb <| ha

/-- **The node locus of the quotient is the complement of the charted locus**: cover plus
disjointness. -/
theorem image_base_tateInvSaturate_nodeLocus_eq_compl
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q) =
      (⇑π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q))ᶜ := by
  refine Set.Subset.antisymm (fun z hz => Set.disjoint_right.mp
    (disjoint_image_base_tateInvSaturate_nodeLocus R I q hq hI h) hz) (fun z _ => ?_)
  have hcov : z ∈ ⇑π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q) ∪
      ⇑π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q)ᶜ := by
    rw [image_base_tateInvSaturate_union_compl_eq_univ hq hI h]
    trivial
  exact hcov.resolve_left (by assumption)

/-- **The node locus of the quotient is closed.** With
`AlgebraicGeometry.isOpen_image_base_tateInvSaturate_chartLocus`: the quotient splits into an open
set on which charts are already known and a closed set on which they are not, so "uncharted by the
overlap route" is a closed condition on `T_inv/⟨σ⟩`. -/
theorem isClosed_image_base_tateInvSaturate_nodeLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    IsClosed (⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q)) := by
  rw [image_base_tateInvSaturate_nodeLocus_eq_compl R I q hq hI h]
  exact (isOpen_image_base_tateInvSaturate_chartLocus hq hI h).isClosed_compl

/-- **One node of the quotient per node of one patch.** The map `z ↦ π (ι m z)` is a bijection
from the node locus of `Spf A` onto the uncharted set of the quotient, for every patch index `m`.
Surjectivity is `image_base_tateInvSaturate_eq_image_base_ι` and injectivity is
`injOn_base_ι_tateInvNodeLocus`.

This is the Néron 1-gon's single node, on the formal model: the chain has one node per pair of
consecutive components and the quotient has one node in total. It is a statement about points
only — see `tateInvNodeLocusHomeomorph` for the topology, and note that no claim is made about
structure sheaves anywhere. -/
theorem bijOn_base_ι_tateInvNodeLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (m : ULift.{u} ℤ) :
    Set.BijOn (fun z => π.base (((tateChainInvFormalGlueData R I q hq hI).ι m).base z))
      (tateInvNodeLocus R I q)
      (⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q)) := by
  have himg : (fun z => π.base (((tateChainInvFormalGlueData R I q hq hI).ι m).base z)) ''
      tateInvNodeLocus R I q =
        ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q) := by
    rw [image_base_tateInvSaturate_eq_image_base_ι R I q hq hI h _ m, Set.image_image]
  exact himg ▸ (injOn_base_ι_tateInvNodeLocus R I q hq hI h m).bijOn_image

/-- **A node point is recognised inside its own patch.** A node point whose image lies in the
image of `ι m '' O` is itself in `O`: the only preimage of its image that could be in `O` is
itself, by `eq_of_base_ι_eq_of_mem_tateInvNodeLocus`. This is the statement that the opens
`π (ι m '' O)` of the quotient cut the node locus in exactly the opens `O ∩ V(x, y)`, and it is
the topological input to `tateInvNodeLocusHomeomorph`. -/
theorem preimage_image_base_ι_inter_tateInvNodeLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (m : ULift.{u} ℤ)
    (O : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    (fun z => π.base (((tateChainInvFormalGlueData R I q hq hI).ι m).base z)) ⁻¹'
        (⇑π.base '' (⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' O)) ∩
          tateInvNodeLocus R I q =
      O ∩ tateInvNodeLocus R I q := by
  refine Set.Subset.antisymm (fun z hz => ⟨?_, hz.2⟩) (fun z hz =>
    ⟨⟨_, Set.mem_image_of_mem _ hz.1, rfl⟩, hz.2⟩)
  obtain ⟨_, ⟨a, ha, rfl⟩, heq⟩ := hz.1
  exact (eq_of_base_ι_eq_of_mem_tateInvNodeLocus R I q hq hI h hz.2 heq.symm) ▸ ha

/-- **The images of the opens of a patch cut the quotient's node locus correctly.** The image
form of `preimage_image_base_ι_inter_tateInvNodeLocus`: taking images along `π ∘ ι m` commutes
with intersecting against the node locus, which is false for a general pair of sets and holds here
because one of them is the node locus. -/
theorem image_base_ι_inter_image_base_tateInvSaturate_nodeLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (m : ULift.{u} ℤ)
    (O : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    ⇑π.base '' (⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' O) ∩
        (⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q)) =
      ⇑π.base '' (⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base ''
        (O ∩ tateInvNodeLocus R I q)) := by
  rw [image_base_tateInvSaturate_eq_image_base_ι R I q hq hI h _ m, Set.image_image,
    Set.image_image, Set.image_image]
  refine Set.Subset.antisymm (fun z hz => ?_)
    (Set.subset_inter (Set.image_mono Set.inter_subset_left)
      (Set.image_mono Set.inter_subset_right))
  obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, hbz⟩⟩ := hz
  exact ⟨a, ⟨ha, (eq_of_base_ι_eq_of_mem_tateInvNodeLocus R I q hq hI h hb hbz) ▸ hb⟩, rfl⟩

/-- **The overlap charts do not cover the quotient**, for `I ≠ ⊤`. So the residue that
`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart` isolates is a statement about a
genuinely nonempty set, and the chart theorem
`AlgebraicGeometry.hasAffineChartAt_of_mem_tateInvOverlap` alone cannot finish the question. The
witness is the image of `AlgebraicGeometry.annulusNodePoint`. -/
theorem exists_notMem_image_base_tateInvSaturate_chartLocus (hItop : I ≠ ⊤)
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    ∃ z : Q, z ∉ ⇑π.base '' tateInvSaturate R I q hq hI (tateInvChartLocus R I q) := by
  obtain ⟨y, hy⟩ := tateInvNodeLocus_nonempty R I q hq hI hItop
  refine ⟨π.base (((tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩).base y), fun hc => ?_⟩
  exact Set.disjoint_left.mp (disjoint_image_base_tateInvSaturate_nodeLocus R I q hq hI h) hc
    (Set.mem_image_of_mem _ (image_ι_subset_tateInvSaturate hq hI
      (tateInvNodeLocus R I q) ⟨0⟩ (Set.mem_image_of_mem _ hy)))

/-- **The node locus of the quotient, as a space, is the node locus of one patch.** The bijection
of `bijOn_base_ι_tateInvNodeLocus` is a homeomorphism: it is continuous because `π` and `ι m` are,
and open because the image of an open `O` of `Spf A` is the open set `π (ι m '' O)` of the
quotient (`LocallyRingedSpace.isOpenMap_base_of_isActionQuotient`, which needs no hypothesis on
the action) intersected with the node locus, by
`preimage_image_base_ι_inter_tateInvNodeLocus`.

A homeomorphism of underlying spaces and nothing more: no morphism of locally ringed spaces is
claimed here, and in particular this is not a chart. -/
def tateInvNodeLocusHomeomorph
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) (m : ULift.{u} ℤ) :
    (tateInvNodeLocus R I q) ≃ₜ
      (⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeLocus R I q)) := by
  have hbij := bijOn_base_ι_tateInvNodeLocus R I q hq hI h m
  refine Equiv.toHomeomorphOfContinuousOpen (hbij.equiv _)
    (Continuous.restrict hbij.mapsTo (by fun_prop)) ?_
  rintro W hW
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hW
  refine isOpen_induced_iff.mpr ⟨⇑π.base ''
    (⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' O), ?_, ?_⟩
  · exact LocallyRingedSpace.isOpenMap_base_of_isActionQuotient h _
      (((tateChainInvFormalGlueData R I q hq hI).ι_isOpenImmersion m).base_open.isOpenMap _ hO)
  · refine Set.eq_of_subset_of_subset (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨z, hz, hzy⟩ := hbij.surjOn y.2
      obtain ⟨_, ⟨a, ha, rfl⟩, heq⟩ := hy
      have hza : z = a := eq_of_base_ι_eq_of_mem_tateInvNodeLocus R I q hq hI h hz
        (hzy.trans heq.symm)
      exact ⟨⟨z, hz⟩, show z ∈ O by rw [hza]; exact ha, Subtype.ext hzy⟩
    · obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨_, Set.mem_image_of_mem _ hz, rfl⟩

end Quotient

end AlgebraicGeometry
