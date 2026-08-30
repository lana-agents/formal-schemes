import FormalSchemes.TateInvOverlapBand
import FormalSchemes.TateInvPeriodNotDiscontinuous

set_option linter.style.header false

/-!
# `tateInvPatchSaturate` in the annulus charts

`AlgebraicGeometry.tateInvPatchSaturate` (`FormalSchemes.TateInvNodeChartRing`) is defined as the
preimage under the patch inclusion `ι ⟨0⟩` of a saturation *inside* the glued chain `T_inv`. It is
the open of the model patch `Spf A` over which the whole overlap condition of
`FormalSchemes.TateInvOverlapBand` is read, and it was the last place the chain survived in that
condition: `AlgebraicGeometry.isTateInvOverlapCompatible_iff_charts` eliminated the glue datum from
the two *legs*, and its own docstring says the open they are read over still names `ι ⟨0⟩`.

This file computes that open. Splitting the saturation's union by patch index, a patch contributes
to `ι ⟨0⟩`'s preimage only if it is `U₀` itself or one of its two neighbours, and each of the three
contributions is expressible in the two annulus charts alone:

* the patch itself contributes `S`, because `ι ⟨0⟩` is injective;
* `U₁` contributes the `x`-chart image of what the `𝔾m`-inversion transition followed by the
  `y`-chart pulls back from `S`;
* `U₋₁` contributes the mirror;
* every other patch contributes nothing, its image being disjoint from `U₀`'s.

## What is here

* `AlgebraicGeometry.annulusOverlapChartY_comp_ι`: the backward mirror of the existing
  `AlgebraicGeometry.annulusOverlapChart_comp_ι`
  (`FormalSchemes.TateInvPeriodNotDiscontinuous`), obtained from it by composing with
  `(annulusChartTransitionInvSpf …).inv`. `AlgebraicGeometry.base_ι_annulusOverlapChart` and
  `AlgebraicGeometry.base_ι_annulusOverlapChartY` are the two read at a point.
* `AlgebraicGeometry.preimage_ι_image_ι_forward`,
  `AlgebraicGeometry.preimage_ι_image_ι_backward`,
  `AlgebraicGeometry.preimage_ι_image_ι_far`: **what one patch sees of another's copy of `S`.**
  The three cases above, each stated for an arbitrary pair of indices in the relevant position.
  The right-hand sides do not mention the indices at all: what patch `i` sees of patch `j`'s copy
  of `S` depends only on whether `j` is `i`, `i ± 1`, or further away.
* `AlgebraicGeometry.tateInvChartSaturate` and
  `AlgebraicGeometry.tateInvPatchSaturate_eq_tateInvChartSaturate`: **the description.** No glue
  datum, no `ι`, no `AlgebraicGeometry.tateInvSaturate` and no object of `T_inv` occurs on the
  right-hand side. `AlgebraicGeometry.mem_tateInvChartSaturate_iff` is its membership rule.
* `AlgebraicGeometry.isOpen_tateInvChartSaturate`,
  `AlgebraicGeometry.tateInvChartSaturateOpens` and
  `AlgebraicGeometry.tateInvPatchSaturateOpens_eq_tateInvChartSaturateOpens`: the `Opens` form,
  which is what every downstream statement actually mentions.
* `AlgebraicGeometry.subset_tateInvChartSaturate`,
  `AlgebraicGeometry.tateInvChartSaturate_empty`,
  `AlgebraicGeometry.tateInvChartSaturate_univ`: the description evaluated. Through the main
  theorem the last two reproduce `AlgebraicGeometry.tateInvPatchSaturate_univ`
  (`FormalSchemes.TateInvNodeChartRing`) and `AlgebraicGeometry.tateInvPatchSaturate_empty`
  (`FormalSchemes.TateInvChartAnnulusRing`), each computed there by a different route.
* `AlgebraicGeometry.tateInvChartSaturateSection` and
  `AlgebraicGeometry.isTateInvOverlapCompatible_iff_charts_chartSaturateOpens`: the overlap
  condition restated over the chain-free open.

## What is *not* proved

**The right-hand side is not claimed to be a disjoint union, nor irredundant.** The three pieces
overlap: `S` meets both chart images whenever `S` meets a chart locus, and nothing here says the
second and third are non-empty for any particular `S`.

**Nothing here is about the chart ring.** Whether
`AlgebraicGeometry.tateInvChartAnnulusSubring` (`FormalSchemes.TateInvChartAnnulusRing`) is a
proper subring is a different question and is untouched; so is the question of an element of it
outside the image of `Γ (Spf R, ·)`.

**Nothing here produces a chart.** An open is not a ring and a ring is not a chart:
`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart`
(`FormalSchemes.TateInvPeriodQuotientCharts`) still needs an adic structure and an open immersion.

**`AlgebraicGeometry.IsTateInvOverlapCompatible` itself is still defined through the glue datum**,
and `isTateInvOverlapCompatible_iff_charts_chartSaturateOpens` does not change that — it is the
left-hand side of a characterisation whose right-hand side, and whose ambient ring, are now
chain-free.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon.
  Geometrically the description says: the part of one component visible in the `n`-gon over `S` is
  `S` together with what the two adjacent components glue onto it, and nothing further along the
  chain reaches it.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} {q : R}
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] {hq : q ∈ I} {hI : I.FG}

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The glue condition on a backward pair.** For `j = i - 1`, the `y`-chart of the patch `U_i`
and the `x`-chart of the patch `U_j` have the same composite into the chain, once the second is
preceded by the inverse `𝔾m`-inversion transition. The mirror of
`AlgebraicGeometry.annulusOverlapChart_comp_ι`
(`FormalSchemes.TateInvPeriodNotDiscontinuous`), and derived from it rather than re-proved: read
that lemma at the pair `(j, i)` and compose with `(annulusChartTransitionInvSpf …).inv`. -/
theorem annulusOverlapChartY_comp_ι {i j : ULift.{u} ℤ} (h : j.down - i.down = -1) :
    annulusOverlapChartY R I q ≫ (tateChainInvFormalGlueData R I q hq hI).ι i =
      (annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapChart R I q ≫
        (tateChainInvFormalGlueData R I q hq hI).ι j := by
  have hf := annulusOverlapChart_comp_ι R I q hq hI (i := j) (j := i) (by omega)
  rw [hf, Iso.inv_hom_id_assoc]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The forward glue condition at a point.** `annulusOverlapChart_comp_ι` with both sides
applied to `w`; the composites unfold definitionally, so this is `congrArg` and nothing else. -/
theorem base_ι_annulusOverlapChart {i j : ULift.{u} ℤ} (h : j.down - i.down = 1)
    (w : FormalSpectrum.locallyRingedSpaceObj
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))) :
    ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base
        ((annulusOverlapChart R I q).base w) =
      ⇑((tateChainInvFormalGlueData R I q hq hI).ι j).base
        (⇑((annulusChartTransitionInvSpf R I q hI).hom ≫
          annulusOverlapChartY R I q).base w) := by
  have hmor := annulusOverlapChart_comp_ι R I q hq hI (i := i) (j := j) h
  exact congrArg (fun φ : FormalSpectrum.locallyRingedSpaceObj
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) ⟶
    (tateChainInv R I q hq hI).toLocallyRingedSpace => ⇑φ.base w) hmor

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The backward glue condition at a point.** `annulusOverlapChartY_comp_ι` at `w`. -/
theorem base_ι_annulusOverlapChartY {i j : ULift.{u} ℤ} (h : j.down - i.down = -1)
    (w : FormalSpectrum.locallyRingedSpaceObj
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))) :
    ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base
        ((annulusOverlapChartY R I q).base w) =
      ⇑((tateChainInvFormalGlueData R I q hq hI).ι j).base
        (⇑((annulusChartTransitionInvSpf R I q hI).inv ≫
          annulusOverlapChart R I q).base w) := by
  have hmor := annulusOverlapChartY_comp_ι (hq := hq) (hI := hI) (i := i) (j := j) h
  exact congrArg (fun φ : FormalSpectrum.locallyRingedSpaceObj
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)) ⟶
    (tateChainInv R I q hq hI).toLocallyRingedSpace => ⇑φ.base w) hmor

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **What the next patch contributes.** For `j = i + 1`, the part of `U_i`'s copy of the model
patch that meets `U_j`'s copy of `S` is the `x`-chart image of the pullback of `S` along the
transition-then-`y`-chart leg — the same leg
`AlgebraicGeometry.IsTateInvChartCompatibleForward` (`FormalSchemes.TateInvOverlapBand`) is stated
with.

One inclusion is the glue condition read forwards. The other uses that a point of `U_i` lying in
`U_j` lies in the overlap `AlgebraicGeometry.tateInvOverlap`
(`AlgebraicGeometry.tateInvOverlap_eq_range_ι_inter`), which is `ι i`'s image of the `x`-chart, and
then injectivity of the two patch inclusions
(`AlgebraicGeometry.tateChainInv_ι_injective`) twice.

**The right-hand side does not mention `i` or `j`.** Every forward pair contributes the same
set. -/
theorem preimage_ι_image_ι_forward {i j : ULift.{u} ℤ} (h : j.down - i.down = 1)
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base ⁻¹'
        (⇑((tateChainInvFormalGlueData R I q hq hI).ι j).base '' S) =
      ⇑(annulusOverlapChart R I q).base ''
        (⇑((annulusChartTransitionInvSpf R I q hI).hom ≫
          annulusOverlapChartY R I q).base ⁻¹' S) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨s, hs, hzs⟩
    have hmem : ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base z ∈
        tateInvOverlap R I q hq hI i := by
      rw [tateInvOverlap_eq_range_ι_inter R I q hq hI h]
      exact ⟨⟨z, rfl⟩, ⟨s, hzs⟩⟩
    obtain ⟨p, ⟨w, hw⟩, hp⟩ := hmem
    have hzw : (annulusOverlapChart R I q).base w = z :=
      tateChainInv_ι_injective R I q hq hI i (by rw [hw]; exact hp)
    refine ⟨w, ?_, hzw⟩
    have hj : ⇑((tateChainInvFormalGlueData R I q hq hI).ι j).base s =
        ⇑((tateChainInvFormalGlueData R I q hq hI).ι j).base
          (⇑((annulusChartTransitionInvSpf R I q hI).hom ≫
            annulusOverlapChartY R I q).base w) := by
      rw [← base_ι_annulusOverlapChart (hq := hq) (hI := hI) h w, hzw]
      exact hzs
    have heq := tateChainInv_ι_injective R I q hq hI j hj
    exact Set.mem_preimage.2 (heq ▸ hs)
  · rintro z ⟨w, hw, rfl⟩
    exact ⟨_, hw, (base_ι_annulusOverlapChart (hq := hq) (hI := hI) h w).symm⟩

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **What the previous patch contributes.** The mirror of `preimage_ι_image_ι_forward`, read at
the pair `(j, i)`: the overlap is `tateInvOverlap j`, and
`AlgebraicGeometry.tateInvOverlap_eq_image_chartY` presents it as `ι i`'s image of the `y`-chart,
which is the form this direction needs. -/
theorem preimage_ι_image_ι_backward {i j : ULift.{u} ℤ} (h : j.down - i.down = -1)
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base ⁻¹'
        (⇑((tateChainInvFormalGlueData R I q hq hI).ι j).base '' S) =
      ⇑(annulusOverlapChartY R I q).base ''
        (⇑((annulusChartTransitionInvSpf R I q hI).inv ≫
          annulusOverlapChart R I q).base ⁻¹' S) := by
  have h' : i.down - j.down = 1 := by omega
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨s, hs, hzs⟩
    have hmem : ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base z ∈
        tateInvOverlap R I q hq hI j := by
      rw [tateInvOverlap_eq_range_ι_inter R I q hq hI h']
      exact ⟨⟨s, hzs⟩, ⟨z, rfl⟩⟩
    rw [tateInvOverlap_eq_image_chartY R I q hq hI h'] at hmem
    obtain ⟨p, ⟨w, hw⟩, hp⟩ := hmem
    have hzw : (annulusOverlapChartY R I q).base w = z :=
      tateChainInv_ι_injective R I q hq hI i (by rw [hw]; exact hp)
    refine ⟨w, ?_, hzw⟩
    have hj : ⇑((tateChainInvFormalGlueData R I q hq hI).ι j).base s =
        ⇑((tateChainInvFormalGlueData R I q hq hI).ι j).base
          (⇑((annulusChartTransitionInvSpf R I q hI).inv ≫
            annulusOverlapChart R I q).base w) := by
      rw [← base_ι_annulusOverlapChartY (hq := hq) (hI := hI) h w, hzw]
      exact hzs
    have heq := tateChainInv_ι_injective R I q hq hI j hj
    exact Set.mem_preimage.2 (heq ▸ hs)
  · rintro z ⟨w, hw, rfl⟩
    exact ⟨_, hw, (base_ι_annulusOverlapChartY (hq := hq) (hI := hI) h w).symm⟩

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **A non-adjacent patch contributes nothing.** `AlgebraicGeometry.tateChainInv_ι_range_disjoint`
(`FormalSchemes.TateActionInv`): the images of `U_i` and `U_j` in the chain are disjoint, so no
point of `U_i` can see `U_j`'s copy of `S`. Note the hypothesis `i ≠ j` is needed **in addition**
to the two numeric ones — the diagonal also satisfies `j - i ∉ {1, -1}`. -/
theorem preimage_ι_image_ι_far {i j : ULift.{u} ℤ} (hne : i ≠ j)
    (h1 : j.down - i.down ≠ 1) (h2 : j.down - i.down ≠ -1)
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base ⁻¹'
        (⇑((tateChainInvFormalGlueData R I q hq hI).ι j).base '' S) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun z hz => ?_
  obtain ⟨s, _, hs⟩ := hz
  exact Set.disjoint_left.1
    (tateChainInv_ι_range_disjoint R I q hq hI hne h1 h2) ⟨z, rfl⟩ ⟨s, hs⟩

section Chart

variable (hI)

/-- **The chain-free description of `AlgebraicGeometry.tateInvPatchSaturate`**: the open of the
model patch that a saturation sees, written from `S` by the two annulus charts alone.

`S`, together with the `x`-chart image of what the transition-then-`y`-chart leg pulls back from
`S`, together with the `y`-chart image of what the inverse leg pulls back. The two legs are exactly
those of `AlgebraicGeometry.IsTateInvChartCompatibleForward` and
`AlgebraicGeometry.IsTateInvChartCompatibleBackward`
(`FormalSchemes.TateInvOverlapBand`), so nothing new is introduced.

`tateInvPatchSaturate_eq_tateInvChartSaturate` is the theorem that this is the same set. The three
pieces are **not** claimed to be disjoint. -/
def tateInvChartSaturate
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)) :=
  S ∪
      ⇑(annulusOverlapChart R I q).base ''
        (⇑((annulusChartTransitionInvSpf R I q hI).hom ≫
          annulusOverlapChartY R I q).base ⁻¹' S) ∪
    ⇑(annulusOverlapChartY R I q).base ''
      (⇑((annulusChartTransitionInvSpf R I q hI).inv ≫
        annulusOverlapChart R I q).base ⁻¹' S)

end Chart

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The open of the model patch that a saturation sees is chain-free.** Splitting
`AlgebraicGeometry.tateInvSaturate`'s union by patch index and applying the three contribution
lemmas: `preimage_ι_image_ι_forward` at `⟨1⟩`, `preimage_ι_image_ι_backward` at `⟨-1⟩`,
`preimage_ι_image_ι_far` everywhere else, and injectivity of `ι ⟨0⟩` on the diagonal.

**This is what `FormalSchemes.TateInvOverlapBand` names as missing.** That file's module docstring
says of `tateInvPatchSaturateOpens` that "no chain-free description of it is on the tree"; this is
that description. The *definition* of `tateInvPatchSaturate` is unchanged and still goes through
`ι ⟨0⟩` — what is proved here is that the set it denotes has a description that does not. -/
theorem tateInvPatchSaturate_eq_tateInvChartSaturate
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    tateInvPatchSaturate hq hI S = tateInvChartSaturate hI S := by
  have hf : ((⟨(1 : ℤ)⟩ : ULift.{u} ℤ)).down - ((⟨(0 : ℤ)⟩ : ULift.{u} ℤ)).down = 1 := by
    change (1 : ℤ) - 0 = 1; omega
  have hb : ((⟨(-1 : ℤ)⟩ : ULift.{u} ℤ)).down - ((⟨(0 : ℤ)⟩ : ULift.{u} ℤ)).down = -1 := by
    change (-1 : ℤ) - 0 = -1; omega
  have hpre : tateInvPatchSaturate hq hI S =
      ⋃ m : ULift.{u} ℤ, ⇑((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base ⁻¹'
        (⇑((tateChainInvFormalGlueData R I q hq hI).ι m).base '' S) :=
    Set.preimage_iUnion
  rw [hpre, tateInvChartSaturate]
  refine Set.Subset.antisymm (Set.iUnion_subset fun m => ?_) ?_
  · by_cases h0 : m.down = 0
    · have hm : m = (⟨(0 : ℤ)⟩ : ULift.{u} ℤ) := ULift.down_injective h0
      subst hm
      rintro z ⟨y, hy, hyz⟩
      exact Or.inl (Or.inl (tateChainInv_ι_injective R I q hq hI ⟨(0 : ℤ)⟩ hyz ▸ hy))
    · by_cases h1 : m.down = 1
      · have hm : m = (⟨(1 : ℤ)⟩ : ULift.{u} ℤ) := ULift.down_injective h1
        subst hm
        rw [preimage_ι_image_ι_forward (hq := hq) (hI := hI) hf S]
        exact fun z hz => Or.inl (Or.inr hz)
      · by_cases h2 : m.down = -1
        · have hm : m = (⟨(-1 : ℤ)⟩ : ULift.{u} ℤ) := ULift.down_injective h2
          subst hm
          rw [preimage_ι_image_ι_backward (hq := hq) (hI := hI) hb S]
          exact fun z hz => Or.inr hz
        · have hne : (⟨(0 : ℤ)⟩ : ULift.{u} ℤ) ≠ m := fun hc => h0 (congrArg ULift.down hc).symm
          have hn1 : m.down - ((⟨(0 : ℤ)⟩ : ULift.{u} ℤ)).down ≠ 1 := by
            change m.down - (0 : ℤ) ≠ 1; omega
          have hn2 : m.down - ((⟨(0 : ℤ)⟩ : ULift.{u} ℤ)).down ≠ -1 := by
            change m.down - (0 : ℤ) ≠ -1; omega
          rw [preimage_ι_image_ι_far (hq := hq) (hI := hI) hne hn1 hn2 S]
          exact Set.empty_subset _
  · rintro z ((hz | hz) | hz)
    · exact Set.mem_iUnion.2 ⟨⟨(0 : ℤ)⟩, ⟨z, hz, rfl⟩⟩
    · refine Set.mem_iUnion.2 ⟨⟨(1 : ℤ)⟩, ?_⟩
      rw [preimage_ι_image_ι_forward (hq := hq) (hI := hI) hf S]
      exact hz
    · refine Set.mem_iUnion.2 ⟨⟨(-1 : ℤ)⟩, ?_⟩
      rw [preimage_ι_image_ι_backward (hq := hq) (hI := hI) hb S]
      exact hz

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **Membership in the description.** A point of the model patch is seen by the saturation of `S`
exactly when it lies in `S`, or is the `x`-chart image of a point the forward leg carries into `S`,
or is the `y`-chart image of a point the backward leg carries into `S`. The three disjuncts are
`Set.mem_union` and `Set.mem_image` unfolded, with the existentials reordered so that the equation
naming the point comes first. -/
theorem mem_tateInvChartSaturate_iff
    {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}
    {z : FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)} :
    z ∈ tateInvChartSaturate hI S ↔
      z ∈ S ∨
        (∃ w, (annulusOverlapChart R I q).base w = z ∧
          ⇑((annulusChartTransitionInvSpf R I q hI).hom ≫
            annulusOverlapChartY R I q).base w ∈ S) ∨
        (∃ w, (annulusOverlapChartY R I q).base w = z ∧
          ⇑((annulusChartTransitionInvSpf R I q hI).inv ≫
            annulusOverlapChart R I q).base w ∈ S) := by
  constructor
  · rintro ((hz | ⟨w, hw, hwz⟩) | ⟨w, hw, hwz⟩)
    · exact Or.inl hz
    · exact Or.inr (Or.inl ⟨w, hwz, hw⟩)
    · exact Or.inr (Or.inr ⟨w, hwz, hw⟩)
  · rintro (hz | ⟨w, hwz, hw⟩ | ⟨w, hwz, hw⟩)
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr ⟨w, hw, hwz⟩)
    · exact Or.inr ⟨w, hw, hwz⟩

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **`S` sits inside the description**, immediately, being the first of its three pieces. Through
`tateInvPatchSaturate_eq_tateInvChartSaturate` this recovers
`AlgebraicGeometry.subset_tateInvPatchSaturate` (`FormalSchemes.TateInvNodeChartRing`), which is
proved there from the saturation instead. -/
theorem subset_tateInvChartSaturate
    (S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
    S ⊆ tateInvChartSaturate hI S := fun _ hz => Or.inl (Or.inl hz)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The description at `S = ∅` is empty.** Each of the three pieces is: a preimage of `∅` is `∅`
and an image of `∅` is `∅`. Composed with `tateInvPatchSaturate_eq_tateInvChartSaturate` this is a
second proof of `AlgebraicGeometry.tateInvPatchSaturate_empty`
(`FormalSchemes.TateInvChartAnnulusRing`), which is derived there from
`AlgebraicGeometry.tateInvSaturate_empty` — a different route to the same value, and the check that
this file's description is not off by a term.

Proved through `mem_tateInvChartSaturate_iff` rather than by `simp`: the `Set.image_empty` and
`Set.preimage_empty` rewrites do not fire on these coercions, the same mismatch
`FormalSchemes.TateInvChartAnnulusRing` records for `tateInvSaturate`. -/
theorem tateInvChartSaturate_empty :
    tateInvChartSaturate (R := R) (I := I) (q := q) hI ∅ = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun z hz => by
    rcases mem_tateInvChartSaturate_iff.1 hz with h | ⟨_, _, hw⟩ | ⟨_, _, hw⟩
    · exact absurd h (Set.notMem_empty z)
    · exact absurd hw (Set.notMem_empty _)
    · exact absurd hw (Set.notMem_empty _)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The description at `S = Set.univ` is everything.** `Set.univ_union`, twice. Composed with
`tateInvPatchSaturate_eq_tateInvChartSaturate` it reproduces
`AlgebraicGeometry.tateInvPatchSaturate_univ` (`FormalSchemes.TateInvNodeChartRing`), proved there
from `AlgebraicGeometry.tateInvSaturate_univ` and joint surjectivity of the patch inclusions. -/
theorem tateInvChartSaturate_univ :
    tateInvChartSaturate (R := R) (I := I) (q := q) hI Set.univ = Set.univ := by
  simp only [tateInvChartSaturate, Set.univ_union]

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The description of an open is open.** Each of the three pieces is: `S` by hypothesis, and the
other two are images under the open maps `annulusOverlapChart` and `annulusOverlapChartY`
(`isOpenImmersion_annulusOverlapChart`, `isOpenImmersion_annulusOverlapChartY` — both at the root
namespace, unlike most of this cluster) of preimages of `S` under continuous maps.

Proved directly rather than transported from `AlgebraicGeometry.isOpen_tateInvPatchSaturate`, so
that `tateInvChartSaturateOpens` below does not depend on the chain. -/
theorem isOpen_tateInvChartSaturate
    {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}
    (hS : IsOpen S) : IsOpen (tateInvChartSaturate hI S) :=
  (hS.union ((isOpenImmersion_annulusOverlapChart R I q hI).base_open.isOpenMap _
      (hS.preimage ((annulusChartTransitionInvSpf R I q hI).hom ≫
        annulusOverlapChartY R I q).base.hom.continuous))).union
    ((isOpenImmersion_annulusOverlapChartY R I q hI).base_open.isOpenMap _
      (hS.preimage ((annulusChartTransitionInvSpf R I q hI).inv ≫
        annulusOverlapChart R I q).base.hom.continuous))

section ChartOpens

variable (hI)

/-- **The description, as an open of `Spf A`.** The counterpart of
`AlgebraicGeometry.tateInvPatchSaturateOpens` (`FormalSchemes.TateInvNodeChartGlue`), built from
`isOpen_tateInvChartSaturate` and mentioning no object of the chain. -/
def tateInvChartSaturateOpens
    {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}
    (hS : IsOpen S) :
    Opens (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)) :=
  ⟨tateInvChartSaturate hI S, isOpen_tateInvChartSaturate (hI := hI) hS⟩

end ChartOpens

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The two opens are equal.** The `Opens` form of
`tateInvPatchSaturate_eq_tateInvChartSaturate`, and the shape every downstream statement wants:
`AlgebraicGeometry.IsTateInvChartCompatibleForward` and its backward mirror are stated over
`tateInvPatchSaturateOpens hq hI hS`, and this says that open is `tateInvChartSaturateOpens hI
hS`. -/
theorem tateInvPatchSaturateOpens_eq_tateInvChartSaturateOpens
    {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}
    (hS : IsOpen S) :
    tateInvPatchSaturateOpens hq hI hS = tateInvChartSaturateOpens hI hS :=
  Opens.ext (tateInvPatchSaturate_eq_tateInvChartSaturate S)

section Transport

variable (hq hI)

/-- **A section over the chain-free open, read as a section over `tateInvPatchSaturateOpens`.**
The presheaf applied to the `eqToHom` of
`tateInvPatchSaturateOpens_eq_tateInvChartSaturateOpens`; an isomorphism, being the image of one,
but only the map is needed below. -/
def tateInvChartSaturateSection {S : Set (FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q))} (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvChartSaturateOpens hI hS))) :
    (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI hS)) :=
  (((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.map
    (eqToHom (congrArg op
      (tateInvPatchSaturateOpens_eq_tateInvChartSaturateOpens (hq := hq) hS).symm))).hom) s

end Transport

/-- **The overlap condition, read over the chain-free open.**
`AlgebraicGeometry.isTateInvOverlapCompatible_iff_charts`
(`FormalSchemes.TateInvOverlapBand`) with its ambient ring presented over
`tateInvChartSaturateOpens hI hS` instead of `tateInvPatchSaturateOpens hq hI hS`. There is no new
content in the proof — it is that theorem at the transported section — and the point is the
statement: the right-hand side names only `annulusOverlapChart`, `annulusOverlapChartY` and
`annulusChartTransitionInvSpf`, and the ring the section lives in is now presented over an open
built from `S` by those same charts.

**What still names the chain is the left-hand side**, `AlgebraicGeometry.IsTateInvOverlapCompatible`
itself, whose definition quantifies over the glue datum's pairs of indices. That is the thing being
characterised, and eliminating it is not what a characterisation does. -/
theorem isTateInvOverlapCompatible_iff_charts_chartSaturateOpens
    {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}
    (hS : IsOpen S)
    (s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvChartSaturateOpens hI hS))) :
    IsTateInvOverlapCompatible hS (tateInvChartSaturateSection hq hI hS s) ↔
      IsTateInvChartCompatibleForward hS (tateInvChartSaturateSection hq hI hS s) ∧
        IsTateInvChartCompatibleBackward hS (tateInvChartSaturateSection hq hI hS s) :=
  isTateInvOverlapCompatible_iff_charts hS _

end AlgebraicGeometry
