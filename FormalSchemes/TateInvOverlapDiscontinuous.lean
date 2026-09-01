import FormalSchemes.ActionDiscontinuous
import FormalSchemes.GlueDataImageInter
import FormalSchemes.TateActionInv

set_option linter.style.header false

/-!
# The patch overlaps of the inversion-glued Tate chain separate the one-step shift

`AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction`
(`FormalSchemes.TateInvPeriodNodePoint`) shows that the one-step shift `σ` on the inversion-glued
chain `T_inv` is **not** free and properly discontinuous: no neighbourhood of a node is separating.
That is a statement about the nodes, and this file is the complementary positive one — away from the
nodes, `σ` separates.

`tateInvShift_properlyDiscontinuous` (`FormalSchemes.TateActionInv`) says the patch `U_i` is
disjoint from `U_{i+k}` for `k ∉ {−1, 0, 1}`, and that is why a whole patch separates the **square**
action. It is not enough for `σ` itself, since `U_i` meets `U_{i±1}`. The observation here is that
the *overlap* `W_i := U_i ∩ U_{i+1}` does separate `σ`, and for a reason that has nothing to do with
patches being far apart:

* `W_i` and `W_{i+1}` both sit inside `U_{i+1}`, where they are the images of the two overlap charts
  `D(y)` and `D(x)` of the annulus `Spf A`. Those are disjoint, because `x · y = q` is topologically
  nilpotent so no point of the formal spectrum inverts both — `annulusOverlapChart_range_disjoint`
  (`FormalSchemes.TateOverlapDisjoint`), already on the tree as the input that degenerates the
  chain's triple overlaps.
* `W_i` and `W_j` for `|i − j| ≥ 2` are separated already, by `tateChainInv_ι_range_disjoint`.

Since `σ` translates the overlaps — `σᵏ(W_i) = W_{i+k}` — those two bullets are the whole of
`LocallyRingedSpace.IsProperlyDiscontinuousOn (tateInvPeriodAction …) (W_i)`.

## What this buys, and what it does not

Combined with `hasAffineChartAt_of_isProperlyDiscontinuousOn`
(`FormalSchemes.ActionQuotientChartAt`), it gives an affine formal chart of the quotient
`T_inv/⟨σ⟩` at the image of every point of every overlap. The two descriptions
`tateInvOverlap_eq_image_chartX` and `tateInvOverlap_eq_image_chartY` say that the two overlaps
meeting a patch `U_i` are the `ι i`-images of the chart loci `D(x)` and `D(y)` of `Spf A`, so the
points *not* covered are the `ι i`-images of the annulus's node locus `V(x, y)`. That residue is
`FormalSchemes.TateInvPeriodQuotientCharts`.

Nothing here weakens `LocallyRingedSpace.IsProperlyDiscontinuousOn` or
`LocallyRingedSpace.IsFreeProperlyDiscontinuous`: both are used at their existing definitions, and
the negative result they carry for `σ` is untouched and cited. The two are consistent because
`IsFreeProperlyDiscontinuous` asks for a separating neighbourhood of *every* point, and a node has
none.

## Main results

* `AlgebraicGeometry.tateInvOverlap`: the overlap `W_i = U_i ∩ U_{i+1}`, as the `ι i`-image of the
  `x`-chart locus of the annulus.
* `AlgebraicGeometry.tateInvOverlap_eq_image_chartY`: the same set is the `ι (i+1)`-image of the
  `y`-chart locus — the glue condition, read on ranges.
* `AlgebraicGeometry.tateInvOverlap_eq_range_ι_inter`: `W_i` is the intersection `U_i ∩ U_{i+1}`,
  so the name is the theorem it claims to be.
* `AlgebraicGeometry.tateInvOverlap_disjoint`: `W_i` and `W_j` are disjoint for `i ≠ j`.
* `AlgebraicGeometry.image_tateInvOverlap_tateInvShiftAut_zpow`: `σᵏ(W_i) = W_{i+k}`.
* `AlgebraicGeometry.tateInvOverlap_isProperlyDiscontinuousOn`: **the positive result** — every
  overlap separates the one-step shift.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

/-! ### An image manipulation for locally ringed spaces

It is stated over abstract locally ringed spaces and instantiated at the Tate chain below.
Instantiation is substitution, so nothing here re-elaborates at the chain's concrete types — the
rule `FormalSchemes.TateInvPeriodNodePoint` records for the annulus completions applies equally to
the glue datum, whose index type is only propositionally `ULift ℤ`.

The range counterpart used to sit here too, in an `Iso` form and an `eqToHom` form that this file
believed were two lemmas. They are one, three other files had restated one or the other of them,
and both now come from `FormalSchemes.LocallyRingedSpaceRange` (issue 1399). -/

/-- **Images compose**: the `b`-image of the `a`-image is the `(a ≫ b)`-image. The image form of
`range_comp_base`. -/
theorem image_comp_base {X Y Z : LocallyRingedSpace.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (s : Set X) :
    ⇑b.base '' (⇑a.base '' s) = ⇑(a ≫ b).base '' s := by
  rw [← Set.image_comp]
  rfl

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-! ### The glue datum's overlap inclusions, in terms of `tateF` -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Off the diagonal the inversion-glued datum's map `f i j` is `eqToHom ≫ tateF i j`, so it has the
range of `tateF i j`. The `eqToHom` is what `CategoryTheory.GlueData.ofGlueData'` inserts. -/
theorem range_tateChainInv_f {i j : ULift.{u} ℤ} (hij : i ≠ j) :
    Set.range ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.f
      i j).base = Set.range (tateF R I q i j).base := by
  have hij' : ¬ @Eq (ULift.{u} ℤ) i j := hij
  simp only [tateChainInvFormalGlueData, tateChainInvLRSGlueData, tateChainInvGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij']
  exact LocallyRingedSpace.range_eqToHom_comp_base _ _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The overlap inclusion is symmetric in its two indices**, on ranges. This is the glue condition
`f i j ≫ ι i = t i j ≫ f j i ≫ ι j` together with the invertibility of the transition `t i j`, and
it is what makes `W_i` a subset of *both* `U_i` and `U_{i+1}`. -/
theorem range_tateChainInv_f_comp_ι_symm (i j : ULift.{u} ℤ) :
    Set.range (((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.f
        i j ≫ (tateChainInvFormalGlueData R I q hq hI).ι i).base) =
      Set.range (((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.f
        j i ≫ (tateChainInvFormalGlueData R I q hq hI).ι j).base) := by
  have hgc :
      (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.f i j ≫
          (tateChainInvFormalGlueData R I q hq hI).ι i =
        (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.t i j ≫
          (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.f j i ≫
            (tateChainInvFormalGlueData R I q hq hI).ι j :=
    ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.glue_condition
      i j).symm
  rw [hgc]
  exact LocallyRingedSpace.range_iso_hom_comp_base (asIso
    ((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.t i j)) _

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- The forward overlap `V(i, i+1)` is the `x`-chart `Spf A{1/x}` for every `i`, so all the forward
overlap inclusions have the same range inside a patch. -/
theorem range_tateF_forward {i j : ULift.{u} ℤ} (h : j.down - i.down = 1) :
    Set.range (tateF R I q i j).base = Set.range (annulusOverlapChart R I q).base := by
  rw [tateF_forward R I q h]
  exact LocallyRingedSpace.range_eqToHom_comp_base _ _

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- The backward overlap `V(i, i−1)` is the `y`-chart `Spf A{1/y}` for every `i`. -/
theorem range_tateF_backward {i j : ULift.{u} ℤ} (h : j.down - i.down = -1) :
    Set.range (tateF R I q i j).base = Set.range (annulusOverlapChartY R I q).base := by
  rw [tateF_backward R I q h]
  exact LocallyRingedSpace.range_eqToHom_comp_base _ _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The patch inclusions are injective on underlying spaces, being open immersions. -/
theorem tateChainInv_ι_injective (i : ULift.{u} ℤ) :
    Function.Injective ((tateChainInvFormalGlueData R I q hq hI).ι i).base :=
  ((tateChainInvFormalGlueData R I q hq hI).ι_isOpenImmersion i).base_open.injective

/-! ### The overlaps -/

/-- **The overlap `W_i = U_i ∩ U_{i+1}`** of two consecutive patches of the inversion-glued chain:
the `ι i`-image of the `x`-chart locus `D(x) ⊆ Spf A`. Seen from the other side it is the
`ι (i+1)`-image of the `y`-chart locus `D(y)`, which is `tateInvOverlap_eq_image_chartY`. -/
def tateInvOverlap (i : ULift.{u} ℤ) : Set (tateChainInv R I q hq hI).toLocallyRingedSpace :=
  ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base ''
    Set.range (annulusOverlapChart R I q).base

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The definition, restated: `W_i` is the `ι i`-image of `D(x)`. -/
theorem tateInvOverlap_eq_image_chartX (i : ULift.{u} ℤ) :
    tateInvOverlap R I q hq hI i =
      ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base ''
        Set.range (annulusOverlapChart R I q).base :=
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The overlap is open: `D(x)` is the range of the open immersion `annulusOverlapChart`, and `ι i`
is an open map. -/
theorem isOpen_tateInvOverlap (i : ULift.{u} ℤ) : IsOpen (tateInvOverlap R I q hq hI i) :=
  ((tateChainInvFormalGlueData R I q hq hI).ι_isOpenImmersion i).base_open.isOpenMap _
    (isOpenImmersion_annulusOverlapChart R I q hI).base_open.isOpen_range

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The overlap seen from the other patch.** For `j = i + 1`, the set `W_i` is also the
`ι j`-image of the `y`-chart locus `D(y) ⊆ Spf A`. Together with `tateInvOverlap_eq_image_chartX`
this identifies the two overlaps meeting `U_j` with the two chart loci of the annulus, whose union
misses exactly the node locus `V(x, y)`.

The proof is the glue condition, transported along `range_tateChainInv_f` at both indices; every
step is a term-level `Eq.trans`, because rewriting inside the glue datum's `f` fails at `instances`
transparency (its index type is `ULift ℤ` only after unfolding a semireducible definition). -/
theorem tateInvOverlap_eq_image_chartY {i j : ULift.{u} ℤ} (h : j.down - i.down = 1) :
    tateInvOverlap R I q hq hI i =
      ⇑((tateChainInvFormalGlueData R I q hq hI).ι j).base ''
        Set.range (annulusOverlapChartY R I q).base := by
  have hj : j.down = i.down + 1 := by omega
  obtain rfl : j = (⟨i.down + 1⟩ : ULift.{u} ℤ) := ULift.down_injective hj
  have hne : i ≠ (⟨i.down + 1⟩ : ULift.{u} ℤ) := by
    intro hc
    have h' := congrArg ULift.down hc
    simp at h'
  calc tateInvOverlap R I q hq hI i
      = ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base ''
          Set.range (tateF R I q i ⟨i.down + 1⟩).base :=
        congrArg _ (range_tateF_forward R I q (i := i) (j := ⟨i.down + 1⟩) (by simp)).symm
    _ = ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base ''
          Set.range ((tateChainInvFormalGlueData R I q hq
            hI).toLocallyRingedSpaceGlueData.toGlueData.f i ⟨i.down + 1⟩).base :=
        congrArg _ (range_tateChainInv_f R I q hq hI hne).symm
    _ = Set.range (((tateChainInvFormalGlueData R I q hq
            hI).toLocallyRingedSpaceGlueData.toGlueData.f i ⟨i.down + 1⟩ ≫
          (tateChainInvFormalGlueData R I q hq hI).ι i).base) :=
        (range_comp_base _ _).symm
    _ = Set.range (((tateChainInvFormalGlueData R I q hq
            hI).toLocallyRingedSpaceGlueData.toGlueData.f ⟨i.down + 1⟩ i ≫
          (tateChainInvFormalGlueData R I q hq hI).ι ⟨i.down + 1⟩).base) :=
        range_tateChainInv_f_comp_ι_symm R I q hq hI i ⟨i.down + 1⟩
    _ = ⇑((tateChainInvFormalGlueData R I q hq hI).ι ⟨i.down + 1⟩).base ''
          Set.range ((tateChainInvFormalGlueData R I q hq
            hI).toLocallyRingedSpaceGlueData.toGlueData.f ⟨i.down + 1⟩ i).base :=
        range_comp_base _ _
    _ = ⇑((tateChainInvFormalGlueData R I q hq hI).ι ⟨i.down + 1⟩).base ''
          Set.range (tateF R I q ⟨i.down + 1⟩ i).base :=
        congrArg _ (range_tateChainInv_f R I q hq hI (Ne.symm hne))
    _ = ⇑((tateChainInvFormalGlueData R I q hq hI).ι ⟨i.down + 1⟩).base ''
          Set.range (annulusOverlapChartY R I q).base :=
        congrArg _ (range_tateF_backward R I q (i := ⟨i.down + 1⟩) (j := i) (by simp))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The overlap is the range of the glue datum's overlap inclusion** `f i j ≫ ι i`, for
`j = i + 1`. The three steps are the opening of `tateInvOverlap_eq_image_chartY`'s calculation,
named separately because `tateInvOverlap_eq_range_ι_inter` needs them on their own. -/
theorem tateInvOverlap_eq_range_f_comp_ι {i j : ULift.{u} ℤ} (h : j.down - i.down = 1) :
    tateInvOverlap R I q hq hI i =
      Set.range (((tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.f
        i j ≫ (tateChainInvFormalGlueData R I q hq hI).ι i).base) := by
  have hne : i ≠ j := by
    intro hc
    obtain rfl := hc
    omega
  calc tateInvOverlap R I q hq hI i
      = ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base ''
          Set.range (tateF R I q i j).base :=
        congrArg _ (range_tateF_forward R I q h).symm
    _ = ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base ''
          Set.range ((tateChainInvFormalGlueData R I q hq
            hI).toLocallyRingedSpaceGlueData.toGlueData.f i j).base :=
        congrArg _ (range_tateChainInv_f R I q hq hI hne).symm
    _ = Set.range (((tateChainInvFormalGlueData R I q hq
          hI).toLocallyRingedSpaceGlueData.toGlueData.f i j ≫
            (tateChainInvFormalGlueData R I q hq hI).ι i).base) :=
        (range_comp_base _ _).symm

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **`W_i` really is `U_i ∩ U_{i+1}`.** Every docstring here describes `tateInvOverlap` as the
intersection of two consecutive patches; this is that description as a theorem, so nothing depends
on reading the definition as a claim about ranges.

One inclusion is `LocallyRingedSpace.GlueData.range_ι_inter_subset`
(`FormalSchemes.GlueDataImageInter`) — two glued pieces meet only along the image of their overlap
object. The other is that the overlap inclusion lands in `U_i` by construction and in `U_{i+1}` by
the glue condition, which is `range_tateChainInv_f_comp_ι_symm`. -/
theorem tateInvOverlap_eq_range_ι_inter {i j : ULift.{u} ℤ} (h : j.down - i.down = 1) :
    tateInvOverlap R I q hq hI i =
      Set.range ((tateChainInvFormalGlueData R I q hq hI).ι i).base ∩
        Set.range ((tateChainInvFormalGlueData R I q hq hI).ι j).base := by
  refine Set.Subset.antisymm ?_ ?_
  · rw [tateInvOverlap_eq_range_f_comp_ι R I q hq hI h]
    refine Set.subset_inter ?_ ?_
    · rw [range_comp_base]
      exact Set.image_subset_range _ _
    · rw [range_tateChainInv_f_comp_ι_symm R I q hq hI i j, range_comp_base]
      exact Set.image_subset_range _ _
  · rw [tateInvOverlap_eq_range_f_comp_ι R I q hq hI h]
    exact (tateChainInvFormalGlueData R I q hq
      hI).toLocallyRingedSpaceGlueData.range_ι_inter_subset i j


omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Distinct overlaps are disjoint.** Three cases, and only the two adjacent ones carry content:
for `j = i ± 1` both overlaps live in the same patch, where they are `D(x)` and `D(y)` and
`annulusOverlapChart_range_disjoint` applies; otherwise the *patches* are already disjoint by
`tateChainInv_ι_range_disjoint`. -/
theorem tateInvOverlap_disjoint {i j : ULift.{u} ℤ} (hij : i ≠ j) :
    Disjoint (tateInvOverlap R I q hq hI i) (tateInvOverlap R I q hq hI j) := by
  by_cases h1 : j.down - i.down = 1
  · rw [tateInvOverlap_eq_image_chartY R I q hq hI h1]
    exact Set.disjoint_image_of_injective (tateChainInv_ι_injective R I q hq hI j)
      (annulusOverlapChart_range_disjoint R I q hq hI).symm
  · by_cases h2 : j.down - i.down = -1
    · rw [tateInvOverlap_eq_image_chartY R I q hq hI (show i.down - j.down = 1 by omega)]
      exact Set.disjoint_image_of_injective (tateChainInv_ι_injective R I q hq hI i)
        (annulusOverlapChart_range_disjoint R I q hq hI)
    · exact (tateChainInv_ι_range_disjoint R I q hq hI hij h1 h2).mono
        (Set.image_subset_range _ _) (Set.image_subset_range _ _)

/-- **The shift translates the overlaps**: `σᵏ(W_i) = W_{i+k}`. The cover-shift law
`ι_tateInvShiftAut_zpow` moves the patch inclusion, and the chart locus `D(x)` inside the patch is
the same set for every index. -/
theorem image_tateInvOverlap_tateInvShiftAut_zpow (k : ℤ) {i j : ULift.{u} ℤ}
    (h : j.down = i.down + k) :
    ⇑((tateInvShiftAut R I q hq hI) ^ k).hom.base '' tateInvOverlap R I q hq hI i =
      tateInvOverlap R I q hq hI j := by
  obtain rfl : j = (⟨i.down + k⟩ : ULift.{u} ℤ) := ULift.down_injective h
  rw [tateInvOverlap, tateInvOverlap, ← ι_tateInvShiftAut_zpow R I q hq hI k i]
  exact image_comp_base ((tateChainInvFormalGlueData R I q hq hI).ι i)
    ((tateInvShiftAut R I q hq hI ^ k).hom) (Set.range (annulusOverlapChart R I q).base)

/-- **Every overlap separates the one-step shift.** A nontrivial `σᵏ` carries `W_i` to `W_{i+k}`,
and `W_{i+k}` is disjoint from `W_i` because `k ≠ 0`.

This does not contradict `not_isFreeProperlyDiscontinuous_tateInvPeriodAction`
(`FormalSchemes.TateInvPeriodNodePoint`), which refutes the *neighbourhood* form: the overlaps do
not cover the chain, and a node has no separating neighbourhood at all. -/
theorem tateInvOverlap_isProperlyDiscontinuousOn (i : ULift.{u} ℤ) :
    LocallyRingedSpace.IsProperlyDiscontinuousOn (tateInvPeriodAction R I q hq hI)
      (tateInvOverlap R I q hq hI i) := by
  intro g hg
  have hk0 : g.toAdd ≠ 0 := fun h => hg (by simpa using h)
  rw [tateInvPeriodAction_apply,
    image_tateInvOverlap_tateInvShiftAut_zpow R I q hq hI g.toAdd (i := i) (j := ⟨i.down + g.toAdd⟩)
      rfl]
  exact (tateInvOverlap_disjoint R I q hq hI
    (fun hc => hk0 (by simpa using congrArg ULift.down hc))).symm

end AlgebraicGeometry
