import FormalSchemes.TateActionInv
import FormalSchemes.AnnulusNontrivial
import FormalSchemes.GlueDataImageInter
import FormalSchemes.AnnulusOverlapProper

set_option linter.style.header false

/-!
# Freeness of the `q^ℤ`-period action on the inversion-glued formal Tate chain

Fix an adic base `(R, I)` with `I` finitely generated, Noetherian `R`, and a topologically nilpotent
Tate parameter `q ∈ I`. The `q^ℤ`-period action `tateInvPeriodAction : ℤ → Aut T_inv`
(`FormalSchemes.TateActionInv`) sends `n` to the `n`-fold shift `σⁿ` of the **inversion-glued**
formal Tate chain `T_inv = tateChainInv R I q hq hI` (`FormalSchemes.TateChainInvGlue`).

This file is the `Inv` analogue of `FormalSchemes.TateFreeness` and
`FormalSchemes.TateFreenessAdjacent` taken together: for `I ≠ ⊤` the action is **free**, i.e.
`σⁿ = 𝟙 ⇒ n = 0`, equivalently `tateInvPeriodAction` is injective. As in
`FormalSchemes.TateShiftInv`, `Inv` refers throughout to the **chain** — the one glued by the
𝔾m-inversion — never to the direction of a shift. Nothing in the swap-chain files is touched; the
two chains coexist until the migration of issue 606 lands in full.

The argument runs in two halves, exactly as for the swap chain.

**Large periods `|n| ≥ 2`.** Proper discontinuity (`tateInvShift_properlyDiscontinuous`) says the
patch `U₀` is disjoint from its translate `σⁿ(U₀) = U_n`, and `annulus_formalSpectrum_nonempty`
says (for `I ≠ ⊤`) that the patch is nonempty. If `σⁿ = 𝟙` then `U₀` and `σⁿ(U₀)` have the same
image, so a nonempty set would be disjoint from itself.

**Adjacent periods `n = ±1`.** Consecutive patches genuinely overlap, in `D(x)`, so proper
discontinuity does not apply. Instead: the image-intersection containment
`range (ι i) ∩ range (ι j) ⊆ range (f i j ≫ ι i)` (`FormalSchemes.GlueDataImageInter`) together
with properness of the overlap `D(x) ⊊ Spf A` (`range_annulusOverlapChart_ne_univ`). If `σ^{±1}`
fixed `T_inv` then `U i` would coincide with `U_{i±1}`, the two would meet along their whole image,
and the overlap inclusion `D(x) ↪ U i` would have to be surjective.

## How much of this is really about the *inversion* — the answer is: none of it

The issue that carved this file (606b) asked which of the four statements genuinely re-proves and
which is index bookkeeping shared with the swap chain. The answer is that **the whole argument is
transition-independent**, and the reason is visible in `tateChainInvGlueData'`: its `V` and `f`
fields are literally `tateV` and `tateF`, the same functions the swap datum uses, and only the
field `t` differs. Freeness reads the glue datum in exactly two ways — through the ranges of the
glue maps `f i j` (`tateChainInv_range_glueF_forward`) and through the ranges of the patch
inclusions `ι` — and neither passes through `t`. The geometric inputs
(`annulus_formalSpectrum_nonempty`, `annulusOverlapChart_range_disjoint`,
`range_annulusOverlapChart_ne_univ`) are statements about the affine annulus alone.

Concretely: `(tateChainInvLRSGlueData …).toGlueData.f i j` and its swap-chain counterpart are
**definitionally equal** — `CategoryTheory.GlueData.ofGlueData'` builds `f` out of `U`, `V` and `f`
only — so `tateChainInv_range_glueF_forward` could be discharged by `rfl`-transport from
`tateChain_range_glueF_forward`. It deliberately is not. Routing this file through
`FormalSchemes.TateFreenessAdjacent` would make the `Inv` subtree depend on files the migration of
issue 606 exists in order to retire, and it would rest the argument on a defeq between two large
glue-datum definitions. The proofs below are therefore self-contained mirrors; the sharing is
recorded here as a fact about the objects rather than exploited as a proof device.

## Main results

* `tateChainInv_range_ι_base_nonempty`: for `I ≠ ⊤`, the image of each patch inclusion `ι i` in
  `T_inv` is nonempty.
* `tateChainInv_range_glueF_forward`: the glue map of a forward step is the `x`-chart `D(x)`.
* `tateChainInv_range_ι_succ_ne`: for `I ≠ ⊤`, consecutive patches have distinct images in `T_inv`.
* `tateInvShiftAut_zpow_ne_one`: large-period freeness — for `I ≠ ⊤` and `n ∉ {−1, 0, 1}`,
  `σⁿ ≠ 𝟙`.
* `tateInvShiftAut_zpow_ne_one_of_ne_zero`: **freeness** — for `I ≠ ⊤` and `n ≠ 0`, `σⁿ ≠ 𝟙`.
* `tateInvShiftAut_zpow_eq_one_iff`: `σⁿ = 𝟙 ↔ n = 0`.
* `tateInvPeriodAction_injective`: the `q^ℤ`-period action `ℤ → Aut T_inv` is injective.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*], Ch. V (the Tate curve).
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-! ### Nonemptiness of the patches -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The image of each patch inclusion is nonempty.** For `I ≠ ⊤` the underlying space of the
annulus patch `Spf A` is nonempty (`annulus_formalSpectrum_nonempty`), so the range of the
inclusion `ι i : U i ⟶ T_inv` is a nonempty subset of `T_inv`. The patches are shared with the swap
chain, so this is the same statement as `tateChain_range_ι_base_nonempty` about the other glued
object. -/
theorem tateChainInv_range_ι_base_nonempty (hItop : I ≠ ⊤) (i : ULift.{u} ℤ) :
    (Set.range ((tateChainInvFormalGlueData R I q hq hI).ι i).base).Nonempty := by
  obtain ⟨p⟩ := annulus_formalSpectrum_nonempty R I q hq hItop
  exact ⟨_, Set.mem_range_self p⟩

/-! ### Large-period freeness -/

/-- **Large-period freeness of the `q^ℤ`-action on `T_inv`.** For `I ≠ ⊤` and any period `n` with
`|n| ≥ 2` (that is `n ∉ {−1, 0, 1}`), the shift power `σⁿ` is not the identity automorphism of the
inversion-glued formal Tate chain `T_inv`. Indeed if `σⁿ = 𝟙` then the inclusion of `U₀` and its
translate `ι₀ ≫ σⁿ = ι_n` have the same range, so proper discontinuity
(`tateInvShift_properlyDiscontinuous`) would force that nonempty range to be disjoint from
itself. -/
theorem tateInvShiftAut_zpow_ne_one {n : ℤ} (hItop : I ≠ ⊤)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hnm1 : n ≠ -1) :
    (tateInvShiftAut R I q hq hI) ^ n ≠ 1 := by
  intro h
  have hpd := tateInvShift_properlyDiscontinuous R I q hq hI ⟨0⟩ n hn0 hn1 hnm1
  have hhom : ((tateInvShiftAut R I q hq hI) ^ n).hom = 𝟙 _ := by rw [h]; rfl
  have hBA :
      (tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩ ≫ ((tateInvShiftAut R I q hq hI) ^ n).hom =
      (tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩ := by rw [hhom]; exact Category.comp_id _
  obtain ⟨x, hx⟩ := tateChainInv_range_ι_base_nonempty R I q hq hI hItop ⟨0⟩
  have hxB : x ∈ Set.range ((tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩ ≫
      ((tateInvShiftAut R I q hq hI) ^ n).hom).base := by rw [hBA]; exact hx
  exact (Set.disjoint_left.mp hpd hx) hxB

/-- **Large-period freeness, in eliminated form.** If a shift power `σⁿ` is the identity (with
`I ≠ ⊤`) then the period `n` lies in `{−1, 0, 1}`. Full freeness then reduces to excluding
`n = ±1`, which is `tateChainInv_range_ι_succ_ne` below. -/
theorem tateInvShiftAut_zpow_eq_one_imp {n : ℤ} (hItop : I ≠ ⊤)
    (h : (tateInvShiftAut R I q hq hI) ^ n = 1) : n = 0 ∨ n = 1 ∨ n = -1 := by
  by_contra hc
  rw [not_or, not_or] at hc
  exact tateInvShiftAut_zpow_ne_one R I q hq hI hItop hc.1 hc.2.1 hc.2.2 h

/-- **Large-period freeness for the period action** `tateInvPeriodAction : ℤ → Aut T_inv`: for
`I ≠ ⊤` and `n ∉ {−1, 0, 1}` the action element `tateInvPeriodAction n` is nontrivial. -/
theorem tateInvPeriodAction_apply_ne_one {n : ℤ} (hItop : I ≠ ⊤)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hnm1 : n ≠ -1) :
    tateInvPeriodAction R I q hq hI (Multiplicative.ofAdd n) ≠ 1 := by
  rw [tateInvPeriodAction_apply]
  simpa using tateInvShiftAut_zpow_ne_one R I q hq hI hItop hn0 hn1 hnm1

/-! ### The adjacent case -/

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The glue map of a forward step is the `x`-chart `D(x)`.** For `j.down = i.down + 1` the range
of the inversion-glued chain's glue inclusion `f i j : V(i, j) ⟶ U i` equals the range of the
overlap chart `annulusOverlapChart` — the basic open `D(x) ⊆ Spf A`. The glue datum's `f` field is
`tateF`, shared verbatim with the swap chain, so the transition never enters. -/
theorem tateChainInv_range_glueF_forward {i j : ULift.{u} ℤ} (h : j.down - i.down = 1) :
    Set.range ((tateChainInvLRSGlueData R I q hq hI).toGlueData.f i j).base =
      Set.range (annulusOverlapChart R I q).base := by
  have hne : i ≠ j := by rintro rfl; simp at h
  have hfeq : (tateChainInvLRSGlueData R I q hq hI).toGlueData.f i j =
      eqToHom (by
        simp only [tateChainInvLRSGlueData, CategoryTheory.GlueData.ofGlueData', dif_neg hne,
          tateChainInvGlueData']) ≫ tateF R I q i j := by
    simp only [tateChainInvLRSGlueData, CategoryTheory.GlueData.ofGlueData', GlueData'.f',
      dif_neg hne, tateChainInvGlueData']
  calc Set.range ((tateChainInvLRSGlueData R I q hq hI).toGlueData.f i j).base
      = Set.range (tateF R I q i j).base := by
        rw [hfeq]; exact LocallyRingedSpace.range_eqToHom_comp_base _ _
    _ = Set.range (annulusOverlapChart R I q).base := by
        rw [tateF_forward R I q h]; exact LocallyRingedSpace.range_eqToHom_comp_base _ _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Consecutive patches have distinct images.** For `I ≠ ⊤` and `j.down = i.down + 1`, the patch
`U i` and its neighbour `U j` do not have the same image in the inversion-glued chain `T_inv`. If
they did, the two pieces would meet along their entire image, forcing the overlap inclusion
`D(x) ↪ U i` to be surjective — i.e. `D(x)` to be all of `U i` — contradicting that `x` is a
non-unit in the special fibre (`range_annulusOverlapChart_ne_univ`). -/
theorem tateChainInv_range_ι_succ_ne (hItop : I ≠ ⊤) {i j : ULift.{u} ℤ}
    (hij : j.down = i.down + 1) :
    Set.range ((tateChainInvFormalGlueData R I q hq hI).ι i).base ≠
      Set.range ((tateChainInvFormalGlueData R I q hq hI).ι j).base := by
  intro heq
  have hstep : j.down - i.down = 1 := by rw [hij]; ring
  -- `range (ι i) ∩ range (ι j) ⊆ range (f i j ≫ ι i)`, and the two ranges coincide.
  have hsub :
      Set.range ((tateChainInvFormalGlueData R I q hq hI).ι i).base ∩
        Set.range ((tateChainInvFormalGlueData R I q hq hI).ι j).base ⊆
        Set.range ((tateChainInvLRSGlueData R I q hq hI).toGlueData.f i j ≫
          (tateChainInvFormalGlueData R I q hq hI).ι i).base :=
    LocallyRingedSpace.GlueData.range_ι_inter_subset (tateChainInvLRSGlueData R I q hq hI) i j
  rw [← heq, Set.inter_self] at hsub
  -- The composite range factors as `(ι i).base '' D(x)`.
  have hbase : Set.range
      ((tateChainInvLRSGlueData R I q hq hI).toGlueData.f i j ≫
        (tateChainInvFormalGlueData R I q hq hI).ι i).base =
      ((tateChainInvFormalGlueData R I q hq hI).ι i).base ''
        Set.range (annulusOverlapChart R I q).base := by
    rw [range_comp_base]
    congr 1
    exact tateChainInv_range_glueF_forward R I q hq hI hstep
  rw [hbase] at hsub
  -- `range (ι i) = (ι i).base '' univ`; injectivity forces `D(x) = univ`.
  have hinj : Function.Injective
      ⇑((tateChainInvFormalGlueData R I q hq hI).ι i).base :=
    (PresheafedSpace.IsOpenImmersion.base_open
      (f := ((tateChainInvFormalGlueData R I q hq hI).ι i).toHom)).injective
  rw [← Set.image_univ, Set.image_subset_image_iff hinj, Set.univ_subset_iff] at hsub
  exact range_annulusOverlapChart_ne_univ R I q hq hI hItop hsub

/-! ### Full freeness -/

/-- **Freeness of the `q^ℤ`-action on `T_inv`.** For `I ≠ ⊤` and any nonzero period `n`, the shift
power `σⁿ` is not the identity automorphism of the inversion-glued formal Tate chain. The
large-period cases `|n| ≥ 2` are `tateInvShiftAut_zpow_ne_one`; the adjacent cases `n = ±1` follow
from `tateChainInv_range_ι_succ_ne`. -/
theorem tateInvShiftAut_zpow_ne_one_of_ne_zero {n : ℤ} (hItop : I ≠ ⊤) (hn : n ≠ 0) :
    (tateInvShiftAut R I q hq hI) ^ n ≠ 1 := by
  rcases eq_or_ne n 1 with rfl | hn1
  · -- `σ¹ = 𝟙` ⇒ `ι⟨0⟩` and `ι⟨1⟩` share a range, impossible.
    intro h
    have hhom : ((tateInvShiftAut R I q hq hI) ^ (1 : ℤ)).hom = 𝟙 _ := by rw [h]; rfl
    have hcov := ι_tateInvShiftAut_zpow R I q hq hI 1 ⟨0⟩
    have mcov : (tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩ =
        (tateChainInvFormalGlueData R I q hq hI).ι ⟨(⟨0⟩ : ULift.{u} ℤ).down + 1⟩ := by
      rw [← hcov, hhom]; exact (Category.comp_id _).symm
    exact tateChainInv_range_ι_succ_ne R I q hq hI hItop
      (i := ⟨0⟩) (j := ⟨(⟨0⟩ : ULift.{u} ℤ).down + 1⟩) rfl
      congr(Set.range ⇑($mcov).base)
  · rcases eq_or_ne n (-1) with rfl | hnm1
    · -- `σ⁻¹ = 𝟙` ⇒ `ι⟨-1⟩` and `ι⟨0⟩` share a range, impossible.
      intro h
      have hhom : ((tateInvShiftAut R I q hq hI) ^ (-1 : ℤ)).hom = 𝟙 _ := by rw [h]; rfl
      have hcov := ι_tateInvShiftAut_zpow R I q hq hI (-1) ⟨0⟩
      have mcov : (tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩ =
          (tateChainInvFormalGlueData R I q hq hI).ι ⟨(⟨0⟩ : ULift.{u} ℤ).down + -1⟩ := by
        rw [← hcov, hhom]; exact (Category.comp_id _).symm
      exact tateChainInv_range_ι_succ_ne R I q hq hI hItop
        (i := ⟨(⟨0⟩ : ULift.{u} ℤ).down + -1⟩) (j := ⟨0⟩) (by simp)
        congr(Set.range ⇑($mcov).base).symm
    · exact tateInvShiftAut_zpow_ne_one R I q hq hI hItop hn hn1 hnm1

/-- **Freeness, in packaged form.** For `I ≠ ⊤`, a shift power `σⁿ` is the identity iff `n = 0`. -/
theorem tateInvShiftAut_zpow_eq_one_iff {n : ℤ} (hItop : I ≠ ⊤) :
    (tateInvShiftAut R I q hq hI) ^ n = 1 ↔ n = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, zpow_zero]⟩
  by_contra hn
  exact tateInvShiftAut_zpow_ne_one_of_ne_zero R I q hq hI hItop hn h

/-- **The `q^ℤ`-period action on `T_inv` is free.** For `I ≠ ⊤`, the group homomorphism
`tateInvPeriodAction : ℤ → Aut T_inv` is injective: distinct periods act by distinct
automorphisms. This is the input the quotient presentation of issue 606c consumes — note that the
quotient `𝔈_q = T_inv / ⟨σ²⟩` uses the subgroup generated by `σ²`, on which the action is free
because it is free on all of `σ^ℤ`. -/
theorem tateInvPeriodAction_injective (hItop : I ≠ ⊤) :
    Function.Injective (tateInvPeriodAction R I q hq hI) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  rw [tateInvPeriodAction_apply] at hn
  simpa [tateInvShiftAut_zpow_eq_one_iff R I q hq hI hItop] using hn

end AlgebraicGeometry
