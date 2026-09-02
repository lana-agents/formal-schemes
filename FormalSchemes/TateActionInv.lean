import FormalSchemes.TateShiftInv
import FormalSchemes.TateChainInvGlue
import FormalSchemes.GlueDataCarrier
import FormalSchemes.ActionQuotient

set_option linter.style.header false

/-!
# The `q^ℤ`-period action on the inversion-glued formal Tate chain, over `Spf R`

Fix an adic base `(R, I)` with `I` finitely generated and Noetherian `R`, and a topologically
nilpotent Tate parameter `q ∈ I`. The inversion-glued formal Tate chain
`T_inv = tateChainInv R I q hq hI` (`FormalSchemes.TateChainInvGlue`) is glued from the
`ℤ`-indexed family of formal annuli `Spf A` (`A = R{x, y} / (x·y − q)`) along `x_n · y_{n+1} = 1`;
the shift automorphism `tateInvShiftIso : T_inv ≅ T_inv` (`FormalSchemes.TateShiftInv`) sends the
patch `U_n` to `U_{n+1}`.

This file is the `…Inv` analogue of `FormalSchemes.TateAction` (and of the single result of
`FormalSchemes.TateActionQuotient`): it packages the `q^ℤ`-action on `T_inv` and its defining
geometric properties. Nothing in the swap-chain files is touched; the two chains coexist until the
migration of issue 606 lands in full.

As in `FormalSchemes.TateShiftInv`, `…Inv` here refers to the **chain** (glued by the 𝔾m-inversion),
never to the direction of a shift.

## What this file provides

* `tateInvShiftAut`: the shift automorphism as an element of the group `Aut T_inv`.
* `tateInvPeriodAction`: the group homomorphism `ℤ → Aut T_inv`, `n ↦ σⁿ`, sending the additive
  generator `1` to the shift automorphism (via `zpowersHom`).
* `ι_tateInvShiftAut_zpow`: the **cover-shift law** `ι i ≫ (σⁿ).hom = ι ⟨i.down + n⟩`, computed by
  induction on `n : ℤ`.
* `tateInvShiftAut_zpow_comp_structMap`: the action is **over `Spf R`** — every `σⁿ` commutes with
  the structural morphism `tateChainInvStructMap : T_inv ⟶ Spf R`.
* `tateInvShift_properlyDiscontinuous`: **proper discontinuity** — the patch `U_n` is disjoint from
  its translate `σᵏ(U_n) = U_{n+k}` whenever `k ∉ {−1, 0, 1}`. The geometric input
  (`tateV_far`, `range_ι_disjoint_of_isEmpty_V`) depends only on the patches and their overlaps,
  never on the transition, so it is the same statement for both chains.
* `tateChainInvStructMap_isActionInvariant`: the structural morphism is `IsActionInvariant` under
  `tateInvPeriodAction`, hence descends to any quotient of `T_inv` by the action.

## A note on the period

The generic fibre of the inversion gluing satisfies `x_n · y_{n+1} = 1` together with
`x_n · y_n = q`, so `x_{n+1} = q · x_n`: the shift `σ` built here is multiplication by `q`, and
`T_inv / ⟨σ⟩` is the Tate curve of period `q`. The two-chart model `tateCurveModel` glues `U₀` to
`U₁` along **both** overlaps, so it is the Néron 2-gon `T_inv / ⟨σ²⟩` — the Tate curve of period
`q²`. That is why the quotient presentation of issue 606c is stated for `σ²` and not for `σ`.

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

/-- **The shift automorphism as an element of the automorphism group** `Aut T_inv`: the `+1` index
shift `tateInvShiftIso`, the generator of the `q^ℤ`-action on the inversion-glued chain. -/
def tateInvShiftAut : CategoryTheory.Aut (tateChainInv R I q hq hI).toLocallyRingedSpace :=
  tateInvShiftIso R I q hq hI

/-- `tateInvShiftAut.hom` is the `+1`-shift `tateInvShift`, definitionally. -/
theorem tateInvShiftAut_hom : (tateInvShiftAut R I q hq hI).hom = tateInvShift R I q hq hI := rfl

/-- `tateInvShiftAut.inv` is the `−1`-shift `tateInvShiftBack`, definitionally. -/
theorem tateInvShiftAut_inv :
    (tateInvShiftAut R I q hq hI).inv = tateInvShiftBack R I q hq hI := rfl

/-! ### The period action as a group homomorphism `ℤ → Aut T_inv` -/

/-- **The `q^ℤ`-period action** of the inversion-glued formal Tate chain: the group homomorphism
`ℤ → Aut T_inv`, `n ↦ σⁿ`, sending the additive generator to the shift automorphism
`tateInvShiftAut`. `…Inv` analogue of `tatePeriodAction`. -/
def tateInvPeriodAction :
    Multiplicative ℤ →* CategoryTheory.Aut (tateChainInv R I q hq hI).toLocallyRingedSpace :=
  zpowersHom _ (tateInvShiftAut R I q hq hI)

theorem tateInvPeriodAction_apply (n : Multiplicative ℤ) :
    tateInvPeriodAction R I q hq hI n = (tateInvShiftAut R I q hq hI) ^ n.toAdd :=
  rfl

/-! ### The cover-shift law -/

/-- **The cover-shift law.** The `n`-fold shift `σⁿ` restricts along the inclusion `ι i` of the
patch `U_i` to the inclusion `ι ⟨i.down + n⟩` of the patch `U_{i+n}`: the `q^ℤ`-action translates
the cover by `n`. Proved by induction on `n : ℤ`, reducing each step to the `+1`/`−1` restriction
identities `ι_tateInvShift` / `ι_tateInvShiftBack`. -/
theorem ι_tateInvShiftAut_zpow (n : ℤ) (i : ULift.{u} ℤ) :
    (tateChainInvFormalGlueData R I q hq hI).ι i ≫ ((tateInvShiftAut R I q hq hI) ^ n).hom =
      (tateChainInvFormalGlueData R I q hq hI).ι ⟨i.down + n⟩ := by
  induction n generalizing i with
  | zero =>
    rw [zpow_zero]
    change (tateChainInvFormalGlueData R I q hq hI).ι i ≫ 𝟙 _ = _
    rw [Category.comp_id]
    congr 1
    exact ULift.down_injective (by simp)
  | succ k hk =>
    rw [zpow_add_one, Aut.Aut_mul_def, Iso.trans_hom, tateInvShiftAut_hom]
    erw [ι_tateInvShift_assoc, hk]
    congr 1
    exact ULift.down_injective (by simp only [tateShiftFun_down]; omega)
  | pred k hk =>
    rw [zpow_sub_one, Aut.Aut_mul_def, Iso.trans_hom, Aut.Aut_inv_def, Iso.symm_hom,
      tateInvShiftAut_inv]
    erw [ι_tateInvShiftBack_assoc, hk]
    congr 1
    exact ULift.down_injective (by simp only [tateShiftFunInv_down]; omega)

/-! ### The action is over `Spf R` -/

/-- The `i`-th inclusion followed by the glued structural morphism is the affine structural morphism
`annulusStructMap` of the patch `U_i`. -/
@[reassoc]
theorem ι_tateChainInvStructMap (i : ULift.{u} ℤ) :
    (tateChainInvFormalGlueData R I q hq hI).ι i ≫ tateChainInvStructMap R I q hq hI =
      annulusStructMap R I q hI :=
  (tateChainInvFormalGlueData R I q hq hI).ι_glueMorphisms _ _ i

/-- **The `q^ℤ`-action is over `Spf R`.** Every power `σⁿ` of the shift automorphism commutes with
the structural morphism `T_inv ⟶ Spf R`: the shift permutes the patches `U_n`, all of which carry
the same affine structural morphism `annulusStructMap`, so the glued structural morphism is
preserved. Verified on each patch by the cover-shift law `ι_tateInvShiftAut_zpow`. -/
theorem tateInvShiftAut_zpow_comp_structMap (n : ℤ) :
    ((tateInvShiftAut R I q hq hI) ^ n).hom ≫ tateChainInvStructMap R I q hq hI =
      tateChainInvStructMap R I q hq hI := by
  apply (tateChainInvFormalGlueData R I q hq hI).hom_ext
  intro i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ tateChainInvStructMap R I q hq hI)
      (ι_tateInvShiftAut_zpow R I q hq hI n i)).trans
      ((ι_tateChainInvStructMap R I q hq hI ⟨i.down + n⟩).trans
        (ι_tateChainInvStructMap R I q hq hI i).symm))

/-- The shift itself is over `Spf R` (the case `n = 1` of
`tateInvShiftAut_zpow_comp_structMap`). -/
theorem tateInvShift_comp_structMap :
    tateInvShift R I q hq hI ≫ tateChainInvStructMap R I q hq hI =
      tateChainInvStructMap R I q hq hI := by
  apply (tateChainInvFormalGlueData R I q hq hI).hom_ext
  intro i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ tateChainInvStructMap R I q hq hI) (ι_tateInvShift R I q hq hI i)).trans
      ((ι_tateChainInvStructMap R I q hq hI (tateShiftFun i)).trans
        (ι_tateChainInvStructMap R I q hq hI i).symm))

/-! ### Proper discontinuity -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Non-adjacent patches have disjoint ranges.** If `i ≠ j` are indices whose difference is
neither `+1` nor `−1`, the patches `U_i`, `U_j` do not overlap: their images in `T_inv` are
disjoint. The overlaps `tateV` and the inclusions `tateF` are shared with the swap chain, so this
is the same geometric statement as `tateChain_ι_range_disjoint`, only about the other glued
object. -/
theorem tateChainInv_ι_range_disjoint {i j : ULift.{u} ℤ} (hne : i ≠ j)
    (h1 : j.down - i.down ≠ 1) (h2 : j.down - i.down ≠ -1) :
    Disjoint (Set.range ((tateChainInvFormalGlueData R I q hq hI).ι i).base)
      (Set.range ((tateChainInvFormalGlueData R I q hq hI).ι j).base) := by
  apply LocallyRingedSpace.GlueData.range_ι_disjoint_of_isEmpty_V
  have hV :
      (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.V (i, j) =
        tateV R I q i j := by
    simp only [tateChainInvFormalGlueData, tateChainInvLRSGlueData,
      CategoryTheory.GlueData.ofGlueData', dif_neg hne, tateChainInvGlueData']
  rw [hV, tateV_far R I q h1 h2]
  infer_instance

/-- **Proper discontinuity of the `q^ℤ`-action.** For any translation amount `k ∉ {−1, 0, 1}`, the
patch `U_n` is disjoint from its translate `σᵏ(U_n) = U_{n+k}`. Only the two neighbouring
translates (`k = ±1`) meet `U_n`, so the `q^ℤ`-action moves every patch off itself away from its
neighbours — the separation input the quotient construction consumes to make the quotient map a
local isomorphism. -/
theorem tateInvShift_properlyDiscontinuous (n : ULift.{u} ℤ) (k : ℤ)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hkm1 : k ≠ -1) :
    Disjoint (Set.range ((tateChainInvFormalGlueData R I q hq hI).ι n).base)
      (Set.range
        ((tateChainInvFormalGlueData R I q hq hI).ι n ≫
          ((tateInvShiftAut R I q hq hI) ^ k).hom).base) := by
  rw [ι_tateInvShiftAut_zpow]
  refine tateChainInv_ι_range_disjoint R I q hq hI (fun h => hk0 ?_) ?_ ?_
  · have := congrArg ULift.down h.symm; simpa using this
  · simp only; omega
  · simp only; omega

/-! ### Action-invariance of the structural morphism -/

/-- **The structural morphism of the inversion-glued chain is action-invariant.** The morphism
`tateChainInvStructMap : T_inv ⟶ Spf R` is invariant under the `q^ℤ`-period action
`tateInvPeriodAction`: every power `σⁿ` of the shift automorphism commutes with it
(`tateInvShiftAut_zpow_comp_structMap`). Consequently it descends through any quotient of `T_inv`
by the action, in particular through `𝔈_q = T_inv / ⟨σ²⟩`. `…Inv` analogue of
`tateChainStructMap_isActionInvariant`. -/
theorem tateChainInvStructMap_isActionInvariant :
    IsActionInvariant (tateInvPeriodAction R I q hq hI) (tateChainInvStructMap R I q hq hI) := by
  intro g
  rw [tateInvPeriodAction_apply]
  exact tateInvShiftAut_zpow_comp_structMap R I q hq hI g.toAdd

end AlgebraicGeometry
