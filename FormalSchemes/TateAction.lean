import FormalSchemes.TateShift
import FormalSchemes.TateChainStructMap
import FormalSchemes.GlueDataCarrier

set_option linter.style.header false

/-!
# The `q^ℤ`-period action on the formal Tate chain, over `Spf R`

Fix an adic base `(R, I)` with `I` finitely generated and Noetherian `R`, and a topologically
nilpotent Tate parameter `q ∈ I`. The formal Tate chain `T = tateChain R I q hq hI`
(`FormalSchemes.TateChainGlue`) is glued from the `ℤ`-indexed family of formal annuli `Spf A`
(`A = R{x, y} / (x·y − q)`); the shift automorphism `tateShiftIso : T ≅ T`
(`FormalSchemes.TateShift`) sends the patch `U_n` to `U_{n+1}`.

The `q^ℤ` naming is inherited from the pre-435 model: the shift is multiplication by `q` on the
**inversion-glued** chain (`FormalSchemes.TateActionInv`), whereas the swap gluing of this file
gives `x_{n+1} = q / x_n`. See the discussion in `FormalSchemes.TateShift` and the period note in
`FormalSchemes.TateCurveModel`.

This file packages the `q^ℤ`-action and its two defining geometric properties, following Bosch,
LNM 2105, §9:

## What this file provides

* `tateShiftAut`: the shift automorphism as an element of the group `Aut T`.
* `tatePeriodAction`: the group homomorphism `ℤ → Aut T`, `n ↦ σⁿ`, sending the additive generator
  `1` to the shift automorphism (via `zpowersHom`). The Tate curve model is the quotient by `σ²`,
  not by `σ` (issue 69); see the period note in `FormalSchemes.TateCurveModel`.
* `ι_tateShiftAut_zpow`: the **cover-shift law** `ι i ≫ (σⁿ).hom = ι ⟨i.down + n⟩` — the `n`-fold
  shift translates the patch `U_i` onto the patch `U_{i+n}`, computed by induction on `n : ℤ`.
* `tateShiftAut_zpow_comp_structMap`: the action is **over `Spf R`** — every `σⁿ` commutes with the
  structural morphism `tateChainStructMap : T ⟶ Spf R`.
* `tateShift_properlyDiscontinuous`: **proper discontinuity** — the patch `U_n` is disjoint from its
  translate `σᵏ(U_n) = U_{n+k}` whenever `k ∉ {−1, 0, 1}` (only consecutive patches overlap). This
  is the separation input the quotient construction of issue 69 consumes: away from the neighbouring
  translates the action moves each patch off itself, so the quotient map is a local isomorphism.

The **freeness** of the action — `σⁿ = 𝟙` forces `n = 0` — is a genuine follow-up: it needs the
annulus coordinate `x` to be a non-unit in `A ⧸ (I·A)` (equivalently `D(x) ≠ ⊤`, so that `U_0` is
not covered by a single overlap), which requires `I ≠ ⊤` and the nontriviality of the annulus
quotient. See the module note at the end.

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

/-- **The shift automorphism as an element of the automorphism group** `Aut T`: the `+1` index
shift `tateShiftIso`, the generator of the `q^ℤ`-action. -/
def tateShiftAut : CategoryTheory.Aut (tateChain R I q hq hI).toLocallyRingedSpace :=
  tateShiftIso R I q hq hI

/-- `tateShiftAut.hom` is the `+1`-shift `tateShift`, definitionally. -/
theorem tateShiftAut_hom : (tateShiftAut R I q hq hI).hom = tateShift R I q hq hI := rfl

/-- `tateShiftAut.inv` is the `-1`-shift `tateShiftInv`, definitionally. -/
theorem tateShiftAut_inv : (tateShiftAut R I q hq hI).inv = tateShiftInv R I q hq hI := rfl

/-! ### The period action as a group homomorphism `ℤ → Aut T` -/

/-- **The `q^ℤ`-period action** of the formal Tate chain: the group homomorphism
`ℤ → Aut T`, `n ↦ σⁿ`, sending the additive generator to the shift automorphism `tateShiftAut`.

The name is inherited: `σ` is multiplication by `q` on the *inversion-glued* chain
(`tateInvPeriodAction`), not on this swap-glued one. And the two-chart model is the quotient by
`σ²`, not by `σ` — see the period note in `FormalSchemes.TateCurveModel`. -/
def tatePeriodAction :
    Multiplicative ℤ →* CategoryTheory.Aut (tateChain R I q hq hI).toLocallyRingedSpace :=
  zpowersHom _ (tateShiftAut R I q hq hI)

theorem tatePeriodAction_apply (n : Multiplicative ℤ) :
    tatePeriodAction R I q hq hI n = (tateShiftAut R I q hq hI) ^ n.toAdd :=
  rfl

/-! ### The cover-shift law -/

/-- **The cover-shift law.** The `n`-fold shift `σⁿ` restricts along the inclusion `ι i` of the
patch `U_i` to the inclusion `ι ⟨i.down + n⟩` of the patch `U_{i+n}`: the `q^ℤ`-action translates
the cover by `n`. Proved by induction on `n : ℤ`, reducing each step to the merged `+1`/`−1`
restriction identities `ι_tateShift` / `ι_tateShiftInv`. -/
theorem ι_tateShiftAut_zpow (n : ℤ) (i : ULift.{u} ℤ) :
    (tateChainFormalGlueData R I q hq hI).ι i ≫ ((tateShiftAut R I q hq hI) ^ n).hom =
      (tateChainFormalGlueData R I q hq hI).ι ⟨i.down + n⟩ := by
  induction n generalizing i with
  | zero =>
    rw [zpow_zero]
    change (tateChainFormalGlueData R I q hq hI).ι i ≫ 𝟙 _ = _
    rw [Category.comp_id]
    congr 1
    exact ULift.down_injective (by simp)
  | succ k hk =>
    rw [zpow_add_one, Aut.Aut_mul_def, Iso.trans_hom, tateShiftAut_hom]
    erw [ι_tateShift_assoc, hk]
    congr 1
    exact ULift.down_injective (by simp only [tateShiftFun_down]; omega)
  | pred k hk =>
    rw [zpow_sub_one, Aut.Aut_mul_def, Iso.trans_hom, Aut.Aut_inv_def, Iso.symm_hom,
      tateShiftAut_inv]
    erw [ι_tateShiftInv_assoc, hk]
    congr 1
    exact ULift.down_injective (by simp only [tateShiftFunInv_down]; omega)

/-! ### The action is over `Spf R` -/

/-- The `i`-th inclusion followed by the glued structural morphism is the affine structural morphism
`annulusStructMap` of the patch `U_i`. -/
@[reassoc]
theorem ι_tateChainStructMap (i : ULift.{u} ℤ) :
    (tateChainFormalGlueData R I q hq hI).ι i ≫ tateChainStructMap R I q hq hI =
      annulusStructMap R I q hI :=
  (tateChainFormalGlueData R I q hq hI).ι_glueMorphisms _ _ i

/-- **The `q^ℤ`-action is over `Spf R`.** Every power `σⁿ` of the shift automorphism commutes with
the structural morphism `T ⟶ Spf R`: the shift permutes the patches `U_n`, all of which carry the
same affine structural morphism `annulusStructMap`, so the glued structural morphism is preserved.
Verified on each patch by the cover-shift law `ι_tateShiftAut_zpow`. -/
theorem tateShiftAut_zpow_comp_structMap (n : ℤ) :
    ((tateShiftAut R I q hq hI) ^ n).hom ≫ tateChainStructMap R I q hq hI =
      tateChainStructMap R I q hq hI := by
  apply (tateChainFormalGlueData R I q hq hI).hom_ext
  intro i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ tateChainStructMap R I q hq hI) (ι_tateShiftAut_zpow R I q hq hI n i)).trans
      ((ι_tateChainStructMap R I q hq hI ⟨i.down + n⟩).trans
        (ι_tateChainStructMap R I q hq hI i).symm))

/-- The shift automorphism itself is over `Spf R` (the case `n = 1` of
`tateShiftAut_zpow_comp_structMap`). -/
theorem tateShift_comp_structMap :
    tateShift R I q hq hI ≫ tateChainStructMap R I q hq hI = tateChainStructMap R I q hq hI := by
  apply (tateChainFormalGlueData R I q hq hI).hom_ext
  intro i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ tateChainStructMap R I q hq hI) (ι_tateShift R I q hq hI i)).trans
      ((ι_tateChainStructMap R I q hq hI (tateShiftFun i)).trans
        (ι_tateChainStructMap R I q hq hI i).symm))

/-! ### Proper discontinuity -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Non-adjacent patches have disjoint ranges.** If `i ≠ j` are indices whose difference is
neither `+1` nor `−1`, the patches `U_i`, `U_j` do not overlap: their images in `T` are disjoint.
This is the geometric crux of the Tate chain — a patch overlaps only its two neighbours — packaged
via the glue-data disjointness lemma `range_ι_disjoint_of_isEmpty_V` fed by the empty overlap
`tateV_far`. -/
theorem tateChain_ι_range_disjoint {i j : ULift.{u} ℤ} (hne : i ≠ j)
    (h1 : j.down - i.down ≠ 1) (h2 : j.down - i.down ≠ -1) :
    Disjoint (Set.range ((tateChainFormalGlueData R I q hq hI).ι i).base)
      (Set.range ((tateChainFormalGlueData R I q hq hI).ι j).base) := by
  apply LocallyRingedSpace.GlueData.range_ι_disjoint_of_isEmpty_V
  have hV : (tateChainFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.V (i, j) =
      tateV R I q i j := by
    simp only [tateChainFormalGlueData, tateChainLRSGlueData, CategoryTheory.GlueData.ofGlueData',
      dif_neg hne, tateChainGlueData']
  rw [hV, tateV_far R I q h1 h2]
  infer_instance

/-- **Proper discontinuity of the `q^ℤ`-action.** For any translation amount `k ∉ {−1, 0, 1}`, the
patch `U_n` is disjoint from its translate `σᵏ(U_n) = U_{n+k}`: the image of `U_n` and the image of
`ι n ≫ σᵏ` in `T` are disjoint. Only the two neighbouring translates (`k = ±1`) meet `U_n`, so the
`q^ℤ`-action moves every patch off itself away from its neighbours — the precise separation the Tate
curve quotient (issue 69) consumes to make the quotient map a local isomorphism. -/
theorem tateShift_properlyDiscontinuous (n : ULift.{u} ℤ) (k : ℤ)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hkm1 : k ≠ -1) :
    Disjoint (Set.range ((tateChainFormalGlueData R I q hq hI).ι n).base)
      (Set.range
        ((tateChainFormalGlueData R I q hq hI).ι n ≫
          ((tateShiftAut R I q hq hI) ^ k).hom).base) := by
  rw [ι_tateShiftAut_zpow]
  refine tateChain_ι_range_disjoint R I q hq hI (fun h => hk0 ?_) ?_ ?_
  · have := congrArg ULift.down h.symm; simpa using this
  · simp only; omega
  · simp only; omega

end AlgebraicGeometry
