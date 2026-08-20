import FormalSchemes.TateChainInvGlue
import FormalSchemes.GlueMorphisms
import FormalSchemes.TateShift

set_option linter.style.header false

/-!
# The `q^ℤ`-shift automorphism of the inversion-glued formal Tate chain

Fix an adic base `(R, I)` with `I` finitely generated and Noetherian `R`, and a topologically
nilpotent Tate parameter `q ∈ I`. The inversion-glued formal Tate chain
`T_inv = tateChainInv R I q hq hI` (`FormalSchemes.TateChainInvGlue`) is glued from the
`ℤ`-indexed family of formal annuli `Spf A` (`A = R{x, y} / (x·y − q)`) along the **𝔾m-inversion**
transition `annulusChartTransitionInvSpf`, i.e. along `x_n · y_{n+1} = 1`. This is the
identification the rerouted two-chart model `tateCurveModel` uses (issue 435 and successors);
the swap-glued chain `tateChain` of `FormalSchemes.TateShift` is glued by the identification that
reroute rejected (issue 606).

## A note on the period

Here the `q^ℤ` naming is accurate: `x_n · y_{n+1} = 1` together with `x_n · y_n = q` gives
`x_{n+1} = q · x_n`, so the one-patch shift `σ` really is multiplication by the Tate parameter, and
`T_inv/⟨σ⟩` is the Tate curve of period `q`. The two-chart model `tateCurveModel` glues `U₀` to `U₁`
along **both** overlaps, so it is `T_inv/⟨σ²⟩` — period `q²`, not `q`. See the period note in
`FormalSchemes.TateCurveModel`, and `FormalSchemes.TateQuotientMap` for the presentation.

This file is the `Inv` analogue of `FormalSchemes.TateShift`: it builds the `±1` index shifts of
`T_inv` and packages them as an automorphism. Nothing in `FormalSchemes.TateShift` is touched;
the two chains coexist until the migration of issue 606 lands in full.

## A warning about the two meanings of `Inv`

`FormalSchemes.TateShift` already has a declaration called `tateShiftInv`: it is the **`−1`-shift
of the swap chain**. Here `Inv` refers instead to the **chain** — the one glued by the
𝔾m-inversion. To keep the two apart, the declarations of this file suffix the chain rather than
the direction:

| this file          | meaning                       | swap-chain counterpart |
| ------------------ | ----------------------------- | ---------------------- |
| `tateInvShift`     | `+1` shift of `T_inv`         | `tateShift`            |
| `tateInvShiftBack` | `−1` shift of `T_inv`         | `tateShiftInv`         |
| `tateInvShiftIso`  | the shift automorphism of `T_inv` | `tateShiftIso`     |

## What this file provides

The abstract gluing criterion `tateChainInv_glueMorphisms_compat`, which both shifts below are
built from, lives in `FormalSchemes.TateChainInvGlue` beside the glue datum it unfolds — it is not
specific to shifts, and `tateChainInvStructMap` is the other instance of it (issue 621).

* `tateInvShift_overlap_forward_gen` / `tateInvShift_overlap_backward_gen`: for **any** index map
  `σ` preserving the index difference on an adjacent pair, the two per-patch inclusions
  `annulusOverlapChart(Y) ≫ ι (σ ·)` agree over the inversion chart transition. These are read off
  `CategoryTheory.GlueData.glue_condition` at the shifted indices.
* `tateInvShift` / `tateInvShiftBack`: the `+1` / `−1` self-maps of `T_inv`.
* `ι_tateInvShift` / `ι_tateInvShiftBack`: the defining `ι`-restriction identities.
* `tateInvShiftIso`: the shift packaged as an automorphism `T_inv ≅ T_inv`.

The index maps `tateShiftFun` / `tateShiftFunInv` on `ULift ℤ` and their round-trip identities are
about the index type alone — they never mention a glue datum — so they are reused verbatim from
`FormalSchemes.TateShift`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The adjacent-overlap cruxes -/

set_option maxHeartbeats 1600000 in
-- Unfolding `glue_condition` at the shifted indices through `ofGlueData'` is expensive; raise it.
/-- **The forward adjacent-overlap identity for a difference-preserving reindexing `σ`.** If `σ`
carries the adjacent pair `(i, j)` (with `j = i + 1`) to an adjacent pair `(σ i, σ j)` (still a
forward step), then the `x`-chart into `U (σ i)` agrees, over the 𝔾m-inversion chart transition
`Spf A{1/x} ≅ Spf A{1/y}`, with the `y`-chart into `U (σ j)`. This is exactly
`CategoryTheory.GlueData.glue_condition` at the shifted indices, unfolded through `ofGlueData'`.
`Inv` analogue of `tateShift_overlap_forward_gen`. -/
theorem tateInvShift_overlap_forward_gen [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
    (hq : q ∈ I) (hI : I.FG) (σ : ULift.{u} ℤ → ULift.{u} ℤ) {i j : ULift.{u} ℤ}
    (h1 : (σ j).down - (σ i).down = 1) :
    annulusOverlapChart R I q ≫ (tateChainInvFormalGlueData R I q hq hI).ι (σ i) =
      (annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q ≫
        (tateChainInvFormalGlueData R I q hq hI).ι (σ j) := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  have hij' : ¬ @Eq (ULift.{u} ℤ) (σ i) (σ j) := by
    intro h; rw [h] at h1; omega
  have hji' : ¬ @Eq (ULift.{u} ℤ) (σ j) (σ i) := fun h => hij' h.symm
  have key :=
    (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.glue_condition
      (σ i) (σ j)
  simp only [tateChainInvFormalGlueData, tateChainInvLRSGlueData, tateChainInvGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji',
    Category.assoc] at key
  rw [tateF_forward R I q h1, tateTInv, dif_pos h1,
    tateF_backward R I q (show (σ i).down - (σ j).down = -1 by omega)] at key
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  exact ((cancel_epi (eqToHom _)).mp key).symm

set_option maxHeartbeats 1600000 in
-- Unfolding `glue_condition` at the shifted indices through `ofGlueData'` is expensive; raise it.
/-- **The backward adjacent-overlap identity for a difference-preserving reindexing `σ`.** The
analogue of `tateInvShift_overlap_forward_gen` for a backward step `j = i - 1`. -/
theorem tateInvShift_overlap_backward_gen [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
    (hq : q ∈ I) (hI : I.FG) (σ : ULift.{u} ℤ → ULift.{u} ℤ) {i j : ULift.{u} ℤ}
    (h2 : (σ j).down - (σ i).down = -1) :
    annulusOverlapChartY R I q ≫ (tateChainInvFormalGlueData R I q hq hI).ι (σ i) =
      (annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapChart R I q ≫
        (tateChainInvFormalGlueData R I q hq hI).ι (σ j) := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  have hij' : ¬ @Eq (ULift.{u} ℤ) (σ i) (σ j) := by
    intro h; rw [h] at h2; omega
  have hji' : ¬ @Eq (ULift.{u} ℤ) (σ j) (σ i) := fun h => hij' h.symm
  have h1 : ¬ (σ j).down - (σ i).down = 1 := by omega
  have key :=
    (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.glue_condition
      (σ i) (σ j)
  simp only [tateChainInvFormalGlueData, tateChainInvLRSGlueData, tateChainInvGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji',
    Category.assoc] at key
  rw [tateF_backward R I q h2, tateTInv, dif_neg h1, dif_pos h2,
    tateF_forward R I q (show (σ i).down - (σ j).down = 1 by omega)] at key
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  exact ((cancel_epi (eqToHom _)).mp key).symm

/-! ### The shift self-maps of `T_inv` -/

/-- **The `+1`-shift self-map of the inversion-glued formal Tate chain** `T_inv ⟶ T_inv`, assembled
from the shifted inclusions `ι (tateShiftFun ·)` via `glueMorphisms`, using the criterion
`tateChainInv_glueMorphisms_compat` fed by the overlap cruxes. `Inv` analogue of `tateShift`. -/
def tateInvShift [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG) :
    (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶
      (tateChainInv R I q hq hI).toLocallyRingedSpace :=
  (tateChainInvFormalGlueData R I q hq hI).glueMorphisms
    (fun i => (tateChainInvFormalGlueData R I q hq hI).ι (tateShiftFun i))
    (tateChainInv_glueMorphisms_compat R I q hq hI _
      (fun i j h => tateInvShift_overlap_forward_gen R I q hq hI tateShiftFun (by
        simp only [tateShiftFun_down]; omega))
      (fun i j h => tateInvShift_overlap_backward_gen R I q hq hI tateShiftFun (by
        simp only [tateShiftFun_down]; omega)))

/-- **The `−1`-shift self-map of the inversion-glued formal Tate chain** `T_inv ⟶ T_inv`, the
inverse of `tateInvShift`, assembled from the inclusions `ι (tateShiftFunInv ·)`. `Inv` analogue of
`tateShiftInv` — note the different meaning of the two `Inv`s, explained in the module docstring. -/
def tateInvShiftBack [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I)
    (hI : I.FG) :
    (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶
      (tateChainInv R I q hq hI).toLocallyRingedSpace :=
  (tateChainInvFormalGlueData R I q hq hI).glueMorphisms
    (fun i => (tateChainInvFormalGlueData R I q hq hI).ι (tateShiftFunInv i))
    (tateChainInv_glueMorphisms_compat R I q hq hI _
      (fun i j h => tateInvShift_overlap_forward_gen R I q hq hI tateShiftFunInv (by
        simp only [tateShiftFunInv_down]; omega))
      (fun i j h => tateInvShift_overlap_backward_gen R I q hq hI tateShiftFunInv (by
        simp only [tateShiftFunInv_down]; omega)))

/-- The `+1`-shift restricts along `ι i` to `ι (tateShiftFun i)`. -/
@[reassoc (attr := simp)]
theorem ι_tateInvShift [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I)
    (hI : I.FG) (i : ULift.{u} ℤ) :
    (tateChainInvFormalGlueData R I q hq hI).ι i ≫ tateInvShift R I q hq hI =
      (tateChainInvFormalGlueData R I q hq hI).ι (tateShiftFun i) := by
  rw [tateInvShift, FormalScheme.GlueData.ι_glueMorphisms]

/-- The `−1`-shift restricts along `ι i` to `ι (tateShiftFunInv i)`. -/
@[reassoc (attr := simp)]
theorem ι_tateInvShiftBack [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I)
    (hI : I.FG) (i : ULift.{u} ℤ) :
    (tateChainInvFormalGlueData R I q hq hI).ι i ≫ tateInvShiftBack R I q hq hI =
      (tateChainInvFormalGlueData R I q hq hI).ι (tateShiftFunInv i) := by
  rw [tateInvShiftBack, FormalScheme.GlueData.ι_glueMorphisms]

/-! ### The shift automorphism -/

/-- **The `q^ℤ`-shift automorphism of the inversion-glued formal Tate chain** `T_inv ≅ T_inv`: the
`+1` index shift `tateInvShift`, with inverse the `−1` index shift `tateInvShiftBack`. The triangle
identities reduce, via `hom_ext`, to the round-trip identities `tateShiftFunInv_tateShiftFun` /
`tateShiftFun_tateShiftFunInv` of the index maps. `Inv` analogue of `tateShiftIso`. -/
def tateInvShiftIso [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I)
    (hI : I.FG) :
    (tateChainInv R I q hq hI).toLocallyRingedSpace ≅
      (tateChainInv R I q hq hI).toLocallyRingedSpace where
  hom := tateInvShift R I q hq hI
  inv := tateInvShiftBack R I q hq hI
  hom_inv_id := by
    apply (tateChainInvFormalGlueData R I q hq hI).hom_ext
    intro i
    erw [ι_tateInvShift_assoc, ι_tateInvShiftBack]
    rw [tateShiftFunInv_tateShiftFun]
    exact (Category.comp_id _).symm
  inv_hom_id := by
    apply (tateChainInvFormalGlueData R I q hq hI).hom_ext
    intro i
    erw [ι_tateInvShiftBack_assoc, ι_tateInvShift]
    rw [tateShiftFun_tateShiftFunInv]
    exact (Category.comp_id _).symm

end AlgebraicGeometry
