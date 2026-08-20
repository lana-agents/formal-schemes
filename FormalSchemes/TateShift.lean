import FormalSchemes.TateChainGlue
import FormalSchemes.GlueMorphisms
import FormalSchemes.TateChainStructMap
import FormalSchemes.TateChartTransition

set_option linter.style.header false

/-!
# The `q^ℤ`-shift automorphism of the formal Tate chain

Fix an adic base `(R, I)` with `I` finitely generated and Noetherian `R`, and a topologically
nilpotent Tate parameter `q ∈ I`. The formal Tate chain `T = tateChain R I q hq hI`
(`FormalSchemes.TateChainGlue`) is glued from the `ℤ`-indexed family of formal annuli `Spf A`
(`A = R{x, y} / (x·y − q)`) along their consecutive overlaps `{x invertible} ≅ {y invertible}`.

The chain carries a canonical `+1` index shift: the map that sends patch `U_n` to patch `U_{n+1}`.

## What "`q^ℤ`" means here, and why it is inherited rather than accurate

The reading "the shift is multiplication by the Tate parameter `q`" is correct for the
**inversion-glued** chain `T_inv` (`FormalSchemes.TateShiftInv`), not for the swap-glued chain of
this file. Under the inversion gluing `x_n · y_{n+1} = 1` the relation `x_n · y_n = q` gives
`x_{n+1} = q · x_n`; under the *swap* gluing `y_{n+1} = x_n` of this file it gives instead
`x_{n+1} = q / x_n`, which is not a translation. That is the discrepancy issue 435 rerouted
`tateCurveModel` away from, and issue 606 is migrating the chain to match.

The `q^ℤ` labels are kept here because they name the declarations
(`tatePeriodAction` and friends), and renaming would be a large mechanical diff; the geometric
reading belongs to the `Inv` files. Note also that the two-chart model `tateCurveModel` is the
quotient by the **square** of the shift, hence has period `q²` — see the period note in
`FormalSchemes.TateCurveModel`.

## What this file provides

* `tateShiftFun` / `tateShiftFunInv`: the `+1` / `-1` index maps on `ULift.{u} ℤ`, together with
  their round-trip identities `tateShiftFunInv_tateShiftFun` / `tateShiftFun_tateShiftFunInv`.
* `tateChain_glueMorphisms_compat`: the abstract compatibility criterion for gluing a family
  `k : ∀ i, Spf A ⟶ Y` out of `T` — namely that the `x`- and `y`-charts agree over the chart
  transition on adjacent patches. Proved by the same four-case split as `tateChainStructMap`
  (diagonal / far / forward / backward); the adjacent cases just rewrite by the supplied hypotheses.
* `tateShift_overlap_forward_gen` / `tateShift_overlap_backward_gen`: for **any** index map `σ`
  preserving the index difference on an adjacent pair, the two per-patch inclusions
  `annulusOverlapChart(Y) ≫ ι (σ ·)` agree over the chart transition. These are read off
  `CategoryTheory.GlueData.glue_condition` at the shifted indices — the only genuinely new inputs.
* `tateShift` / `tateShiftInv`: the `+1` / `-1` self-maps of `T`, assembled from the shifted
  inclusions via `FormalScheme.GlueData.glueMorphisms` and the criterion above.
* `ι_tateShift` / `ι_tateShiftInv`: the defining `ι`-restriction identities.
* `tateShiftIso`: the shift packaged as an automorphism `T ≅ T`, its inverse being `tateShiftInv`;
  the two triangle identities follow from `hom_ext` and the round-trip identities of the index maps.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The shift maps on the index type `ULift ℤ` -/

/-- The `+1` shift of the index type `ULift ℤ`, sending patch `U_n` to patch `U_{n+1}`. -/
def tateShiftFun (i : ULift.{u} ℤ) : ULift.{u} ℤ := ⟨i.down + 1⟩

/-- The `-1` shift of the index type `ULift ℤ`, the inverse of `tateShiftFun`. -/
def tateShiftFunInv (i : ULift.{u} ℤ) : ULift.{u} ℤ := ⟨i.down - 1⟩

@[simp] theorem tateShiftFun_down (i : ULift.{u} ℤ) : (tateShiftFun i).down = i.down + 1 := rfl

@[simp] theorem tateShiftFunInv_down (i : ULift.{u} ℤ) :
    (tateShiftFunInv i).down = i.down - 1 := rfl

/-- Round-trip: applying the `+1` shift then the `-1` shift is the identity. -/
@[simp] theorem tateShiftFunInv_tateShiftFun (i : ULift.{u} ℤ) :
    tateShiftFunInv (tateShiftFun i) = i := by
  apply ULift.down_injective
  simp

/-- Round-trip: applying the `-1` shift then the `+1` shift is the identity. -/
@[simp] theorem tateShiftFun_tateShiftFunInv (i : ULift.{u} ℤ) :
    tateShiftFun (tateShiftFunInv i) = i := by
  apply ULift.down_injective
  simp

/-! ### The abstract gluing criterion -/

set_option maxHeartbeats 1600000 in
-- The four-case unfolding of the glue datum `ofGlueData'` produces a large term; raise the budget.
/-- **Abstract criterion for gluing a family of morphisms out of the Tate chain.** A family
`k i : Spf A ⟶ Y` is compatible with the gluing (i.e. satisfies the obligation of
`FormalScheme.GlueData.glueMorphisms`) as soon as the `x`- and `y`-charts agree with `k` over the
chart transition on each adjacent pair. The proof is the same four-case split as
`tateChainStructMap` (diagonal via `t_id`; far via initiality of the empty overlap; adjacent via
`hf` / `hb`). -/
theorem tateChain_glueMorphisms_compat [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
    (hq : q ∈ I) (hI : I.FG) {Y : LocallyRingedSpace.{u}}
    (k : ∀ _ : ULift.{u} ℤ, locallyRingedSpaceObj (annulusIdealOfDefinition R I q) ⟶ Y)
    (hf : ∀ i j : ULift.{u} ℤ, j.down - i.down = 1 →
      annulusOverlapChart R I q ≫ k i =
        (annulusChartTransitionSpf R I q hI).hom ≫ annulusOverlapChartY R I q ≫ k j)
    (hb : ∀ i j : ULift.{u} ℤ, j.down - i.down = -1 →
      annulusOverlapChartY R I q ≫ k i =
        (annulusChartTransitionSpf R I q hI).inv ≫ annulusOverlapChart R I q ≫ k j)
    (i j : ULift.{u} ℤ) :
    (tateChainFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.f i j ≫ k i =
      (tateChainFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.t i j ≫
        (tateChainFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.f j i ≫
          k j := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  by_cases hij : i = j
  · subst hij
    simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
  · have hij' : ¬ @Eq (ULift.{u} ℤ) i j := hij
    have hji' : ¬ @Eq (ULift.{u} ℤ) j i := fun h => hij h.symm
    simp only [tateChainFormalGlueData, tateChainLRSGlueData, tateChainGlueData',
      CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij',
      dif_neg hji', Category.assoc]
    by_cases h1 : j.down - i.down = 1
    · rw [tateF_forward R I q h1, tateT, dif_pos h1,
        tateF_backward R I q (show i.down - j.down = -1 by omega)]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [hf i j h1]
    · by_cases h2 : j.down - i.down = -1
      · rw [tateF_backward R I q h2, tateT, dif_neg h1, dif_pos h2,
          tateF_forward R I q (show i.down - j.down = 1 by omega)]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [hb i j h2]
      · haveI : IsEmpty (tateV R I q i j) := (tateV_far R I q h1 h2) ▸ inferInstance
        simp only [eqToHom_trans_assoc]
        congr 1
        exact (LocallyRingedSpace.isInitialOfIsEmpty (X := tateV R I q i j)).hom_ext _ _

/-! ### The adjacent-overlap cruxes -/

set_option maxHeartbeats 1600000 in
-- Unfolding `glue_condition` at the shifted indices through `ofGlueData'` is expensive; raise it.
/-- **The forward adjacent-overlap identity for a difference-preserving reindexing `σ`.** If `σ`
carries the adjacent pair `(i, j)` (with `j = i + 1`) to an adjacent pair `(σ i, σ j)` (still a
forward step), then the `x`-chart into `U (σ i)` agrees, over the chart transition
`Spf A{1/x} ≅ Spf A{1/y}`, with the `y`-chart into `U (σ j)`. This is exactly
`CategoryTheory.GlueData.glue_condition` at the shifted indices, unfolded through `ofGlueData'`. -/
theorem tateShift_overlap_forward_gen [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
    (hq : q ∈ I) (hI : I.FG) (σ : ULift.{u} ℤ → ULift.{u} ℤ) {i j : ULift.{u} ℤ}
    (h1 : (σ j).down - (σ i).down = 1) :
    annulusOverlapChart R I q ≫ (tateChainFormalGlueData R I q hq hI).ι (σ i) =
      (annulusChartTransitionSpf R I q hI).hom ≫ annulusOverlapChartY R I q ≫
        (tateChainFormalGlueData R I q hq hI).ι (σ j) := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  have hij' : ¬ @Eq (ULift.{u} ℤ) (σ i) (σ j) := by
    intro h; rw [h] at h1; omega
  have hji' : ¬ @Eq (ULift.{u} ℤ) (σ j) (σ i) := fun h => hij' h.symm
  have key :=
    (tateChainFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.glue_condition
      (σ i) (σ j)
  simp only [tateChainFormalGlueData, tateChainLRSGlueData, tateChainGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji',
    Category.assoc] at key
  rw [tateF_forward R I q h1, tateT, dif_pos h1,
    tateF_backward R I q (show (σ i).down - (σ j).down = -1 by omega)] at key
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  exact ((cancel_epi (eqToHom _)).mp key).symm

set_option maxHeartbeats 1600000 in
-- Unfolding `glue_condition` at the shifted indices through `ofGlueData'` is expensive; raise it.
/-- **The backward adjacent-overlap identity for a difference-preserving reindexing `σ`.** The
analogue of `tateShift_overlap_forward_gen` for a backward step `j = i - 1`. -/
theorem tateShift_overlap_backward_gen [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
    (hq : q ∈ I) (hI : I.FG) (σ : ULift.{u} ℤ → ULift.{u} ℤ) {i j : ULift.{u} ℤ}
    (h2 : (σ j).down - (σ i).down = -1) :
    annulusOverlapChartY R I q ≫ (tateChainFormalGlueData R I q hq hI).ι (σ i) =
      (annulusChartTransitionSpf R I q hI).inv ≫ annulusOverlapChart R I q ≫
        (tateChainFormalGlueData R I q hq hI).ι (σ j) := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  have hij' : ¬ @Eq (ULift.{u} ℤ) (σ i) (σ j) := by
    intro h; rw [h] at h2; omega
  have hji' : ¬ @Eq (ULift.{u} ℤ) (σ j) (σ i) := fun h => hij' h.symm
  have h1 : ¬ (σ j).down - (σ i).down = 1 := by omega
  have key :=
    (tateChainFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.glue_condition
      (σ i) (σ j)
  simp only [tateChainFormalGlueData, tateChainLRSGlueData, tateChainGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji',
    Category.assoc] at key
  rw [tateF_backward R I q h2, tateT, dif_neg h1, dif_pos h2,
    tateF_forward R I q (show (σ i).down - (σ j).down = 1 by omega)] at key
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  exact ((cancel_epi (eqToHom _)).mp key).symm

/-! ### The shift self-maps of `T` -/

/-- **The `+1`-shift self-map of the formal Tate chain** `T ⟶ T`, assembled from the shifted
inclusions `ι (tateShiftFun ·)` via `glueMorphisms`, using the criterion
`tateChain_glueMorphisms_compat` fed by the overlap cruxes. -/
def tateShift [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG) :
    (tateChain R I q hq hI).toLocallyRingedSpace ⟶ (tateChain R I q hq hI).toLocallyRingedSpace :=
  (tateChainFormalGlueData R I q hq hI).glueMorphisms
    (fun i => (tateChainFormalGlueData R I q hq hI).ι (tateShiftFun i))
    (tateChain_glueMorphisms_compat R I q hq hI _
      (fun i j h => tateShift_overlap_forward_gen R I q hq hI tateShiftFun (by
        simp only [tateShiftFun_down]; omega))
      (fun i j h => tateShift_overlap_backward_gen R I q hq hI tateShiftFun (by
        simp only [tateShiftFun_down]; omega)))

/-- **The `-1`-shift self-map of the formal Tate chain** `T ⟶ T`, the inverse of `tateShift`,
assembled from the inclusions `ι (tateShiftFunInv ·)`. -/
def tateShiftInv [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG) :
    (tateChain R I q hq hI).toLocallyRingedSpace ⟶ (tateChain R I q hq hI).toLocallyRingedSpace :=
  (tateChainFormalGlueData R I q hq hI).glueMorphisms
    (fun i => (tateChainFormalGlueData R I q hq hI).ι (tateShiftFunInv i))
    (tateChain_glueMorphisms_compat R I q hq hI _
      (fun i j h => tateShift_overlap_forward_gen R I q hq hI tateShiftFunInv (by
        simp only [tateShiftFunInv_down]; omega))
      (fun i j h => tateShift_overlap_backward_gen R I q hq hI tateShiftFunInv (by
        simp only [tateShiftFunInv_down]; omega)))

/-- The `+1`-shift restricts along `ι i` to `ι (tateShiftFun i)`. -/
@[reassoc (attr := simp)]
theorem ι_tateShift [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I)
    (hI : I.FG) (i : ULift.{u} ℤ) :
    (tateChainFormalGlueData R I q hq hI).ι i ≫ tateShift R I q hq hI =
      (tateChainFormalGlueData R I q hq hI).ι (tateShiftFun i) := by
  rw [tateShift, FormalScheme.GlueData.ι_glueMorphisms]

/-- The `-1`-shift restricts along `ι i` to `ι (tateShiftFunInv i)`. -/
@[reassoc (attr := simp)]
theorem ι_tateShiftInv [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I)
    (hI : I.FG) (i : ULift.{u} ℤ) :
    (tateChainFormalGlueData R I q hq hI).ι i ≫ tateShiftInv R I q hq hI =
      (tateChainFormalGlueData R I q hq hI).ι (tateShiftFunInv i) := by
  rw [tateShiftInv, FormalScheme.GlueData.ι_glueMorphisms]

/-! ### The shift automorphism -/

/-- **The `q^ℤ`-shift automorphism of the formal Tate chain** `T ≅ T`: the `+1` index shift
`tateShift`, with inverse the `-1` index shift `tateShiftInv`. The triangle identities reduce, via
`hom_ext`, to the round-trip identities `tateShiftFunInv_tateShiftFun` /
`tateShiftFun_tateShiftFunInv` of the index maps. -/
def tateShiftIso [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG) :
    (tateChain R I q hq hI).toLocallyRingedSpace ≅
      (tateChain R I q hq hI).toLocallyRingedSpace where
  hom := tateShift R I q hq hI
  inv := tateShiftInv R I q hq hI
  hom_inv_id := by
    apply (tateChainFormalGlueData R I q hq hI).hom_ext
    intro i
    erw [ι_tateShift_assoc, ι_tateShiftInv]
    rw [tateShiftFunInv_tateShiftFun]
    exact (Category.comp_id _).symm
  inv_hom_id := by
    apply (tateChainFormalGlueData R I q hq hI).hom_ext
    intro i
    erw [ι_tateShiftInv_assoc, ι_tateShift]
    rw [tateShiftFun_tateShiftFunInv]
    exact (Category.comp_id _).symm

end AlgebraicGeometry
