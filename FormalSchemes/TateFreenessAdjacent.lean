import FormalSchemes.TateFreeness
import FormalSchemes.GlueDataImageInter
import FormalSchemes.AnnulusOverlapProper

set_option linter.style.header false

/-!
# Full freeness of the `q^ℤ`-period action on the formal Tate chain

Fix an adic base `(R, I)` with `I` finitely generated, Noetherian `R`, and a topologically nilpotent
Tate parameter `q ∈ I`. The large-period freeness (`FormalSchemes.TateFreeness`,
`tateShiftAut_zpow_ne_one`) rules out every period of absolute value `≥ 2`; this file closes the
remaining adjacent case `n = ±1`, giving **full freeness** of the `q^ℤ`-action for `I ≠ ⊤`:
`σⁿ = 𝟙 ⇒ n = 0`.

Unlike the far translates, consecutive patches `U₀` and `U₁` *do* overlap (in `D(x)`), so proper
discontinuity does not apply. Instead we use:

* the image-intersection containment `range (ι i) ∩ range (ι j) ⊆ range (f i j ≫ ι i)`
  (`FormalSchemes.GlueDataImageInter`);
* that the overlap `D(x)` is a *proper* open of the patch — `x` a non-unit in the special fibre
  (`FormalSchemes.AnnulusOverlapProper`, `range_annulusOverlapChart_ne_univ`).

If `σ^{±1}` fixed `T` then a patch `U i` would coincide with its neighbour `U_{i±1}`; the two would
meet along their *whole* image, forcing the overlap inclusion `D(x) ↪ U i` to be surjective — i.e.
`D(x)` to be all of `U i`, contradicting properness.

## Main results

* `tateChain_range_ι_succ_ne`: for `I ≠ ⊤`, the patch `U i` and its neighbour `U_{i+1}` have
  distinct images in `T`.
* `tateShiftAut_zpow_ne_one_of_ne_zero`: for `I ≠ ⊤` and `n ≠ 0`, `σⁿ ≠ 𝟙` — **freeness**.
* `tateShiftAut_zpow_eq_one_iff`: `σⁿ = 𝟙 ↔ n = 0`.
* `tatePeriodAction_injective`: the `q^ℤ`-period action `ℤ → Aut T` is injective.

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

/-- Pre-composing with an `eqToHom` isomorphism does not change the underlying-space range. -/
private theorem range_eqToHom_comp {X Y Z : LocallyRingedSpace.{u}} (e : X = Y) (g : Y ⟶ Z) :
    Set.range (eqToHom e ≫ g).base = Set.range g.base := by subst e; simp

/-- The range of a composite morphism factors through the image of the second leg. -/
private theorem range_comp_base {X Y Z : LocallyRingedSpace.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    Set.range (a ≫ b).base = ⇑b.base '' Set.range ⇑a.base := by
  rw [LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp]

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The glue map of a forward step is the `x`-chart `D(x)`.** For `j.down = i.down + 1` the range
of the Tate-chain glue inclusion `f i j : V(i, j) ⟶ U i` equals the range of the overlap chart
`annulusOverlapChart` — the basic open `D(x) ⊆ Spf A`. -/
theorem tateChain_range_glueF_forward {i j : ULift.{u} ℤ} (h : j.down - i.down = 1) :
    Set.range ((tateChainLRSGlueData R I q hq hI).toGlueData.f i j).base =
      Set.range (annulusOverlapChart R I q).base := by
  have hne : i ≠ j := by rintro rfl; simp at h
  have hfeq : (tateChainLRSGlueData R I q hq hI).toGlueData.f i j =
      eqToHom (by
        simp only [tateChainLRSGlueData, CategoryTheory.GlueData.ofGlueData', dif_neg hne,
          tateChainGlueData']) ≫ tateF R I q i j := by
    simp only [tateChainLRSGlueData, CategoryTheory.GlueData.ofGlueData', GlueData'.f',
      dif_neg hne, tateChainGlueData']
  calc Set.range ((tateChainLRSGlueData R I q hq hI).toGlueData.f i j).base
      = Set.range (tateF R I q i j).base := by rw [hfeq]; exact range_eqToHom_comp _ _
    _ = Set.range (annulusOverlapChart R I q).base := by
        rw [tateF_forward R I q h]; exact range_eqToHom_comp _ _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Consecutive patches have distinct images.** For `I ≠ ⊤` and `j.down = i.down + 1`, the patch
`U i` and its neighbour `U j` do not have the same image in the glued Tate chain `T`. If they did,
the two pieces would meet along their entire image, forcing the overlap inclusion `D(x) ↪ U i` to be
surjective — i.e. `D(x)` to be all of `U i` — contradicting that `x` is a non-unit in the special
fibre (`range_annulusOverlapChart_ne_univ`). -/
theorem tateChain_range_ι_succ_ne (hItop : I ≠ ⊤) {i j : ULift.{u} ℤ} (hij : j.down = i.down + 1) :
    Set.range ((tateChainFormalGlueData R I q hq hI).ι i).base ≠
      Set.range ((tateChainFormalGlueData R I q hq hI).ι j).base := by
  intro heq
  have hstep : j.down - i.down = 1 := by rw [hij]; ring
  -- `range (ι i) ∩ range (ι j) ⊆ range (f i j ≫ ι i)`, and the two ranges coincide.
  have hsub :
      Set.range ((tateChainFormalGlueData R I q hq hI).ι i).base ∩
        Set.range ((tateChainFormalGlueData R I q hq hI).ι j).base ⊆
        Set.range ((tateChainLRSGlueData R I q hq hI).toGlueData.f i j ≫
          (tateChainFormalGlueData R I q hq hI).ι i).base :=
    LocallyRingedSpace.GlueData.range_ι_inter_subset (tateChainLRSGlueData R I q hq hI) i j
  rw [← heq, Set.inter_self] at hsub
  -- The composite range factors as `(ι i).base '' D(x)`.
  have hbase : Set.range
      ((tateChainLRSGlueData R I q hq hI).toGlueData.f i j ≫
        (tateChainFormalGlueData R I q hq hI).ι i).base =
      ((tateChainFormalGlueData R I q hq hI).ι i).base ''
        Set.range (annulusOverlapChart R I q).base := by
    rw [range_comp_base]
    congr 1
    exact tateChain_range_glueF_forward R I q hq hI hstep
  rw [hbase] at hsub
  -- `range (ι i) = (ι i).base '' univ`; injectivity forces `D(x) = univ`.
  have hoi : LocallyRingedSpace.IsOpenImmersion ((tateChainFormalGlueData R I q hq hI).ι i) :=
    inferInstance
  have hinj : Function.Injective
      ⇑((tateChainFormalGlueData R I q hq hI).ι i).base :=
    (PresheafedSpace.IsOpenImmersion.base_open
      (f := ((tateChainFormalGlueData R I q hq hI).ι i).toHom)).injective
  rw [← Set.image_univ, Set.image_subset_image_iff hinj, Set.univ_subset_iff] at hsub
  exact range_annulusOverlapChart_ne_univ R I q hq hI hItop hsub

/-- **Freeness of the `q^ℤ`-action.** For `I ≠ ⊤` and any nonzero period `n`, the shift power `σⁿ`
is not the identity automorphism of the formal Tate chain `T`. The large-period cases `|n| ≥ 2` are
`tateShiftAut_zpow_ne_one`; the adjacent cases `n = ±1` follow from `tateChain_range_ι_succ_ne`. -/
theorem tateShiftAut_zpow_ne_one_of_ne_zero {n : ℤ} (hItop : I ≠ ⊤) (hn : n ≠ 0) :
    (tateShiftAut R I q hq hI) ^ n ≠ 1 := by
  rcases eq_or_ne n 1 with rfl | hn1
  · -- `σ¹ = 𝟙` ⇒ `ι⟨0⟩` and `ι⟨1⟩` share a range, impossible.
    intro h
    have hhom : ((tateShiftAut R I q hq hI) ^ (1 : ℤ)).hom = 𝟙 _ := by rw [h]; rfl
    have hcov := ι_tateShiftAut_zpow R I q hq hI 1 ⟨0⟩
    have mcov : (tateChainFormalGlueData R I q hq hI).ι ⟨0⟩ =
        (tateChainFormalGlueData R I q hq hI).ι ⟨(⟨0⟩ : ULift.{u} ℤ).down + 1⟩ := by
      rw [← hcov, hhom]; exact (Category.comp_id _).symm
    exact tateChain_range_ι_succ_ne R I q hq hI hItop
      (i := ⟨0⟩) (j := ⟨(⟨0⟩ : ULift.{u} ℤ).down + 1⟩) rfl
      congr(Set.range ⇑($mcov).base)
  · rcases eq_or_ne n (-1) with rfl | hnm1
    · -- `σ⁻¹ = 𝟙` ⇒ `ι⟨-1⟩` and `ι⟨0⟩` share a range, impossible.
      intro h
      have hhom : ((tateShiftAut R I q hq hI) ^ (-1 : ℤ)).hom = 𝟙 _ := by rw [h]; rfl
      have hcov := ι_tateShiftAut_zpow R I q hq hI (-1) ⟨0⟩
      have mcov : (tateChainFormalGlueData R I q hq hI).ι ⟨0⟩ =
          (tateChainFormalGlueData R I q hq hI).ι ⟨(⟨0⟩ : ULift.{u} ℤ).down + -1⟩ := by
        rw [← hcov, hhom]; exact (Category.comp_id _).symm
      exact tateChain_range_ι_succ_ne R I q hq hI hItop
        (i := ⟨(⟨0⟩ : ULift.{u} ℤ).down + -1⟩) (j := ⟨0⟩) (by simp)
        congr(Set.range ⇑($mcov).base).symm
    · exact tateShiftAut_zpow_ne_one R I q hq hI hItop hn hn1 hnm1

/-- **Freeness, in packaged form.** For `I ≠ ⊤`, a shift power `σⁿ` is the identity iff `n = 0`. -/
theorem tateShiftAut_zpow_eq_one_iff {n : ℤ} (hItop : I ≠ ⊤) :
    (tateShiftAut R I q hq hI) ^ n = 1 ↔ n = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, zpow_zero]⟩
  by_contra hn
  exact tateShiftAut_zpow_ne_one_of_ne_zero R I q hq hI hItop hn h

/-- **The `q^ℤ`-period action is free.** For `I ≠ ⊤`, the group homomorphism
`tatePeriodAction : ℤ → Aut T` is injective: distinct periods act by distinct automorphisms. -/
theorem tatePeriodAction_injective (hItop : I ≠ ⊤) :
    Function.Injective (tatePeriodAction R I q hq hI) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  rw [tatePeriodAction_apply] at hn
  simpa [tateShiftAut_zpow_eq_one_iff R I q hq hI hItop] using hn

end AlgebraicGeometry
