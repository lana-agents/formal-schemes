import FormalSchemes.CoproductOpenImmersion
import FormalSchemes.GlueDataImageInter
import FormalSchemes.GraphCodiagonalClosedEmbedding
import FormalSchemes.TateDiagonalClosedCover
import FormalSchemes.TateGraphCodiagonalFactor
import FormalSchemes.TateSelfProductMixedGlue

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000
set_option maxRecDepth 8000

/-!
# Descending a mixed chart of the Tate self-product into the overlap summands

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`, and let
`A = R{x, y}/(x·y − q)`. The self fibre product `𝔈_q ×_{Spf R} 𝔈_q = tateSelfProductInv` is glued
from four copies of `Spf(A ⊗̂_R A)` indexed by `ULift (Bool × Bool)`, and the glued diagonal `Δ`
factors through the two *diagonal* charts `(c, c)`
(`range Δ.base = S_false ∪ S_true` with `S_c = range ((diagChart ≫ ι⟨(c,c)⟩).base)`).

Showing that the preimage of `range Δ.base` over a **mixed** chart `(b, ¬b)` is closed (EGA I
§10.15, the separatedness input for the Tate curve) begins with a purely topological step: a point
of the mixed chart whose image lies in a diagonal chart must come from the *overlap object* of the
two charts, and the overlap object is a coproduct of two affine summands. This file isolates that
step. Nothing here mentions a ring map, a graph lift, or a preimage criterion — those are the
companion, ring-theoretic half.

## Main results

* `AlgebraicGeometry.mixedChartDescent`: the general form. Given a factorisation of the glue
  datum's overlap inclusion through a chart `c : W ⟶ Spf(A ⊗̂_R A)` and the glue relation
  `c ≫ ι i = t ≫ c ≫ ι j`, a point `z` of the chart `i` whose image lies in
  `range ((diagChart ≫ ι j).base)` is `c.base v` for a `v : W` with
  `(t ≫ c).base v ∈ range (diagChart.base)`.
* `AlgebraicGeometry.mixedChartDescent_second_ft`, `..._first_ft`, `..._second_tf`, `..._first_tf`:
  the four instances, one per (mixed chart, diagonal chart) pair.
* `AlgebraicGeometry.mixedChartSplit_second_ft` and its three companions: the same four statements
  with `v` split over the two coproduct summands of the overlap object, which is the form the
  assembly consumes — `coprod.inᵢ ≫ t ≫ c` is the summand's transition composite.
* `AlgebraicGeometry.isClosed_coe_preimage_chartCover_of_isClosed_preimage`: transport of closedness
  from the affine chart to the corresponding member of `tateSelfProductChartCover`.
* `AlgebraicGeometry.isClosed_range_spfGraphCodiagX` and companions: the two graph pieces (and their
  factor-swapped variants) are closed in all of `Spf(A ⊗̂_R A)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open AlgebraicGeometry FormalSpectrum CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]

/-! ### A range-folding helper -/

/-- Precomposition can only shrink the range of the underlying map. -/
theorem range_comp_base_subset {X Y Z : LocallyRingedSpace.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    Set.range ⇑(a ≫ b).base ⊆ Set.range ⇑b.base := by
  rintro _ ⟨w, rfl⟩
  exact ⟨a.base w, rfl⟩

/-! ### The general descent step -/

/-- **Descent of a mixed-chart point into the overlap object.** Let `i ≠ j` be two charts of the
four-chart Tate self-product glue datum, let `c : W ⟶ Spf(A ⊗̂_R A)` be a morphism whose composite
with `ι i` absorbs the glue datum's overlap inclusion `f i j ≫ ι i` on ranges (`hf`), and let `t`
satisfy the glue relation `c ≫ ι i = t ≫ c ≫ ι j` (`hglue`).

If a point `z` of the chart `i` has `ι i z` in the range of `diagChart ≫ ι j`, then `z` comes from
a point `v` of `W`, and the transported point `(t ≫ c) v` lies on the affine diagonal. -/
theorem mixedChartDescent (hq : q ∈ I) (hI : I.FG) {W : LocallyRingedSpace.{u}}
    (i j : ULift.{u} (Bool × Bool))
    (c : W ⟶ (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.U i) (t : W ⟶ W)
    (hf : Set.range ⇑((tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.f i j ≫
          (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι i).base ⊆
        Set.range ⇑(c ≫ (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι i).base)
    (hglue : c ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι i =
      t ≫ c ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι j)
    (z : (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.U i)
    (hz : ((tateSelfProductFormalGlueDataInv R I q hq hI).ι i).base z ∈
      Set.range ⇑(diagChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι j).base) :
    ∃ v : W, z = c.base v ∧
      (t ≫ c).base v ∈ Set.range ⇑(diagChart R I q hI).base := by
  obtain ⟨p, hp⟩ := hz
  have hinjI : Function.Injective
      ⇑((tateSelfProductFormalGlueDataInv R I q hq hI).ι i).base :=
    ((tateSelfProductFormalGlueDataInv R I q hq hI).ι_isOpenImmersion i).base_open.injective
  have hinjJ : Function.Injective
      ⇑((tateSelfProductFormalGlueDataInv R I q hq hI).ι j).base :=
    ((tateSelfProductFormalGlueDataInv R I q hq hI).ι_isOpenImmersion j).base_open.injective
  have hmem : ((tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι i).base z ∈
      Set.range ⇑((tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι i).base ∩
        Set.range ⇑((tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι j).base :=
    ⟨⟨z, rfl⟩, ⟨(diagChart R I q hI).base p, hp⟩⟩
  obtain ⟨w, hw⟩ :=
    (tateSelfProductLRSGlueDataInv R I q hq hI).range_ι_inter_subset i j hmem
  obtain ⟨v, hv⟩ := hf ⟨w, rfl⟩
  rw [hw] at hv
  have hvz : c.base v = z := hinjI hv
  refine ⟨v, hvz.symm, p, ?_⟩
  apply hinjJ
  have hgpt := congrArg (fun m => m.base v) hglue
  simp only at hgpt
  have h1 : ((tateSelfProductFormalGlueDataInv R I q hq hI).ι j).base
        ((diagChart R I q hI).base p) =
      ((tateSelfProductFormalGlueDataInv R I q hq hI).ι i).base z := hp
  have h2 : ((tateSelfProductFormalGlueDataInv R I q hq hI).ι i).base z =
      (c ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι i).base v := by
    rw [← hvz]
    rfl
  exact h1.trans (h2.trans hgpt)

/-! ### Identifying the glue datum's overlap inclusions -/

section GlueF

/-- The glue datum's overlap inclusion for a pair of distinct charts is the corresponding merged
overlap chart, up to the `eqToHom` produced by `CategoryTheory.GlueData'.f'`; on ranges this makes
the former land inside the latter. -/
private theorem glueF_range_subset_second_ft (hq : q ∈ I) (hI : I.FG) :
    Set.range ⇑((tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.f
          ⟨(false, true)⟩ ⟨(false, false)⟩ ≫
        (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(false, true)⟩).base ⊆
      Set.range ⇑(secondFactorOverlapChart R I q hI ≫
        (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(false, true)⟩).base := by
  have hij : ({ down := (false, true) } : ULift.{u} (Bool × Bool)) ≠
      { down := (false, false) } := by decide
  rw [show (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.f
        ⟨(false, true)⟩ ⟨(false, false)⟩ ≫
      (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(false, true)⟩ =
      eqToHom (dif_neg hij) ≫ secondFactorOverlapChart R I q hI ≫
        (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(false, true)⟩ from by
      simp only [tateSelfProductLRSGlueDataInv, tateSelfProductGlueData'Inv,
        tateSelfProductGlueF, CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hij, Category.assoc]
      rfl]
  exact range_comp_base_subset _ _

private theorem glueF_range_subset_first_ft (hq : q ∈ I) (hI : I.FG) :
    Set.range ⇑((tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.f
          ⟨(false, true)⟩ ⟨(true, true)⟩ ≫
        (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(false, true)⟩).base ⊆
      Set.range ⇑(firstFactorOverlapChart R I q hI ≫
        (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(false, true)⟩).base := by
  have hij : ({ down := (false, true) } : ULift.{u} (Bool × Bool)) ≠
      { down := (true, true) } := by decide
  rw [show (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.f
        ⟨(false, true)⟩ ⟨(true, true)⟩ ≫
      (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(false, true)⟩ =
      eqToHom (dif_neg hij) ≫ firstFactorOverlapChart R I q hI ≫
        (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(false, true)⟩ from by
      simp only [tateSelfProductLRSGlueDataInv, tateSelfProductGlueData'Inv,
        tateSelfProductGlueF, CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hij, Category.assoc]
      rfl]
  exact range_comp_base_subset _ _

private theorem glueF_range_subset_second_tf (hq : q ∈ I) (hI : I.FG) :
    Set.range ⇑((tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.f
          ⟨(true, false)⟩ ⟨(true, true)⟩ ≫
        (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(true, false)⟩).base ⊆
      Set.range ⇑(secondFactorOverlapChart R I q hI ≫
        (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(true, false)⟩).base := by
  have hij : ({ down := (true, false) } : ULift.{u} (Bool × Bool)) ≠
      { down := (true, true) } := by decide
  rw [show (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.f
        ⟨(true, false)⟩ ⟨(true, true)⟩ ≫
      (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(true, false)⟩ =
      eqToHom (dif_neg hij) ≫ secondFactorOverlapChart R I q hI ≫
        (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(true, false)⟩ from by
      simp only [tateSelfProductLRSGlueDataInv, tateSelfProductGlueData'Inv,
        tateSelfProductGlueF, CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hij, Category.assoc]
      rfl]
  exact range_comp_base_subset _ _

private theorem glueF_range_subset_first_tf (hq : q ∈ I) (hI : I.FG) :
    Set.range ⇑((tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.f
          ⟨(true, false)⟩ ⟨(false, false)⟩ ≫
        (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(true, false)⟩).base ⊆
      Set.range ⇑(firstFactorOverlapChart R I q hI ≫
        (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(true, false)⟩).base := by
  have hij : ({ down := (true, false) } : ULift.{u} (Bool × Bool)) ≠
      { down := (false, false) } := by decide
  rw [show (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.f
        ⟨(true, false)⟩ ⟨(false, false)⟩ ≫
      (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(true, false)⟩ =
      eqToHom (dif_neg hij) ≫ firstFactorOverlapChart R I q hI ≫
        (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(true, false)⟩ from by
      simp only [tateSelfProductLRSGlueDataInv, tateSelfProductGlueData'Inv,
        tateSelfProductGlueF, CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hij, Category.assoc]
      rfl]
  exact range_comp_base_subset _ _

end GlueF

/-! ### The four concrete descent statements -/

/-- **Chart `(false, true)` against the diagonal chart `(false, false)`.** The two differ in the
second factor, so the overlap object is `Spf(A ⊗̂ A{1/x}) ⨿ Spf(A ⊗̂ A{1/y})`. -/
theorem mixedChartDescent_second_ft (hq : q ∈ I) (hI : I.FG)
    (z : locallyRingedSpaceObj
      (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)))
    (hz : ((tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(false, true)⟩ : ULift.{u} (Bool × Bool))).base z ∈
      Set.range ⇑(diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(false, false)⟩ : ULift.{u} (Bool × Bool))).base) :
    ∃ v : (dAX R I q ⨿ dAY R I q : LocallyRingedSpace.{u}),
      z = (secondFactorOverlapChart R I q hI).base v ∧
        ((tateSelfProductRightTransitionInv R I q hI).hom ≫
          secondFactorOverlapChart R I q hI).base v ∈
          Set.range ⇑(diagChart R I q hI).base :=
  mixedChartDescent R I q hq hI _ _ (secondFactorOverlapChart R I q hI)
    (tateSelfProductRightTransitionInv R I q hI).hom
    (glueF_range_subset_second_ft R I q hq hI)
    (tateSelfProduct_second_glue_condition_inv_ft R I q hq hI) z hz

/-- **Chart `(false, true)` against the diagonal chart `(true, true)`.** The two differ in the
first factor, so the overlap object is `Spf(A{1/x} ⊗̂ A) ⨿ Spf(A{1/y} ⊗̂ A)`. -/
theorem mixedChartDescent_first_ft (hq : q ∈ I) (hI : I.FG)
    (z : locallyRingedSpaceObj
      (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)))
    (hz : ((tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(false, true)⟩ : ULift.{u} (Bool × Bool))).base z ∈
      Set.range ⇑(diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(true, true)⟩ : ULift.{u} (Bool × Bool))).base) :
    ∃ v : (dXA R I q ⨿ dYA R I q : LocallyRingedSpace.{u}),
      z = (firstFactorOverlapChart R I q hI).base v ∧
        ((tateSelfProductFirstTransitionInv R I q hI).hom ≫
          firstFactorOverlapChart R I q hI).base v ∈
          Set.range ⇑(diagChart R I q hI).base :=
  mixedChartDescent R I q hq hI _ _ (firstFactorOverlapChart R I q hI)
    (tateSelfProductFirstTransitionInv R I q hI).hom
    (glueF_range_subset_first_ft R I q hq hI)
    (tateSelfProduct_first_glue_condition_inv_ft R I q hq hI) z hz

/-- **Chart `(true, false)` against the diagonal chart `(true, true)`** (second factor differs). -/
theorem mixedChartDescent_second_tf (hq : q ∈ I) (hI : I.FG)
    (z : locallyRingedSpaceObj
      (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)))
    (hz : ((tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(true, false)⟩ : ULift.{u} (Bool × Bool))).base z ∈
      Set.range ⇑(diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(true, true)⟩ : ULift.{u} (Bool × Bool))).base) :
    ∃ v : (dAX R I q ⨿ dAY R I q : LocallyRingedSpace.{u}),
      z = (secondFactorOverlapChart R I q hI).base v ∧
        ((tateSelfProductRightTransitionInv R I q hI).hom ≫
          secondFactorOverlapChart R I q hI).base v ∈
          Set.range ⇑(diagChart R I q hI).base :=
  mixedChartDescent R I q hq hI _ _ (secondFactorOverlapChart R I q hI)
    (tateSelfProductRightTransitionInv R I q hI).hom
    (glueF_range_subset_second_tf R I q hq hI)
    (tateSelfProduct_second_glue_condition_inv_tf R I q hq hI) z hz

/-- **Chart `(true, false)` against the diagonal chart `(false, false)`** (first factor differs). -/
theorem mixedChartDescent_first_tf (hq : q ∈ I) (hI : I.FG)
    (z : locallyRingedSpaceObj
      (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)))
    (hz : ((tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(true, false)⟩ : ULift.{u} (Bool × Bool))).base z ∈
      Set.range ⇑(diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(false, false)⟩ : ULift.{u} (Bool × Bool))).base) :
    ∃ v : (dXA R I q ⨿ dYA R I q : LocallyRingedSpace.{u}),
      z = (firstFactorOverlapChart R I q hI).base v ∧
        ((tateSelfProductFirstTransitionInv R I q hI).hom ≫
          firstFactorOverlapChart R I q hI).base v ∈
          Set.range ⇑(diagChart R I q hI).base :=
  mixedChartDescent R I q hq hI _ _ (firstFactorOverlapChart R I q hI)
    (tateSelfProductFirstTransitionInv R I q hI).hom
    (glueF_range_subset_first_tf R I q hq hI)
    (tateSelfProduct_first_glue_condition_inv_tf R I q hq hI) z hz

/-! ### Splitting over the two summands of the overlap object -/

/-- Split a descent conclusion over the two coproduct summands of the overlap object. -/
theorem coprodSplit {X Y : LocallyRingedSpace.{u}} {Z : LocallyRingedSpace.{u}}
    {c : (X ⨿ Y : LocallyRingedSpace.{u}) ⟶ Z} {t : (X ⨿ Y : LocallyRingedSpace.{u}) ⟶
      (X ⨿ Y : LocallyRingedSpace.{u})} {z : Z} {S : Set Z}
    (h : ∃ v : (X ⨿ Y : LocallyRingedSpace.{u}), z = c.base v ∧ (t ≫ c).base v ∈ S) :
    (∃ u : X, z = (coprod.inl ≫ c).base u ∧ (coprod.inl ≫ t ≫ c).base u ∈ S) ∨
      (∃ u : Y, z = (coprod.inr ≫ c).base u ∧ (coprod.inr ≫ t ≫ c).base u ∈ S) := by
  obtain ⟨v, hv, hmem⟩ := h
  rcases LocallyRingedSpace.coprod_base_mem_range (X := X) (Y := Y) v with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · exact Or.inl ⟨u, hv, hmem⟩
  · exact Or.inr ⟨u, hv, hmem⟩

/-- **Chart `(false, true)`, diagonal chart `(false, false)`, split over `dAX ⨿ dAY`.** -/
theorem mixedChartSplit_second_ft (hq : q ∈ I) (hI : I.FG)
    (z : locallyRingedSpaceObj
      (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)))
    (hz : ((tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(false, true)⟩ : ULift.{u} (Bool × Bool))).base z ∈
      Set.range ⇑(diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(false, false)⟩ : ULift.{u} (Bool × Bool))).base) :
    (∃ u : (dAX R I q : LocallyRingedSpace.{u}),
        z = (coprod.inl ≫ secondFactorOverlapChart R I q hI).base u ∧
          (coprod.inl ≫ (tateSelfProductRightTransitionInv R I q hI).hom ≫
            secondFactorOverlapChart R I q hI).base u ∈
            Set.range ⇑(diagChart R I q hI).base) ∨
      (∃ u : (dAY R I q : LocallyRingedSpace.{u}),
        z = (coprod.inr ≫ secondFactorOverlapChart R I q hI).base u ∧
          (coprod.inr ≫ (tateSelfProductRightTransitionInv R I q hI).hom ≫
            secondFactorOverlapChart R I q hI).base u ∈
            Set.range ⇑(diagChart R I q hI).base) :=
  coprodSplit (mixedChartDescent_second_ft R I q hq hI z hz)

/-- **Chart `(false, true)`, diagonal chart `(true, true)`, split over `dXA ⨿ dYA`.** -/
theorem mixedChartSplit_first_ft (hq : q ∈ I) (hI : I.FG)
    (z : locallyRingedSpaceObj
      (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)))
    (hz : ((tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(false, true)⟩ : ULift.{u} (Bool × Bool))).base z ∈
      Set.range ⇑(diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(true, true)⟩ : ULift.{u} (Bool × Bool))).base) :
    (∃ u : (dXA R I q : LocallyRingedSpace.{u}),
        z = (coprod.inl ≫ firstFactorOverlapChart R I q hI).base u ∧
          (coprod.inl ≫ (tateSelfProductFirstTransitionInv R I q hI).hom ≫
            firstFactorOverlapChart R I q hI).base u ∈
            Set.range ⇑(diagChart R I q hI).base) ∨
      (∃ u : (dYA R I q : LocallyRingedSpace.{u}),
        z = (coprod.inr ≫ firstFactorOverlapChart R I q hI).base u ∧
          (coprod.inr ≫ (tateSelfProductFirstTransitionInv R I q hI).hom ≫
            firstFactorOverlapChart R I q hI).base u ∈
            Set.range ⇑(diagChart R I q hI).base) :=
  coprodSplit (mixedChartDescent_first_ft R I q hq hI z hz)

/-- **Chart `(true, false)`, diagonal chart `(true, true)`, split over `dAX ⨿ dAY`.** -/
theorem mixedChartSplit_second_tf (hq : q ∈ I) (hI : I.FG)
    (z : locallyRingedSpaceObj
      (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)))
    (hz : ((tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(true, false)⟩ : ULift.{u} (Bool × Bool))).base z ∈
      Set.range ⇑(diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(true, true)⟩ : ULift.{u} (Bool × Bool))).base) :
    (∃ u : (dAX R I q : LocallyRingedSpace.{u}),
        z = (coprod.inl ≫ secondFactorOverlapChart R I q hI).base u ∧
          (coprod.inl ≫ (tateSelfProductRightTransitionInv R I q hI).hom ≫
            secondFactorOverlapChart R I q hI).base u ∈
            Set.range ⇑(diagChart R I q hI).base) ∨
      (∃ u : (dAY R I q : LocallyRingedSpace.{u}),
        z = (coprod.inr ≫ secondFactorOverlapChart R I q hI).base u ∧
          (coprod.inr ≫ (tateSelfProductRightTransitionInv R I q hI).hom ≫
            secondFactorOverlapChart R I q hI).base u ∈
            Set.range ⇑(diagChart R I q hI).base) :=
  coprodSplit (mixedChartDescent_second_tf R I q hq hI z hz)

/-- **Chart `(true, false)`, diagonal chart `(false, false)`, split over `dXA ⨿ dYA`.** -/
theorem mixedChartSplit_first_tf (hq : q ∈ I) (hI : I.FG)
    (z : locallyRingedSpaceObj
      (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)))
    (hz : ((tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(true, false)⟩ : ULift.{u} (Bool × Bool))).base z ∈
      Set.range ⇑(diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(false, false)⟩ : ULift.{u} (Bool × Bool))).base) :
    (∃ u : (dXA R I q : LocallyRingedSpace.{u}),
        z = (coprod.inl ≫ firstFactorOverlapChart R I q hI).base u ∧
          (coprod.inl ≫ (tateSelfProductFirstTransitionInv R I q hI).hom ≫
            firstFactorOverlapChart R I q hI).base u ∈
            Set.range ⇑(diagChart R I q hI).base) ∨
      (∃ u : (dYA R I q : LocallyRingedSpace.{u}),
        z = (coprod.inr ≫ firstFactorOverlapChart R I q hI).base u ∧
          (coprod.inr ≫ (tateSelfProductFirstTransitionInv R I q hI).hom ≫
            firstFactorOverlapChart R I q hI).base u ∈
            Set.range ⇑(diagChart R I q hI).base) :=
  coprodSplit (mixedChartDescent_first_tf R I q hq hI z hz)

/-! ### Transport of closedness from the affine chart to the cover -/

/-- **Chart transport.** A set of the glued Tate self-product has closed coe-preimage in the chart
`p` of `tateSelfProductChartCover` as soon as its preimage under the affine chart inclusion `ι p`
is closed. This is the `ψ`-step of `restrictPreimage_diagonal_diagChart`, stated once for an
arbitrary set. -/
theorem isClosed_coe_preimage_chartCover_of_isClosed_preimage (hq : q ∈ I) (hI : I.FG)
    (p : ULift.{u} (Bool × Bool))
    (S : Set ((tateSelfProductInv R I q hq hI).toLocallyRingedSpace))
    (h : IsClosed (⇑((tateSelfProductFormalGlueDataInv R I q hq hI).ι p).base ⁻¹' S)) :
    IsClosed (Subtype.val ⁻¹' S : Set (tateSelfProductChartCover R I q hq hI p)) := by
  have he_emb : IsOpenEmbedding
      ⇑((tateSelfProductFormalGlueDataInv R I q hq hI).ι p).base :=
    ((tateSelfProductFormalGlueDataInv R I q hq hI).ι_isOpenImmersion p).base_open
  refine ((he_emb.toIsEmbedding.toHomeomorph).isClosed_preimage).mp ?_
  exact h

/-! ### The two graph pieces are closed -/

section GraphPieces

variable [TopologicalSpace R] [IsAdicRing I] (hI : I.FG)

/-- The `x`-side graph piece is closed in all of `Spf(A ⊗̂_R A)`. -/
theorem isClosed_range_spfGraphCodiagX :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    IsClosed (Set.range ⇑(spfGraphCodiagX R I q hI).base) := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  exact (CompletedTensorProduct.isClosedEmbedding_map_graphCodiagX
    (R := R) (I := I) (q := q) hI).isClosed_range

/-- The `y`-side graph piece is closed in all of `Spf(A ⊗̂_R A)`. -/
theorem isClosed_range_spfGraphCodiagY :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    IsClosed (Set.range ⇑(spfGraphCodiagY R I q hI).base) := by
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  exact (CompletedTensorProduct.isClosedEmbedding_map_graphCodiagY
    (R := R) (I := I) (q := q) hI).isClosed_range

/-- The factor-swapped `x`-side graph piece is closed: `graphCodiagX ∘ comm` is surjective, being
the composite of a surjection with the commutativity isomorphism. -/
theorem isClosed_range_spfGraphCodiagXComm :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    IsClosed (Set.range ⇑(spfGraphCodiagXComm R I q hI).base) := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hsurj : Function.Surjective
      ⇑((CompletedTensorProduct.graphCodiagX (R := R) (I := I) (q := q) hI).comp
        (CompletedTensorProduct.commHom (R := R) (I := I) (A := annulusAlgebra R I q)
          (B := annulusAlgebra R I q) hI)) := by
    rw [RingHom.coe_comp]
    exact (CompletedTensorProduct.graphCodiagX_surjective hI).comp
      (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := annulusAlgebra R I q)
        (B := annulusAlgebra R I q) hI).surjective
  exact (FormalSpectrum.isClosedEmbedding_map_of_surjective _ _ _ _ hsurj).isClosed_range

/-- The factor-swapped `y`-side graph piece is closed. -/
theorem isClosed_range_spfGraphCodiagYComm :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    IsClosed (Set.range ⇑(spfGraphCodiagYComm R I q hI).base) := by
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hsurj : Function.Surjective
      ⇑((CompletedTensorProduct.graphCodiagY (R := R) (I := I) (q := q) hI).comp
        (CompletedTensorProduct.commHom (R := R) (I := I) (A := annulusAlgebra R I q)
          (B := annulusAlgebra R I q) hI)) := by
    rw [RingHom.coe_comp]
    exact (CompletedTensorProduct.graphCodiagY_surjective hI).comp
      (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := annulusAlgebra R I q)
        (B := annulusAlgebra R I q) hI).surjective
  exact (FormalSpectrum.isClosedEmbedding_map_of_surjective _ _ _ _ hsurj).isClosed_range

end GraphPieces

end AlgebraicGeometry
