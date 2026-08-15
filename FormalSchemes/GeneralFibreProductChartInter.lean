import FormalSchemes.GeneralFibreProductBothProjectionLeft
import FormalSchemes.GeneralFibreProductBothProjectionRight
import FormalSchemes.GeneralFibreProductBothOverlapRange
import FormalSchemes.GlueDataImageInter
import FormalSchemes.BasicOpenImmersionLRS
import FormalSchemes.SpfMap

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The product chart of `X ×_{Spf R} Y` as a preimage intersection of the projections

For the fully general two-sided fibre product `X ×_{Spf R} Y` of two affine-charted glued formal
schemes `X` (charts `Spf(A i)`) and `Y` (charts `Spf(B j)`) over the affine adic base `Spf R`
(`FormalSchemes.GeneralFibreProductBothObject`), the glued space `P = X ×_{Spf R} Y` is covered by
the double completed-tensor charts `Spf(A_{p.1} ⊗̂_R B_{p.2})`, `p : JX × JY`, glued through the
`FormalScheme.GlueData` inclusions `ι p`. Each factor projection `pr₁ : P ⟶ X`, `pr₂ : P ⟶ Y`
restricts, along `ι p`, to the affine chart projections `Spf(inl)`, `Spf(inr)` followed by the glue
inclusions of `X`, `Y` (`ι_pr₁`, `ι_pr₂`).

This file records the geometric content that a point of `P` lies in the product chart `(i, j)`
**iff** its first projection lies in the `X`-chart `i` and its second projection lies in the
`Y`-chart `j`:

`range (ι (i,j)) = pr₁⁻¹ (range (ι_X i)) ∩ pr₂⁻¹ (range (ι_Y j))`.

Geometrically this is the compatibility of the product cover with the two factor covers; it is the
issue-426/430 crux input consumed by the diagonal/separatedness analysis of issue 400 (the
locally-closed-immersion diagonal of `X ×_{Spf R} Y ⟶ X × Y`).

## Main results

* `AlgebraicGeometry.BothChartedFibreDatumXY.range_ι_eq_pr_preimage_inter`: the range/preimage
  identity above.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

open scoped Classical

universe u

namespace AlgebraicGeometry

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable (D : BothChartedFibreDatumXY R I hI)

/-- **A point of the product `X ×_{Spf R} Y` lies in the chart `p = (i, j)` iff its first
projection lies in the `X`-chart `i` and its second projection lies in the `Y`-chart `j`.** On
underlying spaces the range of the glue inclusion `ι p` of the product cover equals the
intersection of the preimages under the two projections of the ranges of the `X`- and `Y`-glue
inclusions `ι_X p.1`, `ι_Y p.2`. This is the compatibility of the product cover with the two factor
covers (EGA I §10.7); it is the issue-426/430 crux consumed by the diagonal analysis of issue 400.

The three concreteness hypotheses `hV`/`hf`/`ht` pin the carried abstract glue of `D` to the
concrete `bothAlgData*` and are the same ones taken by `pr₁`/`pr₂` (holding by `rfl` for any
`ofAlgebraData`-built datum). -/
theorem range_ι_eq_pr_preimage_inter
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (p : D.JX × D.JY) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    letI := D.topologyA
    letI := D.isAdicA
    letI := D.topologyB
    letI := D.isAdicB
    Set.range (D.formalGlueData.ι p).base =
      (D.pr₁ hV hf ht).base ⁻¹' Set.range (D.xFormalGlueData.ι p.1).base ∩
      (D.pr₂ hV hf ht).base ⁻¹' Set.range (D.yFormalGlueData.ι p.2).base := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  letI := D.topologyA
  letI := D.isAdicA
  letI := D.topologyB
  letI := D.isAdicB
  apply Set.Subset.antisymm
  · -- ⊆ : a point of the chart projects into the two factor charts, by `ι_pr₁`/`ι_pr₂`.
    rintro x ⟨w, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Set.mem_preimage]
      have h1 : (D.pr₁ hV hf ht).base ((D.formalGlueData.ι p).base w) =
          (D.xFormalGlueData.ι p.1).base ((D.pr₁ChartSelf p).base w) :=
        congrArg (fun m => m.base w) (D.ι_pr₁ hV hf ht p)
      rw [h1]
      exact ⟨_, rfl⟩
    · rw [Set.mem_preimage]
      have h2 : (D.pr₂ hV hf ht).base ((D.formalGlueData.ι p).base w) =
          (D.yFormalGlueData.ι p.2).base ((D.pr₂ChartSelf p).base w) :=
        congrArg (fun m => m.base w) (D.ι_pr₂ hV hf ht p)
      rw [h2]
      exact ⟨_, rfl⟩
  · -- ⊇ : joint surjectivity gives some chart `p'`; if `p' = p` we are done, else we show the
    -- preimage point lies in the overlap `V(p', p)` and glue back to the chart `p`.
    rintro x ⟨hx1, hx2⟩
    rw [Set.mem_preimage] at hx1 hx2
    obtain ⟨p', w, rfl⟩ := D.formalGlueData.ι_jointly_surjective x
    by_cases hpp : p' = p
    · subst hpp
      exact ⟨w, rfl⟩
    · have h' : p' ≠ p := hpp
      -- Rewrite the projections of `x = ι_{p'} w` through `ι_pr₁`/`ι_pr₂` at `p'`.
      have hu1eq : (D.pr₁ hV hf ht).base ((D.formalGlueData.ι p').base w) =
          (D.xFormalGlueData.ι p'.1).base ((D.pr₁ChartSelf p').base w) :=
        congrArg (fun m => m.base w) (D.ι_pr₁ hV hf ht p')
      have hu2eq : (D.pr₂ hV hf ht).base ((D.formalGlueData.ι p').base w) =
          (D.yFormalGlueData.ι p'.2).base ((D.pr₂ChartSelf p').base w) :=
        congrArg (fun m => m.base w) (D.ι_pr₂ hV hf ht p')
      rw [hu1eq] at hx1
      rw [hu2eq] at hx2
      -- The overlap point `w` lies in the range of the product-overlap immersion `f p' p`.
      have hwmem : w ∈ Set.range (D.lrsGlueData.toGlueData.f p' p).base := by
        have hcgdf : D.lrsGlueData.toGlueData.f p' p =
            eqToHom (dif_neg h') ≫ D.f p' p h' := by
          simp only [BothChartedFibreDatum.lrsGlueData, BothChartedFibreDatum.glueData',
            CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
          exact dif_neg h'
        have hrange : Set.range ⇑(D.lrsGlueData.toGlueData.f p' p).base =
            Set.range ⇑(bothAlgDataF hI D.gX D.gY p' p h').base := by
          rw [hcgdf]
          refine (range_eqToHom_comp_base _ _).trans ?_
          rw [hf p' p h']
          exact range_eqToHom_comp_base _ _
        rw [hrange, range_bothAlgDataF_base]
        refine ⟨?_, ?_⟩
        · -- first coordinate
          by_cases h1 : p'.1 = p.1
          · rw [if_pos h1]
            exact Set.mem_univ _
          · rw [if_neg h1]
            -- Goal: `w ∈ D(inl (gX p'.1 p.1))`.
            -- Establish `(pr₁ChartSelf p').base w ∈ D(gX p'.1 p.1)` via the `X`-glue overlap.
            have hxf : D.xLrsGlueData.toGlueData.f p'.1 p.1 =
                eqToHom (dif_neg h1) ≫
                  basicOpenChart (I.map (algebraMap R (D.A p'.1))) (D.gX p'.1 p.1) := by
              simp only [xLrsGlueData, xGlueData', CategoryTheory.GlueData.ofGlueData',
                CategoryTheory.GlueData'.f', dif_neg h1]
              rfl
            have hxf_range : Set.range (D.xLrsGlueData.toGlueData.f p'.1 p.1).base =
                (basicOpen (I.map (algebraMap R (D.A p'.1))) (D.gX p'.1 p.1) :
                  Set (FormalSpectrum (I.map (algebraMap R (D.A p'.1))))) := by
              rw [hxf]
              exact (range_eqToHom_comp_base _ _).trans
                (range_basicOpenChart_base _ _ (hI.map (algebraMap R (D.A p'.1))))
            -- `(ι_X p'.1) u` lies in the intersection of the two `X`-chart ranges.
            have hmem := D.xLrsGlueData.range_ι_inter_subset p'.1 p.1
              ⟨⟨(D.pr₁ChartSelf p').base w, rfl⟩, hx1⟩
            obtain ⟨v, hv⟩ := hmem
            have hinj :=
              ((D.xFormalGlueData.ι_isOpenImmersion p'.1).base_open).injective
            have hv' : (D.xFormalGlueData.ι p'.1).base
                  ((D.xLrsGlueData.toGlueData.f p'.1 p.1).base v) =
                (D.xFormalGlueData.ι p'.1).base ((D.pr₁ChartSelf p').base w) := hv
            have hu1 : (D.pr₁ChartSelf p').base w ∈
                (basicOpen (I.map (algebraMap R (D.A p'.1))) (D.gX p'.1 p.1) :
                  Set (FormalSpectrum (I.map (algebraMap R (D.A p'.1))))) :=
              hxf_range ▸ ⟨v, hinj hv'⟩
            -- Transport the membership along `pr₁ChartSelf p' = Spf(inl)`.
            have hset : (↑(basicOpen (idealOfDefinition R I (D.A p'.1) (D.B p'.2))
                  (inl R I (D.A p'.1) (D.B p'.2) (D.gX p'.1 p.1))) :
                    Set (FormalSpectrum (idealOfDefinition R I (D.A p'.1) (D.B p'.2)))) =
                (D.pr₁ChartSelf p').base ⁻¹'
                  (↑(basicOpen (I.map (algebraMap R (D.A p'.1))) (D.gX p'.1 p.1)) :
                    Set (FormalSpectrum (I.map (algebraMap R (D.A p'.1))))) := by
              have hpre := FormalSpectrum.map_preimage_basicOpen
                (I.map (algebraMap R (D.A p'.1)))
                (idealOfDefinition R I (D.A p'.1) (D.B p'.2))
                (inl R I (D.A p'.1) (D.B p'.2)).toRingHom
                CompletedTensorProduct.inl_isAdicHom.le_comap (D.gX p'.1 p.1)
              exact (congrArg (fun U : TopologicalSpace.Opens
                  (FormalSpectrum (idealOfDefinition R I (D.A p'.1) (D.B p'.2))) =>
                  (↑U : Set (FormalSpectrum
                    (idealOfDefinition R I (D.A p'.1) (D.B p'.2))))) hpre).symm
            rw [hset]
            exact hu1
        · -- second coordinate (symmetric, via the `Y`-glue overlap)
          by_cases h2 : p'.2 = p.2
          · rw [if_pos h2]
            exact Set.mem_univ _
          · rw [if_neg h2]
            have hyf : D.yLrsGlueData.toGlueData.f p'.2 p.2 =
                eqToHom (dif_neg h2) ≫
                  basicOpenChart (I.map (algebraMap R (D.B p'.2))) (D.gY p'.2 p.2) := by
              simp only [yLrsGlueData, yGlueData', CategoryTheory.GlueData.ofGlueData',
                CategoryTheory.GlueData'.f', dif_neg h2]
              rfl
            have hyf_range : Set.range (D.yLrsGlueData.toGlueData.f p'.2 p.2).base =
                (basicOpen (I.map (algebraMap R (D.B p'.2))) (D.gY p'.2 p.2) :
                  Set (FormalSpectrum (I.map (algebraMap R (D.B p'.2))))) := by
              rw [hyf]
              exact (range_eqToHom_comp_base _ _).trans
                (range_basicOpenChart_base _ _ (hI.map (algebraMap R (D.B p'.2))))
            have hmem := D.yLrsGlueData.range_ι_inter_subset p'.2 p.2
              ⟨⟨(D.pr₂ChartSelf p').base w, rfl⟩, hx2⟩
            obtain ⟨v, hv⟩ := hmem
            have hinj :=
              ((D.yFormalGlueData.ι_isOpenImmersion p'.2).base_open).injective
            have hv' : (D.yFormalGlueData.ι p'.2).base
                  ((D.yLrsGlueData.toGlueData.f p'.2 p.2).base v) =
                (D.yFormalGlueData.ι p'.2).base ((D.pr₂ChartSelf p').base w) := hv
            have hu2 : (D.pr₂ChartSelf p').base w ∈
                (basicOpen (I.map (algebraMap R (D.B p'.2))) (D.gY p'.2 p.2) :
                  Set (FormalSpectrum (I.map (algebraMap R (D.B p'.2))))) :=
              hyf_range ▸ ⟨v, hinj hv'⟩
            have hset : (↑(basicOpen (idealOfDefinition R I (D.A p'.1) (D.B p'.2))
                  (inr R I (D.A p'.1) (D.B p'.2) (D.gY p'.2 p.2))) :
                    Set (FormalSpectrum (idealOfDefinition R I (D.A p'.1) (D.B p'.2)))) =
                (D.pr₂ChartSelf p').base ⁻¹'
                  (↑(basicOpen (I.map (algebraMap R (D.B p'.2))) (D.gY p'.2 p.2)) :
                    Set (FormalSpectrum (I.map (algebraMap R (D.B p'.2))))) := by
              have hpre := FormalSpectrum.map_preimage_basicOpen
                (I.map (algebraMap R (D.B p'.2)))
                (idealOfDefinition R I (D.A p'.1) (D.B p'.2))
                (inr R I (D.A p'.1) (D.B p'.2)).toRingHom
                CompletedTensorProduct.inr_isAdicHom.le_comap (D.gY p'.2 p.2)
              exact (congrArg (fun U : TopologicalSpace.Opens
                  (FormalSpectrum (idealOfDefinition R I (D.A p'.1) (D.B p'.2))) =>
                  (↑U : Set (FormalSpectrum
                    (idealOfDefinition R I (D.A p'.1) (D.B p'.2))))) hpre).symm
            rw [hset]
            exact hu2
      -- Glue back: `x = ι_{p'} w = ι_{p'} (f_{p'p} v) = ι_p ((t ≫ f) v)`.
      obtain ⟨v, hv⟩ := hwmem
      refine ⟨(D.lrsGlueData.toGlueData.t p' p ≫ D.lrsGlueData.toGlueData.f p p').base v, ?_⟩
      have key := congrArg (fun m => m.base v)
        (D.lrsGlueData.toGlueData.glue_condition p' p)
      rw [← hv]
      exact key

end BothChartedFibreDatumXY

end AlgebraicGeometry
