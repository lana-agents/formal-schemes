import FormalSchemes.GeneralFibreProductBothProjectionLeft
import FormalSchemes.GeneralFibreProductBothProjectionRight

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The cone identity of the general two-sided fibre product `X ×_{Spf R} Y`

`FormalSchemes.GeneralFibreProductBothProjectionLeft` builds the first projection
`pr₁ : X ×_{Spf R} Y ⟶ X` into the exposed glued factor `X`
(`BothChartedFibreDatumXY.xGlued`), and
`FormalSchemes.GeneralFibreProductBothProjectionRight` builds the second projection
`pr₂ : X ×_{Spf R} Y ⟶ Y` into the exposed glued factor `Y`
(`BothChartedFibreDatumXY.yGlued`). The exposed structural morphisms
`xStructMap : X ⟶ Spf R` and `yStructMap : Y ⟶ Spf R` are built in
`FormalSchemes.GeneralFibreProductBothExposeXY`.

This file closes the final brick 308d of issue 308 (= 233 item 3): the **cone identity**

`pr₁ ≫ xStructMap = pr₂ ≫ yStructMap`   over   `Spf R`,

exhibiting `X ×_{Spf R} Y` as a genuine cone over `Spf R`. It is proved by
`FormalScheme.GlueData.hom_ext`: restricting both sides along each glue inclusion `ι p` of the
fibre product reduces — via `ι_pr₁`/`ι_xStructMap` on the left and `ι_pr₂`/`ι_yStructMap` on the
right — to the per-chart cone identity

`pr₁ChartSelf p ≫ xStructMapChart p.1 = pr₂ChartSelf p ≫ yStructMapChart p.2`

(`cone_identity_chart`). Each side fuses through `FormalSpectrum.locallyRingedSpaceMap_comp` into a
single `locallyRingedSpaceMap` out of `Spf(A_{p.1} ⊗̂_R B_{p.2})`, and the underlying ring maps
agree because both `inl : A_{p.1} → A_{p.1} ⊗̂_R B_{p.2}` and `inr : B_{p.2} → A_{p.1} ⊗̂_R B_{p.2}`
are `R`-algebra maps: their composites with the base structure maps both equal
`algebraMap R (A_{p.1} ⊗̂_R B_{p.2})` (`AlgHom.comp_algebraMap`). This is the affine cone identity
`CompletedTensorProduct.fibre_cone_comm`, reproved in the instance-light world of raw
`locallyRingedSpaceMap`s (the general charts `A_i`/`B_j` carry no adic-ring structure of their own,
so `fibre_cone_comm` — which needs those instances — is not invoked directly).

## Main definitions

* `BothChartedFibreDatumXY.cone_identity_chart`: the per-chart cone identity.
* `BothChartedFibreDatumXY.cone_comm`: the glued cone identity
  `pr₁ ≫ xStructMap = pr₂ ≫ yStructMap`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum
open CompletedTensorProduct

universe u

namespace AlgebraicGeometry

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable (D : BothChartedFibreDatumXY R I hI)

/-- **The per-chart cone identity.** The per-chart first projection of chart `p` followed by the
per-chart structural morphism of `X` equals the per-chart second projection of chart `p` followed by
the per-chart structural morphism of `Y`. Both sides collapse to a single `locallyRingedSpaceMap`
out of `Spf(A_{p.1} ⊗̂_R B_{p.2})`, and the underlying ring maps agree because
`inl.comp (algebraMap R (A_{p.1}))` and `inr.comp (algebraMap R (B_{p.2}))` both equal
`algebraMap R (A_{p.1} ⊗̂_R B_{p.2})` (`AlgHom.comp_algebraMap`). -/
theorem cone_identity_chart (p : D.JX × D.JY) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    D.pr₁ChartSelf p ≫ D.xStructMapChart p.1 =
      D.pr₂ChartSelf p ≫ D.yStructMapChart p.2 := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  rw [pr₁ChartSelf, xStructMapChart, pr₂ChartSelf, yStructMapChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (I := I) (J := I.map (algebraMap R (D.A p.1)))
      (K := CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2))
      (φ := algebraMap R (D.A p.1))
      (ψ := (CompletedTensorProduct.inl R I (D.A p.1) (D.B p.2)).toRingHom)
      (hIJ := Ideal.le_comap_map)
      (hJK := CompletedTensorProduct.inl_isAdicHom.le_comap)
      (hIK := le_comap_comp (algebraMap R (D.A p.1))
        (CompletedTensorProduct.inl R I (D.A p.1) (D.B p.2)).toRingHom
        Ideal.le_comap_map CompletedTensorProduct.inl_isAdicHom.le_comap),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (I := I) (J := I.map (algebraMap R (D.B p.2)))
      (K := CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2))
      (φ := algebraMap R (D.B p.2))
      (ψ := (CompletedTensorProduct.inr R I (D.A p.1) (D.B p.2)).toRingHom)
      (hIJ := Ideal.le_comap_map)
      (hJK := CompletedTensorProduct.inr_isAdicHom.le_comap)
      (hIK := le_comap_comp (algebraMap R (D.B p.2))
        (CompletedTensorProduct.inr R I (D.A p.1) (D.B p.2)).toRingHom
        Ideal.le_comap_map CompletedTensorProduct.inr_isAdicHom.le_comap)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    ((AlgHom.comp_algebraMap (CompletedTensorProduct.inl R I (D.A p.1) (D.B p.2))).trans
      (AlgHom.comp_algebraMap (CompletedTensorProduct.inr R I (D.A p.1) (D.B p.2))).symm)

/-- **The cone identity of the general two-sided fibre product**
`pr₁ ≫ xStructMap = pr₂ ≫ yStructMap` over `Spf R`, exhibiting `X ×_{Spf R} Y` as a genuine cone
over `Spf R`. Proved by
`FormalScheme.GlueData.hom_ext`: restricting along each glue inclusion `ι p` reduces to
`cone_identity_chart` via `ι_pr₁`/`ι_xStructMap` (left) and `ι_pr₂`/`ι_yStructMap` (right). The
three concreteness hypotheses `hV`/`hf`/`ht` pin the carried abstract glue of `D` to the concrete
`bothAlgData*` (holding by `rfl` for any `ofAlgebraData`-built datum), matching `pr₁`/`pr₂`. -/
theorem cone_comm
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    letI := D.topologyA
    letI := D.isAdicA
    letI := D.topologyB
    letI := D.isAdicB
    D.pr₁ hV hf ht ≫ D.xStructMap = D.pr₂ hV hf ht ≫ D.yStructMap := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  letI := D.topologyA
  letI := D.isAdicA
  letI := D.topologyB
  letI := D.isAdicB
  suffices h : ∀ (p : D.JX × D.JY),
      D.formalGlueData.ι p ≫ D.pr₁ hV hf ht ≫ D.xStructMap =
        D.formalGlueData.ι p ≫ D.pr₂ hV hf ht ≫ D.yStructMap by
    exact D.formalGlueData.hom_ext h
  -- The index type `JX × JY` of the glue data is semireducible (the `GlueData.ofGlueData'`
  -- object-defeq wall), so `rw`/`simp` cannot match against `ι p`; chase the equality in term mode
  -- instead, where the defeq is discharged at elaboration.
  intro p
  exact (Category.assoc _ _ _).symm.trans <|
    (((D.ι_pr₁ hV hf ht p) =≫ D.xStructMap).trans <|
      (Category.assoc _ _ _).trans <|
        (D.pr₁ChartSelf p ≫= D.ι_xStructMap p.1).trans <|
          (D.cone_identity_chart p).trans <|
            (D.pr₂ChartSelf p ≫= (D.ι_yStructMap p.2).symm).trans <|
              (Category.assoc _ _ _).symm.trans <|
                (((D.ι_pr₂ hV hf ht p).symm =≫ D.yStructMap).trans
                  (Category.assoc _ _ _)))

end BothChartedFibreDatumXY

end AlgebraicGeometry
