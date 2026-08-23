import FormalSchemes.AffineFibreProductLRS
import FormalSchemes.BothDatumAdicOverBase
import FormalSchemes.GeneralFibreProductBothProjectionLeft

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The general fibre product `X ×_{Spf R} Y` is adic over the base

For a two-sided fibre-product datum `D : BothChartedFibreDatumXY R I hI`, the glued factors
`D.xGlued` and `D.yGlued` are adic over their structural morphisms
(`FormalSchemes.BothDatumAdicOverBase`, issues 468/487). This file proves the same for the fibre
product itself: `D.generalFibreProduct` is adic over `pr₁ ≫ xStructMap` in the sense of
`FormalScheme.AdicOverBaseLocallyFG`.

`AdicOverBaseLocallyFG` of the **source** is the sole hypothesis of the two halves of the general
fibre product's universal property — `BothChartedFibreDatumXY.fibreLiftAdic` (issue 794) and
`BothChartedFibreDatumXY.fibreLift_unique_adicOverBase` (issue 518). Applying either of them with
the fibre product itself as the source is therefore blocked on exactly this statement, and that is
the shape every "compare two presentations of the same `X`" argument takes.

`FormalSchemes.TateSelfProductAdicOverBase` proves the same thing for the hand-built four-chart
Tate self-product `𝔈_q ×_{Spf R} 𝔈_q`, and its module docstring says outright that the proof is
`BothChartedFibreDatumXY.adicOverBase_xStructMap`'s, transplanted. This file is that observation
carried out once and for all at the generic datum, so no future consumer has to transplant it
again.

## The argument

Every point of `generalFibreProduct = D.formalGlueData.gluedFormalScheme` lies in the image of one
of the glue inclusions `ι p : Spf(A_{p.1} ⊗̂_R B_{p.2}) ⟶ X ×_{Spf R} Y`
(`GlueData.ι_jointly_surjective`), an open immersion onto a chart whose ideal of definition is
finitely generated (`CompletedTensorProduct.idealOfDefinition_fg`). What has to be checked is that
`ι p ≫ pr₁ ≫ xStructMap` is adic on global sections, and this is where all the charts collapse to
one computation: by `ι_pr₁` and `ι_xStructMap` the composite is the affine
`pr₁ChartSelf p ≫ xStructMapChart p.1`, which is `Spf` of `algebraMap R (A_{p.1} ⊗̂_R B_{p.2})`
(`pr₁ChartSelf_comp_xStructMapChart`), and that map is adic by
`CompletedTensorProduct.algebraMap_isAdicHom`.

`pr₁ChartSelf_comp_xStructMapChart` is the first projection's half of `cone_identity_chart`
(`FormalSchemes.GeneralFibreProductBothCone`), extracted and stated in its own right: that theorem
proves the two per-chart projections agree over `Spf R` by computing both composites to
`Spf (algebraMap R (A ⊗̂_R B))`, and here only the value of the computation is wanted, not the
agreement.

## Main results

* `AlgebraicGeometry.BothChartedFibreDatumXY.pr₁ChartSelf_comp_xStructMapChart`: the per-chart
  structural morphism of the fibre product is `Spf` of `algebraMap R (A_{p.1} ⊗̂_R B_{p.2})`.
* `AlgebraicGeometry.BothChartedFibreDatumXY.adicOverBase_fibreProductStructMap`:
  `AdicOverBaseLocallyFG D.generalFibreProduct (D.pr₁ hV hf ht ≫ D.xStructMap)`.
* `AlgebraicGeometry.BothChartedFibreDatumXY.locallyFG_generalFibreProduct`: the `LocallyFG`
  consequence.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6, §10.7, §10.15.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology FormalSpectrum

universe u

namespace AlgebraicGeometry.BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable (D : BothChartedFibreDatumXY R I hI)

private theorem le_comap_comp' {S T U : Type u} [CommRing S] [CommRing T] [CommRing U]
    {J : Ideal S} {K : Ideal T} {L : Ideal U} (φ : S →+* T) (ψ : T →+* U)
    (hJK : J ≤ K.comap φ) (hKL : K ≤ L.comap ψ) : J ≤ L.comap (ψ.comp φ) :=
  fun _ ha => hKL (hJK ha)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The per-chart structural morphism of the fibre product.** The per-chart first projection
followed by the per-chart structural morphism of `X` is `Spf` of the `R`-algebra structure map of
the completed tensor product — in particular it does not depend on which of the two projections it
is read through (that symmetric statement is `cone_identity_chart`). -/
theorem pr₁ChartSelf_comp_xStructMapChart (p : D.JX × D.JY) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    D.pr₁ChartSelf p ≫ D.xStructMapChart p.1 =
      FormalSpectrum.locallyRingedSpaceMap I
        (CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2))
        (algebraMap R (CompletedTensorProduct R I (D.A p.1) (D.B p.2)))
        CompletedTensorProduct.algebraMap_isAdicHom.le_comap := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  rw [pr₁ChartSelf, xStructMapChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (I := I) (J := I.map (algebraMap R (D.A p.1)))
      (K := CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2))
      (φ := algebraMap R (D.A p.1))
      (ψ := (CompletedTensorProduct.inl R I (D.A p.1) (D.B p.2)).toRingHom)
      (hIJ := Ideal.le_comap_map)
      (hJK := CompletedTensorProduct.inl_isAdicHom.le_comap)
      (hIK := le_comap_comp' (algebraMap R (D.A p.1))
        (CompletedTensorProduct.inl R I (D.A p.1) (D.B p.2)).toRingHom
        Ideal.le_comap_map CompletedTensorProduct.inl_isAdicHom.le_comap)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (AlgHom.comp_algebraMap (CompletedTensorProduct.inl R I (D.A p.1) (D.B p.2)))

set_option backward.isDefEq.respectTransparency false in
/-- **The general fibre product is adic over the base.** Every point lies in a glue chart
`ι p : Spf(A_{p.1} ⊗̂_R B_{p.2}) ⟶ X ×_{Spf R} Y`, an open immersion with finitely generated ideal
of definition, whose composite with the structural morphism `pr₁ ≫ xStructMap` is `Spf` of
`algebraMap R (A_{p.1} ⊗̂_R B_{p.2})` and hence adic on global sections.

The three concreteness hypotheses `hV`/`hf`/`ht` are those of `pr₁`; they hold by `rfl` for any
`ofAlgebraData`-built datum. -/
theorem adicOverBase_fibreProductStructMap
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm) :
    FormalScheme.AdicOverBaseLocallyFG D.toBothChartedFibreDatum.generalFibreProduct
      (D.pr₁ hV hf ht ≫ D.xStructMap) := by
  letI := D.commRingA; letI := D.algebraA; letI := D.topologyA; letI := D.isAdicA
  letI := D.commRingB; letI := D.algebraB; letI := D.topologyB; letI := D.isAdicB
  intro x
  obtain ⟨p, y, hy⟩ := D.toBothChartedFibreDatum.formalGlueData.ι_jointly_surjective x
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2)) :=
    CompletedTensorProduct.isAdicRing R I (D.A p.1) (D.B p.2) hI
  refine ⟨CompletedTensorProduct R I (D.A p.1) (D.B p.2), inferInstance, inferInstance,
    CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2), inferInstance,
    D.toBothChartedFibreDatum.formalGlueData.ι p,
    CompletedTensorProduct.idealOfDefinition_fg hI, ⟨y, hy⟩, inferInstance, ?_⟩
  rw [← Category.assoc, D.ι_pr₁ hV hf ht p, Category.assoc, D.ι_xStructMap p.1,
    D.pr₁ChartSelf_comp_xStructMapChart p,
    FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap]
  exact CompletedTensorProduct.algebraMap_isAdicHom.le_comap

/-- **The general fibre product is locally finitely generated**, the `LocallyFG` consequence of
`adicOverBase_fibreProductStructMap`. -/
theorem locallyFG_generalFibreProduct
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm) :
    D.toBothChartedFibreDatum.generalFibreProduct.LocallyFG :=
  (D.adicOverBase_fibreProductStructMap hV hf ht).locallyFG

end AlgebraicGeometry.BothChartedFibreDatumXY

end
