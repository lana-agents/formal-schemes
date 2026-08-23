import FormalSchemes.TateSelfProductCone
import FormalSchemes.AdicOverBaseChart
import FormalSchemes.AffineFibreProductLRS

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The Tate self-fibre product is adic over `Spf R`

The four-chart Tate self-fibre product `𝔈_q ×_{Spf R} 𝔈_q` (`tateSelfProductInv`) carries a
structural morphism to `Spf R`, namely either projection followed by `tateCurveModelStructMap` —
the two agree by `tateSelfProduct_cone_comm`. This file proves that it is **adic over that base**
in the sense of `FormalScheme.AdicOverBaseLocallyFG`, and hence in particular `LocallyFG`.

Both statements are hypotheses that the general fibre-product API leaves to its callers, and both
are consumed by the brick-4 comparison of issue 740:

* `tateFibreProductHom` (the `Φ` half, `FormalSchemes/TateFibreProductHom.lean`) is
  `BothChartedFibreDatumXY.fibreLiftAdic` (794) at this witness, which is what makes it
  **unconditional** — the witness discharges both `fibreLift`'s `hZ : LocallyFG` and its otherwise
  unreachable per-refined-chart continuity bound (issue 798);
* `BothChartedFibreDatumXY.fibreLift_unique_adicOverBase` — the lemma that makes the round trip
  `Ψ ≫ Φ = 𝟙` free once the reverse comparison exists — needs
  `FormalScheme.AdicOverBaseLocallyFG Z s` for `Z = tateSelfProductInv`.

Neither had been checked. They are both true, and cheaply: the proof is
`BothChartedFibreDatum.adicOverBase_xStructMap`'s, transplanted from the generic datum's glued
object to this hand-built glue datum.

## The argument

Every point of the glued object lies in the image of one of the four glue inclusions
`ι i : Spf(A ⊗̂_R A) ⟶ 𝔈_q ×_{Spf R} 𝔈_q` (`ι_jointly_surjective`), which is an open immersion
onto a chart whose ideal of definition is finitely generated (`tensorIdealOfDefinition_fg`). What
has to be checked is that the composite `ι i ≫ structMap` is adic on global sections, and this is
where the four charts collapse to one computation: by `ι_glueMorphisms` the composite is the affine
`pr₁Chart ≫ annulusStructMap`, *independently of `i`*, and that map is `Spf` of the algebra map
`R → A ⊗̂_R A` (`pr₁Chart_comp_annulusStructMap`), which is adic by
`CompletedTensorProduct.algebraMap_isAdicHom`.

The chart-level identity is the first projection's half of `tateSelfProduct_chart_cone_comm`,
extracted and stated in its own right: that theorem proves the two chart projections agree over
`Spf R` by computing both composites to `Spf (algebraMap R (A ⊗̂_R A))`, and here only the value of
the computation is wanted, not the agreement.

## Main definitions and results

* `AlgebraicGeometry.tateSelfProductStructMap`: the structural morphism
  `𝔈_q ×_{Spf R} 𝔈_q ⟶ Spf R`.
* `AlgebraicGeometry.pr₁Chart_comp_annulusStructMap`: the per-chart structural morphism is `Spf` of
  `algebraMap R (A ⊗̂_R B)`.
* `AlgebraicGeometry.ι_tateSelfProductStructMap`: each glue inclusion followed by the structural
  morphism is the per-chart structural morphism.
* `AlgebraicGeometry.tateSelfProductInv_adicOverBase`: `AdicOverBaseLocallyFG`.
* `AlgebraicGeometry.tateSelfProductInv_locallyFG`: `LocallyFG`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]
  [TopologicalSpace R] [IsAdicRing I]

/-! ### The per-chart structural morphism -/

/-- **The per-chart structural morphism of the Tate self-fibre product is `Spf` of the algebra
map.** The affine first projection `pr₁Chart = Spf(inl)` (transported through the base
ideal-convention bridge), followed by the annulus structural morphism `Spf A ⟶ Spf R`, is `Spf` of
`algebraMap R (A ⊗̂_R B)`, because `inl` is an `R`-algebra map. This is the first-projection half
of `tateSelfProduct_chart_cone_comm`, stated for its value rather than for the agreement. -/
theorem pr₁Chart_comp_annulusStructMap (B : Type u) [CommRing B] [Algebra R B] (hI : I.FG) :
    pr₁Chart R I q B ≫ annulusStructMap R I q hI =
      locallyRingedSpaceMap I (idealOfDefinition R I (annulusAlgebra R I q) B)
        (algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q) B))
        algebraMap_isAdicHom.le_comap := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  have hInlEq : (inl R I (annulusAlgebra R I q) B).toRingHom.comp
      ((RingHom.id (annulusAlgebra R I q)).comp (algebraMap R (annulusAlgebra R I q))) =
      algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q) B) := by
    rw [RingHom.id_comp]
    exact AlgHom.comp_algebraMap (inl R I (annulusAlgebra R I q) B)
  have hIdAlg : I ≤ (I.map (algebraMap R (annulusAlgebra R I q))).comap
      ((RingHom.id (annulusAlgebra R I q)).comp (algebraMap R (annulusAlgebra R I q))) := by
    rw [RingHom.id_comp]; exact Ideal.le_comap_map
  have hInl : I ≤ (idealOfDefinition R I (annulusAlgebra R I q) B).comap
      ((inl R I (annulusAlgebra R I q) B).toRingHom.comp
        ((RingHom.id (annulusAlgebra R I q)).comp (algebraMap R (annulusAlgebra R I q)))) :=
    hInlEq ▸ algebraMap_isAdicHom.le_comap
  rw [pr₁Chart, annulusBaseBridge, annulusStructMap, IsTopologicallyFiniteType.structMap,
    Category.assoc, ← locallyRingedSpaceMap_comp (hIK := hIdAlg),
    ← locallyRingedSpaceMap_comp (hIK := hInl)]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _ hInlEq

omit [IsNoetherianRing R] [TopologicalSpace R] [IsAdicRing I] in
/-- **The ideal of definition of `A ⊗̂_R B` is finitely generated.** Stated here in the form the
adic-over-base witness needs, proved from `idealOfDefinition_eq_map` directly so that no topology
or adicity instance on the factors has to be in scope. -/
theorem tensorIdealOfDefinition_fg (B : Type u) [CommRing B] [Algebra R B] (hI : I.FG) :
    (idealOfDefinition R I (annulusAlgebra R I q) B).FG := by
  rw [CompletedTensorProduct.idealOfDefinition_eq_map]
  exact hI.map _

/-- **The per-chart structural morphism is adic on global sections.** Its global-sections map is
the algebra map `R → A ⊗̂_R B`, which carries `I` into the ideal of definition. -/
theorem le_comap_globalSectionsMap_pr₁Chart_comp_annulusStructMap
    (B : Type u) [CommRing B] [Algebra R B]
    [TopologicalSpace (CompletedTensorProduct R I (annulusAlgebra R I q) B)]
    [IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) B)] (hI : I.FG) :
    I ≤ (idealOfDefinition R I (annulusAlgebra R I q) B).comap
      (globalSectionsMap I (idealOfDefinition R I (annulusAlgebra R I q) B)
        (pr₁Chart R I q B ≫ annulusStructMap R I q hI)) := by
  rw [pr₁Chart_comp_annulusStructMap, globalSectionsMap_locallyRingedSpaceMap]
  exact algebraMap_isAdicHom.le_comap

/-! ### The structural morphism of the glued self-fibre product -/

/-- **The structural morphism** `𝔈_q ×_{Spf R} 𝔈_q ⟶ Spf R`, taken as the first projection followed
by the model's structural morphism. By `tateSelfProduct_cone_comm` the second projection gives the
same morphism, so the choice is immaterial. -/
def tateSelfProductStructMap (hq : q ∈ I) (hI : I.FG) :
    (tateSelfProductInv R I q hq hI).toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  tateSelfProductPr₁ R I q hq hI ≫ tateCurveModelStructMap R I q hq hI

/-- The structural morphism is also the *second* projection followed by the model's structural
morphism — this is `tateSelfProduct_cone_comm`, restated for `tateSelfProductStructMap`. -/
theorem tateSelfProductStructMap_eq_pr₂ (hq : q ∈ I) (hI : I.FG) :
    tateSelfProductStructMap R I q hq hI =
      tateSelfProductPr₂ R I q hq hI ≫ tateCurveModelStructMap R I q hq hI :=
  tateSelfProduct_cone_comm R I q hq hI

/-- **Each glue inclusion followed by the structural morphism is the per-chart structural
morphism** — and, crucially, the *same* one for all four charts, because the first projection's
per-chart value `pr₁Chart` does not depend on the chart index and both model charts have the same
structural morphism `annulusStructMap`.

Kept in pure term mode. `rw` cannot rebuild a motive across the `tateSelfProductInv` versus
`(tateSelfProductFormalGlueDataInv …).gluedFormalScheme` object-defeq wall: `rw
[tateSelfProductStructMap]` *succeeds* and silently leaves the goal type-incorrect at `instances`
transparency, after which the next rewrite fails with a message naming the wrong lemma.
`tateSelfProduct_cone_comm` is written this way for the same reason. -/
theorem ι_tateSelfProductStructMap (hq : q ∈ I) (hI : I.FG)
    (i : (tateSelfProductFormalGlueDataInv R I q hq hI).toLocallyRingedSpaceGlueData.J) :
    (tateSelfProductFormalGlueDataInv R I q hq hI).ι i ≫ tateSelfProductStructMap R I q hq hI =
      pr₁Chart R I q (annulusAlgebra R I q) ≫ annulusStructMap R I q hI := by
  have h1 : (tateSelfProductFormalGlueDataInv R I q hq hI).ι i ≫ tateSelfProductPr₁ R I q hq hI =
      pr₁Chart R I q (annulusAlgebra R I q) ≫
        (tateCurveFormalGlueData R I q hq hI).ι ⟨i.down.1⟩ := by
    rw [tateSelfProductPr₁]
    exact (tateSelfProductFormalGlueDataInv R I q hq hI).ι_glueMorphisms _ _ i
  have hs : (tateCurveFormalGlueData R I q hq hI).ι ⟨i.down.1⟩ ≫
      tateCurveModelStructMap R I q hq hI = annulusStructMap R I q hI := by
    rw [tateCurveModelStructMap]
    exact (tateCurveFormalGlueData R I q hq hI).ι_glueMorphisms _ _ _
  have hL : (tateSelfProductFormalGlueDataInv R I q hq hI).ι i ≫
        tateSelfProductPr₁ R I q hq hI ≫ tateCurveModelStructMap R I q hq hI =
      pr₁Chart R I q (annulusAlgebra R I q) ≫ annulusStructMap R I q hI :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ tateCurveModelStructMap R I q hq hI) h1).trans <|
        (Category.assoc _ _ _).trans <|
          congrArg (pr₁Chart R I q (annulusAlgebra R I q) ≫ ·) hs
  exact hL

/-! ### Adicity over the base -/

/-- **The Tate self-fibre product is adic over `Spf R`.** Every point lies in one of the four glue
charts `Spf(A ⊗̂_R A)`, which is an open immersion with finitely generated ideal of definition, and
whose composite with the structural morphism is `Spf (algebraMap R (A ⊗̂_R A))`, adic on global
sections. This is the hypothesis `hZadic` of
`BothChartedFibreDatumXY.fibreLift_unique_adicOverBase` for the Tate model's self-fibre product. -/
theorem tateSelfProductInv_adicOverBase (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.AdicOverBaseLocallyFG (tateSelfProductInv R I q hq hI)
      (tateSelfProductStructMap R I q hq hI) := by
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
  intro x
  obtain ⟨i, y, hy⟩ := (tateSelfProductFormalGlueDataInv R I q hq hI).ι_jointly_surjective x
  refine ⟨CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q),
    inferInstance, inferInstance,
    idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q), inferInstance,
    (tateSelfProductFormalGlueDataInv R I q hq hI).ι i,
    tensorIdealOfDefinition_fg R I q _ hI, ⟨y, hy⟩,
    FormalScheme.GlueData.ι_isOpenImmersion _ i, ?_⟩
  -- The transport is done with an explicit `Eq.mpr` on the *ring homomorphism*, never with `rw`
  -- on the morphism of locally ringed spaces: the goal mentions `ι i ≫ tateSelfProductStructMap`,
  -- which is not type-correct at `instances` transparency (`tateSelfProductInv` versus
  -- `(tateSelfProductFormalGlueDataInv …).gluedFormalScheme`), so `rw`'s `kabstract` cannot even
  -- locate a pattern inside it. `Eq.mpr` is checked at default transparency, where it is free.
  refine Eq.mpr (congrArg (fun φ : R →+* CompletedTensorProduct R I (annulusAlgebra R I q)
      (annulusAlgebra R I q) =>
        I ≤ (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)).comap φ)
    (congrArg (globalSectionsMap I (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q))) (ι_tateSelfProductStructMap R I q hq hI i))) ?_
  exact le_comap_globalSectionsMap_pr₁Chart_comp_annulusStructMap R I q _ hI

/-- **The Tate self-fibre product is locally of finite generation.** This is the hypothesis `hZ` of
`tateFibreProductHom` (and of `BothChartedFibreDatumXY.fibreLift` for this source), obtained by
dropping the adic-over-base conjunct from `tateSelfProductInv_adicOverBase`. -/
theorem tateSelfProductInv_locallyFG (hq : q ∈ I) (hI : I.FG) :
    (tateSelfProductInv R I q hq hI).LocallyFG :=
  (tateSelfProductInv_adicOverBase R I q hq hI).locallyFG

end AlgebraicGeometry

end
