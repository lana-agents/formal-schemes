import FormalSchemes.TateSelfProductProjectionLeft
import FormalSchemes.TateSelfProductProjectionRight
import FormalSchemes.AffineFibreProduct

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The cone identity of the four-chart Tate self-fibre-product over `Spf R`

The four-chart Tate self-fibre product `𝔈_q ×_{Spf R} 𝔈_q` (`tateSelfProduct`) carries two
projections into the glued Tate curve model `𝔈_q` (`tateCurveModel`): the first projection
`tateSelfProductPr₁` (#173) and the second projection `tateSelfProductPr₂` (#174). This file proves
the remaining **cone identity** of the fibre product: both projections agree after composition with
the structural morphism `𝔈_q ⟶ Spf R` (`tateCurveModelStructMap`), i.e. `𝔈_q ×_{Spf R} 𝔈_q` is a
genuine cone over `Spf R`.

The proof is `FormalScheme.GlueData.hom_ext` on the glued source: it suffices to check the identity
after restriction along each glue inclusion `ι (a, b)`. Both projections restrict to per-chart
affine maps (`ι_glueMorphisms`), and the two glue inclusions `ι ⟨(a,b).1⟩` / `ι ⟨(a,b).2⟩` of the
target both collapse against `tateCurveModelStructMap` to the same per-patch structural map
`annulusStructMap` (again `ι_glueMorphisms`). What remains, uniformly in the chart, is the affine
cone identity for the completed tensor product `A ⊗̂_R A`: the first projection `Spf(inl)` and the
second projection `Spf(inr)` (each transported through the ideal-convention bridge
`annulusBaseBridge`) agree over `Spf R`, because `inl` and `inr` are `R`-algebra maps, so both
composites are the algebra structure map `algebraMap R (A ⊗̂_R A)`. This is the self-product
instance of `CompletedTensorProduct.fibre_cone_comm`.

## Main results

* `AlgebraicGeometry.tateSelfProduct_chart_cone_comm`: the affine per-chart cone identity.
* `AlgebraicGeometry.tateSelfProduct_cone_comm`: `pr₁ ≫ structMap = pr₂ ≫ structMap` (closes the
  cone datum of issue 237).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]
  [TopologicalSpace R] [IsAdicRing I]

/-! ### The affine per-chart cone identity -/

/-- **The affine per-chart cone identity.** On each affine chart `Spf(A ⊗̂_R A)` of the Tate
self-fibre product, the first projection `pr₁Chart` and the second projection `pr₂Chart` (the latter
transported through the base ideal-convention bridge) agree over `Spf R`. Both composites are the
structural map induced by `algebraMap R (A ⊗̂_R A)`, since `inl` and `inr` are `R`-algebra maps. -/
theorem tateSelfProduct_chart_cone_comm (hI : I.FG) :
    pr₁Chart R I q (annulusAlgebra R I q) ≫ annulusStructMap R I q hI =
      pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫
        annulusBaseBridge R I q ≫ annulusStructMap R I q hI := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  -- The `le_comap` witnesses of the three combined ring homomorphisms, proved cheaply here (each
  -- collapses to the algebra structure map) so the reverse-composition rewrites stay metavar-free.
  have hInlEq : (inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)).toRingHom.comp
      ((RingHom.id (annulusAlgebra R I q)).comp (algebraMap R (annulusAlgebra R I q))) =
      algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q)) := by
    rw [RingHom.id_comp]
    exact AlgHom.comp_algebraMap (inl R I (annulusAlgebra R I q) (annulusAlgebra R I q))
  have hInrEq : (inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)).toRingHom.comp
      ((RingHom.id (annulusAlgebra R I q)).comp (algebraMap R (annulusAlgebra R I q))) =
      algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q)) := by
    rw [RingHom.id_comp]
    exact AlgHom.comp_algebraMap (inr R I (annulusAlgebra R I q) (annulusAlgebra R I q))
  have hIdAlg : I ≤ (I.map (algebraMap R (annulusAlgebra R I q))).comap
      ((RingHom.id (annulusAlgebra R I q)).comp (algebraMap R (annulusAlgebra R I q))) := by
    rw [RingHom.id_comp]; exact Ideal.le_comap_map
  have hInl : I ≤ (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)).comap
      ((inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)).toRingHom.comp
        ((RingHom.id (annulusAlgebra R I q)).comp (algebraMap R (annulusAlgebra R I q)))) :=
    hInlEq ▸ algebraMap_isAdicHom.le_comap
  have hInr : I ≤ (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)).comap
      ((inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)).toRingHom.comp
        ((RingHom.id (annulusAlgebra R I q)).comp (algebraMap R (annulusAlgebra R I q)))) :=
    hInrEq ▸ algebraMap_isAdicHom.le_comap
  rw [pr₁Chart, pr₂Chart, annulusBaseBridge, annulusStructMap,
    IsTopologicallyFiniteType.structMap, Category.assoc,
    ← locallyRingedSpaceMap_comp (hIK := hIdAlg),
    ← locallyRingedSpaceMap_comp (hIK := hInl),
    ← locallyRingedSpaceMap_comp (hIK := hInr)]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _ (hInlEq.trans hInrEq.symm)

/-! ### The glued cone identity -/

/-- **The cone identity of the four-chart Tate self-fibre product.** The two projections
`pr₁, pr₂ : 𝔈_q ×_{Spf R} 𝔈_q ⟶ 𝔈_q` agree after composition with the structural morphism
`𝔈_q ⟶ Spf R`, so `𝔈_q ×_{Spf R} 𝔈_q` is a genuine cone over `Spf R`. Proved by `hom_ext` on the
glued source, reducing on each chart to the affine cone identity. -/
theorem tateSelfProduct_cone_comm (hq : q ∈ I) (hI : I.FG) :
    tateSelfProductPr₁ R I q hq hI ≫ tateCurveModelStructMap R I q hq hI =
      tateSelfProductPr₂ R I q hq hI ≫ tateCurveModelStructMap R I q hq hI := by
  refine (tateSelfProductFormalGlueData R I q hq hI).hom_ext (fun i => ?_)
  -- Per-chart restriction of each projection (`ι_glueMorphisms`) and of the structural map. These
  -- typecheck at default transparency; the ensuing combination is kept in pure term mode
  -- (`congrArg`/`Category.assoc`/`Eq.trans`), so no `rw` ever rebuilds a motive containing `i.down`
  -- across the `J = ULift (Bool × Bool)` object-defeq wall (which fails at instances transparency).
  have h1 : (tateSelfProductFormalGlueData R I q hq hI).ι i ≫ tateSelfProductPr₁ R I q hq hI =
      pr₁Chart R I q (annulusAlgebra R I q) ≫
        (tateCurveFormalGlueData R I q hq hI).ι ⟨i.down.1⟩ := by
    rw [tateSelfProductPr₁]
    exact (tateSelfProductFormalGlueData R I q hq hI).ι_glueMorphisms _ _ i
  have h2 : (tateSelfProductFormalGlueData R I q hq hI).ι i ≫ tateSelfProductPr₂ R I q hq hI =
      pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫
        annulusBaseBridge R I q ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨i.down.2⟩ := by
    rw [tateSelfProductPr₂]
    exact (tateSelfProductFormalGlueData R I q hq hI).ι_glueMorphisms _ _ i
  have hs1 : (tateCurveFormalGlueData R I q hq hI).ι ⟨i.down.1⟩ ≫
      tateCurveModelStructMap R I q hq hI = annulusStructMap R I q hI := by
    rw [tateCurveModelStructMap]
    exact (tateCurveFormalGlueData R I q hq hI).ι_glueMorphisms _ _ ⟨i.down.1⟩
  have hs2 : (tateCurveFormalGlueData R I q hq hI).ι ⟨i.down.2⟩ ≫
      tateCurveModelStructMap R I q hq hI = annulusStructMap R I q hI := by
    rw [tateCurveModelStructMap]
    exact (tateCurveFormalGlueData R I q hq hI).ι_glueMorphisms _ _ ⟨i.down.2⟩
  have hL : (tateSelfProductFormalGlueData R I q hq hI).ι i ≫
        tateSelfProductPr₁ R I q hq hI ≫ tateCurveModelStructMap R I q hq hI =
      pr₁Chart R I q (annulusAlgebra R I q) ≫ annulusStructMap R I q hI :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ tateCurveModelStructMap R I q hq hI) h1).trans <|
        (Category.assoc _ _ _).trans <|
          congrArg (pr₁Chart R I q (annulusAlgebra R I q) ≫ ·) hs1
  have hR : (tateSelfProductFormalGlueData R I q hq hI).ι i ≫
        tateSelfProductPr₂ R I q hq hI ≫ tateCurveModelStructMap R I q hq hI =
      pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫
        annulusBaseBridge R I q ≫ annulusStructMap R I q hI :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ tateCurveModelStructMap R I q hq hI) h2).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ ·)
            (Category.assoc _ _ _)).trans <|
            congrArg (pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫
              annulusBaseBridge R I q ≫ ·) hs2
  exact hL.trans ((tateSelfProduct_chart_cone_comm R I q hI).trans hR.symm)

end AlgebraicGeometry
