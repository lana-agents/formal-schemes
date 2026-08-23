import FormalSchemes.TwoPatchFibreProductObject
import FormalSchemes.TateGlueTwoPatch
import FormalSchemes.CompletedTensorAwayInterchangePrLeft
import FormalSchemes.CompletedTensorMapSpfPr
import FormalSchemes.TateChartTransitionAlgEq
import FormalSchemes.GlueMorphisms

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The first projection of the two-patch fibre product `X ×_{Spf R} Spf B`

`FormalSchemes.TwoPatchFibreProductObject` assembles the fibre product of the two-patch Tate model
`X = tateTwoPatch` with an affine base `Spf B` as a glued formal scheme `twoPatchFibreProduct`, two
copies of the chart `Spf(A ⊗̂_R B)` (`A = R{x,y}/(x·y−q)`) glued along the base-changed annulus
overlap transition. This file builds the **first projection** `pr₁ : X ×_{Spf R} Spf B ⟶ X` into
the *glued* Tate model `X`, gluing the affine first projections `Spf(inl) : Spf(A ⊗̂_R B) ⟶ Spf A`
across the two charts and composing with the glue inclusions `ι` of `tateTwoPatch`, via
`FormalScheme.GlueData.glueMorphisms`.

It is the mirror of the second projection `pr₂ : X ×_{Spf R} Spf B ⟶ Spf B`
(`FormalSchemes.TwoPatchFibreProductProjection`), but where `pr₂` lands in the affine base `Spf B`,
`pr₁` lands in the *glued* target `X`. The affine first projection lives in the ideal convention
`I·A = I.map (algebraMap R A)` of the away-localization interchange, whereas the target `X` is glued
over `annulusIdealOfDefinition`; the two coincide by `annulus_map_eq`, and the per-chart map
`pr₁Chart` transports along that equality.

The compatibility datum `glueMorphisms` consumes on the double overlap is the naturality square

`interchange(x) ≫ pr₁Chart ≫ ι₀ = t.hom ≫ interchange(y) ≫ pr₁Chart ≫ ι₁`

(`twoPatchFibreProduct_pr₁_naturality`), which is assembled from the merged data:

* the away-localization interchange chart, under the *first* projection, lands in the affine
  basic-open chart of `A` (`interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl`, #133);
* the base-changed transition `t = mapSpfIso` commutes with the `inl` projection
  (`mapSpf_comp_inlMap` below, the raw-`locallyRingedSpaceMap` mirror of `mapSpf_comp_fibrePr₁`);
* the geometric annulus chart transition is `Spf` of its `R`-algebra avatar
  (`annulusChartTransitionSpf_hom_eq`, #135); and
* the `tateTwoPatch` glue condition `annulusOverlapChart ≫ ι₀ =
  annulusChartTransitionSpf.hom ≫ annulusOverlapChartY ≫ ι₁`.

## Main definitions

* `CompletedTensorProduct.mapSpf_comp_inlMap`: the raw-`locallyRingedSpaceMap` naturality of the
  fibre-product map in the first projection.
* `AlgebraicGeometry.twoPatchFibreProduct_pr₁_naturality`: the double-overlap compatibility square.
* `AlgebraicGeometry.twoPatchFibreProductPr₁`: the glued first projection `X ×_{Spf R} Spf B ⟶ X`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum
open CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A B A' B' : Type u}
variable [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [CommRing A'] [CommRing B'] [Algebra R A'] [Algebra R B']

/-- An `R`-algebra homomorphism carries the extended ideal of definition `I·A` onto `I·A'`; the
topology-free form needed to state the base map `Spf f` with raw `locallyRingedSpaceMap`. -/
theorem algHom_mapIdeal_isAdicHom (f : A →ₐ[R] A') :
    IsAdicHom (I.map (algebraMap R A)) (I.map (algebraMap R A')) f.toRingHom := by
  unfold IsAdicHom
  rw [Ideal.map_map,
    show f.toRingHom.comp (algebraMap R A) = algebraMap R A' from AlgHom.comp_algebraMap f]

/-- **Naturality of the first projection under `mapSpf`, in raw `locallyRingedSpaceMap` form.**
The functorial map `mapSpf hI f g : Spf(A' ⊗̂_R B') ⟶ Spf(A ⊗̂_R B)` composed with the first
projection `Spf(inl) : Spf(A ⊗̂_R B) ⟶ Spf A` equals the first projection of the source chart
followed by the map `Spf f : Spf A' ⟶ Spf A`. This is the mirror of `mapSpf_comp_fibrePr₁` phrased
with raw `locallyRingedSpaceMap` of the two `inl`s, needing no adic-ring instance on the base. -/
theorem mapSpf_comp_inlMap (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B' hI
    mapSpf hI f g ≫ FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R A))
        (idealOfDefinition R I A B) (inl R I A B).toRingHom inl_isAdicHom.le_comap =
      FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R A'))
          (idealOfDefinition R I A' B') (inl R I A' B').toRingHom inl_isAdicHom.le_comap ≫
        FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R A)) (I.map (algebraMap R A'))
          f.toRingHom (algHom_mapIdeal_isAdicHom f).le_comap := by
  haveI := isAdicRing R I A B hI
  haveI := isAdicRing R I A' B' hI
  simp only [mapSpf, IsAdicHom.spfMap]
  rw [← FormalSpectrum.locallyRingedSpaceMap_comp (I := I.map (algebraMap R A))
      (J := idealOfDefinition R I A B) (K := idealOfDefinition R I A' B')
      (φ := (inl R I A B).toRingHom) (ψ := map hI f g)
      (hIJ := inl_isAdicHom.le_comap) (hJK := (map_isAdicHom hI f g).le_comap)
      (hIK := (inl_isAdicHom.comp (map_isAdicHom hI f g)).le_comap),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (I := I.map (algebraMap R A))
      (J := I.map (algebraMap R A')) (K := idealOfDefinition R I A' B')
      (φ := f.toRingHom) (ψ := (inl R I A' B').toRingHom)
      (hIJ := (algHom_mapIdeal_isAdicHom f).le_comap) (hJK := inl_isAdicHom.le_comap)
      (hIK := ((algHom_mapIdeal_isAdicHom f).comp inl_isAdicHom).le_comap)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (RingHom.ext fun a => map_inl hI f g a)

end CompletedTensorProduct

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable (B : Type u) [CommRing B] [Algebra R B]

/-! ### The ideal-convention bridge and the per-chart first projection -/

/-- The base ideal-convention bridge `Spf(A) ⟶ Spf(A)` transporting the `I·A = I.map (algebraMap R
A)` convention to the `annulusIdealOfDefinition` convention, along `annulus_map_eq`. It is `Spf` of
the identity ring hom, presented over the two (equal) ideals of definition. -/
def annulusBaseBridge :
    locallyRingedSpaceObj (I.map (algebraMap R (annulusAlgebra R I q))) ⟶
      locallyRingedSpaceObj (annulusIdealOfDefinition R I q) :=
  FormalSpectrum.locallyRingedSpaceMap (annulusIdealOfDefinition R I q)
    (I.map (algebraMap R (annulusAlgebra R I q))) (RingHom.id (annulusAlgebra R I q))
    (by
      rw [Ideal.comap_id]
      exact (annulus_map_eq R I q).ge)

/-- **The per-chart first projection** `Spf(A ⊗̂_R B) ⟶ Spf A` (into the `annulusIdealOfDefinition`
convention of the glued target `X`): the raw `Spf(inl)` first projection followed by the base
ideal-convention bridge. -/
def pr₁Chart :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) B) ⟶
      locallyRingedSpaceObj (annulusIdealOfDefinition R I q) :=
  FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (annulusAlgebra R I q)))
      (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) B)
      (CompletedTensorProduct.inl R I (annulusAlgebra R I q) B).toRingHom
      CompletedTensorProduct.inl_isAdicHom.le_comap ≫
    annulusBaseBridge R I q

/-! ### The overlap ideal-convention bridge -/

/-- The overlap ideal-convention bridge `Spf(A{1/x}) ⟶ Spf(A{1/x})` on the `x`-overlap, transporting
the `I·A`-convention completion `awayCompletion (I·A) x` (codomain of the affine basic-open chart
of `A` at `x`) to the `annulusIdealOfDefinition`-convention completion `awayCompletion (I·A_ann) x`.
It is `Spf` of the inverse `R`-algebra ideal-transport bridge `annulusFibreChartBridgeX`. -/
def annulusOverlapBridgeX :
    locallyRingedSpaceObj
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q)))) ⟶
      locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) :=
  FormalSpectrum.locallyRingedSpaceMap
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
    (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
      (overlapX R I q))))
    (annulusFibreChartBridgeX R I q).symm.toRingHom (by
      rw [FormalSpectrum.map_algebraMap_awayCompletion_eq, annulusFibreChartBridgeX,
        AdicCompletion.congrIdealₐ_symm_toRingHom]
      exact FormalSpectrum.le_comap_congrIdeal_symm _)

/-! ### Ring-hom cores of the two ideal-convention identifications -/

/-- The inverse bridge `annulusFibreChartBridgeX.symm` intertwines the two structural completion
maps of `A` at `x`: `bridgeX.symm ∘ awayCompletionHom(I·A_ann) = awayCompletionHom(I·A)`. Kept at
the `RingHom.comp` level, `congrIdeal` opaque. -/
theorem awayCompletionHom_bridgeX_symm :
    (annulusFibreChartBridgeX R I q).symm.toRingHom.comp
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)) =
      awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q) := by
  simp only [awayCompletionHom, annulusFibreChartBridgeX,
    AdicCompletion.congrIdealₐ_symm_toRingHom]
  rw [← RingHom.comp_assoc, AdicCompletion.congrIdeal_symm_toRingHom_comp_algebraMap]

/-- The forward bridge `annulusFibreChartBridgeY` intertwines the two structural completion maps of
`A` at `y`: `bridgeY ∘ awayCompletionHom(I·A) = awayCompletionHom(I·A_ann)`. -/
theorem awayCompletionHom_bridgeY :
    (annulusFibreChartBridgeY R I q).toRingHom.comp
        (awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) =
      awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q) := by
  simp only [awayCompletionHom, annulusFibreChartBridgeY,
    AdicCompletion.congrIdealₐ_toRingHom]
  rw [← RingHom.comp_assoc, AdicCompletion.congrIdeal_toRingHom_comp_algebraMap]

/-- The underlying ring hom of the inverse base-changed chart transition, unfolded through the two
ideal-convention bridges and `annulusChartTransitionAlg.symm`. Kept at the `RingHom.comp` level with
`congrIdeal` opaque (via `AlgEquiv.symm_trans_eq`, `algEquiv_trans_toRingHom`). -/
theorem annulusFibreChartTransitionAlg_symm_toRingHom (hI : I.FG) :
    (annulusFibreChartTransitionAlg R I q hI).symm.toRingHom =
      (annulusFibreChartBridgeX R I q).symm.toRingHom.comp
        ((annulusChartTransitionAlg R I q hI).symm.toRingHom.comp
          (annulusFibreChartBridgeY R I q).toRingHom) := by
  rw [annulusFibreChartTransitionAlg, AlgEquiv.symm_trans_eq, AlgEquiv.symm_trans_eq,
    AlgEquiv.symm_symm, algEquiv_trans_toRingHom, algEquiv_trans_toRingHom]

/-- The ring hom underlying `e.toAlgHom` is the ring hom underlying `e`. Stated (and proved by
`rfl`) at abstract types, used as a black-box coercion bridge. -/
theorem algEquiv_toAlgHom_toRingHom {S T U : Type u} [CommSemiring S] [Semiring T] [Semiring U]
    [Algebra S T] [Algebra S U] (e : T ≃ₐ[S] U) :
    e.toAlgHom.toRingHom = e.toRingHom :=
  rfl

/-! ### The two ideal-convention bridge squares -/

/-- **The affine first projection of `A` at `x`, transported to the target convention, factors
through the annulus overlap chart.** The `Spf`-completion chart `Spf(A{1/x}) ⟶ Spf A` in the `I·A`
convention, followed by the base ideal-convention bridge, equals the overlap ideal-convention bridge
followed by the annulus overlap chart `annulusOverlapChart : Spf(A{1/x}) ⟶ Spf A`. -/
theorem spfAwayX_comp_baseBridge :
    FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (annulusAlgebra R I q)))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))))
        (awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (le_comap_awayCompletionHom_base I (overlapX R I q)) ≫ annulusBaseBridge R I q =
      annulusOverlapBridgeX R I q ≫ annulusOverlapChart R I q := by
  have hLHS : annulusIdealOfDefinition R I q ≤
      (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q)))).comap
        ((awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)).comp
          (RingHom.id (annulusAlgebra R I q))) := by
    rw [RingHom.comp_id]
    exact (annulus_map_eq R I q).ge.trans
      (le_comap_awayCompletionHom_base I (overlapX R I q))
  have hRHS : annulusIdealOfDefinition R I q ≤
      (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q)))).comap
        ((annulusFibreChartBridgeX R I q).symm.toRingHom.comp
          (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q))) := by
    rw [awayCompletionHom_bridgeX_symm]
    exact (annulus_map_eq R I q).ge.trans
      (le_comap_awayCompletionHom_base I (overlapX R I q))
  rw [annulusBaseBridge, ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hLHS),
    annulusOverlapBridgeX, annulusOverlapChart, FormalSpectrum.basicOpenChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hRHS)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    ((RingHom.comp_id _).trans (awayCompletionHom_bridgeX_symm R I q).symm)

/-- **The base-changed transition, followed by the `y`-first-projection into the target convention,
factors through the annulus chart transition and the `y`-overlap chart.** This is the `y`-side
companion of `spfAwayX_comp_baseBridge`, incorporating the base-changed transition `Spf(e.symm)`. -/
theorem spfESymm_comp_spfAwayY_comp_baseBridge (hI : I.FG) :
    FormalSpectrum.locallyRingedSpaceMap
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))))
        (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))))
        (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom.toRingHom
        (CompletedTensorProduct.algHom_mapIdeal_isAdicHom
          (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom).le_comap ≫
      (FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (annulusAlgebra R I q)))
          (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q))))
          (awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
          (le_comap_awayCompletionHom_base I (overlapY R I q)) ≫ annulusBaseBridge R I q) =
      annulusOverlapBridgeX R I q ≫ (annulusChartTransitionSpf R I q hI).hom ≫
        annulusOverlapChartY R I q := by
  have hφ : (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom.toRingHom.comp
        ((awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)).comp
          (RingHom.id (annulusAlgebra R I q))) =
      (annulusFibreChartBridgeX R I q).symm.toRingHom.comp
        ((annulusChartTransitionAlg R I q hI).symm.toRingHom.comp
          (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q))) := by
    rw [algEquiv_toAlgHom_toRingHom, annulusFibreChartTransitionAlg_symm_toRingHom,
      RingHom.comp_id, RingHom.comp_assoc, RingHom.comp_assoc, awayCompletionHom_bridgeY]
  have hL_inner : annulusIdealOfDefinition R I q ≤
      (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q)))).comap
        ((awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)).comp
          (RingHom.id (annulusAlgebra R I q))) := by
    rw [RingHom.comp_id]
    exact (annulus_map_eq R I q).ge.trans
      (le_comap_awayCompletionHom_base I (overlapY R I q))
  have hR_inner : annulusIdealOfDefinition R I q ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)).comap
        ((annulusChartTransitionAlg R I q hI).symm.toRingHom.comp
          (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q))) :=
    le_comap_comp _ _
      (FormalSpectrum.le_comap_awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q))
      (annulusChartTransitionAlg_symm_le_comap R I q hI)
  have h3 : awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q) ≤
      (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q)))).comap (annulusFibreChartBridgeX R I q).symm.toRingHom := by
    rw [FormalSpectrum.map_algebraMap_awayCompletion_eq, annulusFibreChartBridgeX,
      AdicCompletion.congrIdealₐ_symm_toRingHom]
    exact FormalSpectrum.le_comap_congrIdeal_symm _
  have hR_outer : annulusIdealOfDefinition R I q ≤
      (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q)))).comap
        ((annulusFibreChartBridgeX R I q).symm.toRingHom.comp
          ((annulusChartTransitionAlg R I q hI).symm.toRingHom.comp
            (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)))) :=
    le_comap_comp _ _ hR_inner h3
  have hL_outer : annulusIdealOfDefinition R I q ≤
      (I.map (algebraMap R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q)))).comap
        ((annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom.toRingHom.comp
          ((awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)).comp
            (RingHom.id (annulusAlgebra R I q)))) := by
    rw [hφ]
    exact hR_outer
  rw [annulusChartTransitionSpf_hom_eq, annulusBaseBridge, annulusOverlapBridgeX,
    annulusOverlapChartY, FormalSpectrum.basicOpenChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hL_inner),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hL_outer),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hR_inner),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hR_outer)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ hφ

/-! ### The glue condition of the target `tateTwoPatch` -/

/-- **The `tateTwoPatch` glue relation on the double overlap.** The `x`-overlap chart into the glued
target equals the annulus chart transition followed by the `y`-overlap chart into the glued target:
`annulusOverlapChart ≫ ι₀ = annulusChartTransitionSpf.hom ≫ annulusOverlapChartY ≫ ι₁`. This is the
`glue_condition` of `tateTwoPatchLRSGlueData` on the `(false, true)` overlap, unfolded through the
`GlueData.ofGlueData'` construction. -/
theorem tateTwoPatch_glue_rel [IsNoetherianRing R] (hI : I.FG) :
    annulusOverlapChart R I q ≫ (tateTwoPatchFormalGlueData R I q hI).ι ⟨false⟩ =
      (annulusChartTransitionSpf R I q hI).hom ≫ annulusOverlapChartY R I q ≫
        (tateTwoPatchFormalGlueData R I q hI).ι ⟨true⟩ := by
  have h01 : ({ down := false } : ULift.{u} Bool) ≠ { down := true } := by decide
  have h10 : ({ down := true } : ULift.{u} Bool) ≠ { down := false } := by decide
  have key := (tateTwoPatchLRSGlueData R I q hI).toGlueData.glue_condition ⟨false⟩ ⟨true⟩
  set ι0 := (tateTwoPatchLRSGlueData R I q hI).toGlueData.ι ⟨false⟩ with hι0
  set ι1 := (tateTwoPatchLRSGlueData R I q hI).toGlueData.ι ⟨true⟩ with hι1
  simp only [tateTwoPatchLRSGlueData, tateTwoPatchGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
    dif_neg h01, dif_neg h10, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  rw [cancel_epi] at key
  exact key.symm

/-! ### The double-overlap compatibility squares -/

/-- **The double-overlap compatibility square of the first projection.** The `x`-overlap chart
followed by the per-chart first projection and the glue inclusion `ι₀` equals the base-changed
transition `t.hom` followed by the `y`-overlap chart, the first projection and `ι₁`. -/
theorem twoPatchFibreProduct_pr₁_naturality [IsNoetherianRing R] (hI : I.FG) :
    interchangeOpenImmersion (B := B) I (overlapX R I q) hI ≫ pr₁Chart R I q B ≫
        (tateTwoPatchFormalGlueData R I q hI).ι ⟨false⟩ =
      (twoPatchFibreProductTransition R I q B hI).hom ≫
        interchangeOpenImmersion (B := B) I (overlapY R I q) hI ≫ pr₁Chart R I q B ≫
          (tateTwoPatchFormalGlueData R I q hI).ι ⟨true⟩ := by
  simp only [pr₁Chart, Category.assoc]
  rw [reassoc_of% (interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl I (overlapX R I q) hI),
    reassoc_of% (interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl I (overlapY R I q) hI),
    twoPatchFibreProductTransition, mapSpfIso_hom,
    reassoc_of% (CompletedTensorProduct.mapSpf_comp_inlMap hI
      (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom
      (AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom),
    reassoc_of% (spfAwayX_comp_baseBridge R I q),
    tateTwoPatch_glue_rel R I q hI,
    reassoc_of% (spfESymm_comp_spfAwayY_comp_baseBridge R I q hI)]

/-- The reverse double-overlap compatibility square (`y`-side): derived from
`twoPatchFibreProduct_pr₁_naturality` by cancelling `t.inv ≫ t.hom`. -/
theorem twoPatchFibreProduct_pr₁_naturality' [IsNoetherianRing R] (hI : I.FG) :
    interchangeOpenImmersion (B := B) I (overlapY R I q) hI ≫ pr₁Chart R I q B ≫
        (tateTwoPatchFormalGlueData R I q hI).ι ⟨true⟩ =
      (twoPatchFibreProductTransition R I q B hI).inv ≫
        interchangeOpenImmersion (B := B) I (overlapX R I q) hI ≫ pr₁Chart R I q B ≫
          (tateTwoPatchFormalGlueData R I q hI).ι ⟨false⟩ := by
  rw [twoPatchFibreProduct_pr₁_naturality R I q B hI, Iso.inv_hom_id_assoc]

/-- **The first projection of the two-patch fibre product** `pr₁ : X ×_{Spf R} Spf B ⟶ X`, glued
from the two affine first projections `Spf(inl)` (transported to the target convention and composed
with the glue inclusions of `X`) via `FormalScheme.GlueData.glueMorphisms`, using the double-overlap
compatibility squares. -/
def twoPatchFibreProductPr₁ [IsNoetherianRing R] (hI : I.FG) :
    (twoPatchFibreProduct R I q B hI).toLocallyRingedSpace ⟶
      (tateTwoPatch R I q hI).toLocallyRingedSpace :=
  (twoPatchFibreProductFormalGlueData R I q B hI).glueMorphisms
    (fun i => pr₁Chart R I q B ≫ (tateTwoPatchFormalGlueData R I q hI).ι i) (by
      intro i j
      rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
      · simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
      · have h01 : ({ down := false } : ULift.{u} Bool) ≠ { down := true } := by decide
        have h10 : ({ down := true } : ULift.{u} Bool) ≠ { down := false } := by decide
        simp only [twoPatchFibreProductFormalGlueData, twoPatchFibreProductLRSGlueData,
          twoPatchFibreProductGlueData', CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', dif_neg h01, dif_neg h10, Category.assoc,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        congr 1
        exact twoPatchFibreProduct_pr₁_naturality R I q B hI
      · have h01 : ({ down := false } : ULift.{u} Bool) ≠ { down := true } := by decide
        have h10 : ({ down := true } : ULift.{u} Bool) ≠ { down := false } := by decide
        simp only [twoPatchFibreProductFormalGlueData, twoPatchFibreProductLRSGlueData,
          twoPatchFibreProductGlueData', CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', dif_neg h01, dif_neg h10, Category.assoc,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        congr 1
        exact twoPatchFibreProduct_pr₁_naturality' R I q B hI
      · simp only [CategoryTheory.GlueData.t_id, Category.id_comp])

end AlgebraicGeometry
