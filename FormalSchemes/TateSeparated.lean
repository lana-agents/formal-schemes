import FormalSchemes.TateSelfProductCone
import FormalSchemes.TateSelfProductProjectionRight
import FormalSchemes.DiagonalClosedEmbedding
import FormalSchemes.ClosedImmersionSections

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The diagonal of the Tate curve model and its separatedness over `Spf R`

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`, and let
`A = R{x, y}/(x·y − q)` be the coordinate ring of the formal Tate annulus. The Tate curve model
`𝔈_q = tateCurveModel` is glued from two copies of `Spf A`, and its self fibre product
`𝔈_q ×_{Spf R} 𝔈_q = tateSelfProduct` from the four charts `Spf(A ⊗̂_R A)`.

This file provides the **reusable bricks** for the **diagonal morphism**

```
Δ : 𝔈_q ⟶ 𝔈_q ×_{Spf R} 𝔈_q
```

which is glued from the per-chart affine diagonals `diagChart : Spf A ⟶ Spf(A ⊗̂_R A)`
(topology-free `Spf` of the codiagonal `∇ : A ⊗̂_R A →+* A`), each composed with the glue inclusion
of the
*diagonal* chart `(b, b)` of the product, via `FormalScheme.GlueData.glueMorphisms`. The goal is to
exhibit `Δ` as a common **section of both projections** `pr₁, pr₂`, hence a **split monomorphism**,
hence a **monomorphism** — the categorical statement that `𝔈_q` is separated over `Spf R`
(EGA I §10.15).

## Main definitions and results

* `AlgebraicGeometry.diagChart`: the per-chart affine diagonal `Spf A ⟶ Spf(A ⊗̂_R A)`, built
  topology-free at the `locallyRingedSpaceMap` level from `CompletedTensorProduct.codiagonal`.
* `AlgebraicGeometry.diagChart_comp_pr₁Chart`, `...diagChart_comp_pr₂Chart`: the **affine section
  identities** `Δ ≫ pr₁Chart = 𝟙` and `Δ ≫ pr₂Chart ≫ bridge = 𝟙`, from `∇ ∘ inl = ∇ ∘ inr = id`.
* `CompletedTensorProduct.codiagonal_naturality`: the topology-free **codiagonal naturality**
  `∇_{A'} ∘ (f ⊗̂ f) = f ∘ ∇_A`, the ring-level engine of the diagonal's naturality.
* `AlgebraicGeometry.tateSelfProduct_both_glue_condition`: the **product-side glue relation** at the
  diagonal charts `(false,false)`–`(true,true)`.
* `AlgebraicGeometry.tateSelfProductDiagonal`: the **glued diagonal** `Δ : 𝔈_q ⟶ 𝔈_q ×_{Spf R} 𝔈_q`.
* `AlgebraicGeometry.tateSelfProductDiagonal_comp_pr₁`, `...comp_pr₂`: the **glued section
  identities** `Δ ≫ pr₁ = 𝟙`, `Δ ≫ pr₂ = 𝟙`.
* `AlgebraicGeometry.isSplitMono_tateSelfProductDiagonal`,
  `AlgebraicGeometry.mono_tateSelfProductDiagonal`: `Δ` is a split monomorphism, hence a
  monomorphism — the separatedness of `𝔈_q` over `Spf R`.

## Route

The glued diagonal `tateSelfProductDiagonal` is assembled via `FormalScheme.GlueData.glueMorphisms`
over the source index `ULift Bool`, sending each source chart `b` to
`diagChart ≫ ι_prod(b, b)` — the affine diagonal into the *diagonal* product chart `(b, b)`.
The only non-trivial `glueMorphisms` compatibility is the **off-diagonal** source-overlap pair
`(⟨false⟩, ⟨true⟩)`, whose `x`-summand obligation is
```
annulusOverlapChart ≫ diagChart ≫ ι_prod(false,false)
  = (annulusChartTransitionSpf).hom ≫ annulusOverlapChartY ≫ diagChart ≫ ι_prod(true,true).
```
It is discharged (`diagBothGlue_fwd`/`_rev`) from two affine bricks: the **diagonal/localization
factorisation** `annulusOverlapChart ≫ diagChart = diagChartXX ≫ bothInterchangeOpenImmersion I x x`
(`overlapChart_comp_diagChart_x`, the geometric shadow of `codiagonal_naturality` for the
localization `A →ₐ A{1/x}`) and the **transition compatibility**
`diagChartXX ≫ (bothSummandDiag).hom = (annulusChartTransitionSpf).hom ≫ diagChartYY`
(`diagXX_transition`, again `codiagonal_naturality` for the chart transition), after which the
product glue relation `tateSelfProduct_both_glue_condition` closes the square. The glued section
identities are proved cone-style by `hom_ext` on the source cover, kept in pure term mode to avoid
the `ULift (Bool × Bool)` object-defeq wall, reducing per chart to the affine section identities
`diagChart_comp_pr₁Chart`/`_pr₂Chart`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct

universe u

namespace FormalSpectrum

/-- The structural completion map `awayCompletionHom K f : A →+* A{1/f}` is the algebra map
`algebraMap A (awayCompletion K f)` (both factor `A → A_f → A{1/f}`). This lets one bridge the
`awayCompletionHom` presentation against the scalar-tower `IsScalarTower.toAlgHom` presentation of
the same map. -/
theorem awayCompletionHom_eq_algebraMap {A : Type u} [CommRing A] (K : Ideal A) (f : A) :
    awayCompletionHom K f = algebraMap A (awayCompletion K f) := by
  rw [awayCompletionHom]
  exact (IsScalarTower.algebraMap_eq A (Localization.Away f) (awayCompletion K f)).symm

end FormalSpectrum

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
variable [TopologicalSpace A'] [IsAdicRing (I.map (algebraMap R A'))]

/-- Topology-free (in `R`) form of `codiagonal_inl`: `∇ (inl a) = a`. The Mathlib-layer
`codiagonal_inl` carries a spurious `[TopologicalSpace R]`, unavailable in the annulus layer. -/
private theorem codiag_inl' {B : Type u} [CommRing B] [Algebra R B] [TopologicalSpace B]
    [IsAdicRing (I.map (algebraMap R B))] (b : B) :
    codiagonal R I B (inl R I B B b) = b := by
  haveI : IsAdicComplete (I.map (algebraMap R B)) B :=
    ‹IsAdicRing (I.map (algebraMap R B))›.toIsAdicComplete
  rw [codiagonal, lift_inl, AlgHom.id_apply]

/-- Topology-free (in `R`) form of `codiagonal_inr`: `∇ (inr a) = a`. -/
private theorem codiag_inr' {B : Type u} [CommRing B] [Algebra R B] [TopologicalSpace B]
    [IsAdicRing (I.map (algebraMap R B))] (b : B) :
    codiagonal R I B (inr R I B B b) = b := by
  haveI : IsAdicComplete (I.map (algebraMap R B)) B :=
    ‹IsAdicRing (I.map (algebraMap R B))›.toIsAdicComplete
  rw [codiagonal, lift_inr, AlgHom.id_apply]

/-- **Naturality of the codiagonal.** For an `R`-algebra map `f : A →ₐ[R] A'` the codiagonal
square commutes: `∇_{A'} ∘ (f ⊗̂ f) = f ∘ ∇_A` (topology-free ring identity). This is the ring-level
input to the diagonal being natural, from which the geometric factorisation of the diagonal chart
through the localized both-factor chart follows. -/
theorem codiagonal_naturality (f : A →ₐ[R] A') (hI : I.FG) :
    (codiagonal R I A').comp (map hI f f) = f.toRingHom.comp (codiagonal R I A) := by
  haveI : IsAdicComplete (I.map (algebraMap R A')) A' :=
    ‹IsAdicRing (I.map (algebraMap R A'))›.toIsAdicComplete
  haveI : IsAdicRing (idealOfDefinition R I A A) := isAdicRing R I A A hI
  haveI : IsAdicRing (idealOfDefinition R I A' A') := isAdicRing R I A' A' hI
  refine hom_ext (I.map (algebraMap R A')) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · exact lift_mem_pow _ (le_refl _) (AlgHom.id R A') (AlgHom.id R A') hI m
      (map_mem_pow hI f f m hx)
  · have hy : codiagonal R I A x ∈ (I.map (algebraMap R A)) ^ m :=
      lift_mem_pow _ (le_refl _) (AlgHom.id R A) (AlgHom.id R A) hI m hx
    have hmem : f.toRingHom (codiagonal R I A x) ∈
        Ideal.map f.toRingHom ((I.map (algebraMap R A)) ^ m) := Ideal.mem_map_of_mem _ hy
    rwa [Ideal.map_pow, algHom_mapIdeal_isAdicHom f] at hmem
  · rw [RingHom.comp_apply, RingHom.comp_apply, map_inl, codiag_inl', codiag_inl']
    rfl
  · rw [RingHom.comp_apply, RingHom.comp_apply, map_inr, codiag_inr', codiag_inr']
    rfl

set_option linter.unusedSectionVars false in
/-- **Topology-free `codiagonal_le_comap`.** The codiagonal `∇ : A ⊗̂_R A →+* A` carries the ideal
of definition of `A ⊗̂_R A` into `I·A`. The Mathlib-layer `codiagonal_le_comap`
(`DiagonalClosedEmbedding`) carries spurious `[TopologicalSpace R] [IsAdicRing I]` section
variables, unavailable in the annulus layer; this is `lift_le_comap` specialised to `(id, id)`
(recall `∇ = lift (id, id)`), needing only completeness of `A` at `I·A`. -/
theorem codiagonal_le_comap' (hI : I.FG) :
    idealOfDefinition R I A A ≤ (I.map (algebraMap R A)).comap (codiagonal R I A) := by
  haveI : IsAdicComplete (I.map (algebraMap R A)) A :=
    ‹IsAdicRing (I.map (algebraMap R A))›.toIsAdicComplete
  rw [codiagonal]
  exact lift_le_comap (le_refl _) (AlgHom.id R A) (AlgHom.id R A) hI

/-- **The generic affine diagonal chart** `Spf B ⟶ Spf(B ⊗̂_R B)`, for any complete adic
`R`-algebra `B` whose ideal of definition is `I·B`, as `Spf` of the codiagonal. This is the
convention-agnostic engine behind `AlgebraicGeometry.diagChart`, applied here at the localized
charts `B = A{1/x}`. -/
def codiagChart (_hI : I.FG) [IsAdicRing (idealOfDefinition R I A A)] :
    locallyRingedSpaceObj (I.map (algebraMap R A)) ⟶
      locallyRingedSpaceObj (idealOfDefinition R I A A) :=
  FormalSpectrum.locallyRingedSpaceMap (idealOfDefinition R I A A) (I.map (algebraMap R A))
    (codiagonal R I A)
    (Ideal.map_le_iff_le_comap.mp (map_codiagonal_eq (R := R) (I := I) (A := A)).le)

/-- **Geometric naturality of the diagonal chart.** For an `R`-algebra map `f : A →ₐ[R] A'`, the
diagonal chart intertwines `Spf f` on the base with `mapSpf f f` on the tensor square:
`Spf f ≫ codiagChart_A = codiagChart_{A'} ≫ mapSpf f f`. This is the geometric shadow of
`codiagonal_naturality`, derived purely through `locallyRingedSpaceMap` functoriality. -/
theorem codiagChart_naturality (f : A →ₐ[R] A') (hI : I.FG)
    [IsAdicRing (idealOfDefinition R I A A)] [IsAdicRing (idealOfDefinition R I A' A')] :
    FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R A)) (I.map (algebraMap R A'))
        f.toRingHom (algHom_mapIdeal_isAdicHom f).le_comap ≫ codiagChart (A := A) hI =
      codiagChart (A := A') hI ≫ mapSpf hI f f := by
  have hL : idealOfDefinition R I A A ≤ (I.map (algebraMap R A')).comap
      (f.toRingHom.comp (codiagonal R I A)) := by
    refine Ideal.map_le_iff_le_comap.mp (le_of_eq ?_)
    rw [← Ideal.map_map, map_codiagonal_eq (R := R) (I := I) (A := A),
      ← algHom_mapIdeal_isAdicHom f]
  have hR : idealOfDefinition R I A A ≤ (I.map (algebraMap R A')).comap
      ((codiagonal R I A').comp (map hI f f)) := by
    refine Ideal.map_le_iff_le_comap.mp (le_of_eq ?_)
    rw [← Ideal.map_map, map_isAdicHom hI f f,
      map_codiagonal_eq (R := R) (I := I) (A := A')]
  rw [codiagChart, codiagChart, mapSpf, IsAdicHom.spfMap,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hL),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hR)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (codiagonal_naturality f hI).symm

end CompletedTensorProduct

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]

/-! ### The per-chart affine diagonal `diagChart` -/

/-- The adic-ring instance for `A = annulusAlgebra` in the `I·A` convention, obtained by
transporting `annulus_isAdicRing` across `annulus_map_eq`. Isolated as a named lemma so the
(kernel-expensive)
`▸`-transport is checked exactly once here, and every consumer references it opaquely by name — this
is what keeps `diagChart` and its section identities cheap to kernel-check. -/
theorem annulus_isAdicRing_map (hI : I.FG) :
    IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
  (annulus_map_eq R I q).symm ▸ annulus_isAdicRing R I q hI

/-- **The affine diagonal chart** `Spf A ⟶ Spf(A ⊗̂_R A)`, topology-free, as `Spf` of the codiagonal
(multiplication) `∇ : A ⊗̂_R A →+* A`. It is built at the `locallyRingedSpaceMap` level so that no
`TopologicalSpace R` instance is needed (the annulus layer carries no topology on the base). -/
def diagChart (hI : I.FG) :
    locallyRingedSpaceObj (annulusIdealOfDefinition R I q) ⟶
      locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
          (annulusAlgebra R I q)) :=
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
  FormalSpectrum.locallyRingedSpaceMap
    (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
    (annulusIdealOfDefinition R I q)
    (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q))
    (by
      refine Ideal.map_le_iff_le_comap.mp ?_
      rw [CompletedTensorProduct.map_codiagonal_eq (R := R) (I := I)
        (A := annulusAlgebra R I q)]
      exact (annulus_map_eq R I q).le)

/-! ### The affine section identities of the diagonal chart -/

/-- **Common section skeleton.** For any ring map `ι : A →+* A ⊗̂_R A` that splits the codiagonal
(`∇ ∘ ι = id`) and carries `I·A` into the ideal of definition, the diagonal chart is a section of
`Spf(ι)` transported through the base ideal-convention bridge: `Δ ≫ Spf(ι) ≫ bridge = 𝟙 (Spf A)`.
Applied to `ι = inl` this is the first-projection section identity, and to `ι = inr` the second. -/
private theorem diagChart_comp_bridge (hI : I.FG)
    [IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q)))]
    [IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q))]
    (ι : annulusAlgebra R I q →+*
      CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q))
    (hι : I.map (algebraMap R (annulusAlgebra R I q)) ≤
      (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q)).comap ι)
    (hcomp : (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q)).comp ι =
      RingHom.id (annulusAlgebra R I q)) :
    diagChart R I q hI ≫
        FormalSpectrum.locallyRingedSpaceMap
          (I.map (algebraMap R (annulusAlgebra R I q)))
          (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
            (annulusAlgebra R I q)) ι hι ≫
        annulusBaseBridge R I q =
      𝟙 (locallyRingedSpaceObj (annulusIdealOfDefinition R I q)) := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  have hIK1 : I.map (algebraMap R (annulusAlgebra R I q)) ≤
      (annulusIdealOfDefinition R I q).comap
        ((CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q)).comp ι) := by
    rw [hcomp, Ideal.comap_id]
    exact (annulus_map_eq R I q).le
  have hIK2 : annulusIdealOfDefinition R I q ≤
      (annulusIdealOfDefinition R I q).comap
        (((CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q)).comp ι).comp
          (RingHom.id (annulusAlgebra R I q))) := by
    rw [RingHom.comp_id, hcomp, Ideal.comap_id]
  rw [diagChart, annulusBaseBridge, ← Category.assoc,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK1),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK2)]
  refine (FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ (RingHom.id (annulusAlgebra R I q)) _
    (Ideal.comap_id (annulusIdealOfDefinition R I q)).ge ?_).trans
    (FormalSpectrum.locallyRingedSpaceMap_id (annulusIdealOfDefinition R I q))
  rw [RingHom.comp_id, hcomp]

/-- **The diagonal is a section of the first projection** (affine level):
`Δ ≫ pr₁Chart = 𝟙 (Spf A)`, since `∇ ∘ inl = id`. -/
theorem diagChart_comp_pr₁Chart (hI : I.FG) :
    diagChart R I q hI ≫ pr₁Chart R I q (annulusAlgebra R I q) =
      𝟙 (locallyRingedSpaceObj (annulusIdealOfDefinition R I q)) := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
  rw [pr₁Chart_eq]
  exact diagChart_comp_bridge R I q hI
    (CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)).toRingHom
    CompletedTensorProduct.inl_isAdicHom.le_comap
    (RingHom.ext fun a => CompletedTensorProduct.codiag_inl' a)

/-- **The diagonal is a section of the second projection** (affine level):
`Δ ≫ pr₂Chart ≫ bridge = 𝟙 (Spf A)`, since `∇ ∘ inr = id`. -/
theorem diagChart_comp_pr₂Chart (hI : I.FG) :
    diagChart R I q hI ≫ pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫
        annulusBaseBridge R I q =
      𝟙 (locallyRingedSpaceObj (annulusIdealOfDefinition R I q)) := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
  exact diagChart_comp_bridge R I q hI
    (CompletedTensorProduct.inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)).toRingHom
    CompletedTensorProduct.inr_isAdicHom.le_comap
    (RingHom.ext fun a => CompletedTensorProduct.codiag_inr' a)

/-! ### The product-side glue relation at the diagonal charts -/

omit [IsNoetherianRing R] in
/-- **The diagonal-chart glue relation of the self-fibre product.** On the
`(false,false)`–`(true,true)` overlap of `tateSelfProduct` (a both-factor-differing pair, whose
overlap chart is `bothFactorOverlapChart` and whose transition is `tateSelfProductBothTransition`),
the glue inclusion of the `(false,false)` chart equals the both-factor transition followed by the
glue inclusion of the
`(true,true)` chart. Extracted from the `LocallyRingedSpace.GlueData.glue_condition`, mirroring
`tateCurve_glue_condition`. -/
theorem tateSelfProduct_both_glue_condition (hq : q ∈ I) (hI : I.FG) :
    bothFactorOverlapChart R I q hI ≫
        (tateSelfProductFormalGlueData R I q hq hI).ι ⟨(false, false)⟩ =
      (tateSelfProductBothTransition R I q hI).hom ≫ bothFactorOverlapChart R I q hI ≫
        (tateSelfProductFormalGlueData R I q hq hI).ι ⟨(true, true)⟩ := by
  have h01 : ({ down := (false, false) } : ULift.{u} (Bool × Bool)) ≠ { down := (true, true) } := by
    decide
  have h10 : ({ down := (true, true) } : ULift.{u} (Bool × Bool)) ≠ { down := (false, false) } := by
    decide
  have key := (tateSelfProductLRSGlueData R I q hq hI).toGlueData.glue_condition
    ⟨(false, false)⟩ ⟨(true, true)⟩
  set ι0 := (tateSelfProductLRSGlueData R I q hq hI).toGlueData.ι ⟨(false, false)⟩ with hι0
  set ι1 := (tateSelfProductLRSGlueData R I q hq hI).toGlueData.ι ⟨(true, true)⟩ with hι1
  simp only [tateSelfProductLRSGlueData, tateSelfProductGlueData',
    tateSelfProductGlueF, tateSelfProductGlueT,
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
    dif_neg h01, dif_neg h10, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  rw [cancel_epi] at key
  exact key.symm

omit [IsNoetherianRing R] in
/-- **The diagonal-chart glue relation of the self-fibre product.** On the
`(false,false)`–`(true,true)` overlap of `tateSelfProduct` (a both-factor-differing pair, whose
overlap chart is `bothFactorOverlapChart` and whose transition is the inversion both-transition),
the glue inclusion of the `(false,false)` chart equals the both-factor transition followed by the
glue inclusion of the
`(true,true)` chart. Extracted from the `LocallyRingedSpace.GlueData.glue_condition`, mirroring
`tateCurve_glue_condition`. -/
theorem tateSelfProduct_both_glue_condition_inv (hq : q ∈ I) (hI : I.FG) :
    bothFactorOverlapChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ =
      (tateSelfProductBothTransitionInv R I q hI).hom ≫ bothFactorOverlapChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
  have h01 : ({ down := (false, false) } : ULift.{u} (Bool × Bool)) ≠ { down := (true, true) } := by
    decide
  have h10 : ({ down := (true, true) } : ULift.{u} (Bool × Bool)) ≠ { down := (false, false) } := by
    decide
  have key := (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.glue_condition
    ⟨(false, false)⟩ ⟨(true, true)⟩
  set ι0 := (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(false, false)⟩
    with hι0
  set ι1 := (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.ι ⟨(true, true)⟩ with hι1
  simp only [tateSelfProductLRSGlueDataInv, tateSelfProductGlueData'Inv,
    tateSelfProductGlueF, tateSelfProductGlueTInv,
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
    dif_neg h01, dif_neg h10, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  rw [cancel_epi] at key
  exact key.symm

end AlgebraicGeometry

namespace AlgebraicGeometry

open CompletedTensorAwayInterchange

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]

/-! ### The per-chart localized diagonals and their factorisations -/

omit [IsNoetherianRing R] in
/-- Localized adic-ring instance for the `x`-chart `A{1/x}`. -/
theorem isAdicRing_locX (hI : I.FG) : IsAdicRing (I.map (algebraMap R
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))) := by
  rw [← CompletedTensorAwayInterchange.idealOfDef_Achart_eq (A := annulusAlgebra R I q) I
    (overlapX R I q)]
  exact AdicCompletion.isAdicRing_map _ ((hI.map _).map _)

omit [IsNoetherianRing R] in
/-- Localized adic-ring instance for the `y`-chart `A{1/y}`. -/
theorem isAdicRing_locY (hI : I.FG) : IsAdicRing (I.map (algebraMap R
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) := by
  rw [← CompletedTensorAwayInterchange.idealOfDef_Achart_eq (A := annulusAlgebra R I q) I
    (overlapY R I q)]
  exact AdicCompletion.isAdicRing_map _ ((hI.map _).map _)

omit [IsNoetherianRing R] in
/-- The ideal-convention bridge intertwines the two `x`-chart structural completion maps in the
forward direction: `bridgeX ∘ awayCompletionHom(I·A) = awayCompletionHom(annIdeal)`. -/
theorem bridgeX_comp_awayCompletionHom :
    (annulusFibreChartBridgeX R I q).toRingHom.comp
        (awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) =
      awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q) := by
  simp only [awayCompletionHom, annulusFibreChartBridgeX,
    AdicCompletion.congrIdealₐ_toRingHom]
  rw [← RingHom.comp_assoc, AdicCompletion.congrIdeal_toRingHom_comp_algebraMap]

/-- **The `(x,x)` diagonal summand chart** `Spf A{1/x} ⟶ Spf(A{1/x} ⊗̂_R A{1/x})`: the codiagonal
of the localized chart `A{1/x}`, presented over the `annulusIdealOfDefinition`-convention domain via
the ideal-convention bridge `annulusFibreChartBridgeX`. -/
def diagChartXX (hI : I.FG) :
    locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) ⟶
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
  haveI hax : IsAdicRing (I.map (algebraMap R
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))) :=
    isAdicRing_locX R I q hI
  FormalSpectrum.locallyRingedSpaceMap
    (CompletedTensorProduct.idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
    ((annulusFibreChartBridgeX R I q).toRingHom.comp
      (CompletedTensorProduct.codiagonal R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))))
    (by
      haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
        CompletedTensorProduct.isAdicRing R I _ _ hI
      refine (CompletedTensorProduct.codiagonal_le_comap' (A :=
        awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) hI).trans ?_
      rw [← Ideal.comap_comap]
      refine Ideal.comap_mono ?_
      rw [annulusFibreChartBridgeX, AdicCompletion.congrIdealₐ_toRingHom,
        ← CompletedTensorAwayInterchange.idealOfDef_Achart_eq (A := annulusAlgebra R I q) I
          (overlapX R I q)]
      exact FormalSpectrum.le_comap_congrIdeal _)

/-- **The `(y,y)` diagonal summand chart** `Spf A{1/y} ⟶ Spf(A{1/y} ⊗̂_R A{1/y})`. -/
def diagChartYY (hI : I.FG) :
    locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)) ⟶
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
  haveI hay : IsAdicRing (I.map (algebraMap R
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) :=
    isAdicRing_locY R I q hI
  FormalSpectrum.locallyRingedSpaceMap
    (CompletedTensorProduct.idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
    ((annulusFibreChartBridgeY R I q).toRingHom.comp
      (CompletedTensorProduct.codiagonal R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))))
    (by
      haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
        CompletedTensorProduct.isAdicRing R I _ _ hI
      refine (CompletedTensorProduct.codiagonal_le_comap' (A :=
        awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) hI).trans ?_
      rw [← Ideal.comap_comap]
      refine Ideal.comap_mono ?_
      rw [annulusFibreChartBridgeY, AdicCompletion.congrIdealₐ_toRingHom,
        ← CompletedTensorAwayInterchange.idealOfDef_Achart_eq (A := annulusAlgebra R I q) I
          (overlapY R I q)]
      exact FormalSpectrum.le_comap_congrIdeal _)

/-- **Diagonal/localization factorisation (x).** The `x`-overlap chart followed by the affine
diagonal factors through the localized `(x,x)` diagonal and the both-factor interchange chart. -/
theorem overlapChart_comp_diagChart_x (hI : I.FG) :
    annulusOverlapChart R I q ≫ diagChart R I q hI =
      diagChartXX R I q hI ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapX R I q) (overlapX R I q) hI := by
  haveI hax : IsAdicRing (I.map (algebraMap R
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))) :=
    isAdicRing_locX R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hring : (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)).comp
        (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q)) =
      ((annulusFibreChartBridgeX R I q).toRingHom.comp
          (CompletedTensorProduct.codiagonal R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))).comp
        (CompletedTensorProduct.map hI
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))) := by
    have hg : (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q))).toRingHom =
        awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q) :=
      (FormalSpectrum.awayCompletionHom_eq_algebraMap _ _).symm
    rw [RingHom.comp_assoc,
      CompletedTensorProduct.codiagonal_naturality
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) hI,
      ← RingHom.comp_assoc, hg, bridgeX_comp_awayCompletionHom]
  have hIK_L : CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q) ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)).comap
        ((awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)).comp
          (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q))) := by
    rw [← Ideal.comap_comap]
    refine (CompletedTensorProduct.codiagonal_le_comap' hI).trans (Ideal.comap_mono ?_)
    exact (annulus_map_eq R I q).le.trans
      (FormalSpectrum.le_comap_awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q))
  have hIK_R : CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q) ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)).comap
        (((annulusFibreChartBridgeX R I q).toRingHom.comp
            (CompletedTensorProduct.codiagonal R I
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))).comp
          (CompletedTensorProduct.map hI
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))))) := by
    rw [← hring]; exact hIK_L
  rw [annulusOverlapChart, FormalSpectrum.basicOpenChart, diagChart, diagChartXX,
    bothInterchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK_L),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK_R)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ hring

/-- **Diagonal/localization factorisation (y).** -/
theorem overlapChart_comp_diagChart_y (hI : I.FG) :
    annulusOverlapChartY R I q ≫ diagChart R I q hI =
      diagChartYY R I q hI ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapY R I q) (overlapY R I q) hI := by
  haveI hay : IsAdicRing (I.map (algebraMap R
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) :=
    isAdicRing_locY R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hring : (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)).comp
        (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q)) =
      ((annulusFibreChartBridgeY R I q).toRingHom.comp
          (CompletedTensorProduct.codiagonal R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))).comp
        (CompletedTensorProduct.map hI
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) := by
    have hg : (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q))).toRingHom =
        awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q) :=
      (FormalSpectrum.awayCompletionHom_eq_algebraMap _ _).symm
    rw [RingHom.comp_assoc,
      CompletedTensorProduct.codiagonal_naturality
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) hI,
      ← RingHom.comp_assoc, hg, awayCompletionHom_bridgeY]
  have hIK_L : CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q) ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)).comap
        ((awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)).comp
          (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q))) := by
    rw [← Ideal.comap_comap]
    refine (CompletedTensorProduct.codiagonal_le_comap' hI).trans (Ideal.comap_mono ?_)
    exact (annulus_map_eq R I q).le.trans
      (FormalSpectrum.le_comap_awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q))
  have hIK_R : CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q) ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)).comap
        (((annulusFibreChartBridgeY R I q).toRingHom.comp
            (CompletedTensorProduct.codiagonal R I
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))).comp
          (CompletedTensorProduct.map hI
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))))) := by
    rw [← hring]; exact hIK_L
  rw [annulusOverlapChartY, FormalSpectrum.basicOpenChart, diagChart, diagChartYY,
    bothInterchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK_L),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK_R)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ hring

/-! ### The transition reconciliation on the diagonal charts -/

omit [IsNoetherianRing R] in
/-- **Diagonal-chart transition reconciliation.** Through the affine diagonals, the annulus chart
transition `annulusChartTransitionSpf` realises the diagonal both-summand transition
`bothSummandDiag`. The proof reduces (via `codiagonal_naturality` and the clean `lrsMap`-form
`annulusChartTransitionSpf_hom_eq`) to the bridge identity
`annulusFibreChartTransitionAlg_symm_toRingHom`. The `le_comap` witness of the tensor-map leg is
obtained from the cheap witness of the transition leg through the ring-hom equality `hring`,
avoiding a whnf explosion over the completed-tensor tower. -/
theorem diagXX_transition (hI : I.FG) :
    diagChartXX R I q hI ≫ (bothSummandDiag R I q hI).hom =
      (annulusChartTransitionSpf R I q hI).hom ≫ diagChartYY R I q hI := by
  haveI hax : IsAdicRing (I.map (algebraMap R
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))) :=
    isAdicRing_locX R I q hI
  haveI hay : IsAdicRing (I.map (algebraMap R
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) :=
    isAdicRing_locY R I q hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hid : (annulusFibreChartBridgeX R I q).toRingHom.comp
      (annulusFibreChartBridgeX R I q).symm.toRingHom = RingHom.id _ := by
    simp only [annulusFibreChartBridgeX, AdicCompletion.congrIdealₐ_toRingHom,
      AdicCompletion.congrIdealₐ_symm_toRingHom]
    exact RingEquiv.toRingHom_comp_symm_toRingHom _
  have hcore : (annulusFibreChartBridgeX R I q).toRingHom.comp
        (annulusFibreChartTransitionAlg R I q hI).symm.toRingHom =
      (annulusChartTransitionAlg R I q hI).symm.toRingHom.comp
        (annulusFibreChartBridgeY R I q).toRingHom := by
    rw [annulusFibreChartTransitionAlg_symm_toRingHom, ← RingHom.comp_assoc, hid, RingHom.id_comp]
  have hring : ((annulusFibreChartBridgeX R I q).toRingHom.comp
          (CompletedTensorProduct.codiagonal R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))).comp
        (CompletedTensorProduct.map hI
          (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom
          (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom) =
      (annulusChartTransitionAlg R I q hI).symm.toRingHom.comp
        ((annulusFibreChartBridgeY R I q).toRingHom.comp
          (CompletedTensorProduct.codiagonal R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) := by
    rw [RingHom.comp_assoc,
      CompletedTensorProduct.codiagonal_naturality
        (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom hI,
      algEquiv_toAlgHom_toRingHom, ← RingHom.comp_assoc, hcore, RingHom.comp_assoc]
  have hIK_R : CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)).comap
        ((annulusChartTransitionAlg R I q hI).symm.toRingHom.comp
          ((annulusFibreChartBridgeY R I q).toRingHom.comp
            (CompletedTensorProduct.codiagonal R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))))) := by
    rw [← Ideal.comap_comap, ← Ideal.comap_comap]
    refine (CompletedTensorProduct.codiagonal_le_comap' hI).trans (Ideal.comap_mono ?_)
    have hbY : I.map (algebraMap R
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) ≤
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)).comap
          (annulusFibreChartBridgeY R I q).toRingHom := by
      rw [annulusFibreChartBridgeY, AdicCompletion.congrIdealₐ_toRingHom,
        ← CompletedTensorAwayInterchange.idealOfDef_Achart_eq (A := annulusAlgebra R I q) I
          (overlapY R I q)]
      exact FormalSpectrum.le_comap_congrIdeal _
    exact hbY.trans (Ideal.comap_mono (annulusChartTransitionAlg_symm_le_comap R I q hI))
  have hIK_L : CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)).comap
        (((annulusFibreChartBridgeX R I q).toRingHom.comp
            (CompletedTensorProduct.codiagonal R I
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))).comp
          (CompletedTensorProduct.map hI
            (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom
            (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom)) := by
    rw [hring]; exact hIK_R
  rw [diagChartXX, bothSummandDiag, CompletedTensorProduct.mapSpfIso_hom,
    CompletedTensorProduct.mapSpf_eq, annulusChartTransitionSpf_hom_eq, diagChartYY,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK_L),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK_R)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ hring

set_option maxRecDepth 4000 in
omit [IsNoetherianRing R] in
/-- Diagonal-chart transition reconciliation (inversion); mirror of `diagXX_transition`
with the 𝔾m-inversion transition. -/
theorem diagXX_transition_inv (hI : I.FG) :
    diagChartXX R I q hI ≫ (bothSummandDiagInv R I q hI).hom =
      (annulusChartTransitionInvSpf R I q hI).hom ≫ diagChartYY R I q hI := by
  haveI hax : IsAdicRing (I.map (algebraMap R
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))) :=
    isAdicRing_locX R I q hI
  haveI hay : IsAdicRing (I.map (algebraMap R
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) :=
    isAdicRing_locY R I q hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hid : (annulusFibreChartBridgeX R I q).toRingHom.comp
      (annulusFibreChartBridgeX R I q).symm.toRingHom = RingHom.id _ := by
    simp only [annulusFibreChartBridgeX, AdicCompletion.congrIdealₐ_toRingHom,
      AdicCompletion.congrIdealₐ_symm_toRingHom]
    exact RingEquiv.toRingHom_comp_symm_toRingHom _
  have hcore : (annulusFibreChartBridgeX R I q).toRingHom.comp
        (annulusFibreChartTransitionInvAlg R I q hI).symm.toRingHom =
      (annulusChartTransitionInvAlg R I q hI).symm.toRingHom.comp
        (annulusFibreChartBridgeY R I q).toRingHom := by
    rw [annulusFibreChartTransitionInvAlg_symm_toRingHom, ← RingHom.comp_assoc, hid,
      RingHom.id_comp]
  have hring : ((annulusFibreChartBridgeX R I q).toRingHom.comp
          (CompletedTensorProduct.codiagonal R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))).comp
        (CompletedTensorProduct.map hI
          (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom
          (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom) =
      (annulusChartTransitionInvAlg R I q hI).symm.toRingHom.comp
        ((annulusFibreChartBridgeY R I q).toRingHom.comp
          (CompletedTensorProduct.codiagonal R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) := by
    rw [RingHom.comp_assoc,
      CompletedTensorProduct.codiagonal_naturality
        (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom hI,
      algEquiv_toAlgHom_toRingHom, ← RingHom.comp_assoc, hcore, RingHom.comp_assoc]
  have hIK_R : CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)).comap
        ((annulusChartTransitionInvAlg R I q hI).symm.toRingHom.comp
          ((annulusFibreChartBridgeY R I q).toRingHom.comp
            (CompletedTensorProduct.codiagonal R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))))) := by
    rw [← Ideal.comap_comap, ← Ideal.comap_comap]
    refine (CompletedTensorProduct.codiagonal_le_comap' hI).trans (Ideal.comap_mono ?_)
    have hbY : I.map (algebraMap R
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) ≤
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)).comap
          (annulusFibreChartBridgeY R I q).toRingHom := by
      rw [annulusFibreChartBridgeY, AdicCompletion.congrIdealₐ_toRingHom,
        ← CompletedTensorAwayInterchange.idealOfDef_Achart_eq (A := annulusAlgebra R I q) I
          (overlapY R I q)]
      exact FormalSpectrum.le_comap_congrIdeal _
    exact hbY.trans (Ideal.comap_mono (annulusChartTransitionInvAlg_symm_le_comap R I q hI))
  have hIK_L : CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)).comap
        (((annulusFibreChartBridgeX R I q).toRingHom.comp
            (CompletedTensorProduct.codiagonal R I
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))).comp
          (CompletedTensorProduct.map hI
            (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom
            (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom)) := by
    rw [hring]; exact hIK_R
  rw [diagChartXX, bothSummandDiagInv, CompletedTensorProduct.mapSpfIso_hom,
    CompletedTensorProduct.mapSpf_eq, annulusChartTransitionInvSpf_hom_eq, diagChartYY,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK_L),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK_R)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ hring

omit [IsNoetherianRing R] in
/-- The inverse form of `diagXX_transition`. -/
theorem diagYY_transition_inv (hI : I.FG) :
    diagChartYY R I q hI ≫ (bothSummandDiag R I q hI).inv =
      (annulusChartTransitionSpf R I q hI).inv ≫ diagChartXX R I q hI := by
  rw [Iso.comp_inv_eq, Category.assoc, diagXX_transition R I q hI, Iso.inv_hom_id_assoc]

omit [IsNoetherianRing R] in
/-- The inverse form of `diagXX_transition_inv`. -/
theorem diagYY_transition_inv_inv (hI : I.FG) :
    diagChartYY R I q hI ≫ (bothSummandDiagInv R I q hI).inv =
      (annulusChartTransitionInvSpf R I q hI).inv ≫ diagChartXX R I q hI := by
  rw [Iso.comp_inv_eq, Category.assoc, diagXX_transition_inv R I q hI, Iso.inv_hom_id_assoc]

/-! ### The per-summand diagonal glue relations of the self-product -/

omit [IsNoetherianRing R] in
/-- The `(x,x)` diagonal chart glue relation, extracted from the inversion both-glue relation
`tateSelfProduct_both_glue_condition_inv` by precomposition with the `(x,x)`-summand inclusion. -/
theorem diagBoth_glue_xx (hq : q ∈ I) (hI : I.FG) :
    bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
        (overlapX R I q) (overlapX R I q) hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ =
      (bothSummandDiagInv R I q hI).hom ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapY R I q) (overlapY R I q) hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
  have h := congrArg (fun m => (coprod.inl ≫ coprod.inl) ≫ m)
    (tateSelfProduct_both_glue_condition_inv R I q hq hI)
  simpa only [bothFactorOverlapChart, tateSelfProductBothTransitionInv, Category.assoc,
    coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc] using h

omit [IsNoetherianRing R] in
/-- The `(y,y)` diagonal chart glue relation. -/
theorem diagBoth_glue_yy (hq : q ∈ I) (hI : I.FG) :
    bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
        (overlapY R I q) (overlapY R I q) hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ =
      (bothSummandDiagInv R I q hI).inv ≫
        bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
          (overlapX R I q) (overlapX R I q) hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
  have h := congrArg (fun m => (coprod.inr ≫ coprod.inr) ≫ m)
    (tateSelfProduct_both_glue_condition_inv R I q hq hI)
  simpa only [bothFactorOverlapChart, tateSelfProductBothTransitionInv, Category.assoc,
    coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc] using h

omit [IsNoetherianRing R] in
/-- The chart-swap transition datum of `𝔈_q` is its own inverse. -/
theorem chartSwap_selfinv (hI : I.FG) :
    coprod.desc ((annulusChartTransitionInvSpf R I q hI).hom ≫ coprod.inr)
        ((annulusChartTransitionInvSpf R I q hI).inv ≫ coprod.inl) ≫
      coprod.desc ((annulusChartTransitionInvSpf R I q hI).hom ≫ coprod.inr)
        ((annulusChartTransitionInvSpf R I q hI).inv ≫ coprod.inl) =
      𝟙 (locallyRingedSpaceObj
          (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) ⨿
        locallyRingedSpaceObj
          (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))) := by
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, coprod.inl_desc, Category.assoc, coprod.inr_desc,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  · rw [← Category.assoc, coprod.inr_desc, Category.assoc, coprod.inl_desc,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]

/-- x-summand of the forward diagonal glue relation on the `(false,true)` source overlap. -/
theorem diagBothSummandX_fwd (hq : q ∈ I) (hI : I.FG) :
    annulusOverlapChart R I q ≫ diagChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ =
      (annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q ≫
        diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
  rw [reassoc_of% (overlapChart_comp_diagChart_x R I q hI), diagBoth_glue_xx R I q hq hI,
    reassoc_of% (diagXX_transition_inv R I q hI),
    ← reassoc_of% (overlapChart_comp_diagChart_y R I q hI)]

/-- y-summand of the forward diagonal glue relation. -/
theorem diagBothSummandY_fwd (hq : q ∈ I) (hI : I.FG) :
    annulusOverlapChartY R I q ≫ diagChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ =
      (annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapChart R I q ≫ diagChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
  rw [reassoc_of% (overlapChart_comp_diagChart_y R I q hI), diagBoth_glue_yy R I q hq hI,
    reassoc_of% (diagYY_transition_inv_inv R I q hI),
    ← reassoc_of% (overlapChart_comp_diagChart_x R I q hI)]

/-- **Forward diagonal glue relation** on the `(false,true)` source overlap. -/
theorem diagBothGlue_fwd (hq : q ∈ I) (hI : I.FG) :
    coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q) ≫
        diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ =
      coprod.desc ((annulusChartTransitionInvSpf R I q hI).hom ≫ coprod.inr)
          ((annulusChartTransitionInvSpf R I q hI).inv ≫ coprod.inl) ≫
        coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q) ≫
          diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
  refine coprod.hom_ext ?_ ?_
  · simp only [coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact diagBothSummandX_fwd R I q hq hI
  · simp only [coprod.inr_desc_assoc, coprod.inl_desc_assoc, Category.assoc]
    exact diagBothSummandY_fwd R I q hq hI

/-- **Reverse diagonal glue relation** on the `(true,false)` source overlap, from the forward
relation and the self-inverse property of the chart-swap transition. -/
theorem diagBothGlue_rev (hq : q ∈ I) (hI : I.FG) :
    coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q) ≫
        diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ =
      coprod.desc ((annulusChartTransitionInvSpf R I q hI).hom ≫ coprod.inr)
          ((annulusChartTransitionInvSpf R I q hI).inv ≫ coprod.inl) ≫
        coprod.desc (annulusOverlapChart R I q) (annulusOverlapChartY R I q) ≫
          diagChart R I q hI ≫
            (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ := by
  rw [diagBothGlue_fwd R I q hq hI, reassoc_of% (chartSwap_selfinv R I q hI)]

/-! ### The glued diagonal, its section identities, and separatedness -/

/-- **The glued diagonal** `Δ : 𝔈_q ⟶ 𝔈_q ×_{Spf R} 𝔈_q`, glued from the per-chart affine diagonals
`diagChart` composed with the glue inclusion of the diagonal product chart `(b, b)`. -/
def tateSelfProductDiagonal (hq : q ∈ I) (hI : I.FG) :
    (tateCurveModel R I q hq hI).toLocallyRingedSpace ⟶
      (tateSelfProductInv R I q hq hI).toLocallyRingedSpace :=
  (tateCurveFormalGlueData R I q hq hI).glueMorphisms
    (fun b => diagChart R I q hI ≫
      (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(b.down, b.down)⟩) (by
      intro i j
      by_cases hij : i = j
      · subst hij
        simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
      · have hij' : ¬ @Eq (ULift.{u} Bool) i j := hij
        have hji' : ¬ @Eq (ULift.{u} Bool) j i := fun h => hij h.symm
        simp only [tateCurveFormalGlueData, tateCurveLRSGlueData, tateCurveGlueData',
          CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij',
          dif_neg hji', Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        congr 1
        rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩ <;>
          first
            | exact absurd rfl hij'
            | exact diagBothGlue_fwd R I q hq hI
            | exact diagBothGlue_rev R I q hq hI)

/-- **The diagonal is a section of the first projection**: `Δ ≫ pr₁ = 𝟙`. -/
theorem tateSelfProductDiagonal_comp_pr₁ (hq : q ∈ I) (hI : I.FG) :
    tateSelfProductDiagonal R I q hq hI ≫ tateSelfProductPr₁ R I q hq hI = 𝟙 _ := by
  refine (tateCurveFormalGlueData R I q hq hI).hom_ext (fun b => ?_)
  have hΔ : (tateCurveFormalGlueData R I q hq hI).ι b ≫ tateSelfProductDiagonal R I q hq hI =
      diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(b.down, b.down)⟩ := by
    rw [tateSelfProductDiagonal]
    exact (tateCurveFormalGlueData R I q hq hI).ι_glueMorphisms _ _ b
  have hpr : (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(b.down, b.down)⟩ ≫
        tateSelfProductPr₁ R I q hq hI =
      pr₁Chart R I q (annulusAlgebra R I q) ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨b.down⟩ := by
    rw [tateSelfProductPr₁]
    exact (tateSelfProductFormalGlueDataInv R I q hq hI).ι_glueMorphisms _ _ ⟨(b.down, b.down)⟩
  have key : (tateCurveFormalGlueData R I q hq hI).ι b ≫
        tateSelfProductDiagonal R I q hq hI ≫ tateSelfProductPr₁ R I q hq hI =
      (tateCurveFormalGlueData R I q hq hI).ι b :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ tateSelfProductPr₁ R I q hq hI) hΔ).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (diagChart R I q hI ≫ ·) hpr).trans <|
            (Category.assoc _ _ _).symm.trans <|
              (congrArg (· ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨b.down⟩)
                (diagChart_comp_pr₁Chart R I q hI)).trans (Category.id_comp _)
  exact key.trans (Category.comp_id _).symm

/-- **The diagonal is a section of the second projection**: `Δ ≫ pr₂ = 𝟙`. -/
theorem tateSelfProductDiagonal_comp_pr₂ (hq : q ∈ I) (hI : I.FG) :
    tateSelfProductDiagonal R I q hq hI ≫ tateSelfProductPr₂ R I q hq hI = 𝟙 _ := by
  refine (tateCurveFormalGlueData R I q hq hI).hom_ext (fun b => ?_)
  have hΔ : (tateCurveFormalGlueData R I q hq hI).ι b ≫ tateSelfProductDiagonal R I q hq hI =
      diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(b.down, b.down)⟩ := by
    rw [tateSelfProductDiagonal]
    exact (tateCurveFormalGlueData R I q hq hI).ι_glueMorphisms _ _ b
  have hpr : (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(b.down, b.down)⟩ ≫
        tateSelfProductPr₂ R I q hq hI =
      pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
        (tateCurveFormalGlueData R I q hq hI).ι ⟨b.down⟩ := by
    rw [tateSelfProductPr₂]
    exact (tateSelfProductFormalGlueDataInv R I q hq hI).ι_glueMorphisms _ _ ⟨(b.down, b.down)⟩
  have key : (tateCurveFormalGlueData R I q hq hI).ι b ≫
        tateSelfProductDiagonal R I q hq hI ≫ tateSelfProductPr₂ R I q hq hI =
      (tateCurveFormalGlueData R I q hq hI).ι b :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ tateSelfProductPr₂ R I q hq hI) hΔ).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (diagChart R I q hI ≫ ·) hpr).trans <|
            (Category.assoc _ _ _).symm.trans <|
              (Category.assoc _ _ _).symm.trans <|
                (congrArg (· ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨b.down⟩)
                  (diagChart_comp_pr₂Chart R I q hI)).trans (Category.id_comp _)
  exact key.trans (Category.comp_id _).symm

/-- **The diagonal of the Tate curve model is a split monomorphism** (the first projection is a
retraction). -/
theorem isSplitMono_tateSelfProductDiagonal (hq : q ∈ I) (hI : I.FG) :
    IsSplitMono (tateSelfProductDiagonal R I q hq hI) :=
  IsSplitMono.mk' ⟨tateSelfProductPr₁ R I q hq hI, tateSelfProductDiagonal_comp_pr₁ R I q hq hI⟩

/-- **`𝔈_q` is separated over `Spf R`** (EGA I §10.15): the diagonal is a monomorphism. -/
theorem mono_tateSelfProductDiagonal (hq : q ∈ I) (hI : I.FG) :
    Mono (tateSelfProductDiagonal R I q hq hI) :=
  haveI := isSplitMono_tateSelfProductDiagonal R I q hq hI
  inferInstance

/-! ### Surjectivity of the stalk maps of the glued diagonal -/

/-- Surjectivity of the underlying ring hom is preserved by composition in `CommRingCat`. -/
theorem surjective_hom_comp {X Y Z : CommRingCat} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Function.Surjective f.hom) (hg : Function.Surjective g.hom) :
    Function.Surjective (f ≫ g).hom := by
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact hg.comp hf

/-- An open immersion of locally ringed spaces has surjective (indeed bijective) stalk maps. -/
theorem surjective_stalkMap_of_isOpenImmersion {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion f] (x : X) :
    Function.Surjective (f.stalkMap x).hom :=
  ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).surjective

/-- Surjectivity of stalk maps is stable under composition: if `g` is surjective on the stalk over
`f x` and `f` is surjective on the stalk over `x`, then so is `f ≫ g`. -/
theorem surjective_stalkMap_comp {X Y Z : LocallyRingedSpace} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hg : Function.Surjective (g.stalkMap (f.base x)).hom)
    (hf : Function.Surjective (f.stalkMap x).hom) :
    Function.Surjective ((f ≫ g).stalkMap x).hom := by
  rw [LocallyRingedSpace.stalkMap_comp]
  exact surjective_hom_comp hg hf

/-- Surjectivity of stalk maps is local on the source along open immersions: if `f` is an open
immersion and `f ≫ g` has a surjective stalk map at `x`, then `g` has a surjective stalk map at
`f x`. The chart stalk map `f.stalkMap x` is an isomorphism, so it can be cancelled on the right. -/
theorem surjective_stalkMap_of_comp {X Y Z : LocallyRingedSpace} (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion f] (g : Y ⟶ Z) (x : X)
    (h : Function.Surjective ((f ≫ g).stalkMap x).hom) :
    Function.Surjective (g.stalkMap (f.base x)).hom := by
  have hEq : g.stalkMap (f.base x) = (f ≫ g).stalkMap x ≫ (asIso (f.stalkMap x)).inv :=
    (Iso.eq_comp_inv _).mpr (LocallyRingedSpace.stalkMap_comp f g x).symm
  rw [hEq]
  exact surjective_hom_comp h
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).surjective

/-- **The stalk maps of the glued Tate diagonal are surjective** (source-local half of the
closed-immersion criterion for the diagonal, EGA I §10.15). Being surjective on stalks is a
condition local on the source, so by joint surjectivity of the two open-immersion charts
`(tateCurveFormalGlueData …).ι b` it suffices to check it after precomposing with each `ι b`. On
the `b`-chart the diagonal factors as the affine diagonal `diagChart` followed by the open-immersion
chart `ι ⟨(b, b)⟩` of the self-product. The two chart stalk maps are isomorphisms, and `diagChart`
has surjective stalk maps: its underlying `presheafedSpaceMap` is the topology-free formal spectrum
of the surjective codiagonal `∇`, whose stalk maps are surjective by
`isClosedEmbedding_base_and_surjective_stalkMap_of_surjective`, with target ideal identified through
`map_codiagonal_eq` and `annulus_map_eq`. Composing (surjective after cancelling the chart
isomorphisms) gives the claim. -/
theorem tateSelfProductDiagonal_surjective_stalkMap (hq : q ∈ I) (hI : I.FG) :
    ∀ y, Function.Surjective ((tateSelfProductDiagonal R I q hq hI).stalkMap y).hom := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
  have hmapeq : Ideal.map (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q))
      (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q)) = annulusIdealOfDefinition R I q :=
    (CompletedTensorProduct.map_codiagonal_eq (R := R) (I := I)
      (A := annulusAlgebra R I q)).trans (annulus_map_eq R I q)
  have hsurjcod : Function.Surjective
      (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q)) := by
    intro a
    exact ⟨CompletedTensorProduct.inl R I _ _ a, by
      rw [CompletedTensorProduct.codiagonal, CompletedTensorProduct.lift_inl, AlgHom.id_apply]⟩
  have hdiag : ∀ y', Function.Surjective ((diagChart R I q hI).stalkMap y').hom :=
    (FormalSpectrum.isClosedEmbedding_base_and_surjective_stalkMap_of_surjective
      (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
      (annulusIdealOfDefinition R I q)
      (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q))
      (Ideal.map_le_iff_le_comap.mp (le_of_eq hmapeq))
      (by rw [CompletedTensorProduct.idealOfDefinition_eq_map]; exact hI.map _)
      hsurjcod hmapeq).2
  intro y
  obtain ⟨b, y', hy'⟩ := (tateCurveFormalGlueData R I q hq hI).ι_jointly_surjective y
  subst hy'
  have hΔ : (tateCurveFormalGlueData R I q hq hI).ι b ≫ tateSelfProductDiagonal R I q hq hI =
      diagChart R I q hI ≫ (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(b.down, b.down)⟩ := by
    rw [tateSelfProductDiagonal]
    exact (tateCurveFormalGlueData R I q hq hI).ι_glueMorphisms _ _ b
  have hRHSsurj := surjective_stalkMap_comp (diagChart R I q hI)
    ((tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(b.down, b.down)⟩) y'
    (surjective_stalkMap_of_isOpenImmersion
      ((tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(b.down, b.down)⟩) _) (hdiag y')
  have hcompsurj := hΔ.symm ▸ hRHSsurj
  exact surjective_stalkMap_of_comp ((tateCurveFormalGlueData R I q hq hI).ι b)
    (tateSelfProductDiagonal R I q hq hI) y' hcompsurj

end AlgebraicGeometry
