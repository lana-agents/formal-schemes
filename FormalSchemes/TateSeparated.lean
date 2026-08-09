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

## Scope — what is delivered vs. what remains

Delivered: the affine diagonal chart `diagChart`, its two affine section identities, the topology-
free codiagonal naturality lemma, and the product-side diagonal-chart glue relation — the reusable
bricks the glued diagonal is assembled from.

Not yet delivered: the glued morphism `tateSelfProductDiagonal` itself, its glued section
identities, and the `IsSplitMono`/`Mono` separatedness conclusion. These are blocked on the
**off-diagonal
`glueMorphisms` compatibility** at the source-overlap pair `(⟨false⟩, ⟨true⟩)`, whose `x`-summand
obligation is
```
annulusOverlapChart ≫ diagChart ≫ ι_prod(false,false)
  = (annulusChartTransitionSpf).hom ≫ annulusOverlapChartY ≫ diagChart ≫ ι_prod(true,true).
```
Closing it needs two further affine bricks: (i) the **diagonal/localization factorisation**
`annulusOverlapChart ≫ diagChart = diagChart_{A{1/x}} ≫ bothInterchangeOpenImmersion I x x`
(the geometric shadow of `codiagonal_naturality` for the localization `A →ₐ A{1/x}`, requiring the
ideal-convention bridges `annulusOverlapBridgeX`/`annulusChartDomainSpfX` reconciling
`awayCompletionIdeal (annulusIdealOfDefinition) x` with `awayCompletion (I·A) x`), and (ii) the
**transition compatibility** `diagChart_{A{1/x}} ≫ (bothSummandDiag).hom
= (annulusChartTransitionSpf).hom ≫ diagChart_{A{1/y}}` (again `codiagonal_naturality` for the chart
transition), after which the product glue relation `tateSelfProduct_both_glue_condition` closes the
square. This bridge reconciliation is the same infrastructure that makes each Tate self-product
projection a full development (`TateSelfProductProjectionLeft`/`Right`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct

universe u

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

/-- **The affine diagonal chart** `Spf A ⟶ Spf(A ⊗̂_R A)`, topology-free, as `Spf` of the codiagonal
(multiplication) `∇ : A ⊗̂_R A →+* A`. It is built at the `locallyRingedSpaceMap` level so that no
`TopologicalSpace R` instance is needed (the annulus layer carries no topology on the base). -/
def diagChart (hI : I.FG) :
    locallyRingedSpaceObj (annulusIdealOfDefinition R I q) ⟶
      locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
          (annulusAlgebra R I q)) :=
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    (annulus_map_eq R I q).symm ▸ annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
  FormalSpectrum.locallyRingedSpaceMap
    (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
    (annulusIdealOfDefinition R I q)
    (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q))
    (annulus_map_eq R I q ▸ Ideal.map_le_iff_le_comap.mp
      (CompletedTensorProduct.map_codiagonal_eq (R := R) (I := I)
        (A := annulusAlgebra R I q)).le)

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
    (annulus_map_eq R I q).symm ▸ annulus_isAdicRing R I q hI
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
    (annulus_map_eq R I q).symm ▸ annulus_isAdicRing R I q hI
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

end AlgebraicGeometry
