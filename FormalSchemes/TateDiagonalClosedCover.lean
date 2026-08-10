import FormalSchemes.TateSeparated
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Sets.OpenCover

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The four-chart open cover of the Tate self-product and its diagonal charts

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`, and let
`A = R{x, y}/(x·y − q)` be the coordinate ring of the formal Tate annulus. The self fibre product
`𝔈_q ×_{Spf R} 𝔈_q = tateSelfProduct` is glued from the four affine charts `Spf(A ⊗̂_R A)` indexed
by `ULift (Bool × Bool)`.

This file packages the **four-chart open cover** of `tateSelfProduct` by the ranges of the glue
inclusions `ι p`, and shows that on the two **diagonal charts** `(b, b)` the restriction of the
underlying map of the glued diagonal

```
Δ : 𝔈_q ⟶ 𝔈_q ×_{Spf R} 𝔈_q
```

to the preimage of the chart is a **closed topological embedding**. This is the local-at-target
input for upgrading `Δ` to a closed immersion (EGA I §10.15): being a closed immersion is local on
the target along an open cover, and on each diagonal chart `Δ` factors through the per-chart affine
diagonal `diagChart`, whose base map is a closed embedding
(`CompletedTensorProduct.isClosedEmbedding_diagonal_base`).

## Main definitions and results

* `AlgebraicGeometry.tateSelfProductChartCover`: the family of opens
  `range (ι p).base` of `tateSelfProduct`, indexed by `ULift (Bool × Bool)`.
* `AlgebraicGeometry.tateSelfProductChartCover_isOpenCover`: the family is an open cover, from the
  joint surjectivity of the glue inclusions.
* `AlgebraicGeometry.isClosedEmbedding_diagChart_base`: the base map of the per-chart affine
  diagonal `diagChart` is a closed topological embedding, from surjectivity of the codiagonal.
* `AlgebraicGeometry.restrictPreimage_diagonal_diagChart`: on each diagonal chart `(b, b)` the
  restriction of `Δ.base` to the preimage of the chart is a closed embedding.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]

/-- **The four-chart open cover of the Tate self-product.** Each chart `p : ULift (Bool × Bool)`
contributes the open set `range (ι p).base`, the image of the affine chart `Spf(A ⊗̂_R A)` under its
glue inclusion; it is open because `ι p` is an open immersion. -/
def tateSelfProductChartCover (hq : q ∈ I) (hI : I.FG) :
    ULift (Bool × Bool) →
      TopologicalSpace.Opens ((tateSelfProduct R I q hq hI).toLocallyRingedSpace) :=
  fun p => ⟨Set.range ((tateSelfProductFormalGlueData R I q hq hI).ι p).base,
    ((tateSelfProductFormalGlueData R I q hq hI).ι_isOpenImmersion p).base_open.isOpen_range⟩

omit [IsNoetherianRing R] in
/-- **The four charts form an open cover** of the Tate self-product: their union is the whole space,
by the joint surjectivity of the glue inclusions `ι p`. -/
theorem tateSelfProductChartCover_isOpenCover (hq : q ∈ I) (hI : I.FG) :
    TopologicalSpace.IsOpenCover (tateSelfProductChartCover R I q hq hI) := by
  refine TopologicalSpace.IsOpenCover.mk ?_
  refine TopologicalSpace.Opens.ext ?_
  rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.eq_univ_iff_forall]
  intro x
  obtain ⟨i, y, hy⟩ := (tateSelfProductFormalGlueData R I q hq hI).ι_jointly_surjective x
  exact Set.mem_iUnion.mpr ⟨i, y, hy⟩

/-- **The base map of the per-chart affine diagonal is a closed topological embedding.** The
morphism `diagChart : Spf A ⟶ Spf(A ⊗̂_R A)` is the topology-free `Spf` of the surjective codiagonal
`∇ : A ⊗̂_R A →+* A`, and `Spf` (i.e. `Spec` of the level-`0` reduction) of a surjection is a closed
embedding (`FormalSpectrum.isClosedEmbedding_map_of_surjective`). -/
theorem isClosedEmbedding_diagChart_base (hI : I.FG) :
    IsClosedEmbedding ⇑(diagChart R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
  have hsurjcod : Function.Surjective
      (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q)) := by
    intro a
    exact ⟨CompletedTensorProduct.inl R I _ _ a, by
      rw [CompletedTensorProduct.codiagonal, CompletedTensorProduct.lift_inl, AlgHom.id_apply]⟩
  exact FormalSpectrum.isClosedEmbedding_map_of_surjective
    (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
    (annulusIdealOfDefinition R I q)
    (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q))
    (by
      refine Ideal.map_le_iff_le_comap.mp ?_
      rw [CompletedTensorProduct.map_codiagonal_eq (R := R) (I := I)
        (A := annulusAlgebra R I q)]
      exact (annulus_map_eq R I q).le)
    hsurjcod

/-- **The diagonal chart is a closed embedding on the preimage.** On each diagonal chart `(b, b)`
of the Tate self-product, the restriction of the underlying map of the glued diagonal `Δ` to the
preimage of the chart is a closed topological embedding. The diagonal is a section of the first
projection `pr₁` (`tateSelfProductDiagonal_comp_pr₁`), so its base map is a global topological
embedding; and via the factorisation `ι b ≫ Δ = diagChart ≫ ι (b,b)` the chart-restricted range is
the closed diagonal locus `range (diagChart.base)`. -/
theorem restrictPreimage_diagonal_diagChart (hq : q ∈ I) (hI : I.FG) (b : ULift Bool) :
    IsClosedEmbedding
      (Set.restrictPreimage
        ((tateSelfProductChartCover R I q hq hI ⟨(b.down, b.down)⟩ :
          Set ((tateSelfProduct R I q hq hI).toLocallyRingedSpace)))
        (tateSelfProductDiagonal R I q hq hI).base) := by
  -- The factorisation of the diagonal on the `b`-chart.
  have hΔ : (tateCurveFormalGlueData R I q hq hI).ι ⟨b.down⟩ ≫ tateSelfProductDiagonal R I q hq hI =
      diagChart R I q hI ≫ (tateSelfProductFormalGlueData R I q hq hI).ι ⟨(b.down, b.down)⟩ := by
    rw [tateSelfProductDiagonal]
    exact (tateCurveFormalGlueData R I q hq hI).ι_glueMorphisms _ _ ⟨b.down⟩
  -- The compatibility of the first projection with the diagonal chart.
  have hpr : (tateSelfProductFormalGlueData R I q hq hI).ι ⟨(b.down, b.down)⟩ ≫
        tateSelfProductPr₁ R I q hq hI =
      pr₁Chart R I q (annulusAlgebra R I q) ≫ (tateCurveFormalGlueData R I q hq hI).ι ⟨b.down⟩ := by
    rw [tateSelfProductPr₁]
    exact (tateSelfProductFormalGlueData R I q hq hI).ι_glueMorphisms _ _ ⟨(b.down, b.down)⟩
  -- Pointwise base identities extracted from the categorical equalities.
  have hΔpt : ∀ x, (tateSelfProductDiagonal R I q hq hI).base
        (((tateCurveFormalGlueData R I q hq hI).ι ⟨b.down⟩).base x) =
      ((tateSelfProductFormalGlueData R I q hq hI).ι ⟨(b.down, b.down)⟩).base
        ((diagChart R I q hI).base x) := by
    intro x
    exact congrArg (fun m => m.base x) hΔ
  have hprpt : ∀ w, (tateSelfProductPr₁ R I q hq hI).base
        (((tateSelfProductFormalGlueData R I q hq hI).ι ⟨(b.down, b.down)⟩).base w) =
      ((tateCurveFormalGlueData R I q hq hI).ι ⟨b.down⟩).base
        ((pr₁Chart R I q (annulusAlgebra R I q)).base w) := by
    intro w
    exact congrArg (fun m => m.base w) hpr
  have hsecpt : ∀ c, (tateSelfProductPr₁ R I q hq hI).base
        ((tateSelfProductDiagonal R I q hq hI).base c) = c := by
    intro c
    exact congrArg (fun m => m.base c) (tateSelfProductDiagonal_comp_pr₁ R I q hq hI)
  -- Continuity of the base maps.
  have hcΔ : Continuous ⇑(tateSelfProductDiagonal R I q hq hI).base :=
    (tateSelfProductDiagonal R I q hq hI).base.hom.continuous
  have hcpr : Continuous ⇑(tateSelfProductPr₁ R I q hq hI).base :=
    (tateSelfProductPr₁ R I q hq hI).base.hom.continuous
  -- The diagonal's base map is a global topological embedding (it is a section of `pr₁`).
  have hg_emb : IsEmbedding ⇑(tateSelfProductDiagonal R I q hq hI).base :=
    Topology.IsEmbedding.of_leftInverse hsecpt hcpr hcΔ
  -- The chart inclusions are open embeddings and `diagChart.base` is a closed embedding.
  have he_emb : IsOpenEmbedding
      ⇑((tateSelfProductFormalGlueData R I q hq hI).ι ⟨(b.down, b.down)⟩).base :=
    ((tateSelfProductFormalGlueData R I q hq hI).ι_isOpenImmersion ⟨(b.down, b.down)⟩).base_open
  have hd_ce : IsClosedEmbedding ⇑(diagChart R I q hI).base :=
    isClosedEmbedding_diagChart_base R I q hI
  -- The homeomorphism of `Spf(A ⊗̂_R A)` onto the chart (its range equals the chart cover set).
  let ψ := he_emb.toIsEmbedding.toHomeomorph
  refine ⟨Set.restrictPreimage_isEmbedding _ hg_emb, ?_⟩
  rw [Set.range_restrictPreimage]
  refine (ψ.isClosed_preimage).mp ?_
  have hset : ⇑ψ ⁻¹' (Subtype.val ⁻¹'
        Set.range ⇑(tateSelfProductDiagonal R I q hq hI).base) =
      Set.range ⇑(diagChart R I q hI).base := by
    ext z
    have hval : Subtype.val (ψ z) =
        ((tateSelfProductFormalGlueData R I q hq hI).ι ⟨(b.down, b.down)⟩).base z := rfl
    simp only [Set.mem_preimage, Set.mem_range]
    rw [hval]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(pr₁Chart R I q (annulusAlgebra R I q)).base z, ?_⟩
      have hy2 : y = ((tateCurveFormalGlueData R I q hq hI).ι ⟨b.down⟩).base
          ((pr₁Chart R I q (annulusAlgebra R I q)).base z) := by
        have hs := hsecpt y
        rw [hy, hprpt z] at hs
        exact hs.symm
      apply he_emb.injective
      rw [← hΔpt ((pr₁Chart R I q (annulusAlgebra R I q)).base z), ← hy2]
      exact hy
    · rintro ⟨x, hx⟩
      exact ⟨((tateCurveFormalGlueData R I q hq hI).ι ⟨b.down⟩).base x, by
        rw [hΔpt x, hx]⟩
  exact hset ▸ hd_ce.isClosed_range

end AlgebraicGeometry
