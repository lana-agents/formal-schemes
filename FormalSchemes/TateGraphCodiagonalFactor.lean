import FormalSchemes.TateGraphCodiagonalBridge
import FormalSchemes.TateSelfProductMixedGlue

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000
set_option maxRecDepth 8000

/-!
# The graph-codiagonal factorisations of the mixed Tate self-product charts

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`, write
`A = annulusAlgebra R I q`, `Ω = A[x⁻¹]^∧` and `Ω_y = A[y⁻¹]^∧`.

Read in a **mixed** chart `(b, ¬b)` of the four-chart self fibre product
`𝔈_q ×_{Spf R} 𝔈_q`, the diagonal of the Tate curve is the *graph of the 𝔾m-inversion gluing*: a
disjoint union of two pieces, parametrised by `Spf Ω` and `Spf Ω_y` and cut out by the graph
codiagonals `∇ˣ`, `∇ʸ` of `GraphCodiagonalClosedEmbedding`.

This file proves the `⊇` half of that description: each graph piece, followed by the glue inclusion
of the mixed chart, factors through the diagonal chart of a *diagonal* chart `(c, c)`. Combined with
`ι_curve c ≫ Δ = diagChart ≫ ι ⟨(c, c)⟩` this exhibits every point of the two pieces in
`range Δ.base`.

## Main results

* `spfGraphCodiagX_comp_ι_ft`: the `x`-piece of the chart `(false, true)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section
open Ideal AlgebraicGeometry CategoryTheory CategoryTheory.Limits FormalSpectrum
  CompletedTensorProduct CompletedTensorAwayInterchange
universe u
namespace AlgebraicGeometry
variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]
variable [TopologicalSpace R] [IsAdicRing I]

/-- `Spf` of the `x`-side graph codiagonal. -/
def spfGraphCodiagX (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    locallyRingedSpaceObj (annulusOverlapIdeal R I q) ⟶
      locallyRingedSpaceObj
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  locallyRingedSpaceMap _ _ (graphCodiagX R I q hI) (graphCodiagX_le_comap hI)

/-- `Spf` of the `x`-side graph lift. -/
def spfGraphLiftX (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    locallyRingedSpaceObj (annulusOverlapIdeal R I q) ⟶
      locallyRingedSpaceObj (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  locallyRingedSpaceMap _ _ (graphLiftX R I q hI) (by
    intro x hx
    rw [Ideal.mem_comap]
    have h := graphLiftX_mem_pow R I q hI 1 (by rwa [pow_one])
    rwa [pow_one] at h)

/-- **(A)** The `x`-side graph codiagonal factors through the `y`-summand of the second-factor
overlap chart. -/
theorem spfGraphCodiagX_eq (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphCodiagX R I q hI =
      spfGraphLiftX R I q hI ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hIK : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdeal R I q).comap ((graphLiftX R I q hI).comp
        (CompletedTensorProduct.map hI (AlgHom.id R (annulusAlgebra R I q))
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))))) := by
    rw [graphLiftX_comp_map R I q hI]
    exact graphCodiagX_le_comap hI
  rw [rightInterchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    spfGraphLiftX, spfGraphCodiagX,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (graphLiftX_comp_map R I q hI).symm

/-- `Spf` of the structural map `A → A[x⁻¹]^∧`. -/
def spfLocX (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
    locallyRingedSpaceObj (annulusOverlapIdeal R I q) ⟶
      locallyRingedSpaceObj (annulusIdealOfDefinition R I q) :=
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  locallyRingedSpaceMap _ _
    (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q))
    (Ideal.map_le_iff_le_comap.mp (by
      rw [← annulus_map_eq, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q) (annulusOverlap R I q),
        overlapIdeal_eq_map]))

/-- **(B)** The graph lift, transported back through the second-factor inversion transition and the
`x`-summand chart, is the diagonal chart along the structural map. -/
theorem spfGraphLiftX_comp_transition (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphLiftX R I q hI ≫ (rightSummandInv R I q hI).inv ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI =
      spfLocX R I q hI ≫ diagChart R I q hI := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hIK₂ : idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) ≤
      (annulusOverlapIdeal R I q).comap ((graphLiftX R I q hI).comp
        (CompletedTensorProduct.map hI
          (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
          (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom)) := by
    intro x hx
    rw [Ideal.mem_comap, RingHom.comp_apply]
    have h := graphLiftX_mem_pow R I q hI 1
      (CompletedTensorProduct.map_mem_pow hI
        (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
        (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom 1 (by rwa [pow_one]))
    rwa [pow_one] at h
  have hRing : (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)).map
      ((algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)).comp
        (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q))) =
      annulusOverlapIdeal R I q := by
    rw [← Ideal.map_map, CompletedTensorProduct.map_codiagonal_eq, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q) (annulusOverlap R I q),
      overlapIdeal_eq_map]
  have hIKR : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdeal R I q).comap
        ((algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)).comp
          (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q))) :=
    Ideal.map_le_iff_le_comap.mp hRing.le
  have hIK₁ : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdeal R I q).comap
        (((graphLiftX R I q hI).comp
          (CompletedTensorProduct.map hI
            (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
            (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom)).comp
          (CompletedTensorProduct.map hI (AlgHom.id R (annulusAlgebra R I q))
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
                (overlapX R I q))))) := by
    rw [graphLiftX_comp_map_transition R I q hI]
    exact hIKR
  rw [← Category.assoc, rightInterchangeOpenImmersion_eq_mapSpf,
    CompletedTensorProduct.mapSpf_eq, rightSummandInv, CompletedTensorProduct.mapSpfIso_inv,
    CompletedTensorProduct.mapSpf_eq, spfGraphLiftX, spfLocX, diagChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK₂),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK₁),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIKR)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (graphLiftX_comp_map_transition R I q hI)

/-- **The `x`-piece of the mixed chart `(false, true)` lands in the diagonal.** -/
theorem spfGraphCodiagX_comp_ι_ft (hq : q ∈ I) (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphCodiagX R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, true)⟩ =
      spfLocX R I q hI ≫ diagChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hinl : (coprod.inl : dAX R I q ⟶ dAX R I q ⨿ dAY R I q) ≫
      secondFactorOverlapChart R I q hI =
      rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI :=
    coprod.inl_desc _ _
  have hinr : (coprod.inr : dAY R I q ⟶ dAX R I q ⨿ dAY R I q) ≫
      secondFactorOverlapChart R I q hI =
      rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI :=
    coprod.inr_desc _ _
  have htr : (coprod.inr : dAY R I q ⟶ dAX R I q ⨿ dAY R I q) ≫
      (tateSelfProductRightTransitionInv R I q hI).hom =
      (rightSummandInv R I q hI).inv ≫ coprod.inl :=
    coprod.inr_desc _ _
  calc spfGraphCodiagX R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, true)⟩
      = spfGraphLiftX R I q hI ≫ coprod.inr ≫ (secondFactorOverlapChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, true)⟩) := by
        rw [spfGraphCodiagX_eq R I q hI, ← hinr]; simp only [Category.assoc]
    _ = spfGraphLiftX R I q hI ≫ (coprod.inr ≫ (tateSelfProductRightTransitionInv R I q hI).hom) ≫
          secondFactorOverlapChart R I q hI ≫
            (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ := by
        rw [tateSelfProduct_second_glue_condition_inv_ft]; simp only [Category.assoc]
    _ = (spfGraphLiftX R I q hI ≫ (rightSummandInv R I q hI).inv ≫
          rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI) ≫
            (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ := by
        rw [htr, ← hinl]; simp only [Category.assoc]
    _ = spfLocX R I q hI ≫ diagChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ := by
        rw [spfGraphLiftX_comp_transition R I q hI]; simp only [Category.assoc]

end AlgebraicGeometry
