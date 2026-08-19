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

The four factorisations, one per (mixed chart, piece):

* `spfGraphCodiagX_comp_ι_ft` — chart `(false, true)`, `x`-piece, through the diagonal chart
  `(false, false)` (second-factor glue relation);
* `spfGraphCodiagY_comp_ι_ft` — chart `(false, true)`, `y`-piece, through `(true, true)`
  (first-factor glue relation);
* `spfGraphCodiagXComm_comp_ι_tf` — chart `(true, false)`, `x`-piece, through `(false, false)`;
* `spfGraphCodiagYComm_comp_ι_tf` — chart `(true, false)`, `y`-piece, through `(true, true)`.

and the resulting range inclusions `range_spfGraphCodiag*_subset` into `range Δ.base`.

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

/-! ### The `y`-piece of the mixed chart `(false, true)` -/

/-- `Spf` of the `y`-side graph codiagonal. -/
def spfGraphCodiagY (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    locallyRingedSpaceObj (annulusOverlapIdealY R I q) ⟶
      locallyRingedSpaceObj
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  locallyRingedSpaceMap _ _ (graphCodiagY R I q hI) (graphCodiagY_le_comap hI)

/-- `Spf` of the `y`-side graph lift. -/
def spfGraphLiftY (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    locallyRingedSpaceObj (annulusOverlapIdealY R I q) ⟶
      locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusAlgebra R I q)) :=
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  locallyRingedSpaceMap _ _ (graphLiftY R I q hI) (by
    intro x hx
    rw [Ideal.mem_comap]
    have h := graphLiftY_mem_pow R I q hI 1 (by rwa [pow_one])
    rwa [pow_one] at h)

/-- `Spf` of the partner-coordinate map `A →+* A[y⁻¹]^∧`. -/
def spfInvLocXY (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
    locallyRingedSpaceObj (annulusOverlapIdealY R I q) ⟶
      locallyRingedSpaceObj (annulusIdealOfDefinition R I q) :=
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  locallyRingedSpaceMap _ _ (invLocXY R I q hI).toRingHom
    (Ideal.map_le_iff_le_comap.mp (by
      have h0 : (invLocXY R I q hI).toRingHom =
          ((annulusOverlapInversion R I q hI :
              annulusOverlap R I q →+* annulusOverlapY R I q)).comp
            (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) := rfl
      have h1 : (I.map (algebraMap R (annulusAlgebra R I q))).map
          (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) =
          annulusOverlapIdeal R I q := by
        rw [Ideal.map_map,
          ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q) (annulusOverlap R I q),
          overlapIdeal_eq_map]
      rw [h0, ← annulus_map_eq, ← Ideal.map_map, h1,
        map_annulusOverlapInversion_annulusOverlapIdeal]))

set_option linter.unusedSectionVars false in
/-- **(A)** for the `y`-piece: the `y`-side graph codiagonal factors through the `y`-summand of the
first-factor overlap chart. -/
theorem spfGraphCodiagY_eq (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphCodiagY R I q hI =
      spfGraphLiftY R I q hI ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI := by
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hIK : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdealY R I q).comap ((graphLiftY R I q hI).comp
        (CompletedTensorProduct.map hI
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))
          (AlgHom.id R (annulusAlgebra R I q)))) := by
    rw [graphLiftY_comp_map R I q hI]
    exact graphCodiagY_le_comap hI
  rw [interchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    spfGraphLiftY, spfGraphCodiagY,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (graphLiftY_comp_map R I q hI).symm

set_option linter.unusedSectionVars false in
/-- **(B)** for the `y`-piece. -/
theorem spfGraphLiftY_comp_transition (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphLiftY R I q hI ≫ (firstSummandInv R I q hI).inv ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI =
      spfInvLocXY R I q hI ≫ diagChart R I q hI := by
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hIK₂ : idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q) ≤
      (annulusOverlapIdealY R I q).comap ((graphLiftY R I q hI).comp
        (CompletedTensorProduct.map hI
          (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom
          (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom)) := by
    intro x hx
    rw [Ideal.mem_comap, RingHom.comp_apply]
    have h := graphLiftY_mem_pow R I q hI 1
      (CompletedTensorProduct.map_mem_pow hI
        (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom
        (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom 1 (by rwa [pow_one]))
    rwa [pow_one] at h
  have hIKR : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdealY R I q).comap
        ((invLocXY R I q hI).toRingHom.comp
          (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q))) := by
    intro x hx
    rw [Ideal.mem_comap, RingHom.comp_apply]
    have hc : CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q) x ∈
        I.map (algebraMap R (annulusAlgebra R I q)) := by
      have := CompletedTensorProduct.lift_mem_pow _ (le_refl _) (AlgHom.id R _) (AlgHom.id R _)
        hI 1 (show x ∈ _ ^ 1 by rwa [pow_one])
      rwa [pow_one] at this
    have h0 : (invLocXY R I q hI).toRingHom =
        ((annulusOverlapInversion R I q hI :
            annulusOverlap R I q →+* annulusOverlapY R I q)).comp
          (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) := rfl
    have h1 : (I.map (algebraMap R (annulusAlgebra R I q))).map
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) =
        annulusOverlapIdeal R I q := by
      rw [Ideal.map_map,
        ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q) (annulusOverlap R I q),
        overlapIdeal_eq_map]
    have hid : (I.map (algebraMap R (annulusAlgebra R I q))).map
        (invLocXY R I q hI).toRingHom = annulusOverlapIdealY R I q := by
      rw [h0, ← Ideal.map_map, h1, map_annulusOverlapInversion_annulusOverlapIdeal]
    exact hid.le (Ideal.mem_map_of_mem _ hc)
  have hIK₁ : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdealY R I q).comap
        (((graphLiftY R I q hI).comp
          (CompletedTensorProduct.map hI
            (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom
            (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom)).comp
          (CompletedTensorProduct.map hI
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
            (AlgHom.id R (annulusAlgebra R I q)))) := by
    rw [graphLiftY_comp_map_transition R I q hI]
    exact hIKR
  rw [← Category.assoc, interchangeOpenImmersion_eq_mapSpf,
    CompletedTensorProduct.mapSpf_eq, firstSummandInv, twoPatchFibreProductInvTransition,
    CompletedTensorProduct.mapSpfIso_inv, CompletedTensorProduct.mapSpf_eq,
    spfGraphLiftY, spfInvLocXY, diagChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK₂),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK₁),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIKR)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (graphLiftY_comp_map_transition R I q hI)

set_option linter.unusedSectionVars false in
/-- **The `y`-piece of the mixed chart `(false, true)` lands in the diagonal.** -/
theorem spfGraphCodiagY_comp_ι_ft (hq : q ∈ I) (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphCodiagY R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, true)⟩ =
      spfInvLocXY R I q hI ≫ diagChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hinl : (coprod.inl : dXA R I q ⟶ dXA R I q ⨿ dYA R I q) ≫
      firstFactorOverlapChart R I q hI =
      interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI :=
    coprod.inl_desc _ _
  have hinr : (coprod.inr : dYA R I q ⟶ dXA R I q ⨿ dYA R I q) ≫
      firstFactorOverlapChart R I q hI =
      interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI :=
    coprod.inr_desc _ _
  have htr : (coprod.inr : dYA R I q ⟶ dXA R I q ⨿ dYA R I q) ≫
      (tateSelfProductFirstTransitionInv R I q hI).hom =
      (firstSummandInv R I q hI).inv ≫ coprod.inl :=
    coprod.inr_desc _ _
  calc spfGraphCodiagY R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, true)⟩
      = spfGraphLiftY R I q hI ≫ coprod.inr ≫ (firstFactorOverlapChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, true)⟩) := by
        rw [spfGraphCodiagY_eq R I q hI, ← hinr]; simp only [Category.assoc]
    _ = spfGraphLiftY R I q hI ≫ (coprod.inr ≫ (tateSelfProductFirstTransitionInv R I q hI).hom) ≫
          firstFactorOverlapChart R I q hI ≫
            (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
        rw [tateSelfProduct_first_glue_condition_inv_ft]; simp only [Category.assoc]
    _ = (spfGraphLiftY R I q hI ≫ (firstSummandInv R I q hI).inv ≫
          interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI) ≫
            (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
        rw [htr, ← hinl]; simp only [Category.assoc]
    _ = spfInvLocXY R I q hI ≫ diagChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
        rw [spfGraphLiftY_comp_transition R I q hI]; simp only [Category.assoc]

/-! ### The two pieces of the mixed chart `(true, false)`

For the other mixed chart the roles of the two tensor factors are exchanged; the cutting maps are
the graph codiagonals precomposed with the commutativity swap `commHom`.
-/

set_option linter.unusedSectionVars false in
theorem commHom_le_comap_self (hI : I.FG) :
    idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)).comap
        (commHom (R := R) (I := I) (A := annulusAlgebra R I q)
          (B := annulusAlgebra R I q) hI) := by
  haveI : IsAdicComplete (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
      (CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    (CompletedTensorProduct.isAdicRing R I _ _ hI).toIsAdicComplete
  intro x hx
  rw [Ideal.mem_comap, commHom]
  have h := CompletedTensorProduct.lift_mem_pow
    (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
    (le_of_eq (idealOfDefinition_eq_map).symm) (inr R I _ _) (inl R I _ _) hI 1
    (show x ∈ _ ^ 1 by rwa [pow_one])
  rwa [pow_one] at h

/-- `Spf` of the swapped `x`-side graph codiagonal. -/
def spfGraphCodiagXComm (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    locallyRingedSpaceObj (annulusOverlapIdeal R I q) ⟶
      locallyRingedSpaceObj
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  locallyRingedSpaceMap _ _
    ((graphCodiagX R I q hI).comp
      (commHom (R := R) (I := I) (A := annulusAlgebra R I q)
        (B := annulusAlgebra R I q) hI))
    (by
      intro x hx
      rw [Ideal.mem_comap, RingHom.comp_apply]
      exact graphCodiagX_le_comap hI (commHom_le_comap_self R I q hI hx))

/-- `Spf` of the swapped `y`-side graph codiagonal. -/
def spfGraphCodiagYComm (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    locallyRingedSpaceObj (annulusOverlapIdealY R I q) ⟶
      locallyRingedSpaceObj
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  locallyRingedSpaceMap _ _
    ((graphCodiagY R I q hI).comp
      (commHom (R := R) (I := I) (A := annulusAlgebra R I q)
        (B := annulusAlgebra R I q) hI))
    (by
      intro x hx
      rw [Ideal.mem_comap, RingHom.comp_apply]
      exact graphCodiagY_le_comap hI (commHom_le_comap_self R I q hI hx))

/-- `Spf` of the mixed graph lift `A{1/y} ⊗̂_R A →+* A[x⁻¹]^∧`. -/
def spfGraphLiftXY (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    locallyRingedSpaceObj (annulusOverlapIdeal R I q) ⟶
      locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusAlgebra R I q)) :=
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  locallyRingedSpaceMap _ _ (graphLiftXY R I q hI) (by
    intro x hx
    rw [Ideal.mem_comap]
    have h := graphLiftXY_mem_pow R I q hI 1 (by rwa [pow_one])
    rwa [pow_one] at h)

/-- `Spf` of the mixed graph lift `A ⊗̂_R A{1/y} →+* A[y⁻¹]^∧`. -/
def spfGraphLiftYX (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    locallyRingedSpaceObj (annulusOverlapIdealY R I q) ⟶
      locallyRingedSpaceObj (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  locallyRingedSpaceMap _ _ (graphLiftYX R I q hI) (by
    intro x hx
    rw [Ideal.mem_comap]
    have h := graphLiftYX_mem_pow R I q hI 1 (by rwa [pow_one])
    rwa [pow_one] at h)

set_option linter.unusedSectionVars false in
theorem locX_comp_codiagonal_le_comap (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdeal R I q).comap
        ((algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)).comp
          (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q))) := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  have h1 : (I.map (algebraMap R (annulusAlgebra R I q))).map
      (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) = annulusOverlapIdeal R I q := by
    rw [Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q) (annulusOverlap R I q),
      overlapIdeal_eq_map]
  intro x hx
  rw [Ideal.mem_comap, RingHom.comp_apply]
  have hc : CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q) x ∈
      I.map (algebraMap R (annulusAlgebra R I q)) := by
    have := CompletedTensorProduct.lift_mem_pow _ (le_refl _) (AlgHom.id R _) (AlgHom.id R _)
      hI 1 (show x ∈ _ ^ 1 by rwa [pow_one])
    rwa [pow_one] at this
  exact h1.le (Ideal.mem_map_of_mem _ hc)

set_option linter.unusedSectionVars false in
theorem invLocXY_comp_codiagonal_le_comap (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdealY R I q).comap
        ((invLocXY R I q hI).toRingHom.comp
          (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q))) := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  have h0 : (invLocXY R I q hI).toRingHom =
      ((annulusOverlapInversion R I q hI : annulusOverlap R I q →+* annulusOverlapY R I q)).comp
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) := rfl
  have h1 : (I.map (algebraMap R (annulusAlgebra R I q))).map
      (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) = annulusOverlapIdeal R I q := by
    rw [Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q) (annulusOverlap R I q),
      overlapIdeal_eq_map]
  have hid : (I.map (algebraMap R (annulusAlgebra R I q))).map
      (invLocXY R I q hI).toRingHom = annulusOverlapIdealY R I q := by
    rw [h0, ← Ideal.map_map, h1, map_annulusOverlapInversion_annulusOverlapIdeal]
  intro x hx
  rw [Ideal.mem_comap, RingHom.comp_apply]
  have hc : CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q) x ∈
      I.map (algebraMap R (annulusAlgebra R I q)) := by
    have := CompletedTensorProduct.lift_mem_pow _ (le_refl _) (AlgHom.id R _) (AlgHom.id R _)
      hI 1 (show x ∈ _ ^ 1 by rwa [pow_one])
    rwa [pow_one] at this
  exact hid.le (Ideal.mem_map_of_mem _ hc)

set_option linter.unusedSectionVars false in
/-- **(A)** for the swapped `x`-piece. -/
theorem spfGraphCodiagXComm_eq (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphCodiagXComm R I q hI =
      spfGraphLiftXY R I q hI ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hIK : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdeal R I q).comap ((graphLiftXY R I q hI).comp
        (CompletedTensorProduct.map hI
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))
          (AlgHom.id R (annulusAlgebra R I q)))) := by
    rw [graphLiftXY_comp_map R I q hI]
    intro x hx
    rw [Ideal.mem_comap, RingHom.comp_apply]
    exact graphCodiagX_le_comap hI (commHom_le_comap_self R I q hI hx)
  rw [interchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    spfGraphLiftXY, spfGraphCodiagXComm,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (graphLiftXY_comp_map R I q hI).symm

set_option linter.unusedSectionVars false in
/-- **(B)** for the swapped `x`-piece. -/
theorem spfGraphLiftXY_comp_transition (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphLiftXY R I q hI ≫ (firstSummandInv R I q hI).inv ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI =
      spfLocX R I q hI ≫ diagChart R I q hI := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hIK₂ : idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q) ≤
      (annulusOverlapIdeal R I q).comap ((graphLiftXY R I q hI).comp
        (CompletedTensorProduct.map hI
          (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom
          (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom)) := by
    intro x hx
    rw [Ideal.mem_comap, RingHom.comp_apply]
    have h := graphLiftXY_mem_pow R I q hI 1
      (CompletedTensorProduct.map_mem_pow hI
        (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom
        (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom 1 (by rwa [pow_one]))
    rwa [pow_one] at h
  have hIKR := locX_comp_codiagonal_le_comap R I q hI
  have hIK₁ : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdeal R I q).comap
        (((graphLiftXY R I q hI).comp
          (CompletedTensorProduct.map hI
            (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom
            (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom)).comp
          (CompletedTensorProduct.map hI
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
            (AlgHom.id R (annulusAlgebra R I q)))) := by
    rw [graphLiftXY_comp_map_transition R I q hI]
    exact hIKR
  rw [← Category.assoc, interchangeOpenImmersion_eq_mapSpf,
    CompletedTensorProduct.mapSpf_eq, firstSummandInv, twoPatchFibreProductInvTransition,
    CompletedTensorProduct.mapSpfIso_inv, CompletedTensorProduct.mapSpf_eq,
    spfGraphLiftXY, spfLocX, diagChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK₂),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK₁),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIKR)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (graphLiftXY_comp_map_transition R I q hI)

set_option linter.unusedSectionVars false in
/-- **The `x`-piece of the mixed chart `(true, false)` lands in the diagonal.** -/
theorem spfGraphCodiagXComm_comp_ι_tf (hq : q ∈ I) (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphCodiagXComm R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, false)⟩ =
      spfLocX R I q hI ≫ diagChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hinl : (coprod.inl : dXA R I q ⟶ dXA R I q ⨿ dYA R I q) ≫
      firstFactorOverlapChart R I q hI =
      interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI :=
    coprod.inl_desc _ _
  have hinr : (coprod.inr : dYA R I q ⟶ dXA R I q ⨿ dYA R I q) ≫
      firstFactorOverlapChart R I q hI =
      interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI :=
    coprod.inr_desc _ _
  have htr : (coprod.inr : dYA R I q ⟶ dXA R I q ⨿ dYA R I q) ≫
      (tateSelfProductFirstTransitionInv R I q hI).hom =
      (firstSummandInv R I q hI).inv ≫ coprod.inl :=
    coprod.inr_desc _ _
  calc spfGraphCodiagXComm R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, false)⟩
      = spfGraphLiftXY R I q hI ≫ coprod.inr ≫ (firstFactorOverlapChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, false)⟩) := by
        rw [spfGraphCodiagXComm_eq R I q hI, ← hinr]; simp only [Category.assoc]
    _ = spfGraphLiftXY R I q hI ≫
          (coprod.inr ≫ (tateSelfProductFirstTransitionInv R I q hI).hom) ≫
          firstFactorOverlapChart R I q hI ≫
            (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ := by
        rw [tateSelfProduct_first_glue_condition_inv_tf]; simp only [Category.assoc]
    _ = (spfGraphLiftXY R I q hI ≫ (firstSummandInv R I q hI).inv ≫
          interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI) ≫
            (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ := by
        rw [htr, ← hinl]; simp only [Category.assoc]
    _ = spfLocX R I q hI ≫ diagChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩ := by
        rw [spfGraphLiftXY_comp_transition R I q hI]; simp only [Category.assoc]

set_option linter.unusedSectionVars false in
/-- **(A)** for the swapped `y`-piece. -/
theorem spfGraphCodiagYComm_eq (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphCodiagYComm R I q hI =
      spfGraphLiftYX R I q hI ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI := by
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hIK : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdealY R I q).comap ((graphLiftYX R I q hI).comp
        (CompletedTensorProduct.map hI (AlgHom.id R (annulusAlgebra R I q))
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))))) := by
    rw [graphLiftYX_comp_map R I q hI]
    intro x hx
    rw [Ideal.mem_comap, RingHom.comp_apply]
    exact graphCodiagY_le_comap hI (commHom_le_comap_self R I q hI hx)
  rw [rightInterchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    spfGraphLiftYX, spfGraphCodiagYComm,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (graphLiftYX_comp_map R I q hI).symm

set_option linter.unusedSectionVars false in
/-- **(B)** for the swapped `y`-piece. -/
theorem spfGraphLiftYX_comp_transition (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphLiftYX R I q hI ≫ (rightSummandInv R I q hI).inv ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI =
      spfInvLocXY R I q hI ≫ diagChart R I q hI := by
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
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
      (annulusOverlapIdealY R I q).comap ((graphLiftYX R I q hI).comp
        (CompletedTensorProduct.map hI
          (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
          (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom)) := by
    intro x hx
    rw [Ideal.mem_comap, RingHom.comp_apply]
    have h := graphLiftYX_mem_pow R I q hI 1
      (CompletedTensorProduct.map_mem_pow hI
        (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
        (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom 1 (by rwa [pow_one]))
    rwa [pow_one] at h
  have hIKR := invLocXY_comp_codiagonal_le_comap R I q hI
  have hIK₁ : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdealY R I q).comap
        (((graphLiftYX R I q hI).comp
          (CompletedTensorProduct.map hI
            (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
            (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom)).comp
          (CompletedTensorProduct.map hI (AlgHom.id R (annulusAlgebra R I q))
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
                (overlapX R I q))))) := by
    rw [graphLiftYX_comp_map_transition R I q hI]
    exact hIKR
  rw [← Category.assoc, rightInterchangeOpenImmersion_eq_mapSpf,
    CompletedTensorProduct.mapSpf_eq, rightSummandInv, CompletedTensorProduct.mapSpfIso_inv,
    CompletedTensorProduct.mapSpf_eq, spfGraphLiftYX, spfInvLocXY, diagChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK₂),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK₁),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIKR)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (graphLiftYX_comp_map_transition R I q hI)

set_option linter.unusedSectionVars false in
/-- **The `y`-piece of the mixed chart `(true, false)` lands in the diagonal.** -/
theorem spfGraphCodiagYComm_comp_ι_tf (hq : q ∈ I) (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphCodiagYComm R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, false)⟩ =
      spfInvLocXY R I q hI ≫ diagChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
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
  calc spfGraphCodiagYComm R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, false)⟩
      = spfGraphLiftYX R I q hI ≫ coprod.inr ≫ (secondFactorOverlapChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, false)⟩) := by
        rw [spfGraphCodiagYComm_eq R I q hI, ← hinr]; simp only [Category.assoc]
    _ = spfGraphLiftYX R I q hI ≫
          (coprod.inr ≫ (tateSelfProductRightTransitionInv R I q hI).hom) ≫
          secondFactorOverlapChart R I q hI ≫
            (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
        rw [tateSelfProduct_second_glue_condition_inv_tf]; simp only [Category.assoc]
    _ = (spfGraphLiftYX R I q hI ≫ (rightSummandInv R I q hI).inv ≫
          rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI) ≫
            (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
        rw [htr, ← hinl]; simp only [Category.assoc]
    _ = spfInvLocXY R I q hI ≫ diagChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩ := by
        rw [spfGraphLiftYX_comp_transition R I q hI]; simp only [Category.assoc]

/-! ### The four pieces lie in the range of the glued diagonal -/

theorem range_comp_comp_base_subset {W X Y Z : LocallyRingedSpace.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Set.range (f ≫ g ≫ h).base ⊆ Set.range h.base := by
  rintro y ⟨w, rfl⟩
  exact ⟨g.base (f.base w), rfl⟩

set_option linter.unusedSectionVars false in
/-- The factorisation of the glued diagonal on the `c`-chart: `ι c ≫ Δ = diagChart ≫ ι (c, c)`.
(The same statement as the `424` scaffold's `curve_ι_comp_diagonal`, kept here so that this file
is self-contained; drop one of the two copies when the scaffold lands.) -/
theorem curve_ι_comp_selfProductDiagonal (hq : q ∈ I) (hI : I.FG) (c : Bool) :
    (tateCurveFormalGlueData R I q hq hI).ι ⟨c⟩ ≫ tateSelfProductDiagonal R I q hq hI =
      diagChart R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(c, c)⟩ := by
  rw [tateSelfProductDiagonal]
  exact (tateCurveFormalGlueData R I q hq hI).ι_glueMorphisms _ _ ⟨c⟩

set_option linter.unusedSectionVars false in
/-- **The `x`-piece of the chart `(false, true)` lies in `range Δ.base`.** -/
theorem range_spfGraphCodiagX_ft_subset (hq : q ∈ I) (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    Set.range (spfGraphCodiagX R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, true)⟩).base ⊆
      Set.range (tateSelfProductDiagonal R I q hq hI).base := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [spfGraphCodiagX_comp_ι_ft R I q hq hI,
    ← curve_ι_comp_selfProductDiagonal R I q hq hI false]
  exact range_comp_comp_base_subset _ _ _

set_option linter.unusedSectionVars false in
/-- **The `y`-piece of the chart `(false, true)` lies in `range Δ.base`.** -/
theorem range_spfGraphCodiagY_ft_subset (hq : q ∈ I) (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    Set.range (spfGraphCodiagY R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, true)⟩).base ⊆
      Set.range (tateSelfProductDiagonal R I q hq hI).base := by
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [spfGraphCodiagY_comp_ι_ft R I q hq hI,
    ← curve_ι_comp_selfProductDiagonal R I q hq hI true]
  exact range_comp_comp_base_subset _ _ _

set_option linter.unusedSectionVars false in
/-- **The `x`-piece of the chart `(true, false)` lies in `range Δ.base`.** -/
theorem range_spfGraphCodiagXComm_tf_subset (hq : q ∈ I) (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    Set.range (spfGraphCodiagXComm R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, false)⟩).base ⊆
      Set.range (tateSelfProductDiagonal R I q hq hI).base := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [spfGraphCodiagXComm_comp_ι_tf R I q hq hI,
    ← curve_ι_comp_selfProductDiagonal R I q hq hI false]
  exact range_comp_comp_base_subset _ _ _

set_option linter.unusedSectionVars false in
/-- **The `y`-piece of the chart `(true, false)` lies in `range Δ.base`.** -/
theorem range_spfGraphCodiagYComm_tf_subset (hq : q ∈ I) (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    Set.range (spfGraphCodiagYComm R I q hI ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, false)⟩).base ⊆
      Set.range (tateSelfProductDiagonal R I q hq hI).base := by
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [spfGraphCodiagYComm_comp_ι_tf R I q hq hI,
    ← curve_ι_comp_selfProductDiagonal R I q hq hI true]
  exact range_comp_comp_base_subset _ _ _

end AlgebraicGeometry
