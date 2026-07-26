import FormalSchemes.TwoPatchFibreProductObject
import FormalSchemes.CompletedTensorMapSpfPr
import FormalSchemes.CompletedTensorAwayInterchangePr

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The second projection of the two-patch fibre product onto the affine base `Spf B`

Building on the glued object `AlgebraicGeometry.twoPatchFibreProduct`
(`FormalSchemes.TwoPatchFibreProductObject`) — the fibre product `X ×_{Spf R} Spf B` of the
two-patch Tate model `X = tateTwoPatch` with an affine base `Spf B` — this file assembles the
**second projection** onto the affine base:

`twoPatchFibreProductPr₂ : X ×_{Spf R} Spf B ⟶ Spf B`.

It is glued from the per-patch second projections `CompletedTensorProduct.fibrePr₂ = Spf(inr)` of
the two affine charts `Spf(A ⊗̂_R B)` via `FormalScheme.GlueData.glueMorphisms`
(`FormalSchemes.GlueMorphisms`). The overlap compatibility that `glueMorphisms` consumes is checked
by casing on whether the two `Bool`-indices coincide: on the diagonal the transition is the
identity; off the diagonal it reduces to the two naturality data of the second projection across a
double overlap, namely

* the away-localization interchange square
  `CompletedTensorAwayInterchange.interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr`
  (`FormalSchemes.CompletedTensorAwayInterchangePr`), realising the interchange chart immersion as a
  morphism over `Spf B`, and
* the `mapSpf`-naturality square `CompletedTensorProduct.mapSpf_comp_fibrePr₂`
  (`FormalSchemes.CompletedTensorMapSpfPr`), witnessing that the base-changed overlap transition
  commutes with the second projections.

The residual comparison map is `Spf` of the identity ring homomorphism `RingHom.id B` (coming from
`AlgEquiv.refl R B`), collapsed to `𝟙` by `FormalSpectrum.locallyRingedSpaceMap_id`.

## Main definitions

* `AlgebraicGeometry.twoPatchFibreProductPr₂`: the glued second projection
  `X ×_{Spf R} Spf B ⟶ Spf B`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable (B : Type u) [CommRing B] [Algebra R B]

/-- The completed localization chart `A{1/f} = awayCompletion (I·A) f` is a complete adic ring over
`(R, I)` for `I` finitely generated: its ideal of definition `I·(A{1/f})` is the extension along
the completion map of `I·(A_f)`, so it is `AdicCompletion.isAdicRing_map`. This packages the
factor-side adic instance the naturality square `mapSpf_comp_fibrePr₂` needs on each overlap
chart. -/
theorem awayCompletion_isAdicRing {A : Type u} [CommRing A] [Algebra R A] (f : A) (hI : I.FG) :
    IsAdicRing
      (I.map (algebraMap R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f))) := by
  rw [show
      I.map (algebraMap R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f)) =
        FormalSpectrum.awayCompletionIdeal (I.map (algebraMap R A)) f by
    rw [FormalSpectrum.awayCompletionIdeal, AdicCompletion.idealOfDefinition,
      IsScalarTower.algebraMap_eq R (Localization.Away f)
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f), ← Ideal.map_map]
    congr 1
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R A (Localization.Away f)]]
  exact AdicCompletion.isAdicRing_map _ ((hI.map _).map _)

/-- The morphism of formal spectra induced by an `R`-algebra endomorphism `g : B →ₐ[R] B` whose
underlying ring homomorphism is the identity is itself the identity: the residual comparison map
`Spf(RingHom.id B)` on the affine base collapses to `𝟙` via
`FormalSpectrum.locallyRingedSpaceMap_id`.
This kills the leftover factor `Spf(AlgEquiv.refl R B)` produced by `mapSpf_comp_fibrePr₂`. -/
theorem spfMap_algHom_toRingHom_id [TopologicalSpace R] [IsAdicRing I]
    [TopologicalSpace B] [IsAdicRing (I.map (algebraMap R B))]
    {g : B →ₐ[R] B} (hg : g.toRingHom = RingHom.id B) :
    (CompletedTensorProduct.algHom_isAdicHom_map (I := I) g).spfMap =
      𝟙 (FormalSpectrum.locallyRingedSpaceObj (I.map (algebraMap R B))) := by
  have h : (CompletedTensorProduct.algHom_isAdicHom_map (I := I) g).spfMap =
      FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R B)) (I.map (algebraMap R B))
        (RingHom.id B) (Ideal.comap_id _).ge := by
    rw [IsAdicHom.spfMap]
    exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ hg
  rw [h, FormalSpectrum.locallyRingedSpaceMap_id]

/-- **The second projection `X ×_{Spf R} Spf B ⟶ Spf B`** of the two-patch fibre product onto the
affine base, glued from the per-patch second projections `fibrePr₂ = Spf(inr)` of the two affine
charts `Spf(A ⊗̂_R B)`. -/
def twoPatchFibreProductPr₂ [TopologicalSpace R] [IsAdicRing I]
    [TopologicalSpace B] [IsAdicRing (I.map (algebraMap R B))] (hI : I.FG) :
    (twoPatchFibreProduct R I q B hI).toLocallyRingedSpace ⟶
      FormalSpectrum.locallyRingedSpaceObj (I.map (algebraMap R B)) :=
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) B) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) B hI
  haveI := awayCompletion_isAdicRing R I (overlapX R I q) hI
  haveI := awayCompletion_isAdicRing R I (overlapY R I q) hI
  haveI := CompletedTensorProduct.isAdicRing R I
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) B hI
  haveI := CompletedTensorProduct.isAdicRing R I
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) B hI
  (twoPatchFibreProductFormalGlueData R I q B hI).glueMorphisms
    (fun _ =>
      CompletedTensorProduct.fibrePr₂ (R := R) (I := I) (A := annulusAlgebra R I q) (B := B))
    (by
      intro i j
      by_cases hij : i = j
      · subst hij
        simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
      · have hij' : ¬ @Eq (ULift.{u} Bool) i j := hij
        have hji' : ¬ @Eq (ULift.{u} Bool) j i := fun h => hij h.symm
        simp only [twoPatchFibreProductFormalGlueData, twoPatchFibreProductLRSGlueData,
          twoPatchFibreProductGlueData', CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji', Category.assoc,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        congr 1
        obtain ⟨_ | _⟩ := i <;> obtain ⟨_ | _⟩ := j
        · exact absurd rfl hij'
        · -- overlap `(⟨false⟩, ⟨true⟩)`: the `x`-chart glues to the `y`-chart
          have hX : interchangeOpenImmersion I (overlapX R I q) hI ≫
              fibrePr₂ (R := R) (I := I) (A := annulusAlgebra R I q) (B := B) =
              fibrePr₂ (R := R) (I := I)
                (A := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
                  (overlapX R I q)) (B := B) :=
            interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr I (overlapX R I q) hI
          have hY : interchangeOpenImmersion I (overlapY R I q) hI ≫
              fibrePr₂ (R := R) (I := I) (A := annulusAlgebra R I q) (B := B) =
              fibrePr₂ (R := R) (I := I)
                (A := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
                  (overlapY R I q)) (B := B) :=
            interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr I (overlapY R I q) hI
          dsimp only [twoPatchFibreProductTransition, CompletedTensorProduct.mapSpfIso_hom]
          erw [hX, hY, CompletedTensorProduct.mapSpf_comp_fibrePr₂ hI
              (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom
              (AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom]
          rw [spfMap_algHom_toRingHom_id R I B (by ext x; simp), Category.comp_id]
        · -- overlap `(⟨true⟩, ⟨false⟩)`: the mirror gluing (`y`-chart to `x`-chart)
          have hX : interchangeOpenImmersion I (overlapX R I q) hI ≫
              fibrePr₂ (R := R) (I := I) (A := annulusAlgebra R I q) (B := B) =
              fibrePr₂ (R := R) (I := I)
                (A := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
                  (overlapX R I q)) (B := B) :=
            interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr I (overlapX R I q) hI
          have hY : interchangeOpenImmersion I (overlapY R I q) hI ≫
              fibrePr₂ (R := R) (I := I) (A := annulusAlgebra R I q) (B := B) =
              fibrePr₂ (R := R) (I := I)
                (A := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
                  (overlapY R I q)) (B := B) :=
            interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr I (overlapY R I q) hI
          dsimp only [twoPatchFibreProductTransition, CompletedTensorProduct.mapSpfIso_inv]
          erw [hX, hY, CompletedTensorProduct.mapSpf_comp_fibrePr₂ hI
              (annulusFibreChartTransitionAlg R I q hI).toAlgHom
              (AlgEquiv.refl (R := R) (A₁ := B)).toAlgHom]
          rw [spfMap_algHom_toRingHom_id R I B (by ext x; simp), Category.comp_id]
        · exact absurd rfl hij')

end AlgebraicGeometry
