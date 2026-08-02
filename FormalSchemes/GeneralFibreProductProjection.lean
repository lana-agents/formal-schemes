import FormalSchemes.GeneralFibreProductAffineBase
import FormalSchemes.TwoPatchFibreProductProjection
import FormalSchemes.GlueMorphisms

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The second projection of the general fibre product `X ×_{Spf R} Spf B`

`FormalSchemes.GeneralFibreProductAffineBase` assembles, from an `AffineChartedFibreDatum`, the
fibre product `X ×_{Spf R} Spf B` of a general affine-charted glued `X` over the affine base `Spf B`
as a glued formal scheme `AffineChartedFibreDatum.fibreProduct`, with charts `Spf(A_i ⊗̂_R B)` glued
along the base-changed transitions `t i j = (mapSpfIso τ_ij (refl B)).hom`.

This file builds the **second projection** `pr₂ : X ×_{Spf R} Spf B ⟶ Spf B`, gluing the affine
second projections `Spf(inr) : Spf(A_i ⊗̂_R B) ⟶ Spf B` across the (arbitrary-index) cover via
`FormalScheme.GlueData.glueMorphisms`. It generalises the two-patch projection
`AlgebraicGeometry.twoPatchFibreProductPr₂`
(`FormalSchemes.TwoPatchFibreProductProjection`, `J = ULift Bool`) to the general index type `J` of
the datum, and reuses the two-patch's per-chart map `pr₂Chart` and transition naturality
`CompletedTensorProduct.mapSpf_comp_inrMap` verbatim.

The compatibility datum `glueMorphisms` consumes on the double overlap is the naturality square

`interchange(g_ij) ≫ pr₂Chart(A_i) = t.hom ≫ interchange(g_ji) ≫ pr₂Chart(A_j)`

(`AffineChartedFibreDatum.pr₂_naturality`), assembled from the merged data:

* the away-localization interchange chart is a morphism over `Spf B`
  (`interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr`, `CompletedTensorAwayInterchangePr`),
  and
* the base-changed transition `t = mapSpfIso τ (refl B)` commutes with the `inr` projection
  (`CompletedTensorProduct.mapSpf_comp_inrMap`, `CompletedTensorMapSpfPr`), with the residual
  `Spf(refl B)` collapsed to `𝟙` via `locallyRingedSpaceMap_id`.

Because `X` enters the datum only through its *algebra* data `(A_i, g_ij, τ_ij)` and the affine base
`Spf B` needs no adic-ring hypothesis, the whole construction stays in the instance-light world of
`FormalSpectrum.locallyRingedSpaceMap` of the `inr` homomorphisms — exactly as for the two-patch
model. The *first* projection `pr₁ : X ×_{Spf R} Spf B ⟶ X` and the cone identity over `Spf R`
require `X` as a *glued* object (its own `A`-level cocycle and glue inclusions `ι`), which the
present `AffineChartedFibreDatum` does not carry; they are left to a follow-up that first exposes
the glued `X`.

## Main definitions

* `AlgebraicGeometry.AffineChartedFibreDatum.pr₂_naturality`: the double-overlap compatibility
  square of the second projection.
* `AlgebraicGeometry.AffineChartedFibreDatum.pr₂`: the glued second projection
  `X ×_{Spf R} Spf B ⟶ Spf B`.
* `AlgebraicGeometry.AffineChartedFibreDatum.ι_pr₂`: it restricts to `pr₂Chart(A_i)` along each
  glue inclusion `ι i`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum
open CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

namespace AffineChartedFibreDatum

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable {B : Type u} [CommRing B] [Algebra R B]
variable (D : AffineChartedFibreDatum R I hI B)

/-- **The double-overlap compatibility square of the second projection.** For distinct charts
`i ≠ j`, the `(i,j)`-overlap interchange chart followed by the second projection `Spf(inr)` of
chart `i` equals the base-changed transition `t i j = (mapSpfIso τ_ij (refl B)).hom` followed by the
`(j,i)`-overlap interchange chart and the second projection of chart `j` — the datum
`glueMorphisms` consumes to glue `pr₂` across the cover. This is the general-index analogue of
`twoPatchFibreProduct_pr₂_naturality`, proved by the same reduction. -/
theorem pr₂_naturality (i j : D.J) (h : i ≠ j) :
    letI := D.commRing
    letI := D.algebra
    interchangeOpenImmersion (B := B) I (D.g i j) hI ≫ pr₂Chart R I B (D.A i) =
      (mapSpfIso hI (D.τ i j h) (AlgEquiv.refl (R := R) (A₁ := B))).hom ≫
        interchangeOpenImmersion (B := B) I (D.g j i) hI ≫ pr₂Chart R I B (D.A j) := by
  letI := D.commRing
  letI := D.algebra
  simp only [pr₂Chart]
  rw [interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr I (D.g i j) hI,
    interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr I (D.g j i) hI,
    mapSpfIso_hom,
    mapSpf_comp_inrMap hI (D.τ i j h).symm.toAlgHom
      (AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom]
  have hg : (((AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom : B →ₐ[R] B)).toRingHom =
      RingHom.id B := by
    ext b; simp
  rw [FormalSpectrum.locallyRingedSpaceMap_congr (φ₂ := RingHom.id B)
      (h₂ := (Ideal.comap_id (I.map (algebraMap R B))).ge) (hφ := hg),
    FormalSpectrum.locallyRingedSpaceMap_id, Category.comp_id]

/-- **The second projection of the general fibre product** `pr₂ : X ×_{Spf R} Spf B ⟶ Spf B`,
glued from the affine second projections `Spf(inr) : Spf(A_i ⊗̂_R B) ⟶ Spf B` via
`FormalScheme.GlueData.glueMorphisms`, using the double-overlap compatibility squares
`pr₂_naturality`. Off the diagonal the overlap obligation is `pr₂_naturality`; on the diagonal it
collapses through `GlueData.t_id`. -/
def pr₂ :
    (D.fibreProduct).toLocallyRingedSpace ⟶ locallyRingedSpaceObj (I.map (algebraMap R B)) :=
  letI := D.commRing
  letI := D.algebra
  D.formalGlueData.glueMorphisms (fun i => pr₂Chart R I B (D.A i)) (by
    intro i j
    by_cases hij : i = j
    · -- diagonal: `t i i = 𝟙`, so both sides collapse to `f i i ≫ pr₂Chart`.
      subst hij
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · -- off-diagonal: unfold the `ofGlueData'` `if`-forms; the dite conditions are on `= : D.J`,
      -- so re-type the disequalities in `¬ Eq` form before rewriting.
      have hij' : ¬ @Eq D.J i j := hij
      have hji' : ¬ @Eq D.J j i := fun heq => hij heq.symm
      simp only [formalGlueData, lrsGlueData, glueData', CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji', Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [D.pr₂_naturality i j hij'])

/-- **The second projection restricts to `pr₂Chart(A_i)` along each glue inclusion.** -/
@[reassoc (attr := simp)]
theorem ι_pr₂ (i : D.J) :
    letI := D.commRing
    letI := D.algebra
    D.formalGlueData.ι i ≫ D.pr₂ = pr₂Chart R I B (D.A i) := by
  letI := D.commRing
  letI := D.algebra
  exact D.formalGlueData.ι_glueMorphisms _ _ i

end AffineChartedFibreDatum

end AlgebraicGeometry
