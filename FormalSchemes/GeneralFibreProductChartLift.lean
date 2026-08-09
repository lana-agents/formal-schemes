import FormalSchemes.GeneralFibreProductBothProjectionLeft
import FormalSchemes.GeneralFibreProductBothProjectionRight

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The per-chart mediating morphism of the general two-sided fibre product `X ×_{Spf R} Y`

`FormalSchemes.GeneralFibreProductBothObject` assembles, from a `BothChartedFibreDatum`, the general
two-sided fibre product `X ×_{Spf R} Y` of two affine-charted glued formal schemes `X` (charts
`Spf(A i)`, `i : JX`) and `Y` (charts `Spf(B j)`, `j : JY`) over the affine adic base `Spf R`, glued
from the double completed-tensor charts `Spf(A_{p.1} ⊗̂_R B_{p.2})` (`p : JX × JY`), with glue
inclusions `formalGlueData.ι p`. `FormalSchemes.GeneralFibreProductBothProjectionLeft`/`Right`
build the projections `pr₁ : X ×_{Spf R} Y ⟶ X` and `pr₂ : X ×_{Spf R} Y ⟶ Y` into the exposed
glued factors.

This file builds the **per-source-chart mediating morphism** that the assembly of the universal
property (issue 234c) glues. Given a point of the product chart `p` — an `R`-algebra `S` with ideal
of definition `L` together with `R`-algebra maps `f : A_{p.1} →ₐ[R] S` and `g : B_{p.2} →ₐ[R] S` —
the affine mediating morphism `CompletedTensorProduct.fibreLift` produces a map
`Spf L ⟶ Spf(A_{p.1} ⊗̂_R B_{p.2})` into the product chart, which we compose with the glue inclusion
`formalGlueData.ι p` to land in the glued fibre product.

## Main definitions

* `BothChartedFibreDatumXY.chartLift`: the per-chart mediating morphism
  `Spf L ⟶ X ×_{Spf R} Y`.
* `BothChartedFibreDatumXY.chartLift_comp_pr₁`: it recovers `Spf(f)` (followed by `X`'s chart
  inclusion) after the first projection.
* `BothChartedFibreDatumXY.chartLift_comp_pr₂`: it recovers `Spf(g)` (followed by `Y`'s chart
  inclusion) after the second projection.

## The concreteness hypotheses

Like the projections `pr₁`/`pr₂`, the factorisation lemmas take the three concreteness hypotheses
`hV`/`hf`/`ht` pinning the carried abstract glue of `D` to the concrete `bothAlgData*`; they hold by
`rfl` for any datum built by the smart constructor `ofAlgebraData`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum
open CompletedTensorProduct

universe u

namespace AlgebraicGeometry

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
-- The affine mediating morphism `CompletedTensorProduct.fibreLift` lives over the adic base
-- `Spf R`, so it requires `R` to carry its adic topology.
variable [TopologicalSpace R] [IsAdicRing I]
variable (D : BothChartedFibreDatumXY R I hI)

/-- **The per-chart mediating morphism** `Spf L ⟶ X ×_{Spf R} Y`: the affine mediating morphism
`CompletedTensorProduct.fibreLift` into the product chart `Spf(A_{p.1} ⊗̂_R B_{p.2})` induced by the
`R`-algebra maps `f`, `g`, composed with the glue inclusion `formalGlueData.ι p`. -/
def chartLift (p : D.JX × D.JY)
    {S : Type u} [CommRing S] [Algebra R S] [TopologicalSpace S] {L : Ideal S} [IsAdicRing L]
    (hIL : I.map (algebraMap R S) ≤ L)
    (f : letI := D.commRingA; letI := D.algebraA; D.A p.1 →ₐ[R] S)
    (g : letI := D.commRingB; letI := D.algebraB; D.B p.2 →ₐ[R] S) :
    letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
    letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
    FormalSpectrum.locallyRingedSpaceObj L ⟶
      D.toBothChartedFibreDatum.generalFibreProduct.toLocallyRingedSpace :=
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  CompletedTensorProduct.fibreLift hIL f g hI ≫ D.formalGlueData.ι p

/-- **The mediating morphism recovers `Spf(f)` after the first projection.** Composing `chartLift`
with `pr₁` and restricting to the `I·A_{p.1}` convention of the exposed `X` yields `Spf(f)` followed
by `X`'s chart inclusion `ι_{p.1}`. -/
theorem chartLift_comp_pr₁ (p : D.JX × D.JY)
    {S : Type u} [CommRing S] [Algebra R S] [TopologicalSpace S] {L : Ideal S} [IsAdicRing L]
    (hIL : I.map (algebraMap R S) ≤ L)
    (f : letI := D.commRingA; letI := D.algebraA; D.A p.1 →ₐ[R] S)
    (g : letI := D.commRingB; letI := D.algebraB; D.B p.2 →ₐ[R] S)
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm) :
    letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
    letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
    D.chartLift p hIL f g ≫ D.pr₁ hV hf ht =
      FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.A p.1))) L
        f.toRingHom (CompletedTensorProduct.algHom_le_comap f hIL) ≫ D.xFormalGlueData.ι p.1 := by
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  haveI := CompletedTensorProduct.isAdicRing R I (D.A p.1) (D.B p.2) hI
  -- The index type `JX × JY` of the glue data is semireducible (the `GlueData.ofGlueData'`
  -- object-defeq wall), so `rw` cannot match against `ι p`; chase the equality in term mode.
  rw [chartLift, Category.assoc]
  exact
    (CompletedTensorProduct.fibreLift hIL f g hI ≫= D.ι_pr₁ hV hf ht p).trans <|
      (Category.assoc _ _ _).symm.trans
        (CompletedTensorProduct.fibreLift_comp_pr₁ hIL f g hI =≫ D.xFormalGlueData.ι p.1)

/-- **The mediating morphism recovers `Spf(g)` after the second projection.** Composing `chartLift`
with `pr₂` and restricting to the `I·B_{p.2}` convention of the exposed `Y` yields `Spf(g)` followed
by `Y`'s chart inclusion `ι_{p.2}`. -/
theorem chartLift_comp_pr₂ (p : D.JX × D.JY)
    {S : Type u} [CommRing S] [Algebra R S] [TopologicalSpace S] {L : Ideal S} [IsAdicRing L]
    (hIL : I.map (algebraMap R S) ≤ L)
    (f : letI := D.commRingA; letI := D.algebraA; D.A p.1 →ₐ[R] S)
    (g : letI := D.commRingB; letI := D.algebraB; D.B p.2 →ₐ[R] S)
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm) :
    letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
    letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
    D.chartLift p hIL f g ≫ D.pr₂ hV hf ht =
      FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (D.B p.2))) L
        g.toRingHom (CompletedTensorProduct.algHom_le_comap g hIL) ≫ D.yFormalGlueData.ι p.2 := by
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  haveI := CompletedTensorProduct.isAdicRing R I (D.A p.1) (D.B p.2) hI
  -- The index type `JX × JY` of the glue data is semireducible (the `GlueData.ofGlueData'`
  -- object-defeq wall), so `rw` cannot match against `ι p`; chase the equality in term mode.
  rw [chartLift, Category.assoc]
  exact
    (CompletedTensorProduct.fibreLift hIL f g hI ≫= D.ι_pr₂ hV hf ht p).trans <|
      (Category.assoc _ _ _).symm.trans
        (CompletedTensorProduct.fibreLift_comp_pr₂ hIL f g hI =≫ D.yFormalGlueData.ι p.2)

end BothChartedFibreDatumXY

end AlgebraicGeometry
