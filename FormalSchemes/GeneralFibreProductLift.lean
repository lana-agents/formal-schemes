import FormalSchemes.GlueOpenCoverFactorBothAlg
import FormalSchemes.GeneralFibreProductChartLift
import FormalSchemes.GeneralFibreProductLiftUnique
import FormalSchemes.OpenImmersionSourceFormalScheme
import FormalSchemes.OpenCoverGlueMorphisms
import FormalSchemes.SpfGammaRoundTrip

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Existence of the general fibre-product mediating morphism `X ×_{Spf R} Y`

For the fully general two-sided fibre product `X ×_{Spf R} Y` of two affine-charted glued formal
schemes `X` (charts `Spf(A i)`) and `Y` (charts `Spf(B j)`) over the affine adic base `Spf R`, this
file proves the **existence half** of the fibre-product universal property (EGA I §10.7): given a
locally finitely-generated formal scheme `Z` with morphisms `a : Z ⟶ X`, `b : Z ⟶ Y` whose
composites into the base agree (`a ≫ xStructMap = b ≫ yStructMap`), and per-source-chart continuity
witnesses `hs`, there is a mediating morphism `fibreLift : Z ⟶ X ×_{Spf R} Y` with
`fibreLift ≫ pr₁ = a` and `fibreLift ≫ pr₂ = b`.

## Route

Refine the source cover of `Z` along the pair `(a, b)` (`bothRefinedCover`, issue 398): every piece
`c` is a finitely generated affine chart `Spf L_c` of `Z` whose range lands inside a single
`X`-chart `Spf(A_{xIndex c})` **and** a single `Y`-chart `Spf(B_{yIndex c})`. The per-chart
mediating morphism `chartLift` (issue 398) then produces a map
`k c : Spf L_c ⟶ X ×_{Spf R} Y` into the product chart `Spf(A_{xIndex c} ⊗̂_R B_{yIndex c})`, and
`fibreLift` glues the `k c` via `OpenCover.glueMorphisms`.

The two triangle identities `fibreLift ≫ pr₁ = a`, `fibreLift ≫ pr₂ = b` reduce, by
`OpenCover.hom_ext`, to the per-piece triangles `k c ≫ pr₁ = cmap c ≫ a` (`chartLift_comp_pr₁`
followed by the `Spf∘Γ` round-trip identifying the localized chart map with `xFactor c`, then
`xFactor_comp_ι`); symmetrically for `pr₂`.

The `glueMorphisms` overlap obligation — that the two maps `pullback.fst ≫ k c` and
`pullback.snd ≫ k c'` out of the overlap `V(c,c') = pullback (cmap c) (cmap c')` coincide — is
discharged by packaging `V(c,c')` as a `LocallyFG` formal scheme (`overlapFormalScheme`, issue 447)
and applying the fibre-product uniqueness `fibreLift_unique` (issue 234d): both maps agree after
`pr₁` (via `a` and `pullback.condition`) and after `pr₂` (via `b`).

## Scope

Continuity-restricted existence: the per-piece continuity witnesses `hs` are unavoidable at the
level of arbitrary locally-ringed-space morphisms (issue 156). Uniqueness is issue 234d (merged).
Together they constitute the fibre-product universal property (EGA I §10.7), feeding the general
diagonal (issue 235) and §10.15 general separatedness (issue 62).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorProduct

universe u

namespace AlgebraicGeometry

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {Z : FormalScheme.{u}} (D : BothChartedFibreDatumXY R I hI)
variable (a : Z.toLocallyRingedSpace ⟶ D.xGlued.toLocallyRingedSpace)
variable (b : Z.toLocallyRingedSpace ⟶ D.yGlued.toLocallyRingedSpace)
variable (hZ : Z.LocallyFG)

/-- **The per-piece mediating morphism** `k c : Spf L_c ⟶ X ×_{Spf R} Y` of the refined source
cover: the per-chart `chartLift` induced by the `R`-algebra maps `xAlg c`, `yAlg c` into the chart
ring `S_c`, landing in the product chart `Spf(A_{xIndex c} ⊗̂_R B_{yIndex c})`. -/
def bothChartLift (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (D.bothRefinedChart a b hZ c).J.comap (D.refinedStructHom a b hZ c))
    (c : (D.bothRefinedCover a b hZ).J) :
    letI := D.refinedAlgebra a b hZ c
    ((D.bothRefinedCover a b hZ).obj c).toLocallyRingedSpace ⟶
      D.generalFibreProduct.toLocallyRingedSpace :=
  letI := D.refinedAlgebra a b hZ c
  D.chartLift (D.xIndex a b hZ c, D.yIndex a b hZ c) (D.refinedAlgebra_hIL a b hZ c (hs c))
    (D.xAlg a b hZ c) (D.yAlg a b hZ c hcomm)

variable (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
variable (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
variable (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)

/-- **The per-piece triangle for `pr₁`.** Composing the piece map `k c` with the first projection
recovers `map c ≫ a`: `chartLift_comp_pr₁` identifies `k c ≫ pr₁` with the localized chart map, the
`Spf∘Γ` round-trip identifies that with `xFactor c`, and `xFactor_comp_ι` gives `map c ≫ a`. -/
theorem bothChartLift_comp_pr₁ (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (D.bothRefinedChart a b hZ c).J.comap (D.refinedStructHom a b hZ c))
    (c : (D.bothRefinedCover a b hZ).J) :
    D.bothChartLift a b hZ hcomm hs c ≫ D.pr₁ hV hf ht =
      (D.bothRefinedChart a b hZ c).map ≫ a := by
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  letI := D.refinedAlgebra a b hZ c
  refine (D.chartLift_comp_pr₁ (D.xIndex a b hZ c, D.yIndex a b hZ c)
      (D.refinedAlgebra_hIL a b hZ c (hs c)) (D.xAlg a b hZ c) (D.yAlg a b hZ c hcomm)
      hV hf ht).trans ?_
  refine Eq.trans (congrArg (· ≫ D.xFormalGlueData.ι (D.xIndex a b hZ c)) ?_)
    (D.xFactor_comp_ι a b hZ c)
  exact FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap _ _
    (hI.map (algebraMap R (D.A (D.xIndex a b hZ c)))) (D.bothRefinedChart a b hZ c).fg
    (D.xFactor a b hZ c) _

/-- **The per-piece triangle for `pr₂`.** Analogue of `bothChartLift_comp_pr₁` on the `Y`-side. -/
theorem bothChartLift_comp_pr₂ (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (D.bothRefinedChart a b hZ c).J.comap (D.refinedStructHom a b hZ c))
    (c : (D.bothRefinedCover a b hZ).J) :
    D.bothChartLift a b hZ hcomm hs c ≫ D.pr₂ hV hf ht =
      (D.bothRefinedChart a b hZ c).map ≫ b := by
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  letI := D.refinedAlgebra a b hZ c
  refine (D.chartLift_comp_pr₂ (D.xIndex a b hZ c, D.yIndex a b hZ c)
      (D.refinedAlgebra_hIL a b hZ c (hs c)) (D.xAlg a b hZ c) (D.yAlg a b hZ c hcomm)
      hV hf ht).trans ?_
  refine Eq.trans (congrArg (· ≫ D.yFormalGlueData.ι (D.yIndex a b hZ c)) ?_)
    (D.yFactor_comp_ι a b hZ c)
  exact FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap _ _
    (hI.map (algebraMap R (D.B (D.yIndex a b hZ c)))) (D.bothRefinedChart a b hZ c).fg
    (D.yFactor a b hZ c) _

end BothChartedFibreDatumXY

end AlgebraicGeometry
