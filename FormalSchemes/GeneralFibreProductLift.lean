import FormalSchemes.GlueOpenCoverFactorBothAlg
import FormalSchemes.OpenCoverGlueMorphisms
import FormalSchemes.OpenImmersionSourceFormalScheme
import FormalSchemes.GeneralFibreProductLiftUnique
import FormalSchemes.SpfGammaRoundTrip

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Existence of the general fibre-product mediating morphism `X ×_{Spf R} Y`

For the fully general two-sided fibre product `X ×_{Spf R} Y` of two affine-charted glued formal
schemes `X` (charts `Spf(A i)`) and `Y` (charts `Spf(B j)`) over the affine adic base `Spf R`
(`FormalSchemes.GeneralFibreProductBothObject`), this file proves the **existence half** of the
fibre-product universal property (EGA I §10.7): from a pair of morphisms `a : Z ⟶ X`, `b : Z ⟶ Y`
out of a locally finitely-generated formal scheme `Z` agreeing over the base, together with the
per-piece continuity witnesses, we assemble a mediating morphism `fibreLift : Z ⟶ X ×_{Spf R} Y`
recovering `a` and `b` after the two projections `pr₁`, `pr₂`.

## Route

Refine the source cover of `Z` along the pair `(a, b)` (`bothRefinedCover`, issue 412c): every
piece `c` is a finitely generated affine chart `Spf S_c` of `Z` whose two restrictions `map ≫ a`,
`map ≫ b` factor simultaneously through a single `X`-chart `Spf(A_i)` and a single `Y`-chart
`Spf(B_j)`. The per-piece `R`-algebra data (`xAlg`, `yAlg`, issue 412c Part 2) feeds the affine
mediating morphism `chartLift` (issue 398), giving `k c : Spf S_c ⟶ X ×_{Spf R} Y`. These local
morphisms agree on the pairwise overlaps `V(c,c') = Spf S_c ×_Z Spf S_{c'}` — each overlap is
itself a `LocallyFG` formal scheme (`overlapFormalScheme`, issue 447), so the uniqueness half
`fibreLift_unique` (issue 234d) forces the agreement from the two projection identities. Descent
(`OpenCover.glueMorphisms`, issue 397) then glues the `k c` into `fibreLift`.

## Status

The construction `fibreLift` and the two triangles `fibreLift_comp_pr₁`, `fibreLift_comp_pr₂` are
complete, as are the per-piece factorisations `fibreLiftPiece_comp_pr₁`/`_pr₂` and the two
projection legs `hpr₁`/`hpr₂` of the overlap obligation `fibreLift_overlap`. The **one remaining
gap** is the continuity input `hcont` that `fibreLift_unique` demands for the overlap's internally
chosen refined cover: it reduces (see the inline derivation in `fibreLift_overlap`) to the general
fact that an **open immersion of affine adic formal spectra induces an adic (continuous)
global-sections map**, which is not yet available on master (only the basic-open special case
`FormalSpectrum.le_comap_awayCompletionHom` exists). Proving that continuity lemma — or restating
`fibreLift_unique` to derive `hcont` from continuity on a *given* cover — closes this file.

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
variable (D : BothChartedFibreDatumXY R I hI)

/-- **The per-piece mediating morphism** `k c : Spf S_c ⟶ X ×_{Spf R} Y` of the refined cover: the
affine `chartLift` on the product chart `Spf(A_{xIndex c} ⊗̂_R B_{yIndex c})` induced by the
per-piece algebra maps `xAlg c`, `yAlg c`. -/
def fibreLiftPiece {Z : FormalScheme.{u}}
    (a : Z.toLocallyRingedSpace ⟶ D.xGlued.toLocallyRingedSpace)
    (b : Z.toLocallyRingedSpace ⟶ D.yGlued.toLocallyRingedSpace)
    (hZ : Z.LocallyFG)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (D.bothRefinedChart a b hZ c).J.comap (D.refinedStructHom a b hZ c))
    (c : (D.bothRefinedCover a b hZ).J) :
    ((D.bothRefinedCover a b hZ).obj c).toLocallyRingedSpace ⟶
      D.generalFibreProduct.toLocallyRingedSpace :=
  letI := D.refinedAlgebra a b hZ c
  D.chartLift (D.xIndex a b hZ c, D.yIndex a b hZ c)
    (D.refinedAlgebra_hIL a b hZ c (hs c)) (D.xAlg a b hZ c) (D.yAlg a b hZ c hcomm)

/-- **The per-piece morphism recovers `map ≫ a` after `pr₁`.** -/
theorem fibreLiftPiece_comp_pr₁
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    {Z : FormalScheme.{u}}
    (a : Z.toLocallyRingedSpace ⟶ D.xGlued.toLocallyRingedSpace)
    (b : Z.toLocallyRingedSpace ⟶ D.yGlued.toLocallyRingedSpace)
    (hZ : Z.LocallyFG)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (D.bothRefinedChart a b hZ c).J.comap (D.refinedStructHom a b hZ c))
    (c : (D.bothRefinedCover a b hZ).J) :
    D.fibreLiftPiece a b hZ hcomm hs c ≫ D.pr₁ hV hf ht =
      (D.bothRefinedChart a b hZ c).map ≫ a := by
  letI := D.commRingA; letI := D.algebraA; letI := D.topologyA; letI := D.isAdicA
  letI := D.refinedAlgebra a b hZ c
  have h1 := D.chartLift_comp_pr₁ (D.xIndex a b hZ c, D.yIndex a b hZ c)
    (D.refinedAlgebra_hIL a b hZ c (hs c)) (D.xAlg a b hZ c) (D.yAlg a b hZ c hcomm) hV hf ht
  have hrt : FormalSpectrum.locallyRingedSpaceMap
      (I.map (algebraMap R (D.A (D.xIndex a b hZ c)))) (D.bothRefinedChart a b hZ c).J
      (D.xAlg a b hZ c).toRingHom
      (CompletedTensorProduct.algHom_le_comap (D.xAlg a b hZ c)
        (D.refinedAlgebra_hIL a b hZ c (hs c))) = D.xFactor a b hZ c :=
    locallyRingedSpaceMap_globalSectionsMap (I.map (algebraMap R (D.A (D.xIndex a b hZ c))))
      (D.bothRefinedChart a b hZ c).J (hI.map (algebraMap R (D.A (D.xIndex a b hZ c))))
      (D.bothRefinedChart a b hZ c).fg (D.xFactor a b hZ c) _
  exact h1.trans ((congrArg (· ≫ D.xFormalGlueData.ι (D.xIndex a b hZ c)) hrt).trans
    (D.xFactor_comp_ι a b hZ c))

/-- **The per-piece morphism recovers `map ≫ b` after `pr₂`.** -/
theorem fibreLiftPiece_comp_pr₂
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    {Z : FormalScheme.{u}}
    (a : Z.toLocallyRingedSpace ⟶ D.xGlued.toLocallyRingedSpace)
    (b : Z.toLocallyRingedSpace ⟶ D.yGlued.toLocallyRingedSpace)
    (hZ : Z.LocallyFG)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (D.bothRefinedChart a b hZ c).J.comap (D.refinedStructHom a b hZ c))
    (c : (D.bothRefinedCover a b hZ).J) :
    D.fibreLiftPiece a b hZ hcomm hs c ≫ D.pr₂ hV hf ht =
      (D.bothRefinedChart a b hZ c).map ≫ b := by
  letI := D.commRingB; letI := D.algebraB; letI := D.topologyB; letI := D.isAdicB
  letI := D.refinedAlgebra a b hZ c
  have h1 := D.chartLift_comp_pr₂ (D.xIndex a b hZ c, D.yIndex a b hZ c)
    (D.refinedAlgebra_hIL a b hZ c (hs c)) (D.xAlg a b hZ c) (D.yAlg a b hZ c hcomm) hV hf ht
  have hrt : FormalSpectrum.locallyRingedSpaceMap
      (I.map (algebraMap R (D.B (D.yIndex a b hZ c)))) (D.bothRefinedChart a b hZ c).J
      (D.yAlg a b hZ c hcomm).toRingHom
      (CompletedTensorProduct.algHom_le_comap (D.yAlg a b hZ c hcomm)
        (D.refinedAlgebra_hIL a b hZ c (hs c))) = D.yFactor a b hZ c :=
    locallyRingedSpaceMap_globalSectionsMap (I.map (algebraMap R (D.B (D.yIndex a b hZ c))))
      (D.bothRefinedChart a b hZ c).J (hI.map (algebraMap R (D.B (D.yIndex a b hZ c))))
      (D.bothRefinedChart a b hZ c).fg (D.yFactor a b hZ c) _
  exact h1.trans ((congrArg (· ≫ D.yFormalGlueData.ι (D.yIndex a b hZ c)) hrt).trans
    (D.yFactor_comp_ι a b hZ c))

/-- **The overlap obligation for gluing the per-piece morphisms.** On each pairwise overlap
`V(c,c') = Spf S_c ×_Z Spf S_{c'}` the two restrictions of `k c` and `k c'` agree. -/
theorem fibreLift_overlap
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    {Z : FormalScheme.{u}}
    (a : Z.toLocallyRingedSpace ⟶ D.xGlued.toLocallyRingedSpace)
    (b : Z.toLocallyRingedSpace ⟶ D.yGlued.toLocallyRingedSpace)
    (hZ : Z.LocallyFG)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (D.bothRefinedChart a b hZ c).J.comap (D.refinedStructHom a b hZ c))
    (c c' : (D.bothRefinedCover a b hZ).J) :
    pullback.fst ((D.bothRefinedCover a b hZ).cmap c) ((D.bothRefinedCover a b hZ).cmap c') ≫
        D.fibreLiftPiece a b hZ hcomm hs c =
      pullback.snd ((D.bothRefinedCover a b hZ).cmap c) ((D.bothRefinedCover a b hZ).cmap c') ≫
        D.fibreLiftPiece a b hZ hcomm hs c' := by
  have hchart : ((D.bothRefinedCover a b hZ).obj c).LocallyFG :=
    FormalScheme.locallyFG_Spf (D.bothRefinedChart a b hZ c).fg
  refine D.fibreLift_unique hV hf ht
    (pullback.fst ((D.bothRefinedCover a b hZ).cmap c) ((D.bothRefinedCover a b hZ).cmap c') ≫
      D.fibreLiftPiece a b hZ hcomm hs c)
    (pullback.snd ((D.bothRefinedCover a b hZ).cmap c) ((D.bothRefinedCover a b hZ).cmap c') ≫
      D.fibreLiftPiece a b hZ hcomm hs c')
    ((D.bothRefinedCover a b hZ).overlapFormalScheme_locallyFG c c' hchart) ?_ ?_ ?_
  · -- hpr₁: both composites equal `(pullback leg) ≫ (chart) ≫ a`, equal by `pullback.condition`.
    have hcond : pullback.fst ((D.bothRefinedCover a b hZ).cmap c) ((D.bothRefinedCover a b hZ).cmap c')
          ≫ (D.bothRefinedChart a b hZ c).map =
        pullback.snd ((D.bothRefinedCover a b hZ).cmap c) ((D.bothRefinedCover a b hZ).cmap c')
          ≫ (D.bothRefinedChart a b hZ c').map := pullback.condition
    rw [Category.assoc, Category.assoc, D.fibreLiftPiece_comp_pr₁ hV hf ht a b hZ hcomm hs c,
      D.fibreLiftPiece_comp_pr₁ hV hf ht a b hZ hcomm hs c']
    exact (reassoc_of% hcond) a
  · -- hpr₂: symmetric, via `pr₂` and `b`.
    have hcond : pullback.fst ((D.bothRefinedCover a b hZ).cmap c) ((D.bothRefinedCover a b hZ).cmap c')
          ≫ (D.bothRefinedChart a b hZ c).map =
        pullback.snd ((D.bothRefinedCover a b hZ).cmap c) ((D.bothRefinedCover a b hZ).cmap c')
          ≫ (D.bothRefinedChart a b hZ c').map := pullback.condition
    rw [Category.assoc, Category.assoc, D.fibreLiftPiece_comp_pr₂ hV hf ht a b hZ hcomm hs c,
      D.fibreLiftPiece_comp_pr₂ hV hf ht a b hZ hcomm hs c']
    exact (reassoc_of% hcond) b
  · -- hcont: the per-piece continuity of `fibreLift_unique`'s *internal* refined cover of the
    -- overlap `V(c,c') = Spf S_c ×_Z Spf S_{c'}` along `m₁ = pullback.fst ≫ k c`.
    --
    -- For a piece `c''`, writing `W := refinedChart m₁ _ c''` (a chart `Spf W.J ↪ V`),
    -- `P := chartIndex m₁ _ c''` and `F := factor m₁ _ c''`, the goal is the continuity
    --   `idealOfDefinition R I (A_P.1) (B_P.2) ≤ W.J.comap (globalSectionsMap _ _ F)`.
    -- Mirroring the `hJ`/`hgpr`/`hcomp`/`hc2` block of `fibreLift_unique` (issue 234d), this
    -- reduces — via `idealOfDefinition = (I·A_P.1).map inl` and `pr₁ChartSelf`-functoriality —
    -- to continuity of the base composite
    --   `W.map ≫ m₁ ≫ pr₁ ≫ xStructMap = W.map ≫ pullback.fst ≫ (bothRefinedChart c).map ≫ a ≫ xStructMap`
    -- (using `fibreLiftPiece_comp_pr₁`). Threading through the chart `S_c`, where
    -- `(bothRefinedChart c).map ≫ a ≫ xStructMap` is continuous by the given witness `hs c`, this in
    -- turn requires continuity of the OPEN IMMERSION `W.map ≫ pullback.fst : Spf W.J ↪ Spf S_c`,
    -- i.e. `S_c.J ≤ W.J.comap (globalSectionsMap S_c.J W.J (W.map ≫ pullback.fst))`.
    --
    -- BLOCKER (reported to the launching issue): this last fact — that an open immersion of affine
    -- adic formal spectra induces an *adic* (continuous) global-sections map — is a genuine general
    -- theorem NOT present on master (only the basic-open special case `le_comap_awayCompletionHom`
    -- exists). It is the missing infrastructure isolating the `hcont` obligation; see the handoff
    -- report for the recommended split (a continuity sub-lemma + this assembly).
    sorry

/-- **The general fibre-product mediating morphism** `fibreLift : Z ⟶ X ×_{Spf R} Y` (EGA I §10.7,
existence half): glued from the per-piece morphisms `fibreLiftPiece` via `OpenCover.glueMorphisms`,
using the overlap agreement `fibreLift_overlap`. -/
def fibreLift
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    {Z : FormalScheme.{u}}
    (a : Z.toLocallyRingedSpace ⟶ D.xGlued.toLocallyRingedSpace)
    (b : Z.toLocallyRingedSpace ⟶ D.yGlued.toLocallyRingedSpace)
    (hZ : Z.LocallyFG)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (D.bothRefinedChart a b hZ c).J.comap (D.refinedStructHom a b hZ c)) :
    Z.toLocallyRingedSpace ⟶ D.generalFibreProduct.toLocallyRingedSpace :=
  (D.bothRefinedCover a b hZ).glueMorphisms
    (fun c => D.fibreLiftPiece a b hZ hcomm hs c)
    (D.fibreLift_overlap hV hf ht a b hZ hcomm hs)

/-- **The mediating morphism recovers `a` after the first projection.** -/
theorem fibreLift_comp_pr₁
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    {Z : FormalScheme.{u}}
    (a : Z.toLocallyRingedSpace ⟶ D.xGlued.toLocallyRingedSpace)
    (b : Z.toLocallyRingedSpace ⟶ D.yGlued.toLocallyRingedSpace)
    (hZ : Z.LocallyFG)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (D.bothRefinedChart a b hZ c).J.comap (D.refinedStructHom a b hZ c)) :
    D.fibreLift hV hf ht a b hZ hcomm hs ≫ D.pr₁ hV hf ht = a := by
  refine (D.bothRefinedCover a b hZ).hom_ext _ _ (fun c => ?_)
  rw [fibreLift, ← Category.assoc, (D.bothRefinedCover a b hZ).map_glueMorphisms _ _ c]
  exact D.fibreLiftPiece_comp_pr₁ hV hf ht a b hZ hcomm hs c

/-- **The mediating morphism recovers `b` after the second projection.** -/
theorem fibreLift_comp_pr₂
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    {Z : FormalScheme.{u}}
    (a : Z.toLocallyRingedSpace ⟶ D.xGlued.toLocallyRingedSpace)
    (b : Z.toLocallyRingedSpace ⟶ D.yGlued.toLocallyRingedSpace)
    (hZ : Z.LocallyFG)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (D.bothRefinedChart a b hZ c).J.comap (D.refinedStructHom a b hZ c)) :
    D.fibreLift hV hf ht a b hZ hcomm hs ≫ D.pr₂ hV hf ht = b := by
  refine (D.bothRefinedCover a b hZ).hom_ext _ _ (fun c => ?_)
  rw [fibreLift, ← Category.assoc, (D.bothRefinedCover a b hZ).map_glueMorphisms _ _ c]
  exact D.fibreLiftPiece_comp_pr₂ hV hf ht a b hZ hcomm hs c

end BothChartedFibreDatumXY

end AlgebraicGeometry