import FormalSchemes.GlueOpenCoverFactorBothAlg
import FormalSchemes.OpenCoverGlueMorphisms
import FormalSchemes.OpenImmersionSourceFormalScheme
import FormalSchemes.GeneralFibreProductLiftUnique
import FormalSchemes.GeneralFibreProductLiftPiece
import FormalSchemes.LiftedBasicOpenCover
import FormalSchemes.AffineFibreProductLRS
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

## Discharging the overlap continuity

The overlap agreement `fibreLift_overlap` is proven by descending along an **explicit** cover of the
overlap `V(c,c') = Spf S_c ×_Z Spf S_{c'}` rather than the internally-chosen refined cover that
`fibreLift_unique` would use. The general fact "an open immersion of affine adic formal spectra is
adic on global sections" is *false* (issue 460), but the overlap's real charts are adic *by
construction*: `V(c,c')` is covered by basic-open charts of `Spf S_c` lifted through the open
immersion `pullback.fst` (`FormalScheme.liftedBasicCover`), and each cover map `w` satisfies
`w ≫ pullback.fst = basicOpenChart S_c g` (`liftedBasicCover_map_comp_pf`), so `w ≫ pullback.fst`
is adic on global sections (issue 460a,
`FormalSpectrum.le_comap_globalSectionsMap_basicOpenChart_comp`). Composing with the affine chart
lift's continuity (`CompletedTensorProduct.lift_le_comap`) discharges the per-piece continuity, and
the per-chart uniqueness primitive `BothChartedFibreDatumXY.hom_eq_of_chart_factor` (issue 234d's
core) closes each piece.

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

set_option backward.isDefEq.respectTransparency false in
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
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  letI := D.refinedAlgebra a b hZ c
  have hchart : ((D.bothRefinedCover a b hZ).obj c).LocallyFG :=
    FormalScheme.locallyFG_Spf (D.bothRefinedChart a b hZ c).fg
  set V := (D.bothRefinedCover a b hZ).overlapFormalScheme c c' hchart with hVdef
  set pf := pullback.fst ((D.bothRefinedCover a b hZ).cmap c) ((D.bothRefinedCover a b hZ).cmap c')
    with hpf
  set ps := pullback.snd ((D.bothRefinedCover a b hZ).cmap c) ((D.bothRefinedCover a b hZ).cmap c')
    with hps
  haveI hpfOI : LocallyRingedSpace.IsOpenImmersion pf :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      (pullback.fst ((D.bothRefinedCover a b hZ).cmap c) ((D.bothRefinedCover a b hZ).cmap c')))
  -- The two projection legs of the overlap: equal because `k c`, `k c'` agree after `pr₁`/`pr₂` on
  -- the two `pullback` legs, which agree via `pullback.condition`.
  have hpr₁ : (pf ≫ D.fibreLiftPiece a b hZ hcomm hs c) ≫ D.pr₁ hV hf ht =
      (ps ≫ D.fibreLiftPiece a b hZ hcomm hs c') ≫ D.pr₁ hV hf ht := by
    have hcond : pf ≫ (D.bothRefinedChart a b hZ c).map =
        ps ≫ (D.bothRefinedChart a b hZ c').map := pullback.condition
    rw [Category.assoc, Category.assoc, D.fibreLiftPiece_comp_pr₁ hV hf ht a b hZ hcomm hs c,
      D.fibreLiftPiece_comp_pr₁ hV hf ht a b hZ hcomm hs c']
    exact (reassoc_of% hcond) a
  have hpr₂ : (pf ≫ D.fibreLiftPiece a b hZ hcomm hs c) ≫ D.pr₂ hV hf ht =
      (ps ≫ D.fibreLiftPiece a b hZ hcomm hs c') ≫ D.pr₂ hV hf ht := by
    have hcond : pf ≫ (D.bothRefinedChart a b hZ c).map =
        ps ≫ (D.bothRefinedChart a b hZ c').map := pullback.condition
    rw [Category.assoc, Category.assoc, D.fibreLiftPiece_comp_pr₂ hV hf ht a b hZ hcomm hs c,
      D.fibreLiftPiece_comp_pr₂ hV hf ht a b hZ hcomm hs c']
    exact (reassoc_of% hcond) b
  set P : D.formalGlueData.toLocallyRingedSpaceGlueData.J :=
    (D.xIndex a b hZ c, D.yIndex a b hZ c) with hP
  set CTPF := CompletedTensorProduct.fibreLift (D.refinedAlgebra_hIL a b hZ c (hs c))
    (D.xAlg a b hZ c) (D.yAlg a b hZ c hcomm) hI with hCTPF
  have hk : D.fibreLiftPiece a b hZ hcomm hs c = CTPF ≫ D.formalGlueData.ι P := rfl
  -- Continuity of the affine chart lift `CTPF` on global sections (issue 234a).
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (D.A P.1) (D.B P.2)) :=
    CompletedTensorProduct.isAdicRing R I (D.A P.1) (D.B P.2) hI
  have hφ : CompletedTensorProduct.idealOfDefinition R I (D.A P.1) (D.B P.2) ≤
      (D.bothRefinedChart a b hZ c).J.comap
        (FormalSpectrum.globalSectionsMap
          (CompletedTensorProduct.idealOfDefinition R I (D.A P.1) (D.B P.2))
          (D.bothRefinedChart a b hZ c).J CTPF) := by
    have hglob : FormalSpectrum.globalSectionsMap
        (CompletedTensorProduct.idealOfDefinition R I (D.A P.1) (D.B P.2))
        (D.bothRefinedChart a b hZ c).J CTPF =
        CompletedTensorProduct.lift (D.bothRefinedChart a b hZ c).J
          (D.refinedAlgebra_hIL a b hZ c (hs c)) (D.xAlg a b hZ c) (D.yAlg a b hZ c hcomm) := by
      rw [hCTPF, CompletedTensorProduct.fibreLift,
        FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap]
    rw [hglob]
    exact CompletedTensorProduct.lift_le_comap (D.refinedAlgebra_hIL a b hZ c (hs c))
      (D.xAlg a b hZ c) (D.yAlg a b hZ c hcomm) hI
  -- Descend along the explicit basic-open cover of the overlap `V = overlapFormalScheme`.
  refine (@FormalScheme.liftedBasicCover (D.bothRefinedChart a b hZ c).R _ _
    (D.bothRefinedChart a b hZ c).J _ V pf hpfOI
    (D.bothRefinedChart a b hZ c).fg).hom_ext _ _ (fun v => ?_)
  -- The per-piece chart `w` and its basic-open parameter `gv`, obtained once (`J` explicit to avoid
  -- the `Spf`-object-defeq wall on `pf`'s target).
  set lbc := @FormalScheme.liftedBasicChart (D.bothRefinedChart a b hZ c).R _ _
    (D.bothRefinedChart a b hZ c).J _ _ pf hpfOI (D.bothRefinedChart a b hZ c).fg v with hlbc
  set gv := lbc.g with hgv
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal (D.bothRefinedChart a b hZ c).J gv) :=
    AdicCompletion.isAdicRing_map _ ((D.bothRefinedChart a b hZ c).fg.map _)
  set w := LocallyRingedSpace.IsOpenImmersion.lift pf
    (FormalSpectrum.basicOpenChart (D.bothRefinedChart a b hZ c).J gv) lbc.hsub with hw
  change w ≫ (pf ≫ D.fibreLiftPiece a b hZ hcomm hs c) =
    w ≫ (ps ≫ D.fibreLiftPiece a b hZ hcomm hs c')
  have hwpf : w ≫ pf = FormalSpectrum.basicOpenChart (D.bothRefinedChart a b hZ c).J gv :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac pf
      (FormalSpectrum.basicOpenChart (D.bothRefinedChart a b hZ c).J gv) lbc.hsub
  have hLfg : (FormalSpectrum.awayCompletionIdeal (D.bothRefinedChart a b hZ c).J gv).FG := by
    rw [← FormalSpectrum.map_awayCompletionHom (D.bothRefinedChart a b hZ c).J gv]
    exact (D.bothRefinedChart a b hZ c).fg.map _
  refine D.hom_eq_of_chart_factor (Z := V) hV hf ht
    (pf ≫ D.fibreLiftPiece a b hZ hcomm hs c) (ps ≫ D.fibreLiftPiece a b hZ hcomm hs c')
    hpr₁ hpr₂ hLfg w P (w ≫ pf ≫ CTPF) ?_ ?_
  · -- hfac: `(w ≫ pf ≫ CTPF) ≫ ι P = w ≫ (pf ≫ k c)`.
    rw [Category.assoc, Category.assoc]
    exact congrArg (fun t => w ≫ pf ≫ t) hk.symm
  · -- hcont: `w ≫ pf = basicOpenChart`, adic on sections by 460a composed with `hφ`.
    have hfac_eq : w ≫ pf ≫ CTPF =
        FormalSpectrum.basicOpenChart (D.bothRefinedChart a b hZ c).J gv ≫ CTPF := by
      rw [← Category.assoc, hwpf]
    have key := FormalSpectrum.le_comap_globalSectionsMap_basicOpenChart_comp
      (CompletedTensorProduct.idealOfDefinition R I (D.A P.1) (D.B P.2))
      (D.bothRefinedChart a b hZ c).J gv CTPF hφ
    rw [← hfac_eq] at key
    exact key

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
