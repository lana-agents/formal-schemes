import FormalSchemes.GeneralFibreProductLiftPiece
import FormalSchemes.GlueOpenCoverFactorBothAlg
import FormalSchemes.LiftedBasicOpenCover
import FormalSchemes.OpenCoverGlueMorphisms

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The general fibre-product mediating morphism over an *explicit* refined chart family

The general `fibreLift` (issue 234c, deleted in issue 805) refined the
source cover of `Z` using the internally-chosen refined charts `bothRefinedChart a b hZ`, obtained
by `Classical.choice` from `nonempty_bothRefinedChart`. That choice is opaque: the chosen chart's
`BothRefinedChart` fields carry no adic-over-base bound, and `Classical.choice` erases which witness
was picked (issue 487). Consequently the general diagonal's continuity witness `hs` — asking each
refined-cover piece to be adic on global sections over the base — is *unreachable* for the plain
`bothRefinedChart` (issues 468/472/487; the "open immersion is adic on sections" statement is false,
issue 460).

This file removes the dependence on `Classical.choice` by re-deriving the entire mediating-morphism
tower over an **arbitrary user-supplied chart family** `charts : ∀ z, BothRefinedChart D a b z`.
Every construction and lemma mirrors its merged counterpart verbatim with `bothRefinedChart a b hZ`
replaced by `charts` (and the `hZ : Z.LocallyFG` hypothesis dropped — the charts *are* the local
finite generation). The chart-generic ingredients (`chartLift`, `hom_eq_of_chart_factor`,
`overlapFormalScheme`, `liftedBasicCover`) are reused unchanged.

Feeding an adic-carrying chart family (built from `exists_affineChart_subset_adicOverBase` +
`adicOverBase_xStructMap`, `AdicOverBaseChart.lean`/`BothDatumAdicOverBase.lean`, issue 487) then
discharges `hs` from the chart's retained adic bound, yielding the **unconditional** general
diagonal `diagonal'` (`GeneralDiagonalUnconditional.lean`) — the input to EGA I §10.15 general
separatedness.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
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
variable (charts : ∀ z : Z, BothRefinedChart D a b z)

/-- The common refinement of the source cover of `Z` built from an **explicit** chart family
`charts`, indexed by the points of `Z`. Mirrors `bothRefinedCover`, dropping the `LocallyFG`
hypothesis. -/
def bothRefinedCoverOf : FormalScheme.OpenCover Z where
  J := Z
  obj z := FormalScheme.Spf (charts z).J
  map z := FormalScheme.Hom.mk (charts z).map
  f z := z
  covers z := (charts z).mem
  isOpenImmersion z := (charts z).isOpenImmersion

/-- The `X`-chart index selected by `charts` for each cover piece. -/
def xIndexOf (c : (D.bothRefinedCoverOf a b charts).J) : D.JX := (charts c).xIdx

/-- The `Y`-chart index selected by `charts` for each cover piece. -/
def yIndexOf (c : (D.bothRefinedCoverOf a b charts).J) : D.JY := (charts c).yIdx

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The range of `map c ≫ a` on a piece of `bothRefinedCoverOf` lies in the range of the selected
`X`-chart. Mirrors `bothRefinedChart_range_comp_xsubset`. -/
theorem chart_range_comp_xsubsetOf (c : (D.bothRefinedCoverOf a b charts).J) :
    Set.range ((charts c).map ≫ a).base ⊆
      Set.range (D.xFormalGlueData.ι (D.xIndexOf a b charts c)).base := by
  rintro w ⟨s, rfl⟩
  simp only [LocallyRingedSpace.comp_base, TopCat.comp_app]
  exact (charts c).xsubset ⟨s, rfl⟩

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The range of `map c ≫ b` on a piece of `bothRefinedCoverOf` lies in the range of the selected
`Y`-chart. Mirrors `bothRefinedChart_range_comp_ysubset`. -/
theorem chart_range_comp_ysubsetOf (c : (D.bothRefinedCoverOf a b charts).J) :
    Set.range ((charts c).map ≫ b).base ⊆
      Set.range (D.yFormalGlueData.ι (D.yIndexOf a b charts c)).base := by
  rintro w ⟨s, rfl⟩
  simp only [LocallyRingedSpace.comp_base, TopCat.comp_app]
  exact (charts c).ysubset ⟨s, rfl⟩

/-- The `X`-side chart-wise factorization of `map c ≫ a` through the selected `X`-chart. Mirrors
`xFactor`. -/
def xFactorOf (c : (D.bothRefinedCoverOf a b charts).J) :
    FormalSpectrum.locallyRingedSpaceObj (charts c).J ⟶
      D.xFormalGlueData.toLocallyRingedSpaceGlueData.U (D.xIndexOf a b charts c) :=
  LocallyRingedSpace.IsOpenImmersion.lift (D.xFormalGlueData.ι (D.xIndexOf a b charts c))
    ((charts c).map ≫ a) (D.chart_range_comp_xsubsetOf a b charts c)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `xFactorOf c ≫ ι (xIndexOf c)` recovers `map c ≫ a`. Mirrors `xFactor_comp_ι`. -/
@[reassoc]
theorem xFactorOf_comp_ι (c : (D.bothRefinedCoverOf a b charts).J) :
    D.xFactorOf a b charts c ≫ D.xFormalGlueData.ι (D.xIndexOf a b charts c) =
      (charts c).map ≫ a :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- The `Y`-side chart-wise factorization of `map c ≫ b` through the selected `Y`-chart. Mirrors
`yFactor`. -/
def yFactorOf (c : (D.bothRefinedCoverOf a b charts).J) :
    FormalSpectrum.locallyRingedSpaceObj (charts c).J ⟶
      D.yFormalGlueData.toLocallyRingedSpaceGlueData.U (D.yIndexOf a b charts c) :=
  LocallyRingedSpace.IsOpenImmersion.lift (D.yFormalGlueData.ι (D.yIndexOf a b charts c))
    ((charts c).map ≫ b) (D.chart_range_comp_ysubsetOf a b charts c)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `yFactorOf c ≫ ι (yIndexOf c)` recovers `map c ≫ b`. Mirrors `yFactor_comp_ι`. -/
@[reassoc]
theorem yFactorOf_comp_ι (c : (D.bothRefinedCoverOf a b charts).J) :
    D.yFactorOf a b charts c ≫ D.yFormalGlueData.ι (D.yIndexOf a b charts c) =
      (charts c).map ≫ b :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- The structure ring hom `σ_c : R →+* S_c` of a piece of `bothRefinedCoverOf`. Mirrors
`refinedStructHom`. -/
def refinedStructHomOf (c : Z) :
    R →+* (charts c).R :=
  globalSectionsMap I (charts c).J ((charts c).map ≫ a ≫ D.xStructMap)

/-- The `R`-algebra structure on `S_c` induced by `refinedStructHomOf`. Mirrors `refinedAlgebra`. -/
@[reducible]
def refinedAlgebraOf (c : Z) :
    Algebra R (charts c).R :=
  (D.refinedStructHomOf a b charts c).toAlgebra

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The `X`-leg factorization pushed to the base. Mirrors `map_comp_a_xStructMap_eq`. -/
theorem map_comp_a_xStructMap_eqOf (c : Z) :
    letI := D.commRingA; letI := D.algebraA
    (charts c).map ≫ a ≫ D.xStructMap =
      D.xFactorOf a b charts c ≫ D.xStructMapChart (D.xIndexOf a b charts c) := by
  letI := D.commRingA; letI := D.algebraA
  rw [← D.ι_xStructMap (D.xIndexOf a b charts c), D.xFactorOf_comp_ι_assoc a b charts c]
  exact (Category.assoc _ _ _).symm

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The `Y`-leg factorization pushed to the base. Mirrors `map_comp_b_yStructMap_eq`. -/
theorem map_comp_b_yStructMap_eqOf (c : Z) :
    letI := D.commRingB; letI := D.algebraB
    (charts c).map ≫ b ≫ D.yStructMap =
      D.yFactorOf a b charts c ≫ D.yStructMapChart (D.yIndexOf a b charts c) := by
  letI := D.commRingB; letI := D.algebraB
  rw [← D.ι_yStructMap (D.yIndexOf a b charts c), D.yFactorOf_comp_ι_assoc a b charts c]
  exact (Category.assoc _ _ _).symm

/-- The `X`-side per-piece `R`-algebra map `xAlgOf c : A_i →ₐ[R] S_c`. Mirrors `xAlg`. -/
def xAlgOf (c : Z) :
    letI := D.commRingA; letI := D.algebraA; letI := D.refinedAlgebraOf a b charts c
    D.A (D.xIndexOf a b charts c) →ₐ[R] (charts c).R := by
  letI := D.commRingA; letI := D.algebraA; letI := D.topologyA; letI := D.isAdicA
  letI := D.refinedAlgebraOf a b charts c
  let φ : D.A (D.xIndexOf a b charts c) →+* (charts c).R :=
    globalSectionsMap (I.map (algebraMap R (D.A (D.xIndexOf a b charts c))))
      (charts c).J (D.xFactorOf a b charts c)
  refine { φ with commutes' := ?_ }
  intro r
  have hcomp : φ.comp (algebraMap R (D.A (D.xIndexOf a b charts c))) =
        globalSectionsMap I (charts c).J
          ((charts c).map ≫ a ≫ D.xStructMap) := by
    rw [show φ = _ from rfl, ← D.globalSectionsMap_xStructMapChart (D.xIndexOf a b charts c),
      ← globalSectionsMap_comp]
    exact congrArg (globalSectionsMap I (charts c).J)
      (D.map_comp_a_xStructMap_eqOf a b charts c).symm
  exact RingHom.congr_fun
    (hcomp.trans (RingHom.algebraMap_toAlgebra (D.refinedStructHomOf a b charts c)).symm) r

/-- The `Y`-side per-piece `R`-algebra map `yAlgOf c : B_j →ₐ[R] S_c`. Mirrors `yAlg`. -/
def yAlgOf (c : Z)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap) :
    letI := D.commRingB; letI := D.algebraB; letI := D.refinedAlgebraOf a b charts c
    D.B (D.yIndexOf a b charts c) →ₐ[R] (charts c).R := by
  letI := D.commRingB; letI := D.algebraB; letI := D.topologyB; letI := D.isAdicB
  letI := D.refinedAlgebraOf a b charts c
  let φ : D.B (D.yIndexOf a b charts c) →+* (charts c).R :=
    globalSectionsMap (I.map (algebraMap R (D.B (D.yIndexOf a b charts c))))
      (charts c).J (D.yFactorOf a b charts c)
  refine { φ with commutes' := ?_ }
  intro r
  have hcomp : φ.comp (algebraMap R (D.B (D.yIndexOf a b charts c))) =
        globalSectionsMap I (charts c).J
          ((charts c).map ≫ a ≫ D.xStructMap) := by
    rw [show φ = _ from rfl, ← D.globalSectionsMap_yStructMapChart (D.yIndexOf a b charts c),
      ← globalSectionsMap_comp]
    refine congrArg (globalSectionsMap I (charts c).J)
      ((D.map_comp_b_yStructMap_eqOf a b charts c).symm.trans ?_)
    rw [hcomm]
  exact RingHom.congr_fun
    (hcomp.trans (RingHom.algebraMap_toAlgebra (D.refinedStructHomOf a b charts c)).symm) r

/-- The `chartLift` precondition `hIL` from the continuity witness `hs`. Mirrors
`refinedAlgebra_hIL`. -/
theorem refinedAlgebra_hILOf (c : Z)
    (hs : I ≤ (charts c).J.comap (D.refinedStructHomOf a b charts c)) :
    letI := D.refinedAlgebraOf a b charts c
    I.map (algebraMap R (charts c).R) ≤ (charts c).J := by
  letI := D.refinedAlgebraOf a b charts c
  rw [show (algebraMap R (charts c).R) = D.refinedStructHomOf a b charts c from
    RingHom.algebraMap_toAlgebra _]
  exact Ideal.map_le_iff_le_comap.mpr hs

/-- The per-piece mediating morphism `k c : Spf S_c ⟶ X ×_{Spf R} Y`. Mirrors `fibreLiftPiece`. -/
def fibreLiftPieceOf
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (charts c).J.comap (D.refinedStructHomOf a b charts c))
    (c : (D.bothRefinedCoverOf a b charts).J) :
    ((D.bothRefinedCoverOf a b charts).obj c).toLocallyRingedSpace ⟶
      D.generalFibreProduct.toLocallyRingedSpace :=
  letI := D.refinedAlgebraOf a b charts c
  D.chartLift (D.xIndexOf a b charts c, D.yIndexOf a b charts c)
    (D.refinedAlgebra_hILOf a b charts c (hs c)) (D.xAlgOf a b charts c)
    (D.yAlgOf a b charts c hcomm)

/-- The per-piece morphism recovers `map ≫ a` after `pr₁`. Mirrors `fibreLiftPiece_comp_pr₁`. -/
theorem fibreLiftPieceOf_comp_pr₁
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (charts c).J.comap (D.refinedStructHomOf a b charts c))
    (c : (D.bothRefinedCoverOf a b charts).J) :
    D.fibreLiftPieceOf a b charts hcomm hs c ≫ D.pr₁ hV hf ht =
      (charts c).map ≫ a := by
  letI := D.commRingA; letI := D.algebraA; letI := D.topologyA; letI := D.isAdicA
  letI := D.refinedAlgebraOf a b charts c
  have h1 := D.chartLift_comp_pr₁ (D.xIndexOf a b charts c, D.yIndexOf a b charts c)
    (D.refinedAlgebra_hILOf a b charts c (hs c)) (D.xAlgOf a b charts c)
    (D.yAlgOf a b charts c hcomm) hV hf ht
  have hrt : FormalSpectrum.locallyRingedSpaceMap
      (I.map (algebraMap R (D.A (D.xIndexOf a b charts c)))) (charts c).J
      (D.xAlgOf a b charts c).toRingHom
      (CompletedTensorProduct.algHom_le_comap (D.xAlgOf a b charts c)
        (D.refinedAlgebra_hILOf a b charts c (hs c))) = D.xFactorOf a b charts c :=
    locallyRingedSpaceMap_globalSectionsMap (I.map (algebraMap R (D.A (D.xIndexOf a b charts c))))
      (charts c).J (hI.map (algebraMap R (D.A (D.xIndexOf a b charts c))))
      (charts c).fg (D.xFactorOf a b charts c) _
  exact h1.trans ((congrArg (· ≫ D.xFormalGlueData.ι (D.xIndexOf a b charts c)) hrt).trans
    (D.xFactorOf_comp_ι a b charts c))

/-- The per-piece morphism recovers `map ≫ b` after `pr₂`. Mirrors `fibreLiftPiece_comp_pr₂`. -/
theorem fibreLiftPieceOf_comp_pr₂
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (charts c).J.comap (D.refinedStructHomOf a b charts c))
    (c : (D.bothRefinedCoverOf a b charts).J) :
    D.fibreLiftPieceOf a b charts hcomm hs c ≫ D.pr₂ hV hf ht =
      (charts c).map ≫ b := by
  letI := D.commRingB; letI := D.algebraB; letI := D.topologyB; letI := D.isAdicB
  letI := D.refinedAlgebraOf a b charts c
  have h1 := D.chartLift_comp_pr₂ (D.xIndexOf a b charts c, D.yIndexOf a b charts c)
    (D.refinedAlgebra_hILOf a b charts c (hs c)) (D.xAlgOf a b charts c)
    (D.yAlgOf a b charts c hcomm) hV hf ht
  have hrt : FormalSpectrum.locallyRingedSpaceMap
      (I.map (algebraMap R (D.B (D.yIndexOf a b charts c)))) (charts c).J
      (D.yAlgOf a b charts c hcomm).toRingHom
      (CompletedTensorProduct.algHom_le_comap (D.yAlgOf a b charts c hcomm)
        (D.refinedAlgebra_hILOf a b charts c (hs c))) = D.yFactorOf a b charts c :=
    locallyRingedSpaceMap_globalSectionsMap (I.map (algebraMap R (D.B (D.yIndexOf a b charts c))))
      (charts c).J (hI.map (algebraMap R (D.B (D.yIndexOf a b charts c))))
      (charts c).fg (D.yFactorOf a b charts c) _
  exact h1.trans ((congrArg (· ≫ D.yFormalGlueData.ι (D.yIndexOf a b charts c)) hrt).trans
    (D.yFactorOf_comp_ι a b charts c))

set_option backward.isDefEq.respectTransparency false in
/-- The overlap obligation for gluing the per-piece morphisms. Mirrors `fibreLift_overlap`. -/
theorem fibreLift_overlapOf
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (charts c).J.comap (D.refinedStructHomOf a b charts c))
    (c c' : (D.bothRefinedCoverOf a b charts).J) :
    pullback.fst ((D.bothRefinedCoverOf a b charts).cmap c)
          ((D.bothRefinedCoverOf a b charts).cmap c') ≫
        D.fibreLiftPieceOf a b charts hcomm hs c =
      pullback.snd ((D.bothRefinedCoverOf a b charts).cmap c)
          ((D.bothRefinedCoverOf a b charts).cmap c') ≫
        D.fibreLiftPieceOf a b charts hcomm hs c' := by
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  letI := D.refinedAlgebraOf a b charts c
  have hchart : ((D.bothRefinedCoverOf a b charts).obj c).LocallyFG :=
    FormalScheme.locallyFG_Spf (charts c).fg
  set V := (D.bothRefinedCoverOf a b charts).overlapFormalScheme c c' hchart with hVdef
  set pf := pullback.fst ((D.bothRefinedCoverOf a b charts).cmap c)
    ((D.bothRefinedCoverOf a b charts).cmap c') with hpf
  set ps := pullback.snd ((D.bothRefinedCoverOf a b charts).cmap c)
    ((D.bothRefinedCoverOf a b charts).cmap c') with hps
  haveI hpfOI : LocallyRingedSpace.IsOpenImmersion pf :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      (pullback.fst ((D.bothRefinedCoverOf a b charts).cmap c)
        ((D.bothRefinedCoverOf a b charts).cmap c')))
  have hpr₁ : (pf ≫ D.fibreLiftPieceOf a b charts hcomm hs c) ≫ D.pr₁ hV hf ht =
      (ps ≫ D.fibreLiftPieceOf a b charts hcomm hs c') ≫ D.pr₁ hV hf ht := by
    have hcond : pf ≫ (charts c).map = ps ≫ (charts c').map := pullback.condition
    rw [Category.assoc, Category.assoc, D.fibreLiftPieceOf_comp_pr₁ a b charts hV hf ht hcomm hs c,
      D.fibreLiftPieceOf_comp_pr₁ a b charts hV hf ht hcomm hs c']
    exact (reassoc_of% hcond) a
  have hpr₂ : (pf ≫ D.fibreLiftPieceOf a b charts hcomm hs c) ≫ D.pr₂ hV hf ht =
      (ps ≫ D.fibreLiftPieceOf a b charts hcomm hs c') ≫ D.pr₂ hV hf ht := by
    have hcond : pf ≫ (charts c).map = ps ≫ (charts c').map := pullback.condition
    rw [Category.assoc, Category.assoc, D.fibreLiftPieceOf_comp_pr₂ a b charts hV hf ht hcomm hs c,
      D.fibreLiftPieceOf_comp_pr₂ a b charts hV hf ht hcomm hs c']
    exact (reassoc_of% hcond) b
  set P : D.formalGlueData.toLocallyRingedSpaceGlueData.J :=
    (D.xIndexOf a b charts c, D.yIndexOf a b charts c) with hP
  set CTPF := CompletedTensorProduct.fibreLift (D.refinedAlgebra_hILOf a b charts c (hs c))
    (D.xAlgOf a b charts c) (D.yAlgOf a b charts c hcomm) hI with hCTPF
  have hk : D.fibreLiftPieceOf a b charts hcomm hs c = CTPF ≫ D.formalGlueData.ι P := rfl
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (D.A P.1) (D.B P.2)) :=
    CompletedTensorProduct.isAdicRing R I (D.A P.1) (D.B P.2) hI
  have hφ : CompletedTensorProduct.idealOfDefinition R I (D.A P.1) (D.B P.2) ≤
      (charts c).J.comap
        (FormalSpectrum.globalSectionsMap
          (CompletedTensorProduct.idealOfDefinition R I (D.A P.1) (D.B P.2))
          (charts c).J CTPF) := by
    have hglob : FormalSpectrum.globalSectionsMap
        (CompletedTensorProduct.idealOfDefinition R I (D.A P.1) (D.B P.2))
        (charts c).J CTPF =
        CompletedTensorProduct.lift (charts c).J
          (D.refinedAlgebra_hILOf a b charts c (hs c)) (D.xAlgOf a b charts c)
          (D.yAlgOf a b charts c hcomm) := by
      rw [hCTPF, CompletedTensorProduct.fibreLift,
        FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap]
    rw [hglob]
    exact CompletedTensorProduct.lift_le_comap (D.refinedAlgebra_hILOf a b charts c (hs c))
      (D.xAlgOf a b charts c) (D.yAlgOf a b charts c hcomm) hI
  refine (@FormalScheme.liftedBasicCover (charts c).R _ _
    (charts c).J _ V pf hpfOI (charts c).fg).hom_ext _ _ (fun v => ?_)
  set lbc := @FormalScheme.liftedBasicChart (charts c).R _ _
    (charts c).J _ _ pf hpfOI (charts c).fg v with hlbc
  set gv := lbc.g with hgv
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal (charts c).J gv) :=
    AdicCompletion.isAdicRing_map _ ((charts c).fg.map _)
  set w := LocallyRingedSpace.IsOpenImmersion.lift pf
    (FormalSpectrum.basicOpenChart (charts c).J gv) lbc.hsub with hw
  change w ≫ (pf ≫ D.fibreLiftPieceOf a b charts hcomm hs c) =
    w ≫ (ps ≫ D.fibreLiftPieceOf a b charts hcomm hs c')
  have hwpf : w ≫ pf = FormalSpectrum.basicOpenChart (charts c).J gv :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac pf
      (FormalSpectrum.basicOpenChart (charts c).J gv) lbc.hsub
  have hLfg : (FormalSpectrum.awayCompletionIdeal (charts c).J gv).FG := by
    rw [← FormalSpectrum.map_awayCompletionHom (charts c).J gv]
    exact (charts c).fg.map _
  refine D.hom_eq_of_chart_factor (Z := V) hV hf ht
    (pf ≫ D.fibreLiftPieceOf a b charts hcomm hs c)
    (ps ≫ D.fibreLiftPieceOf a b charts hcomm hs c')
    hpr₁ hpr₂ hLfg w P (w ≫ pf ≫ CTPF) ?_ ?_
  · rw [Category.assoc, Category.assoc]
    exact congrArg (fun t => w ≫ pf ≫ t) hk.symm
  · have hfac_eq : w ≫ pf ≫ CTPF =
        FormalSpectrum.basicOpenChart (charts c).J gv ≫ CTPF := by
      rw [← Category.assoc, hwpf]
    have key := FormalSpectrum.le_comap_globalSectionsMap_basicOpenChart_comp
      (CompletedTensorProduct.idealOfDefinition R I (D.A P.1) (D.B P.2))
      (charts c).J gv CTPF hφ
    rw [← hfac_eq] at key
    exact key

/-- The general fibre-product mediating morphism over the explicit chart family `charts`. Mirrors
`fibreLift`. -/
def fibreLiftOf
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (charts c).J.comap (D.refinedStructHomOf a b charts c)) :
    Z.toLocallyRingedSpace ⟶ D.generalFibreProduct.toLocallyRingedSpace :=
  (D.bothRefinedCoverOf a b charts).glueMorphisms
    (fun c => D.fibreLiftPieceOf a b charts hcomm hs c)
    (D.fibreLift_overlapOf a b charts hV hf ht hcomm hs)

/-- `fibreLiftOf` recovers `a` after the first projection. Mirrors `fibreLift_comp_pr₁`. -/
theorem fibreLiftOf_comp_pr₁
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (charts c).J.comap (D.refinedStructHomOf a b charts c)) :
    D.fibreLiftOf a b charts hV hf ht hcomm hs ≫ D.pr₁ hV hf ht = a := by
  refine (D.bothRefinedCoverOf a b charts).hom_ext _ _ (fun c => ?_)
  rw [fibreLiftOf, ← Category.assoc, (D.bothRefinedCoverOf a b charts).map_glueMorphisms _ _ c]
  exact D.fibreLiftPieceOf_comp_pr₁ a b charts hV hf ht hcomm hs c

/-- `fibreLiftOf` recovers `b` after the second projection. Mirrors `fibreLift_comp_pr₂`. -/
theorem fibreLiftOf_comp_pr₂
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap)
    (hs : ∀ c, I ≤ (charts c).J.comap (D.refinedStructHomOf a b charts c)) :
    D.fibreLiftOf a b charts hV hf ht hcomm hs ≫ D.pr₂ hV hf ht = b := by
  refine (D.bothRefinedCoverOf a b charts).hom_ext _ _ (fun c => ?_)
  rw [fibreLiftOf, ← Category.assoc, (D.bothRefinedCoverOf a b charts).map_glueMorphisms _ _ c]
  exact D.fibreLiftPieceOf_comp_pr₂ a b charts hV hf ht hcomm hs c

end BothChartedFibreDatumXY

end AlgebraicGeometry

end
