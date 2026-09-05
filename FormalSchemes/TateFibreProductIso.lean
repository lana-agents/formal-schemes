import FormalSchemes.GeneralSeparatedChartCodiagonal
import FormalSchemes.TateFibreOverlapTransition
import FormalSchemes.TateFibreProductHom
import FormalSchemes.TateSelfProductAdicOverBase

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# `𝔈_q ×_{Spf R} 𝔈_q`: the generic fibre product is the hand-built four-chart object

Brick 4b of issue 601 (issue 705c) needs the Tate curve model's self fibre product in **two**
presentations to be identified: the hand-built four-chart object `tateSelfProductInv`, over which
#241's diagonal closed-embedding analysis lives, and the `generalFibreProduct` of the diagonal
datum of `tateCurveExposeXDatum`, in whose vocabulary §10.15's `schemeDiagonal'` is phrased.

`FormalSchemes/TateFibreProductHom.lean` (#274) supplied **`Φ`**, the direction that needs no
glue-datum comparison: the fibre-product mediating morphism of the two legs
`pr₁ ≫ tateXGluedInv`, `pr₂ ≫ tateXGluedInv`, with its two projection laws free from
`fibreLift_comp_pr₁` / `_comp_pr₂`. This file supplies **`Ψ`**, the reverse direction, and the
isomorphism.

## `Ψ`, and the combinator it is built from

`Ψ` glues the four Tate glue inclusions over the four product charts. The overlap obligation is
exactly the `V`, `f` and `t` layers of the comparison that 705c's three earlier bricks provide:
`tateOverlapCompareIso` and `tateOverlapCompareIso_hom_fac` (#277) and
`tateOverlapCompareIso_hom_t` (771/#280), together with the Tate glue datum's own glue relation
`tateSelfProduct_glue_raw_inv` below.

The gluing itself is packaged once and for all as `BothChartedFibreDatumXY.glueOut`: **a morphism
out of `X ×_{Spf R} Y` is a family of chart morphisms agreeing on the overlaps in the raw
`bothAlgData` vocabulary.** This is the map-out companion of `pr₁` / `pr₂` and is stated for an
arbitrary datum, which is not a stylistic choice — see the implementation notes.

## `Φ` on the charts, and both round trips

The crux of the file is `ι_tateFibreProductHom`: **`Φ` carries the `c`-th Tate chart to the
product chart `(c.1, c.2)`.** Both sides are morphisms out of the affine `Spf(A ⊗̂_R A)` into the
general fibre product, and they have the same two projections, so `fibreLift_unique_adicOverBase`
(issue 518) identifies them; its `AdicOverBaseLocallyFG` hypothesis is
`FormalScheme.adicOverBaseLocallyFG_Spf` (`FormalSchemes.AdicOverBaseChart`, issue 778), for which
an affine source needs only its identity chart, and the base morphism is `#276`'s per-chart
structural morphism.

With that one lemma **both** round trips are `GlueData.hom_ext` and three rewrites each — no
uniqueness argument is needed for either, because `Ψ` and `Φ` are now both known chartwise.

## Main results

* `AlgebraicGeometry.BothChartedFibreDatumXY.glueOut`, `ι_glueOut`: mapping out of the general
  fibre product from a compatible family of chart morphisms.
* `AlgebraicGeometry.tateSelfProduct_glue_raw_inv`: the four-chart Tate glue relation at an
  arbitrary pair of indices.
* `AlgebraicGeometry.tateFibreProductPsi`, `ι_tateFibreProductPsi`: **`Ψ`**.
* `AlgebraicGeometry.ι_tateFibreProductHom`: **`Φ` on the Tate charts** — the crux.
* `AlgebraicGeometry.tateFibreProductIso`: **the comparison isomorphism**, with
  `tateFibreProductIso_inv_comp_pr₁` / `_comp_pr₂` and the two `ι` characterisations.

## Implementation notes

Three walls, all of them the same one seen from different sides: `generalFibreProduct`,
`formalGlueData`, `ofFactors` and `xGlued` are semireducible, so a term mixing the datum's spelling
with the unfolded one is definitionally correct but **not type-correct at `instances`
transparency**, and `rw` cannot build a motive across it.

1. **Do the gluing at a variable datum.** Unfolding `formalGlueData` at the *Tate* datum to expose
   the `GlueData'.f'` dispatch does not terminate: the first attempt at `tateFibreProductPsi`
   spent 9.5 minutes and died in `simp`'s `whnf` and then in `abstract nested proofs`, at
   `maxHeartbeats 3200000`. The identical proof with the datum a variable (`glueOut`) elaborates in
   13 s, and instantiating afterwards is substitution rather than conversion. This is #277's rule
   — *generalise the constant to a variable before the equation, never after* — applied a third
   time, and the first time to a **definition** rather than to a lemma or a proof.
2. **Same for a spelled-out chart index.** `pr₁Chart_comp_ι_tateXGluedInv` is stated over a
   variable `b : tateModelIdx …`; at `⟨c.down.1⟩` the statement is not type-correct at `instances`
   transparency, `rw` fails with "Did not find an occurrence of the pattern", and the real cause is
   only in the `Full error:` tail.
3. **Everything that crosses the wall is term mode** (`congrArg` / `Category.assoc` / `Eq.trans`,
   with the `congrArg` lambda type-ascribed), as `TateFibreProductHom.lean` and
   `TateSelfProductAdicOverBase.lean` already do.

**The isomorphism is unconditional** (issue 798). `Φ` used to carry the general `fibreLift`
hypotheses `hZ : LocallyFG` and `hs` (abbreviated `TateFibreLiftContinuity`) and propagate them
through every declaration here. `Φ` is now built from `fibreLiftAdic` (794) on #276's
`tateSelfProductInv_adicOverBase` witness, which discharges both, so nothing below has a hypothesis
beyond `hq` and `hI`.

`ι_tateFibreProductHom` — the one lemma here with real content — did not change: its proof is
`fibreLift_unique_adicOverBase` (518) fed the two projection laws and the base compatibility, and
all three exist verbatim in the `Adic` spelling. Only the now-inlined `hleg` moved, to
`tateFibreLegX_comp_xStructMap` in `TateFibreProductHom.lean`, where `fibreLiftAdic`'s `hbase`
needs it anyway.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace FormalSpectrum

variable {S : Type u} [CommRing S] [TopologicalSpace S]

/-- **`Spf` of the identity along an equality of ideals of definition is the transport.** -/
theorem locallyRingedSpaceMap_id_eq_eqToHom {K L : Ideal S} [IsAdicRing K] [IsAdicRing L]
    (h : K = L) (hc : L ≤ K.comap (RingHom.id S)) :
    locallyRingedSpaceMap L K (RingHom.id S) hc = eqToHom (by subst h; rfl) := by
  subst h
  rw [locallyRingedSpaceMap_id]
  simp

end FormalSpectrum

namespace AlgebraicGeometry

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable (D : BothChartedFibreDatumXY R I hI)

/-- Mapping out of the general fibre product from a compatible family of chart maps. -/
def glueOut
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    {Y : LocallyRingedSpace.{u}}
    (k : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p : D.JX × D.JY,
        locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2)) ⟶
          Y)
    (hk : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        bothAlgDataF hI D.gX D.gY p p' h ≫ k p =
          bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
            bothAlgDataF hI D.gX D.gY p' p h.symm ≫ k p') :
    D.toBothChartedFibreDatum.generalFibreProduct.toLocallyRingedSpace ⟶ Y :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  D.formalGlueData.glueMorphisms k (by
    intro p p'
    by_cases hpp : p = p'
    · subst hpp
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · obtain ⟨i, j⟩ := p
      obtain ⟨i', j'⟩ := p'
      have hpp' : ((i, j) : D.JX × D.JY) ≠ (i', j') := hpp
      have hp'p : ((i', j') : D.JX × D.JY) ≠ (i, j) := fun heq => hpp heq.symm
      simp only [BothChartedFibreDatum.formalGlueData, BothChartedFibreDatum.lrsGlueData,
        BothChartedFibreDatum.glueData', CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hpp', dif_neg hp'p, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [hf (i, j) (i', j') hpp', ht (i, j) (i', j') hpp', hf (i', j') (i, j) hp'p]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      congr 1
      exact hk (i, j) (i', j') hpp')

/-- `glueOut` restricts to `k p` along each glue inclusion. -/
theorem ι_glueOut
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    {Y : LocallyRingedSpace.{u}}
    (k : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p : D.JX × D.JY,
        locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2)) ⟶
          Y)
    (hk : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        bothAlgDataF hI D.gX D.gY p p' h ≫ k p =
          bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
            bothAlgDataF hI D.gX D.gY p' p h.symm ≫ k p')
    (p : D.JX × D.JY) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    D.formalGlueData.ι p ≫ D.glueOut hV hf ht k hk = k p :=
  D.formalGlueData.ι_glueMorphisms _ _ p

end BothChartedFibreDatumXY

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
variable (B : Type u) [CommRing B] [Algebra R B]

/-! ### The Tate-side glue relation -/

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- The glue relation of the four-chart Tate self-fibre product, at an arbitrary pair. -/
theorem tateSelfProduct_glue_raw_inv (hq : q ∈ I) (hI : I.FG) {i j : Bool × Bool} (h : i ≠ j) :
    tateSelfProductGlueF R I q hI i j h ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨i⟩ =
      tateSelfProductGlueTInv R I q hI i j h ≫
        tateSelfProductGlueF R I q hI j i h.symm ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨j⟩ := by
  have hij : ({ down := i } : ULift.{u} (Bool × Bool)) ≠ ⟨j⟩ := fun e => h (congrArg ULift.down e)
  have hji : ({ down := j } : ULift.{u} (Bool × Bool)) ≠ ⟨i⟩ :=
    fun e => h (congrArg ULift.down e).symm
  have key := (tateSelfProductLRSGlueDataInv R I q hq hI).toGlueData.glue_condition ⟨i⟩ ⟨j⟩
  simp only [tateSelfProductLRSGlueDataInv, tateSelfProductGlueData'Inv,
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
    dif_neg hij, dif_neg hji, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  rw [cancel_epi] at key
  exact key.symm

/-! ### The overlap obligation -/

/-- The overlap obligation of `Ψ`, at the level of the raw algebra data. -/
theorem tatePsi_overlap (hq : q ∈ I) (hI : I.FG)
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') :
    bothAlgDataF (A := tateFibreA R I q) (B := tateFibreA R I q) hI
          (tateFibreG R I q) (tateFibreG R I q) p p' h ≫
        (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨tateFibreIdx p⟩ =
      bothAlgDataT (A := tateFibreA R I q) (B := tateFibreA R I q) hI
          (tateFibreG R I q) (tateFibreG R I q)
          (fun _ _ _ => annulusFibreOverlapTransitionAlg R I q hq hI)
          (fun _ _ _ => annulusFibreOverlapTransitionAlg R I q hq hI) p p' h ≫
        bothAlgDataF (A := tateFibreA R I q) (B := tateFibreA R I q) hI
            (tateFibreG R I q) (tateFibreG R I q) p' p h.symm ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨tateFibreIdx p'⟩ := by
  rw [← tateOverlapCompareIso_hom_fac R I q hq hI p p' h,
    ← tateOverlapCompareIso_hom_fac R I q hq hI p' p h.symm, Category.assoc,
    tateSelfProduct_glue_raw_inv R I q hq hI (tateFibreIdx_ne h),
    ← Category.assoc, ← Category.assoc, tateOverlapCompareIso_hom_t R I q hq hI p p' h]
  simp only [Category.assoc]

/-! ### The comparison morphism -/

/-- **`Ψ`**: the comparison morphism from the generic fibre product to the hand-built one. -/
def tateFibreProductPsi (hq : q ∈ I) (hI : I.FG) :
    (tateDiagonalDatum R I q B hq hI).generalFibreProduct.toLocallyRingedSpace ⟶
      (tateSelfProductInv R I q hq hI).toLocallyRingedSpace :=
  (tateDiagonalDatum R I q B hq hI).glueOut
    (BothChartedFibreDatumXY.ofFactors_hV _ _ _ _ _ _ _ _)
    (BothChartedFibreDatumXY.ofFactors_hf _ _ _ _ _ _ _ _)
    (BothChartedFibreDatumXY.ofFactors_ht _ _ _ _ _ _ _ _)
    (fun p => (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨tateFibreIdx p⟩)
    (tatePsi_overlap R I q hq hI)

/-- `Ψ` restricted to the `p`-th product chart is the Tate glue inclusion at `tateFibreIdx p`. -/
theorem ι_tateFibreProductPsi (hq : q ∈ I) (hI : I.FG)
    (p : ULift.{u} Bool × ULift.{u} Bool) :
    (tateDiagonalDatum R I q B hq hI).formalGlueData.ι p ≫ tateFibreProductPsi R I q B hq hI =
      (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨tateFibreIdx p⟩ :=
  (tateDiagonalDatum R I q B hq hI).ι_glueOut _ _ _ _ _ p


/-! ### The base ideal-convention bridge is the chart comparison -/

/-- The base ideal-convention bridge is 704's chart comparison isomorphism. -/
theorem annulusBaseBridge_eq (hI : I.FG) :
    annulusBaseBridge R I q = (tateChartCompIso R I q).hom := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_map_eq R I q ▸ annulus_isAdicRing R I q hI
  rw [annulusBaseBridge, tateChartCompIso, eqToIso.hom,
    FormalSpectrum.locallyRingedSpaceMap_id_eq_eqToHom (annulus_map_eq R I q)]

/-- The base bridge cancels the chart comparison of 704. -/
theorem annulusBaseBridge_comp_tateChartCompUInv (hq : q ∈ I) (hI : I.FG)
    (i : tateModelIdx R I q hq hI) :
    annulusBaseBridge R I q ≫ tateChartCompUInv B i = 𝟙 _ := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_map_eq R I q ▸ annulus_isAdicRing R I q hI
  rw [annulusBaseBridge_eq R I q hI, tateChartCompUInv]
  exact (tateChartCompIso R I q).hom_inv_id


/-! ### The two legs of `Φ`, chartwise -/

/-- The first affine projection into the model chart, carried by 704's comparison, is the raw
`Spf(inl)` into the datum's chart. Stated over a **variable** model index: at a spelled-out index
the statement is not type-correct at `instances` transparency and `rw` cannot build a motive. -/
theorem pr₁Chart_comp_ι_tateXGluedInv (hq : q ∈ I) (hI : I.FG) (b : tateModelIdx R I q hq hI) :
    pr₁Chart R I q (annulusAlgebra R I q) ≫
        (tateCurveFormalGlueData R I q hq hI).ι b ≫ tateXGluedInv R I q B hq hI =
      pr₁ChartSelf R I q ≫
        (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.ι (tateModelIdxToX B b) := by
  have hbridge : pr₁Chart R I q (annulusAlgebra R I q) ≫ tateChartCompUInv B b =
      pr₁ChartSelf R I q :=
    (congrArg (· ≫ tateChartCompUInv B b) (pr₁Chart_eq R I q)).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (pr₁ChartSelf R I q ≫ ·)
          (annulusBaseBridge_comp_tateChartCompUInv R I q B hq hI b)).trans (Category.comp_id _)
  exact (congrArg (fun g : locallyRingedSpaceObj (annulusIdealOfDefinition R I q) ⟶
      ((tateCurveExposeXDatum R I q B hq
        hI).xFormalGlueData.gluedFormalScheme).toLocallyRingedSpace =>
        pr₁Chart R I q (annulusAlgebra R I q) ≫ g)
    (ι_tateXGluedInv R I q B hq hI b)).trans <|
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.ι
        (tateModelIdxToX B b)) hbridge)

/-- The second-projection companion of `pr₁Chart_comp_ι_tateXGluedInv`. -/
theorem pr₂Chart_comp_ι_tateXGluedInv (hq : q ∈ I) (hI : I.FG) (b : tateModelIdx R I q hq hI) :
    pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫
        annulusBaseBridge R I q ≫
          (tateCurveFormalGlueData R I q hq hI).ι b ≫ tateXGluedInv R I q B hq hI =
      pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫
        (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.ι (tateModelIdxToX B b) := by
  exact congrArg (fun g : locallyRingedSpaceObj
      (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q)) ⟶
      ((tateCurveExposeXDatum R I q B hq
        hI).xFormalGlueData.gluedFormalScheme).toLocallyRingedSpace => g)
    (((congrArg (pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ ·)
        ((congrArg (annulusBaseBridge R I q ≫ ·)
            (ι_tateXGluedInv R I q B hq hI b)).trans <|
          (Category.assoc _ _ _).symm.trans <|
            congrArg (· ≫ (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.ι
              (tateModelIdxToX B b))
              (annulusBaseBridge_comp_tateChartCompUInv R I q B hq hI b))).trans <|
      congrArg (pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ ·)
        (Category.id_comp _)))

/-- The `X`-leg of `Φ` restricted to the `c`-th Tate chart. -/
theorem ι_tateFibreLegX (hq : q ∈ I) (hI : I.FG) (c : ULift.{u} (Bool × Bool)) :
    (tateSelfProductFormalGlueDataInv R I q hq hI).ι c ≫ tateFibreLegX R I q B hq hI =
      pr₁ChartSelf R I q ≫
        (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.ι ⟨c.down.1⟩ := by
  have h1 : (tateSelfProductFormalGlueDataInv R I q hq hI).ι c ≫ tateSelfProductPr₁ R I q hq hI =
      pr₁Chart R I q (annulusAlgebra R I q) ≫
        (tateCurveFormalGlueData R I q hq hI).ι ⟨c.down.1⟩ := by
    rw [tateSelfProductPr₁]
    exact (tateSelfProductFormalGlueDataInv R I q hq hI).ι_glueMorphisms _ _ c
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ tateXGluedInv R I q B hq hI) h1).trans <|
      (Category.assoc _ _ _).trans
        (pr₁Chart_comp_ι_tateXGluedInv R I q B hq hI ⟨c.down.1⟩)

/-- The `Y`-leg of `Φ` restricted to the `c`-th Tate chart. -/
theorem ι_tateFibreLegY (hq : q ∈ I) (hI : I.FG) (c : ULift.{u} (Bool × Bool)) :
    (tateSelfProductFormalGlueDataInv R I q hq hI).ι c ≫ tateFibreLegY R I q B hq hI =
      pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫
        (tateCurveExposeXDatum R I q B hq hI).xFormalGlueData.ι ⟨c.down.2⟩ := by
  have h1 : (tateSelfProductFormalGlueDataInv R I q hq hI).ι c ≫ tateSelfProductPr₂ R I q hq hI =
      pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ annulusBaseBridge R I q ≫
        (tateCurveFormalGlueData R I q hq hI).ι ⟨c.down.2⟩ := by
    rw [tateSelfProductPr₂]
    exact (tateSelfProductFormalGlueDataInv R I q hq hI).ι_glueMorphisms _ _ c
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ tateXGluedInv R I q B hq hI) h1).trans <|
      (Category.assoc _ _ _).trans
        ((congrArg (pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≫ ·)
          (Category.assoc _ _ _)).trans
          (pr₂Chart_comp_ι_tateXGluedInv R I q B hq hI ⟨c.down.2⟩))


/-! ### `Φ` on the Tate charts -/

/-- Abbreviation for the product index attached to a Tate chart index. -/
abbrev tateProdIdx (c : ULift.{u} (Bool × Bool)) : ULift.{u} Bool × ULift.{u} Bool :=
  (⟨c.down.1⟩, ⟨c.down.2⟩)

/-- **`Φ` carries the `c`-th Tate chart to the corresponding product chart.** Both sides are
morphisms out of the affine `Spf(A ⊗̂_R A)` into the general fibre product with the same two
projections, so `fibreLift_unique_adicOverBase` identifies them. -/
theorem ι_tateFibreProductHom (hq : q ∈ I) (hI : I.FG)
    (c : ULift.{u} (Bool × Bool)) :
    (tateSelfProductFormalGlueDataInv R I q hq hI).ι c ≫ tateFibreProductHom R I q B hq hI =
      (tateDiagonalDatum R I q B hq hI).formalGlueData.ι (tateProdIdx c) := by
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
  refine BothChartedFibreDatumXY.fibreLift_unique_adicOverBase (tateDiagonalDatum R I q B hq hI)
    (BothChartedFibreDatumXY.ofFactors_hV _ _ _ _ _ _ _ _)
    (BothChartedFibreDatumXY.ofFactors_hf _ _ _ _ _ _ _ _)
    (BothChartedFibreDatumXY.ofFactors_ht _ _ _ _ _ _ _ _)
    (Z := FormalScheme.Spf (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)))
    _ _ (locallyRingedSpaceMap I (CompletedTensorProduct.idealOfDefinition R I
      (annulusAlgebra R I q) (annulusAlgebra R I q))
      (algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q)))
      CompletedTensorProduct.algebraMap_isAdicHom.le_comap)
    (FormalScheme.adicOverBaseLocallyFG_Spf
      (tensorIdealOfDefinition_fg R I q (annulusAlgebra R I q) hI) _ ?_) ?_ ?_ ?_
  · rw [globalSectionsMap_locallyRingedSpaceMap]
    exact CompletedTensorProduct.algebraMap_isAdicHom.le_comap
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (fun g : (tateSelfProductInv R I q hq hI).toLocallyRingedSpace ⟶
          (tateDiagonalDatum R I q B hq hI).xGlued.toLocallyRingedSpace =>
            (tateSelfProductFormalGlueDataInv R I q hq hI).ι c ≫ g)
        (tateFibreProductHom_comp_pr₁ R I q B hq hI)).trans <|
        (ι_tateFibreLegX R I q B hq hI c).trans
          ((tateDiagonalDatum R I q B hq hI).ι_pr₁ _ _ _ (tateProdIdx c)).symm
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (fun g : (tateSelfProductInv R I q hq hI).toLocallyRingedSpace ⟶
          (tateDiagonalDatum R I q B hq hI).yGlued.toLocallyRingedSpace =>
            (tateSelfProductFormalGlueDataInv R I q hq hI).ι c ≫ g)
        (tateFibreProductHom_comp_pr₂ R I q B hq hI)).trans <|
        (ι_tateFibreLegY R I q B hq hI c).trans
          ((tateDiagonalDatum R I q B hq hI).ι_pr₂ _ _ _ (tateProdIdx c)).symm
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (fun g : (tateSelfProductInv R I q hq hI).toLocallyRingedSpace ⟶
          locallyRingedSpaceObj I =>
            (tateSelfProductFormalGlueDataInv R I q hq hI).ι c ≫ g)
        ((Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ (tateDiagonalDatum R I q B hq hI).xStructMap)
            (tateFibreProductHom_comp_pr₁ R I q B hq hI)).trans
            (tateFibreLegX_comp_xStructMap R I q B hq hI))).trans <|
      (ι_tateSelfProductStructMap R I q hq hI c).trans
        (pr₁Chart_comp_annulusStructMap R I q (annulusAlgebra R I q) hI)


/-! ### The two round trips -/

/-- `Ψ ≫ Φ = 𝟙` on the general fibre product. -/
theorem tateFibreProductPsi_comp_hom (hq : q ∈ I) (hI : I.FG) :
    tateFibreProductPsi R I q B hq hI ≫ tateFibreProductHom R I q B hq hI = 𝟙 _ := by
  refine FormalScheme.GlueData.hom_ext _ fun p => ?_
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ tateFibreProductHom R I q B hq hI)
      (ι_tateFibreProductPsi R I q B hq hI p)).trans <|
      (ι_tateFibreProductHom R I q B hq hI ⟨tateFibreIdx p⟩).trans
        (Category.comp_id _).symm

/-- `Φ ≫ Ψ = 𝟙` on the hand-built self fibre product. -/
theorem tateFibreProductHom_comp_psi (hq : q ∈ I) (hI : I.FG) :
    tateFibreProductHom R I q B hq hI ≫ tateFibreProductPsi R I q B hq hI = 𝟙 _ := by
  refine FormalScheme.GlueData.hom_ext _ fun c => ?_
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ tateFibreProductPsi R I q B hq hI)
      (ι_tateFibreProductHom R I q B hq hI c)).trans <|
      (ι_tateFibreProductPsi R I q B hq hI (tateProdIdx c)).trans (Category.comp_id _).symm


/-! ### The comparison isomorphism -/

/-- **The two presentations of `𝔈_q ×_{Spf R} 𝔈_q` agree**, as locally ringed spaces. -/
def tateFibreProductIsoLRS (hq : q ∈ I) (hI : I.FG) :
    (tateDiagonalDatum R I q B hq hI).generalFibreProduct.toLocallyRingedSpace ≅
      (tateSelfProductInv R I q hq hI).toLocallyRingedSpace where
  hom := tateFibreProductPsi R I q B hq hI
  inv := tateFibreProductHom R I q B hq hI
  hom_inv_id := tateFibreProductPsi_comp_hom R I q B hq hI
  inv_hom_id := tateFibreProductHom_comp_psi R I q B hq hI

/-- **The Tate diagonal datum's general fibre product is the hand-built four-chart self fibre
product** — the headline of brick 4b (issue 705c). -/
def tateFibreProductIso (hq : q ∈ I) (hI : I.FG) :
    (tateDiagonalDatum R I q B hq hI).generalFibreProduct ≅ tateSelfProductInv R I q hq hI :=
  (Functor.FullyFaithful.ofFullyFaithful
    FormalScheme.forgetToLocallyRingedSpace).preimageIso
      (tateFibreProductIsoLRS R I q B hq hI)

/-- The underlying morphism of the comparison isomorphism is `Ψ`. -/
theorem forgetToLocallyRingedSpace_map_tateFibreProductIso_hom (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.forgetToLocallyRingedSpace.map (tateFibreProductIso R I q B hq hI).hom =
      tateFibreProductPsi R I q B hq hI :=
  (Functor.FullyFaithful.ofFullyFaithful
    FormalScheme.forgetToLocallyRingedSpace).map_preimage _

/-- The underlying morphism of the inverse comparison isomorphism is `Φ`. -/
theorem forgetToLocallyRingedSpace_map_tateFibreProductIso_inv (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.forgetToLocallyRingedSpace.map (tateFibreProductIso R I q B hq hI).inv =
      tateFibreProductHom R I q B hq hI :=
  (Functor.FullyFaithful.ofFullyFaithful
    FormalScheme.forgetToLocallyRingedSpace).map_preimage _


/-! ### The characterisations brick 4c consumes -/

/-- **The comparison isomorphism recovers the first projection.** With
`tateFibreProductIso_inv_comp_pr₂` this is the shape 706 consumes: the generic `pr₁` of the
diagonal datum, read through the comparison, is the hand-built `tateSelfProductPr₁` followed by
704's model comparison. -/
theorem tateFibreProductIso_inv_comp_pr₁ (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.forgetToLocallyRingedSpace.map (tateFibreProductIso R I q B hq hI).inv ≫
        (tateDiagonalDatum R I q B hq hI).pr₁
          (BothChartedFibreDatumXY.ofFactors_hV _ _ _ _ _ _ _ _)
          (BothChartedFibreDatumXY.ofFactors_hf _ _ _ _ _ _ _ _)
          (BothChartedFibreDatumXY.ofFactors_ht _ _ _ _ _ _ _ _) =
      tateFibreLegX R I q B hq hI := by
  rw [forgetToLocallyRingedSpace_map_tateFibreProductIso_inv]
  exact tateFibreProductHom_comp_pr₁ R I q B hq hI

/-- **The comparison isomorphism recovers the second projection.** -/
theorem tateFibreProductIso_inv_comp_pr₂ (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.forgetToLocallyRingedSpace.map (tateFibreProductIso R I q B hq hI).inv ≫
        (tateDiagonalDatum R I q B hq hI).pr₂
          (BothChartedFibreDatumXY.ofFactors_hV _ _ _ _ _ _ _ _)
          (BothChartedFibreDatumXY.ofFactors_hf _ _ _ _ _ _ _ _)
          (BothChartedFibreDatumXY.ofFactors_ht _ _ _ _ _ _ _ _) =
      tateFibreLegY R I q B hq hI := by
  rw [forgetToLocallyRingedSpace_map_tateFibreProductIso_inv]
  exact tateFibreProductHom_comp_pr₂ R I q B hq hI

/-- **The comparison isomorphism on the `p`-th product chart.** -/
theorem ι_tateFibreProductIso_hom (hq : q ∈ I) (hI : I.FG)
    (p : ULift.{u} Bool × ULift.{u} Bool) :
    (tateDiagonalDatum R I q B hq hI).formalGlueData.ι p ≫
        FormalScheme.forgetToLocallyRingedSpace.map
          (tateFibreProductIso R I q B hq hI).hom =
      (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨tateFibreIdx p⟩ := by
  rw [forgetToLocallyRingedSpace_map_tateFibreProductIso_hom]
  exact ι_tateFibreProductPsi R I q B hq hI p

/-- **The inverse comparison isomorphism on the `c`-th Tate chart.** -/
theorem ι_tateFibreProductIso_inv (hq : q ∈ I) (hI : I.FG)
    (c : ULift.{u} (Bool × Bool)) :
    (tateSelfProductFormalGlueDataInv R I q hq hI).ι c ≫
        FormalScheme.forgetToLocallyRingedSpace.map
          (tateFibreProductIso R I q B hq hI).inv =
      (tateDiagonalDatum R I q B hq hI).formalGlueData.ι (tateProdIdx c) := by
  rw [forgetToLocallyRingedSpace_map_tateFibreProductIso_inv]
  exact ι_tateFibreProductHom R I q B hq hI c

end AlgebraicGeometry

end
