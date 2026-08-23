import FormalSchemes.ClosedImmersionIso
import FormalSchemes.GeneralSeparatedTopological
import FormalSchemes.TateDiagonalClosedImmersion
import FormalSchemes.TateFibreProductIso

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The Tate curve model is separated over `Spf R` (EGA I §10.15)

Brick 4c of issue 601, and the last step of the Tate separatedness goal. #243
(`tateSelfProductDiagonal_isClosedImmersion`) proved that the **glued** Tate diagonal
`Δ : 𝔈_q ⟶ 𝔈_q ×_{Spf R} 𝔈_q` is a closed immersion, but as a bare conjunction about a morphism of
locally ringed spaces, over the hand-built four-chart self fibre product. §10.15's vocabulary
(`FormalSchemes/GeneralSeparated.lean`) instead asks that the datum-level `schemeDiagonal'` be a
closed immersion of *formal schemes*. This file converts one into the other, using the two
comparison isomorphisms of bricks 4a and 4b:

* `tateXGluedIso` (704) — the datum's glued object is `𝔈_q`;
* `tateFibreProductIso` (740) — the datum's `generalFibreProduct` is `tateSelfProductInv`.

## The two steps

`tate_schemeDiagonal'_eq` identifies the general diagonal with the conjugate of the glued one:

```
schemeDiagonal' = (tateXGluedIso).hom ≫ tateSchemeDiagonal ≫ (tateFibreProductIso).inv
```

Both sides are morphisms **into** `generalFibreProduct` and both are sections of `pr₁` and of
`pr₂`, so `fibreLift_unique_adicOverBase` (518) identifies them; its adic hypothesis is
`adicOverBase_xStructMap`, datum-generic. This is `AffineSeparatedValue.lean:135`'s
`oneChart_schemeDiagonal'_eq` with the two isomorphisms changed, and the three side goals really are
datum-generic, exactly as issue 706 predicted.

`tate_isSeparated` then transports #243 across the two isomorphisms with
`FormalScheme.IsClosedImmersion.iso_comp` / `.comp_iso`. **No stalk is computed**: the stalk half of
the closed-immersion predicate is free from the split-mono argument of 549, which is already how
`tateSelfProductDiagonal_surjective_stalkMap` is obtained.

## Main results

* `AlgebraicGeometry.tateSchemeDiagonal`: the glued Tate diagonal as a morphism of formal schemes,
  with `tateSchemeDiagonal_isClosedImmersion` (#243 repackaged).
* `AlgebraicGeometry.tate_schemeDiagonal'_eq`: the diagonal identification.
* `AlgebraicGeometry.tate_isSeparated`: **`𝔈_q` is separated over `Spf R`**, with no hypotheses
  beyond `hq : q ∈ I`, `hI : I.FG` and the ambient instances.

## No remaining hypothesis (issue 798)

`tate_isSeparated` used to carry `hs : TateFibreLiftContinuity`, travelling in from
`tateFibreProductHom` (#274) through `tateFibreProductIso` (#283) — the per-refined-chart adic
bound that `BothChartedFibreDatumXY.fibreLift` requires of *every* source, and which is
**unreachable** for the cover `fibreLift` chooses internally (issues 460/468/472/487). It is gone.
`Φ` is now built from `fibreLiftAdic` (794), whose only input is `AdicOverBaseLocallyFG` of the
source; #276's `tateSelfProductInv_adicOverBase` supplies that, and it implies `LocallyFG` too, so
the separate `tate_isSeparated_of_fibreLiftContinuity` that discharged only the `LocallyFG` half is
no longer meaningful and has been removed.

## Implementation notes

The `xGlued` spelling wall of 704/#274 is in force throughout: `(tateDiagonalDatum …).xGlued` and
`(tateCurveExposeXDatum …).xFormalGlueData.gluedFormalScheme` are definitionally but not
syntactically equal, and `ofFactors` is semireducible, so goals mentioning both are not type-correct
at `instances` transparency and `rw` cannot build a motive across them. Concretely, `rw
[Category.assoc]` on the two projection side goals fails with "Did not find an occurrence of the
pattern" and the real cause (`uliftBool_not_pairwise_distinct` at `(tateCurveExposeXDatum …).J`
versus `ULift Bool`) appears only in the `Full error:` tail. The remedy is 704's: pin each side goal
as its own top-level lemma (`tateConjugatedDiagonal_comp_pr₁` / `_comp_pr₂`) and assemble in term
mode with type-ascribed `congrArg` lambdas.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
variable (B : Type u) [CommRing B] [Algebra R B]

/-- The glued Tate diagonal, as a morphism of formal schemes. -/
def tateSchemeDiagonal (hq : q ∈ I) (hI : I.FG) :
    tateCurveModel R I q hq hI ⟶ tateSelfProductInv R I q hq hI :=
  FormalScheme.Hom.mk (tateSelfProductDiagonal R I q hq hI)

/-- Its underlying locally-ringed-space morphism is the glued diagonal. -/
theorem tateSchemeDiagonal_toLRSHom (hq : q ∈ I) (hI : I.FG) :
    (tateSchemeDiagonal R I q hq hI).toLRSHom = tateSelfProductDiagonal R I q hq hI := rfl

/-- **The glued Tate diagonal is a closed immersion of formal schemes** — #243, repackaged. -/
theorem tateSchemeDiagonal_isClosedImmersion (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.IsClosedImmersion (tateSchemeDiagonal R I q hq hI) where
  base_closedEmbedding := isClosedEmbedding_tateSelfProductDiagonal_base R I q hq hI
  surjective_stalkMap := tateSelfProductDiagonal_surjective_stalkMap R I q hq hI


/-- The underlying locally-ringed-space morphism of the conjugated diagonal. -/
theorem tateConjugatedDiagonal_toLRSHom (hq : q ∈ I) (hI : I.FG) :
    ((tateXGluedIso R I q B hq hI).hom ≫ tateSchemeDiagonal R I q hq hI ≫
        (tateFibreProductIso R I q B hq hI).inv).toLRSHom =
      tateXGluedHom R I q B hq hI ≫ tateSelfProductDiagonal R I q hq hI ≫
        tateFibreProductHom R I q B hq hI := by
  rw [FormalScheme.comp_toLRSHom, FormalScheme.comp_toLRSHom, tateSchemeDiagonal_toLRSHom,
    show (tateXGluedIso R I q B hq hI).hom.toLRSHom = tateXGluedHom R I q B hq hI from
      forgetToLocallyRingedSpace_map_tateXGluedIso_hom R I q B hq hI,
    show (tateFibreProductIso R I q B hq hI).inv.toLRSHom =
        tateFibreProductHom R I q B hq hI from
      forgetToLocallyRingedSpace_map_tateFibreProductIso_inv R I q B hq hI]
  rfl

/-- The conjugated diagonal is a section of the first projection. -/
theorem tateConjugatedDiagonal_comp_pr₁ (hq : q ∈ I) (hI : I.FG) :
    (tateXGluedHom R I q B hq hI ≫ tateSelfProductDiagonal R I q hq hI ≫
        tateFibreProductHom R I q B hq hI) ≫
      (tateDiagonalDatum R I q B hq hI).pr₁
        (BothChartedFibreDatumXY.ofFactors_hV _ _ _ _ _ _ _ _)
        (BothChartedFibreDatumXY.ofFactors_hf _ _ _ _ _ _ _ _)
        (BothChartedFibreDatumXY.ofFactors_ht _ _ _ _ _ _ _ _) = 𝟙 _ :=
  have hinner : tateSelfProductDiagonal R I q hq hI ≫
      tateFibreProductHom R I q B hq hI ≫
        (tateDiagonalDatum R I q B hq hI).pr₁ _ _ _ = tateXGluedInv R I q B hq hI :=
    (congrArg (fun m : (tateSelfProductInv R I q hq hI).toLocallyRingedSpace ⟶
        (tateDiagonalDatum R I q B hq hI).xGlued.toLocallyRingedSpace =>
          tateSelfProductDiagonal R I q hq hI ≫ m)
      (tateFibreProductHom_comp_pr₁ R I q B hq hI)).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (fun m : (tateCurveModel R I q hq hI).toLocallyRingedSpace ⟶
            (tateCurveModel R I q hq hI).toLocallyRingedSpace =>
              m ≫ tateXGluedInv R I q B hq hI)
          (tateSelfProductDiagonal_comp_pr₁ R I q hq hI)).trans (Category.id_comp _)
  (Category.assoc _ _ _).trans <|
    (congrArg (fun m : (tateCurveModel R I q hq hI).toLocallyRingedSpace ⟶
        (tateDiagonalDatum R I q B hq hI).xGlued.toLocallyRingedSpace =>
          tateXGluedHom R I q B hq hI ≫ m)
      ((Category.assoc _ _ _).trans hinner)).trans
      (tateXGluedIsoLRS R I q B hq hI).hom_inv_id

/-- The conjugated diagonal is a section of the second projection. -/
theorem tateConjugatedDiagonal_comp_pr₂ (hq : q ∈ I) (hI : I.FG) :
    (tateXGluedHom R I q B hq hI ≫ tateSelfProductDiagonal R I q hq hI ≫
        tateFibreProductHom R I q B hq hI) ≫
      (tateDiagonalDatum R I q B hq hI).pr₂
        (BothChartedFibreDatumXY.ofFactors_hV _ _ _ _ _ _ _ _)
        (BothChartedFibreDatumXY.ofFactors_hf _ _ _ _ _ _ _ _)
        (BothChartedFibreDatumXY.ofFactors_ht _ _ _ _ _ _ _ _) = 𝟙 _ :=
  have hinner : tateSelfProductDiagonal R I q hq hI ≫
      tateFibreProductHom R I q B hq hI ≫
        (tateDiagonalDatum R I q B hq hI).pr₂ _ _ _ = tateXGluedInv R I q B hq hI :=
    (congrArg (fun m : (tateSelfProductInv R I q hq hI).toLocallyRingedSpace ⟶
        (tateDiagonalDatum R I q B hq hI).yGlued.toLocallyRingedSpace =>
          tateSelfProductDiagonal R I q hq hI ≫ m)
      (tateFibreProductHom_comp_pr₂ R I q B hq hI)).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (fun m : (tateCurveModel R I q hq hI).toLocallyRingedSpace ⟶
            (tateCurveModel R I q hq hI).toLocallyRingedSpace =>
              m ≫ tateXGluedInv R I q B hq hI)
          (tateSelfProductDiagonal_comp_pr₂ R I q hq hI)).trans (Category.id_comp _)
  (Category.assoc _ _ _).trans <|
    (congrArg (fun m : (tateCurveModel R I q hq hI).toLocallyRingedSpace ⟶
        (tateDiagonalDatum R I q B hq hI).xGlued.toLocallyRingedSpace =>
          tateXGluedHom R I q B hq hI ≫ m)
      ((Category.assoc _ _ _).trans hinner)).trans
      (tateXGluedIsoLRS R I q B hq hI).hom_inv_id

/-- **The general diagonal of the Tate datum is the glued Tate diagonal**, conjugated by 704's and
740's comparison isomorphisms. -/
theorem tate_schemeDiagonal'_eq (hq : q ∈ I) (hI : I.FG) :
    BothChartedFibreDatumXY.schemeDiagonal' (tateCurveExposeXDatum R I q B hq hI)
        (fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim)
        (fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim)
        (fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim) =
      (tateXGluedIso R I q B hq hI).hom ≫ tateSchemeDiagonal R I q hq hI ≫
        (tateFibreProductIso R I q B hq hI).inv := by
  apply FormalScheme.Hom.ext'
  refine (tateDiagonalDatum R I q B hq hI).fibreLift_unique_adicOverBase
    (BothChartedFibreDatumXY.ofFactors_hV _ _ _ _ _ _ _ _)
    (BothChartedFibreDatumXY.ofFactors_hf _ _ _ _ _ _ _ _)
    (BothChartedFibreDatumXY.ofFactors_ht _ _ _ _ _ _ _ _)
    _ _ (tateDiagonalDatum R I q B hq hI).xStructMap
    (BothChartedFibreDatumXY.adicOverBase_xStructMap _) ?_ ?_ ?_
  · exact (BothChartedFibreDatumXY.diagonal'_comp_pr₁ _ _ _ _).trans
      ((congrArg (fun m : (tateDiagonalDatum R I q B hq hI).xGlued.toLocallyRingedSpace ⟶
            (tateDiagonalDatum R I q B hq hI).generalFibreProduct.toLocallyRingedSpace =>
          m ≫ (tateDiagonalDatum R I q B hq hI).pr₁ _ _ _)
        (tateConjugatedDiagonal_toLRSHom R I q B hq hI)).trans
        (tateConjugatedDiagonal_comp_pr₁ R I q B hq hI)).symm
  · exact (BothChartedFibreDatumXY.diagonal'_comp_pr₂ _ _ _ _).trans
      ((congrArg (fun m : (tateDiagonalDatum R I q B hq hI).xGlued.toLocallyRingedSpace ⟶
            (tateDiagonalDatum R I q B hq hI).generalFibreProduct.toLocallyRingedSpace =>
          m ≫ (tateDiagonalDatum R I q B hq hI).pr₂ _ _ _)
        (tateConjugatedDiagonal_toLRSHom R I q B hq hI)).trans
        (tateConjugatedDiagonal_comp_pr₂ R I q B hq hI)).symm
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m : (tateDiagonalDatum R I q B hq hI).xGlued.toLocallyRingedSpace ⟶
            (tateDiagonalDatum R I q B hq hI).xGlued.toLocallyRingedSpace =>
          m ≫ (tateDiagonalDatum R I q B hq hI).xStructMap)
        (BothChartedFibreDatumXY.diagonal'_comp_pr₁ _ _ _ _)).trans (Category.id_comp _))


/-! ### Separatedness -/

/-- **The Tate curve model `𝔈_q` is separated over `Spf R`** (EGA I §10.15), in the §10.15
vocabulary: the scheme-level general diagonal of the datum presenting `𝔈_q` is a closed immersion
of formal schemes. -/
theorem tate_isSeparated (hq : q ∈ I) (hI : I.FG) :
    BothChartedFibreDatumXY.IsSeparated (tateCurveExposeXDatum R I q B hq hI)
      (fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim)
      (fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim)
      (fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim) := by
  change FormalScheme.IsClosedImmersion (BothChartedFibreDatumXY.schemeDiagonal' _ _ _ _)
  rw [tate_schemeDiagonal'_eq R I q B hq hI]
  exact FormalScheme.IsClosedImmersion.iso_comp _
    ((tateSchemeDiagonal_isClosedImmersion R I q hq hI).comp_iso _)


end AlgebraicGeometry

end
