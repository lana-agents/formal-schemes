import FormalSchemes.GeneralDiagonal
import FormalSchemes.TateSelfProductCone
import FormalSchemes.TateXGluedIso

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The comparison morphism `𝔈_q ×_{Spf R} 𝔈_q ⟶ (Tate diagonal datum).generalFibreProduct`

Brick 4 of issue 601 needs the Tate curve model's self fibre product in *two* presentations to be
identified: the hand-built four-chart object `tateSelfProductInv` (over which #241's diagonal
closed-embedding analysis lives) and the generic `generalFibreProduct` of the diagonal datum of
`tateCurveExposeXDatum` (in whose vocabulary §10.15's `schemeDiagonal'` is phrased). This file
supplies **one half** of that identification, the half that needs no glue-datum comparison at all:
the morphism from the hand-built object to the generic one, together with its two projection
compatibilities.

The construction is the general fibre-product mediating morphism `fibreLift`, fed the two legs

```
pr₁ ≫ tateXGluedInv ,  pr₂ ≫ tateXGluedInv  :  𝔈_q ×_{Spf R} 𝔈_q ⟶ (datum).xGlued
```

so the projection laws come out of `fibreLift_comp_pr₁` / `_comp_pr₂` rather than having to be
proved. `FormalSchemes/GeneralDiagonal.lean` is the same construction for the pair of identities
`(𝟙, 𝟙)`; this file is that file with the legs changed.

The reverse morphism — the one that genuinely needs the overlap comparison of 738/739/751 and the
transition law — is not here.

## The one new geometric input

`fibreLift`'s cone hypothesis `hcomm` is `tateSelfProduct_cone_comm` **once the comparison
isomorphism of 704 is known to be a morphism over `Spf R`**, which 704 did not record: it ships
`tateXGluedIso` and its `ι` characterisations but never relates either to a structural morphism.
`tateXGluedInv_comp_xStructMap` below supplies that, by `GlueData.hom_ext` over the model's two
charts, reducing to the ideal-convention transport `eqToHom_comp_locallyRingedSpaceMap`.

## Implementation notes: the `xGlued` spelling wall

`tateXGluedInv`'s codomain is spelled `(tateCurveExposeXDatum …).xFormalGlueData.gluedFormalScheme`
while the diagonal datum's is `(tateDiagonalDatum …).xGlued`. The two are definitionally equal, but
**only after unfolding `xGlued` and `ofFactors`, which are semireducible**, so a composite mixing
them is not type-correct at `instances` transparency and `rw` refuses to build a motive across it
(`Application type mismatch … LocallyRingedSpace.instQuiver` versus
`LocallyRingedSpace.instCategory.toQuiver`). This is 704's wall, and the remedy is 704's:

* restate the structural compatibility once in **each** spelling
  (`tateXGluedInv_comp_xStructMap` and `tateXGluedInv_comp_tateDiagonalDatum_xStructMap`, the
  second proved by `exact` on the first — the elaborator checks that at default transparency,
  where it is free);
* then keep the assembly in **pure term mode** (`congrArg` / `Category.assoc` / `Eq.trans`), never
  `rw`. `tateSelfProduct_cone_comm` itself is written this way for the same reason.

Do not try to bridge the two spellings with `rw [show … from rfl]`: the rewrite succeeds, leaves
the goal type-incorrect at `instances` transparency, and the *next* rewrite fails with a message
that points at the wrong lemma.

## Main definitions and results

* `AlgebraicGeometry.tateXGluedInv_comp_xStructMap`: 704's comparison isomorphism is a morphism
  over `Spf R`.
* `AlgebraicGeometry.tateDiagonalDatum`: the Tate curve model's diagonal datum (the double-overlap
  data are vacuous on a two-element index type).
* `AlgebraicGeometry.tateFibreLegX`, `tateFibreLegY`: the two legs, and `tateFibreLeg_cone_comm`.
* `AlgebraicGeometry.tateFibreProductHom`: the comparison morphism, with
  `tateFibreProductHom_comp_pr₁` and `tateFibreProductHom_comp_pr₂`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R]

/-- **A structural morphism transports along an equality of ideals of definition.** Stated
generically in the two ideals, so `subst` discharges it and no concrete completion is ever
unfolded. -/
theorem eqToHom_comp_locallyRingedSpaceMap {S : Type u} [CommRing S] {I : Ideal R} {K L : Ideal S}
    (h : K = L) (φ : R →+* S) (hK : I ≤ K.comap φ) (hL : I ≤ L.comap φ) :
    eqToHom (congrArg locallyRingedSpaceObj h).symm ≫ locallyRingedSpaceMap I K φ hK =
      locallyRingedSpaceMap I L φ hL := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

end FormalSpectrum

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
variable (B : Type u) [CommRing B] [Algebra R B]

/-! ### 704's comparison isomorphism is a morphism over `Spf R` -/

/-- **The chart comparison is over `Spf R`**: the datum's chart `Spf(I·A)` and the model's chart
`Spf A` differ only by the ideal convention (`annulus_map_eq`), and both structural morphisms are
`Spf` of the same algebra map `R → A`. -/
theorem tateChartCompUInv_comp_xStructMapChart (hq : q ∈ I) (hI : I.FG)
    (i : tateModelIdx R I q hq hI) :
    tateChartCompUInv B i ≫
        (tateCurveExposeXDatum R I q B hq hI).xStructMapChart (tateModelIdxToX B i) =
      annulusStructMap R I q hI := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  rw [tateChartCompUInv, tateChartCompIso, eqToIso.inv,
    AffineChartedFibreDatumX.xStructMapChart, annulusStructMap,
    IsTopologicallyFiniteType.structMap]
  exact FormalSpectrum.eqToHom_comp_locallyRingedSpaceMap (annulus_map_eq R I q) _ _ _

/-- **704's comparison isomorphism is a morphism over `Spf R`.** The inverse comparison
`tateXGluedInv : 𝔈_q ⟶ (datum).xGlued`, followed by the datum's glued structural morphism, is the
model's structural morphism. 704 shipped the isomorphism and its `ι` characterisations but never
related it to a structural morphism; this is the missing compatibility, and it is what makes
`fibreLift`'s cone hypothesis below reduce to `tateSelfProduct_cone_comm`. -/
theorem tateXGluedInv_comp_xStructMap (hq : q ∈ I) (hI : I.FG) :
    tateXGluedInv R I q B hq hI ≫ (tateCurveExposeXDatum R I q B hq hI).xStructMap =
      tateCurveModelStructMap R I q hq hI := by
  refine FormalScheme.GlueData.hom_ext _ fun i => ?_
  rw [← Category.assoc, ι_tateXGluedInv, Category.assoc,
    AffineChartedFibreDatumX.ι_xStructMap, tateChartCompUInv_comp_xStructMapChart,
    tateCurveModelStructMap, FormalScheme.GlueData.ι_glueMorphisms]

/-! ### The Tate diagonal datum and the two legs -/

/-- **The Tate curve model's diagonal datum** `𝔈_q ×_{Spf R} 𝔈_q` in the generic vocabulary:
`diagonalDatum` applied to `tateCurveExposeXDatum`. The double-overlap data `σ`, `hστ`, `hσc` are
vacuous, because a two-element index type has no three pairwise-distinct elements. -/
abbrev tateDiagonalDatum (hq : q ∈ I) (hI : I.FG) : BothChartedFibreDatumXY R I hI :=
  BothChartedFibreDatumXY.diagonalDatum (tateCurveExposeXDatum R I q B hq hI)
    (fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim)
    (fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim)
    (fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim)

/-- **The `X`-side leg**: the first projection of the hand-built self fibre product, carried into
the datum's glued object by 704's comparison. The type ascription is in the datum's spelling; see
the implementation notes. -/
abbrev tateFibreLegX (hq : q ∈ I) (hI : I.FG) :
    (tateSelfProductInv R I q hq hI).toLocallyRingedSpace ⟶
      (tateDiagonalDatum R I q B hq hI).xGlued.toLocallyRingedSpace :=
  tateSelfProductPr₁ R I q hq hI ≫ tateXGluedInv R I q B hq hI

/-- **The `Y`-side leg**: the second projection, carried into the datum's glued object. Note that
`diagonalDatum` makes `yGlued` definitionally `xGlued`, so the same comparison serves both. -/
abbrev tateFibreLegY (hq : q ∈ I) (hI : I.FG) :
    (tateSelfProductInv R I q hq hI).toLocallyRingedSpace ⟶
      (tateDiagonalDatum R I q B hq hI).yGlued.toLocallyRingedSpace :=
  tateSelfProductPr₂ R I q hq hI ≫ tateXGluedInv R I q B hq hI

/-- `tateXGluedInv_comp_xStructMap`, restated in the diagonal datum's spelling. The two statements
are definitionally the same; the elaborator reconciles them at default transparency, whereas a
`rw` between them would not be type-correct at `instances` transparency. -/
theorem tateXGluedInv_comp_tateDiagonalDatum_xStructMap (hq : q ∈ I) (hI : I.FG) :
    tateXGluedInv R I q B hq hI ≫ (tateDiagonalDatum R I q B hq hI).xStructMap =
      tateCurveModelStructMap R I q hq hI :=
  tateXGluedInv_comp_xStructMap R I q B hq hI

/-- The `Y`-side form of `tateXGluedInv_comp_tateDiagonalDatum_xStructMap`. -/
theorem tateXGluedInv_comp_tateDiagonalDatum_yStructMap (hq : q ∈ I) (hI : I.FG) :
    tateXGluedInv R I q B hq hI ≫ (tateDiagonalDatum R I q B hq hI).yStructMap =
      tateCurveModelStructMap R I q hq hI :=
  tateXGluedInv_comp_xStructMap R I q B hq hI

/-- **The cone condition of the two legs**, `fibreLift`'s `hcomm` input: both legs agree after the
datum's structural morphism, because both reduce to `tateSelfProduct_cone_comm` through the
compatibility above.

Kept in pure term mode. `rw` cannot rebuild a motive across the `xGlued` object-defeq wall — see
the implementation notes — and `tateSelfProduct_cone_comm` is written the same way for the same
reason. -/
theorem tateFibreLeg_cone_comm (hq : q ∈ I) (hI : I.FG) :
    tateFibreLegX R I q B hq hI ≫ (tateDiagonalDatum R I q B hq hI).xStructMap =
      tateFibreLegY R I q B hq hI ≫ (tateDiagonalDatum R I q B hq hI).yStructMap :=
  (Category.assoc _ _ _).trans
    (((congrArg (fun g : (tateCurveModel R I q hq hI).toLocallyRingedSpace ⟶
          locallyRingedSpaceObj I => tateSelfProductPr₁ R I q hq hI ≫ g)
        (tateXGluedInv_comp_tateDiagonalDatum_xStructMap R I q B hq hI)).trans
      ((tateSelfProduct_cone_comm R I q hq hI).trans
        (congrArg (fun g : (tateCurveModel R I q hq hI).toLocallyRingedSpace ⟶
            locallyRingedSpaceObj I => tateSelfProductPr₂ R I q hq hI ≫ g)
          (tateXGluedInv_comp_tateDiagonalDatum_yStructMap R I q B hq hI)).symm)).trans
      (Category.assoc _ _ _).symm)

/-! ### The comparison morphism -/

/-- **The per-refined-chart continuity input** of `fibreLift`, for the two Tate legs. Named because
it is long and appears in every statement below.

It stays a hypothesis, exactly as it does for the general diagonal
(`BothChartedFibreDatumXY.diagonal`): discharging it in general is issue 235c, and nothing in this
file makes the Tate case easier than the general one. The same applies to `LocallyFG` of the
source. -/
abbrev TateFibreLiftContinuity (hq : q ∈ I) (hI : I.FG)
    (hZ : (tateSelfProductInv R I q hq hI).LocallyFG) : Prop :=
  ∀ c, I ≤ ((tateDiagonalDatum R I q B hq hI).bothRefinedChart
      (tateFibreLegX R I q B hq hI) (tateFibreLegY R I q B hq hI) hZ c).J.comap
    ((tateDiagonalDatum R I q B hq hI).refinedStructHom
      (tateFibreLegX R I q B hq hI) (tateFibreLegY R I q B hq hI) hZ c)

/-- **The comparison morphism** `𝔈_q ×_{Spf R} 𝔈_q ⟶ (Tate diagonal datum).generalFibreProduct`,
from the hand-built four-chart self fibre product to the generic one, defined as the fibre-product
mediating morphism of the two legs.

This is the direction of the brick-4 comparison that needs no glue-datum work: the overlap
identifications of 738/739/751 are consumed by the *other* direction. -/
def tateFibreProductHom (hq : q ∈ I) (hI : I.FG)
    (hZ : (tateSelfProductInv R I q hq hI).LocallyFG)
    (hs : TateFibreLiftContinuity R I q B hq hI hZ) :
    (tateSelfProductInv R I q hq hI).toLocallyRingedSpace ⟶
      (tateDiagonalDatum R I q B hq hI).generalFibreProduct.toLocallyRingedSpace :=
  (tateDiagonalDatum R I q B hq hI).fibreLift
    (BothChartedFibreDatumXY.ofFactors_hV _ _ _ _ _ _ _ _)
    (BothChartedFibreDatumXY.ofFactors_hf _ _ _ _ _ _ _ _)
    (BothChartedFibreDatumXY.ofFactors_ht _ _ _ _ _ _ _ _)
    (Z := tateSelfProductInv R I q hq hI)
    (tateFibreLegX R I q B hq hI) (tateFibreLegY R I q B hq hI) hZ
    (tateFibreLeg_cone_comm R I q B hq hI) hs

/-- **The comparison morphism recovers the first projection.** Together with its `pr₂` mirror this
is the shape brick 4c (706) consumes: `schemeDiagonal'` for the Tate model is pinned by its two
projections, and these are what identify them with `tateSelfProductPr₁` / `Pr₂`. -/
theorem tateFibreProductHom_comp_pr₁ (hq : q ∈ I) (hI : I.FG)
    (hZ : (tateSelfProductInv R I q hq hI).LocallyFG)
    (hs : TateFibreLiftContinuity R I q B hq hI hZ) :
    tateFibreProductHom R I q B hq hI hZ hs ≫ (tateDiagonalDatum R I q B hq hI).pr₁
        (BothChartedFibreDatumXY.ofFactors_hV _ _ _ _ _ _ _ _)
        (BothChartedFibreDatumXY.ofFactors_hf _ _ _ _ _ _ _ _)
        (BothChartedFibreDatumXY.ofFactors_ht _ _ _ _ _ _ _ _) =
      tateFibreLegX R I q B hq hI :=
  (tateDiagonalDatum R I q B hq hI).fibreLift_comp_pr₁ _ _ _ _ _ hZ _ hs

/-- **The comparison morphism recovers the second projection.** -/
theorem tateFibreProductHom_comp_pr₂ (hq : q ∈ I) (hI : I.FG)
    (hZ : (tateSelfProductInv R I q hq hI).LocallyFG)
    (hs : TateFibreLiftContinuity R I q B hq hI hZ) :
    tateFibreProductHom R I q B hq hI hZ hs ≫ (tateDiagonalDatum R I q B hq hI).pr₂
        (BothChartedFibreDatumXY.ofFactors_hV _ _ _ _ _ _ _ _)
        (BothChartedFibreDatumXY.ofFactors_hf _ _ _ _ _ _ _ _)
        (BothChartedFibreDatumXY.ofFactors_ht _ _ _ _ _ _ _ _) =
      tateFibreLegY R I q B hq hI :=
  (tateDiagonalDatum R I q B hq hI).fibreLift_comp_pr₂ _ _ _ _ _ hZ _ hs

end AlgebraicGeometry

end
