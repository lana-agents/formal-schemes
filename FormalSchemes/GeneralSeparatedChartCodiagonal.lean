import FormalSchemes.AffineSeparated
import FormalSchemes.DiagonalClosedEmbedding
import FormalSchemes.GeneralFibreProductLiftUniqueAdic
import FormalSchemes.GeneralSeparatedChartPreimage
import FormalSchemes.GlueDataImageInter

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The chart-restricted diagonal is `Spf` of the chart codiagonal (EGA I §10.15)

`FormalSchemes/GeneralSeparatedChartPreimage.lean` (issue 777) reduced separatedness of a
datum-presented `X` to a per-chart statement inside one affine formal spectrum: `X` is separated
over `Spf R` iff, for every pair `(i, j)` of chart indices, the set

```
⇑(ι (i, j)).base ⁻¹' Set.range ⇑(schemeDiagonal' …).base ⊆ Spf(A i ⊗̂_R A j)
```

is closed. It did **not** say what that set is. This file identifies it, and thereby turns §10.15
into a purely ring-theoretic condition on the datum's own data.

## The chart codiagonal

For distinct charts `i ≠ j` the overlap `X_i ∩ X_j` is the datum's `Spf(A i{1/g i j}^)`, and it
receives two structure maps: the away-completion map out of `A i` (`overlapAlgFst`) and the
away-completion map out of `A j` composed with the datum's transition `(τ i j)⁻¹`
(`overlapAlgSnd`). Their `CompletedTensorProduct.lift` is the **chart codiagonal**

```
∇_{i j} : A i ⊗̂_R A j →+* A i{1/g i j}^ ,
```

and `chartCodiagonalMap` is the corresponding morphism of formal spectra — presented as
`CompletedTensorProduct.fibreLift`, so that its two projection laws are free. On the diagonal
`i = j` it degenerates to the ordinary codiagonal `A i ⊗̂_R A i → A i`
(`CompletedTensorProduct.codiagonal`), whose `Spf` is the affine diagonal `Δ_{A i/R}`.

## The identification

The engine is `chartLift_comp_diagonal'`: if a morphism `w : Spf L ⟶ X` out of an affine formal
scheme is presented **both** as `Spf a` into the chart `i` and as `Spf b` into the chart `j`, then

```
w ≫ Δ = fibreLift a b ≫ ι (i, j).
```

Both sides have the same two projections — `w` on the left because `Δ` is a section of both
(`diagonal'_comp_pr₁` / `_pr₂`), `w` on the right by `ι_pr₁` / `ι_pr₂` and the two presentations —
so `fibreLift_unique_adicOverBase` (issue 518) identifies them; the adic-over-base hypothesis is
`AlgebraicGeometry.FormalScheme.adicOverBaseLocallyFG_Spf` (`FormalSchemes.AdicOverBaseChart`), for
which an affine source needs only its identity chart.

Off the diagonal the two presentations of the overlap are the two structure maps, related by the
glue relation `x_glue_rel` (`overlapChart_comp_ι_eq`); on the diagonal both are the identity. Since
the image of the overlap in `X` is exactly `X_i ∩ X_j` (`range_overlapChart_comp_ι`), 777's
`preimage_range_ι_diagonal'` then converts the morphism identity into the set identity
`preimage_range_diagonal'_eq_range_fibreLift`.

## The criterion

```lean
theorem isSeparated_of_chartCodiagonal_surjective
    (hsurj : ∀ i j (hij : i ≠ j), Function.Surjective (DX.chartCodiagonal i j hij)) :
    IsSeparated DX σX hστX hσcX
```

**`X` is separated over `Spf R` as soon as every chart codiagonal is surjective.** The diagonal
pairs are free: there the chart-restricted diagonal is `Spf` of the ordinary codiagonal, which is
always surjective. Closedness comes from `FormalSpectrum.isClosedEmbedding_map_of_surjective`.

Surjectivity is not automatic, and that is the point: for the line with a doubled origin the
overlap is `𝔾ₘ` and the chart codiagonal `k[x] ⊗ k[y] → k[t, t⁻¹]` misses `t⁻¹`, exactly matching
the failure of separatedness.

## Main definitions and results

* `AlgebraicGeometry.AffineChartedFibreDatumX.overlapAlgFst` / `overlapAlgSnd`: the two structure
  maps of the overlap `X_i ∩ X_j`.
* `AlgebraicGeometry.AffineChartedFibreDatumX.chartCodiagonal`: the chart codiagonal
  `A i ⊗̂_R A j →+* A i{1/g i j}^`, with its restrictions to the two factors.
* `AlgebraicGeometry.AffineChartedFibreDatumX.chartCodiagonalMap`: its formal spectrum, with the
  two projection laws.
* `AlgebraicGeometry.BothChartedFibreDatumXY.chartLift_comp_diagonal'`: the chart-lift
  identification.
* `AlgebraicGeometry.BothChartedFibreDatumXY.preimage_range_diagonal'_eq_range_chartCodiagonalMap`
  and `preimage_range_diagonal'_eq_range_diagonal`: what each product chart sees of the diagonal.
* `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_chartCodiagonal_surjective`: the
  ring-theoretic separatedness criterion.

## Implementation notes

The uniqueness lemma forces the source to be spelled `FormalScheme.Spf L`, whose
`toLocallyRingedSpace` is definitionally but not syntactically `locallyRingedSpaceObj L`. Under
`instances` transparency `rw [Category.assoc]` therefore fails inside `chartLift_comp_diagonal'`,
and the whole proof is written in term mode, where the two spellings are free. For the same reason
the datum argument of every `BothChartedFibreDatumXY` lemma used here is given explicitly rather
than as `_`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum Topology
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

namespace AffineChartedFibreDatumX

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {BX : Type u} [CommRing BX] [Algebra R BX]
variable (DX : AffineChartedFibreDatumX R I hI BX)

/-! ### The two structure maps of an overlap -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The away completion's ideal of definition is finitely generated when `I` is. -/
theorem fg_awayCompletionIdeal (i j : DX.J) :
    letI := DX.commRing; letI := DX.algebra
    (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j)).FG :=
  letI := DX.commRing; letI := DX.algebra
  awayCompletionIdeal_fg _ _ (hI.map _)

/-- **The first structure map of the overlap** `A i → A i{1/g i j}^`: the away-completion map,
i.e. the ring map of the inclusion `X_i ∩ X_j ↪ X_i`. -/
def overlapAlgFst (i j : DX.J) :
    letI := DX.commRing; letI := DX.algebra
    DX.A i →ₐ[R] awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j) :=
  letI := DX.commRing; letI := DX.algebra
  IsScalarTower.toAlgHom R (DX.A i) (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j))

/-- **The second structure map of the overlap** `A j → A i{1/g i j}^`: the away-completion map out
of `A j` followed by the datum's transition `(τ i j)⁻¹`, i.e. the ring map of the inclusion
`X_i ∩ X_j ↪ X_j` read in the `i`-th presentation of the overlap. -/
def overlapAlgSnd (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra
    DX.A j →ₐ[R] awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j) :=
  letI := DX.commRing; letI := DX.algebra
  (DX.τ i j h).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R (DX.A j)
      (awayCompletion (I.map (algebraMap R (DX.A j))) (DX.g j i)))

/-! ### The chart codiagonal -/

/-- **The chart codiagonal** `∇_{i j} : A i ⊗̂_R A j → A i{1/g i j}^` of a pair of distinct charts:
the lift of the two structure maps of the overlap `X_i ∩ X_j = Spf(A i{1/g i j}^)`, namely the
away-completion map out of `A i` and the away-completion map out of `A j` followed by the datum's
transition `(τ i j)⁻¹`.

Geometrically it is the ring map of the diagonal restricted to the overlap: a point of `X_i ∩ X_j`
gives the same point of `X` in both factors, which is exactly the statement that the two structure
maps into the overlap are glued by `τ`. -/
def chartCodiagonal (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra
    CompletedTensorProduct R I (DX.A i) (DX.A j) →+*
      awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j) :=
  letI := DX.commRing; letI := DX.algebra
  haveI : IsAdicComplete (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j))
      (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j)) :=
    (isAdicRing_awayCompletionIdeal _ _ (hI.map _)).toIsAdicComplete
  CompletedTensorProduct.lift (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j))
    (map_algebraMap_awayCompletion_eq I (DX.g i j)).le
    (DX.overlapAlgFst i j) (DX.overlapAlgSnd i j h)

/-- The chart codiagonal restricted to the first factor is the away-completion map `A i → A i{1/g}`
— the ring map of the overlap's inclusion into the chart `i`. -/
theorem chartCodiagonal_comp_inl (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra
    (DX.chartCodiagonal i j h).comp
        (CompletedTensorProduct.inl R I (DX.A i) (DX.A j)).toRingHom =
      awayCompletionHom (I.map (algebraMap R (DX.A i))) (DX.g i j) := by
  letI := DX.commRing; letI := DX.algebra
  haveI : IsAdicComplete (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j))
      (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j)) :=
    (isAdicRing_awayCompletionIdeal _ _ (hI.map _)).toIsAdicComplete
  exact RingHom.ext fun a => CompletedTensorProduct.lift_inl _
    (map_algebraMap_awayCompletion_eq I (DX.g i j)).le _ _ a

/-- The chart codiagonal restricted to the second factor is the away-completion map
`A j → A j{1/g j i}` followed by the transition `(τ i j)⁻¹`. -/
theorem chartCodiagonal_comp_inr (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra
    (DX.chartCodiagonal i j h).comp
        (CompletedTensorProduct.inr R I (DX.A i) (DX.A j)).toRingHom =
      (DX.τ i j h).symm.toRingEquiv.toRingHom.comp
        (awayCompletionHom (I.map (algebraMap R (DX.A j))) (DX.g j i)) := by
  letI := DX.commRing; letI := DX.algebra
  haveI : IsAdicComplete (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j))
      (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j)) :=
    (isAdicRing_awayCompletionIdeal _ _ (hI.map _)).toIsAdicComplete
  exact RingHom.ext fun a => CompletedTensorProduct.lift_inr _
    (map_algebraMap_awayCompletion_eq I (DX.g i j)).le _ _ a

/-! ### The chart-restricted diagonal, affinely -/

/-- **The chart-restricted diagonal** `Spf(A i{1/g i j}^) ⟶ Spf(A i ⊗̂_R A j)`: `Spf` of the chart
codiagonal, presented as the affine fibre-product mediating morphism `fibreLift` of the two
structure maps of the overlap, so that its two projection laws are `fibreLift_comp_pr₁` /
`fibreLift_comp_pr₂`. -/
def chartCodiagonalMap (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra
    locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j)) ⟶
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)) :=
  letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
  haveI : IsAdicRing (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j)) :=
    isAdicRing_awayCompletionIdeal _ _ (hI.map _)
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)) :=
    CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A j) hI
  CompletedTensorProduct.fibreLift (map_algebraMap_awayCompletion_eq I (DX.g i j)).le
    (DX.overlapAlgFst i j) (DX.overlapAlgSnd i j h) hI

/-- **The chart-restricted diagonal followed by the first projection is the overlap's inclusion
into the chart `i`** — `fibreLift_comp_pr₁` for the chart codiagonal. -/
theorem chartCodiagonalMap_comp_fibrePr₁ (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
    haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)) :=
      CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A j) hI
    DX.chartCodiagonalMap i j h ≫ CompletedTensorProduct.fibrePr₁ =
      basicOpenChart (I.map (algebraMap R (DX.A i))) (DX.g i j) := by
  letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
  haveI : IsAdicRing (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j)) :=
    isAdicRing_awayCompletionIdeal _ _ (hI.map _)
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)) :=
    CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A j) hI
  exact CompletedTensorProduct.fibreLift_comp_pr₁ _ _ _ hI

/-- **The chart-restricted diagonal followed by the second projection is the overlap's inclusion
into the chart `j`**, read through the datum's transition `τ i j`. -/
theorem chartCodiagonalMap_comp_fibrePr₂ (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
    haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)) :=
      CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A j) hI
    DX.chartCodiagonalMap i j h ≫ CompletedTensorProduct.fibrePr₂ =
      awayCompletionTransition (DX.g i j) (DX.g j i) (DX.τ i j h) ≫
        basicOpenChart (I.map (algebraMap R (DX.A j))) (DX.g j i) := by
  letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
  haveI : IsAdicRing (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j)) :=
    isAdicRing_awayCompletionIdeal _ _ (hI.map _)
  haveI : IsAdicRing (awayCompletionIdeal (I.map (algebraMap R (DX.A j))) (DX.g j i)) :=
    isAdicRing_awayCompletionIdeal _ _ (hI.map _)
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)) :=
    CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A j) hI
  refine (CompletedTensorProduct.fibreLift_comp_pr₂ _ _ _ hI).trans ?_
  exact locallyRingedSpaceMap_comp _ _ _ _ _
    (le_comap_awayCompletionHom (I.map (algebraMap R (DX.A j))) (DX.g j i))
    (awayCompletionTransition_le_comap (DX.g i j) (DX.g j i) (DX.τ i j h)) _

end AffineChartedFibreDatumX

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {BX : Type u} [CommRing BX] [Algebra R BX]
variable (DX : AffineChartedFibreDatumX R I hI BX)
variable
  (σX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (DX.A i'))) (DX.g i' i'' * DX.g i' i)))
  (hστX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (DX.g i' i'') (DX.g i' i) hI) =
      (furtherLocFst I (DX.g i i') (DX.g i i'') hI).comp (DX.τ i i' h1).symm.toAlgHom)
  (hσcX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
      (σX i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'')))

/-! ### The chart-lift identification -/

/-- **A morphism into `X` that factors through both the chart `i` and the chart `j`, by affine
data, has diagonal `Spf` of the corresponding lift.**

This is the general form of the identification: `w : Spf L ⟶ X` is presented in two ways, as
`Spf a` into the chart `i` and as `Spf b` into the chart `j`; then `w ≫ Δ` factors through the
product chart `(i, j)` as `fibreLift a b`. Both `i = j` (with `a = b`) and `i ≠ j` (with `w` the
overlap `X_i ∩ X_j`) are instances.

The proof is uniqueness (`fibreLift_unique_adicOverBase`, issue 518): both sides have the same two
projections — `w` on the left because `Δ` is a section of both, and `w` on the right by `ι_pr₁` /
`ι_pr₂` together with the two presentations of `w`. -/
theorem chartLift_comp_diagonal'
    {S : Type u} [CommRing S] [Algebra R S] [TopologicalSpace S] {L : Ideal S} [IsAdicRing L]
    (hLfg : L.FG) (hIL : I.map (algebraMap R S) ≤ L) (i j : DX.J)
    (a : letI := DX.commRing; letI := DX.algebra; DX.A i →ₐ[R] S)
    (b : letI := DX.commRing; letI := DX.algebra; DX.A j →ₐ[R] S)
    (w : locallyRingedSpaceObj L ⟶
      (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
    (ha : letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
      w = locallyRingedSpaceMap (I.map (algebraMap R (DX.A i))) L a.toRingHom
          (CompletedTensorProduct.algHom_le_comap a hIL) ≫
        (diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i)
    (hb : letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
      w = locallyRingedSpaceMap (I.map (algebraMap R (DX.A j))) L b.toRingHom
          (CompletedTensorProduct.algHom_le_comap b hIL) ≫
        (diagonalDatum DX σX hστX hσcX).yFormalGlueData.ι j) :
    letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
    haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)) :=
      CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A j) hI
    w ≫ diagonal' DX σX hστX hσcX =
      CompletedTensorProduct.fibreLift hIL a b hI ≫
        (diagonalDatum DX σX hστX hσcX).formalGlueData.ι (i, j) := by
  letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)) :=
    CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A j) hI
  have hbase : I ≤ L.comap (algebraMap R S) := Ideal.map_le_iff_le_comap.mp hIL
  have hcomp : I ≤ L.comap (a.toRingHom.comp (algebraMap R (DX.A i))) := by
    rw [show a.toRingHom.comp (algebraMap R (DX.A i)) = algebraMap R S from
      AlgHom.comp_algebraMap a]
    exact hbase
  -- The base morphism of the affine source, read off the chart-`i` presentation of `w`.
  -- Everything below is in term mode: the two spellings `locallyRingedSpaceObj L` and
  -- `(FormalScheme.Spf L).toLocallyRingedSpace` are definitionally but not syntactically equal,
  -- so `rw` cannot build a motive through them.
  have hstruct : w ≫ (diagonalDatum DX σX hστX hσcX).xStructMap =
      locallyRingedSpaceMap I L (algebraMap R S) hbase :=
    (congrArg (fun m => m ≫ (diagonalDatum DX σX hστX hσcX).xStructMap) ha).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (fun m => locallyRingedSpaceMap (I.map (algebraMap R (DX.A i))) L a.toRingHom
            (CompletedTensorProduct.algHom_le_comap a hIL) ≫ m)
          (BothChartedFibreDatumXY.ι_xStructMap (diagonalDatum DX σX hστX hσcX) i)).trans <|
        (locallyRingedSpaceMap_comp I (I.map (algebraMap R (DX.A i))) L
            (algebraMap R (DX.A i)) a.toRingHom Ideal.le_comap_map
            (CompletedTensorProduct.algHom_le_comap a hIL) hcomp).symm.trans
          (locallyRingedSpaceMap_congr _ _ _ _ _ _ (AlgHom.comp_algebraMap a))
  refine BothChartedFibreDatumXY.fibreLift_unique_adicOverBase (diagonalDatum DX σX hστX hσcX)
    (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
    (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)
    (Z := FormalScheme.Spf L) _ _ (locallyRingedSpaceMap I L (algebraMap R S) hbase)
    (FormalScheme.adicOverBaseLocallyFG_Spf hLfg _ ?_) ?_ ?_ ?_
  · rw [globalSectionsMap_locallyRingedSpaceMap]
    exact hbase
  · -- both sides have first projection `w`
    exact (Category.assoc _ _ _).trans <|
      (congrArg (fun m => w ≫ m)
        (BothChartedFibreDatumXY.diagonal'_comp_pr₁ DX σX hστX hσcX)).trans <|
      (Category.comp_id w).trans <| ha.trans <|
      (congrArg (fun m => m ≫ (diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i)
        (CompletedTensorProduct.fibreLift_comp_pr₁ hIL a b hI).symm).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (fun m => CompletedTensorProduct.fibreLift hIL a b hI ≫ m)
        (BothChartedFibreDatumXY.ι_pr₁ (diagonalDatum DX σX hστX hσcX)
          (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
          (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
          (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX) (i, j)).symm).trans
      (Category.assoc _ _ _).symm
  · -- both sides have second projection `w`
    exact (Category.assoc _ _ _).trans <|
      (congrArg (fun m => w ≫ m)
        (BothChartedFibreDatumXY.diagonal'_comp_pr₂ DX σX hστX hσcX)).trans <|
      (Category.comp_id w).trans <| hb.trans <|
      (congrArg (fun m => m ≫ (diagonalDatum DX σX hστX hσcX).yFormalGlueData.ι j)
        (CompletedTensorProduct.fibreLift_comp_pr₂ hIL a b hI).symm).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (fun m => CompletedTensorProduct.fibreLift hIL a b hI ≫ m)
        (BothChartedFibreDatumXY.ι_pr₂ (diagonalDatum DX σX hστX hσcX)
          (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
          (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
          (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX) (i, j)).symm).trans
      (Category.assoc _ _ _).symm
  · -- the diagonal lies over the base
    exact (Category.assoc _ _ _).trans <|
      ((congrArg (fun m => w ≫ m) (Category.assoc _ _ _).symm).trans <|
        (congrArg (fun m => w ≫ m ≫ (diagonalDatum DX σX hστX hσcX).xStructMap)
          (BothChartedFibreDatumXY.diagonal'_comp_pr₁ DX σX hστX hσcX)).trans <|
        (congrArg (fun m => w ≫ m) (Category.id_comp _)).trans hstruct)

/-! ### The two instances of the chart-lift identification -/

/-- **The overlap's inclusion into `X`, read through the chart `j`.** The same morphism
`X_i ∩ X_j ⟶ X` that the chart `i` presents as `basicOpenChart (g i j) ≫ ι_i` is presented by the
chart `j` as `Spf` of the second structure map `overlapAlgSnd`, by the datum's glue relation
`x_glue_rel`. This is the `hb` input of `chartLift_comp_diagonal'` off the diagonal. -/
theorem overlapChart_comp_ι_eq (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
    basicOpenChart (I.map (algebraMap R (DX.A i))) (DX.g i j) ≫
        (diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i =
      locallyRingedSpaceMap (I.map (algebraMap R (DX.A j)))
          (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j))
          (DX.overlapAlgSnd i j h).toRingHom
          (CompletedTensorProduct.algHom_le_comap (DX.overlapAlgSnd i j h)
            (map_algebraMap_awayCompletion_eq I (DX.g i j)).le) ≫
        (diagonalDatum DX σX hστX hσcX).yFormalGlueData.ι j := by
  letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
  exact (BothChartedFibreDatumXY.x_glue_rel (diagonalDatum DX σX hστX hσcX) i j h).trans <|
    (Category.assoc _ _ _).symm.trans <|
      congrArg (fun m => m ≫ (diagonalDatum DX σX hστX hσcX).yFormalGlueData.ι j)
        (locallyRingedSpaceMap_comp (I.map (algebraMap R (DX.A j)))
          (awayCompletionIdeal (I.map (algebraMap R (DX.A j))) (DX.g j i))
          (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j))
          (awayCompletionHom (I.map (algebraMap R (DX.A j))) (DX.g j i))
          (DX.τ i j h).symm.toRingHom
          (le_comap_awayCompletionHom (I.map (algebraMap R (DX.A j))) (DX.g j i))
          (awayCompletionTransition_le_comap (DX.g i j) (DX.g j i) (DX.τ i j h)) _).symm

/-- **The overlap `X_i ∩ X_j` maps into the product chart `(i, j)` by the chart codiagonal.**
The `i ≠ j` instance of `chartLift_comp_diagonal'`: the source is the overlap
`Spf(A i{1/g i j}^)`, presented into the chart `i` by its own away-completion map and into the
chart `j` through the datum's transition, by the glue relation `x_glue_rel`. -/
theorem overlapChart_comp_diagonal' (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
    (basicOpenChart (I.map (algebraMap R (DX.A i))) (DX.g i j) ≫
        (diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i) ≫ diagonal' DX σX hστX hσcX =
      DX.chartCodiagonalMap i j h ≫
        (diagonalDatum DX σX hστX hσcX).formalGlueData.ι (i, j) := by
  letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
  haveI : IsAdicRing (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j)) :=
    isAdicRing_awayCompletionIdeal _ _ (hI.map _)
  haveI : IsAdicRing (awayCompletionIdeal (I.map (algebraMap R (DX.A j))) (DX.g j i)) :=
    isAdicRing_awayCompletionIdeal _ _ (hI.map _)
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)) :=
    CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A j) hI
  exact chartLift_comp_diagonal' DX σX hστX hσcX (DX.fg_awayCompletionIdeal i j)
    (map_algebraMap_awayCompletion_eq I (DX.g i j)).le i j
    (DX.overlapAlgFst i j) (DX.overlapAlgSnd i j h) _ rfl
    (overlapChart_comp_ι_eq DX σX hστX hσcX i j h)


/-! ### What the product chart sees of the diagonal, as a range -/

/-- **The chart-restricted diagonal, as a set.** Under the hypotheses of
`chartLift_comp_diagonal'` together with the identification of `w`'s range with the overlap
`X_i ∩ X_j`, the preimage of the diagonal's image in the product chart `(i, j)` is exactly the
range of the affine lift.

`⊇` is the morphism identity read pointwise; `⊆` uses `preimage_range_ι_diagonal'` (issue 777) to
place the source point in `X_i ∩ X_j = range w`, and then cancels the injective `ι (i, j)`. -/
theorem preimage_range_diagonal'_eq_range_fibreLift
    {S : Type u} [CommRing S] [Algebra R S] [TopologicalSpace S] {L : Ideal S} [IsAdicRing L]
    (hLfg : L.FG) (hIL : I.map (algebraMap R S) ≤ L) (i j : DX.J)
    (a : letI := DX.commRing; letI := DX.algebra; DX.A i →ₐ[R] S)
    (b : letI := DX.commRing; letI := DX.algebra; DX.A j →ₐ[R] S)
    (w : locallyRingedSpaceObj L ⟶
      (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
    (ha : letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
      w = locallyRingedSpaceMap (I.map (algebraMap R (DX.A i))) L a.toRingHom
          (CompletedTensorProduct.algHom_le_comap a hIL) ≫
        (diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i)
    (hb : letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
      w = locallyRingedSpaceMap (I.map (algebraMap R (DX.A j))) L b.toRingHom
          (CompletedTensorProduct.algHom_le_comap b hIL) ≫
        (diagonalDatum DX σX hστX hσcX).yFormalGlueData.ι j)
    (hw : Set.range ⇑w.base =
      Set.range ⇑((diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i).base ∩
      Set.range ⇑((diagonalDatum DX σX hστX hσcX).yFormalGlueData.ι j).base) :
    letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
    haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)) :=
      CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A j) hI
    ⇑((diagonalDatum DX σX hστX hσcX).formalGlueData.ι (i, j)).base ⁻¹'
        Set.range ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base =
      Set.range ⇑(CompletedTensorProduct.fibreLift hIL a b hI).base := by
  letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)) :=
    CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A j) hI
  -- The morphism identity, read pointwise. The ascription crosses `diagonal'` versus
  -- `(schemeDiagonal' …).toLRSHom`, which are defeq but print the same and cannot be `rw`n.
  have hpt : ∀ y, (schemeDiagonal' DX σX hστX hσcX).toLRSHom.base (w.base y) =
      ((diagonalDatum DX σX hστX hσcX).formalGlueData.ι (i, j)).base
        ((CompletedTensorProduct.fibreLift hIL a b hI).base y) :=
    fun y => congrFun (congrArg (fun m : locallyRingedSpaceObj L ⟶
        (diagonalDatum DX σX hστX hσcX).generalFibreProduct.toLocallyRingedSpace => ⇑m.base)
      (chartLift_comp_diagonal' DX σX hστX hσcX hLfg hIL i j a b w ha hb)) y
  have hinj : Function.Injective
      ⇑((diagonalDatum DX σX hστX hσcX).formalGlueData.ι (i, j)).base :=
    ((diagonalDatum DX σX hστX hσcX).formalGlueData.ι_isOpenImmersion (i, j)).base_open.injective
  have hpre : ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base ⁻¹'
      Set.range ⇑((diagonalDatum DX σX hστX hσcX).formalGlueData.ι (i, j)).base =
      Set.range ⇑((diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i).base ∩
      Set.range ⇑((diagonalDatum DX σX hστX hσcX).yFormalGlueData.ι j).base :=
    preimage_range_ι_diagonal' DX σX hστX hσcX (i, j)
  refine Set.eq_of_subset_of_subset (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨x, hx⟩ := hz
    have hxmem : x ∈ Set.range ⇑w.base := by
      rw [← hw] at hpre
      exact hpre.le ⟨z, hx.symm⟩
    obtain ⟨y, rfl⟩ := hxmem
    exact ⟨y, hinj ((hpt y).symm.trans hx)⟩
  · obtain ⟨y, rfl⟩ := hz
    exact ⟨w.base y, hpt y⟩


/-! ### The overlap is the intersection of the two charts -/

/-- **The image of the overlap `Spf(A i{1/g i j}^)` in `X` is `X_i ∩ X_j`.** The containment `⊇` is
`LocallyRingedSpace.GlueData.range_ι_inter_subset` (two glued pieces meet only along the image of
their overlap object); `⊆` is the glue relation `x_glue_rel`, which exhibits the same map as
factoring through the chart `j` as well. -/
theorem range_overlapChart_comp_ι (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
    Set.range ⇑(basicOpenChart (I.map (algebraMap R (DX.A i))) (DX.g i j) ≫
        (diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i).base =
      Set.range ⇑((diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i).base ∩
      Set.range ⇑((diagonalDatum DX σX hστX hσcX).yFormalGlueData.ι j).base := by
  letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
  have hglue := BothChartedFibreDatumXY.x_glue_rel (diagonalDatum DX σX hστX hσcX) i j h
  refine Set.eq_of_subset_of_subset (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨y, rfl⟩ := hx
    refine ⟨⟨_, rfl⟩, ?_⟩
    refine ⟨(basicOpenChart (I.map (algebraMap R (DX.A j))) (DX.g j i)).base
      ((awayCompletionTransition (DX.g i j) (DX.g j i) (DX.τ i j h)).base y), ?_⟩
    exact (congrFun (congrArg (fun m : locallyRingedSpaceObj
        (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j)) ⟶
        (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace => ⇑m.base) hglue) y).symm
  · -- the overlap-object containment, transported off the dispatched glue map `f i j`
    have h' : ¬ @Eq (diagonalDatum DX σX hστX hσcX).JX i j := h
    have hxf : (diagonalDatum DX σX hστX hσcX).xLrsGlueData.toGlueData.f i j =
        eqToHom (dif_neg h') ≫
          basicOpenChart (I.map (algebraMap R (DX.A i))) (DX.g i j) := by
      simp only [BothChartedFibreDatumXY.xLrsGlueData, BothChartedFibreDatumXY.xGlueData',
        CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg h']
      rfl
    have e : (diagonalDatum DX σX hστX hσcX).xLrsGlueData.toGlueData.f i j ≫
        (diagonalDatum DX σX hστX hσcX).xLrsGlueData.toGlueData.ι i =
        eqToHom (dif_neg h') ≫ (basicOpenChart (I.map (algebraMap R (DX.A i))) (DX.g i j) ≫
          (diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i) :=
      (congrArg (fun m => m ≫
        (diagonalDatum DX σX hστX hσcX).xLrsGlueData.toGlueData.ι i) hxf).trans
        (Category.assoc _ _ _)
    have hr : Set.range ⇑((diagonalDatum DX σX hστX hσcX).xLrsGlueData.toGlueData.f i j ≫
        (diagonalDatum DX σX hστX hσcX).xLrsGlueData.toGlueData.ι i).base =
        Set.range ⇑(basicOpenChart (I.map (algebraMap R (DX.A i))) (DX.g i j) ≫
          (diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i).base := by
      rw [e]
      exact LocallyRingedSpace.range_eqToHom_comp_base _ _
    exact hr ▸ (diagonalDatum DX σX hστX hσcX).xLrsGlueData.range_ι_inter_subset i j hx


/-! ### The two chart-restricted diagonals, as ranges -/

/-- **Off the diagonal**: what the product chart `(i, j)` sees of the diagonal is the image of the
chart codiagonal. -/
theorem preimage_range_diagonal'_eq_range_chartCodiagonalMap (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
    ⇑((diagonalDatum DX σX hστX hσcX).formalGlueData.ι (i, j)).base ⁻¹'
        Set.range ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base =
      Set.range ⇑(DX.chartCodiagonalMap i j h).base := by
  letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
  haveI : IsAdicRing (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j)) :=
    isAdicRing_awayCompletionIdeal _ _ (hI.map _)
  haveI : IsAdicRing (awayCompletionIdeal (I.map (algebraMap R (DX.A j))) (DX.g j i)) :=
    isAdicRing_awayCompletionIdeal _ _ (hI.map _)
  exact preimage_range_diagonal'_eq_range_fibreLift DX σX hστX hσcX
    (DX.fg_awayCompletionIdeal i j) (map_algebraMap_awayCompletion_eq I (DX.g i j)).le i j
    (DX.overlapAlgFst i j) (DX.overlapAlgSnd i j h) _ rfl
    (overlapChart_comp_ι_eq DX σX hστX hσcX i j h)
    (range_overlapChart_comp_ι DX σX hστX hσcX i j h)

/-- **On the diagonal**: what the product chart `(i, i)` sees of the diagonal is the image of the
affine diagonal `Δ_{A i/R}`, i.e. of the ordinary codiagonal `A i ⊗̂_R A i → A i`. -/
theorem preimage_range_diagonal'_eq_range_diagonal (i : DX.J) :
    letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
    haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A i)) :=
      CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A i) hI
    ⇑((diagonalDatum DX σX hστX hσcX).formalGlueData.ι (i, i)).base ⁻¹'
        Set.range ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base =
      Set.range ⇑(CompletedTensorProduct.diagonal (A := DX.A i) hI).base := by
  letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A i)) :=
    CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A i) hI
  have hid : locallyRingedSpaceMap (I.map (algebraMap R (DX.A i)))
        (I.map (algebraMap R (DX.A i))) (AlgHom.id R (DX.A i)).toRingHom
        (CompletedTensorProduct.algHom_le_comap (AlgHom.id R (DX.A i)) (le_refl _)) ≫
      (diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i =
      (diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i :=
    (congrArg (fun m => m ≫ (diagonalDatum DX σX hστX hσcX).xFormalGlueData.ι i)
      (locallyRingedSpaceMap_id (I := I.map (algebraMap R (DX.A i))))).trans (Category.id_comp _)
  exact preimage_range_diagonal'_eq_range_fibreLift DX σX hστX hσcX (hI.map _) (le_refl _) i i
    (AlgHom.id R (DX.A i)) (AlgHom.id R (DX.A i)) _ hid.symm hid.symm
    (Set.inter_self _).symm

/-! ### The criterion -/

/-- **`X` is separated over `Spf R` as soon as every chart codiagonal is surjective.**

This is the §10.15 obligation reduced to pure ring theory: the datum's own data
`(A i, g i j, τ i j)` determines, for each ordered pair of distinct charts, the map
`∇_{i j} : A i ⊗̂_R A j → A i{1/g i j}^`, and separatedness of the glued `X` follows from
surjectivity of all of them. Nothing topological and nothing about the glued object is left for an
instance to supply.

The diagonal pairs `(i, i)` are **free**: there the chart-restricted diagonal is the affine
diagonal `Δ_{A i/R}`, whose ring map is the ordinary codiagonal `A i ⊗̂_R A i → A i`, always
surjective (`CompletedTensorProduct.codiagonal_surjective`) — the affine case of §10.15. -/
theorem isSeparated_of_chartCodiagonal_surjective
    (hsurj : ∀ (i j : DX.J) (hij : i ≠ j),
      letI := DX.commRing; letI := DX.algebra
      Function.Surjective (DX.chartCodiagonal i j hij)) :
    IsSeparated DX σX hστX hσcX := by
  letI := DX.commRing; letI := DX.algebra; letI := DX.topology; letI := DX.isAdic
  refine isSeparated_of_isClosed_preimage_ι DX σX hστX hσcX fun p => ?_
  obtain ⟨i, j⟩ := p
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)) :=
    CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A j) hI
  by_cases hij : i = j
  · subst hij
    rw [preimage_range_diagonal'_eq_range_diagonal DX σX hστX hσcX i]
    exact (FormalSpectrum.isClosedEmbedding_map_of_surjective
      (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A i))
      (I.map (algebraMap R (DX.A i))) (CompletedTensorProduct.codiagonal R I (DX.A i))
      (CompletedTensorProduct.lift_le_comap (le_refl _) (AlgHom.id R (DX.A i))
        (AlgHom.id R (DX.A i)) hI)
      (CompletedTensorProduct.codiagonal_surjective)).isClosed_range
  · haveI : IsAdicRing (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j)) :=
      isAdicRing_awayCompletionIdeal _ _ (hI.map _)
    rw [preimage_range_diagonal'_eq_range_chartCodiagonalMap DX σX hστX hσcX i j hij]
    exact (FormalSpectrum.isClosedEmbedding_map_of_surjective
      (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j))
      (awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j))
      (DX.chartCodiagonal i j hij)
      (CompletedTensorProduct.lift_le_comap
        (map_algebraMap_awayCompletion_eq I (DX.g i j)).le _ _ hI)
      (hsurj i j hij)).isClosed_range


end BothChartedFibreDatumXY

end AlgebraicGeometry

end
