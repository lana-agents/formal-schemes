import FormalSchemes.AffineSeparatedIso
import FormalSchemes.ClosedImmersionAffine
import FormalSchemes.ClosedImmersionIso
import FormalSchemes.GeneralFibreProductLiftUniqueAdic

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# `Spf A` over `Spf R`: the first `BothChartedFibreDatumXY.IsSeparated` value (EGA I §10.15)

`FormalSchemes/GeneralSeparated.lean` (issue 499) introduced the §10.15 separatedness vocabulary
for a datum-presented formal scheme — the scheme-level general diagonal
`BothChartedFibreDatumXY.schemeDiagonal'` and the predicate `BothChartedFibreDatumXY.IsSeparated` —
but produced no value of that predicate. `FormalSchemes/AffineSeparatedInstance.lean` (issue 506)
presented `Spf A` as a one-chart datum `oneChartExposeXDatum`, and
`FormalSchemes/AffineSeparatedIso.lean` (issue 512) identified the two glued objects of that datum
with their single charts. This file closes the loop.

The general diagonal `diagonal'` is an *opaque glued mediating morphism* (`fibreLiftOf` of the
identity pair over an adic-carrying refined cover), so it is not definitionally the affine diagonal
`CompletedTensorProduct.schemeDiagonal`. The two are identified through the uniqueness half of the
fibre-product universal property, in its adic-tracking form
`BothChartedFibreDatumXY.fibreLift_unique_adicOverBase` (issue 518): both morphisms have the same
composites with the two projections `pr₁`, `pr₂` (each is the identity of `Spf A`), and the source
`xGlued` is adic over the base by `adicOverBase_xStructMap`, which discharges the per-chart
continuity hypothesis internally. Transporting the affine diagonal's closed immersion
(`CompletedTensorProduct.schemeDiagonal_isClosedImmersion`, issue 492) across the two gluing
isomorphisms with `FormalScheme.IsClosedImmersion.iso_comp`/`comp_iso` then gives separatedness.

## Main definitions and results

* `AlgebraicGeometry.oneChartDiagDatum`: the one-chart diagonal datum `Spf A ×_{Spf R} Spf A`.
* `AlgebraicGeometry.oneChart_schemeDiagonal'_eq`: the general diagonal of the one-chart datum is
  the affine diagonal, conjugated by the two gluing isomorphisms.
* `AlgebraicGeometry.oneChart_isSeparated`: **`Spf A` is separated over `Spf R`** — the first
  concrete `BothChartedFibreDatumXY.IsSeparated` value.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A] [TopologicalSpace A]
variable [IsAdicRing (I.map (algebraMap R A))]

/-- The one-chart index type has no two distinct elements. Stated at the datum's own index type
`(oneChartExposeXDatum R I hI A).J` rather than at `ULift Unit`, so that the vacuous overlap data
built from it stays type-correct at `instances` transparency — which is what lets `rw` operate on
goals mentioning the resulting diagonal datum. -/
private theorem oneChartNeElim {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
    {A : Type u} [CommRing A] [Algebra R A] [TopologicalSpace A]
    [IsAdicRing (I.map (algebraMap R A))]
    {i j : (oneChartExposeXDatum R I hI A).J} (h : i ≠ j) : False :=
  h (Subsingleton.elim (α := ULift.{u} Unit) i j)

/-- The inverse of the one-chart identification `xGlued ≅ Spf A` is the single chart inclusion. -/
theorem oneChartXGluedIso_inv_toLRSHom :
    (oneChartXGluedIso hI (A := A)).inv.toLRSHom =
      (oneChartExposeXDatum R I hI A).xFormalGlueData.ι ⟨⟨⟩⟩ := by
  simp only [oneChartXGluedIso, Iso.symm_inv]
  exact (Functor.FullyFaithful.ofFullyFaithful
    FormalScheme.forgetToLocallyRingedSpace).map_preimage _

/-- **The one-chart diagonal datum** presenting `Spf A ×_{Spf R} Spf A`: `diagonalDatum` applied to
the one-chart datum `oneChartExposeXDatum`, all of whose double-overlap `σ`-data is vacuous. -/
abbrev oneChartDiagDatum : BothChartedFibreDatumXY R I hI :=
  BothChartedFibreDatumXY.diagonalDatum (oneChartExposeXDatum R I hI A)
    (fun _ _ _ h _ _ => (oneChartNeElim h).elim)
    (fun _ _ _ h _ _ => (oneChartNeElim h).elim)
    (fun _ _ _ h _ _ => (oneChartNeElim h).elim)

variable [IsAdicRing (CompletedTensorProduct.idealOfDefinition R I A A)]

/-- The inverse of the one-chart identification `X ×_{Spf R} X ≅ Spf (A ⊗̂_R A)` is the single
product chart inclusion. -/
theorem oneChartFibreProductIso_inv_toLRSHom :
    (oneChartFibreProductIso hI (A := A)).inv.toLRSHom =
      (oneChartDiagDatum hI (A := A)).formalGlueData.ι ⟨⟨⟨⟩⟩, ⟨⟨⟩⟩⟩ := by
  simp only [oneChartFibreProductIso]
  exact (Functor.FullyFaithful.ofFullyFaithful
    FormalScheme.forgetToLocallyRingedSpace).map_preimage _

/-- The single product chart's first projection is the affine one. -/
theorem oneChartDiagDatum_pr₁ChartSelf :
    (oneChartDiagDatum hI (A := A)).pr₁ChartSelf ⟨⟨⟨⟩⟩, ⟨⟨⟩⟩⟩ =
      CompletedTensorProduct.fibrePr₁ (R := R) (I := I) (A := A) (B := A) := rfl

/-- The single product chart's second projection is the affine one. -/
theorem oneChartDiagDatum_pr₂ChartSelf :
    (oneChartDiagDatum hI (A := A)).pr₂ChartSelf ⟨⟨⟨⟩⟩, ⟨⟨⟩⟩⟩ =
      CompletedTensorProduct.fibrePr₂ (R := R) (I := I) (A := A) (B := A) := rfl

/-- The `X`-factor chart inclusion of the diagonal datum is the inverse of `oneChartXGluedIso`. -/
theorem oneChartDiagDatum_xFormalGlueData_ι :
    (oneChartDiagDatum hI (A := A)).xFormalGlueData.ι ⟨⟨⟩⟩ =
      (oneChartXGluedIso hI (A := A)).inv.toLRSHom :=
  (oneChartXGluedIso_inv_toLRSHom hI).symm

/-- The `Y`-factor chart inclusion of the diagonal datum is the inverse of `oneChartXGluedIso`
(the two factors of the diagonal datum are the same). -/
theorem oneChartDiagDatum_yFormalGlueData_ι :
    (oneChartDiagDatum hI (A := A)).yFormalGlueData.ι ⟨⟨⟩⟩ =
      (oneChartXGluedIso hI (A := A)).inv.toLRSHom :=
  (oneChartXGluedIso_inv_toLRSHom hI).symm

/-- The underlying locally-ringed-space morphism of the affine scheme-level diagonal. -/
theorem CompletedTensorProduct.schemeDiagonal_toLRSHom :
    (CompletedTensorProduct.schemeDiagonal (R := R) (I := I) (A := A) hI).toLRSHom =
      CompletedTensorProduct.diagonal (R := R) (I := I) (A := A) hI := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The general diagonal of the one-chart datum is the affine diagonal**, conjugated by the two
gluing isomorphisms of `FormalSchemes/AffineSeparatedIso.lean`.

Both sides are morphisms `X ⟶ X ×_{Spf R} X` out of the glued `X = Spf A`, and both become the
identity after either projection; the adic-tracking uniqueness
`BothChartedFibreDatumXY.fibreLift_unique_adicOverBase` (issue 518) — whose continuity hypothesis is
supplied by `adicOverBase_xStructMap` — identifies them. -/
theorem oneChart_schemeDiagonal'_eq :
    BothChartedFibreDatumXY.schemeDiagonal' (oneChartExposeXDatum R I hI A)
        (fun _ _ _ h _ _ => (oneChartNeElim h).elim)
        (fun _ _ _ h _ _ => (oneChartNeElim h).elim)
        (fun _ _ _ h _ _ => (oneChartNeElim h).elim) =
      (oneChartXGluedIso hI).hom ≫ CompletedTensorProduct.schemeDiagonal hI ≫
        (oneChartFibreProductIso hI).inv := by
  apply FormalScheme.Hom.ext'
  refine (oneChartDiagDatum hI (A := A)).fibreLift_unique_adicOverBase
    (BothChartedFibreDatumXY.ofFactors_hV _ _ _ _ _ _ _ _)
    (BothChartedFibreDatumXY.ofFactors_hf _ _ _ _ _ _ _ _)
    (BothChartedFibreDatumXY.ofFactors_ht _ _ _ _ _ _ _ _)
    _ _ (oneChartDiagDatum hI (A := A)).xStructMap
    (BothChartedFibreDatumXY.adicOverBase_xStructMap _) ?_ ?_ ?_
  · -- Both sides are sections of `pr₁`.
    refine (BothChartedFibreDatumXY.diagonal'_comp_pr₁ _ _ _ _).trans ?_
    symm
    simp only [FormalScheme.comp_toLRSHom, Category.assoc]
    rw [oneChartFibreProductIso_inv_toLRSHom, BothChartedFibreDatumXY.ι_pr₁,
      oneChartDiagDatum_pr₁ChartSelf, CompletedTensorProduct.schemeDiagonal_toLRSHom]
    dsimp only
    rw [oneChartDiagDatum_xFormalGlueData_ι,
      reassoc_of% (CompletedTensorProduct.diagonal_comp_pr₁ (A := A) hI),
      ← FormalScheme.comp_toLRSHom, Iso.hom_inv_id]
    rfl
  · -- Both sides are sections of `pr₂`.
    refine (BothChartedFibreDatumXY.diagonal'_comp_pr₂ _ _ _ _).trans ?_
    symm
    simp only [FormalScheme.comp_toLRSHom, Category.assoc]
    rw [oneChartFibreProductIso_inv_toLRSHom, BothChartedFibreDatumXY.ι_pr₂,
      oneChartDiagDatum_pr₂ChartSelf, CompletedTensorProduct.schemeDiagonal_toLRSHom]
    dsimp only
    rw [oneChartDiagDatum_yFormalGlueData_ι,
      reassoc_of% (CompletedTensorProduct.diagonal_comp_pr₂ (A := A) hI),
      ← FormalScheme.comp_toLRSHom, Iso.hom_inv_id]
    rfl
  · -- The diagonal lies over the base, being a section of `pr₁`.
    rw [← Category.assoc]
    exact (congrArg (· ≫ (oneChartDiagDatum hI (A := A)).xStructMap)
      (BothChartedFibreDatumXY.diagonal'_comp_pr₁ _ _ _ _)).trans (Category.id_comp _)

/-- **`Spf A` is separated over `Spf R`** (EGA I §10.15): the general diagonal of the one-chart
datum presenting `Spf A` is a closed immersion of formal schemes.

This is the first concrete `BothChartedFibreDatumXY.IsSeparated` value: the §10.15 vocabulary of
`FormalSchemes/GeneralSeparated.lean` is inhabited, by the affine case. It is obtained by
transporting the affine diagonal's closed immersion
(`CompletedTensorProduct.schemeDiagonal_isClosedImmersion`) across the two one-chart gluing
isomorphisms, using the stability of closed immersions under pre- and post-composition with
isomorphisms. -/
theorem oneChart_isSeparated :
    BothChartedFibreDatumXY.IsSeparated (oneChartExposeXDatum R I hI A)
      (fun _ _ _ h _ _ => (oneChartNeElim h).elim)
      (fun _ _ _ h _ _ => (oneChartNeElim h).elim)
      (fun _ _ _ h _ _ => (oneChartNeElim h).elim) := by
  change FormalScheme.IsClosedImmersion (BothChartedFibreDatumXY.schemeDiagonal' _ _ _ _)
  rw [oneChart_schemeDiagonal'_eq hI]
  exact FormalScheme.IsClosedImmersion.iso_comp _
    ((CompletedTensorProduct.schemeDiagonal_isClosedImmersion hI).comp_iso _)

end AlgebraicGeometry

end
