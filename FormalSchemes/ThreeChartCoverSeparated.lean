import FormalSchemes.AwayCongrAlgebraMap
import FormalSchemes.GeneralSeparatedChartCodiagonalSurjective
import FormalSchemes.ThreeChartCoverDatum

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The three-chart open cover is separated (EGA I §10.15)

`FormalSchemes/ThreeChartCoverDatum.lean` (issue 609) presents `D(f₀) ∪ D(f₁) ∪ D(f₂) ⊆ Spf A` as
an `AffineChartedFibreDatumX` with chart algebras `A{1/f_i}` and overlap elements
`g_ij = ` the image of `f_i·f_j`. Its module docstring promises that the glued `X`, being an open
subscheme of the affine `Spf A`, is separated, and leaves the proof to a follow-up. This file is
that follow-up.

The route is **not** the identification of `X` with an open subscheme of `Spf A` — that would need
base-change infrastructure the tree does not have. It is
`BothChartedFibreDatumXY.isSeparated_of_chartCodiagonal_surjective`
(`FormalSchemes/GeneralSeparatedChartCodiagonal.lean`, issue 778), which reduces §10.15 for a
datum-presented `X` to surjectivity of the **chart codiagonals**

```
∇_{ij} : A{1/f_i}^ ⊗̂_R A{1/f_j}^ ⟶ A{1/f_i}^{1/g_ij}^
```

— a purely ring-theoretic condition on the datum's own data. This is the second concrete
`IsSeparated` value in the tree after the affine one (issue 513), and the first with more than one
chart.

## Why the chart codiagonals are surjective

The image of `∇_{ij}` contains the chart `A{1/f_i}^` itself (through `inl`), so surjectivity comes
down to hitting the inverse of the away element `g_ij`. And `g_ij` is the image of `f_i·f_j`, whose
two factors are inverted in the *two different* charts: `f_i` already in `A{1/f_i}^`, reached
through `inl`, and `f_j` in `A{1/f_j}^`, reached through `inr`. **That is the whole content of the
statement**, and it is exactly what fails for a non-separated datum: for the line with a doubled
origin the two charts are the same `A`, the overlap is `A{1/x}`, and neither factor supplies `x⁻¹`.

So all this file has to do is exhibit the witness `inl (f_i⁻¹) · inr (f_j⁻¹)` and multiply out.
Everything else — the passage from "the image contains a generating set" to genuine surjectivity,
which is successive approximation for complete adic rings — is
`AffineChartedFibreDatumX.chartCodiagonal_surjective_of_mul_eq_one`
(`FormalSchemes/GeneralSeparatedChartCodiagonalSurjective.lean`), stated there for an arbitrary
datum.

**No hypothesis had to be added.** In particular neither `IsNoetherianRing R` nor adicity of `A` is
needed: `I.FG` is enough for the approximation argument, and only the chart algebras `A{1/f_i}`
(which are adic for free) ever occur.

## The transitions are inert, and that is what makes the pairing work

The second structure map of the overlap is `A{1/f_j}^ → A{1/f_j}^{1/g_ji}^ →^{τ⁻¹}
A{1/f_i}^{1/g_ij}^`, so pairing `f_j⁻¹` from the `j`-th chart against `f_j` from the `i`-th chart
needs the transition to be **compatible with the map from `A`**. It is: `τ` is built by passing
through the common `A{1/(f_i f_j)}` downstairs, and both legs — the nested chart identification
`chartOverlapEquiv` and 594's comparison isomorphism `ThreeChart.tau` — fix the image of `A`
(`chartOverlapEquiv_algebraMap`, `ThreeChart.tau_symm_algebraMap`). This is `ThreeChartCover`'s
structural advantage over the Tate datum, whose transition is a genuine automorphism.

## Main definitions and results

* `AlgebraicGeometry.ThreeChartCover.tau_symm_algebraMap`: the open cover's transition fixes the
  image of `A`.
* `AlgebraicGeometry.ThreeChartCover.chartCodiagonal_witness_mul_eq_one`: the witness
  `inl (f_i⁻¹) · inr (f_j⁻¹)`.
* `AlgebraicGeometry.ThreeChartCover.datumX_chartCodiagonal_surjective`: the chart codiagonals of
  the open cover are surjective.
* `AlgebraicGeometry.ThreeChartCover.datumX_isSeparated`: **`D(f₀) ∪ D(f₁) ∪ D(f₂)` is separated
  over `Spf R`.**

The datum-generic machinery this file consumes lives elsewhere, so that another instance can reach
it without importing the three-chart tower:
`FormalSpectrum.surjective_of_algebraMap_mem_range` in
`FormalSchemes/AwayCompletionSurjective.lean`;
`AffineChartedFibreDatumX.map_idealOfDefinition_chartCodiagonal` and
`chartCodiagonal_surjective_of_mul_eq_one` in
`FormalSchemes/GeneralSeparatedChartCodiagonalSurjective.lean`; and
`CompletedTensorAwayInterchange.awayCongrEquiv_algebraMap` in
`FormalSchemes/AwayCongrAlgebraMap.lean`.

## Implementation notes

The cost note of `FormalSchemes/ThreeChartCoverCharts.lean` is in force: `chartOverlapEquiv` must
never be delta-unfolded by the kernel inside a statement about the doubly nested completion. It is
not here — `chartOverlapEquiv_algebraMap` consumes the top-level `chartOverlapEquiv_apply` exactly
as that file intends, and the module costs seconds.

The friction specific to writing *ring* identities against a datum: an equation between the two
spellings of a chart algebra elaborates (`Eq` unifies up to definitional equality), but a
**product** of one element in each does not — `HMul` is synthesised from the syntactic type, and
`(datumX …).A i` is not syntactically `chartAlgebra I f i`. `coverCodiagonal` exists solely to fix
the spelling once, and every identity below is stated against it. (The two frictions inherited from
issue 778 — `AlgHom.comp_algebraMap`'s coercion, and `rw` failing to build a motive through
`awayCompletionIdeal`'s ideal-dependent `CommRing` — are recorded with the lemmas they bit, in
`FormalSchemes/GeneralSeparatedChartCodiagonalSurjective.lean`.)

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

/-! ### 594's comparison isomorphism fixes the base -/

namespace ThreeChart

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable {A : Type u} [CommRing A] [Algebra R A]
variable (f : ULift.{u} (Fin 3) → A)

/-- **594's single-overlap transition fixes the image of `A`**, being a comparison isomorphism of
two completed localizations of `A` at equal elements. -/
theorem tau_symm_algebraMap (i j : ULift.{u} (Fin 3)) (a : A) :
    (tau hI f i j).symm
        (algebraMap A (awayCompletion (I.map (algebraMap R A)) (f j * f i)) a) =
      algebraMap A (awayCompletion (I.map (algebraMap R A)) (f i * f j)) a := by
  rw [tau, awayCongrEquiv_symm]
  exact awayCongrEquiv_algebraMap I _ _ hI _ _ a

end ThreeChart

/-! ### The open cover -/

namespace ThreeChartCover

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A]
variable (f : ULift.{u} (Fin 3) → A)

/-! #### The chart identifications fix the base -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The nested chart identification fixes the image of `A`.** Proved through the top-level
`chartOverlapEquiv_apply`, so that the kernel never delta-unfolds `chartOverlapEquiv` inside a
statement about the doubly nested completion — see the cost note of
`FormalSchemes.ThreeChartCoverCharts`. -/
theorem chartOverlapEquiv_algebraMap (hI : I.FG) (i j : ULift.{u} (Fin 3)) (a : A) :
    chartOverlapEquiv I f hI i j
        (algebraMap A (awayCompletion (I.map (algebraMap R A)) (f i * f j)) a) =
      algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
        (overlapElt I f i j)) a :=
  (chartOverlapEquiv_apply I f hI i j _).trans
    (awayCompletionNestedAlgEquiv_algebraMap I hI (f i) (f i * f j) (isUnit_self_mul f i j) a)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The inverse nested chart identification fixes the image of `A`. -/
theorem chartOverlapEquiv_symm_algebraMap (hI : I.FG) (i j : ULift.{u} (Fin 3)) (a : A) :
    (chartOverlapEquiv I f hI i j).symm
        (algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
          (overlapElt I f i j)) a) =
      algebraMap A (awayCompletion (I.map (algebraMap R A)) (f i * f j)) a :=
  (AlgEquiv.symm_apply_eq _).mpr (chartOverlapEquiv_algebraMap I f hI i j a).symm

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The open cover's chart transition fixes the image of `A`.** Both legs of `tau` — the nested
chart identification and 594's comparison isomorphism downstairs — do, and this is what lets the
inverse of `f_j` supplied by the `j`-th chart be paired against `f_j` read in the `i`-th. -/
theorem tau_symm_algebraMap (hI : I.FG) (i j : ULift.{u} (Fin 3)) (a : A) :
    (tau I f hI i j).symm
        (algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f j)))
          (overlapElt I f j i)) a) =
      algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
        (overlapElt I f i j)) a := by
  rw [tau, AlgEquiv.symm_trans_apply, AlgEquiv.symm_trans_apply, AlgEquiv.symm_symm,
    chartOverlapEquiv_symm_algebraMap, ThreeChart.tau_symm_algebraMap,
    chartOverlapEquiv_algebraMap]

/-! #### The witness -/

/-- **The inverse of `f_i` inside the `i`-th chart** `A{1/f_i}`. -/
def chartInvSelf (i : ULift.{u} (Fin 3)) : chartAlgebra I f i :=
  algebraMap (Localization.Away (f i)) (chartAlgebra I f i) (IsLocalization.Away.invSelf (f i))

/-- `f_i` is inverted in its own chart. -/
theorem chartInvSelf_mul (i : ULift.{u} (Fin 3)) :
    chartInvSelf I f i * algebraMap A (chartAlgebra I f i) (f i) = 1 := by
  rw [chartInvSelf, IsScalarTower.algebraMap_apply A (Localization.Away (f i))
    (chartAlgebra I f i), ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]

variable (B : Type u) [CommRing B] [Algebra R B]

/-- **The chart codiagonal of the open cover**, in the concrete spelling of the chart algebras.

Definitionally `(datumX I f B hI).chartCodiagonal i j hij`. Giving the concrete type here is what
lets the ring identities below be *stated*: `HMul` is synthesised from the syntactic type, and the
datum spells its chart algebras through its own projections, so a product of one element in each
spelling does not elaborate even though the two types are definitionally equal. -/
def coverCodiagonal (hI : I.FG) (i j : ULift.{u} (Fin 3)) (hij : i ≠ j) :
    CompletedTensorProduct R I (chartAlgebra I f i) (chartAlgebra I f j) →+*
      awayCompletion (I.map (algebraMap R (chartAlgebra I f i))) (overlapElt I f i j) :=
  (datumX I f B hI).chartCodiagonal i j hij

/-- `chartCodiagonal_inl` at this datum, in the concrete spelling of the chart algebras. -/
theorem datumX_chartCodiagonal_inl (hI : I.FG) (i j : ULift.{u} (Fin 3)) (hij : i ≠ j)
    (c : chartAlgebra I f i) :
    coverCodiagonal I f B hI i j hij
        (CompletedTensorProduct.inl R I (chartAlgebra I f i) (chartAlgebra I f j) c) =
      algebraMap (chartAlgebra I f i)
        (awayCompletion (I.map (algebraMap R (chartAlgebra I f i))) (overlapElt I f i j)) c :=
  (datumX I f B hI).chartCodiagonal_inl i j hij c

/-- `chartCodiagonal_inr` at this datum, in the concrete spelling of the chart algebras. -/
theorem datumX_chartCodiagonal_inr (hI : I.FG) (i j : ULift.{u} (Fin 3)) (hij : i ≠ j)
    (c : chartAlgebra I f j) :
    coverCodiagonal I f B hI i j hij
        (CompletedTensorProduct.inr R I (chartAlgebra I f i) (chartAlgebra I f j) c) =
      (tau I f hI i j).symm
        (algebraMap (chartAlgebra I f j)
          (awayCompletion (I.map (algebraMap R (chartAlgebra I f j))) (overlapElt I f j i)) c) :=
  (datumX I f B hI).chartCodiagonal_inr i j hij c

/-- **The first leg inverts `f_i`**: the `i`-th chart already contains `f_i⁻¹`. -/
theorem chartCodiagonal_inl_chartInvSelf (hI : I.FG) (i j : ULift.{u} (Fin 3)) (hij : i ≠ j) :
    coverCodiagonal I f B hI i j hij
        (CompletedTensorProduct.inl R I (chartAlgebra I f i) (chartAlgebra I f j)
          (chartInvSelf I f i)) *
      algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
        (overlapElt I f i j)) (f i) = 1 := by
  rw [datumX_chartCodiagonal_inl I f B hI i j hij,
    IsScalarTower.algebraMap_apply A (chartAlgebra I f i)
      (awayCompletion (I.map (algebraMap R (chartAlgebra I f i))) (overlapElt I f i j)) (f i),
    ← map_mul, chartInvSelf_mul, map_one]

/-- **The second leg inverts `f_j`**: the `j`-th chart contains `f_j⁻¹`, and the transition carries
it to an inverse of `f_j` read in the `i`-th chart because it fixes the image of `A`
(`tau_symm_algebraMap`). This is the step that fails for a non-separated datum. -/
theorem chartCodiagonal_inr_chartInvSelf (hI : I.FG) (i j : ULift.{u} (Fin 3)) (hij : i ≠ j) :
    coverCodiagonal I f B hI i j hij
        (CompletedTensorProduct.inr R I (chartAlgebra I f i) (chartAlgebra I f j)
          (chartInvSelf I f j)) *
      algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
        (overlapElt I f i j)) (f j) = 1 := by
  have hfj : algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
        (overlapElt I f i j)) (f j) =
      (tau I f hI i j).symm
        (algebraMap (chartAlgebra I f j)
          (awayCompletion (I.map (algebraMap R (chartAlgebra I f j))) (overlapElt I f j i))
          (algebraMap A (chartAlgebra I f j) (f j))) := by
    rw [← IsScalarTower.algebraMap_apply A (chartAlgebra I f j)
      (awayCompletion (I.map (algebraMap R (chartAlgebra I f j))) (overlapElt I f j i)) (f j)]
    exact (tau_symm_algebraMap I f hI i j (f j)).symm
  rw [datumX_chartCodiagonal_inr I f B hI i j hij, hfj, ← map_mul, ← map_mul, chartInvSelf_mul,
    map_one, map_one]

/-- The image of the overlap element in the overlap chart is the product of the images of `f_i` and
`f_j`. -/
theorem algebraMap_overlapElt (i j : ULift.{u} (Fin 3)) :
    algebraMap (chartAlgebra I f i)
        (awayCompletion (I.map (algebraMap R (chartAlgebra I f i))) (overlapElt I f i j))
        (overlapElt I f i j) =
      algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
          (overlapElt I f i j)) (f i) *
        algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
          (overlapElt I f i j)) (f j) := by
  rw [← map_mul, IsScalarTower.algebraMap_apply A (chartAlgebra I f i)
    (awayCompletion (I.map (algebraMap R (chartAlgebra I f i))) (overlapElt I f i j))
    (f i * f j)]
  rfl

/-- **The witness.** `inl (f_i⁻¹) · inr (f_j⁻¹)` maps to an inverse of the overlap element: the two
factors of `g_ij = f_i·f_j` are inverted in the two *different* charts, and that is exactly what the
two legs of the chart codiagonal supply. -/
theorem chartCodiagonal_witness_mul_eq_one (hI : I.FG) (i j : ULift.{u} (Fin 3)) (hij : i ≠ j) :
    coverCodiagonal I f B hI i j hij
        (CompletedTensorProduct.inl R I (chartAlgebra I f i) (chartAlgebra I f j)
            (chartInvSelf I f i) *
          CompletedTensorProduct.inr R I (chartAlgebra I f i) (chartAlgebra I f j)
            (chartInvSelf I f j)) *
      algebraMap (chartAlgebra I f i)
        (awayCompletion (I.map (algebraMap R (chartAlgebra I f i))) (overlapElt I f i j))
        (overlapElt I f i j) = 1 := by
  rw [map_mul, algebraMap_overlapElt I f i j]
  calc coverCodiagonal I f B hI i j hij
          (CompletedTensorProduct.inl R I (chartAlgebra I f i) (chartAlgebra I f j)
            (chartInvSelf I f i)) *
        coverCodiagonal I f B hI i j hij
          (CompletedTensorProduct.inr R I (chartAlgebra I f i) (chartAlgebra I f j)
            (chartInvSelf I f j)) *
        (algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
            (overlapElt I f i j)) (f i) *
          algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
            (overlapElt I f i j)) (f j))
      = (coverCodiagonal I f B hI i j hij
            (CompletedTensorProduct.inl R I (chartAlgebra I f i) (chartAlgebra I f j)
              (chartInvSelf I f i)) *
          algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
            (overlapElt I f i j)) (f i)) *
        (coverCodiagonal I f B hI i j hij
            (CompletedTensorProduct.inr R I (chartAlgebra I f i) (chartAlgebra I f j)
              (chartInvSelf I f j)) *
          algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
            (overlapElt I f i j)) (f j)) := by ring
    _ = 1 := by
        rw [chartCodiagonal_inl_chartInvSelf I f B hI i j hij,
          chartCodiagonal_inr_chartInvSelf I f B hI i j hij, one_mul]

/-! #### The value -/

/-- **The chart codiagonals of the open cover are surjective.** -/
theorem datumX_chartCodiagonal_surjective (hI : I.FG) (i j : ULift.{u} (Fin 3)) (hij : i ≠ j) :
    Function.Surjective ((datumX I f B hI).chartCodiagonal i j hij) :=
  (datumX I f B hI).chartCodiagonal_surjective_of_mul_eq_one i j hij _
    (chartCodiagonal_witness_mul_eq_one I f B hI i j hij)

/-- **`D(f₀) ∪ D(f₁) ∪ D(f₂) ⊆ Spf A` is separated over `Spf R`** (EGA I §10.15).

The second concrete `BothChartedFibreDatumXY.IsSeparated` value in the tree after the affine one
(issue 513), and the first with more than one chart. The whole content is that the away element
`g_ij = f_i·f_j` of each overlap has its two factors inverted in the two charts being compared, so
that the chart codiagonal `A{1/f_i}^ ⊗̂_R A{1/f_j}^ → A{1/f_i}^{1/g_ij}^` is surjective; issue
778's criterion does the rest. -/
theorem datumX_isSeparated (hI : I.FG) :
    BothChartedFibreDatumXY.IsSeparated (datumX I f B hI)
      (fun i j k _ _ _ => sigma I f hI i j k)
      (fun i j k _ _ _ => sigma_tau I f hI i j k)
      (fun i j k _ _ _ => sigma_cocycle I f hI i j k) :=
  BothChartedFibreDatumXY.isSeparated_of_chartCodiagonal_surjective _ _ _ _
    (fun i j hij => datumX_chartCodiagonal_surjective I f B hI i j hij)

end ThreeChartCover

end AlgebraicGeometry

end
