import FormalSchemes.AwayCompletionSurjective
import FormalSchemes.GeneralSeparatedChartCodiagonal

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Surjectivity of the chart codiagonal of an arbitrary datum (EGA I §10.15)

`FormalSchemes/GeneralSeparatedChartCodiagonal.lean` (issue 778) reduces separatedness of a
datum-presented `X` to surjectivity of the **chart codiagonals**

```
∇_{ij} : A_i ⊗̂_R A_j ⟶ A_i{1/g_ij}^
```

— one condition per ordered pair of distinct charts, and nothing else. This file supplies the
tools an instance needs to discharge that condition, all of them stated for an **arbitrary**
`AffineChartedFibreDatumX`:

* the two leg computations, pointwise rather than as ring-hom identities;
* that `∇_{ij}` carries the ideal of definition of `A_i ⊗̂_R A_j` onto the overlap's — every
  instance needs this before it can invoke any completeness argument;
* the criterion an instance actually wants: **`∇_{ij}` is surjective as soon as some element maps
  to a multiplicative inverse of `g_ij`**, which hides both the successive-approximation argument
  (`FormalSpectrum.surjective_of_algebraMap_mem_range`) and the `IsLocalization.Away.invSelf`
  bookkeeping.

The reason the last one is the right entry point: `inl` already supplies the whole chart `A_i`, so
an inverse of `g_ij` is the *only* thing missing, and exhibiting a witness for it is a computation
inside the instance's own rings. `FormalSchemes/ThreeChartCoverSeparated.lean` (issue 779) consumes
it in three lines.

These lemmas were first proved inside `FormalSchemes/ThreeChartCoverSeparated.lean`. They live
here because they mention nothing about the three charts, and a consumer of them should not have
to build that instance's tower. Measured: this module's `FormalSchemes` import closure is **175**
modules against that file's **188**, and the three dropped are exactly `ThreeChartCoverCharts`,
`…Transitions` and `…Datum` — the first of which costs ~390 s on its own (issue 737).

Being honest about the size of that win: 13 modules is modest, and it is a *build-graph* saving,
not a memory one. Peak RSS on importing this module is ~2.9 GB against ~2.9 GB for the three-chart
file, because the floor is Mathlib's — a single Mathlib adic-completion import already costs
2.0 GB, and an empty file costs 0.76 GB. The closure also still contains issue 636's OOM-prone
`TateSelfProductDSigmaInv.lean`, inherited from `GeneralSeparatedChartCodiagonal.lean` itself;
nothing short of splitting that file removes it.

## Main results

* `AlgebraicGeometry.AffineChartedFibreDatumX.chartCodiagonal_inl` / `chartCodiagonal_inr`
* `AlgebraicGeometry.AffineChartedFibreDatumX.map_idealOfDefinition_chartCodiagonal`
* `AlgebraicGeometry.AffineChartedFibreDatumX.chartCodiagonal_surjective_of_invSelf_mem_range`
* `AlgebraicGeometry.AffineChartedFibreDatumX.chartCodiagonal_surjective_of_mul_eq_one`

## Implementation notes

Two spelling frictions inherited from issue 778, both live here:

* `AlgHom.comp_algebraMap` produces `↑a ∘ algebraMap`, which `rw` will not match against a goal
  containing `a.toRingHom.comp (algebraMap …)`; pin it as an ascribed `have`.
* `rw` cannot build a motive through `awayCompletionIdeal (I.map …)`, whose `CommRing` instance
  depends on the ideal. `map_idealOfDefinition_chartCodiagonal` is therefore a `calc` of
  `Ideal.map_map` steps and `congrArg`s rather than a `rw` chain.

A third, for anyone stating *ring* identities against a datum: an equation between the datum
spelling `DX.A i` and an instance's concrete chart algebra elaborates, since `Eq` unifies up to
definitional equality, but a **product** of one element in each does not — `HMul` is synthesised
from the syntactic type. Fix the spelling once with a `def` carrying the concrete type, and state
every identity against that.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits FormalSpectrum

universe u

namespace AlgebraicGeometry

namespace AffineChartedFibreDatumX

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {BX : Type u} [CommRing BX] [Algebra R BX]
variable (DX : AffineChartedFibreDatumX R I hI BX)

/-- The chart codiagonal on the first factor is the away-completion map, pointwise. -/
theorem chartCodiagonal_inl (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra
    ∀ c : DX.A i, DX.chartCodiagonal i j h (CompletedTensorProduct.inl R I (DX.A i) (DX.A j) c) =
      algebraMap (DX.A i) (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j)) c := by
  letI := DX.commRing; letI := DX.algebra
  exact fun c => RingHom.congr_fun (DX.chartCodiagonal_comp_inl i j h) c

/-- The chart codiagonal on the second factor is the away-completion map of the `j`-th chart read
through the datum's transition, pointwise. -/
theorem chartCodiagonal_inr (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra
    ∀ c : DX.A j, DX.chartCodiagonal i j h (CompletedTensorProduct.inr R I (DX.A i) (DX.A j) c) =
      (DX.τ i j h).symm
        (algebraMap (DX.A j) (awayCompletion (I.map (algebraMap R (DX.A j))) (DX.g j i)) c) := by
  letI := DX.commRing; letI := DX.algebra
  exact fun c => RingHom.congr_fun (DX.chartCodiagonal_comp_inr i j h) c

/-- The chart codiagonal is a map of `R`-algebras, in the composite spelling the ideal computation
below consumes. -/
theorem chartCodiagonal_comp_algebraMap (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra
    (DX.chartCodiagonal i j h).comp
        (algebraMap R (CompletedTensorProduct R I (DX.A i) (DX.A j))) =
      (awayCompletionHom (I.map (algebraMap R (DX.A i))) (DX.g i j)).comp
        (algebraMap R (DX.A i)) := by
  letI := DX.commRing; letI := DX.algebra
  have hca : (CompletedTensorProduct.inl R I (DX.A i) (DX.A j)).toRingHom.comp
      (algebraMap R (DX.A i)) =
      algebraMap R (CompletedTensorProduct R I (DX.A i) (DX.A j)) :=
    AlgHom.comp_algebraMap _
  calc (DX.chartCodiagonal i j h).comp
        (algebraMap R (CompletedTensorProduct R I (DX.A i) (DX.A j)))
      = (DX.chartCodiagonal i j h).comp
          ((CompletedTensorProduct.inl R I (DX.A i) (DX.A j)).toRingHom.comp
            (algebraMap R (DX.A i))) :=
        congrArg (fun ψ => (DX.chartCodiagonal i j h).comp ψ) hca.symm
    _ = ((DX.chartCodiagonal i j h).comp
          (CompletedTensorProduct.inl R I (DX.A i) (DX.A j)).toRingHom).comp
            (algebraMap R (DX.A i)) := (RingHom.comp_assoc _ _ _).symm
    _ = (awayCompletionHom (I.map (algebraMap R (DX.A i))) (DX.g i j)).comp
          (algebraMap R (DX.A i)) :=
        congrArg (fun ψ => RingHom.comp ψ (algebraMap R (DX.A i)))
          (DX.chartCodiagonal_comp_inl i j h)

/-- **The chart codiagonal carries the ideal of definition of `A_i ⊗̂_R A_j` onto that of the
overlap.** Both are the extension of `I`, and the codiagonal is a map of `R`-algebras. -/
theorem map_idealOfDefinition_chartCodiagonal (i j : DX.J) (h : i ≠ j) :
    letI := DX.commRing; letI := DX.algebra
    (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)).map
        (DX.chartCodiagonal i j h) =
      awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j) := by
  letI := DX.commRing; letI := DX.algebra
  calc (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j)).map
        (DX.chartCodiagonal i j h)
      = (I.map (algebraMap R (CompletedTensorProduct R I (DX.A i) (DX.A j)))).map
          (DX.chartCodiagonal i j h) := by
        rw [CompletedTensorProduct.idealOfDefinition_eq_map]
    _ = I.map ((DX.chartCodiagonal i j h).comp
          (algebraMap R (CompletedTensorProduct R I (DX.A i) (DX.A j)))) := Ideal.map_map _ _
    _ = I.map ((awayCompletionHom (I.map (algebraMap R (DX.A i))) (DX.g i j)).comp
          (algebraMap R (DX.A i))) :=
        congrArg (fun φ => Ideal.map φ I) (DX.chartCodiagonal_comp_algebraMap i j h)
    _ = (I.map (algebraMap R (DX.A i))).map
          (awayCompletionHom (I.map (algebraMap R (DX.A i))) (DX.g i j)) :=
        (Ideal.map_map _ _).symm
    _ = awayCompletionIdeal (I.map (algebraMap R (DX.A i))) (DX.g i j) :=
        map_awayCompletionHom _ _

/-- **The separatedness criterion, one pair at a time: the chart codiagonal is surjective as soon
as the inverse of the overlap element is in its image.**

The first factor already supplies the whole chart `A_i` (`chartCodiagonal_inl`), so this is the
only thing missing, and `FormalSpectrum.surjective_of_algebraMap_mem_range` closes the gap. Any
datum can consume this; for the open cover of `FormalSchemes/ThreeChartCoverDatum.lean` the witness
is the product of the two chart-local inverses of `f_i` and `f_j`. -/
theorem chartCodiagonal_surjective_of_invSelf_mem_range (i j : DX.J) (h : i ≠ j)
    (hinv : letI := DX.commRing; letI := DX.algebra
      ∃ d, DX.chartCodiagonal i j h d =
        algebraMap (Localization.Away (DX.g i j))
          (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j))
          (IsLocalization.Away.invSelf (DX.g i j))) :
    letI := DX.commRing; letI := DX.algebra
    Function.Surjective (DX.chartCodiagonal i j h) := by
  letI := DX.commRing; letI := DX.algebra
  haveI : IsPrecomplete (CompletedTensorProduct.idealOfDefinition R I (DX.A i) (DX.A j))
      (CompletedTensorProduct R I (DX.A i) (DX.A j)) :=
    (CompletedTensorProduct.isAdicRing R I (DX.A i) (DX.A j) hI).toIsAdicComplete.toIsPrecomplete
  exact FormalSpectrum.surjective_of_algebraMap_mem_range _ _ (hI.map _) _ _
    (DX.map_idealOfDefinition_chartCodiagonal i j h)
    (fun c => ⟨CompletedTensorProduct.inl R I (DX.A i) (DX.A j) c,
      DX.chartCodiagonal_inl i j h c⟩)
    hinv

/-- **The chart codiagonal is surjective as soon as some element of `A_i ⊗̂_R A_j` maps to an
inverse of the overlap element `g_ij`.** The practical form of
`chartCodiagonal_surjective_of_invSelf_mem_range`: inverses are unique, so a witness for the
multiplicative inverse of `g_ij` is a witness for `IsLocalization.Away.invSelf`. -/
theorem chartCodiagonal_surjective_of_mul_eq_one (i j : DX.J) (h : i ≠ j)
    (d : letI := DX.commRing; letI := DX.algebra
      CompletedTensorProduct R I (DX.A i) (DX.A j))
    (hd : letI := DX.commRing; letI := DX.algebra
      DX.chartCodiagonal i j h d *
        algebraMap (DX.A i) (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j))
          (DX.g i j) = 1) :
    letI := DX.commRing; letI := DX.algebra
    Function.Surjective (DX.chartCodiagonal i j h) := by
  letI := DX.commRing; letI := DX.algebra
  refine DX.chartCodiagonal_surjective_of_invSelf_mem_range i j h ⟨d, ?_⟩
  have hright : algebraMap (Localization.Away (DX.g i j))
        (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j))
        (IsLocalization.Away.invSelf (DX.g i j)) *
      algebraMap (DX.A i) (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j))
        (DX.g i j) = 1 := by
    rw [IsScalarTower.algebraMap_apply (DX.A i) (Localization.Away (DX.g i j))
      (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j)), ← map_mul, mul_comm,
      IsLocalization.Away.mul_invSelf, map_one]
  calc DX.chartCodiagonal i j h d
      = DX.chartCodiagonal i j h d *
          (algebraMap (Localization.Away (DX.g i j))
              (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j))
              (IsLocalization.Away.invSelf (DX.g i j)) *
            algebraMap (DX.A i) (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j))
              (DX.g i j)) := by rw [hright, mul_one]
    _ = (DX.chartCodiagonal i j h d *
          algebraMap (DX.A i) (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j))
            (DX.g i j)) *
        algebraMap (Localization.Away (DX.g i j))
          (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j))
          (IsLocalization.Away.invSelf (DX.g i j)) := by ring
    _ = algebraMap (Localization.Away (DX.g i j))
          (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i j))
          (IsLocalization.Away.invSelf (DX.g i j)) := by rw [hd, one_mul]

end AffineChartedFibreDatumX

end AlgebraicGeometry

end
