import FormalSchemes.GeneralSeparatedChartCodiagonal
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

The step from "the image contains a generating set" to "the map is surjective" is successive
approximation for complete adic rings (`surjective_of_mk_map_comp_surjective`), in the shape
`FormalSchemes/InversionCodiagonalClosedEmbedding.lean` (issue 502) uses for the Tate annulus. It
is generalised here — `FormalSpectrum.surjective_of_algebraMap_mem_range` — so that it is stated
once for an arbitrary continuous map into an arbitrary away completion, rather than a fourth time
for a concrete one.

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

* `FormalSpectrum.surjective_of_algebraMap_mem_range`: a continuous map into an away completion
  `C{1/g}^` is surjective as soon as its image contains `C` and the inverse of `g`.
* `AlgebraicGeometry.AffineChartedFibreDatumX.map_idealOfDefinition_chartCodiagonal`: the chart
  codiagonal carries the ideal of definition onto the overlap's.
* `AlgebraicGeometry.AffineChartedFibreDatumX.chartCodiagonal_surjective_of_invSelf_mem_range` and
  `chartCodiagonal_surjective_of_mul_eq_one`: **for any datum**, the chart codiagonal is surjective
  as soon as some element maps to an inverse of `g_ij`.
* `AlgebraicGeometry.ThreeChartCover.tau_symm_algebraMap`: the open cover's transition fixes the
  image of `A`.
* `AlgebraicGeometry.ThreeChartCover.chartCodiagonal_witness_mul_eq_one`: the witness
  `inl (f_i⁻¹) · inr (f_j⁻¹)`.
* `AlgebraicGeometry.ThreeChartCover.datumX_chartCodiagonal_surjective`: the chart codiagonals of
  the open cover are surjective.
* `AlgebraicGeometry.ThreeChartCover.datumX_isSeparated`: **`D(f₀) ∪ D(f₁) ∪ D(f₂)` is separated
  over `Spf R`.**

## Implementation notes

The cost note of `FormalSchemes/ThreeChartCoverCharts.lean` is in force: `chartOverlapEquiv` must
never be delta-unfolded by the kernel inside a statement about the doubly nested completion. It is
not here — `chartOverlapEquiv_algebraMap` consumes the top-level `chartOverlapEquiv_apply` exactly
as that file intends, and the module costs seconds.

Two spelling frictions inherited from issue 778, both hit here:

* `AlgHom.comp_algebraMap` produces `↑a ∘ algebraMap`, which `rw` will not match against a goal
  containing `a.toRingHom.comp (algebraMap …)`; pin it as an ascribed `have`.
* `rw` cannot build a motive through `awayCompletionIdeal (I.map …)`, whose `CommRing` instance
  depends on the ideal. `map_idealOfDefinition_chartCodiagonal` is therefore a `calc` of
  `Ideal.map_map` steps and `congrArg`s rather than a `rw` chain.

And one that is specific to writing *ring* identities against a datum: an equation between the two
spellings of a chart algebra elaborates (`Eq` unifies up to definitional equality), but a
**product** of one element in each does not — `HMul` is synthesised from the syntactic type, and
`(datumX …).A i` is not syntactically `chartAlgebra I f i`. `coverCodiagonal` exists solely to fix
the spelling once, and every identity below is stated against it.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange

universe u

/-! ### Surjectivity onto an away completion -/

namespace FormalSpectrum

variable {C : Type u} [CommRing C] (K : Ideal C) (g : C)

/-- Every element of the away localization `C_g` is `c · (g⁻¹)ⁿ` for the chosen numerator and
exponent `(c, n) = IsLocalization.Away.sec g w`. -/
theorem localizationAway_eq_sec (w : Localization.Away g) :
    w = algebraMap C (Localization.Away g) (IsLocalization.Away.sec g w).1 *
      IsLocalization.Away.invSelf g ^ (IsLocalization.Away.sec g w).2 := by
  have hpow : (algebraMap C (Localization.Away g) (g ^ (IsLocalization.Away.sec g w).2))
      * IsLocalization.Away.invSelf g ^ (IsLocalization.Away.sec g w).2 = 1 := by
    rw [map_pow, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]
  have hs := IsLocalization.Away.sec_spec g w
  calc w = w * ((algebraMap C (Localization.Away g) (g ^ (IsLocalization.Away.sec g w).2))
              * IsLocalization.Away.invSelf g ^ (IsLocalization.Away.sec g w).2) := by
          rw [hpow, mul_one]
    _ = (w * algebraMap C (Localization.Away g) (g ^ (IsLocalization.Away.sec g w).2))
          * IsLocalization.Away.invSelf g ^ (IsLocalization.Away.sec g w).2 := by ring
    _ = _ := by rw [hs]

/-- **The level-one approximation step.** If a point `y` of the completion `C{1/g}` and the image
of a point `w` of the localization `C_g` have the same first thickening, they differ by an element
of the ideal of definition. -/
theorem sub_algebraMap_mem_awayCompletionIdeal (hK : K.FG)
    (y : awayCompletion K g) (w : Localization.Away g)
    (hw : Ideal.Quotient.mk ((K.map (algebraMap C (Localization.Away g))) ^ 1) w =
      AdicCompletion.evalₐ (K.map (algebraMap C (Localization.Away g))) 1 y) :
    y - algebraMap (Localization.Away g) (awayCompletion K g) w ∈ awayCompletionIdeal K g := by
  have hof : algebraMap (Localization.Away g) (awayCompletion K g) w =
      AdicCompletion.of (K.map (algebraMap C (Localization.Away g))) (Localization.Away g) w := by
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hev : AdicCompletion.evalₐ (K.map (algebraMap C (Localization.Away g))) 1
      (y - algebraMap (Localization.Away g) (awayCompletion K g) w) = 0 := by
    rw [map_sub, sub_eq_zero, hof, AdicCompletion.evalₐ_of, hw]
  have hmem : y - algebraMap (Localization.Away g) (awayCompletion K g) w ∈
      RingHom.ker
        (AdicCompletion.evalₐ (K.map (algebraMap C (Localization.Away g))) 1).toRingHom :=
    RingHom.mem_ker.mpr hev
  rwa [AdicCompletion.ker_evalₐ _ (hK.map _) 1, pow_one] at hmem

/-- **A continuous map into an away completion is surjective as soon as its image contains the
base ring and the inverse of the away element.**

Modulo the ideal of definition `C{1/g}` is the localization `C̄_ḡ` of `C̄ = C/K` at `ḡ`; the two
hypotheses say the image mod `K` contains `C̄` and `ḡ⁻¹`, hence all of `C̄_ḡ`, and successive
approximation for complete adic rings (`surjective_of_mk_map_comp_surjective`) lifts that to
surjectivity. This is the argument `FormalSchemes/InversionCodiagonalClosedEmbedding.lean` (issue
502) runs for the Tate annulus, stated once for an arbitrary source. -/
theorem surjective_of_algebraMap_mem_range (hK : K.FG)
    {D : Type u} [CommRing D] (J : Ideal D) [IsPrecomplete J D] (φ : D →+* awayCompletion K g)
    (hJ : J.map φ = awayCompletionIdeal K g)
    (hbase : ∀ c : C, ∃ d, φ d = algebraMap C (awayCompletion K g) c)
    (hinv : ∃ d, φ d =
      algebraMap (Localization.Away g) (awayCompletion K g) (IsLocalization.Away.invSelf g)) :
    Function.Surjective φ := by
  haveI : IsAdicRing (awayCompletionIdeal K g) := AdicCompletion.isAdicRing_map _ (hK.map _)
  haveI : IsHausdorff (J.map φ) (awayCompletion K g) := by
    rw [hJ]
    exact (inferInstance : IsAdicComplete (awayCompletionIdeal K g)
      (awayCompletion K g)).toIsHausdorff
  refine _root_.surjective_of_mk_map_comp_surjective (I := J) (f := φ) ?_
  intro ybar
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective ybar
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (K.map (algebraMap C (Localization.Away g))) 1 y)
  obtain ⟨d, hd⟩ := hbase (IsLocalization.Away.sec g w).1
  obtain ⟨e, he⟩ := hinv
  refine ⟨d * e ^ (IsLocalization.Away.sec g w).2, ?_⟩
  have hφ : φ (d * e ^ (IsLocalization.Away.sec g w).2) =
      algebraMap (Localization.Away g) (awayCompletion K g) w := by
    rw [map_mul, map_pow, hd, he, ← map_pow,
      IsScalarTower.algebraMap_apply C (Localization.Away g) (awayCompletion K g), ← map_mul,
      ← localizationAway_eq_sec]
  rw [RingHom.coe_comp, Function.comp_apply, Ideal.Quotient.mk_eq_mk_iff_sub_mem, hJ, hφ]
  have hneg := neg_mem (sub_algebraMap_mem_awayCompletionIdeal K g hK y w hw)
  rwa [neg_sub] at hneg

end FormalSpectrum

/-! ### The comparison maps fix the base -/

namespace CompletedTensorAwayInterchange

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A : Type u} [CommRing A] [Algebra R A]

/-- **The comparison map `A{1/x} →ₐ[R] A{1/y}` fixes the image of `A`** — it is the completion of
an `A`-compatible localization map. -/
theorem awayCongrHom_algebraMap (x y : A) (hI : I.FG)
    (hxy : IsUnit (algebraMap A (Localization.Away y) x)) (a : A) :
    awayCongrHom I x y hI hxy (algebraMap A (awayCompletion (I.map (algebraMap R A)) x) a) =
      algebraMap A (awayCompletion (I.map (algebraMap R A)) y) a :=
  furtherLocAlgHom_algebraMap I x y hI _ _ a

/-- **The comparison isomorphism fixes the image of `A`.** -/
theorem awayCongrEquiv_algebraMap (x y : A) (hI : I.FG)
    (hxy : IsUnit (algebraMap A (Localization.Away y) x))
    (hyx : IsUnit (algebraMap A (Localization.Away x) y)) (a : A) :
    awayCongrEquiv I x y hI hxy hyx
        (algebraMap A (awayCompletion (I.map (algebraMap R A)) x) a) =
      algebraMap A (awayCompletion (I.map (algebraMap R A)) y) a :=
  awayCongrHom_algebraMap I x y hI hxy a

end CompletedTensorAwayInterchange

namespace AlgebraicGeometry

/-! ### The chart codiagonal of an arbitrary datum -/

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

/-- The inverse nested chart identification fixes the image of `A`. -/
theorem chartOverlapEquiv_symm_algebraMap (hI : I.FG) (i j : ULift.{u} (Fin 3)) (a : A) :
    (chartOverlapEquiv I f hI i j).symm
        (algebraMap A (awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
          (overlapElt I f i j)) a) =
      algebraMap A (awayCompletion (I.map (algebraMap R A)) (f i * f j)) a :=
  (AlgEquiv.symm_apply_eq _).mpr (chartOverlapEquiv_algebraMap I f hI i j a).symm

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
