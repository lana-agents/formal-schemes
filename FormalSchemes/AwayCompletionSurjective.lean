import FormalSchemes.BasicOpenChart

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Surjectivity onto a completed away localization

Let `C` be a ring, `K ⊆ C` a finitely generated ideal and `g : C`. This file proves that a
continuous ring map into the completed localization `C{1/g}^` (`FormalSpectrum.awayCompletion`) is
surjective **as soon as its image contains `C` and the inverse of `g`** — no finiteness hypothesis
on the source beyond precompleteness, and in particular no Noetherian input.

The argument is successive approximation for complete adic rings, Mathlib's
`surjective_of_mk_map_comp_surjective`: modulo the ideal of definition, `C{1/g}^` is the
localization `C̄_ḡ` of `C̄ = C ⧸ K` at `ḡ`, so the two hypotheses say the image mod `K` contains a
generating set, and the approximation lifts that to genuine surjectivity.

This is not a new argument. It is the shape `FormalSchemes/InversionCodiagonalClosedEmbedding.lean`
(issue 502) runs for the Tate annulus, mirrored in `…Y.lean` (issue 515) and again, in its
mixed-chart form, in `FormalSchemes/GraphCodiagonalClosedEmbedding.lean` (issue 529). It was stated
generically for the first time in `FormalSchemes/ThreeChartCoverSeparated.lean` (issue 779) and
lives here so that a consumer can reach it without building that instance's tower: this module's
`FormalSchemes` import closure is **17** modules against that file's **188**.

## Main results

* `FormalSpectrum.localizationAway_eq_sec`: every element of `C_g` is `c · (g⁻¹)ⁿ` at the chosen
  numerator and exponent `IsLocalization.Away.sec g`.
* `FormalSpectrum.sub_algebraMap_mem_awayCompletionIdeal`: the level-one approximation step — a
  point of `C{1/g}^` agreeing with a point of `C_g` on the first thickening differs from it by an
  element of the ideal of definition.
* `FormalSpectrum.surjective_of_algebraMap_mem_range`: the surjectivity criterion.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.14, §10.15.
* [Atiyah–Macdonald, *Introduction to Commutative Algebra*][AM], Ch. 10.
-/

noncomputable section

universe u

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

end
