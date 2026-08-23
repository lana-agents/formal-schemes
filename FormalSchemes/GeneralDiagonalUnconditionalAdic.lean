import FormalSchemes.GeneralDiagonalUnconditional
import FormalSchemes.GeneralFibreProductLiftAdic

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The unconditional diagonal is the adic-over-base `fibreLift` at the identity legs

`FormalSchemes.GeneralFibreProductLiftAdic` generalises `GeneralDiagonalUnconditional.lean`'s
construction from the diagonal's identity legs to an arbitrary source. This file records the
**faithfulness check** for that generalisation: the merged `diagonal'` *is* `fibreLiftAdic` at
`Z := xGlued`, `a = b = 𝟙`, `s := xStructMap`.

Nothing depends on this. It is here so that the generalisation cannot silently have weakened
anything: if a field of `BothRefinedChart` or a component of `refinedStructHomOf` had needed the
identity legs, the two would not be definitionally equal and this file would not compile.

The proof is `rfl`, and the reason it is is worth stating, because it is not obvious that a
`Classical.choice` can be compared with a *different* `Classical.choice`. Both chart families are
`Nonempty.some` of a subtype, and at the specialisation the two subtypes are **syntactically the
same type**: `{ chart : BothRefinedChart D 𝟙 𝟙 z // I ≤ chart.J.comap (Γ (chart.map ≫ 𝟙 ≫
D.xStructMap)) }`. The two `Nonempty` proofs then differ only as proofs of the same `Prop`, so
proof irrelevance makes the two `Classical.choice` applications definitionally equal, and the
remaining arguments of `fibreLiftOf` (`hcomm`, `hs`) are proofs too.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

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

/-- **The unconditional diagonal is the adic-over-base mediating morphism of the identity pair.**
The faithfulness check on the generalisation of `GeneralDiagonalUnconditional.lean` to an arbitrary
source; see the module docstring for why this is `rfl`. -/
theorem diagonal'_eq_fibreLiftAdic :
    diagonal' DX σX hστX hσcX =
      (diagonalDatum DX σX hστX hσcX).fibreLiftAdic
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (𝟙 (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
        (diagonalDatum DX σX hστX hσcX).xStructMap
        (adicOverBase_xStructMap (diagonalDatum DX σX hστX hσcX))
        (Category.id_comp _)
        (ofFactors_hV DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_hf DX DX σX σX hστX hστX hσcX hσcX)
        (ofFactors_ht DX DX σX σX hστX hστX hσcX hσcX)
        rfl :=
  rfl

end BothChartedFibreDatumXY

end AlgebraicGeometry

end
