import FormalSchemes.GeneralDiagonalUnconditional
import FormalSchemes.ClosedImmersion
import FormalSchemes.OpenCover

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Separatedness of a general formal scheme over `Spf R` (EGA I §10.15)

`FormalSchemes/GeneralDiagonalUnconditional.lean` (issue 487) built the **unconditional** general
diagonal `diagonal' : X ⟶ X ×_{Spf R} X`, but only as a morphism of *locally ringed spaces* (its
type is stated on the `.toLocallyRingedSpace` of the datum's `xGlued` and `generalFibreProduct`).
`FormalSchemes/ClosedImmersion.lean` (issue 492) introduced the reusable predicate
`FormalScheme.IsClosedImmersion` together with its local-on-target descent
`FormalScheme.isClosedImmersion_of_openCover`.

This file bridges the two into the §10.15 **separatedness** vocabulary at the scheme level:

* `schemeDiagonal'` packages `diagonal'` as an honest morphism of formal schemes
  (`FormalScheme.Hom.mk`), exactly as `FormalSchemes/AffineFibreProductScheme.lean` packages the
  affine projections/diagonal;
* `BothChartedFibreDatumXY.IsSeparated` is the property that this scheme-level diagonal is a closed
  immersion — the categorical statement that the datum-presented `X` is separated over `Spf R`;
* `isSeparated_of_diagonal_cover` reduces separatedness to a per-chart condition over the affine
  cover of the fibre product `X ×_{Spf R} X`, by instantiating the closed-immersion local-on-target
  criterion. This is the general analogue of the concrete Tate assembly (issue 425): per-chart
  closed embedding of the diagonal base together with (globally) surjective stalk maps gives a
  closed immersion, hence separatedness.

The genuine §10.15 content — verifying the per-chart hypotheses for a specific glued `X` — is left
to the consumer (the Tate curve model in issue 424/425; a general glued `X` once a
`GlueData`/`LocallyFG` → datum constructor is available). Everything here is purely additive on top
of the merged general-diagonal (487) and closed-immersion (492) infrastructure.

## Main definitions and results

* `BothChartedFibreDatumXY.schemeDiagonal'`: the general diagonal `Δ' : X ⟶ X ×_{Spf R} X` as a
  `FormalScheme.Hom`.
* `BothChartedFibreDatumXY.IsSeparated`: `X` is separated over `Spf R`, i.e. `schemeDiagonal'` is a
  `FormalScheme.IsClosedImmersion`.
* `BothChartedFibreDatumXY.isSeparated_of_diagonal_cover`: separatedness is local on the target of
  the diagonal (the affine cover of `X ×_{Spf R} X`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum Topology
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

/-- **The scheme-level general diagonal** `Δ' : X ⟶ X ×_{Spf R} X`: the unconditional diagonal
`diagonal'` (a morphism of locally ringed spaces) packaged as a morphism of formal schemes via
`FormalScheme.Hom.mk`. Its underlying locally-ringed-space morphism is `diagonal'` (definitionally),
so its base map and stalk maps are exactly those of `diagonal'`. -/
def schemeDiagonal' :
    (diagonalDatum DX σX hστX hσcX).xGlued ⟶ (diagonalDatum DX σX hστX hσcX).generalFibreProduct :=
  FormalScheme.Hom.mk (diagonal' DX σX hστX hσcX)

/-- **`X` is separated over `Spf R`** (EGA I §10.15), stated categorically: the scheme-level general
diagonal `Δ' : X ⟶ X ×_{Spf R} X` is a closed immersion of formal schemes. -/
def IsSeparated : Prop :=
  FormalScheme.IsClosedImmersion (schemeDiagonal' DX σX hστX hσcX)

/-- **Separatedness is local on the target of the diagonal.** If, over the affine cover of the fibre
product `X ×_{Spf R} X`, the diagonal base map restricts to a closed topological embedding on each
chart, and every stalk map of the diagonal is surjective, then `X` is separated over `Spf R`.

This is the general analogue of the concrete Tate assembly (issue 425): it feeds `schemeDiagonal'`
and the affine cover of `generalFibreProduct` to the closed-immersion local-on-target criterion
`FormalScheme.isClosedImmersion_of_openCover`. The hypotheses are exactly the per-chart
closed-embedding data (issue 424 for the Tate model) plus the global stalk surjectivity of the
diagonal (issue 410 for the Tate model). -/
theorem isSeparated_of_diagonal_cover
    (hbase : ∀ j, IsClosedEmbedding (Set.restrictPreimage
      (Set.range
        ((diagonalDatum DX σX hστX hσcX).generalFibreProduct.affineCover.map j).toLRSHom.base)
      (schemeDiagonal' DX σX hστX hσcX).toLRSHom.base))
    (hstalk : ∀ y,
      Function.Surjective ⇑((schemeDiagonal' DX σX hστX hσcX).toLRSHom.stalkMap y).hom) :
    IsSeparated DX σX hστX hσcX :=
  FormalScheme.isClosedImmersion_of_openCover (schemeDiagonal' DX σX hστX hσcX)
    (diagonalDatum DX σX hστX hσcX).generalFibreProduct.affineCover hbase hstalk

end BothChartedFibreDatumXY

end AlgebraicGeometry

end
