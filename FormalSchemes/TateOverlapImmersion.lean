import FormalSchemes.TateOverlap
import FormalSchemes.BasicOpenImmersionLRS

set_option linter.style.header false

/-!
# The Tate-annulus overlap as an affine formal open subscheme

Fix an adic ring `R` with ideal of definition `I` and a Tate parameter `q : R`, and let
`A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus
(`FormalSchemes.TateAnnulus`). The overlap of two consecutive annulus patches `U_n`, `U_{n+1}` is
the open `V = {x invertible} ⊆ Spf A`; realising it as an *affine formal open subscheme* is the
load-bearing geometric prerequisite for assembling the Tate chain `T` as a
`FormalScheme.GlueData` (issue 134, Bosch, *Lectures on Formal and Rigid Geometry*, §9).

This file supplies that realisation, by specialising the general affine basic-open chart
(`FormalSpectrum.basicOpenChart`, upgraded to a `LocallyRingedSpace` open immersion in issue 163)
to the base ring `A` at the coordinate `x = overlapX`:

* `annulusOverlapChart`: the chart `Spf A{1/x} ⟶ Spf A` (= `Spf A|_{D(x)}`).
* `isOpenImmersion_annulusOverlapChart`: it is a `LocallyRingedSpace.IsOpenImmersion` — the
  formal-geometry analogue of `Spec A_x ≅ D(x) ⊆ Spec A`.
* `range_annulusOverlapChart_base`: its underlying-space range is the basic open `D(x) ⊆ Spf A`.

It also identifies the chart's coordinate ring `A{1/x}` with the completed localization
`A[x⁻¹]^∧ = annulusOverlap` and, through the overlap isomorphism `overlapEquiv` (issue 133), with
the restricted Laurent series ring `R{x, x⁻¹}` — the formal multiplicative group `Ĝm`:

* `awayCompletionEquivAnnulusOverlap`: `A{1/x} ≃+* A[x⁻¹]^∧`.
* `annulusOverlapChartRingEquiv`: `A{1/x} ≃+* R{x, x⁻¹}`.

This exhibits the overlap as a copy of `Ĝm`, which is what the cocycle verification of the Tate
chain consumes. Assembling the `ℤ`-indexed `FormalScheme.GlueData` (with the transition maps
`annulusOverlapTransition`, PR #37, as the `t_{ij}`) remains for the follow-up.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum TopologicalSpace

universe u

namespace AdicCompletion

variable {B : Type u} [CommRing B]

/-- Transport of an adic completion along an equality of ideals: for `K₁ = K₂` the completions
`AdicCompletion K₁ B` and `AdicCompletion K₂ B` are canonically isomorphic. -/
def congrIdeal {K₁ K₂ : Ideal B} (h : K₁ = K₂) :
    AdicCompletion K₁ B ≃+* AdicCompletion K₂ B := by
  subst h
  exact RingEquiv.refl _

end AdicCompletion

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The finitely-generated hypothesis propagates to the annulus: if `I` is finitely generated then
so is the ideal of definition `I·A` of the Tate annulus `A`. -/
theorem annulusIdealOfDefinition_fg (hI : I.FG) :
    (annulusIdealOfDefinition R I q).FG := by
  rw [← annulus_map_eq]
  exact hI.map _

/-- The affine basic-open chart of the Tate annulus at the coordinate `x`: the morphism of locally
ringed spaces `Spf A{1/x} ⟶ Spf A` realising the open `V = {x invertible} ⊆ Spf A`. -/
def annulusOverlapChart :
    locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) ⟶
      locallyRingedSpaceObj (annulusIdealOfDefinition R I q) :=
  basicOpenChart (annulusIdealOfDefinition R I q) (overlapX R I q)

/-- **The Tate-annulus overlap is an affine formal open subscheme**: the chart `Spf A{1/x} ⟶ Spf A`
is a `LocallyRingedSpace.IsOpenImmersion`, the formal-geometry analogue of
`Spec A_x ≅ D(x) ⊆ Spec A`. This is the load-bearing prerequisite for gluing the Tate chain
(issue 134). -/
theorem isOpenImmersion_annulusOverlapChart (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion (annulusOverlapChart R I q) :=
  isOpenImmersion_basicOpenChart (annulusIdealOfDefinition R I q) (overlapX R I q)
    (annulusIdealOfDefinition_fg R I q hI)

/-- The underlying-space range of the overlap chart is the basic open `D(x) ⊆ Spf A`, i.e. the
locus where the coordinate `x` is invertible. -/
theorem range_annulusOverlapChart_base (hI : I.FG) :
    Set.range (annulusOverlapChart R I q).base =
      (basicOpen (annulusIdealOfDefinition R I q) (overlapX R I q) :
        Set (FormalSpectrum (annulusIdealOfDefinition R I q))) :=
  range_basicOpenChart_base (annulusIdealOfDefinition R I q) (overlapX R I q)
    (annulusIdealOfDefinition_fg R I q hI)

/-- The ideal of definition of the chart's coordinate ring `A{1/x}`, obtained from `A`'s ideal of
definition `I·A`, agrees with the ideal `I·A[x⁻¹]` used to build the completed localization
`A[x⁻¹]^∧ = annulusOverlap`: both are `I` extended to the localization `A[x⁻¹]`. -/
theorem annulusChart_locIdeal_eq :
    (annulusIdealOfDefinition R I q).map
        (algebraMap (annulusAlgebra R I q) (annulusLoc R I q)) =
      annulusLocIdeal R I q := by
  rw [← annulus_map_eq, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q) (annulusLoc R I q)]

/-- The chart's coordinate ring `A{1/x}` is the completed localization `A[x⁻¹]^∧ = annulusOverlap`:
both are the `I`-adic completion of `A[x⁻¹]`, taken with respect to equal ideals of definition. -/
def awayCompletionEquivAnnulusOverlap :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) ≃+*
      annulusOverlap R I q :=
  AdicCompletion.congrIdeal (annulusChart_locIdeal_eq R I q)

/-- **The overlap chart's coordinate ring is the formal multiplicative group `Ĝm`**: composing the
identification `A{1/x} ≃+* A[x⁻¹]^∧` with the overlap isomorphism `overlapEquiv` (issue 133) gives
`A{1/x} ≃+* R{x, x⁻¹}`. This is the ring-level statement that the overlap `V ⊆ Spf A` is a copy of
`Ĝm`, feeding the transition maps of the Tate chain. -/
def annulusOverlapChartRingEquiv (hI : I.FG) :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) ≃+*
      RestrictedLaurentSeries R I :=
  (awayCompletionEquivAnnulusOverlap R I q).trans (overlapEquiv R I q hI)

end
