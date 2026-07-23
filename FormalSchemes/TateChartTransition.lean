import FormalSchemes.TateOverlapImmersion
import FormalSchemes.TateOverlapTransitionIso

set_option linter.style.header false

/-!
# The Tate chart transition on the annulus overlap charts

Fix an adic ring `R` with finitely generated ideal of definition `I` and a Tate parameter `q : R`,
and let `A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus with ideal of
definition `I·A`. The affine overlap chart at the coordinate `x` is the open immersion

```
annulusOverlapChart : Spf A{1/x}  ⟶  Spf A
```

(`FormalSchemes.TateOverlapImmersion`, PR #65), whose domain is the formal spectrum of the completed
localization `A{1/x} = awayCompletion (I·A) x`. Sibling issue 134a
(`FormalSchemes.TateOverlapTransitionIso`, PR #69) delivers the transition isomorphism
`annulusOverlapTransitionSpf : Spf(A[x⁻¹]^∧) ≅ Spf(A[y⁻¹]^∧)` between the *completed-localization
overlap rings* `A[x⁻¹]^∧ = annulusOverlap` and their `y`-analogue.

This file bridges the two: the chart *domain* `Spf A{1/x}` is identified with `Spf(A[x⁻¹]^∧)` — they
are the `I`-adic completion of `A[x⁻¹]` taken with *equal* ideals of definition
(`annulusChart_locIdeal_eq`) — and the transition is transported across, producing the geometric
transition between the two overlap *charts* `annulusChartTransitionSpf : Spf A{1/x} ≅ Spf A{1/y}`.

This is precisely the `t`-field datum, on the concrete chart domains, that the ℤ-indexed
`FormalScheme.GlueData` assembly of the Tate chain (issue 208 / 134b) consumes, together with the
two overlap charts `annulusOverlapChart` (`x`, PR #65) and `annulusOverlapChartY` (`y`, here) as its
`f`-fields.

## Main results

* `annulusOverlapChartY` / `isOpenImmersion_annulusOverlapChartY`: the `y`-analogue affine overlap
  chart `Spf A{1/y} ⟶ Spf A` and its open-immersion property (mirror of the `x`-chart).
* `annulusChartY_locIdeal_eq`: the `y`-analogue of `annulusChart_locIdeal_eq`.
* `FormalSpectrum.spfCongrIdeal`: for `K₁ = K₂` the formal spectra of the completions
  `AdicCompletion K₁ B`, `AdicCompletion K₂ B` are canonically isomorphic — the geometric shadow of
  `AdicCompletion.congrIdeal`.
* `annulusChartDomainSpfX` / `annulusChartDomainSpfY`: the identifications
  `Spf A{1/x} ≅ Spf(A[x⁻¹]^∧)`, `Spf A{1/y} ≅ Spf(A[y⁻¹]^∧)` of locally ringed spaces.
* `annulusChartTransitionSpf`: the geometric overlap transition `Spf A{1/x} ≅ Spf A{1/y}` on the
  overlap charts, obtained by conjugating `annulusOverlapTransitionSpf` with the two domain
  identifications.

**Scope.** This delivers, on the concrete chart domains, the `f` (both charts) and `t` (transition
iso) ingredients of the consecutive-overlap `FormalScheme.GlueData` of the Tate chain. The full
bundling — the `ℤ`-indexed `LocallyRingedSpace.GlueData` fields `f_hasPullback`, `t'`, `t_fac`,
`cocycle` (the last automatic away from adjacent pairs, where the overlaps are initial), and the
glued structural morphism `T ⟶ Spf R` — remains the work of issue 208.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4, §10.8.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory FormalSpectrum

universe u

namespace FormalSpectrum

/-- Transport of the formal spectrum along an equality of ideals: for `K₁ = K₂` the locally ringed
spaces `Spf(AdicCompletion K₁ B)` and `Spf(AdicCompletion K₂ B)` are canonically isomorphic. This is
the geometric shadow of `AdicCompletion.congrIdeal`. -/
def spfCongrIdeal {B : Type u} [CommRing B] {K₁ K₂ : Ideal B} (h : K₁ = K₂) :
    locallyRingedSpaceObj (AdicCompletion.idealOfDefinition K₁) ≅
      locallyRingedSpaceObj (AdicCompletion.idealOfDefinition K₂) := by
  subst h; exact Iso.refl _

end FormalSpectrum

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The `y`-analogue of the affine overlap chart: the morphism of locally ringed spaces
`Spf A{1/y} ⟶ Spf A` realising the open `{y invertible} ⊆ Spf A`. -/
def annulusOverlapChartY :
    locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)) ⟶
      locallyRingedSpaceObj (annulusIdealOfDefinition R I q) :=
  basicOpenChart (annulusIdealOfDefinition R I q) (overlapY R I q)

/-- **The `y`-overlap is an affine formal open subscheme**: the chart `Spf A{1/y} ⟶ Spf A` is an
open immersion, the `y`-analogue of `isOpenImmersion_annulusOverlapChart`. -/
theorem isOpenImmersion_annulusOverlapChartY (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion (annulusOverlapChartY R I q) :=
  isOpenImmersion_basicOpenChart (annulusIdealOfDefinition R I q) (overlapY R I q)
    (annulusIdealOfDefinition_fg R I q hI)

/-- The `y`-analogue of `annulusChart_locIdeal_eq`: the ideal of definition of `A{1/y}` obtained
from `A`'s ideal of definition `I·A` agrees with `I·A[y⁻¹] = annulusLocIdealY`. -/
theorem annulusChartY_locIdeal_eq :
    (annulusIdealOfDefinition R I q).map
        (algebraMap (annulusAlgebra R I q) (annulusLocY R I q)) =
      annulusLocIdealY R I q := by
  rw [← annulus_map_eq, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q) (annulusLocY R I q)]

/-- The identification `Spf A{1/x} ≅ Spf(A[x⁻¹]^∧)` of the `x`-overlap chart domain with the
completed-localization overlap ring, from the equality of ideals of definition
`annulusChart_locIdeal_eq`. -/
def annulusChartDomainSpfX :
    locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) ≅
      locallyRingedSpaceObj (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)) :=
  spfCongrIdeal (annulusChart_locIdeal_eq R I q)

/-- The identification `Spf A{1/y} ≅ Spf(A[y⁻¹]^∧)`, `y`-analogue of `annulusChartDomainSpfX`. -/
def annulusChartDomainSpfY :
    locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)) ≅
      locallyRingedSpaceObj (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q)) :=
  spfCongrIdeal (annulusChartY_locIdeal_eq R I q)

/-- **The geometric overlap transition on the annulus charts** `Spf A{1/x} ≅ Spf A{1/y}`: conjugate
the completed-localization transition `annulusOverlapTransitionSpf` (issue 134a) with the two chart
domain identifications. This is the `t_{n,n+1}` transition datum, on the concrete overlap chart
domains, consumed by the `FormalScheme.GlueData` assembly of the Tate chain (issue 208). -/
def annulusChartTransitionSpf (hI : I.FG) :
    locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) ≅
      locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)) :=
  annulusChartDomainSpfX R I q ≪≫ annulusOverlapTransitionSpf R I q hI ≪≫
    (annulusChartDomainSpfY R I q).symm

end
