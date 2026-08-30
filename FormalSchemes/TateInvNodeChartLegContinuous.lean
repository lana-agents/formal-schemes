import FormalSchemes.AdicOnOpenSections
import FormalSchemes.TateInvNodeChartComplete

set_option linter.style.header false

/-!
# The node chart's four legs are adically continuous

`FormalSchemes.TateInvNodeChartComplete` (issue 1284, PR #440) reduced adic completeness of the
node chart ring to two named hypotheses. One of them,
`AlgebraicGeometry.IsTateInvNodeChartLegContinuous`, is discharged here, unconditionally:
`AlgebraicGeometry.isTateInvNodeChartLegContinuous_tateInv`.

## The route, and why the obstruction #440 recorded is not one

#440's delivery comment isolated the obstruction as *"every identification of a section ring in
this cluster goes through `FormalSpectrum.sectionsBasicOpenEquiv`, which
`FormalSchemes.Sections` states as a bare `RingEquiv`"*, and asked whether that equivalence is a
map of `R`-algebras.

**It does not have to be.** `FormalSchemes.AdicOnOpenSections` observes that the ideal of
definition of `Γ(U, O_{Spf A})` is, for *any* open `U`, the extension of `A`'s ideal of definition
along the structural map `FormalSpectrum.sectionsOpenHom` — no basic open, no completed
localization and no algebra structure enter — and that a `.c.app` commutes with those structural
maps by naturality of `w.c` along `U ⊆ ⊤`. The `sectionsBasicOpenEquiv`-shaped identifications are
then needed only to *name* the ideals in the spelling `IsTateInvNodeChartLegContinuous` uses, and
`FormalSpectrum.comap_awayCompletionIdeal_sectionsEquivOfEqBasicOpen` does that translation once.

No algebra structure is consumed anywhere. What this file actually uses from
`FormalSchemes.AdicOnBasicOpenSections` is
`FormalSpectrum.sectionsBasicOpenEquiv_comp_sectionsBasicOpenHom`, which is
`FormalSpectrum.awayCompletionHom_eq_restrict` restated with the composite named; the *ideal*
consequence `FormalSpectrum.map_sectionsBasicOpenHom` — the one flagged there as strictly weaker
than the `AlgHom` statement — enters one file back, in
`FormalSpectrum.sectionsOpenIdeal_basicOpen`.

## What is proved here

* `FormalSpectrum.sectionsEquivOfEqBasicOpen_comp_sectionsOpenHom`,
  `FormalSpectrum.map_sectionsOpenIdeal_sectionsEquivOfEqBasicOpen`,
  `FormalSpectrum.comap_awayCompletionIdeal_sectionsEquivOfEqBasicOpen` and
  `FormalSpectrum.symm_sectionsEquivOfEqBasicOpen_mem_pow` — general: an open that *happens* to be
  a basic open has `FormalSpectrum.sectionsOpenIdeal` equal to the contraction of
  `FormalSpectrum.awayCompletionIdeal` along `FormalSpectrum.sectionsEquivOfEqBasicOpen`.
* `AlgebraicGeometry.annulusOverlapInversionAlg_toRingHom`,
  `AlgebraicGeometry.annulusChartTransitionInvAlg_toRingHom_eq` and
  `AlgebraicGeometry.annulusChartTransitionInvAlg_le_comap` — the forward mirrors of
  `AlgebraicGeometry.annulusOverlapInversionAlg_symm_toRingHom`,
  `AlgebraicGeometry.annulusChartTransitionInvAlg_symm_toRingHom_eq` and
  `AlgebraicGeometry.annulusChartTransitionInvAlg_symm_le_comap`
  (`FormalSchemes.TateChartTransitionInvAlgEq`), which existed only in the `symm` direction. The
  forward direction is what the `XY` leg needs.
* `AlgebraicGeometry.tateInvNodeChartTargetIdealX_eq` and its `y`-side mirror — the two target
  ideals of `FormalSchemes.TateInvNodeChartComplete` are `FormalSpectrum.sectionsOpenIdeal` of the
  two target opens.
* The four adicity witnesses for the legs' global-sections maps
  (`AlgebraicGeometry.le_comap_globalSectionsMap_annulusOverlapChart` and its three companions),
  and the four leg-continuity statements
  (`AlgebraicGeometry.tateInvNodeChartAwayLegX_mem_pow` and its three companions).
* **`AlgebraicGeometry.isTateInvNodeChartLegContinuous_tateInv`** — the four together, which is
  `AlgebraicGeometry.IsTateInvNodeChartLegContinuous` itself. Its hypotheses are exactly those of
  the `Prop`: `[CommRing R] [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]`, `hq : q ∈ I`
  and `hI : I.FG`.
* The consequences that hypothesis unlocks in `FormalSchemes.TateInvNodeChartComplete`, restated
  without it: `AlgebraicGeometry.isAdicallyClosed_tateInvNodeChartAwaySubring'`,
  `AlgebraicGeometry.isInducedPrecomplete_tateInvNodeChartAwaySubring'` and
  `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal'`.

## What is *not* proved

* **`Subring.HasCofinalInducedFiltration` is not proved for the node chart ring**, and no
  `(A, K, S)` at which it fails is exhibited. It is the *other* hypothesis of
  `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_legContinuous`, it is untouched
  here, and `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal'` still carries it. So
  **nothing here makes the node chart ring complete**.
* **`AlgebraicGeometry.tateInvNodeChartAwayIdeal` is not shown to be finitely generated.** That is
  a separate obligation from completeness and is not implied by it, so nothing here says the chart
  ring is an adic ring in this tree's sense.
* **`FormalSpectrum.sectionsBasicOpenEquiv` is still not shown to be a map of `R`-algebras**, and
  nothing here claims it is; the route above avoids the question rather than settling it.
* **Nothing here is a chart.** No open immersion `Spf J ⟶ Q` is constructed, `hnode` is untouched,
  and no claim is made about `AlgebraicGeometry.tateInvNodeChartAmbientHom`. Nothing here says the
  chart ring is nonzero, proper, or larger than the base.

Nothing here weakens `LocallyRingedSpace.IsProperlyDiscontinuousOn`,
`LocallyRingedSpace.IsFreeProperlyDiscontinuous` or
`LocallyRingedSpace.freeActionQuotientFormalScheme`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.4, §10.4.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I]

/-!
### An open that happens to be a basic open
-/

/-- **`FormalSpectrum.sectionsEquivOfEqBasicOpen` carries the structural map of `Γ(U)` to the
structural map of `R{1/f}`.** Both are restrictions from `⊤`, so this is
`FormalSpectrum.sectionsBasicOpenEquiv_comp_sectionsBasicOpenHom`
(`FormalSchemes.AdicOnBasicOpenSections`) after the transport along `hU` has been absorbed by
`FormalSpectrum.comp_eqToHom_sectionsOpenHom`. -/
theorem sectionsEquivOfEqBasicOpen_comp_sectionsOpenHom {U : Opens (FormalSpectrum I)} {f : R}
    (hU : U = basicOpen I f) :
    (sectionsEquivOfEqBasicOpen I hU).toRingHom.comp (sectionsOpenHom I U) =
      awayCompletionHom I f := by
  rw [← sectionsBasicOpenEquiv_comp_sectionsBasicOpenHom I f, ← sectionsOpenHom_basicOpen I f,
    ← comp_eqToHom_sectionsOpenHom I hU, ← RingHom.comp_assoc]
  rfl

/-- **The ideal form of the previous theorem**: the equivalence carries
`FormalSpectrum.sectionsOpenIdeal` to `FormalSpectrum.awayCompletionIdeal`. -/
theorem map_sectionsOpenIdeal_sectionsEquivOfEqBasicOpen {U : Opens (FormalSpectrum I)} {f : R}
    (hU : U = basicOpen I f) :
    (sectionsOpenIdeal I U).map (sectionsEquivOfEqBasicOpen I hU).toRingHom =
      awayCompletionIdeal I f :=
  (Ideal.map_map (I := I) (sectionsOpenHom I U)
      (sectionsEquivOfEqBasicOpen I hU).toRingHom).trans
    ((congrArg (fun φ : R →+* awayCompletion I f => Ideal.map φ I)
      (sectionsEquivOfEqBasicOpen_comp_sectionsOpenHom I hU)).trans (map_awayCompletionHom I f))

/-- **The contraction form**, which is the spelling in which
`AlgebraicGeometry.tateInvNodeChartTargetIdealX` and
`AlgebraicGeometry.tateInvNodeChartAwayIdeal` are stated. -/
theorem comap_awayCompletionIdeal_sectionsEquivOfEqBasicOpen {U : Opens (FormalSpectrum I)}
    {f : R} (hU : U = basicOpen I f) :
    (awayCompletionIdeal I f).comap (sectionsEquivOfEqBasicOpen I hU).toRingHom =
      sectionsOpenIdeal I U :=
  (congrArg (fun K => Ideal.comap (sectionsEquivOfEqBasicOpen I hU).toRingHom K)
      (map_sectionsOpenIdeal_sectionsEquivOfEqBasicOpen I hU)).symm.trans
    (Ideal.comap_map_of_bijective (sectionsEquivOfEqBasicOpen I hU).toRingHom
      (sectionsEquivOfEqBasicOpen I hU).bijective)

/-- **Reading an element of `R{1/f}^∧`'s filtration back on the presheaf spelling.** The
`m`-th power of `FormalSpectrum.awayCompletionIdeal` pulls back along the equivalence to the
`m`-th power of `FormalSpectrum.sectionsOpenIdeal`; contraction along a ring isomorphism commutes
with powers. -/
theorem symm_sectionsEquivOfEqBasicOpen_mem_pow {U : Opens (FormalSpectrum I)} {f : R}
    (hU : U = basicOpen I f) (m : ℕ) {v : awayCompletion I f}
    (hv : v ∈ (awayCompletionIdeal I f) ^ m) :
    (sectionsEquivOfEqBasicOpen I hU).symm v ∈ (sectionsOpenIdeal I U) ^ m := by
  have hcomap : ((awayCompletionIdeal I f) ^ m).comap
      (sectionsEquivOfEqBasicOpen I hU).toRingHom = (sectionsOpenIdeal I U) ^ m := by
    rw [← map_sectionsOpenIdeal_sectionsEquivOfEqBasicOpen I hU, ← Ideal.map_pow]
    exact Ideal.comap_map_of_bijective _ (sectionsEquivOfEqBasicOpen I hU).bijective
  have hmem : (sectionsEquivOfEqBasicOpen I hU).symm v ∈
      ((awayCompletionIdeal I f) ^ m).comap (sectionsEquivOfEqBasicOpen I hU).toRingHom :=
    Ideal.mem_comap.mpr (by simpa using hv)
  exact hcomap ▸ hmem

end FormalSpectrum

namespace AlgebraicGeometry

open FormalSpectrum

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-!
### The forward direction of the inversion chart transition
-/

/-- The underlying ring hom of the `R`-algebra inversion overlap transition is the ring-level
inversion transition. The forward mirror of
`AlgebraicGeometry.annulusOverlapInversionAlg_symm_toRingHom`. -/
theorem annulusOverlapInversionAlg_toRingHom (hI : I.FG) :
    (annulusOverlapInversionAlg R I q hI).toRingHom =
      (annulusOverlapInversion R I q hI).toRingHom :=
  RingHom.ext fun _ => rfl

/-- The underlying ring hom of the `R`-algebra inversion chart transition, unfolded as the
composite `(AdicCompletion.congrIdeal _).symm ∘ annulusOverlapInversion ∘
(AdicCompletion.congrIdeal _)`. The forward mirror of
`AlgebraicGeometry.annulusChartTransitionInvAlg_symm_toRingHom_eq`; it is stated
left-associated because that is the association
`FormalSpectrum.le_comap_comp` produces. -/
theorem annulusChartTransitionInvAlg_toRingHom_eq (hI : I.FG) :
    (annulusChartTransitionInvAlg R I q hI).toRingHom =
      ((AdicCompletion.congrIdeal (annulusChartY_locIdeal_eq R I q)).symm.toRingHom.comp
          (annulusOverlapInversion R I q hI).toRingHom).comp
        (AdicCompletion.congrIdeal (annulusChart_locIdeal_eq R I q)).toRingHom := by
  rw [annulusChartTransitionInvAlg, algEquiv_trans_toRingHom, algEquiv_trans_toRingHom,
    annulusChartOverlapAlgX, annulusChartOverlapAlgY, annulusOverlapInversionAlg_toRingHom,
    AdicCompletion.congrIdealₐ_symm_toRingHom, AdicCompletion.congrIdealₐ_toRingHom]

/-- **The forward inversion chart transition carries the `x`-ideal of definition into the
`y`-ideal.** The forward mirror of
`AlgebraicGeometry.annulusChartTransitionInvAlg_symm_le_comap`, and the continuity witness the
`XY` leg needs. -/
theorem annulusChartTransitionInvAlg_le_comap (hI : I.FG) :
    awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q) ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)).comap
        (annulusChartTransitionInvAlg R I q hI).toRingHom := by
  rw [annulusChartTransitionInvAlg_toRingHom_eq]
  exact le_comap_comp _ _
    (FormalSpectrum.le_comap_congrIdeal (annulusChart_locIdeal_eq R I q))
    (le_comap_comp _ _ (annulusOverlapInversion_isAdicHom R I q hI).le_comap
      (FormalSpectrum.le_comap_congrIdeal_symm (annulusChartY_locIdeal_eq R I q)))

variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-!
### The two target ideals, on the `sectionsOpenIdeal` spelling
-/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `x`-side target ideal is `FormalSpectrum.sectionsOpenIdeal` of the `x`-side target
open.** `AlgebraicGeometry.tateInvNodeChartTargetIdealX` is by definition the contraction of
`FormalSpectrum.awayCompletionIdeal` along
`AlgebraicGeometry.tateInvNodeChartTargetEquivX`, which is
`FormalSpectrum.sectionsEquivOfEqBasicOpen` at
`AlgebraicGeometry.tateInvNodeChartTargetOpensX_eq_basicOpen`. -/
theorem tateInvNodeChartTargetIdealX_eq
    [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))] :
    tateInvNodeChartTargetIdealX R I q hq hI =
      sectionsOpenIdeal (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        ((Opens.map (annulusOverlapChart R I q).base).obj
          (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q))) :=
  FormalSpectrum.comap_awayCompletionIdeal_sectionsEquivOfEqBasicOpen _
    (tateInvNodeChartTargetOpensX_eq_basicOpen R I q hq hI)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `y`-side target ideal is `FormalSpectrum.sectionsOpenIdeal` of the `y`-side target
open.** -/
theorem tateInvNodeChartTargetIdealY_eq
    [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] :
    tateInvNodeChartTargetIdealY R I q hq hI =
      sectionsOpenIdeal (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        ((Opens.map (annulusOverlapChartY R I q).base).obj
          (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q))) :=
  FormalSpectrum.comap_awayCompletionIdeal_sectionsEquivOfEqBasicOpen _
    (tateInvNodeChartTargetOpensY_eq_basicOpen R I q hq hI)

/-!
### The four global-sections maps are adic
-/

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The `x`-chart is adic on global sections.** Its global-sections map is
`FormalSpectrum.awayCompletionHom` at `x`
(`AlgebraicGeometry.globalSectionsMap_annulusOverlapChart`), which is adic by
`FormalSpectrum.le_comap_awayCompletionHom`. -/
theorem le_comap_globalSectionsMap_annulusOverlapChart
    [IsAdicRing (annulusIdealOfDefinition R I q)]
    [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))] :
    annulusIdealOfDefinition R I q ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)).comap
        (FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _
          (annulusOverlapChart R I q)) := by
  rw [globalSectionsMap_annulusOverlapChart]
  exact FormalSpectrum.le_comap_awayCompletionHom _ _

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The `y`-chart is adic on global sections.** -/
theorem le_comap_globalSectionsMap_annulusOverlapChartY
    [IsAdicRing (annulusIdealOfDefinition R I q)]
    [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] :
    annulusIdealOfDefinition R I q ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)).comap
        (FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _
          (annulusOverlapChartY R I q)) := by
  rw [globalSectionsMap_annulusOverlapChartY]
  exact FormalSpectrum.le_comap_awayCompletionHom _ _

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The transition-then-`y`-chart composite is adic on global sections.** Its global-sections
map is `AlgebraicGeometry.tateInvGlobalLegYX`
(`AlgebraicGeometry.globalSectionsMap_transitionInv_comp_chartY`), the composite of
`FormalSpectrum.awayCompletionHom` at `y` with the inverse inversion chart transition; the second
factor is adic by `AlgebraicGeometry.annulusChartTransitionInvAlg_symm_le_comap`. -/
theorem le_comap_globalSectionsMap_transitionInv_comp_chartY
    [IsAdicRing (annulusIdealOfDefinition R I q)]
    [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))]
    [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] :
    annulusIdealOfDefinition R I q ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)).comap
        (FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _
          ((annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q)) := by
  rw [globalSectionsMap_transitionInv_comp_chartY hI, tateInvGlobalLegYX]
  exact le_comap_comp _ _ (FormalSpectrum.le_comap_awayCompletionHom _ _)
    (annulusChartTransitionInvAlg_symm_le_comap R I q hI)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The inverse-transition-then-`x`-chart composite is adic on global sections.** The mirror of
the previous theorem, using the forward
`AlgebraicGeometry.annulusChartTransitionInvAlg_le_comap`. -/
theorem le_comap_globalSectionsMap_transitionInv_inv_comp_chart
    [IsAdicRing (annulusIdealOfDefinition R I q)]
    [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))]
    [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] :
    annulusIdealOfDefinition R I q ≤
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)).comap
        (FormalSpectrum.globalSectionsMap (annulusIdealOfDefinition R I q) _
          ((annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapChart R I q)) := by
  rw [globalSectionsMap_transitionInv_inv_comp_chart hI, tateInvGlobalLegXY]
  exact le_comap_comp _ _ (FormalSpectrum.le_comap_awayCompletionHom _ _)
    (annulusChartTransitionInvAlg_le_comap R I q hI)

/-!
### The four legs
-/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `x`-chart leg is adically continuous.** It is the `.c.app` of
`annulusOverlapChart` (root namespace) at the chart's domain, precomposed with
`AlgebraicGeometry.tateInvNodeChartAmbientEquiv`'s inverse, so
`FormalSpectrum.sectionsComponent_mem_pow` applies with the adicity witness
`AlgebraicGeometry.le_comap_globalSectionsMap_annulusOverlapChart`. -/
theorem tateInvNodeChartAwayLegX_mem_pow (m : ℕ)
    {v : awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)}
    (hv : v ∈ (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) ^ m) :
    tateInvNodeChartAwayLegX R I q hq hI v ∈ tateInvNodeChartTargetIdealX R I q hq hI ^ m := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hawX : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hawY : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  rw [tateInvNodeChartTargetIdealX_eq R I q hq hI]
  exact FormalSpectrum.sectionsComponent_mem_pow (annulusIdealOfDefinition R I q) _
    (annulusOverlapChart R I q) (le_comap_globalSectionsMap_annulusOverlapChart R I q) _ m
    (FormalSpectrum.symm_sectionsEquivOfEqBasicOpen_mem_pow (annulusIdealOfDefinition R I q)
      (tateInvNodeChartOpens_eq_basicOpen R I q hq hI) m hv)

/-- **The transition-then-`y`-chart leg is adically continuous.** The same argument at the
composite morphism, followed by the `eqToHom` presheaf transport that
`AlgebraicGeometry.tateInvChartLegYX` applies, which
`FormalSpectrum.mem_pow_map_eqToHom_sectionsOpenIdeal` carries. -/
theorem tateInvNodeChartAwayLegYX_mem_pow (m : ℕ)
    {v : awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)}
    (hv : v ∈ (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) ^ m) :
    tateInvNodeChartAwayLegYX R I q hq hI v ∈ tateInvNodeChartTargetIdealX R I q hq hI ^ m := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hawX : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hawY : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  rw [tateInvNodeChartTargetIdealX_eq R I q hq hI]
  exact FormalSpectrum.mem_pow_map_eqToHom_sectionsOpenIdeal _
    (map_annulusOverlapChartY_tateInvPatchSaturateOpens
      (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q)) m
    (FormalSpectrum.sectionsComponent_mem_pow (annulusIdealOfDefinition R I q) _
      ((annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q)
      (le_comap_globalSectionsMap_transitionInv_comp_chartY R I q hI) _ m
      (FormalSpectrum.symm_sectionsEquivOfEqBasicOpen_mem_pow (annulusIdealOfDefinition R I q)
        (tateInvNodeChartOpens_eq_basicOpen R I q hq hI) m hv))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `y`-chart leg is adically continuous.** -/
theorem tateInvNodeChartAwayLegY_mem_pow (m : ℕ)
    {v : awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)}
    (hv : v ∈ (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) ^ m) :
    tateInvNodeChartAwayLegY R I q hq hI v ∈ tateInvNodeChartTargetIdealY R I q hq hI ^ m := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hawX : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hawY : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  rw [tateInvNodeChartTargetIdealY_eq R I q hq hI]
  exact FormalSpectrum.sectionsComponent_mem_pow (annulusIdealOfDefinition R I q) _
    (annulusOverlapChartY R I q) (le_comap_globalSectionsMap_annulusOverlapChartY R I q) _ m
    (FormalSpectrum.symm_sectionsEquivOfEqBasicOpen_mem_pow (annulusIdealOfDefinition R I q)
      (tateInvNodeChartOpens_eq_basicOpen R I q hq hI) m hv)

/-- **The inverse-transition-then-`x`-chart leg is adically continuous.** -/
theorem tateInvNodeChartAwayLegXY_mem_pow (m : ℕ)
    {v : awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)}
    (hv : v ∈ (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) ^ m) :
    tateInvNodeChartAwayLegXY R I q hq hI v ∈ tateInvNodeChartTargetIdealY R I q hq hI ^ m := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hawX : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hawY : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  rw [tateInvNodeChartTargetIdealY_eq R I q hq hI]
  exact FormalSpectrum.mem_pow_map_eqToHom_sectionsOpenIdeal _
    (map_annulusOverlapChart_tateInvPatchSaturateOpens
      (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q)) m
    (FormalSpectrum.sectionsComponent_mem_pow (annulusIdealOfDefinition R I q) _
      ((annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapChart R I q)
      (le_comap_globalSectionsMap_transitionInv_inv_comp_chart R I q hI) _ m
      (FormalSpectrum.symm_sectionsEquivOfEqBasicOpen_mem_pow (annulusIdealOfDefinition R I q)
        (tateInvNodeChartOpens_eq_basicOpen R I q hq hI) m hv))

/-!
### The hypothesis, discharged
-/

/-- **The node chart's four legs are adically continuous** — `1284`'s goal 2 step 2, with no
hypothesis beyond those of `AlgebraicGeometry.IsTateInvNodeChartLegContinuous` itself. -/
theorem isTateInvNodeChartLegContinuous_tateInv :
    IsTateInvNodeChartLegContinuous R I q hq hI :=
  ⟨fun m _ hv => tateInvNodeChartAwayLegX_mem_pow R I q hq hI m hv,
    fun m _ hv => tateInvNodeChartAwayLegYX_mem_pow R I q hq hI m hv,
    fun m _ hv => tateInvNodeChartAwayLegY_mem_pow R I q hq hI m hv,
    fun m _ hv => tateInvNodeChartAwayLegXY_mem_pow R I q hq hI m hv⟩

/-!
### The consequences, restated without the hypothesis
-/

/-- **The node chart ring is adically closed in `A{1/(x + y − 1)}`, unconditionally.**
`AlgebraicGeometry.isAdicallyClosed_tateInvNodeChartAwaySubring` at
`AlgebraicGeometry.isTateInvNodeChartLegContinuous_tateInv`. -/
theorem isAdicallyClosed_tateInvNodeChartAwaySubring' :
    (tateInvNodeChartAwaySubring R I q hq hI).IsAdicallyClosed
      (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) :=
  isAdicallyClosed_tateInvNodeChartAwaySubring R I q hq hI
    (isTateInvNodeChartLegContinuous_tateInv R I q hq hI)

/-- **The node chart ring is complete for the induced filtration, unconditionally.** -/
theorem isInducedPrecomplete_tateInvNodeChartAwaySubring' :
    (tateInvNodeChartAwaySubring R I q hq hI).IsInducedPrecomplete
      (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) :=
  isInducedPrecomplete_tateInvNodeChartAwaySubring R I q hq hI
    (isAdicallyClosed_tateInvNodeChartAwaySubring' R I q hq hI)

/-- **Adic completeness of the node chart ring, now conditional on the filtration bridge alone.**
`AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_legContinuous` had two hypotheses;
this has one. `Subring.HasCofinalInducedFiltration` is **not** proved for this subring — see this
file's module docstring — so this is not an unconditional completeness statement. -/
theorem isAdicComplete_tateInvNodeChartAwayIdeal'
    (hcof : (tateInvNodeChartAwaySubring R I q hq hI).HasCofinalInducedFiltration
      (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q))) :
    IsAdicComplete (tateInvNodeChartAwayIdeal R I q hq hI)
      (tateInvNodeChartAwaySubring R I q hq hI) :=
  isAdicComplete_tateInvNodeChartAwayIdeal_of_legContinuous R I q hq hI
    (isTateInvNodeChartLegContinuous_tateInv R I q hq hI) hcof

end AlgebraicGeometry

end
