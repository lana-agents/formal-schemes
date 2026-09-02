import FormalSchemes.AdicOnOpenSectionsPointwise
import FormalSchemes.TateInvNodeChartAmbient
import FormalSchemes.TateInvGlobalSections

set_option linter.style.header false

/-!
# The four legs of the chart condition on the structural image, at an arbitrary open

`FormalSchemes.TateInvChartAnnulusRing` cuts `Γ (T_inv/⟨σ⟩, π V)` out of `Γ (Spf A, S')` as the
infimum of two `RingHom.eqLocus`s, one for each of the four legs
`AlgebraicGeometry.tateInvChartLegX`, `tateInvChartLegYX`, `tateInvChartLegY`, `tateInvChartLegXY`.
`FormalSchemes.TateInvGlobalSections` computes those legs at `S = Set.univ`, where the ambient open
collapses to `⊤` and `FormalSpectrum.globalSectionsEquiv` turns the presheaf into `A` itself. This
file computes them at an **arbitrary** open `S`, on the image of the structural map
`FormalSpectrum.sectionsOpenHom`.

## What is proved

* `AlgebraicGeometry.tateInvChartLegX_sectionsOpenHom` and its three companions: each leg carries
  `sectionsOpenHom A' U a` to `sectionsOpenHom _ U' (l a)`, where `l` is the corresponding
  **ring-level** leg `AlgebraicGeometry.tateInvGlobalLegX`, `tateInvGlobalLegYX`,
  `tateInvGlobalLegY`, `tateInvGlobalLegXY` of `FormalSchemes.TateInvGlobalSections`. No glue datum
  and no presheaf survives on the right.
* `AlgebraicGeometry.sectionsOpenHom_mem_tateInvChartAnnulusSubring`: **the structural map carries
  `AlgebraicGeometry.tateInvGlobalSubring` into the chart ring, at every open `S`.** This is
  `AlgebraicGeometry.symm_algebraMap_mem_tateInvChartAnnulusSubring` (which is the `S = Set.univ`
  case, and there an `↔` through `tateInvGlobalPatchEquiv`) generalised to every `S`, in the one
  direction that survives the generalisation.
* `AlgebraicGeometry.sectionsOpenHom_algebraMap_mem_tateInvChartAnnulusSubring`: the image of the
  base ring lies in the chart ring at every `S`, with no hypothesis — the previous item at
  `AlgebraicGeometry.algebraMap_mem_tateInvGlobalSubring`.
* `AlgebraicGeometry.algebraMap_mem_tateInvNodeChartAwaySubring`: the same statement transported to
  the ambient ring `A{1/(x + y − 1)}` of the node chart, i.e.
  `algebraMap R (awayCompletion _ (annulusNodeChartCoord R I q)) r ∈ tateInvNodeChartAwaySubring`.

## The direction that is *not* available

Only `a ∈ tateInvGlobalSubring hI → sectionsOpenHom A' U a ∈ tateInvChartAnnulusSubring hS`. The
converse would need `FormalSpectrum.sectionsOpenHom` to be **injective**, which is a statement about
restriction from `⊤` to `S` and is not known on this tree for a general open. At `S = Set.univ` the
converse does hold, and that is exactly what
`AlgebraicGeometry.mem_tateInvChartAnnulusSubring_iff_mem_tateInvGlobalSubring` supplies there,
through an isomorphism rather than through `sectionsOpenHom`.

## What made the `YX` and `XY` legs hard, and where the answer lives

Those two legs are a `.c.app` **followed by an `eqToHom` presheaf transport**, and the transport is
written on `(locallyRingedSpaceObj _).presheaf` while `FormalSpectrum.comp_sectionsOpenHom` states
its equation in the pushforward spelling. Letting the two meet at these concrete rings elaborates in
under a second and then does not typecheck: the **kernel** is the cost, and no heartbeat budget
bounds it. `FormalSchemes.AdicOnOpenSectionsPointwise` is the fix — the same two statements with
their types pinned by ascription while the ring, the ideal, the morphism and the open are still
variables — and its module docstring carries the measurement. **Read it before touching the two
`congrArg` proofs below.**

## What is *not* proved here

* **Nothing about the chart ring being larger than the image of the base.** These statements are the
  trivial half in the sense of issue 1223's goal 3: they put elements *into* the chart ring.
* **No adic structure and no open immersion.** A ring is not a chart;
  `AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart` still needs both.
* **Nothing about `S` being a chart domain.** `S` is an arbitrary open throughout, and
  `AlgebraicGeometry.tateInvPatchSaturateOpens hq hI hS` is still described through the chain.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} {q : R}
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] {hq : q ∈ I} {hI : I.FG}
variable {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}

section Legs

variable [IsAdicRing (annulusIdealOfDefinition R I q)]
variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))]
variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))]

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] in
/-- **The `x`-chart leg on the structural image.** The leg is the `.c.app` of
`annulusOverlapChart` (root namespace), so this is `FormalSpectrum.sectionsOpenHom_c_app`
together with `AlgebraicGeometry.globalSectionsMap_annulusOverlapChart`. -/
theorem tateInvChartLegX_sectionsOpenHom (hS : IsOpen S) (a : annulusAlgebra R I q) :
    tateInvChartLegX (hq := hq) (hI := hI) hS
        (sectionsOpenHom (annulusIdealOfDefinition R I q)
          (tateInvPatchSaturateOpens hq hI hS) a) =
      sectionsOpenHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        ((Opens.map (annulusOverlapChart R I q).base).obj (tateInvPatchSaturateOpens hq hI hS))
        (tateInvGlobalLegX a) := by
  rw [← globalSectionsMap_annulusOverlapChart]
  exact FormalSpectrum.sectionsOpenHom_c_app _ _ (annulusOverlapChart R I q) _ a

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))] in
/-- **The `y`-chart leg on the structural image.** As for the `x`-chart leg, with
`AlgebraicGeometry.globalSectionsMap_annulusOverlapChartY`. -/
theorem tateInvChartLegY_sectionsOpenHom (hS : IsOpen S) (a : annulusAlgebra R I q) :
    tateInvChartLegY (hq := hq) (hI := hI) hS
        (sectionsOpenHom (annulusIdealOfDefinition R I q)
          (tateInvPatchSaturateOpens hq hI hS) a) =
      sectionsOpenHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        ((Opens.map (annulusOverlapChartY R I q).base).obj (tateInvPatchSaturateOpens hq hI hS))
        (tateInvGlobalLegY a) := by
  rw [← globalSectionsMap_annulusOverlapChartY]
  exact FormalSpectrum.sectionsOpenHom_c_app _ _ (annulusOverlapChartY R I q) _ a

/-- **The transition-then-`y`-chart leg on the structural image.** The leg is the `.c.app` of the
composite morphism followed by the `eqToHom` transport along
`AlgebraicGeometry.map_annulusOverlapChartY_tateInvPatchSaturateOpens`, so this is
`FormalSpectrum.sectionsOpenHom_c_app` followed by
`FormalSpectrum.eqToHom_sectionsOpenHom_apply`, with
`AlgebraicGeometry.globalSectionsMap_transitionInv_comp_chartY` naming the ring-level leg.

Both inputs are stated in the `locallyRingedSpaceObj` spelling on purpose; substituting the
pushforward-spelled `FormalSpectrum.comp_sectionsOpenHom` here makes the kernel reconcile the two
spellings at these concrete rings and it does not terminate. See
`FormalSchemes.AdicOnOpenSectionsPointwise`. -/
theorem tateInvChartLegYX_sectionsOpenHom (hS : IsOpen S) (a : annulusAlgebra R I q) :
    tateInvChartLegYX (hq := hq) (hI := hI) hS
        (sectionsOpenHom (annulusIdealOfDefinition R I q)
          (tateInvPatchSaturateOpens hq hI hS) a) =
      sectionsOpenHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        ((Opens.map (annulusOverlapChart R I q).base).obj (tateInvPatchSaturateOpens hq hI hS))
        (tateInvGlobalLegYX hI a) := by
  rw [← globalSectionsMap_transitionInv_comp_chartY hI]
  exact (congrArg (((FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
      (annulusIdealOfDefinition R I q) (overlapX R I q))).presheaf.map
        (eqToHom (congrArg op
          (map_annulusOverlapChartY_tateInvPatchSaturateOpens hS)))).hom)
    (FormalSpectrum.sectionsOpenHom_c_app _ _
      ((annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q)
      (tateInvPatchSaturateOpens hq hI hS) a)).trans
    (FormalSpectrum.eqToHom_sectionsOpenHom_apply _
      (map_annulusOverlapChartY_tateInvPatchSaturateOpens (hq := hq) (hI := hI) hS) _)

/-- **The inverse-transition-then-`x`-chart leg on the structural image.** The mirror image of
`tateInvChartLegYX_sectionsOpenHom`, along
`AlgebraicGeometry.map_annulusOverlapChart_tateInvPatchSaturateOpens` and
`AlgebraicGeometry.globalSectionsMap_transitionInv_inv_comp_chart`. -/
theorem tateInvChartLegXY_sectionsOpenHom (hS : IsOpen S) (a : annulusAlgebra R I q) :
    tateInvChartLegXY (hq := hq) (hI := hI) hS
        (sectionsOpenHom (annulusIdealOfDefinition R I q)
          (tateInvPatchSaturateOpens hq hI hS) a) =
      sectionsOpenHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        ((Opens.map (annulusOverlapChartY R I q).base).obj (tateInvPatchSaturateOpens hq hI hS))
        (tateInvGlobalLegXY hI a) := by
  rw [← globalSectionsMap_transitionInv_inv_comp_chart hI]
  exact (congrArg (((FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
      (annulusIdealOfDefinition R I q) (overlapY R I q))).presheaf.map
        (eqToHom (congrArg op
          (map_annulusOverlapChart_tateInvPatchSaturateOpens hS)))).hom)
    (FormalSpectrum.sectionsOpenHom_c_app _ _
      ((annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapChart R I q)
      (tateInvPatchSaturateOpens hq hI hS) a)).trans
    (FormalSpectrum.eqToHom_sectionsOpenHom_apply _
      (map_annulusOverlapChart_tateInvPatchSaturateOpens (hq := hq) (hI := hI) hS) _)

/-! ### The chart ring receives the global chart ring, at every open -/

/-- **The structural map carries `AlgebraicGeometry.tateInvGlobalSubring` into the chart ring**, at
every open `S`. The four leg computations turn each chart condition on `sectionsOpenHom A' U a` into
the corresponding equation in `A` transported along `sectionsOpenHom`, and the equations in `A` are
exactly membership in `tateInvGlobalSubring`.

Only this direction is available: the converse needs `FormalSpectrum.sectionsOpenHom` to be
injective, which is not known here for a general open. -/
theorem sectionsOpenHom_mem_tateInvChartAnnulusSubring (hS : IsOpen S)
    {a : annulusAlgebra R I q} (ha : a ∈ tateInvGlobalSubring hI) :
    sectionsOpenHom (annulusIdealOfDefinition R I q) (tateInvPatchSaturateOpens hq hI hS) a ∈
      tateInvChartAnnulusSubring (hq := hq) (hI := hI) hS := by
  rw [mem_tateInvGlobalSubring_iff] at ha
  refine (mem_tateInvChartAnnulusSubring_iff hS _).2 ⟨?_, ?_⟩
  · exact ((tateInvChartLegX_sectionsOpenHom hS a).trans (congrArg _ ha.1)).trans
      (tateInvChartLegYX_sectionsOpenHom hS a).symm
  · exact ((tateInvChartLegY_sectionsOpenHom hS a).trans (congrArg _ ha.2)).trans
      (tateInvChartLegXY_sectionsOpenHom hS a).symm

/-- **The image of the base ring lies in the chart ring, at every open `S`**, with no hypothesis
beyond the standing ones. The previous theorem at
`AlgebraicGeometry.algebraMap_mem_tateInvGlobalSubring`.

`AlgebraicGeometry.symm_algebraMap_mem_tateInvChartAnnulusSubring`
(`FormalSchemes.TateInvGlobalSections`) is the `S = Set.univ` case, stated through
`AlgebraicGeometry.tateInvGlobalPatchEquiv` because the ambient open collapses there. -/
theorem sectionsOpenHom_algebraMap_mem_tateInvChartAnnulusSubring (hS : IsOpen S) (r : R) :
    sectionsOpenHom (annulusIdealOfDefinition R I q) (tateInvPatchSaturateOpens hq hI hS)
        (algebraMap R (annulusAlgebra R I q) r) ∈
      tateInvChartAnnulusSubring (hq := hq) (hI := hI) hS :=
  sectionsOpenHom_mem_tateInvChartAnnulusSubring hS (algebraMap_mem_tateInvGlobalSubring hI r)

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] in
/-- **The identification of the node chart's ambient ring carries the structural image of `R` to
`algebraMap R (A{1/(x + y − 1)})`.** `AlgebraicGeometry.tateInvNodeChartAmbientEquiv` is
`FormalSpectrum.sectionsEquivOfEqBasicOpen` at
`AlgebraicGeometry.tateInvNodeChartOpens_eq_basicOpen`, so this is
`FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom` followed by
`FormalSpectrum.awayCompletionHom_comp_algebraMap`. -/
theorem tateInvNodeChartAmbientEquiv_sectionsOpenHom_algebraMap (r : R) :
    tateInvNodeChartAmbientEquiv R I q hq hI
        (sectionsOpenHom (annulusIdealOfDefinition R I q)
          (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q))
          (algebraMap R (annulusAlgebra R I q) r)) =
      algebraMap R
        (awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) r := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  rw [tateInvNodeChartAmbientEquiv, FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom]
  exact congrArg (fun φ : R →+* _ => φ r)
    (FormalSpectrum.awayCompletionHom_comp_algebraMap (R := R) (annulusNodeChartCoord R I q))

end Legs

/-! ### The node chart, in the `A{1/(x + y − 1)}` spelling -/

/-- **The image of the base ring lies in the node chart's candidate ring**, in the spelling that
displays that ring inside `A{1/(x + y − 1)}`. This discharges the membership hypothesis that
`FormalSchemes.TateInvNodeChartPrincipal` carries, unconditionally and at every base.

`AlgebraicGeometry.tateInvNodeChartAwaySubring` is the image of
`AlgebraicGeometry.tateInvNodeChartSubring` under
`AlgebraicGeometry.tateInvNodeChartAmbientEquiv`, so `Subring.mem_map` reduces the statement to
`sectionsOpenHom_algebraMap_mem_tateInvChartAnnulusSubring` at the node chart's open together with
`tateInvNodeChartAmbientEquiv_sectionsOpenHom_algebraMap`. -/
theorem algebraMap_mem_tateInvNodeChartAwaySubring (r : R) :
    algebraMap R
        (awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) r ∈
      tateInvNodeChartAwaySubring R I q hq hI := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hawX : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hawY : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  exact Subring.mem_map.2
    ⟨sectionsOpenHom (annulusIdealOfDefinition R I q)
        (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q))
        (algebraMap R (annulusAlgebra R I q) r),
      sectionsOpenHom_algebraMap_mem_tateInvChartAnnulusSubring _ r,
      tateInvNodeChartAmbientEquiv_sectionsOpenHom_algebraMap (hq := hq) (hI := hI) r⟩

end AlgebraicGeometry
