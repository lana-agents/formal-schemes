import FormalSchemes.TateChartTransition
import FormalSchemes.EmptyLocallyRingedSpace

set_option linter.style.header false

/-!
# The Tate annulus has empty doubly-invertible locus

Fix an adic base `(R, I)` with `q ∈ I` (the Tate parameter is topologically nilpotent, as it is for
the Tate curve over a complete valuation ring, where `I = (t)` and `q` is a positive power of the
uniformiser). Let `A = R{x, y}/(x·y − q)` be the coordinate ring of the formal Tate annulus. The
two overlap charts

* `annulusOverlapChart : Spf A{1/x} ⟶ Spf A`  (the locus `{x invertible}`, `D(x)`), and
* `annulusOverlapChartY : Spf A{1/y} ⟶ Spf A`  (the locus `{y invertible}`, `D(y)`)

realise the two open subsets used to glue consecutive annuli in the Tate chain. This file records
that their intersection is **empty**: since `x · y = q` and `q ∈ I` is topologically nilpotent, the
image of `x · y` in the ring of the formal spectrum `A ⧸ (I·A)` vanishes, so `D(x) ∩ D(y) = ∅`.

Geometrically this is the reason the Tate chain is a *chain*: the `{x invertible}` locus of an
annulus glues forward to the next patch and the `{y invertible}` locus glues backward to the
previous one, and these two loci are disjoint, so a patch overlaps only its two neighbours. This
disjointness is precisely what makes the cocycle condition of the ℤ-indexed
`FormalScheme.GlueData` degenerate (issue 208): the triple overlap of a patch with its two
neighbours is empty.

## Main results

* `annulusOverlap_basicOpen_disjoint`: `D(x) ⊓ D(y) = ⊥` in `Spf A` when `q ∈ I`.
* `annulusOverlapChart_range_disjoint`: the underlying-space ranges of the two overlap charts are
  disjoint.
-/

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- In `A = R{x, y}/(x·y − q)` the product of the two overlap coordinates is the image of the Tate
parameter: `x · y = q`. -/
theorem overlapX_mul_overlapY :
    overlapX R I q * overlapY R I q = algebraMap R (annulusAlgebra R I q) q :=
  annulus_coord_mul R I q

/-- The image of the Tate parameter `q` in the ring of the formal spectrum `A ⧸ (I·A)` vanishes when
`q ∈ I`, because `I·A = annulusIdealOfDefinition` is the extension of `I` and `q ∈ I`. -/
theorem mk_algebraMap_q_eq_zero (hq : q ∈ I) :
    Ideal.Quotient.mk (annulusIdealOfDefinition R I q) (algebraMap R (annulusAlgebra R I q) q)
      = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, ← annulus_map_eq]
  exact Ideal.mem_map_of_mem _ hq

/-- **The doubly-invertible locus of the Tate annulus is empty.** When the Tate parameter `q` is
topologically nilpotent (`q ∈ I`), the two overlap opens `D(x)` and `D(y)` of `Spf A` are disjoint,
because `x · y = q` maps to `0` in `A ⧸ (I·A)`. -/
theorem annulusOverlap_basicOpen_disjoint (hq : q ∈ I) :
    basicOpen (annulusIdealOfDefinition R I q) (overlapX R I q)
        ⊓ basicOpen (annulusIdealOfDefinition R I q) (overlapY R I q) = ⊥ := by
  rw [← basicOpen_mul, overlapX_mul_overlapY, basicOpen, mk_algebraMap_q_eq_zero R I q hq]
  exact PrimeSpectrum.basicOpen_zero

/-- **The two overlap charts have disjoint ranges.** The underlying-space images of
`annulusOverlapChart` (the locus `D(x)`) and `annulusOverlapChartY` (the locus `D(y)`) are disjoint
when `q ∈ I`. This is the geometric input degenerating the cocycle of the Tate chain: a patch
overlaps only its immediate neighbours. -/
theorem annulusOverlapChart_range_disjoint (hq : q ∈ I) (hI : I.FG) :
    Disjoint (Set.range (annulusOverlapChart R I q).base)
      (Set.range (annulusOverlapChartY R I q).base) := by
  rw [range_annulusOverlapChart_base R I q hI]
  rw [show annulusOverlapChartY R I q = FormalSpectrum.basicOpenChart _ (overlapY R I q) from rfl]
  rw [range_basicOpenChart_base _ (overlapY R I q) (annulusIdealOfDefinition_fg R I q hI)]
  refine Set.disjoint_iff_inter_eq_empty.mpr ?_
  rw [← TopologicalSpace.Opens.coe_inf, annulusOverlap_basicOpen_disjoint R I q hq,
    TopologicalSpace.Opens.coe_bot]

/-- **The doubly-invertible overlap of the Tate annulus is empty, as a locally ringed space.** The
fibre product `Spf A{1/x} ×_{Spf A} Spf A{1/y}` (the locus where both coordinates are invertible)
has empty carrier when `q ∈ I`. In the ℤ-indexed Tate glue datum this is the triple overlap of a
patch with its two neighbours, so it forces the cocycle condition to hold by initiality. -/
theorem isEmpty_pullback_annulusOverlapCharts (hq : q ∈ I) (hI : I.FG)
    [Limits.HasPullback (annulusOverlapChart R I q) (annulusOverlapChartY R I q)] :
    IsEmpty (Limits.pullback (annulusOverlapChart R I q) (annulusOverlapChartY R I q) :
      LocallyRingedSpace.{u}) :=
  LocallyRingedSpace.isEmpty_pullback _ _ (annulusOverlapChart_range_disjoint R I q hq hI)

/-- **The doubly-invertible overlap of the Tate annulus is initial.** Consequence of
`isEmpty_pullback_annulusOverlapCharts` via `LocallyRingedSpace.isInitialOfIsEmpty`. This is the
morphism-level input to the cocycle of the Tate chain: the triple overlaps are initial, so the
`t'`/`cocycle` fields of the ℤ-indexed glue datum are determined by initiality. -/
noncomputable def isInitialPullbackAnnulusOverlapCharts (hq : q ∈ I) (hI : I.FG)
    [Limits.HasPullback (annulusOverlapChart R I q) (annulusOverlapChartY R I q)] :
    Limits.IsInitial (Limits.pullback (annulusOverlapChart R I q) (annulusOverlapChartY R I q) :
      LocallyRingedSpace.{u}) :=
  LocallyRingedSpace.isInitialPullbackOfDisjointRange _ _
    (annulusOverlapChart_range_disjoint R I q hq hI)

end AlgebraicGeometry
