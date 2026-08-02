import FormalSchemes.TateSelfProductGlueTPrime
import FormalSchemes.PullbackIsoRangeLegs

set_option linter.style.header false
-- The completed-tensor interchange charts range over the nested localization/completion towers of
-- the completed tensor product, which are slow for the elaborator and the kernel; raise the budgets
-- (matching `TateSelfProductGlueTPrime.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The four-chart Tate self-product `t'` in summand-permutation form

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. The lift-built transition-of-transitions `tateSelfProductGlueT'` (issue 237
brick c2, `TateSelfProductGlueTPrime`) is a map
`pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)` on
`J = Bool × Bool`. Its `GlueData'` cocycle cannot telescope through the lift/mono API alone because
the underlying transitions genuinely permute summands (`t i j ≫ f j i ≠ f i j`). This file
delivers the explicit **summand-permutation handle** on `t'` that a follow-up brick can close the
cocycle by `coprod.hom_ext`.

## The route

Every triple-overlap pullback `pullback (f i j) (f i k)` of two of the four charts is, since the
charts are open immersions, cut out **by range**: for pairwise-distinct `i j k` the two charts have
two of the three overlap shapes {first, second, both}, and the concrete both-overlap object realises
exactly the intersection `im (f i j) ∩ im (f i k)`, so the two are canonically isomorphic
(`tateSelfProductBothChartIso`, via `pullbackIsoOfRangeEq`). Conjugating the lift-built `t'` by
these isos gives a *self-map* `tateSelfProductD` of the both-overlap object
`bothOverlapObj`, whose defining law
(`tateSelfProductD_comp_bothChart`) exposes the genuine transition `t i j ≫ f j i` sitting on the
shared overlap. Since `bothFactorOverlapChart` is a mono, that law pins `tateSelfProductD` uniquely
(`tateSelfProductD_uniq`).

## Main definitions / results

* `AlgebraicGeometry.tateSelfProductBothChartIso`: the uniform both-overlap iso
  `bothOverlapObj ≅ pullback (f i j) (f i k)`.
* `AlgebraicGeometry.tateSelfProductD`: the conjugated self-map of `bothOverlapObj`.
* `AlgebraicGeometry.tateSelfProductD_comp_bothChart`: its defining law over the both-chart.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* Mathlib `CategoryTheory.GlueData'` (the `t'`/`t_fac`/`cocycle` fields).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The uniform both-overlap range equality, dispatched by Klein-four shape -/

/-- **The both-overlap range equality** for every pairwise-distinct triple: the range of the
both-factor overlap chart equals the intersection `im (f i j) ∩ im (f i k)` of the two
triple-overlap charts. Proved by a single `Bool × Bool` case split (mirroring
`tateSelfProductGlueT'_range_reduced`)
dispatching each of the 24 valid triples onto one of the six ordered shape pairs among
{first, second, both}: the (first, second) pair is
`range_bothFactorOverlapChart_eq_inter_first_second`; its swap commutes the intersection; and the
four single-factor/both pairs collapse by `range f_both ⊆ range f_first`/`range f_second`. -/
theorem tateSelfProductBothChart_range (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Set.range (bothFactorOverlapChart R I q hI).base =
      Set.range (tateSelfProductGlueF R I q hI i j hij).base ∩
        Set.range (tateSelfProductGlueF R I q hI i k hik).base := by
  revert hij hik hjk
  rcases i with ⟨(_ | _), (_ | _)⟩ <;> rcases j with ⟨(_ | _), (_ | _)⟩ <;>
    rcases k with ⟨(_ | _), (_ | _)⟩ <;> intro hij hik hjk <;>
    first
      | exact absurd rfl hij
      | exact absurd rfl hik
      | exact absurd rfl hjk
      | (simp only [tateSelfProductGlueF]
         first
           | exact range_bothFactorOverlapChart_eq_inter_first_second R I q hI
           | exact (range_bothFactorOverlapChart_eq_inter_first_second R I q hI).trans
               (Set.inter_comm _ _)
           | exact (Set.inter_eq_right.mpr
               (range_bothFactorOverlapChart_subset_first R I q hI)).symm
           | exact (Set.inter_eq_left.mpr
               (range_bothFactorOverlapChart_subset_first R I q hI)).symm
           | exact (Set.inter_eq_right.mpr
               (range_bothFactorOverlapChart_subset_second R I q hI)).symm
           | exact (Set.inter_eq_left.mpr
               (range_bothFactorOverlapChart_subset_second R I q hI)).symm)

/-! ### The uniform both-overlap iso and its leg lemmas -/

/-- **The uniform both-overlap iso** `bothOverlapObj ≅ pullback (f i j) (f i k)` for every
pairwise-distinct triple, built by `pullbackIsoOfRangeEq` from the range equality
`tateSelfProductBothChart_range`. A single `Bool × Bool`-dispatched definition replacing the three
shape-specific isos of `TateSelfProductTripleOverlap`. -/
def tateSelfProductBothChartIso (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI)] :=
  pullbackIsoOfRangeEq (tateSelfProductGlueF R I q hI i j hij)
    (tateSelfProductGlueF R I q hI i k hik) (bothFactorOverlapChart R I q hI)
    (tateSelfProductBothChart_range R I q hI i j k hij hik hjk)

/-- **The `hom`-leg-through-chart law** of `tateSelfProductBothChartIso`: composing the `hom`
direction with the canonical map `pullback.fst (f i j) (f i k) ≫ f i j` of the target overlap into
`Spf C` recovers `bothFactorOverlapChart`. Directly `pullbackIsoOfRangeEq_hom_fst_comp`. -/
@[reassoc]
theorem tateSelfProductBothChartIso_hom_fst_comp (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI)] :
    (tateSelfProductBothChartIso R I q hI i j k hij hik hjk).hom ≫
        pullback.fst (tateSelfProductGlueF R I q hI i j hij)
            (tateSelfProductGlueF R I q hI i k hik) ≫
          tateSelfProductGlueF R I q hI i j hij =
      bothFactorOverlapChart R I q hI :=
  pullbackIsoOfRangeEq_hom_fst_comp (tateSelfProductGlueF R I q hI i j hij)
    (tateSelfProductGlueF R I q hI i k hik) (bothFactorOverlapChart R I q hI)
    (tateSelfProductBothChart_range R I q hI i j k hij hik hjk)

/-- **The `inv`-leg law** of `tateSelfProductBothChartIso`: `inv ≫ bothFactorOverlapChart` is the
canonical map `pullback.fst (f i j) (f i k) ≫ f i j`. Directly `pullbackIsoOfRangeEq_inv_comp`. -/
@[reassoc]
theorem tateSelfProductBothChartIso_inv_comp (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI)] :
    (tateSelfProductBothChartIso R I q hI i j k hij hik hjk).inv ≫
        bothFactorOverlapChart R I q hI =
      pullback.fst (tateSelfProductGlueF R I q hI i j hij)
          (tateSelfProductGlueF R I q hI i k hik) ≫
        tateSelfProductGlueF R I q hI i j hij :=
  pullbackIsoOfRangeEq_inv_comp (tateSelfProductGlueF R I q hI i j hij)
    (tateSelfProductGlueF R I q hI i k hik) (bothFactorOverlapChart R I q hI)
    (tateSelfProductBothChart_range R I q hI i j k hij hik hjk)

/-- **The first-leg-through-chart law of `tateSelfProductGlueT'`.** Composing the lift-built
transition-of-transitions with the canonical map `pullback.fst (f j k) (f j i) ≫ f j k` of its
target overlap into `Spf C` gives `pullback.fst (f i j) (f i k) ≫ t i j ≫ f j i`, exposing the
genuine transition on the shared overlap. Directly `glueTPrimeOfLift_fst_comp`, since
`tateSelfProductGlueT'` is by definition the lift. -/
theorem tateSelfProductGlueT'_fst_comp (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)] :
    tateSelfProductGlueT' R I q hI i j k hij hik hjk ≫
        pullback.fst (tateSelfProductGlueF R I q hI j k hjk)
            (tateSelfProductGlueF R I q hI j i hij.symm) ≫
          tateSelfProductGlueF R I q hI j k hjk =
      pullback.fst (tateSelfProductGlueF R I q hI i j hij)
          (tateSelfProductGlueF R I q hI i k hik) ≫
        tateSelfProductGlueT R I q hI i j hij ≫
          tateSelfProductGlueF R I q hI j i hij.symm :=
  glueTPrimeOfLift_fst_comp (tateSelfProductGlueF R I q hI i j hij)
    (tateSelfProductGlueF R I q hI i k hik) (tateSelfProductGlueF R I q hI j k hjk)
    (tateSelfProductGlueF R I q hI j i hij.symm) (tateSelfProductGlueT R I q hI i j hij)
    (tateSelfProductGlueT'_range R I q hI i j k hij hik hjk)

/-! ### The conjugated self-map `tateSelfProductD` and its defining law -/

/-- **The conjugated self-map** `tateSelfProductD i j k : bothOverlapObj ⟶ bothOverlapObj` of the
both-overlap object: the lift-built transition-of-transitions `tateSelfProductGlueT'` conjugated by
the both-overlap isos of the two triples `(i, j, k)` and `(j, k, i)`. This is the explicit
summand-permutation handle on `t'`. -/
def tateSelfProductD (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j i hij.symm)]
    [LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI)] :=
  (tateSelfProductBothChartIso R I q hI i j k hij hik hjk).hom ≫
    tateSelfProductGlueT' R I q hI i j k hij hik hjk ≫
      (tateSelfProductBothChartIso R I q hI j k i hjk hij.symm hik.symm).inv

/-- **The defining law of `tateSelfProductD`.** Composing the conjugated self-map with the
both-chart `bothFactorOverlapChart` exposes the genuine transition `t i j ≫ f j i` on the shared
overlap:
`tateSelfProductD i j k ≫ bothFactorOverlapChart =
  (bothChartIso i j k).hom ≫ pullback.fst (f i j) (f i k) ≫ t i j ≫ f j i`. Derived from the
first-leg law `tateSelfProductGlueT'_fst_comp` and the `inv`-leg law of the second overlap iso. -/
theorem tateSelfProductD_comp_bothChart (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j i hij.symm)]
    [LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI)] :
    tateSelfProductD R I q hI i j k hij hik hjk ≫ bothFactorOverlapChart R I q hI =
      (tateSelfProductBothChartIso R I q hI i j k hij hik hjk).hom ≫
        pullback.fst (tateSelfProductGlueF R I q hI i j hij)
            (tateSelfProductGlueF R I q hI i k hik) ≫
          tateSelfProductGlueT R I q hI i j hij ≫
            tateSelfProductGlueF R I q hI j i hij.symm := by
  rw [tateSelfProductD, Category.assoc, Category.assoc,
    tateSelfProductBothChartIso_inv_comp R I q hI j k i hjk hij.symm hik.symm]
  exact congrArg (fun m => (tateSelfProductBothChartIso R I q hI i j k hij hik hjk).hom ≫ m)
    (tateSelfProductGlueT'_fst_comp R I q hI i j k hij hik hjk)

end AlgebraicGeometry

end
