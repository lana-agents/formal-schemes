import FormalSchemes.TateSelfProductGlueDatum
import FormalSchemes.TateSelfProductTransitionRange
import FormalSchemes.TateSelfProductTransitionRangeRight
import FormalSchemes.GlueTPrimeOfLift

set_option linter.style.header false
-- The completed-tensor interchange charts range over the nested localization/completion towers of
-- the completed tensor product, which are slow for the elaborator and the kernel; raise the budgets
-- (matching `TateSelfProductGlueDatum.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The transition-of-transitions `t'` and `t_fac` of the four-chart Tate self-fibre-product glue

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. This file assembles the genuine cocycle *transition-of-transitions* fields `t'` and
`t_fac` of the eventual `CategoryTheory.GlueData' LocallyRingedSpace` on `J = Bool × Bool`
presenting `𝔈_q ×_{Spf R} 𝔈_q` (issue 301, 237 brick c2), on top of the structural skeleton
(`TateSelfProductGlueDatum`, the `V`/`f`/`t` datum) and the reusable lift-based mechanism
(`GlueTPrimeOfLift`).

## The construction route (glueTPrimeOfLift)

By the merged `glueTPrimeOfLift` mechanism (`FormalSchemes/GlueTPrimeOfLift.lean`), for charts
sharing the single target `Spf(A ⊗̂_R A)` one sets

```
t' i j k := glueTPrimeOfLift (f i j) (f i k) (f j k) (f j i) (t i j) (H i j k)
```

with `t_fac` **free** (`glueTPrimeOfLift_fac`). The only obligation per pairwise-distinct triple is
the range inclusion

```
H : range (pullback.fst (f i j) (f i k) ≫ t i j).base ⊆ range (pullback.snd (f j k) (f j i)).base .
```

Cancelling the pullback legs (`range_pullback_fst`/`range_pullback_snd`, `Set.range_comp`) reduces
`H` to the base-map/range statement

```
(t i j).base '' ( (f i j).base ⁻¹' range (f i k).base ) ⊆ (f j i).base ⁻¹' range (f j k).base .
```

## The Klein-four dispatch

`Bool × Bool` is the Klein four-group under componentwise XOR; for pairwise-distinct `i, j, k` the
three pairwise differences `{i⊕j, i⊕k, j⊕k}` are exactly the three non-zero elements, i.e. the three
overlap shapes {first, second, both} (since `first ⊕ second = both`). Writing `X = shape(i⊕j)`,
`Y = shape(i⊕k)`, `Z = shape(j⊕k)`, the reduced obligation is

```
t_X '' ( f_X ⁻¹' range f_Y ) ⊆ f_X ⁻¹' range f_Z ,   {X, Y, Z} = {first, second, both}.
```

The six orderings collapse onto the three merged range-tracking lemmas
(`TateSelfProductTransitionRange`, `...Right`): the three orderings with `Z = both` are those lemmas
verbatim; the two "swapped" orderings (`Z = second`/`first` with `Y = both`) follow from
`range f_both = range f_first ∩ range f_second` (turning `f_X ⁻¹' range f_both` into the source
region, lemmas with a `'` suffix below); and the both-source ordering `(both, second, first)` is
trivial (`range f_both ⊆ range f_first`, so the target region is `Set.univ`).

The whole dispatch is a single `Bool × Bool` case split of the reduced statement, which mentions no
`pullback` and so needs no `HasPullback`/`IsOpenImmersion` instances during the case analysis.

## Main definitions / results

* `AlgebraicGeometry.tateSelfProductGlueT'`: the lift-built transition-of-transitions.
* `AlgebraicGeometry.tateSelfProductGlueT_fac`: its `GlueData'.t_fac` compatibility (free).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* Mathlib `CategoryTheory.GlueData'` (the `t'`/`t_fac` fields).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The two "swapped" shape lemmas

The three merged range-tracking lemmas (`TateSelfProductTransitionRange`, `...Right`) cover the
three Klein-four orderings whose *third* shape is `both`. The two orderings whose third shape is a
single factor (`Y = both`) reduce to them via `range f_both = range f_first ∩ range f_second`. -/

/-- **First shape, swapped ordering** `(first, both, second)`: `tateSelfProductFirstTransition`
carries `f_first ⁻¹' range f_both` into `f_first ⁻¹' range f_second`. Since
`range f_both = range f_first ∩ range f_second`, both regions equal `f_first ⁻¹' range f_second`, so
this is the merged first-shape lemma with its `range f_both` target rewritten. -/
theorem tateSelfProductFirstTransition_image_subset' (hI : I.FG) :
    (tateSelfProductFirstTransition R I q hI).hom.base ''
        (⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (bothFactorOverlapChart R I q hI).base) ⊆
      ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (secondFactorOverlapChart R I q hI).base := by
  have hset : ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (bothFactorOverlapChart R I q hI).base =
      ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (secondFactorOverlapChart R I q hI).base := by
    rw [range_bothFactorOverlapChart_eq_inter_first_second R I q hI, Set.preimage_inter,
      Set.preimage_range, Set.univ_inter]
  rw [hset]
  calc (tateSelfProductFirstTransition R I q hI).hom.base ''
          (⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
            Set.range (secondFactorOverlapChart R I q hI).base)
      ⊆ ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (bothFactorOverlapChart R I q hI).base :=
        tateSelfProductFirstTransition_image_subset R I q hI
    _ = ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (secondFactorOverlapChart R I q hI).base := hset

/-- **Right shape, swapped ordering** `(second, both, first)`: `tateSelfProductRightTransition`
carries `f_second ⁻¹' range f_both` into `f_second ⁻¹' range f_first`. Since
`range f_both = range f_first ∩ range f_second`, both regions equal `f_second ⁻¹' range f_first`, so
this is the merged right-shape lemma with its `range f_both` target rewritten. -/
theorem tateSelfProductRightTransition_image_subset' (hI : I.FG) :
    (tateSelfProductRightTransition R I q hI).hom.base ''
        (⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (bothFactorOverlapChart R I q hI).base) ⊆
      ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (firstFactorOverlapChart R I q hI).base := by
  have hset : ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (bothFactorOverlapChart R I q hI).base =
      ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (firstFactorOverlapChart R I q hI).base := by
    rw [range_bothFactorOverlapChart_eq_inter_first_second R I q hI, Set.preimage_inter,
      Set.preimage_range, Set.inter_univ]
  rw [hset]
  calc (tateSelfProductRightTransition R I q hI).hom.base ''
          (⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
            Set.range (firstFactorOverlapChart R I q hI).base)
      ⊆ ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (bothFactorOverlapChart R I q hI).base :=
        tateSelfProductRightTransition_image_subset R I q hI
    _ = ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (firstFactorOverlapChart R I q hI).base := hset

/-- **Both shape, swapped ordering** `(both, second, first)`: `tateSelfProductBothTransition`
carries `f_both ⁻¹' range f_second` into `f_both ⁻¹' range f_first`. Trivial:
`range f_both ⊆ range f_first`
(`range_bothFactorOverlapChart_subset_first`), so the target region is all of `Set.univ`. -/
theorem tateSelfProductBothTransition_image_subset' (hI : I.FG) :
    (tateSelfProductBothTransition R I q hI).hom.base ''
        (⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (secondFactorOverlapChart R I q hI).base) ⊆
      ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (firstFactorOverlapChart R I q hI).base := by
  have huniv : ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
      Set.range (firstFactorOverlapChart R I q hI).base = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    exact fun y =>
      range_bothFactorOverlapChart_subset_first R I q hI (Set.mem_range_self y)
  rw [huniv]
  exact Set.subset_univ _

/-! ### The range inclusion `H`, dispatched by Klein-four shape -/

/-- **The reduced range inclusion** `H` for every pairwise-distinct triple: the transition `t i j`
carries the source triple-overlap region `(f i j) ⁻¹' range (f i k)` into the target region
`(f j i) ⁻¹' range (f j k)`. Proved by a single `Bool × Bool` case split dispatching each of the 24
valid triples onto one of the three merged shape lemmas (or their two swapped variants, or the
trivial both-source case). This statement mentions no `pullback`, so the case split needs no
instances. -/
theorem tateSelfProductGlueT'_range_reduced (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (tateSelfProductGlueT R I q hI i j hij).base ''
        (⇑(tateSelfProductGlueF R I q hI i j hij).base ⁻¹'
          Set.range (tateSelfProductGlueF R I q hI i k hik).base) ⊆
      ⇑(tateSelfProductGlueF R I q hI j i hij.symm).base ⁻¹'
        Set.range (tateSelfProductGlueF R I q hI j k hjk).base := by
  revert hij hik hjk
  rcases i with ⟨(_ | _), (_ | _)⟩ <;> rcases j with ⟨(_ | _), (_ | _)⟩ <;>
    rcases k with ⟨(_ | _), (_ | _)⟩ <;> intro hij hik hjk <;>
    first
      | exact absurd rfl hij
      | exact absurd rfl hik
      | exact absurd rfl hjk
      | (simp only [tateSelfProductGlueF, tateSelfProductGlueT]
         first
           | exact tateSelfProductFirstTransition_image_subset R I q hI
           | exact tateSelfProductRightTransition_image_subset R I q hI
           | exact tateSelfProductBothTransition_image_subset R I q hI
           | exact tateSelfProductFirstTransition_image_subset' R I q hI
           | exact tateSelfProductRightTransition_image_subset' R I q hI
           | exact tateSelfProductBothTransition_image_subset' R I q hI)

/-- **The range inclusion `H`** in the `pullback` form that `glueTPrimeOfLift` consumes. Reduces to
`tateSelfProductGlueT'_range_reduced` by cancelling the pullback legs
(`range_pullback_fst`/`range_pullback_snd`, `Set.range_comp`). The open-immersion instance arguments
supply the `HasPullback` instances (a pullback of an open immersion exists) needed even to state the
inclusion. -/
theorem tateSelfProductGlueT'_range (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)] :
    Set.range (pullback.fst (tateSelfProductGlueF R I q hI i j hij)
          (tateSelfProductGlueF R I q hI i k hik) ≫
        tateSelfProductGlueT R I q hI i j hij).base ⊆
      Set.range (pullback.snd (tateSelfProductGlueF R I q hI j k hjk)
        (tateSelfProductGlueF R I q hI j i hij.symm)).base := by
  rw [LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp,
    range_pullback_fst, range_pullback_snd]
  exact tateSelfProductGlueT'_range_reduced R I q hI i j k hij hik hjk

/-! ### The `t'` and `t_fac` fields -/

/-- **The transition-of-transitions** `t' i j k` of the four-chart Tate self-fibre-product glue:
the lift-built map `pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)`, whose only geometric input
is the range inclusion `tateSelfProductGlueT'_range`. This is exactly the `t'` field of the eventual
`GlueData' LocallyRingedSpace` (the open-immersion instances are supplied there by `f_hasPullback` /
`f_open`). -/
def tateSelfProductGlueT' (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)] :
    pullback (tateSelfProductGlueF R I q hI i j hij) (tateSelfProductGlueF R I q hI i k hik) ⟶
      pullback (tateSelfProductGlueF R I q hI j k hjk)
        (tateSelfProductGlueF R I q hI j i hij.symm) :=
  glueTPrimeOfLift (tateSelfProductGlueF R I q hI i j hij)
    (tateSelfProductGlueF R I q hI i k hik) (tateSelfProductGlueF R I q hI j k hjk)
    (tateSelfProductGlueF R I q hI j i hij.symm) (tateSelfProductGlueT R I q hI i j hij)
    (tateSelfProductGlueT'_range R I q hI i j k hij hik hjk)

/-- **The `t_fac` law**, for free (`glueTPrimeOfLift_fac`):
`t' i j k ≫ pullback.snd (f j k) (f j i) = pullback.fst (f i j) (f i k) ≫ t i j`. This is exactly
the `GlueData'.t_fac` field. -/
theorem tateSelfProductGlueT_fac (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)] :
    tateSelfProductGlueT' R I q hI i j k hij hik hjk ≫
        pullback.snd (tateSelfProductGlueF R I q hI j k hjk)
          (tateSelfProductGlueF R I q hI j i hij.symm) =
      pullback.fst (tateSelfProductGlueF R I q hI i j hij)
          (tateSelfProductGlueF R I q hI i k hik) ≫
        tateSelfProductGlueT R I q hI i j hij :=
  glueTPrimeOfLift_fac (tateSelfProductGlueF R I q hI i j hij)
    (tateSelfProductGlueF R I q hI i k hik) (tateSelfProductGlueF R I q hI j k hjk)
    (tateSelfProductGlueF R I q hI j i hij.symm) (tateSelfProductGlueT R I q hI i j hij)
    (tateSelfProductGlueT'_range R I q hI i j k hij hik hjk)

end AlgebraicGeometry

end
