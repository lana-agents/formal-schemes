import FormalSchemes.TateSelfProductTripleOverlap
import FormalSchemes.TateSelfProductTransition

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The glue-datum skeleton of the four-chart Tate self-fibre-product

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. The self fibre-product `𝔈_q ×_{Spf R} 𝔈_q` of the two-chart Tate curve model is a
**four-chart** glue whose charts are four copies of `Spf C` indexed by `Bool × Bool`. This file
assembles the eight *structural* fields of the eventual `GlueData' LocallyRingedSpace`
of that glue — namely `V`, `f`, `t` together with the discharged laws `f_mono`, `f_hasPullback`,
`t_inv` — as reusable named definitions plus their structural lemmas.

The remaining `t'`/`t_fac`/`cocycle` fields carry the genuine cocycle content and are a
separate later brick; they are **not** built here.

For distinct charts `i j : Bool × Bool` the *difference type* determines the overlap datum:

* first coordinate differs only (`i.1 ≠ j.1`, `i.2 = j.2`): the object is the first-factor overlap
  object `Spf(A{1/x} ⊗̂ A) ⨿ Spf(A{1/y} ⊗̂ A)`, the chart `firstFactorOverlapChart`, and the
  transition `tateSelfProductFirstTransition`;
* second coordinate differs only (`i.1 = j.1`, `i.2 ≠ j.2`): `secondFactorOverlapChart` /
  `tateSelfProductRightTransition`;
* both coordinates differ: `bothFactorOverlapChart` / `tateSelfProductBothTransition`.

The three families are dispatched by an explicit 16-way match on the two chart values, so that
`V i j` and `V j i` reduce to the *same* concrete object definitionally (required for the transition
`t i j : V i j h ⟶ V j i h.symm` to typecheck), exactly as in the two-patch template
`AlgebraicGeometry.tateTwoPatchGlueData'`.

## Main definitions

* `AlgebraicGeometry.tateSelfProductGlueV`: the overlap objects `V i j h`.
* `AlgebraicGeometry.tateSelfProductGlueF`: the overlap charts `f i j h : V i j h ⟶ Spf C`.
* `AlgebraicGeometry.tateSelfProductGlueT`: the overlap transitions `t i j h`.

## Main results

* `AlgebraicGeometry.tateSelfProductGlueF_mono`: each overlap chart is a monomorphism.
* `AlgebraicGeometry.tateSelfProductGlueF_hasPullback`: the triple-overlap pullbacks exist.
* `AlgebraicGeometry.tateSelfProductGlueT_inv`: each transition is its own inverse.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The common chart and the three overlap objects

The overlap objects below are reconstructed so that they are definitionally equal to the domains of
the three overlap charts of `TateSelfProductTripleOverlap` and to the (co)domains of the three
transition isomorphisms of `TateSelfProductTransition`. -/

/-- `Spf(A ⊗̂_R A)`, the common chart `U` of the four-chart glue (each of the four charts is a copy
of it). -/
private abbrev tateSelfProductGlueU : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj
    (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))

/-- `A{1/x}`, the completed localisation of the annulus algebra at the first coordinate. -/
private abbrev awayXCompletion : Type u :=
  awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)

/-- `A{1/y}`, the completed localisation of the annulus algebra at the second coordinate. -/
private abbrev awayYCompletion : Type u :=
  awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)

/-- The first-factor overlap object `Spf(A{1/x} ⊗̂_R A) ⨿ Spf(A{1/y} ⊗̂_R A)`, the domain of
`firstFactorOverlapChart` and the (co)domain of `tateSelfProductFirstTransition`. -/
private abbrev firstOverlapObj : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
      (awayXCompletion R I q) (annulusAlgebra R I q)) ⨿
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
      (awayYCompletion R I q) (annulusAlgebra R I q))

/-- The second-factor overlap object `Spf(A ⊗̂_R A{1/x}) ⨿ Spf(A ⊗̂_R A{1/y})`, the domain of
`secondFactorOverlapChart` and the (co)domain of `tateSelfProductRightTransition`. -/
private abbrev secondOverlapObj : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
      (annulusAlgebra R I q) (awayXCompletion R I q)) ⨿
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
      (annulusAlgebra R I q) (awayYCompletion R I q))

/-- The both-factor overlap object
`(Spf(A{1/x} ⊗̂ A{1/x}) ⨿ Spf(A{1/x} ⊗̂ A{1/y})) ⨿ (Spf(A{1/y} ⊗̂ A{1/x}) ⨿ Spf(A{1/y} ⊗̂ A{1/y}))`,
the domain of `bothFactorOverlapChart` and the (co)domain of `tateSelfProductBothTransition`. -/
private abbrev bothOverlapObj : LocallyRingedSpace.{u} :=
  (locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayXCompletion R I q) (awayXCompletion R I q)) ⨿
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayXCompletion R I q) (awayYCompletion R I q))) ⨿
    (locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayYCompletion R I q) (awayXCompletion R I q)) ⨿
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayYCompletion R I q) (awayYCompletion R I q)))

/-! ### The `V`/`f`/`t` datum -/

/-- **The overlap objects** `V i j h` of the four-chart Tate self-fibre-product glue: for distinct
charts `i j : Bool × Bool` the object is the first-, second- or both-factor overlap object according
to the difference type of `i` and `j`. Defined by an explicit 16-way match so that `V i j` and
`V j i` reduce to the same concrete object definitionally. -/
def tateSelfProductGlueV (_hI : I.FG) :
    ∀ (i j : Bool × Bool), i ≠ j → LocallyRingedSpace.{u} :=
  fun i j h => match i, j, h with
  | (false, false), (false, false), h => (h rfl).elim
  | (false, false), (false, true), _ => secondOverlapObj R I q
  | (false, false), (true, false), _ => firstOverlapObj R I q
  | (false, false), (true, true), _ => bothOverlapObj R I q
  | (false, true), (false, false), _ => secondOverlapObj R I q
  | (false, true), (false, true), h => (h rfl).elim
  | (false, true), (true, false), _ => bothOverlapObj R I q
  | (false, true), (true, true), _ => firstOverlapObj R I q
  | (true, false), (false, false), _ => firstOverlapObj R I q
  | (true, false), (false, true), _ => bothOverlapObj R I q
  | (true, false), (true, false), h => (h rfl).elim
  | (true, false), (true, true), _ => secondOverlapObj R I q
  | (true, true), (false, false), _ => bothOverlapObj R I q
  | (true, true), (false, true), _ => firstOverlapObj R I q
  | (true, true), (true, false), _ => secondOverlapObj R I q
  | (true, true), (true, true), h => (h rfl).elim

/-- **The overlap charts** `f i j h : V i j h ⟶ Spf(A ⊗̂ A)` of the four-chart Tate
self-fibre-product glue: the first-, second- or both-factor overlap chart of
`TateSelfProductTripleOverlap` according to the difference type of `i` and `j`. -/
def tateSelfProductGlueF (hI : I.FG) :
    ∀ (i j : Bool × Bool) (h : i ≠ j),
      tateSelfProductGlueV R I q hI i j h ⟶ tateSelfProductGlueU R I q :=
  fun i j h => match i, j, h with
  | (false, false), (false, false), h => (h rfl).elim
  | (false, false), (false, true), _ => secondFactorOverlapChart R I q hI
  | (false, false), (true, false), _ => firstFactorOverlapChart R I q hI
  | (false, false), (true, true), _ => bothFactorOverlapChart R I q hI
  | (false, true), (false, false), _ => secondFactorOverlapChart R I q hI
  | (false, true), (false, true), h => (h rfl).elim
  | (false, true), (true, false), _ => bothFactorOverlapChart R I q hI
  | (false, true), (true, true), _ => firstFactorOverlapChart R I q hI
  | (true, false), (false, false), _ => firstFactorOverlapChart R I q hI
  | (true, false), (false, true), _ => bothFactorOverlapChart R I q hI
  | (true, false), (true, false), h => (h rfl).elim
  | (true, false), (true, true), _ => secondFactorOverlapChart R I q hI
  | (true, true), (false, false), _ => bothFactorOverlapChart R I q hI
  | (true, true), (false, true), _ => firstFactorOverlapChart R I q hI
  | (true, true), (true, false), _ => secondFactorOverlapChart R I q hI
  | (true, true), (true, true), h => (h rfl).elim

/-- **The overlap transitions** `t i j h : V i j h ⟶ V j i h.symm` of the four-chart Tate
self-fibre-product glue: the `hom` leg of the first-, second- or both-factor transition of
`TateSelfProductTransition` according to the difference type of `i` and `j`. Because the overlap
object is symmetric in `i, j` and each transition is a self-inverse involution, one `hom`
serves both orderings. -/
def tateSelfProductGlueT (hI : I.FG) :
    ∀ (i j : Bool × Bool) (h : i ≠ j),
      tateSelfProductGlueV R I q hI i j h ⟶ tateSelfProductGlueV R I q hI j i h.symm :=
  fun i j h => match i, j, h with
  | (false, false), (false, false), h => (h rfl).elim
  | (false, false), (false, true), _ => (tateSelfProductRightTransition R I q hI).hom
  | (false, false), (true, false), _ => (tateSelfProductFirstTransition R I q hI).hom
  | (false, false), (true, true), _ => (tateSelfProductBothTransition R I q hI).hom
  | (false, true), (false, false), _ => (tateSelfProductRightTransition R I q hI).hom
  | (false, true), (false, true), h => (h rfl).elim
  | (false, true), (true, false), _ => (tateSelfProductBothTransition R I q hI).hom
  | (false, true), (true, true), _ => (tateSelfProductFirstTransition R I q hI).hom
  | (true, false), (false, false), _ => (tateSelfProductFirstTransition R I q hI).hom
  | (true, false), (false, true), _ => (tateSelfProductBothTransition R I q hI).hom
  | (true, false), (true, false), h => (h rfl).elim
  | (true, false), (true, true), _ => (tateSelfProductRightTransition R I q hI).hom
  | (true, true), (false, false), _ => (tateSelfProductBothTransition R I q hI).hom
  | (true, true), (false, true), _ => (tateSelfProductFirstTransition R I q hI).hom
  | (true, true), (true, false), _ => (tateSelfProductRightTransition R I q hI).hom
  | (true, true), (true, true), h => (h rfl).elim

/-! ### The discharged structural laws -/

/-- **Each overlap chart is an open immersion.** For distinct `i j`, `f i j h` is one of the
three named overlap charts of `TateSelfProductTripleOverlap`, each an open immersion. This is the
reusable witness the `f_mono`/`f_hasPullback` laws (and the eventual `f_open` field of the glued
`LocallyRingedSpace.GlueData`) consume. -/
theorem tateSelfProductGlueF_isOpenImmersion (hq : q ∈ I) (hI : I.FG) :
    ∀ (i j : Bool × Bool) (h : i ≠ j),
      LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j h) := by
  rintro ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ h <;>
    first
    | exact absurd rfl h
    | exact isOpenImmersion_firstFactorOverlapChart R I q hq hI
    | exact isOpenImmersion_secondFactorOverlapChart R I q hq hI
    | exact isOpenImmersion_bothFactorOverlapChart R I q hq hI

/-- **`f_mono`.** `f i j h` is a monomorphism, because it is an open immersion. -/
theorem tateSelfProductGlueF_mono (hq : q ∈ I) (hI : I.FG) :
    ∀ (i j : Bool × Bool) (h : i ≠ j), Mono (tateSelfProductGlueF R I q hI i j h) := by
  intro i j h
  haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i j h
  infer_instance

/-- **`f_hasPullback`.** The triple-overlap pullback `pullback (f i j hij) (f i k hik)` exists,
because the left leg `f i j` is an open immersion and pullbacks of open immersions exist
(`LocallyRingedSpace.IsOpenImmersion.hasPullback_of_left`). -/
theorem tateSelfProductGlueF_hasPullback (hq : q ∈ I) (hI : I.FG) :
    ∀ (i j k : Bool × Bool) (hij : i ≠ j) (hik : i ≠ k),
      HasPullback (tateSelfProductGlueF R I q hI i j hij)
        (tateSelfProductGlueF R I q hI i k hik) := by
  intro i j k hij hik
  haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i j hij
  infer_instance

/-- **`t_inv`.** Each transition is its own inverse: `t i j h ≫ t j i h.symm = 𝟙`. Since
`t i j = t j i` is the `Iso.hom` leg of a self-inverse involution (whose `Iso.hom` and `Iso.inv`
legs coincide), each case is `Iso.hom_inv_id` of the corresponding transition. -/
theorem tateSelfProductGlueT_inv (hI : I.FG) :
    ∀ (i j : Bool × Bool) (h : i ≠ j),
      tateSelfProductGlueT R I q hI i j h ≫ tateSelfProductGlueT R I q hI j i h.symm = 𝟙 _ := by
  rintro ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ h <;>
    first
    | exact absurd rfl h
    | exact (tateSelfProductFirstTransition R I q hI).hom_inv_id
    | exact (tateSelfProductRightTransition R I q hI).hom_inv_id
    | exact (tateSelfProductBothTransition R I q hI).hom_inv_id

end AlgebraicGeometry
