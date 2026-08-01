import FormalSchemes.TateSelfProductTripleOverlap
import FormalSchemes.TateSelfProductTransition

set_option linter.style.header false
-- The completed-tensor interchange morphisms range over the nested localization/completion
-- towers of the completed tensor product, which are slow for the elaborator and the kernel;
-- raise the budgets (matching `TateSelfProductTripleOverlap.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The index-dispatched `V`/`f`/`t` scaffold of the Tate self-fibre-product glue

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. The self fibre-product `𝔈_q ×_{Spf R} 𝔈_q` of the two-chart Tate curve model is a
**four-chart** glue: four copies of `Spf C` indexed by `Bool × Bool`. This file assembles the
"easy" six of the nine `CategoryTheory.GlueData'` fields — the ones that do not involve the genuine
`Bool × Bool` cocycle — as standalone `def`s/`theorem`s: the patch objects `U`, the overlap objects
`V`, the overlap charts `f` with their `Mono`/`HasPullback` witnesses, and the self-inverse
transition `t` with its involution law `t_inv`. The three hard fields `t'`, `t_fac`, `cocycle` are a
follow-up and are **not** attempted here.

Every patch object is the same `Spf C`, so the overlap datum of a pair `(i, j)` depends only on
**how** `i` and `j` differ. Writing `p := i.down`, `r := j.down` for distinct `i j`:

* `p.1 = r.1` (so `p.2 ≠ r.2`)  → the second tensor factor differs → `secondFactorOverlapChart`,
  transition `tateSelfProductRightTransition`;
* `p.1 ≠ r.1` and `p.2 = r.2`   → the first tensor factor differs  → `firstFactorOverlapChart`,
  transition `tateSelfProductFirstTransition`;
* `p.1 ≠ r.1` and `p.2 ≠ r.2`   → both factors differ              → `bothFactorOverlapChart`,
  transition `tateSelfProductBothTransition`.

Because the overlap object `V i j` is an `if`-dispatch, the chart `f` and the transition `t` are
`eqToHom`-corrected `if`-dispatches (mirroring Mathlib's `CategoryTheory.GlueData'.f'`): the
`eqToHom`s realign the reduced shape object with `V i j`, keeping every branch homogeneously typed
so that `split_ifs` reasons cleanly.

## Main definitions

* `AlgebraicGeometry.selfProductGlueU`: the constant patch object `Spf C`.
* `AlgebraicGeometry.selfProductGlueV`: the index-dispatched overlap object.
* `AlgebraicGeometry.selfProductGlueF`: the index-dispatched overlap chart `V i j ⟶ U i`.
* `AlgebraicGeometry.selfProductGlueF_mono`, `selfProductGlueF_hasPullback`: the `f_mono`/
  `f_hasPullback` fields, from the open-immersion instances of the three charts.
* `AlgebraicGeometry.selfProductGlueT`: the index-dispatched self-inverse overlap transition.
* `AlgebraicGeometry.selfProductGlueT_inv`: the involution law `t i j ≫ t j i = 𝟙`.

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

/-! ### The coproduct summand objects of the three overlap shapes

The eight affine charts `Spf(A{1/a}? ⊗̂_R A{1/b}?)` appearing as coproduct summands of the three
overlap objects, presented over the `I.map (algebraMap R ·)` ideal convention so that they match the
domains of the overlap charts of `TateSelfProductTripleOverlap` definitionally. -/

/-- `Spf(A{1/x} ⊗̂_R A)`: the `x`-summand of the first-factor overlap object. -/
private abbrev spXA : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
    (annulusAlgebra R I q))

/-- `Spf(A{1/y} ⊗̂_R A)`: the `y`-summand of the first-factor overlap object. -/
private abbrev spYA : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
    (annulusAlgebra R I q))

/-- `Spf(A ⊗̂_R A{1/x})`: the `x`-summand of the second-factor overlap object. -/
private abbrev spAX : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))

/-- `Spf(A ⊗̂_R A{1/y})`: the `y`-summand of the second-factor overlap object. -/
private abbrev spAY : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))

/-- `Spf(A{1/x} ⊗̂_R A{1/x})`: the `(x, x)`-summand of the both-factors overlap object. -/
private abbrev spXX : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))

/-- `Spf(A{1/x} ⊗̂_R A{1/y})`: the `(x, y)`-summand of the both-factors overlap object. -/
private abbrev spXY : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))

/-- `Spf(A{1/y} ⊗̂_R A{1/x})`: the `(y, x)`-summand of the both-factors overlap object. -/
private abbrev spYX : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))

/-- `Spf(A{1/y} ⊗̂_R A{1/y})`: the `(y, y)`-summand of the both-factors overlap object. -/
private abbrev spYY : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))

/-! ### The three overlap-shape objects -/

/-- The domain of `firstFactorOverlapChart`: `Spf(A{1/x} ⊗̂ A) ⨿ Spf(A{1/y} ⊗̂ A)`. -/
private abbrev firstShapeV : LocallyRingedSpace.{u} := spXA R I q ⨿ spYA R I q

/-- The domain of `secondFactorOverlapChart`: `Spf(A ⊗̂ A{1/x}) ⨿ Spf(A ⊗̂ A{1/y})`. -/
private abbrev secondShapeV : LocallyRingedSpace.{u} := spAX R I q ⨿ spAY R I q

/-- The domain of `bothFactorOverlapChart`: the nested four-fold coproduct of the both-localized
summands. -/
private abbrev bothShapeV : LocallyRingedSpace.{u} :=
  (spXX R I q ⨿ spXY R I q) ⨿ (spYX R I q ⨿ spYY R I q)

/-! ### The patch and overlap objects -/

/-- **The patch object.** All four charts of the self fibre-product are the same affine formal
spectrum `Spf C` with `C = A ⊗̂_R A`, so the patch function is constant. -/
def selfProductGlueU (_ : ULift.{u} (Bool × Bool)) : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj
    (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))

/-- **The overlap object.** For distinct charts `i j` it is the domain of the overlap chart of the
shape determined by how `i` and `j` differ: second-factor, first-factor or both-factor. -/
def selfProductGlueV (i j : ULift.{u} (Bool × Bool)) (_ : i ≠ j) : LocallyRingedSpace.{u} :=
  if i.down.1 = j.down.1 then secondShapeV R I q
  else if i.down.2 = j.down.2 then firstShapeV R I q
  else bothShapeV R I q

/-- The overlap object reduces to the second-factor shape when the first coordinates agree. -/
theorem selfProductGlueV_second (i j : ULift.{u} (Bool × Bool)) (h : i ≠ j)
    (h1 : i.down.1 = j.down.1) : selfProductGlueV R I q i j h = secondShapeV R I q := by
  unfold selfProductGlueV
  rw [if_pos h1]

/-- The overlap object reduces to the first-factor shape when only the second coordinates agree. -/
theorem selfProductGlueV_first (i j : ULift.{u} (Bool × Bool)) (h : i ≠ j)
    (h1 : ¬i.down.1 = j.down.1) (h2 : i.down.2 = j.down.2) :
    selfProductGlueV R I q i j h = firstShapeV R I q := by
  unfold selfProductGlueV
  rw [if_neg h1, if_pos h2]

/-- The overlap object reduces to the both-factors shape when both coordinates differ. -/
theorem selfProductGlueV_both (i j : ULift.{u} (Bool × Bool)) (h : i ≠ j)
    (h1 : ¬i.down.1 = j.down.1) (h2 : ¬i.down.2 = j.down.2) :
    selfProductGlueV R I q i j h = bothShapeV R I q := by
  unfold selfProductGlueV
  rw [if_neg h1, if_neg h2]

/-! ### The overlap chart and its `Mono`/`HasPullback` witnesses -/

/-- **The overlap chart** `V i j ⟶ U i`: the second-, first- or both-factor overlap chart of
`TateSelfProductTripleOverlap`, dispatched on how `i` and `j` differ. Each branch is prefixed with
the `eqToHom` realigning `V i j` with the reduced shape object, keeping the `if`-branches
homogeneously typed. -/
def selfProductGlueF (hI : I.FG) (i j : ULift.{u} (Bool × Bool)) (h : i ≠ j) :
    selfProductGlueV R I q i j h ⟶ selfProductGlueU R I q i :=
  if h1 : i.down.1 = j.down.1 then
    eqToHom (selfProductGlueV_second R I q i j h h1) ≫ secondFactorOverlapChart R I q hI
  else if h2 : i.down.2 = j.down.2 then
    eqToHom (selfProductGlueV_first R I q i j h h1 h2) ≫ firstFactorOverlapChart R I q hI
  else
    eqToHom (selfProductGlueV_both R I q i j h h1 h2) ≫ bothFactorOverlapChart R I q hI

/-- **The overlap charts are open immersions.** Each branch is `eqToHom ≫ chart`, the composite of
an isomorphism (`eqToHom`) with an open-immersion overlap chart. -/
theorem selfProductGlueF_isOpenImmersion (hq : q ∈ I) (hI : I.FG) (i j : ULift.{u} (Bool × Bool))
    (h : i ≠ j) : LocallyRingedSpace.IsOpenImmersion (selfProductGlueF R I q hI i j h) := by
  haveI := isOpenImmersion_secondFactorOverlapChart R I q hq hI
  haveI := isOpenImmersion_firstFactorOverlapChart R I q hq hI
  haveI := isOpenImmersion_bothFactorOverlapChart R I q hq hI
  unfold selfProductGlueF
  split_ifs with h1 h2
  · exact LocallyRingedSpace.IsOpenImmersion.comp
      (eqToHom (selfProductGlueV_second R I q i j h h1)) (secondFactorOverlapChart R I q hI)
  · exact LocallyRingedSpace.IsOpenImmersion.comp
      (eqToHom (selfProductGlueV_first R I q i j h h1 h2)) (firstFactorOverlapChart R I q hI)
  · exact LocallyRingedSpace.IsOpenImmersion.comp
      (eqToHom (selfProductGlueV_both R I q i j h h1 h2)) (bothFactorOverlapChart R I q hI)

/-- **The overlap charts are monomorphisms**, being open immersions. -/
theorem selfProductGlueF_mono (hq : q ∈ I) (hI : I.FG) (i j : ULift.{u} (Bool × Bool))
    (h : i ≠ j) : Mono (selfProductGlueF R I q hI i j h) :=
  haveI := selfProductGlueF_isOpenImmersion R I q hq hI i j h
  inferInstance

/-- **The overlap charts admit pullbacks along each other.** The left leg `f i j` is an open
immersion, so the pullback exists (`hasPullback_of_left`). -/
theorem selfProductGlueF_hasPullback (hq : q ∈ I) (hI : I.FG)
    (i j k : ULift.{u} (Bool × Bool)) (hij : i ≠ j) (hik : i ≠ k) :
    HasPullback (selfProductGlueF R I q hI i j hij) (selfProductGlueF R I q hI i k hik) :=
  haveI := selfProductGlueF_isOpenImmersion R I q hq hI i j hij
  inferInstance

/-! ### The overlap transition and its involution law -/

/-- **The overlap transition** `t i j : V i j ⟶ V j i`: the self-inverse summand-swap involution of
the overlap shape determined by how `i` and `j` differ, delivered by `TateSelfProductTransition`,
with `eqToHom`s realigning both ends with the dispatched overlap objects. -/
def selfProductGlueT (hI : I.FG) (i j : ULift.{u} (Bool × Bool)) (h : i ≠ j) :
    selfProductGlueV R I q i j h ⟶ selfProductGlueV R I q j i h.symm :=
  if h1 : i.down.1 = j.down.1 then
    eqToHom (selfProductGlueV_second R I q i j h h1) ≫
      (tateSelfProductRightTransition R I q hI).hom ≫
      eqToHom (selfProductGlueV_second R I q j i h.symm h1.symm).symm
  else if h2 : i.down.2 = j.down.2 then
    eqToHom (selfProductGlueV_first R I q i j h h1 h2) ≫
      (tateSelfProductFirstTransition R I q hI).hom ≫
      eqToHom (selfProductGlueV_first R I q j i h.symm (fun e => h1 e.symm) h2.symm).symm
  else
    eqToHom (selfProductGlueV_both R I q i j h h1 h2) ≫
      (tateSelfProductBothTransition R I q hI).hom ≫
      eqToHom (selfProductGlueV_both R I q j i h.symm
        (fun e => h1 e.symm) (fun e => h2 e.symm)).symm

/-- The second-factor transition squares to the identity: `t.hom ≫ t.hom = 𝟙` because its `hom` and
`inv` coincide definitionally. -/
@[reassoc]
private theorem rightTrans_hom_hom (hI : I.FG) :
    (tateSelfProductRightTransition R I q hI).hom ≫ (tateSelfProductRightTransition R I q hI).hom
      = 𝟙 _ :=
  (tateSelfProductRightTransition R I q hI).hom_inv_id

/-- The first-factor transition squares to the identity. -/
@[reassoc]
private theorem firstTrans_hom_hom (hI : I.FG) :
    (tateSelfProductFirstTransition R I q hI).hom ≫ (tateSelfProductFirstTransition R I q hI).hom
      = 𝟙 _ :=
  (tateSelfProductFirstTransition R I q hI).hom_inv_id

/-- The both-factors transition squares to the identity. -/
@[reassoc]
private theorem bothTrans_hom_hom (hI : I.FG) :
    (tateSelfProductBothTransition R I q hI).hom ≫ (tateSelfProductBothTransition R I q hI).hom
      = 𝟙 _ :=
  (tateSelfProductBothTransition R I q hI).hom_inv_id

/-- **The transition is an involution:** `t i j ≫ t j i = 𝟙`. In each branch it is
`eqToHom ≫ T.hom ≫ eqToHom ≫ eqToHom ≫ T.hom ≫ eqToHom`; the paired `eqToHom`s cancel and each
transition squares to the identity, so the composite is the identity. -/
theorem selfProductGlueT_inv (hI : I.FG) (i j : ULift.{u} (Bool × Bool)) (h : i ≠ j) :
    selfProductGlueT R I q hI i j h ≫ selfProductGlueT R I q hI j i h.symm = 𝟙 _ := by
  unfold selfProductGlueT
  split_ifs <;>
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      rightTrans_hom_hom_assoc, firstTrans_hom_hom_assoc, bothTrans_hom_hom_assoc] <;>
    grind

end AlgebraicGeometry
