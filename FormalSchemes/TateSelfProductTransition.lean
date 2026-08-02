import FormalSchemes.TateSelfProductBothOverlap
import FormalSchemes.TwoPatchFibreProductObject

set_option linter.style.header false
-- The completed-tensor interchange morphisms range over the nested localization/completion
-- towers of the completed tensor product, which are slow for the elaborator and the kernel;
-- raise the budgets (matching `TateSelfProductOverlap.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The overlap transition isomorphisms of the Tate self-fibre-product

Fix an adic base `(R, I)` with `q ∈ I` (the Tate parameter is topologically nilpotent) and finitely
generated `I`, and let `A = annulusAlgebra R I q = R{x, y}/(x·y − q)` be the coordinate ring of the
formal Tate annulus. The self fibre-product `𝔈_q ×_{Spf R} 𝔈_q` of the two-chart Tate curve model
is glued from four copies of the affine chart `Spf(A ⊗̂_R A)` indexed by pairs of the two
`𝔈_q`-charts. This file assembles the **overlap transition isomorphisms** `t` of that four-chart
glue datum: the summand-permuting isomorphisms of the three overlap objects delivered by
`TateSelfProductOverlap` (first factor differs), `TateSelfProductRightOverlap` (second factor
differs) and `TateSelfProductBothOverlap` (both factors differ).

Each transition is the direct base-changed analogue of the two-chart Tate curve model's summand-swap
transition `tateCurveGlueData'.t = coprod.desc (transition.hom ≫ inr) (transition.inv ≫ inl)`
(`FormalSchemes.TateCurveModel`), which sends the `x`-overlap summand to the `y`-overlap summand
through the annulus chart transition and back. Because each overlap object here is a coproduct of
the interchange charts of `TateSelfProduct*Overlap`, the transition is a `coprod.desc` of the
per-summand transition isomorphisms:

* **First factor** (`tateSelfProductFirstTransition`): an involution of
  `Spf(A{1/x} ⊗̂_R A) ⨿ Spf(A{1/y} ⊗̂_R A)` built from the base-changed annulus chart transition
  `twoPatchFibreProductTransition R I q A hI : Spf(A{1/x} ⊗̂_R A) ≅ Spf(A{1/y} ⊗̂_R A)`.
* **Second factor** (`tateSelfProductRightTransition`): an involution of
  `Spf(A ⊗̂_R A{1/x}) ⨿ Spf(A ⊗̂_R A{1/y})` built from
  `mapSpfIso hI (AlgEquiv.refl R A) (annulusFibreChartTransitionAlg R I q hI)`.
* **Both factors** (`tateSelfProductBothTransition`): an involution of the four-fold coproduct
  `(Spf(A{1/x} ⊗̂_R A{1/x}) ⨿ Spf(A{1/x} ⊗̂_R A{1/y})) ⨿
   (Spf(A{1/y} ⊗̂_R A{1/x}) ⨿ Spf(A{1/y} ⊗̂_R A{1/y}))` permuting the four summands
  `(a, b) ↦ (swap a, swap b)` through `mapSpfIso` of the annulus chart transition on each factor.

Since each transition swaps two paired summands (the second factor being the honest inverse of the
first), each is its own inverse, so all three are packaged as `Iso`s whose `hom` and `inv` legs
coincide. The self-inverse law `t i j ≫ t j i = 𝟙` of the eventual four-chart `GlueData'` is then
`Iso.hom_inv_id` of these; the same isomorphisms feed the genuine `Bool × Bool` cocycle.

## Main definitions

* `AlgebraicGeometry.tateSelfProductFirstTransition`: the first-factor overlap transition.
* `AlgebraicGeometry.tateSelfProductRightTransition`: the second-factor overlap transition.
* `AlgebraicGeometry.tateSelfProductBothTransition`: the both-factors overlap transition.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The coordinate ring of the formal Tate annulus, base for the self fibre-product. -/
private abbrev A : Type u := annulusAlgebra R I q

/-! ### The chart-domain objects

The eight affine charts `Spf(A{1/a} ⊗̂_R A{1/b}?)` appearing as coproduct summands of the three
overlap objects, presented over the `I.map (algebraMap R ·)` ideal convention the interchange
immersions use so that they match the domains of `TateSelfProduct*Overlap` definitionally. -/

/-- `Spf(A{1/x} ⊗̂_R A)`: the `x`-summand of the first-factor overlap object. -/
private abbrev dXA : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (A R I q))) (overlapX R I q)) (A R I q))

/-- `Spf(A{1/y} ⊗̂_R A)`: the `y`-summand of the first-factor overlap object. -/
private abbrev dYA : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (A R I q))) (overlapY R I q)) (A R I q))

/-- `Spf(A ⊗̂_R A{1/x})`: the `x`-summand of the second-factor overlap object. -/
private abbrev dAX : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (idealOfDefinition R I (A R I q)
    (awayCompletion (I.map (algebraMap R (A R I q))) (overlapX R I q)))

/-- `Spf(A ⊗̂_R A{1/y})`: the `y`-summand of the second-factor overlap object. -/
private abbrev dAY : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (idealOfDefinition R I (A R I q)
    (awayCompletion (I.map (algebraMap R (A R I q))) (overlapY R I q)))

/-- `Spf(A{1/x} ⊗̂_R A{1/x})`: the `(x, x)`-summand of the both-factors overlap object. -/
abbrev dXX : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (A R I q))) (overlapX R I q))
    (awayCompletion (I.map (algebraMap R (A R I q))) (overlapX R I q)))

/-- `Spf(A{1/x} ⊗̂_R A{1/y})`: the `(x, y)`-summand of the both-factors overlap object. -/
abbrev dXY : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (A R I q))) (overlapX R I q))
    (awayCompletion (I.map (algebraMap R (A R I q))) (overlapY R I q)))

/-- `Spf(A{1/y} ⊗̂_R A{1/x})`: the `(y, x)`-summand of the both-factors overlap object. -/
abbrev dYX : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (A R I q))) (overlapY R I q))
    (awayCompletion (I.map (algebraMap R (A R I q))) (overlapX R I q)))

/-- `Spf(A{1/y} ⊗̂_R A{1/y})`: the `(y, y)`-summand of the both-factors overlap object. -/
abbrev dYY : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (A R I q))) (overlapY R I q))
    (awayCompletion (I.map (algebraMap R (A R I q))) (overlapY R I q)))

/-! ### The per-summand transition isomorphisms -/

/-- The first-factor per-summand transition `Spf(A{1/x} ⊗̂_R A) ≅ Spf(A{1/y} ⊗̂_R A)`: the
base-changed annulus chart transition of the two-patch fibre product with `B := A`. -/
private abbrev firstSummand (hI : I.FG) : dXA R I q ≅ dYA R I q :=
  twoPatchFibreProductTransition R I q (A R I q) hI

/-- The second-factor per-summand transition `Spf(A ⊗̂_R A{1/x}) ≅ Spf(A ⊗̂_R A{1/y})`: `mapSpfIso`
of the identity on the fixed first factor and the annulus chart transition on the second. -/
private abbrev rightSummand (hI : I.FG) : dAX R I q ≅ dAY R I q :=
  mapSpfIso hI (AlgEquiv.refl (R := R) (A₁ := A R I q)) (annulusFibreChartTransitionAlg R I q hI)

/-- The `(x, x) ≅ (y, y)` per-summand transition
`Spf(A{1/x} ⊗̂_R A{1/x}) ≅ Spf(A{1/y} ⊗̂_R A{1/y})`:
`mapSpfIso` of the annulus chart transition on *both* factors. -/
private abbrev bothSummandDiag (hI : I.FG) : dXX R I q ≅ dYY R I q :=
  mapSpfIso hI (annulusFibreChartTransitionAlg R I q hI) (annulusFibreChartTransitionAlg R I q hI)

/-- The `(x, y) ≅ (y, x)` per-summand transition
`Spf(A{1/x} ⊗̂_R A{1/y}) ≅ Spf(A{1/y} ⊗̂_R A{1/x})`:
`mapSpfIso` of the annulus chart transition on the first factor and its inverse on the second. -/
private abbrev bothSummandAnti (hI : I.FG) : dXY R I q ≅ dYX R I q :=
  mapSpfIso hI (annulusFibreChartTransitionAlg R I q hI)
    (annulusFibreChartTransitionAlg R I q hI).symm

/-! ### The overlap transition isomorphisms -/

/-- **The first-factor overlap transition.** The summand-swap involution of the first-factor overlap
object `Spf(A{1/x} ⊗̂_R A) ⨿ Spf(A{1/y} ⊗̂_R A)` (the `V`/`f` datum of `TateSelfProductOverlap`),
sending the `x`-summand to the `y`-summand through the base-changed annulus chart transition
`firstSummand` and back through its inverse. This is the base change (with `B := A`) of the
two-chart Tate curve model's summand-swap transition `tateCurveGlueData'.t`, and is its own inverse,
so it feeds the four-chart glue's transition datum `t` (for the chart pairs where only the first
factor differs) with self-inverse law `Iso.hom_inv_id`. -/
def tateSelfProductFirstTransition (hI : I.FG) :
    (dXA R I q ⨿ dYA R I q) ≅ (dXA R I q ⨿ dYA R I q) where
  hom := coprod.desc ((firstSummand R I q hI).hom ≫ coprod.inr)
    ((firstSummand R I q hI).inv ≫ coprod.inl)
  inv := coprod.desc ((firstSummand R I q hI).hom ≫ coprod.inr)
    ((firstSummand R I q hI).inv ≫ coprod.inl)
  hom_inv_id := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, coprod.inl_desc, Category.assoc, coprod.inr_desc,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, coprod.inr_desc, Category.assoc, coprod.inl_desc,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, coprod.inl_desc, Category.assoc, coprod.inr_desc,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, coprod.inr_desc, Category.assoc, coprod.inl_desc,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]

/-- **The second-factor overlap transition.** The summand-swap involution of the second-factor
overlap object `Spf(A ⊗̂_R A{1/x}) ⨿ Spf(A ⊗̂_R A{1/y})` (the `V`/`f` datum of
`TateSelfProductRightOverlap`), sending the `x`-summand to the `y`-summand through `rightSummand`
and back. Mirror of `tateSelfProductFirstTransition` on the second tensor factor; its own inverse,
so it feeds the four-chart glue's transition datum `t` for the chart pairs where only the second
factor differs. -/
def tateSelfProductRightTransition (hI : I.FG) :
    (dAX R I q ⨿ dAY R I q) ≅ (dAX R I q ⨿ dAY R I q) where
  hom := coprod.desc ((rightSummand R I q hI).hom ≫ coprod.inr)
    ((rightSummand R I q hI).inv ≫ coprod.inl)
  inv := coprod.desc ((rightSummand R I q hI).hom ≫ coprod.inr)
    ((rightSummand R I q hI).inv ≫ coprod.inl)
  hom_inv_id := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, coprod.inl_desc, Category.assoc, coprod.inr_desc,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, coprod.inr_desc, Category.assoc, coprod.inl_desc,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, coprod.inl_desc, Category.assoc, coprod.inr_desc,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, coprod.inr_desc, Category.assoc, coprod.inl_desc,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]

/-- **The both-factors overlap transition.** The four-summand permuting involution of the
both-factors overlap object
`(Spf(A{1/x} ⊗̂ A{1/x}) ⨿ Spf(A{1/x} ⊗̂ A{1/y})) ⨿ (Spf(A{1/y} ⊗̂ A{1/x}) ⨿ Spf(A{1/y} ⊗̂ A{1/y}))`
(the `V`/`f` datum of `TateSelfProductBothOverlap`), realising the coordinate swap
`(a, b) ↦ (swap a, swap b)`: it sends `(x, x) ↦ (y, y)` and `(x, y) ↦ (y, x)` through the two
diagonal/anti-diagonal per-summand transitions `bothSummandDiag`/`bothSummandAnti`, and back through
their inverses. Since swapping twice is the identity, it is its own inverse, feeding the four-chart
glue's transition datum `t` for the chart pairs where both factors differ. -/
def tateSelfProductBothTransition (hI : I.FG) :
    ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ≅
      ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) where
  hom := coprod.desc
    (coprod.desc ((bothSummandDiag R I q hI).hom ≫ coprod.inr ≫ coprod.inr)
      ((bothSummandAnti R I q hI).hom ≫ coprod.inl ≫ coprod.inr))
    (coprod.desc ((bothSummandAnti R I q hI).inv ≫ coprod.inr ≫ coprod.inl)
      ((bothSummandDiag R I q hI).inv ≫ coprod.inl ≫ coprod.inl))
  inv := coprod.desc
    (coprod.desc ((bothSummandDiag R I q hI).hom ≫ coprod.inr ≫ coprod.inr)
      ((bothSummandAnti R I q hI).hom ≫ coprod.inl ≫ coprod.inr))
    (coprod.desc ((bothSummandAnti R I q hI).inv ≫ coprod.inr ≫ coprod.inl)
      ((bothSummandDiag R I q hI).inv ≫ coprod.inl ≫ coprod.inl))
  hom_inv_id := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Category.comp_id]
  inv_hom_id := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Category.comp_id]

end AlgebraicGeometry
