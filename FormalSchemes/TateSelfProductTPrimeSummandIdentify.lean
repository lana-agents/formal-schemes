import FormalSchemes.TateSelfProductTPrimeSummand

set_option linter.style.header false
-- The completed-tensor interchange charts range over the nested localization/completion towers of
-- the completed tensor product, which are slow for the elaborator and the kernel; raise the budgets
-- (matching `TateSelfProductTPrimeSummand.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Identifying the conjugated self-map `t'` with an explicit summand permutation

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. Continuing `TateSelfProductTPrimeSummand`, this file constructs the explicit
**summand permutation** `tateSelfProductSigma i j k` — the closed form that the conjugated self-map
`tateSelfProductD i j k : bothOverlapObj ⟶ bothOverlapObj` of the both-overlap object
`(dXX ⨿ dXY) ⨿ (dYX ⨿ dYY)` is to be identified with. It is a self-isomorphism of `bothOverlapObj`
dispatched by the Klein-four difference of `(i, j)` in `Bool × Bool`:

* differ in **both** coordinates → the diagonal/anti-diagonal swap
  `tateSelfProductBothTransition` (`dXX ↔ dYY`, `dXY ↔ dYX`);
* differ in the **first** coordinate only → the "swap-first" involution
  (`dXX ↔ dYX`, `dXY ↔ dYY`) built from the annulus chart transition on the first tensor factor;
* differ in the **second** coordinate only → the "swap-second" involution
  (`dXX ↔ dXY`, `dYX ↔ dYY`) built from the annulus chart transition on the second tensor factor.

The two new involutions mirror `tateSelfProductBothTransition`: each swaps two paired summands
through the per-summand `mapSpfIso` and back through its inverse, hence is its own inverse. The
`Bool × Bool` dispatch of `tateSelfProductSigma` matches that of `tateSelfProductGlueT` shape for
shape, so `tateSelfProductSigma i j k` is the summand-permutation candidate for `tateSelfProductD`.
The identification theorem `tateSelfProductD i j k = (tateSelfProductSigma …).hom` — proved by
`bothFactorOverlapChart`-mono + `coprod.hom_ext` over the four summands, using
`tateSelfProductD_comp_bothChart` — is the remaining payload of issue 237 brick (c3a) and is left to
a follow-up; it is what brick (c3b) consumes to close the `GlueData'` cocycle by `coprod.hom_ext`.

## Main definitions / results

* `AlgebraicGeometry.tateSelfProductSwapFirstTransition`: the swap-first involution of
  `bothOverlapObj`.
* `AlgebraicGeometry.tateSelfProductSwapSecondTransition`: the swap-second involution of
  `bothOverlapObj`.
* `AlgebraicGeometry.tateSelfProductSigma`: the `Bool × Bool`-dispatched summand permutation.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* Mathlib `CategoryTheory.GlueData'` (the `t'`/`t_fac`/`cocycle` fields).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
  CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The per-summand transitions of the two new swap involutions -/

/-- The swap-first per-summand transition `Spf(A{1/x} ⊗̂ A{1/x}) ≅ Spf(A{1/y} ⊗̂ A{1/x})`:
`mapSpfIso` of the annulus chart transition on the first factor and the identity on the second. -/
abbrev swapFirstSummandXX (hI : I.FG) : dXX R I q ≅ dYX R I q :=
  mapSpfIso hI (annulusFibreChartTransitionAlg R I q hI)
    (AlgEquiv.refl (R := R)
      (A₁ := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))

/-- The swap-first per-summand transition `Spf(A{1/x} ⊗̂ A{1/y}) ≅ Spf(A{1/y} ⊗̂ A{1/y})`:
`mapSpfIso` of the annulus chart transition on the first factor and the identity on the second. -/
abbrev swapFirstSummandXY (hI : I.FG) : dXY R I q ≅ dYY R I q :=
  mapSpfIso hI (annulusFibreChartTransitionAlg R I q hI)
    (AlgEquiv.refl (R := R)
      (A₁ := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))

/-- The swap-second per-summand transition `Spf(A{1/x} ⊗̂ A{1/x}) ≅ Spf(A{1/x} ⊗̂ A{1/y})`:
`mapSpfIso` of the identity on the first factor and the annulus chart transition on the second. -/
abbrev swapSecondSummandXX (hI : I.FG) : dXX R I q ≅ dXY R I q :=
  mapSpfIso hI
    (AlgEquiv.refl (R := R)
      (A₁ := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
    (annulusFibreChartTransitionAlg R I q hI)

/-- The swap-second per-summand transition `Spf(A{1/y} ⊗̂ A{1/x}) ≅ Spf(A{1/y} ⊗̂ A{1/y})`:
`mapSpfIso` of the identity on the first factor and the annulus chart transition on the second. -/
abbrev swapSecondSummandYX (hI : I.FG) : dYX R I q ≅ dYY R I q :=
  mapSpfIso hI
    (AlgEquiv.refl (R := R)
      (A₁ := awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))
    (annulusFibreChartTransitionAlg R I q hI)

/-! ### The two new swap involutions of the both-overlap object -/

/-- **The swap-first overlap involution.** The four-summand permuting involution of the both-overlap
object `(dXX ⨿ dXY) ⨿ (dYX ⨿ dYY)` realising the first-coordinate swap `(a, b) ↦ (swap a, b)`: it
sends `(x, x) ↦ (y, x)` and `(x, y) ↦ (y, y)` through the per-summand transitions
`swapFirstSummandXX`/`swapFirstSummandXY`, and back through their inverses. Its own inverse, it is
the summand-permutation form of `tateSelfProductD` for the chart pairs `(i, j)` differing only in
the first coordinate. -/
def tateSelfProductSwapFirstTransition (hI : I.FG) :
    ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ≅
      ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) where
  hom := coprod.desc
    (coprod.desc ((swapFirstSummandXX R I q hI).hom ≫ coprod.inl ≫ coprod.inr)
      ((swapFirstSummandXY R I q hI).hom ≫ coprod.inr ≫ coprod.inr))
    (coprod.desc ((swapFirstSummandXX R I q hI).inv ≫ coprod.inl ≫ coprod.inl)
      ((swapFirstSummandXY R I q hI).inv ≫ coprod.inr ≫ coprod.inl))
  inv := coprod.desc
    (coprod.desc ((swapFirstSummandXX R I q hI).hom ≫ coprod.inl ≫ coprod.inr)
      ((swapFirstSummandXY R I q hI).hom ≫ coprod.inr ≫ coprod.inr))
    (coprod.desc ((swapFirstSummandXX R I q hI).inv ≫ coprod.inl ≫ coprod.inl)
      ((swapFirstSummandXY R I q hI).inv ≫ coprod.inr ≫ coprod.inl))
  hom_inv_id := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Category.comp_id]
  inv_hom_id := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Category.comp_id]

/-- **The swap-second overlap involution.** The four-summand permuting involution of the
both-overlap object `(dXX ⨿ dXY) ⨿ (dYX ⨿ dYY)` realising the second-coordinate swap
`(a, b) ↦ (a, swap b)`: it
sends `(x, x) ↦ (x, y)` and `(y, x) ↦ (y, y)` through the per-summand transitions
`swapSecondSummandXX`/`swapSecondSummandYX`, and back through their inverses. Its own inverse, it is
the summand-permutation form of `tateSelfProductD` for the chart pairs `(i, j)` differing only in
the second coordinate. -/
def tateSelfProductSwapSecondTransition (hI : I.FG) :
    ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ≅
      ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) where
  hom := coprod.desc
    (coprod.desc ((swapSecondSummandXX R I q hI).hom ≫ coprod.inr ≫ coprod.inl)
      ((swapSecondSummandXX R I q hI).inv ≫ coprod.inl ≫ coprod.inl))
    (coprod.desc ((swapSecondSummandYX R I q hI).hom ≫ coprod.inr ≫ coprod.inr)
      ((swapSecondSummandYX R I q hI).inv ≫ coprod.inl ≫ coprod.inr))
  inv := coprod.desc
    (coprod.desc ((swapSecondSummandXX R I q hI).hom ≫ coprod.inr ≫ coprod.inl)
      ((swapSecondSummandXX R I q hI).inv ≫ coprod.inl ≫ coprod.inl))
    (coprod.desc ((swapSecondSummandYX R I q hI).hom ≫ coprod.inr ≫ coprod.inr)
      ((swapSecondSummandYX R I q hI).inv ≫ coprod.inl ≫ coprod.inr))
  hom_inv_id := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Category.comp_id]
  inv_hom_id := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Category.comp_id]

/-! ### The dispatched summand permutation -/

/-- **The summand permutation** `tateSelfProductSigma i j k : bothOverlapObj ≅ bothOverlapObj`: the
explicit self-isomorphism of the both-overlap object dispatched by the Klein-four difference of
`(i, j)` in `Bool × Bool`, exactly matching the dispatch of `tateSelfProductGlueT`. It is the
`tateSelfProductBothTransition` (both coordinates differ), the `tateSelfProductSwapFirstTransition`
(first coordinate differs) or the `tateSelfProductSwapSecondTransition` (second coordinate differs).
This is the closed-form summand-permutation identification of the conjugated self-map
`tateSelfProductD`. -/
def tateSelfProductSigma (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (_hik : i ≠ k) (_hjk : j ≠ k) :
    (((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ≅
      ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q))) :=
  match i, j, hij with
  | (false, false), (false, false), h => (h rfl).elim
  | (false, false), (false, true), _ => tateSelfProductSwapSecondTransition R I q hI
  | (false, false), (true, false), _ => tateSelfProductSwapFirstTransition R I q hI
  | (false, false), (true, true), _ => tateSelfProductBothTransition R I q hI
  | (false, true), (false, false), _ => tateSelfProductSwapSecondTransition R I q hI
  | (false, true), (false, true), h => (h rfl).elim
  | (false, true), (true, false), _ => tateSelfProductBothTransition R I q hI
  | (false, true), (true, true), _ => tateSelfProductSwapFirstTransition R I q hI
  | (true, false), (false, false), _ => tateSelfProductSwapFirstTransition R I q hI
  | (true, false), (false, true), _ => tateSelfProductBothTransition R I q hI
  | (true, false), (true, false), h => (h rfl).elim
  | (true, false), (true, true), _ => tateSelfProductSwapSecondTransition R I q hI
  | (true, true), (false, false), _ => tateSelfProductBothTransition R I q hI
  | (true, true), (false, true), _ => tateSelfProductSwapFirstTransition R I q hI
  | (true, true), (true, false), _ => tateSelfProductSwapSecondTransition R I q hI
  | (true, true), (true, true), h => (h rfl).elim

end AlgebraicGeometry

end
