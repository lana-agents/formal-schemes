import FormalSchemes.GeneralFibreProductBothAlgebraDataObject
import FormalSchemes.CompletedTensorAwayInterchangeMixedPullback
import FormalSchemes.CompletedTensorAwayInterchangeBothPullback

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The geometric triple-overlap datum of the two-sided fibre product `X ×_{Spf R} Y`

Continuing the object-level dispatch of
`FormalSchemes.GeneralFibreProductBothAlgebraDataObject`, this file assembles the **geometric**
triple-overlap fields `t'`, `t_fac`, `cocycle` of the two-sided smart constructor
`AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraData`, and the constructor itself.

The one-sided template is `AlgebraicGeometry.AffineChartedFibreDatum.ofAlgebraData`
(`FormalSchemes.GeneralFibreProductAlgebraData`): there every overlap immersion is the *uniform*
first-factor `interchangeOpenImmersion`, so the triple-overlap transition is built from a single
`interchangePullbackIso`. Here the overlap immersion `bothAlgDataF` is **coordinate-difference
dispatched** (localize `B`, or `A`, or both), so the triple overlap of two charts
`pullback (bothAlgDataF p p') (bothAlgDataF p p'')` dispatches on the *pair* of shapes of its two
legs, and the per-shape pullback identifications are the six interchange-pullback isomorphisms
`interchangePullbackIso`, `rightInterchangePullbackIso`, `mixedInterchangePullbackIso`,
`firstBothInterchangePullbackIso`, `rightBothInterchangePullbackIso`, and
`bothBothInterchangePullbackIso`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

open scoped Classical

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {JX JY : Type u}
variable {A : JX → Type u} {B : JY → Type u}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]

/-! ### Reduction lemmas for the dispatched overlap immersion -/

/-- Reduction of `bothAlgDataF` in the *second-coordinate-differs* shape (`p.1 = p'.1`): it is the
`B`-localizing `rightInterchangeOpenImmersion`, prefixed by the object-reduction `eqToHom`. -/
theorem bothAlgDataF_snd (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' : JX × JY) (h : p ≠ p') (h1 : p.1 = p'.1) :
    bothAlgDataF hI gX gY p p' h =
      eqToHom (bothAlgDataV_snd hI gX gY p p' h h1) ≫
        rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p'.2) hI := by
  unfold bothAlgDataF; rw [dif_pos h1]

/-- Reduction of `bothAlgDataF` in the *first-coordinate-differs* shape (`p.1 ≠ p'.1`,
`p.2 = p'.2`): it is the `A`-localizing `interchangeOpenImmersion`. -/
theorem bothAlgDataF_fst (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' : JX × JY) (h : p ≠ p') (h1 : p.1 ≠ p'.1) (h2 : p.2 = p'.2) :
    bothAlgDataF hI gX gY p p' h =
      eqToHom (bothAlgDataV_fst hI gX gY p p' h h1 h2) ≫
        interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI := by
  unfold bothAlgDataF; rw [dif_neg h1, dif_pos h2]

/-- Reduction of `bothAlgDataF` in the *both-coordinates-differ* shape: it is the both-localizing
`bothInterchangeOpenImmersion`. -/
theorem bothAlgDataF_both (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' : JX × JY) (h : p ≠ p') (h1 : p.1 ≠ p'.1) (h2 : p.2 ≠ p'.2) :
    bothAlgDataF hI gX gY p p' h =
      eqToHom (bothAlgDataV_both hI gX gY p p' h h1 h2) ≫
        bothInterchangeOpenImmersion I (gX p.1 p'.1) (gY p.2 p'.2) hI := by
  unfold bothAlgDataF; rw [dif_neg h1, dif_neg h2]

/-! ### Bridging the object-reduction `eqToHom` in pullback legs -/

/-- Replacing each leg of a pullback of open immersions by an `eqToHom`-prefixed copy (the
object-reduction cast carried by `bothAlgDataF`) yields a canonically isomorphic pullback. -/
def eqPullbackIso {V₁ W₁ V₂ W₂ Z : LocallyRingedSpace.{u}} (imm₁ : W₁ ⟶ Z) (imm₂ : W₂ ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion imm₁] [LocallyRingedSpace.IsOpenImmersion imm₂]
    (e₁ : V₁ = W₁) (e₂ : V₂ = W₂) :
    pullback (eqToHom e₁ ≫ imm₁) (eqToHom e₂ ≫ imm₂) ≅ pullback imm₁ imm₂ := by
  subst e₁; subst e₂
  exact pullback.congrHom (by rw [eqToHom_refl, Category.id_comp])
    (by rw [eqToHom_refl, Category.id_comp])
end AlgebraicGeometry
