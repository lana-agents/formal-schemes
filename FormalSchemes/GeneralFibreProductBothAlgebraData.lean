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

/-- The `pullback.fst` leg of `eqPullbackIso`'s inverse: it re-embeds the un-cast pullback into the
`eqToHom`-cast one, recording the object-reduction cast `eqToHom e₁.symm` on the first factor. -/
theorem eqPullbackIso_inv_fst {V₁ W₁ V₂ W₂ Z : LocallyRingedSpace.{u}} (imm₁ : W₁ ⟶ Z)
    (imm₂ : W₂ ⟶ Z) [LocallyRingedSpace.IsOpenImmersion imm₁]
    [LocallyRingedSpace.IsOpenImmersion imm₂] (e₁ : V₁ = W₁) (e₂ : V₂ = W₂) :
    (eqPullbackIso imm₁ imm₂ e₁ e₂).inv ≫
        pullback.fst (eqToHom e₁ ≫ imm₁) (eqToHom e₂ ≫ imm₂) =
      pullback.fst imm₁ imm₂ ≫ eqToHom e₁.symm := by
  subst e₁; subst e₂
  simp [eqPullbackIso, pullback.lift_fst]

/-- The `pullback.snd` leg of `eqPullbackIso`'s inverse. -/
theorem eqPullbackIso_inv_snd {V₁ W₁ V₂ W₂ Z : LocallyRingedSpace.{u}} (imm₁ : W₁ ⟶ Z)
    (imm₂ : W₂ ⟶ Z) [LocallyRingedSpace.IsOpenImmersion imm₁]
    [LocallyRingedSpace.IsOpenImmersion imm₂] (e₁ : V₁ = W₁) (e₂ : V₂ = W₂) :
    (eqPullbackIso imm₁ imm₂ e₁ e₂).inv ≫
        pullback.snd (eqToHom e₁ ≫ imm₁) (eqToHom e₂ ≫ imm₂) =
      pullback.snd imm₁ imm₂ ≫ eqToHom e₂.symm := by
  subst e₁; subst e₂
  simp [eqPullbackIso, pullback.lift_snd]

/-- The `pullback.fst` leg of the inverse of `pullback.congrHom`: it transports the first leg back
across the equalities of the two cospan legs. -/
theorem congrHom_inv_fst {C : Type*} [Category C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) [HasPullback f₁ g₁] [HasPullback f₂ g₂] :
    (pullback.congrHom h₁ h₂).inv ≫ pullback.fst f₁ g₁ = pullback.fst f₂ g₂ := by
  simp [pullback.congrHom_inv, pullback.lift_fst]

/-- The `pullback.snd` leg of the inverse of `pullback.congrHom`. -/
theorem congrHom_inv_snd {C : Type*} [Category C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) [HasPullback f₁ g₁] [HasPullback f₂ g₂] :
    (pullback.congrHom h₁ h₂).inv ≫ pullback.snd f₁ g₁ = pullback.snd f₂ g₂ := by
  simp [pullback.congrHom_inv, pullback.lift_snd]

/-! ### The dispatched source/target pullback isomorphisms

For a chart `p` with two legs to distinct charts `p'` and `p''`, the triple overlap
`pullback (bothAlgDataF p p') (bothAlgDataF p p'')` is identified with the appropriate
double-localized `Spf` via the per-shape interchange-pullback isomorphism, bridged across the
object-reduction `eqToHom` casts by `eqPullbackIso` and `pullback.congrHom`. There is one
identification per *ordered pair of leg shapes*; the six available shapes are the domains of the six
interchange-pullback isomorphisms. -/

/-- **Source iso, (2nd, 2nd) shape.** Both legs localize the `B` factor (`p.1 = p'.1`,
`p.1 = p''.1`): the triple overlap is `Spf(A_{p.1} ⊗̂_R B_{p.2}{1/(g_Y·g_Y)})`. -/
def bothAlgDataSrcIso_snd_snd (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 = p'.1) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (locallyRingedSpaceObj (idealOfDefinition R I (A p.1)
        (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2 * gY p.2 p''.2))) ≅
      pullback (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'')) := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p'.2) hI
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p''.2) hI
  exact rightInterchangePullbackIso (A := A p.1) I (gY p.2 p'.2) (gY p.2 p''.2) hI ≪≫
    (eqPullbackIso (rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p'.2) hI)
      (rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p''.2) hI)
      (bothAlgDataV_snd hI gX gY p p' hpp' h1')
      (bothAlgDataV_snd hI gX gY p p'' hpp'' h1'')).symm ≪≫
    (pullback.congrHom (bothAlgDataF_snd hI gX gY p p' hpp' h1')
      (bothAlgDataF_snd hI gX gY p p'' hpp'' h1'')).symm

/-- **Source iso, (1st, 1st) shape.** Both legs localize the `A` factor. -/
def bothAlgDataSrcIso_fst_fst (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1 * gX p.1 p''.1)) (B p.2)) ≅
      pullback (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'')) := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B p.2) I (gX p.1 p''.1) hI
  exact interchangePullbackIso (B := B p.2) I (gX p.1 p'.1) (gX p.1 p''.1) hI ≪≫
    (eqPullbackIso (interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI)
      (interchangeOpenImmersion (B := B p.2) I (gX p.1 p''.1) hI)
      (bothAlgDataV_fst hI gX gY p p' hpp' h1' h2')
      (bothAlgDataV_fst hI gX gY p p'' hpp'' h1'' h2'')).symm ≪≫
    (pullback.congrHom (bothAlgDataF_fst hI gX gY p p' hpp' h1' h2')
      (bothAlgDataF_fst hI gX gY p p'' hpp'' h1'' h2'')).symm

/-- **Source iso, (both, both) shape.** Both legs localize both factors. -/
def bothAlgDataSrcIso_both_both (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1 * gX p.1 p''.1))
        (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2 * gY p.2 p''.2))) ≅
      pullback (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'')) := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (gX p.1 p'.1) (gY p.2 p'.2) hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (gX p.1 p''.1) (gY p.2 p''.2) hI
  exact bothBothInterchangePullbackIso I (gX p.1 p'.1) (gX p.1 p''.1)
      (gY p.2 p'.2) (gY p.2 p''.2) hI ≪≫
    (eqPullbackIso (bothInterchangeOpenImmersion I (gX p.1 p'.1) (gY p.2 p'.2) hI)
      (bothInterchangeOpenImmersion I (gX p.1 p''.1) (gY p.2 p''.2) hI)
      (bothAlgDataV_both hI gX gY p p' hpp' h1' h2')
      (bothAlgDataV_both hI gX gY p p'' hpp'' h1'' h2'')).symm ≪≫
    (pullback.congrHom (bothAlgDataF_both hI gX gY p p' hpp' h1' h2')
      (bothAlgDataF_both hI gX gY p p'' hpp'' h1'' h2'')).symm

/-- **Source iso, (1st, 2nd) shape.** The first leg localizes `A` (`p.1 ≠ p'.1`, `p.2 = p'.2`), the
second localizes `B` (`p.1 = p''.1`): the triple overlap is the mixed double-localized chart, via
`mixedInterchangePullbackIso`. -/
def bothAlgDataSrcIso_fst_snd (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1))
        (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p''.2))) ≅
      pullback (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'')) := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p''.2) hI
  exact mixedInterchangePullbackIso (A := A p.1) (B := B p.2) I (gX p.1 p'.1) (gY p.2 p''.2) hI ≪≫
    (eqPullbackIso (interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI)
      (rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p''.2) hI)
      (bothAlgDataV_fst hI gX gY p p' hpp' h1' h2')
      (bothAlgDataV_snd hI gX gY p p'' hpp'' h1'')).symm ≪≫
    (pullback.congrHom (bothAlgDataF_fst hI gX gY p p' hpp' h1' h2')
      (bothAlgDataF_snd hI gX gY p p'' hpp'' h1'')).symm

/-- **Source iso, (1st, both) shape.** The first leg localizes `A`, the second localizes both
factors, via `firstBothInterchangePullbackIso`. -/
def bothAlgDataSrcIso_fst_both (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1 * gX p.1 p''.1))
        (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p''.2))) ≅
      pullback (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'')) := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (gX p.1 p''.1) (gY p.2 p''.2) hI
  exact firstBothInterchangePullbackIso I (gX p.1 p'.1) (gX p.1 p''.1) (gY p.2 p''.2) hI ≪≫
    (eqPullbackIso (interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI)
      (bothInterchangeOpenImmersion I (gX p.1 p''.1) (gY p.2 p''.2) hI)
      (bothAlgDataV_fst hI gX gY p p' hpp' h1' h2')
      (bothAlgDataV_both hI gX gY p p'' hpp'' h1'' h2'')).symm ≪≫
    (pullback.congrHom (bothAlgDataF_fst hI gX gY p p' hpp' h1' h2')
      (bothAlgDataF_both hI gX gY p p'' hpp'' h1'' h2'')).symm

/-- **Source iso, (2nd, both) shape.** The first leg localizes `B`, the second localizes both
factors, via `rightBothInterchangePullbackIso`. -/
def bothAlgDataSrcIso_snd_both (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p''.1))
        (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2 * gY p.2 p''.2))) ≅
      pullback (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'')) := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p'.2) hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (gX p.1 p''.1) (gY p.2 p''.2) hI
  exact rightBothInterchangePullbackIso I (gX p.1 p''.1) (gY p.2 p'.2) (gY p.2 p''.2) hI ≪≫
    (eqPullbackIso (rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p'.2) hI)
      (bothInterchangeOpenImmersion I (gX p.1 p''.1) (gY p.2 p''.2) hI)
      (bothAlgDataV_snd hI gX gY p p' hpp' h1')
      (bothAlgDataV_both hI gX gY p p'' hpp'' h1'' h2'')).symm ≪≫
    (pullback.congrHom (bothAlgDataF_snd hI gX gY p p' hpp' h1')
      (bothAlgDataF_both hI gX gY p p'' hpp'' h1'' h2'')).symm

/-- **Source iso, (2nd, 1st) shape.** Reverse of the mixed shape: first leg localizes `B`, second
localizes `A`. Obtained from `bothAlgDataSrcIso_fst_snd` (with the two legs swapped) followed by
`pullbackSymmetry`. -/
def bothAlgDataSrcIso_snd_fst (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p''.1))
        (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2))) ≅
      pullback (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'')) := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  exact bothAlgDataSrcIso_fst_snd hI gX gY p p'' p' hpp'' hpp' h1'' h2'' h1' ≪≫
    pullbackSymmetry (bothAlgDataF hI gX gY p p'' hpp'') (bothAlgDataF hI gX gY p p' hpp')

/-- **Source iso, (both, 1st) shape.** Reverse of the (1st, both) shape. -/
def bothAlgDataSrcIso_both_fst (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p''.1 * gX p.1 p'.1))
        (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2))) ≅
      pullback (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'')) := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  exact bothAlgDataSrcIso_fst_both hI gX gY p p'' p' hpp'' hpp' h1'' h2'' h1' h2' ≪≫
    pullbackSymmetry (bothAlgDataF hI gX gY p p'' hpp'') (bothAlgDataF hI gX gY p p' hpp')

/-- **Source iso, (both, 2nd) shape.** Reverse of the (2nd, both) shape. -/
def bothAlgDataSrcIso_both_snd (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1))
        (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p''.2 * gY p.2 p'.2))) ≅
      pullback (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'')) := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  exact bothAlgDataSrcIso_snd_both hI gX gY p p'' p' hpp'' hpp' h1'' h1' h2' ≪≫
    pullbackSymmetry (bothAlgDataF hI gX gY p p'' hpp'') (bothAlgDataF hI gX gY p p' hpp')

end AlgebraicGeometry
