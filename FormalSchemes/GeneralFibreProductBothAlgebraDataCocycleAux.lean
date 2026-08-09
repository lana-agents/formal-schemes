import FormalSchemes.GeneralFibreProductBothAlgebraDataTPrimeFacAux

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Per-leaf cocycle closers for the dispatched triple-overlap transition `bothAlgDataT'`

This file works towards `bothAlgDataT'_cocycle`, the two-sided analogue of the one-sided
`AlgebraicGeometry.algDataT'_cocycle` (`FormalSchemes.GeneralFibreProductAlgebraData`): the three
dispatched triple-overlap transitions `bothAlgDataT'`
(`FormalSchemes.GeneralFibreProductBothAlgebraDataTPrime`) around a pairwise-distinct
product-index triple compose to the identity.

## Telescoping

Each `bothAlgDataT' p p' p''` is `Sp.inv ≫ (mapSpfIso σX σY).hom ≫ Sp'.hom`, where the *target*
source-iso `Sp'` of `bothAlgDataT' p p' p''` is the **same** named term as the *source* iso of
`bothAlgDataT' p' p'' p`. So in the triple composite the adjacent `Sp'.hom ≫ Sp'.inv` cancel by
`Iso.hom_inv_id_assoc` (twice), leaving `Sp.inv ≫ (M₁ ≫ M₂ ≫ M₃) ≫ Sp.hom` with
`Mᵢ = (mapSpfIso …).hom`. The three `mapSpfIso` collapse to the identity by `mapSpfIso_hom` and the
`⊗̂_R`-transport `CompletedTensorProduct.mapSpf_comp₃`, reducing to two independent per-factor
3-fold `AlgHom` cocycle identities (the `A` factor and the `B` factor), which are the genuine
algebra cocycles `hσcX`/`hσcY` (inverted) combined with the reusable index-transport / self-multiply
atoms of `FormalSchemes.GeneralFibreProductBothAlgebraDataTPrimeFacAux`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

open scoped Classical

/-! ### The generic 3-fold `AlgEquiv` cocycle closer

The `A`- and `B`-factor collapses reduce to: three `AlgEquiv`s composing (as `trans`) to the
identity give the composite of their inverses (as `AlgHom`s) equal to the identity. This is the
two-sided analogue of the `have hf`/`have hg` steps in the one-sided `algDataT'_cocycle`. -/

/-- **Generic 3-fold cocycle closer.** If `e₁ ≪≫ (e₂ ≪≫ e₃) = refl`, then the composite of the three
inverse algebra maps is the identity. -/
theorem trans_cocycle_symm_comp {R : Type u} [CommRing R] {X Y Z : Type u}
    [CommRing X] [CommRing Y] [CommRing Z] [Algebra R X] [Algebra R Y] [Algebra R Z]
    (e₁ : X ≃ₐ[R] Y) (e₂ : Y ≃ₐ[R] Z) (e₃ : Z ≃ₐ[R] X)
    (h : e₁.trans (e₂.trans e₃) = AlgEquiv.refl) :
    e₁.symm.toAlgHom.comp (e₂.symm.toAlgHom.comp e₃.symm.toAlgHom) = AlgHom.id R X := by
  have h2 : (e₁.trans (e₂.trans e₃)).symm = AlgEquiv.refl (R := R) := by
    rw [h, AlgEquiv.refl_symm]
  refine AlgHom.ext fun x => ?_
  have hx := AlgEquiv.ext_iff.mp h2 x
  simp only [AlgEquiv.symm_trans_apply, AlgEquiv.coe_refl, id_eq] at hx
  simpa using hx

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {JX JY : Type u}
variable {A : JX → Type u} {B : JY → Type u}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]

variable (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
variable
  (τX : ∀ (i i' : JX), i ≠ i' →
    (awayCompletion (I.map (algebraMap R (A i))) (gX i i') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A i'))) (gX i' i)))
  (τY : ∀ (j j' : JY), j ≠ j' →
    (awayCompletion (I.map (algebraMap R (B j))) (gY j j') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (B j'))) (gY j' j)))
  (σX : ∀ (i i' i'' : JX), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R (A i))) (gX i i' * gX i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A i'))) (gX i' i'' * gX i' i)))
  (σY : ∀ (j j' j'' : JY), j ≠ j' → j ≠ j'' → j' ≠ j'' →
    (awayCompletion (I.map (algebraMap R (B j))) (gY j j' * gY j j'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (B j'))) (gY j' j'' * gY j' j)))
  (hσcX : ∀ (i i' i'' : JX) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
      (σX i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (A i))) (gX i i' * gX i i'')))
  (hσcY : ∀ (j j' j'' : JY) (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j''),
    (σY j j' j'' h1 h2 h3).trans ((σY j' j'' j h3 h1.symm h2.symm).trans
      (σY j'' j j' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (B j))) (gY j j' * gY j j'')))
/-- **`A`-factor transport 3-fold closer.** Three shared-coordinate transports `eqAlgEquivA` around
a cyclic triple of index equalities compose (as inverse algebra maps) to the identity. -/
theorem eqAlgEquivA_cocycle_symm_comp {i i' i'' : JX} (h1 : i = i') (h2 : i' = i'') (h3 : i'' = i) :
    (eqAlgEquivA (R := R) (A := A) h1).symm.toAlgHom.comp
        ((eqAlgEquivA (R := R) (A := A) h2).symm.toAlgHom.comp
          (eqAlgEquivA (R := R) (A := A) h3).symm.toAlgHom) = AlgHom.id R (A i) := by
  subst h1; subst h2; rfl

/-- **`B`-factor transport 3-fold closer.** -/
theorem eqAlgEquivB_cocycle_symm_comp {j j' j'' : JY} (h1 : j = j') (h2 : j' = j'') (h3 : j'' = j) :
    (eqAlgEquivB (R := R) (B := B) h1).symm.toAlgHom.comp
        ((eqAlgEquivB (R := R) (B := B) h2).symm.toAlgHom.comp
          (eqAlgEquivB (R := R) (B := B) h3).symm.toAlgHom) = AlgHom.id R (B j) := by
  subst h1; subst h2; rfl

variable (hI : I.FG) (p p' p'' : JX × JY)
  (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p'')

include gX gY τX τY σX σY hσcX hσcY hI hpp' hpp'' hp'p''

/-! ### The same-shape `(both, both, both)` cocycle leaf -/

/-- **Cocycle, leaf `(both, both, both)`.** All three cyclic transitions are the fully-generic
`both_both` shape; both per-factor collapses are the genuine algebra cocycles `hσcX`/`hσcY`. -/
theorem bothAlgDataT'_cocycle_both_both_both
    (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2)
    (h1t : p'.1 ≠ p''.1) (h2t : p'.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    letI := bothAlgDataHf hI gX gY p'' p hpp''.symm
    letI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' ≫
        bothAlgDataT' hI gX gY τX τY σX σY p' p'' p hp'p'' hpp'.symm hpp''.symm ≫
      bothAlgDataT' hI gX gY τX τY σX σY p'' p p' hpp''.symm hp'p''.symm hpp' = 𝟙 _ := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := bothAlgDataHf hI gX gY p' p'' hp'p''
  haveI := bothAlgDataHf hI gX gY p' p hpp'.symm
  haveI := bothAlgDataHf hI gX gY p'' p hpp''.symm
  haveI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
  have hmid :
      (mapSpfIso hI (σX p.1 p'.1 p''.1 h1' h1'' h1t)
          (σY p.2 p'.2 p''.2 h2' h2'' h2t)).hom ≫
      (mapSpfIso hI (σX p'.1 p''.1 p.1 h1t (fun e => h1' e.symm) (fun e => h1'' e.symm))
          (σY p'.2 p''.2 p.2 h2t (fun e => h2' e.symm) (fun e => h2'' e.symm))).hom ≫
      (mapSpfIso hI (σX p''.1 p.1 p'.1 (fun e => h1'' e.symm) (fun e => h1t e.symm) h1')
          (σY p''.2 p.2 p'.2 (fun e => h2'' e.symm) (fun e => h2t e.symm) h2')).hom = 𝟙 _ := by
    rw [mapSpfIso_hom, mapSpfIso_hom, mapSpfIso_hom]
    exact mapSpf_comp₃ hI _ _ _ _ _ _
      (trans_cocycle_symm_comp _ _ _ (hσcX p.1 p'.1 p''.1 h1' h1'' h1t))
      (trans_cocycle_symm_comp _ _ _ (hσcY p.2 p'.2 p''.2 h2' h2'' h2t))
  rw [bothAlgDataT'_both_both_both gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
      h1' h2' h1'' h2'' h1t h2t,
    bothAlgDataT'_both_both_both gX gY τX τY σX σY hI p' p'' p hp'p'' hpp'.symm hpp''.symm
      h1t h2t (fun e => h1' e.symm) (fun e => h2' e.symm) (fun e => h1'' e.symm)
      (fun e => h2'' e.symm),
    bothAlgDataT'_both_both_both gX gY τX τY σX σY hI p'' p p' hpp''.symm hp'p''.symm hpp'
      (fun e => h1'' e.symm) (fun e => h2'' e.symm) (fun e => h1t e.symm) (fun e => h2t e.symm)
      h1' h2']
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, reassoc_of% hmid, Iso.inv_hom_id]

/-! ### The same-shape `(snd, snd)` cocycle leaf -/

omit hσcX in
/-- **Cocycle, leaf `(snd, snd)`.** All three cyclic transitions are the `snd_snd` shape; the
`A`-factor collapse is the shared-coordinate transport `eqAlgEquivA`, the `B`-factor collapse is the
genuine algebra cocycle `hσcY`. -/
theorem bothAlgDataT'_cocycle_snd_snd (h1' : p.1 = p'.1) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    letI := bothAlgDataHf hI gX gY p'' p hpp''.symm
    letI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' ≫
        bothAlgDataT' hI gX gY τX τY σX σY p' p'' p hp'p'' hpp'.symm hpp''.symm ≫
      bothAlgDataT' hI gX gY τX τY σX σY p'' p p' hpp''.symm hp'p''.symm hpp' = 𝟙 _ := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := bothAlgDataHf hI gX gY p' p'' hp'p''
  haveI := bothAlgDataHf hI gX gY p' p hpp'.symm
  haveI := bothAlgDataHf hI gX gY p'' p hpp''.symm
  haveI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
  have h2' : p.2 ≠ p'.2 := fun e => hpp' (Prod.ext h1' e)
  have h2'' : p.2 ≠ p''.2 := fun e => hpp'' (Prod.ext h1'' e)
  have h2t : p'.2 ≠ p''.2 := fun e => hp'p'' (Prod.ext (h1'.symm.trans h1'') e)
  have hmid :
      (mapSpfIso hI (eqAlgEquivA (A := A) h1') (σY p.2 p'.2 p''.2 h2' h2'' h2t)).hom ≫
      (mapSpfIso hI (eqAlgEquivA (A := A) (h1'.symm.trans h1''))
          (σY p'.2 p''.2 p.2 h2t (fun e => h2' e.symm) (fun e => h2'' e.symm))).hom ≫
      (mapSpfIso hI (eqAlgEquivA (A := A) h1''.symm)
          (σY p''.2 p.2 p'.2 (fun e => h2'' e.symm) (fun e => h2t e.symm) h2')).hom = 𝟙 _ := by
    rw [mapSpfIso_hom, mapSpfIso_hom, mapSpfIso_hom]
    exact mapSpf_comp₃ hI _ _ _ _ _ _
      (eqAlgEquivA_cocycle_symm_comp (A := A) h1' (h1'.symm.trans h1'') h1''.symm)
      (trans_cocycle_symm_comp _ _ _ (hσcY p.2 p'.2 p''.2 h2' h2'' h2t))
  rw [bothAlgDataT'_snd_snd gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p'' h1' h1'',
    bothAlgDataT'_snd_snd gX gY τX τY σX σY hI p' p'' p hp'p'' hpp'.symm hpp''.symm
      (h1'.symm.trans h1'') h1'.symm,
    bothAlgDataT'_snd_snd gX gY τX τY σX σY hI p'' p p' hpp''.symm hp'p''.symm hpp'
      h1''.symm (h1''.symm.trans h1')]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, reassoc_of% hmid, Iso.inv_hom_id]

/-! ### The same-shape `(fst, fst)` cocycle leaf -/

omit hσcY in
/-- **Cocycle, leaf `(fst, fst)`.** All three cyclic transitions are the `fst_fst` shape; the
`A`-factor collapse is the genuine algebra cocycle `hσcX`, the `B`-factor collapse is the
shared-coordinate transport `eqAlgEquivB`. -/
theorem bothAlgDataT'_cocycle_fst_fst (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 = p''.2) (h1t : p'.1 ≠ p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    letI := bothAlgDataHf hI gX gY p'' p hpp''.symm
    letI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' ≫
        bothAlgDataT' hI gX gY τX τY σX σY p' p'' p hp'p'' hpp'.symm hpp''.symm ≫
      bothAlgDataT' hI gX gY τX τY σX σY p'' p p' hpp''.symm hp'p''.symm hpp' = 𝟙 _ := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := bothAlgDataHf hI gX gY p' p'' hp'p''
  haveI := bothAlgDataHf hI gX gY p' p hpp'.symm
  haveI := bothAlgDataHf hI gX gY p'' p hpp''.symm
  haveI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
  have h1t' : p'.1 ≠ p.1 := fun e => h1' e.symm
  have hmid :
      (mapSpfIso hI (σX p.1 p'.1 p''.1 h1' h1'' h1t) (eqAlgEquivB (B := B) h2')).hom ≫
      (mapSpfIso hI (σX p'.1 p''.1 p.1 h1t (fun e => h1' e.symm) (fun e => h1'' e.symm))
          (eqAlgEquivB (B := B) (h2'.symm.trans h2''))).hom ≫
      (mapSpfIso hI (σX p''.1 p.1 p'.1 (fun e => h1'' e.symm) (fun e => h1t e.symm) h1')
          (eqAlgEquivB (B := B) h2''.symm)).hom = 𝟙 _ := by
    rw [mapSpfIso_hom, mapSpfIso_hom, mapSpfIso_hom]
    exact mapSpf_comp₃ hI _ _ _ _ _ _
      (trans_cocycle_symm_comp _ _ _ (hσcX p.1 p'.1 p''.1 h1' h1'' h1t))
      (eqAlgEquivB_cocycle_symm_comp (B := B) h2' (h2'.symm.trans h2'') h2''.symm)
  rw [bothAlgDataT'_fst_fst gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p'' h1' h2' h1'' h2'' h1t,
    bothAlgDataT'_fst_fst gX gY τX τY σX σY hI p' p'' p hp'p'' hpp'.symm hpp''.symm
      h1t (h2'.symm.trans h2'') (fun e => h1' e.symm) h2'.symm (fun e => h1'' e.symm),
    bothAlgDataT'_fst_fst gX gY τX τY σX σY hI p'' p p' hpp''.symm hp'p''.symm hpp'
      (fun e => h1'' e.symm) h2''.symm (fun e => h1t e.symm) (h2''.symm.trans h2') h1']
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, reassoc_of% hmid, Iso.inv_hom_id]

end AlgebraicGeometry
