import FormalSchemes.GeneralFibreProductBothAlgebraDataTPrime

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The `t_fac` law of the dispatched triple-overlap transition `bothAlgDataT'`

This file works towards `bothAlgDataT'_fac`, the two-sided analogue of the one-sided
`AlgebraicGeometry.algDataT'_fac` (`FormalSchemes.GeneralFibreProductAlgebraData`): the dispatched
triple-overlap transition `bothAlgDataT'` (`FormalSchemes.GeneralFibreProductBothAlgebraDataTPrime`)
is compatible with the double-overlap transition `bothAlgDataT`, matching the `t_fac` field of
`AlgebraicGeometry.BothChartedFibreDatum`.

## Interface

The eventual smart-constructor caller supplies the σ/τ compatibility inputs `hστX`/`hστY` in exactly
the one-sided form (once for the `A` factor, once for the `B` factor): the composite
`(σX i i' i'').symm ∘ furtherLocSnd (gX i' i'') (gX i' i)` equals
`furtherLocFst (gX i i') (gX i i'') ∘ (τX i i').symm`, and the `B`-analogue. These are vacuous on a
subsingleton index (no pairwise-distinct triple), so the two-patch validation discharges them.

## Reduction

`bothAlgDataT p p'` is coordinate-difference dispatched; the three shape reductions
`bothAlgDataT_snd`/`_fst`/`_both` expose it as `eqToHom ≫ (mapSpfIso …).hom ≫ eqToHom`. Each `t_fac`
leaf then reduces — via the source/target leg laws `bothAlgDataSrcIso_*_*_hom_fst/_snd`, the
functoriality `mapSpf_comp`, and (for mixed leaves) `interchangeOpenImmersion_eq_mapSpf` — to two
independent algebra identities on the two tensor factors: the genuine-σ factor is exactly
`hστX`/`hστY`, and the shared-coordinate transport factor is discharged by `AlgHom.id_comp`.

The three *same-shape* leaves (`snd_snd`, `fst_fst`, `both_both_both`), whose source and target legs
are both plain `mapSpf`, are proved here as the `bothAlgDataT'_fac_*` lemmas.
The twelve *mixed-shape* leaves require, in addition, the self-multiply expand/collapse and
index-transport algebra compatibilities of the away-completion factors (completion functoriality
over the localisation identities `awayCompletionSelfMulEquiv`/`furtherLoc*`), and are deferred.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
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

/-! ### Shape reductions of the double-overlap transition `bothAlgDataT` -/

section Reductions

variable (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
  (τX : ∀ (i i' : JX), i ≠ i' →
    (awayCompletion (I.map (algebraMap R (A i))) (gX i i') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A i'))) (gX i' i)))
  (τY : ∀ (j j' : JY), j ≠ j' →
    (awayCompletion (I.map (algebraMap R (B j))) (gY j j') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (B j'))) (gY j' j)))
variable (hI : I.FG) (p p' : JX × JY) (h : p ≠ p')

/-- Reduction of `bothAlgDataT` in the *second-coordinate-differs* shape (`p.1 = p'.1`). -/
theorem bothAlgDataT_snd (h1 : p.1 = p'.1) :
    bothAlgDataT hI gX gY τX τY p p' h =
      eqToHom (bothAlgDataV_snd hI gX gY p p' h h1) ≫
        (mapSpfIso hI (eqAlgEquivA h1) (τY p.2 p'.2 (fun e => h (Prod.ext h1 e)))).hom ≫
        eqToHom (bothAlgDataV_snd hI gX gY p' p h.symm h1.symm).symm := by
  unfold bothAlgDataT; rw [dif_pos h1]

/-- Reduction of `bothAlgDataT` in the *first-coordinate-differs* shape (`p.1 ≠ p'.1`,
`p.2 = p'.2`). -/
theorem bothAlgDataT_fst (h1 : p.1 ≠ p'.1) (h2 : p.2 = p'.2) :
    bothAlgDataT hI gX gY τX τY p p' h =
      eqToHom (bothAlgDataV_fst hI gX gY p p' h h1 h2) ≫
        (mapSpfIso hI (τX p.1 p'.1 h1) (eqAlgEquivB h2)).hom ≫
        eqToHom (bothAlgDataV_fst hI gX gY p' p h.symm (fun e => h1 e.symm) h2.symm).symm := by
  unfold bothAlgDataT; rw [dif_neg h1, dif_pos h2]

/-- Reduction of `bothAlgDataT` in the *both-coordinates-differ* shape. -/
theorem bothAlgDataT_both (h1 : p.1 ≠ p'.1) (h2 : p.2 ≠ p'.2) :
    bothAlgDataT hI gX gY τX τY p p' h =
      eqToHom (bothAlgDataV_both hI gX gY p p' h h1 h2) ≫
        (mapSpfIso hI (τX p.1 p'.1 h1) (τY p.2 p'.2 h2)).hom ≫
        eqToHom (bothAlgDataV_both hI gX gY p' p h.symm (fun e => h1 e.symm)
          (fun e => h2 e.symm)).symm := by
  unfold bothAlgDataT; rw [dif_neg h1, dif_neg h2]

end Reductions

/-! ### The same-shape `t_fac` leaves

The three leaves whose source and target legs are both plain `mapSpf` (no interchange immersion):
the `A`- and `B`-factor compatibilities are the genuine `hστX`/`hστY` and the shared-coordinate
transport `eqAlgEquiv` (discharged by `AlgHom.id_comp`/`comp_id`). -/

section Leaves

variable (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j) (hI : I.FG)
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
  (hστX : ∀ (i i' i'' : JX) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (gX i' i'') (gX i' i) hI) =
      (furtherLocFst I (gX i i') (gX i i'') hI).comp (τX i i' h1).symm.toAlgHom)
  (hστY : ∀ (j j' j'' : JY) (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j''),
    (σY j j' j'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (gY j' j'') (gY j' j) hI) =
      (furtherLocFst I (gY j j') (gY j j'') hI).comp (τY j j' h1).symm.toAlgHom)
variable (p p' p'' : JX × JY)
  (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p'')

include gX gY τX τY σX σY hστX hστY hI hpp' hpp'' hp'p''

/-- **`t_fac`, leaf `(snd, snd)`.** `A`-factor transport, `B`-factor genuine (`hστY`). -/
theorem bothAlgDataT'_fac_snd_snd (h1' : p.1 = p'.1) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' ≫
        pullback.snd (bothAlgDataF hI gX gY p' p'' hp'p'') (bothAlgDataF hI gX gY p' p hpp'.symm) =
      pullback.fst (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') ≫
        bothAlgDataT hI gX gY τX τY p p' hpp' := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := bothAlgDataHf hI gX gY p' p'' hp'p''
  haveI := bothAlgDataHf hI gX gY p' p hpp'.symm
  have h2' : p.2 ≠ p'.2 := fun e => hpp' (Prod.ext h1' e)
  have h2'' : p.2 ≠ p''.2 := fun e => hpp'' (Prod.ext h1'' e)
  rw [bothAlgDataT'_snd_snd gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p'' h1' h1'']
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_snd_snd hI gX gY p p' p'' hpp' hpp'' h1' h1'').inv ≫
        mapSpf hI (AlgHom.id R (A p.1))
          (furtherLocFst I (gY p.2 p'.2) (gY p.2 p''.2) hI) ≫
        eqToHom (bothAlgDataV_snd hI gX gY p p' hpp' h1').symm := by
    rw [← bothAlgDataSrcIso_snd_snd_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h1'',
      Iso.inv_hom_id_assoc]
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_snd_snd_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm
      (h1'.symm.trans h1'') h1'.symm, hfst,
    bothAlgDataT_snd gX gY τX τY hI p p' hpp' h1']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [AlgHom.id_comp, AlgHom.comp_id,
    hστY p.2 p'.2 p''.2 h2' h2'' (fun eq => hp'p'' (Prod.ext (h1'.symm.trans h1'') eq))]

/-- **`t_fac`, leaf `(fst, fst)`.** `A`-factor genuine (`hστX`), `B`-factor transport. -/
theorem bothAlgDataT'_fac_fst_fst (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 = p''.2) (h1t : p'.1 ≠ p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' ≫
        pullback.snd (bothAlgDataF hI gX gY p' p'' hp'p'') (bothAlgDataF hI gX gY p' p hpp'.symm) =
      pullback.fst (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') ≫
        bothAlgDataT hI gX gY τX τY p p' hpp' := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := bothAlgDataHf hI gX gY p' p'' hp'p''
  haveI := bothAlgDataHf hI gX gY p' p hpp'.symm
  rw [bothAlgDataT'_fst_fst gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
    h1' h2' h1'' h2'' h1t]
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_fst_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        mapSpf hI (furtherLocFst I (gX p.1 p'.1) (gX p.1 p''.1) hI)
          (AlgHom.id R (B p.2)) ≫
        eqToHom (bothAlgDataV_fst hI gX gY p p' hpp' h1' h2').symm := by
    rw [← bothAlgDataSrcIso_fst_fst_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h2'
      h1'' h2'', Iso.inv_hom_id_assoc]
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_fst_fst_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm h1t
      (h2'.symm.trans h2'') (fun e => h1' e.symm) h2'.symm,
    hfst, bothAlgDataT_fst gX gY τX τY hI p p' hpp' h1' h2']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [AlgHom.id_comp, AlgHom.comp_id, hστX p.1 p'.1 p''.1 h1' h1'' h1t]

/-- **`t_fac`, leaf `(both, both)`, target `both`.** Both factors genuine (`hστX`, `hστY`). -/
theorem bothAlgDataT'_fac_both_both_both (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 ≠ p''.2) (h1t : p'.1 ≠ p''.1) (h2t : p'.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' ≫
        pullback.snd (bothAlgDataF hI gX gY p' p'' hp'p'') (bothAlgDataF hI gX gY p' p hpp'.symm) =
      pullback.fst (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') ≫
        bothAlgDataT hI gX gY τX τY p p' hpp' := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := bothAlgDataHf hI gX gY p' p'' hp'p''
  haveI := bothAlgDataHf hI gX gY p' p hpp'.symm
  rw [bothAlgDataT'_both_both_both gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
    h1' h2' h1'' h2'' h1t h2t]
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_both_both hI gX gY p p' p'' hpp' hpp'' h1' h2'
        h1'' h2'').inv ≫
        mapSpf hI (furtherLocFst I (gX p.1 p'.1) (gX p.1 p''.1) hI)
          (furtherLocFst I (gY p.2 p'.2) (gY p.2 p''.2) hI) ≫
        eqToHom (bothAlgDataV_both hI gX gY p p' hpp' h1' h2').symm := by
    rw [← bothAlgDataSrcIso_both_both_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h2'
      h1'' h2'', Iso.inv_hom_id_assoc]
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_both_both_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm h1t h2t
      (fun e => h1' e.symm) (fun e => h2' e.symm),
    hfst, bothAlgDataT_both gX gY τX τY hI p p' hpp' h1' h2']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [hστX p.1 p'.1 p''.1 h1' h1'' h1t,
    hστY p.2 p'.2 p''.2 h2' h2'' h2t]

end Leaves

end AlgebraicGeometry
