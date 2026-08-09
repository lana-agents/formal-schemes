import FormalSchemes.GeneralFibreProductBothAlgebraDataTPrime
import FormalSchemes.GeneralFibreProductBothAlgebraDataTPrimeFacAux

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

omit hστX in
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

omit hστY in
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

/-! ### The mixed-shape `t_fac` leaves

For these the source and/or target leg is a mixed interchange immersion; converting it to `mapSpf`
via `interchangeOpenImmersion_eq_mapSpf`/`rightInterchangeOpenImmersion_eq_mapSpf` restores the same
`mapSpf`-functoriality reduction. The two per-factor closers are drawn from the Aux atoms:
`awayIdxTrans*_scalarTower_compat` for the shared-coordinate index transport, and
`trans_selfMul_symm_comp` (via `awayCongrElt*`/`awaySelfMul*`) for the self-multiply collapse. -/

omit hστX hστY in
/-- **`t_fac`, leaf `(snd, fst)`.** `A`-factor index transport, `B`-factor self-multiply collapse
(the genuine `τY` survives). -/
theorem bothAlgDataT'_fac_snd_fst (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 = p''.2) :
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
  rw [bothAlgDataT'_snd_fst gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p'' h1' h1'' h2'']
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_snd_fst hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'').inv ≫
        interchangeOpenImmersion
            (B := awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2))
            I (gX p.1 p''.1) hI ≫
        eqToHom (bothAlgDataV_snd hI gX gY p p' hpp' h1').symm := by
    rw [← bothAlgDataSrcIso_snd_fst_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'',
      Iso.inv_hom_id_assoc]
  have hB : ((τY p.2 p'.2 h2').trans ((awaySelfMulB hI (gY p'.2 p.2)).trans
        (awayCongrEltB (show gY p'.2 p.2 * gY p'.2 p.2 = gY p'.2 p.2 * gY p'.2 p''.2
          from by rw [h2''])))).symm.toAlgHom.comp
        (furtherLocFst I (gY p'.2 p.2) (gY p'.2 p''.2) hI) =
      (τY p.2 p'.2 h2').symm.toAlgHom :=
    trans_selfMul_symm_comp _ _ _ _ (by
      rw [awayCongrEltB_symm_comp_furtherLocFst (gY p'.2 p.2) (gY p'.2 p''.2)
          (show gY p'.2 p.2 * gY p'.2 p.2 = gY p'.2 p.2 * gY p'.2 p''.2 from by rw [h2''])
          (show gY p'.2 p''.2 = gY p'.2 p.2 from by rw [h2'']) hI,
        awaySelfMulB_symm_comp_furtherLocFst_self (gY p'.2 p.2) hI])
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_both_snd_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm
      (fun e => h1'' (h1'.trans e)) (fun e => h2' (h2''.trans e.symm)) h1'.symm,
    hfst, interchangeOpenImmersion_eq_mapSpf
      (B := awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2)) I (gX p.1 p''.1) hI,
    bothAlgDataT_snd gX gY τX τY hI p p' hpp' h1']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [AlgHom.id_comp,
    awayIdxTransA_scalarTower_compat h1' (fun x => gX x p''.1), hB]

omit hστX hστY in
/-- **`t_fac`, leaf `(snd, both)`, target `fst`.** `A`-factor index transport, `B`-factor
self-multiply expand. -/
theorem bothAlgDataT'_fac_snd_both_fst (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2)
    (h2t : p'.2 = p''.2) :
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
  rw [bothAlgDataT'_snd_both_fst gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
    h1' h1'' h2'' h2t]
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_snd_both hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'').inv ≫
        mapSpf hI (IsScalarTower.toAlgHom R (A p.1)
            (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p''.1)))
          (furtherLocFst I (gY p.2 p'.2) (gY p.2 p''.2) hI) ≫
        eqToHom (bothAlgDataV_snd hI gX gY p p' hpp' h1').symm := by
    rw [← bothAlgDataSrcIso_snd_both_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'',
      Iso.inv_hom_id_assoc]
  have hB : ((awayCongrEltB (show gY p.2 p'.2 * gY p.2 p''.2 = gY p.2 p'.2 * gY p.2 p'.2
          from by rw [h2t])).trans
        ((awaySelfMulB hI (gY p.2 p'.2)).symm.trans (τY p.2 p'.2 h2'))).symm.toAlgHom =
      (furtherLocFst I (gY p.2 p'.2) (gY p.2 p''.2) hI).comp
        (τY p.2 p'.2 h2').symm.toAlgHom :=
    trans_expand_symm_toAlgHom _ _ _ _
      (awayCongrEltB_symm_comp_awaySelfMulB (gY p.2 p'.2) (gY p.2 p''.2)
        (show gY p.2 p'.2 * gY p.2 p''.2 = gY p.2 p'.2 * gY p.2 p'.2 from by rw [h2t])
        (show gY p.2 p''.2 = gY p.2 p'.2 from by rw [h2t]) hI)
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_fst_snd_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm
      (fun e => h1'' (h1'.trans e)) h2t h1'.symm,
    interchangeOpenImmersion_eq_mapSpf
      (B := awayCompletion (I.map (algebraMap R (B p'.2))) (gY p'.2 p.2)) I (gX p'.1 p''.1) hI,
    hfst, bothAlgDataT_snd gX gY τX τY hI p p' hpp' h1']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [AlgHom.comp_id,
    awayIdxTransA_scalarTower_compat h1' (fun x => gX x p''.1), hB]

omit hστX hστY in
/-- **`t_fac`, leaf `(fst, snd)`.** `A`-factor self-multiply collapse, `B`-factor index transport
(mirror of `(snd, fst)`). -/
theorem bothAlgDataT'_fac_fst_snd (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 = p''.1) :
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
  rw [bothAlgDataT'_fst_snd gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p'' h1' h2' h1'']
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_fst_snd hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'').inv ≫
        rightInterchangeOpenImmersion
            (A := awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1))
            I (gY p.2 p''.2) hI ≫
        eqToHom (bothAlgDataV_fst hI gX gY p p' hpp' h1' h2').symm := by
    rw [← bothAlgDataSrcIso_fst_snd_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'',
      Iso.inv_hom_id_assoc]
  have hA : ((τX p.1 p'.1 h1').trans ((awaySelfMulA hI (gX p'.1 p.1)).trans
        (awayCongrEltA (show gX p'.1 p.1 * gX p'.1 p.1 = gX p'.1 p.1 * gX p'.1 p''.1
          from by rw [h1''])))).symm.toAlgHom.comp
        (furtherLocFst I (gX p'.1 p.1) (gX p'.1 p''.1) hI) =
      (τX p.1 p'.1 h1').symm.toAlgHom :=
    trans_selfMul_symm_comp _ _ _ _ (by
      rw [awayCongrEltA_symm_comp_furtherLocFst (gX p'.1 p.1) (gX p'.1 p''.1)
          (show gX p'.1 p.1 * gX p'.1 p.1 = gX p'.1 p.1 * gX p'.1 p''.1 from by rw [h1''])
          (show gX p'.1 p''.1 = gX p'.1 p.1 from by rw [h1'']) hI,
        awaySelfMulA_symm_comp_furtherLocFst_self (gX p'.1 p.1) hI])
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_both_fst_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm
      (fun e => h1' (h1''.trans e.symm)) (fun e => hpp'' (Prod.ext h1'' (h2'.trans e)))
      (fun e => h1' e.symm) h2'.symm,
    hfst, rightInterchangeOpenImmersion_eq_mapSpf
      (A := awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1)) I (gY p.2 p''.2) hI,
    bothAlgDataT_fst gX gY τX τY hI p p' hpp' h1' h2']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [AlgHom.id_comp,
    awayIdxTransB_scalarTower_compat h2' (fun y => gY y p''.2), hA]

omit hστX hστY in
/-- **`t_fac`, leaf `(fst, both)`, target `snd`.** `A`-factor self-multiply expand, `B`-factor index
transport (mirror of `(snd, both)`/target `fst`). -/
theorem bothAlgDataT'_fac_fst_both_snd (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 ≠ p''.2) (h1t : p'.1 = p''.1) :
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
  rw [bothAlgDataT'_fst_both_snd gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
    h1' h2' h1'' h2'' h1t]
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_fst_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        mapSpf hI (furtherLocFst I (gX p.1 p'.1) (gX p.1 p''.1) hI)
          (IsScalarTower.toAlgHom R (B p.2)
            (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p''.2))) ≫
        eqToHom (bothAlgDataV_fst hI gX gY p p' hpp' h1' h2').symm := by
    rw [← bothAlgDataSrcIso_fst_both_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'',
      Iso.inv_hom_id_assoc]
  have hA : ((awayCongrEltA (show gX p.1 p'.1 * gX p.1 p''.1 = gX p.1 p'.1 * gX p.1 p'.1
          from by rw [h1t])).trans
        ((awaySelfMulA hI (gX p.1 p'.1)).symm.trans (τX p.1 p'.1 h1'))).symm.toAlgHom =
      (furtherLocFst I (gX p.1 p'.1) (gX p.1 p''.1) hI).comp
        (τX p.1 p'.1 h1').symm.toAlgHom :=
    trans_expand_symm_toAlgHom _ _ _ _
      (awayCongrEltA_symm_comp_awaySelfMulA (gX p.1 p'.1) (gX p.1 p''.1)
        (show gX p.1 p'.1 * gX p.1 p''.1 = gX p.1 p'.1 * gX p.1 p'.1 from by rw [h1t])
        (show gX p.1 p''.1 = gX p.1 p'.1 from by rw [h1t]) hI)
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_snd_fst_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm
      h1t (fun e => h1' e.symm) h2'.symm,
    rightInterchangeOpenImmersion_eq_mapSpf
      (A := awayCompletion (I.map (algebraMap R (A p'.1))) (gX p'.1 p.1)) I (gY p'.2 p''.2) hI,
    hfst, bothAlgDataT_fst gX gY τX τY hI p p' hpp' h1' h2']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [AlgHom.comp_id,
    awayIdxTransB_scalarTower_compat h2' (fun y => gY y p''.2), hA]

omit hστX hστY in
/-- **`t_fac`, leaf `(both, snd)`, target `fst`.** `A`-factor self-multiply collapse, `B`-factor
self-multiply expand (both on the `furtherLocSnd` diagonal). -/
theorem bothAlgDataT'_fac_both_snd_fst (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 = p''.1)
    (h2t : p'.2 = p''.2) :
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
  rw [bothAlgDataT'_both_snd_fst gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
    h1' h2' h1'' h2t]
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_both_snd hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'').inv ≫
        mapSpf hI (AlgHom.id R (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1)))
          (furtherLocSnd I (gY p.2 p''.2) (gY p.2 p'.2) hI) ≫
        eqToHom (bothAlgDataV_both hI gX gY p p' hpp' h1' h2').symm := by
    rw [← bothAlgDataSrcIso_both_snd_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'',
      Iso.inv_hom_id_assoc]
  have hA : ((τX p.1 p'.1 h1').trans ((awaySelfMulA hI (gX p'.1 p.1)).trans
        (awayCongrEltA (show gX p'.1 p.1 * gX p'.1 p.1 = gX p'.1 p''.1 * gX p'.1 p.1
          from by rw [h1''])))).symm.toAlgHom.comp
        (furtherLocSnd I (gX p'.1 p''.1) (gX p'.1 p.1) hI) =
      (τX p.1 p'.1 h1').symm.toAlgHom :=
    trans_selfMul_symm_comp _ _ _ _ (by
      rw [awayCongrEltA_symm_comp_furtherLocSnd (gX p'.1 p.1) (gX p'.1 p''.1)
          (show gX p'.1 p.1 * gX p'.1 p.1 = gX p'.1 p''.1 * gX p'.1 p.1 from by rw [h1''])
          (show gX p'.1 p''.1 = gX p'.1 p.1 from by rw [h1'']) hI,
        awaySelfMulA_symm_comp_furtherLocSnd_self (gX p'.1 p.1) hI])
  have hB : ((awayCongrEltB (show gY p.2 p''.2 * gY p.2 p'.2 = gY p.2 p'.2 * gY p.2 p'.2
          from by rw [h2t])).trans
        ((awaySelfMulB hI (gY p.2 p'.2)).symm.trans (τY p.2 p'.2 h2'))).symm.toAlgHom =
      (furtherLocSnd I (gY p.2 p''.2) (gY p.2 p'.2) hI).comp
        (τY p.2 p'.2 h2').symm.toAlgHom :=
    trans_expand_symm_toAlgHom _ _ _ _
      (awayCongrEltB_symm_comp_awaySelfMulB_snd (gY p.2 p'.2) (gY p.2 p''.2)
        (show gY p.2 p''.2 * gY p.2 p'.2 = gY p.2 p'.2 * gY p.2 p'.2 from by rw [h2t])
        (show gY p.2 p''.2 = gY p.2 p'.2 from by rw [h2t]) hI)
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_fst_both_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm
      (fun e => h1' (h1''.trans e.symm)) h2t (fun e => h1' e.symm) (fun e => h2' e.symm),
    hfst, bothAlgDataT_both gX gY τX τY hI p p' hpp' h1' h2']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [AlgHom.id_comp, AlgHom.comp_id, hA, hB]

omit hστX hστY in
/-- **`t_fac`, leaf `(both, fst)`, target `snd`.** `A`-factor self-multiply expand, `B`-factor
self-multiply collapse (mirror of `(both, snd)`/target `fst`). -/
theorem bothAlgDataT'_fac_both_fst_snd (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 = p''.2) (h1t : p'.1 = p''.1) :
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
  rw [bothAlgDataT'_both_fst_snd gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
    h1' h2' h1'' h2'' h1t]
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_both_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        mapSpf hI (furtherLocSnd I (gX p.1 p''.1) (gX p.1 p'.1) hI)
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2))) ≫
        eqToHom (bothAlgDataV_both hI gX gY p p' hpp' h1' h2').symm := by
    rw [← bothAlgDataSrcIso_both_fst_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'',
      Iso.inv_hom_id_assoc]
  have hA : ((awayCongrEltA (show gX p.1 p''.1 * gX p.1 p'.1 = gX p.1 p'.1 * gX p.1 p'.1
          from by rw [h1t])).trans
        ((awaySelfMulA hI (gX p.1 p'.1)).symm.trans (τX p.1 p'.1 h1'))).symm.toAlgHom =
      (furtherLocSnd I (gX p.1 p''.1) (gX p.1 p'.1) hI).comp
        (τX p.1 p'.1 h1').symm.toAlgHom :=
    trans_expand_symm_toAlgHom _ _ _ _
      (awayCongrEltA_symm_comp_awaySelfMulA_snd (gX p.1 p'.1) (gX p.1 p''.1)
        (show gX p.1 p''.1 * gX p.1 p'.1 = gX p.1 p'.1 * gX p.1 p'.1 from by rw [h1t])
        (show gX p.1 p''.1 = gX p.1 p'.1 from by rw [h1t]) hI)
  have hB : ((τY p.2 p'.2 h2').trans ((awaySelfMulB hI (gY p'.2 p.2)).trans
        (awayCongrEltB (show gY p'.2 p.2 * gY p'.2 p.2 = gY p'.2 p''.2 * gY p'.2 p.2
          from by rw [h2''])))).symm.toAlgHom.comp
        (furtherLocSnd I (gY p'.2 p''.2) (gY p'.2 p.2) hI) =
      (τY p.2 p'.2 h2').symm.toAlgHom :=
    trans_selfMul_symm_comp _ _ _ _ (by
      rw [awayCongrEltB_symm_comp_furtherLocSnd (gY p'.2 p.2) (gY p'.2 p''.2)
          (show gY p'.2 p.2 * gY p'.2 p.2 = gY p'.2 p''.2 * gY p'.2 p.2 from by rw [h2''])
          (show gY p'.2 p''.2 = gY p'.2 p.2 from by rw [h2'']) hI,
        awaySelfMulB_symm_comp_furtherLocSnd_self (gY p'.2 p.2) hI])
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_snd_both_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm
      h1t (fun e => h1' e.symm) (fun e => h2' e.symm),
    hfst, bothAlgDataT_both gX gY τX τY hI p p' hpp' h1' h2']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [AlgHom.id_comp, AlgHom.comp_id, hA, hB]

omit hστX in
/-- **`t_fac`, leaf `(snd, both)`, target `both`.** `A`-factor index transport, `B`-factor genuine
(`hστY`) after the `mul_comm` further-localization swap. -/
theorem bothAlgDataT'_fac_snd_both_both (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2)
    (h2t : p'.2 ≠ p''.2) :
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
  rw [bothAlgDataT'_snd_both_both gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
    h1' h1'' h2'' h2t]
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_snd_both hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'').inv ≫
        mapSpf hI (IsScalarTower.toAlgHom R (A p.1)
            (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p''.1)))
          (furtherLocFst I (gY p.2 p'.2) (gY p.2 p''.2) hI) ≫
        eqToHom (bothAlgDataV_snd hI gX gY p p' hpp' h1').symm := by
    rw [← bothAlgDataSrcIso_snd_both_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'',
      Iso.inv_hom_id_assoc]
  have hB : ((σY p.2 p'.2 p''.2 h2' h2'' h2t).trans
        (awayCongrEltB (mul_comm (gY p'.2 p''.2) (gY p'.2 p.2)))).symm.toAlgHom.comp
        (furtherLocFst I (gY p'.2 p.2) (gY p'.2 p''.2) hI) =
      (furtherLocFst I (gY p.2 p'.2) (gY p.2 p''.2) hI).comp (τY p.2 p'.2 h2').symm.toAlgHom := by
    rw [trans_symm_toAlgHom, AlgHom.comp_assoc,
      awayCongrEltB_mulComm_symm_comp_furtherLocFst (gY p'.2 p.2) (gY p'.2 p''.2) hI,
      hστY p.2 p'.2 p''.2 h2' h2'' h2t]
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_both_snd_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm
      (fun e => h1'' (h1'.trans e)) h2t h1'.symm,
    hfst, bothAlgDataT_snd gX gY τX τY hI p p' hpp' h1']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [awayIdxTransA_scalarTower_compat h1' (fun x => gX x p''.1), hB]

omit hστY in
/-- **`t_fac`, leaf `(fst, both)`, target `both`.** `A`-factor genuine (`hστX`) after the `mul_comm`
further-localization swap, `B`-factor index transport. -/
theorem bothAlgDataT'_fac_fst_both_both (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 ≠ p''.2) (h1t : p'.1 ≠ p''.1) :
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
  rw [bothAlgDataT'_fst_both_both gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
    h1' h2' h1'' h2'' h1t]
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_fst_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        mapSpf hI (furtherLocFst I (gX p.1 p'.1) (gX p.1 p''.1) hI)
          (IsScalarTower.toAlgHom R (B p.2)
            (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p''.2))) ≫
        eqToHom (bothAlgDataV_fst hI gX gY p p' hpp' h1' h2').symm := by
    rw [← bothAlgDataSrcIso_fst_both_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'',
      Iso.inv_hom_id_assoc]
  have hA : ((σX p.1 p'.1 p''.1 h1' h1'' h1t).trans
        (awayCongrEltA (mul_comm (gX p'.1 p''.1) (gX p'.1 p.1)))).symm.toAlgHom.comp
        (furtherLocFst I (gX p'.1 p.1) (gX p'.1 p''.1) hI) =
      (furtherLocFst I (gX p.1 p'.1) (gX p.1 p''.1) hI).comp (τX p.1 p'.1 h1').symm.toAlgHom := by
    rw [trans_symm_toAlgHom, AlgHom.comp_assoc,
      awayCongrEltA_mulComm_symm_comp_furtherLocFst (gX p'.1 p.1) (gX p'.1 p''.1) hI,
      hστX p.1 p'.1 p''.1 h1' h1'' h1t]
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_both_fst_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm
      h1t (fun e => h2'' (h2'.trans e)) (fun e => h1' e.symm) h2'.symm,
    hfst, bothAlgDataT_fst gX gY τX τY hI p p' hpp' h1' h2']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [awayIdxTransB_scalarTower_compat h2' (fun y => gY y p''.2), hA]

omit hστX in
/-- **`t_fac`, leaf `(both, snd)`, target `both`.** `A`-factor self-multiply collapse, `B`-factor
genuine (`hστY`) after the `mul_comm` swap (the congruence sits on the *left* of `σY`). -/
theorem bothAlgDataT'_fac_both_snd_both (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 = p''.1)
    (h2t : p'.2 ≠ p''.2) :
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
  rw [bothAlgDataT'_both_snd_both gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
    h1' h2' h1'' h2t]
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_both_snd hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'').inv ≫
        mapSpf hI (AlgHom.id R (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1)))
          (furtherLocSnd I (gY p.2 p''.2) (gY p.2 p'.2) hI) ≫
        eqToHom (bothAlgDataV_both hI gX gY p p' hpp' h1' h2').symm := by
    rw [← bothAlgDataSrcIso_both_snd_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'',
      Iso.inv_hom_id_assoc]
  have hA : ((τX p.1 p'.1 h1').trans ((awaySelfMulA hI (gX p'.1 p.1)).trans
        (awayCongrEltA (show gX p'.1 p.1 * gX p'.1 p.1 = gX p'.1 p''.1 * gX p'.1 p.1
          from by rw [h1''])))).symm.toAlgHom.comp
        (furtherLocSnd I (gX p'.1 p''.1) (gX p'.1 p.1) hI) =
      (τX p.1 p'.1 h1').symm.toAlgHom :=
    trans_selfMul_symm_comp _ _ _ _ (by
      rw [awayCongrEltA_symm_comp_furtherLocSnd (gX p'.1 p.1) (gX p'.1 p''.1)
          (show gX p'.1 p.1 * gX p'.1 p.1 = gX p'.1 p''.1 * gX p'.1 p.1 from by rw [h1''])
          (show gX p'.1 p''.1 = gX p'.1 p.1 from by rw [h1'']) hI,
        awaySelfMulA_symm_comp_furtherLocSnd_self (gX p'.1 p.1) hI])
  have hB : ((awayCongrEltB (mul_comm (gY p.2 p''.2) (gY p.2 p'.2))).trans
        (σY p.2 p'.2 p''.2 h2' (fun eq => hpp'' (Prod.ext h1'' eq)) h2t)).symm.toAlgHom.comp
        (furtherLocSnd I (gY p'.2 p''.2) (gY p'.2 p.2) hI) =
      (furtherLocSnd I (gY p.2 p''.2) (gY p.2 p'.2) hI).comp (τY p.2 p'.2 h2').symm.toAlgHom := by
    rw [trans_symm_toAlgHom, AlgHom.comp_assoc,
      hστY p.2 p'.2 p''.2 h2' (fun eq => hpp'' (Prod.ext h1'' eq)) h2t,
      ← AlgHom.comp_assoc,
      awayCongrEltB_mulComm_symm_comp_furtherLocFst (gY p.2 p'.2) (gY p.2 p''.2) hI]
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_both_both_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm
      (fun e => h1' (h1''.trans e.symm)) h2t (fun e => h1' e.symm) (fun e => h2' e.symm),
    hfst, bothAlgDataT_both gX gY τX τY hI p p' hpp' h1' h2']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [AlgHom.id_comp, hA, hB]

omit hστY in
/-- **`t_fac`, leaf `(both, fst)`, target `both`.** `A`-factor genuine (`hστX`) after the `mul_comm`
swap (congruence on the *left* of `σX`), `B`-factor self-multiply collapse. -/
theorem bothAlgDataT'_fac_both_fst_both (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1)
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
  rw [bothAlgDataT'_both_fst_both gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
    h1' h2' h1'' h2'' h1t]
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_both_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        mapSpf hI (furtherLocSnd I (gX p.1 p''.1) (gX p.1 p'.1) hI)
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2))) ≫
        eqToHom (bothAlgDataV_both hI gX gY p p' hpp' h1' h2').symm := by
    rw [← bothAlgDataSrcIso_both_fst_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'',
      Iso.inv_hom_id_assoc]
  have hA : ((awayCongrEltA (mul_comm (gX p.1 p''.1) (gX p.1 p'.1))).trans
        (σX p.1 p'.1 p''.1 h1' h1'' h1t)).symm.toAlgHom.comp
        (furtherLocSnd I (gX p'.1 p''.1) (gX p'.1 p.1) hI) =
      (furtherLocSnd I (gX p.1 p''.1) (gX p.1 p'.1) hI).comp (τX p.1 p'.1 h1').symm.toAlgHom := by
    rw [trans_symm_toAlgHom, AlgHom.comp_assoc,
      hστX p.1 p'.1 p''.1 h1' h1'' h1t,
      ← AlgHom.comp_assoc,
      awayCongrEltA_mulComm_symm_comp_furtherLocFst (gX p.1 p'.1) (gX p.1 p''.1) hI]
  have hB : ((τY p.2 p'.2 h2').trans ((awaySelfMulB hI (gY p'.2 p.2)).trans
        (awayCongrEltB (show gY p'.2 p.2 * gY p'.2 p.2 = gY p'.2 p''.2 * gY p'.2 p.2
          from by rw [h2''])))).symm.toAlgHom.comp
        (furtherLocSnd I (gY p'.2 p''.2) (gY p'.2 p.2) hI) =
      (τY p.2 p'.2 h2').symm.toAlgHom :=
    trans_selfMul_symm_comp _ _ _ _ (by
      rw [awayCongrEltB_symm_comp_furtherLocSnd (gY p'.2 p.2) (gY p'.2 p''.2)
          (show gY p'.2 p.2 * gY p'.2 p.2 = gY p'.2 p''.2 * gY p'.2 p.2 from by rw [h2''])
          (show gY p'.2 p''.2 = gY p'.2 p.2 from by rw [h2'']) hI,
        awaySelfMulB_symm_comp_furtherLocSnd_self (gY p'.2 p.2) hI])
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_both_both_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm
      h1t (fun e => h2' (h2''.trans e.symm)) (fun e => h1' e.symm) (fun e => h2' e.symm),
    hfst, bothAlgDataT_both gX gY τX τY hI p p' hpp' h1' h2']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [AlgHom.id_comp, hA, hB]

omit hστY in
/-- **`t_fac`, leaf `(both, both)`, target `fst`.** `A`-factor genuine (`hστX`), `B`-factor
self-multiply expand. -/
theorem bothAlgDataT'_fac_both_both_fst (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 ≠ p''.2) (h1t : p'.1 ≠ p''.1) (h2t : p'.2 = p''.2) :
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
  rw [bothAlgDataT'_both_both_fst gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
    h1' h2' h1'' h2'' h1t h2t]
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_both_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        mapSpf hI (furtherLocFst I (gX p.1 p'.1) (gX p.1 p''.1) hI)
          (furtherLocFst I (gY p.2 p'.2) (gY p.2 p''.2) hI) ≫
        eqToHom (bothAlgDataV_both hI gX gY p p' hpp' h1' h2').symm := by
    rw [← bothAlgDataSrcIso_both_both_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'',
      Iso.inv_hom_id_assoc]
  have hB : ((awayCongrEltB (show gY p.2 p'.2 * gY p.2 p''.2 = gY p.2 p'.2 * gY p.2 p'.2
          from by rw [h2t])).trans
        ((awaySelfMulB hI (gY p.2 p'.2)).symm.trans (τY p.2 p'.2 h2'))).symm.toAlgHom =
      (furtherLocFst I (gY p.2 p'.2) (gY p.2 p''.2) hI).comp
        (τY p.2 p'.2 h2').symm.toAlgHom :=
    trans_expand_symm_toAlgHom _ _ _ _
      (awayCongrEltB_symm_comp_awaySelfMulB (gY p.2 p'.2) (gY p.2 p''.2)
        (show gY p.2 p'.2 * gY p.2 p''.2 = gY p.2 p'.2 * gY p.2 p'.2 from by rw [h2t])
        (show gY p.2 p''.2 = gY p.2 p'.2 from by rw [h2t]) hI)
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_fst_both_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm
      h1t h2t (fun e => h1' e.symm) (fun e => h2' e.symm),
    hfst, bothAlgDataT_both gX gY τX τY hI p p' hpp' h1' h2']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [AlgHom.comp_id, hστX p.1 p'.1 p''.1 h1' h1'' h1t, hB]

omit hστX in
/-- **`t_fac`, leaf `(both, both)`, target `snd`.** `A`-factor self-multiply expand, `B`-factor
genuine (`hστY`). -/
theorem bothAlgDataT'_fac_both_both_snd (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 ≠ p''.2) (h1t : p'.1 = p''.1) :
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
  rw [bothAlgDataT'_both_both_snd gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
    h1' h2' h1'' h2'' h1t]
  have hfst : pullback.fst (bothAlgDataF hI gX gY p p' hpp')
        (bothAlgDataF hI gX gY p p'' hpp'') =
      (bothAlgDataSrcIso_both_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        mapSpf hI (furtherLocFst I (gX p.1 p'.1) (gX p.1 p''.1) hI)
          (furtherLocFst I (gY p.2 p'.2) (gY p.2 p''.2) hI) ≫
        eqToHom (bothAlgDataV_both hI gX gY p p' hpp' h1' h2').symm := by
    rw [← bothAlgDataSrcIso_both_both_hom_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'',
      Iso.inv_hom_id_assoc]
  have hA : ((awayCongrEltA (show gX p.1 p'.1 * gX p.1 p''.1 = gX p.1 p'.1 * gX p.1 p'.1
          from by rw [h1t])).trans
        ((awaySelfMulA hI (gX p.1 p'.1)).symm.trans (τX p.1 p'.1 h1'))).symm.toAlgHom =
      (furtherLocFst I (gX p.1 p'.1) (gX p.1 p''.1) hI).comp
        (τX p.1 p'.1 h1').symm.toAlgHom :=
    trans_expand_symm_toAlgHom _ _ _ _
      (awayCongrEltA_symm_comp_awaySelfMulA (gX p.1 p'.1) (gX p.1 p''.1)
        (show gX p.1 p'.1 * gX p.1 p''.1 = gX p.1 p'.1 * gX p.1 p'.1 from by rw [h1t])
        (show gX p.1 p''.1 = gX p.1 p'.1 from by rw [h1t]) hI)
  rw [Category.assoc, Category.assoc,
    bothAlgDataSrcIso_snd_both_hom_snd hI gX gY p' p'' p hp'p'' hpp'.symm
      h1t (fun e => h1' e.symm) (fun e => h2' e.symm),
    hfst, bothAlgDataT_both gX gY τX τY hI p p' hpp' h1' h2']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← mapSpf_comp, ← mapSpf_comp]
  simp only [AlgHom.comp_id, hA,
    hστY p.2 p'.2 p''.2 h2' h2'' (fun eq => hp'p'' (Prod.ext h1t eq))]

/-! ### The dispatch `t_fac` law

The single `BothChartedFibreDatum.t_fac`-shaped compatibility, dispatched by the fifteen coordinate
branches of `bothAlgDataT'` onto the fifteen `bothAlgDataT'_fac_*` leaves above. -/

/-- **`bothAlgDataT'_fac`.** The dispatched triple-overlap transition `bothAlgDataT'` satisfies the
two-sided `t_fac` compatibility with the double-overlap transition `bothAlgDataT`, matching the
`t_fac` field of `AlgebraicGeometry.BothChartedFibreDatum`. -/
theorem bothAlgDataT'_fac :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' ≫
        pullback.snd (bothAlgDataF hI gX gY p' p'' hp'p'') (bothAlgDataF hI gX gY p' p hpp'.symm) =
      pullback.fst (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') ≫
        bothAlgDataT hI gX gY τX τY p p' hpp' := by
  by_cases h1' : p.1 = p'.1
  · by_cases h1'' : p.1 = p''.1
    · exact bothAlgDataT'_fac_snd_snd gX gY hI τX τY σX σY hστY p p' p'' hpp' hpp'' hp'p'' h1' h1''
    · by_cases h2'' : p.2 = p''.2
      · exact bothAlgDataT'_fac_snd_fst gX gY hI τX τY σX σY p p' p'' hpp' hpp'' hp'p''
          h1' h1'' h2''
      · by_cases h2t : p'.2 = p''.2
        · exact bothAlgDataT'_fac_snd_both_fst gX gY hI τX τY σX σY p p' p'' hpp' hpp'' hp'p''
            h1' h1'' h2'' h2t
        · exact bothAlgDataT'_fac_snd_both_both gX gY hI τX τY σX σY hστY p p' p'' hpp' hpp'' hp'p''
            h1' h1'' h2'' h2t
  · by_cases h2' : p.2 = p'.2
    · by_cases h1'' : p.1 = p''.1
      · exact bothAlgDataT'_fac_fst_snd gX gY hI τX τY σX σY p p' p'' hpp' hpp'' hp'p''
          h1' h2' h1''
      · by_cases h2'' : p.2 = p''.2
        · by_cases h1t : p'.1 = p''.1
          · exact absurd (Prod.ext h1t (h2'.symm.trans h2'')) hp'p''
          · exact bothAlgDataT'_fac_fst_fst gX gY hI τX τY σX σY hστX p p' p'' hpp' hpp'' hp'p''
              h1' h2' h1'' h2'' h1t
        · by_cases h1t : p'.1 = p''.1
          · exact bothAlgDataT'_fac_fst_both_snd gX gY hI τX τY σX σY p p' p'' hpp' hpp'' hp'p''
              h1' h2' h1'' h2'' h1t
          · exact bothAlgDataT'_fac_fst_both_both gX gY hI τX τY σX σY hστX p p' p'' hpp' hpp''
              hp'p'' h1' h2' h1'' h2'' h1t
    · by_cases h1'' : p.1 = p''.1
      · by_cases h2t : p'.2 = p''.2
        · exact bothAlgDataT'_fac_both_snd_fst gX gY hI τX τY σX σY p p' p'' hpp' hpp'' hp'p''
            h1' h2' h1'' h2t
        · exact bothAlgDataT'_fac_both_snd_both gX gY hI τX τY σX σY hστY p p' p'' hpp' hpp'' hp'p''
            h1' h2' h1'' h2t
      · by_cases h2'' : p.2 = p''.2
        · by_cases h1t : p'.1 = p''.1
          · exact bothAlgDataT'_fac_both_fst_snd gX gY hI τX τY σX σY p p' p'' hpp' hpp'' hp'p''
              h1' h2' h1'' h2'' h1t
          · exact bothAlgDataT'_fac_both_fst_both gX gY hI τX τY σX σY hστX p p' p'' hpp' hpp''
              hp'p'' h1' h2' h1'' h2'' h1t
        · by_cases h1t : p'.1 = p''.1
          · exact bothAlgDataT'_fac_both_both_snd gX gY hI τX τY σX σY hστY p p' p'' hpp' hpp''
              hp'p'' h1' h2' h1'' h2'' h1t
          · by_cases h2t : p'.2 = p''.2
            · exact bothAlgDataT'_fac_both_both_fst gX gY hI τX τY σX σY hστX p p' p'' hpp' hpp''
                hp'p'' h1' h2' h1'' h2'' h1t h2t
            · exact bothAlgDataT'_fac_both_both_both gX gY hI τX τY σX σY hστX hστY p p' p'' hpp'
                hpp'' hp'p'' h1' h2' h1'' h2'' h1t h2t

end Leaves

end AlgebraicGeometry
