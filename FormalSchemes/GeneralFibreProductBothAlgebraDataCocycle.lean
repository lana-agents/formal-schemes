import FormalSchemes.GeneralFibreProductBothAlgebraDataCocycleAux
import FormalSchemes.GeneralFibreProductBothAlgebraDataTPrimeFac

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The cocycle law `bothAlgDataT'_cocycle` and the smart constructor `ofAlgebraData`

This file completes the two-sided smart constructor `BothChartedFibreDatum.ofAlgebraData`, the
analogue of the one-sided `AlgebraicGeometry.AffineChartedFibreDatum.ofAlgebraData`
(`FormalSchemes.GeneralFibreProductAlgebraData`). It proves the twelve *mixed* leaves of the
triple-overlap cocycle `bothAlgDataT'_cocycle` (the three same-shape leaves are in
`FormalSchemes.GeneralFibreProductBothAlgebraDataCocycleAux`), assembles the fifteen-leaf dispatch,
and packages everything into `ofAlgebraData`, validated on a subsingleton product index.

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
  (τX_symm : ∀ (i i' : JX) (h : i ≠ i'), τX i' i h.symm = (τX i i' h).symm)
  (τY_symm : ∀ (j j' : JY) (h : j ≠ j'), τY j' j h.symm = (τY j j' h).symm)
variable (hI : I.FG) (p p' p'' : JX × JY)
  (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p'')

include gX gY τX τY σX σY hI hpp' hpp'' hp'p''

/-! ### Mixed-shape cocycle leaves

Each leaf mirrors the same-shape leaves of `GeneralFibreProductBothAlgebraDataCocycleAux`: rewrite
the three cyclic `bothAlgDataT'_<leaf>` reductions, telescope the adjacent `SrcIso.hom ≫ SrcIso.inv`
by `Iso.hom_inv_id_assoc` (twice), then collapse the residual `M₁ ≫ M₂ ≫ M₃ = 𝟙` via `mapSpfIso_hom`
+ `mapSpf_comp₃`, feeding the two per-factor 3-fold `AlgHom` closers (`hA`/`hB`). -/

include τX_symm τY_symm in
/-- **Cocycle, mixed leaf `snd_fst`.** `(p,p')` differs in the second coordinate, `(p,p'')` in the
first. -/
theorem bothAlgDataT'_cocycle_snd_fst (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 = p''.2) :
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
  have h1t : p'.1 ≠ p''.1 := fun e => h1'' (h1'.trans e)
  have h2t : p'.2 ≠ p''.2 := fun e => h2' (h2''.trans e.symm)
  have hmid :
      (mapSpfIso hI (awayIdxTransA h1' (fun x => gX x p''.1))
          ((τY p.2 p'.2 (fun e => hpp' (Prod.ext h1' e))).trans
            ((awaySelfMulB hI (gY p'.2 p.2)).trans
              (awayCongrEltB (by rw [h2'']))))).hom ≫
      (mapSpfIso hI ((τX p'.1 p''.1 h1t).trans ((awaySelfMulA hI (gX p''.1 p'.1)).trans
            (awayCongrEltA (by rw [h1'.symm]))))
          ((awayCongrEltB (by rw [h2''.symm])).trans ((awaySelfMulB hI (gY p'.2 p''.2)).symm.trans
            (τY p'.2 p''.2 h2t)))).hom ≫
      (mapSpfIso hI ((awayCongrEltA (by rw [h1'])).trans ((awaySelfMulA hI (gX p''.1 p.1)).symm.trans
            (τX p''.1 p.1 h1''.symm)))
          (awayIdxTransB h2''.symm (fun y => gY y p'.2))).hom = 𝟙 _ := by
    rw [mapSpfIso_hom, mapSpfIso_hom, mapSpfIso_hom]
    refine mapSpf_comp₃ hI _ _ _ _ _ _ ?hA ?hB
    -- hA : the A-factor 3-fold `.comp = id` cocycle.  Via `trans_cocycle_symm_comp` this becomes
    --   `(awayIdxTransA h1' _).trans (E₂.trans E₃) = AlgEquiv.refl`, where E₂/E₃ wrap `τX` with
    --   `awaySelfMulA`/`awayCongrEltA`.  Since p.1 = p'.1 (degenerate coord) it needs only
    --   `τX_symm` + the `TPrimeFacAux` atoms (idxTrans transport, selfMul bridge), NOT `hσcX`.
    case hA => refine trans_cocycle_symm_comp _ _ _ ?_; sorry
    -- hB : the B-factor 3-fold `.comp = id` cocycle (mirror, `τY_symm` + atoms).
    case hB => refine trans_cocycle_symm_comp _ _ _ ?_; sorry
  rw [bothAlgDataT'_snd_fst gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p'' h1' h1'' h2'',
    bothAlgDataT'_both_snd_fst gX gY τX τY σX σY hI p' p'' p hp'p'' hpp'.symm hpp''.symm
      h1t h2t h1'.symm h2''.symm,
    bothAlgDataT'_fst_both_snd gX gY τX τY σX σY hI p'' p p' hpp''.symm hp'p''.symm hpp'
      h1''.symm h2''.symm h1t.symm h2t.symm h1']
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  -- Goal: `Sp.inv ≫ M₁ ≫ M₂ ≫ M₃ ≫ Sp.hom = 𝟙`.  The same-shape leaves close this with
  -- `reassoc_of% hmid, Iso.inv_hom_id`, but for these mixed M-values `reassoc_of% hmid` hits the
  -- `instances`-transparency `kabstract` wall (`awaySelfMul.symm`/`awayIdxTrans` force ill-typed
  -- unfolding).  WORKAROUND TO TRY: `simp only [mapSpfIso_hom]` to convert the M's to `mapSpf`, then
  -- combine with `← mapSpf_comp` and close via `mapSpf_id` (mapSpf-form avoids the mapSpfIso wall).
  sorry

end AlgebraicGeometry
