import FormalSchemes.GeneralFibreProductBothAlgebraData

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Leg laws for the triple-overlap source pullback isomorphisms

For each of the nine ordered leg-shape pairs, the source pullback isomorphism
`AlgebraicGeometry.bothAlgDataSrcIso_a_b` of
`FormalSchemes.GeneralFibreProductBothAlgebraData` has two composite legs
`pullback.fst`/`pullback.snd`. This file records them: pushing each leg back through
`(pullback.congrHom _).inv` and `(eqPullbackIso _).inv` and applying the underlying
interchange-pullback leg law identifies it with the corresponding `furtherLoc`-style embedding
(or, in the mixed shape, an interchange open immersion) postcomposed with the object-reduction cast
`eqToHom` into the overlap object `bothAlgDataV`.

All nine shapes — `snd_snd`, `fst_fst`, `both_both`, `fst_snd`, `fst_both`, `snd_both`,
`snd_fst`, `both_fst`, `both_snd` — have both their `_hom_fst` and `_hom_snd` leg laws proved.

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

/-! ### The leg laws of the dispatched source pullback isomorphisms

For each ordered pair of leg shapes, the two legs `pullback.fst`/`pullback.snd` of the source
isomorphism are computed by pushing the leg through `(pullback.congrHom _).inv` and
`(eqPullbackIso _).inv` (via `congrHom_inv_fst/_snd` and `eqPullbackIso_inv_fst/_snd`) and then
applying the underlying interchange-pullback leg law. The result is the corresponding
`furtherLoc`-style embedding (or interchange open immersion, in the mixed shape) postcomposed with
the object-reduction cast `eqToHom` into the overlap object `bothAlgDataV p p'` (resp. `p p''`). -/

/-- **`fst` leg of the (2nd, 2nd) source iso.** -/
theorem bothAlgDataSrcIso_snd_snd_hom_fst (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 = p'.1) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_snd_snd hI gX gY p p' p'' hpp' hpp'' h1' h1'').hom ≫
        pullback.fst (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI (AlgHom.id R (A p.1))
          (furtherLocFst I (gY p.2 p'.2) (gY p.2 p''.2) hI) ≫
        eqToHom (bothAlgDataV_snd hI gX gY p p' hpp' h1').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p'.2) hI
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p''.2) hI
  rw [bothAlgDataSrcIso_snd_snd, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, congrHom_inv_fst, eqPullbackIso_inv_fst,
    reassoc_of%
      (rightInterchangePullbackIso_hom_fst (A := A p.1) I (gY p.2 p'.2) (gY p.2 p''.2) hI)]

/-- **`snd` leg of the (2nd, 2nd) source iso.** -/
theorem bothAlgDataSrcIso_snd_snd_hom_snd (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 = p'.1) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_snd_snd hI gX gY p p' p'' hpp' hpp'' h1' h1'').hom ≫
        pullback.snd (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI (AlgHom.id R (A p.1))
          (furtherLocSnd I (gY p.2 p'.2) (gY p.2 p''.2) hI) ≫
        eqToHom (bothAlgDataV_snd hI gX gY p p'' hpp'' h1'').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p'.2) hI
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p''.2) hI
  rw [bothAlgDataSrcIso_snd_snd, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, congrHom_inv_snd, eqPullbackIso_inv_snd,
    reassoc_of%
      (rightInterchangePullbackIso_hom_snd (A := A p.1) I (gY p.2 p'.2) (gY p.2 p''.2) hI)]

/-- **`fst` leg of the (1st, 1st) source iso.** -/
theorem bothAlgDataSrcIso_fst_fst_hom_fst (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_fst_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').hom ≫
        pullback.fst (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI (furtherLocFst I (gX p.1 p'.1) (gX p.1 p''.1) hI)
          (AlgHom.id R (B p.2)) ≫
        eqToHom (bothAlgDataV_fst hI gX gY p p' hpp' h1' h2').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B p.2) I (gX p.1 p''.1) hI
  rw [bothAlgDataSrcIso_fst_fst, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, congrHom_inv_fst, eqPullbackIso_inv_fst,
    reassoc_of% (interchangePullbackIso_hom_fst (B := B p.2) I (gX p.1 p'.1) (gX p.1 p''.1) hI)]

/-- **`snd` leg of the (1st, 1st) source iso.** -/
theorem bothAlgDataSrcIso_fst_fst_hom_snd (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_fst_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').hom ≫
        pullback.snd (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI (furtherLocSnd I (gX p.1 p'.1) (gX p.1 p''.1) hI)
          (AlgHom.id R (B p.2)) ≫
        eqToHom (bothAlgDataV_fst hI gX gY p p'' hpp'' h1'' h2'').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B p.2) I (gX p.1 p''.1) hI
  rw [bothAlgDataSrcIso_fst_fst, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, congrHom_inv_snd, eqPullbackIso_inv_snd,
    reassoc_of% (interchangePullbackIso_hom_snd (B := B p.2) I (gX p.1 p'.1) (gX p.1 p''.1) hI)]

/-- **`fst` leg of the (both, both) source iso.** -/
theorem bothAlgDataSrcIso_both_both_hom_fst (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_both_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').hom ≫
        pullback.fst (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI
          (furtherLocFst (A := A p.1) I (gX p.1 p'.1) (gX p.1 p''.1) hI)
          (furtherLocFst (A := B p.2) I (gY p.2 p'.2) (gY p.2 p''.2) hI) ≫
        eqToHom (bothAlgDataV_both hI gX gY p p' hpp' h1' h2').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (gX p.1 p'.1) (gY p.2 p'.2) hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (gX p.1 p''.1) (gY p.2 p''.2) hI
  rw [bothAlgDataSrcIso_both_both, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, congrHom_inv_fst, eqPullbackIso_inv_fst,
    reassoc_of% (bothBothInterchangePullbackIso_hom_fst I (gX p.1 p'.1) (gX p.1 p''.1)
      (gY p.2 p'.2) (gY p.2 p''.2) hI)]

/-- **`snd` leg of the (both, both) source iso.** -/
theorem bothAlgDataSrcIso_both_both_hom_snd (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_both_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').hom ≫
        pullback.snd (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI
          (furtherLocSnd (A := A p.1) I (gX p.1 p'.1) (gX p.1 p''.1) hI)
          (furtherLocSnd (A := B p.2) I (gY p.2 p'.2) (gY p.2 p''.2) hI) ≫
        eqToHom (bothAlgDataV_both hI gX gY p p'' hpp'' h1'' h2'').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (gX p.1 p'.1) (gY p.2 p'.2) hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (gX p.1 p''.1) (gY p.2 p''.2) hI
  rw [bothAlgDataSrcIso_both_both, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, congrHom_inv_snd, eqPullbackIso_inv_snd,
    reassoc_of% (bothBothInterchangePullbackIso_hom_snd I (gX p.1 p'.1) (gX p.1 p''.1)
      (gY p.2 p'.2) (gY p.2 p''.2) hI)]

/-- **`fst` leg of the (1st, 2nd) source iso.** -/
theorem bothAlgDataSrcIso_fst_snd_hom_fst (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_fst_snd hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'').hom ≫
        pullback.fst (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      rightInterchangeOpenImmersion
          (A := awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1)) I (gY p.2 p''.2) hI ≫
        eqToHom (bothAlgDataV_fst hI gX gY p p' hpp' h1' h2').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p''.2) hI
  rw [bothAlgDataSrcIso_fst_snd, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, congrHom_inv_fst, eqPullbackIso_inv_fst,
    reassoc_of% (mixedInterchangePullbackIso_hom_fst (A := A p.1) (B := B p.2) I (gX p.1 p'.1)
      (gY p.2 p''.2) hI)]

/-- **`snd` leg of the (1st, 2nd) source iso.** -/
theorem bothAlgDataSrcIso_fst_snd_hom_snd (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_fst_snd hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'').hom ≫
        pullback.snd (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      interchangeOpenImmersion
          (B := awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p''.2)) I (gX p.1 p'.1) hI ≫
        eqToHom (bothAlgDataV_snd hI gX gY p p'' hpp'' h1'').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p''.2) hI
  rw [bothAlgDataSrcIso_fst_snd, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, congrHom_inv_snd, eqPullbackIso_inv_snd,
    reassoc_of% (mixedInterchangePullbackIso_hom_snd (A := A p.1) (B := B p.2) I (gX p.1 p'.1)
      (gY p.2 p''.2) hI)]

/-- **`fst` leg of the (1st, both) source iso.** -/
theorem bothAlgDataSrcIso_fst_both_hom_fst (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_fst_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').hom ≫
        pullback.fst (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI (furtherLocFst I (gX p.1 p'.1) (gX p.1 p''.1) hI)
          (IsScalarTower.toAlgHom R (B p.2)
            (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p''.2))) ≫
        eqToHom (bothAlgDataV_fst hI gX gY p p' hpp' h1' h2').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (gX p.1 p''.1) (gY p.2 p''.2) hI
  rw [bothAlgDataSrcIso_fst_both, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, congrHom_inv_fst, eqPullbackIso_inv_fst,
    reassoc_of% (firstBothInterchangePullbackIso_hom_fst I (gX p.1 p'.1) (gX p.1 p''.1)
      (gY p.2 p''.2) hI)]

/-- **`snd` leg of the (1st, both) source iso.** -/
theorem bothAlgDataSrcIso_fst_both_hom_snd (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_fst_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').hom ≫
        pullback.snd (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI (furtherLocSnd I (gX p.1 p'.1) (gX p.1 p''.1) hI)
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p''.2))) ≫
        eqToHom (bothAlgDataV_both hI gX gY p p'' hpp'' h1'' h2'').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (gX p.1 p''.1) (gY p.2 p''.2) hI
  rw [bothAlgDataSrcIso_fst_both, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, congrHom_inv_snd, eqPullbackIso_inv_snd,
    reassoc_of% (firstBothInterchangePullbackIso_hom_snd I (gX p.1 p'.1) (gX p.1 p''.1)
      (gY p.2 p''.2) hI)]

/-- **`fst` leg of the (2nd, both) source iso.** -/
theorem bothAlgDataSrcIso_snd_both_hom_fst (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_snd_both hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'').hom ≫
        pullback.fst (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI
          (IsScalarTower.toAlgHom R (A p.1)
            (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p''.1)))
          (furtherLocFst (A := B p.2) I (gY p.2 p'.2) (gY p.2 p''.2) hI) ≫
        eqToHom (bothAlgDataV_snd hI gX gY p p' hpp' h1').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p'.2) hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (gX p.1 p''.1) (gY p.2 p''.2) hI
  rw [bothAlgDataSrcIso_snd_both, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, congrHom_inv_fst, eqPullbackIso_inv_fst,
    reassoc_of% (rightBothInterchangePullbackIso_hom_fst I (gX p.1 p''.1) (gY p.2 p'.2)
      (gY p.2 p''.2) hI)]

/-- **`snd` leg of the (2nd, both) source iso.** -/
theorem bothAlgDataSrcIso_snd_both_hom_snd (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_snd_both hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'').hom ≫
        pullback.snd (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p''.1)))
          (furtherLocSnd (A := B p.2) I (gY p.2 p'.2) (gY p.2 p''.2) hI) ≫
        eqToHom (bothAlgDataV_both hI gX gY p p'' hpp'' h1'' h2'').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p'.2) hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion I (gX p.1 p''.1) (gY p.2 p''.2) hI
  rw [bothAlgDataSrcIso_snd_both, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, congrHom_inv_snd, eqPullbackIso_inv_snd,
    reassoc_of% (rightBothInterchangePullbackIso_hom_snd I (gX p.1 p''.1) (gY p.2 p'.2)
      (gY p.2 p''.2) hI)]

/-! ### Leg laws of the three reverse-order source isos

These postcompose a `pullbackSymmetry`, so each leg is computed from the *opposite* leg of the
forward source iso obtained by swapping the two charts. -/

/-- **`fst` leg of the (2nd, 1st) source iso.** -/
theorem bothAlgDataSrcIso_snd_fst_hom_fst (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_snd_fst hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'').hom ≫
        pullback.fst (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      interchangeOpenImmersion
          (B := awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2)) I (gX p.1 p''.1) hI ≫
        eqToHom (bothAlgDataV_snd hI gX gY p p' hpp' h1').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  rw [bothAlgDataSrcIso_snd_fst, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst,
    bothAlgDataSrcIso_fst_snd_hom_snd hI gX gY p p'' p' hpp'' hpp' h1'' h2'' h1']

/-- **`snd` leg of the (2nd, 1st) source iso.** -/
theorem bothAlgDataSrcIso_snd_fst_hom_snd (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_snd_fst hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'').hom ≫
        pullback.snd (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      rightInterchangeOpenImmersion
          (A := awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p''.1)) I (gY p.2 p'.2) hI ≫
        eqToHom (bothAlgDataV_fst hI gX gY p p'' hpp'' h1'' h2'').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  rw [bothAlgDataSrcIso_snd_fst, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
    bothAlgDataSrcIso_fst_snd_hom_fst hI gX gY p p'' p' hpp'' hpp' h1'' h2'' h1']

/-- **`fst` leg of the (both, 1st) source iso.** -/
theorem bothAlgDataSrcIso_both_fst_hom_fst (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_both_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').hom ≫
        pullback.fst (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI (furtherLocSnd I (gX p.1 p''.1) (gX p.1 p'.1) hI)
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2))) ≫
        eqToHom (bothAlgDataV_both hI gX gY p p' hpp' h1' h2').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  rw [bothAlgDataSrcIso_both_fst, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst,
    bothAlgDataSrcIso_fst_both_hom_snd hI gX gY p p'' p' hpp'' hpp' h1'' h2'' h1' h2']

/-- **`snd` leg of the (both, 1st) source iso.** -/
theorem bothAlgDataSrcIso_both_fst_hom_snd (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_both_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').hom ≫
        pullback.snd (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI (furtherLocFst I (gX p.1 p''.1) (gX p.1 p'.1) hI)
          (IsScalarTower.toAlgHom R (B p.2)
            (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2))) ≫
        eqToHom (bothAlgDataV_fst hI gX gY p p'' hpp'' h1'' h2'').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  rw [bothAlgDataSrcIso_both_fst, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
    bothAlgDataSrcIso_fst_both_hom_fst hI gX gY p p'' p' hpp'' hpp' h1'' h2'' h1' h2']

/-- **`fst` leg of the (both, 2nd) source iso.** -/
theorem bothAlgDataSrcIso_both_snd_hom_fst (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_both_snd hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'').hom ≫
        pullback.fst (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1)))
          (furtherLocSnd (A := B p.2) I (gY p.2 p''.2) (gY p.2 p'.2) hI) ≫
        eqToHom (bothAlgDataV_both hI gX gY p p' hpp' h1' h2').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  rw [bothAlgDataSrcIso_both_snd, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst,
    bothAlgDataSrcIso_snd_both_hom_snd hI gX gY p p'' p' hpp'' hpp' h1'' h1' h2']

/-- **`snd` leg of the (both, 2nd) source iso.** -/
theorem bothAlgDataSrcIso_both_snd_hom_snd (hI : I.FG) (gX : ∀ i i' : JX, A i)
    (gY : ∀ j j' : JY, B j) (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'')
    (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    (bothAlgDataSrcIso_both_snd hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'').hom ≫
        pullback.snd (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') =
      CompletedTensorProduct.mapSpf hI
          (IsScalarTower.toAlgHom R (A p.1)
            (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1)))
          (furtherLocFst (A := B p.2) I (gY p.2 p''.2) (gY p.2 p'.2) hI) ≫
        eqToHom (bothAlgDataV_snd hI gX gY p p'' hpp'' h1'').symm := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  rw [bothAlgDataSrcIso_both_snd, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
    bothAlgDataSrcIso_snd_both_hom_fst hI gX gY p p'' p' hpp'' hpp' h1'' h1' h2']


end AlgebraicGeometry
