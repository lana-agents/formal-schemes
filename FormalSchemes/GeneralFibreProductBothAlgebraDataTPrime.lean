import FormalSchemes.GeneralFibreProductBothAlgebraDataLegs
import FormalSchemes.AwayCompletionSelfMul

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The dispatched triple-overlap transition `bothAlgDataT'` of the two-sided fibre product

This file builds the geometric triple-overlap transition `bothAlgDataT'` of the two-sided smart
constructor `AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraData`, the two-sided analogue of the
one-sided `AlgebraicGeometry.algDataT'`
(`FormalSchemes.GeneralFibreProductAlgebraData`). For a pairwise-distinct product-index triple
`p p' p''` it is
`src.inv ≫ (mapSpfIso hI σX σY).hom ≫ tgt.hom`, where `src`/`tgt` are the shape-dispatched
source/target pullback isomorphisms `bothAlgDataSrcIso_*_*`
(`FormalSchemes.GeneralFibreProductBothAlgebraData`) and `σX`/`σY` are algebra transitions on the
`A`/`B` factors.

Because the overlap immersion `bothAlgDataF` is coordinate-difference dispatched, no single algebra
transition type unifies the branches: the `A`-factor localizes at zero, one, or two elements
according to the first-coordinate collision pattern of `(p.1, p'.1, p''.1)` (symmetrically for `B`).
The transition is therefore dispatched per shape, and the caller supplies two uniformly-typed
transition families:

* `τX`/`τY` — the double-overlap transitions (the structure fields of `BothChartedFibreDatum`);
* `σX`/`σY` — the genuine triple-overlap transitions in the one-sided product-to-product form
  `away(A i, gX i i' * gX i i'') ≃ₐ[R] away(A i', gX i' i'' * gX i' i)`.

In each branch the required `A`-factor transition `σX_branch : A_src ≃ₐ[R] A_tgt` is assembled from
these together with the shared-coordinate transport `eqAlgEquivA`, the element-congruence
`awayCongrEltA`, the index transport `awayIdxTransA`, and the self-multiply expand isomorphism
`FormalSpectrum.awayCompletionSelfMulEquiv` (`FormalSchemes.AwayCompletionSelfMul`).

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

/-! ### Element-congruence and index-transport helpers for the away-completion factors -/

/-- Congruence of the away-completion of `A i` along an equality of the away element. -/
def awayCongrEltA {i : JX} {g g' : A i} (h : g = g') :
    awayCompletion (I.map (algebraMap R (A i))) g ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A i))) g' := by
  subst h; exact AlgEquiv.refl

/-- Congruence of the away-completion of `B j` along an equality of the away element. -/
def awayCongrEltB {j : JY} {g g' : B j} (h : g = g') :
    awayCompletion (I.map (algebraMap R (B j))) g ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (B j))) g' := by
  subst h; exact AlgEquiv.refl

/-- Index-and-element transport of the away-completion of the `A` factor along an equality of the
base index `i = i'`, with the away element given as a value `g i` of a family `g : ∀ x, A x` so its
transport `g i'` is definitionally the target element. -/
def awayIdxTransA {i i' : JX} (h : i = i') (g : ∀ x : JX, A x) :
    awayCompletion (I.map (algebraMap R (A i))) (g i) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A i'))) (g i') := by
  subst h; exact AlgEquiv.refl

/-- Index-and-element transport of the away-completion of the `B` factor. -/
def awayIdxTransB {j j' : JY} (h : j = j') (g : ∀ y : JY, B y) :
    awayCompletion (I.map (algebraMap R (B j))) (g j) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (B j'))) (g j') := by
  subst h; exact AlgEquiv.refl

/-- The self-multiply expand isomorphism on the `A` factor, specialised to the fibre-product
away-completion `away(A i, g)`: `away(A i, g) ≃ₐ[R] away(A i, g * g)`. -/
def awaySelfMulA (hI : I.FG) {i : JX} (g : A i) :
    awayCompletion (I.map (algebraMap R (A i))) g ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A i))) (g * g) :=
  awayCompletionSelfMulEquiv (I.map (algebraMap R (A i))) g (hI.map _)

/-- The self-multiply expand isomorphism on the `B` factor. -/
def awaySelfMulB (hI : I.FG) {j : JY} (g : B j) :
    awayCompletion (I.map (algebraMap R (B j))) g ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (B j))) (g * g) :=
  awayCompletionSelfMulEquiv (I.map (algebraMap R (B j))) g (hI.map _)

/-! ### The dispatched triple-overlap transition -/

/-- **The coordinate-difference-dispatched triple-overlap transition** of three pairwise-distinct
product-index charts, `pullback (f p p') (f p p'') ⟶ pullback (f p' p'') (f p' p)`. Built as
`src.inv ≫ (mapSpfIso hI σX_branch σY_branch).hom ≫ tgt.hom`, dispatched on the coordinate
equalities exactly as `bothAlgDataF`. -/
def bothAlgDataT' (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
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
    (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p'') :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    (pullback (bothAlgDataF hI gX gY p p' hpp') (bothAlgDataF hI gX gY p p'' hpp'') ⟶
      pullback (bothAlgDataF hI gX gY p' p'' hp'p'') (bothAlgDataF hI gX gY p' p hpp'.symm)) := by
  by_cases h1' : p.1 = p'.1
  · -- S1 = snd (p.2 ≠ p'.2); σX is an index transport, σY is genuine
    have h2' : p.2 ≠ p'.2 := fun e => hpp' (Prod.ext h1' e)
    by_cases h1'' : p.1 = p''.1
    · -- leaf 1: (snd, snd); T1 = snd
      have h2'' : p.2 ≠ p''.2 := fun e => hpp'' (Prod.ext h1'' e)
      exact (bothAlgDataSrcIso_snd_snd hI gX gY p p' p'' hpp' hpp'' h1' h1'').inv ≫
        (mapSpfIso hI (eqAlgEquivA h1')
          (σY p.2 p'.2 p''.2 h2' h2''
            (fun eq => hp'p'' (Prod.ext (h1'.symm.trans h1'') eq)))).hom ≫
        (bothAlgDataSrcIso_snd_snd hI gX gY p' p'' p hp'p'' hpp'.symm
          (h1'.symm.trans h1'') h1'.symm).hom
    · by_cases h2'' : p.2 = p''.2
      · -- leaf 2: (snd, fst); T1 = both
        exact (bothAlgDataSrcIso_snd_fst hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'').inv ≫
          (mapSpfIso hI (awayIdxTransA h1' (fun x => gX x p''.1))
            ((τY p.2 p'.2 h2').trans
              ((awaySelfMulB hI (gY p'.2 p.2)).trans (awayCongrEltB (by rw [h2'']))))).hom ≫
          (bothAlgDataSrcIso_both_snd hI gX gY p' p'' p hp'p'' hpp'.symm
            (fun e => h1'' (h1'.trans e)) (fun e => h2' (h2''.trans e.symm)) h1'.symm).hom
      · -- leaf 3: (snd, both); T1 dite on p'.2 =? p''.2
        by_cases h2t : p'.2 = p''.2
        · -- T1 = fst
          exact (bothAlgDataSrcIso_snd_both hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'').inv ≫
            (mapSpfIso hI (awayIdxTransA h1' (fun x => gX x p''.1))
              ((awayCongrEltB (by rw [h2t])).trans
                ((awaySelfMulB hI (gY p.2 p'.2)).symm.trans (τY p.2 p'.2 h2')))).hom ≫
            (bothAlgDataSrcIso_fst_snd hI gX gY p' p'' p hp'p'' hpp'.symm
              (fun e => h1'' (h1'.trans e)) h2t h1'.symm).hom
        · -- T1 = both
          exact (bothAlgDataSrcIso_snd_both hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'').inv ≫
            (mapSpfIso hI (awayIdxTransA h1' (fun x => gX x p''.1))
              ((σY p.2 p'.2 p''.2 h2' h2'' h2t).trans (awayCongrEltB (mul_comm _ _)))).hom ≫
            (bothAlgDataSrcIso_both_snd hI gX gY p' p'' p hp'p'' hpp'.symm
              (fun e => h1'' (h1'.trans e)) h2t h1'.symm).hom
  · -- S1 = fst or both (p.1 ≠ p'.1)
    by_cases h2' : p.2 = p'.2
    · -- S1 = fst (p.1 ≠ p'.1, p.2 = p'.2); σX genuine, σY index transport
      by_cases h1'' : p.1 = p''.1
      · -- leaf 4: (fst, snd); T1 = both
        exact (bothAlgDataSrcIso_fst_snd hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'').inv ≫
          (mapSpfIso hI
            ((τX p.1 p'.1 h1').trans
              ((awaySelfMulA hI (gX p'.1 p.1)).trans (awayCongrEltA (by rw [h1'']))))
            (awayIdxTransB h2' (fun y => gY y p''.2))).hom ≫
          (bothAlgDataSrcIso_both_fst hI gX gY p' p'' p hp'p'' hpp'.symm
            (fun e => h1' (h1''.trans e.symm)) (fun e => hpp'' (Prod.ext h1'' (h2'.trans e)))
            (fun e => h1' e.symm) h2'.symm).hom
      · by_cases h2'' : p.2 = p''.2
        · -- leaf 5: (fst, fst); T1 dite on p'.1 =? p''.1
          by_cases h1t : p'.1 = p''.1
          · -- T1 = snd is vacuous: p'.1 = p''.1 and p'.2 = p''.2 force p' = p''
            exact absurd (Prod.ext h1t (h2'.symm.trans h2'')) hp'p''
          · -- T1 = fst
            exact (bothAlgDataSrcIso_fst_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
              (mapSpfIso hI (σX p.1 p'.1 p''.1 h1' h1'' h1t) (eqAlgEquivB h2')).hom ≫
              (bothAlgDataSrcIso_fst_fst hI gX gY p' p'' p hp'p'' hpp'.symm
                h1t (h2'.symm.trans h2'') (fun e => h1' e.symm) h2'.symm).hom
        · -- leaf 6: (fst, both); T1 dite on p'.1 =? p''.1
          by_cases h1t : p'.1 = p''.1
          · -- T1 = snd
            exact (bothAlgDataSrcIso_fst_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
              (mapSpfIso hI
                ((awayCongrEltA (by rw [h1t])).trans
                  ((awaySelfMulA hI (gX p.1 p'.1)).symm.trans (τX p.1 p'.1 h1')))
                (awayIdxTransB h2' (fun y => gY y p''.2))).hom ≫
              (bothAlgDataSrcIso_snd_fst hI gX gY p' p'' p hp'p'' hpp'.symm
                h1t (fun e => h1' e.symm) h2'.symm).hom
          · -- T1 = both
            exact (bothAlgDataSrcIso_fst_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
              (mapSpfIso hI ((σX p.1 p'.1 p''.1 h1' h1'' h1t).trans (awayCongrEltA (mul_comm _ _)))
                (awayIdxTransB h2' (fun y => gY y p''.2))).hom ≫
              (bothAlgDataSrcIso_both_fst hI gX gY p' p'' p hp'p'' hpp'.symm
                h1t (fun e => h2'' (h2'.trans e)) (fun e => h1' e.symm) h2'.symm).hom
    · -- S1 = both (p.1 ≠ p'.1, p.2 ≠ p'.2); both σX and σY genuine
      by_cases h1'' : p.1 = p''.1
      · -- leaf 7: (both, snd); T1 dite on p'.2 =? p''.2
        by_cases h2t : p'.2 = p''.2
        · -- T1 = fst
          exact (bothAlgDataSrcIso_both_snd hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'').inv ≫
            (mapSpfIso hI
              ((τX p.1 p'.1 h1').trans
                ((awaySelfMulA hI (gX p'.1 p.1)).trans (awayCongrEltA (by rw [h1'']))))
              ((awayCongrEltB (by rw [h2t])).trans
                ((awaySelfMulB hI (gY p.2 p'.2)).symm.trans (τY p.2 p'.2 h2')))).hom ≫
            (bothAlgDataSrcIso_fst_both hI gX gY p' p'' p hp'p'' hpp'.symm
              (fun e => h1' (h1''.trans e.symm)) h2t (fun e => h1' e.symm)
              (fun e => h2' e.symm)).hom
        · -- T1 = both
          exact (bothAlgDataSrcIso_both_snd hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'').inv ≫
            (mapSpfIso hI
              ((τX p.1 p'.1 h1').trans
                ((awaySelfMulA hI (gX p'.1 p.1)).trans (awayCongrEltA (by rw [h1'']))))
              ((awayCongrEltB (mul_comm _ _)).trans
                (σY p.2 p'.2 p''.2 h2' (fun eq => hpp'' (Prod.ext h1'' eq)) h2t))).hom ≫
            (bothAlgDataSrcIso_both_both hI gX gY p' p'' p hp'p'' hpp'.symm
              (fun e => h1' (h1''.trans e.symm)) h2t (fun e => h1' e.symm)
              (fun e => h2' e.symm)).hom
      · by_cases h2'' : p.2 = p''.2
        · -- leaf 8: (both, fst); T1 dite on p'.1 =? p''.1
          by_cases h1t : p'.1 = p''.1
          · -- T1 = snd
            exact (bothAlgDataSrcIso_both_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
              (mapSpfIso hI
                ((awayCongrEltA (by rw [h1t])).trans
                  ((awaySelfMulA hI (gX p.1 p'.1)).symm.trans (τX p.1 p'.1 h1')))
                ((τY p.2 p'.2 h2').trans
                  ((awaySelfMulB hI (gY p'.2 p.2)).trans (awayCongrEltB (by rw [h2'']))))).hom ≫
              (bothAlgDataSrcIso_snd_both hI gX gY p' p'' p hp'p'' hpp'.symm
                h1t (fun e => h1' e.symm) (fun e => h2' e.symm)).hom
          · -- T1 = both
            exact (bothAlgDataSrcIso_both_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
              (mapSpfIso hI ((awayCongrEltA (mul_comm _ _)).trans (σX p.1 p'.1 p''.1 h1' h1'' h1t))
                ((τY p.2 p'.2 h2').trans
                  ((awaySelfMulB hI (gY p'.2 p.2)).trans (awayCongrEltB (by rw [h2'']))))).hom ≫
              (bothAlgDataSrcIso_both_both hI gX gY p' p'' p hp'p'' hpp'.symm
                h1t (fun e => h2' (h2''.trans e.symm)) (fun e => h1' e.symm)
                (fun e => h2' e.symm)).hom
        · -- leaf 9: (both, both); T1 dite on p'.1 =? p''.1 and p'.2 =? p''.2
          by_cases h1t : p'.1 = p''.1
          · -- T1 = snd (p'.2 ≠ p''.2 forced)
            exact (bothAlgDataSrcIso_both_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
              (mapSpfIso hI
                ((awayCongrEltA (by rw [h1t])).trans
                  ((awaySelfMulA hI (gX p.1 p'.1)).symm.trans (τX p.1 p'.1 h1')))
                (σY p.2 p'.2 p''.2 h2' h2''
                  (fun eq => hp'p'' (Prod.ext h1t eq)))).hom ≫
              (bothAlgDataSrcIso_snd_both hI gX gY p' p'' p hp'p'' hpp'.symm
                h1t (fun e => h1' e.symm) (fun e => h2' e.symm)).hom
          · by_cases h2t : p'.2 = p''.2
            · -- T1 = fst
              exact (bothAlgDataSrcIso_both_both hI gX gY p p' p'' hpp' hpp'' h1' h2'
                  h1'' h2'').inv ≫
                (mapSpfIso hI (σX p.1 p'.1 p''.1 h1' h1'' h1t)
                  ((awayCongrEltB (by rw [h2t])).trans
                    ((awaySelfMulB hI (gY p.2 p'.2)).symm.trans (τY p.2 p'.2 h2')))).hom ≫
                (bothAlgDataSrcIso_fst_both hI gX gY p' p'' p hp'p'' hpp'.symm
                  h1t h2t (fun e => h1' e.symm) (fun e => h2' e.symm)).hom
            · -- T1 = both
              exact (bothAlgDataSrcIso_both_both hI gX gY p p' p'' hpp' hpp'' h1' h2'
                  h1'' h2'').inv ≫
                (mapSpfIso hI (σX p.1 p'.1 p''.1 h1' h1'' h1t)
                  (σY p.2 p'.2 p''.2 h2' h2'' h2t)).hom ≫
                (bothAlgDataSrcIso_both_both hI gX gY p' p'' p hp'p'' hpp'.symm
                  h1t h2t (fun e => h1' e.symm) (fun e => h2' e.symm)).hom

/-! ### Per-branch reductions

These rewrite `bothAlgDataT'` to its explicit `src.inv ≫ (mapSpfIso …).hom ≫ tgt.hom` value under
the coordinate hypotheses of each branch, so the downstream `_fac`/`_cocycle` proofs (issues 355,
356) never re-open the dispatch `dite`. There is one per real leaf (the vacuous
`(fst, fst)`/`T1 = snd` leaf carries no transition). Each is closed by `unfold` + the branch's
`dif_pos`/`dif_neg` sequence; proof irrelevance absorbs the internally-derived distinctness proofs.
-/

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
variable (hI : I.FG) (p p' p'' : JX × JY)
  (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p'')

/-- Reduction, leaf `(snd, snd)`. -/
theorem bothAlgDataT'_snd_snd (h1' : p.1 = p'.1) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_snd_snd hI gX gY p p' p'' hpp' hpp'' h1' h1'').inv ≫
        (mapSpfIso hI (eqAlgEquivA h1')
          (σY p.2 p'.2 p''.2 (fun e => hpp' (Prod.ext h1' e))
            (fun e => hpp'' (Prod.ext h1'' e))
            (fun eq => hp'p'' (Prod.ext (h1'.symm.trans h1'') eq)))).hom ≫
        (bothAlgDataSrcIso_snd_snd hI gX gY p' p'' p hp'p'' hpp'.symm
          (h1'.symm.trans h1'') h1'.symm).hom := by
  unfold bothAlgDataT'; rw [dif_pos h1', dif_pos h1'']

/-- Reduction, leaf `(snd, fst)`. -/
theorem bothAlgDataT'_snd_fst (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_snd_fst hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'').inv ≫
        (mapSpfIso hI (awayIdxTransA h1' (fun x => gX x p''.1))
          ((τY p.2 p'.2 (fun e => hpp' (Prod.ext h1' e))).trans
            ((awaySelfMulB hI (gY p'.2 p.2)).trans (awayCongrEltB (by rw [h2'']))))).hom ≫
        (bothAlgDataSrcIso_both_snd hI gX gY p' p'' p hp'p'' hpp'.symm
          (fun e => h1'' (h1'.trans e)) (fun e => (fun e2 => hpp' (Prod.ext h1' e2))
            (h2''.trans e.symm)) h1'.symm).hom := by
  unfold bothAlgDataT'; rw [dif_pos h1', dif_neg h1'', dif_pos h2'']

/-- Reduction, leaf `(snd, both)`, target `fst`. -/
theorem bothAlgDataT'_snd_both_fst (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2)
    (h2t : p'.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_snd_both hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'').inv ≫
        (mapSpfIso hI (awayIdxTransA h1' (fun x => gX x p''.1))
          ((awayCongrEltB (by rw [h2t])).trans
            ((awaySelfMulB hI (gY p.2 p'.2)).symm.trans
              (τY p.2 p'.2 (fun e => hpp' (Prod.ext h1' e)))))).hom ≫
        (bothAlgDataSrcIso_fst_snd hI gX gY p' p'' p hp'p'' hpp'.symm
          (fun e => h1'' (h1'.trans e)) h2t h1'.symm).hom := by
  unfold bothAlgDataT'; rw [dif_pos h1', dif_neg h1'', dif_neg h2'', dif_pos h2t]

/-- Reduction, leaf `(snd, both)`, target `both`. -/
theorem bothAlgDataT'_snd_both_both (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 ≠ p''.2)
    (h2t : p'.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_snd_both hI gX gY p p' p'' hpp' hpp'' h1' h1'' h2'').inv ≫
        (mapSpfIso hI (awayIdxTransA h1' (fun x => gX x p''.1))
          ((σY p.2 p'.2 p''.2 (fun e => hpp' (Prod.ext h1' e)) h2'' h2t).trans
            (awayCongrEltB (mul_comm _ _)))).hom ≫
        (bothAlgDataSrcIso_both_snd hI gX gY p' p'' p hp'p'' hpp'.symm
          (fun e => h1'' (h1'.trans e)) h2t h1'.symm).hom := by
  unfold bothAlgDataT'; rw [dif_pos h1', dif_neg h1'', dif_neg h2'', dif_neg h2t]

/-- Reduction, leaf `(fst, snd)`. -/
theorem bothAlgDataT'_fst_snd (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_fst_snd hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'').inv ≫
        (mapSpfIso hI
          ((τX p.1 p'.1 h1').trans
            ((awaySelfMulA hI (gX p'.1 p.1)).trans (awayCongrEltA (by rw [h1'']))))
          (awayIdxTransB h2' (fun y => gY y p''.2))).hom ≫
        (bothAlgDataSrcIso_both_fst hI gX gY p' p'' p hp'p'' hpp'.symm
          (fun e => h1' (h1''.trans e.symm)) (fun e => hpp'' (Prod.ext h1'' (h2'.trans e)))
          (fun e => h1' e.symm) h2'.symm).hom := by
  unfold bothAlgDataT'; rw [dif_neg h1', dif_pos h2', dif_pos h1'']

/-- Reduction, leaf `(fst, fst)`, target `fst` (the `T1 = snd` sub-branch is vacuous). -/
theorem bothAlgDataT'_fst_fst (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 = p''.2) (h1t : p'.1 ≠ p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_fst_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        (mapSpfIso hI (σX p.1 p'.1 p''.1 h1' h1'' h1t) (eqAlgEquivB h2')).hom ≫
        (bothAlgDataSrcIso_fst_fst hI gX gY p' p'' p hp'p'' hpp'.symm
          h1t (h2'.symm.trans h2'') (fun e => h1' e.symm) h2'.symm).hom := by
  unfold bothAlgDataT'
  rw [dif_neg h1', dif_pos h2', dif_neg h1'', dif_pos h2'', dif_neg h1t]

/-- Reduction, leaf `(fst, both)`, target `snd`. -/
theorem bothAlgDataT'_fst_both_snd (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 ≠ p''.2) (h1t : p'.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_fst_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        (mapSpfIso hI
          ((awayCongrEltA (by rw [h1t])).trans
            ((awaySelfMulA hI (gX p.1 p'.1)).symm.trans (τX p.1 p'.1 h1')))
          (awayIdxTransB h2' (fun y => gY y p''.2))).hom ≫
        (bothAlgDataSrcIso_snd_fst hI gX gY p' p'' p hp'p'' hpp'.symm
          h1t (fun e => h1' e.symm) h2'.symm).hom := by
  unfold bothAlgDataT'; rw [dif_neg h1', dif_pos h2', dif_neg h1'', dif_neg h2'', dif_pos h1t]

/-- Reduction, leaf `(fst, both)`, target `both`. -/
theorem bothAlgDataT'_fst_both_both (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 ≠ p''.2) (h1t : p'.1 ≠ p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_fst_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        (mapSpfIso hI ((σX p.1 p'.1 p''.1 h1' h1'' h1t).trans (awayCongrEltA (mul_comm _ _)))
          (awayIdxTransB h2' (fun y => gY y p''.2))).hom ≫
        (bothAlgDataSrcIso_both_fst hI gX gY p' p'' p hp'p'' hpp'.symm
          h1t (fun e => h2'' (h2'.trans e)) (fun e => h1' e.symm) h2'.symm).hom := by
  unfold bothAlgDataT'; rw [dif_neg h1', dif_pos h2', dif_neg h1'', dif_neg h2'', dif_neg h1t]

/-- Reduction, leaf `(both, snd)`, target `fst`. -/
theorem bothAlgDataT'_both_snd_fst (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 = p''.1)
    (h2t : p'.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_both_snd hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'').inv ≫
        (mapSpfIso hI
          ((τX p.1 p'.1 h1').trans
            ((awaySelfMulA hI (gX p'.1 p.1)).trans (awayCongrEltA (by rw [h1'']))))
          ((awayCongrEltB (by rw [h2t])).trans
            ((awaySelfMulB hI (gY p.2 p'.2)).symm.trans (τY p.2 p'.2 h2')))).hom ≫
        (bothAlgDataSrcIso_fst_both hI gX gY p' p'' p hp'p'' hpp'.symm
          (fun e => h1' (h1''.trans e.symm)) h2t (fun e => h1' e.symm)
          (fun e => h2' e.symm)).hom := by
  unfold bothAlgDataT'; rw [dif_neg h1', dif_neg h2', dif_pos h1'', dif_pos h2t]

/-- Reduction, leaf `(both, snd)`, target `both`. -/
theorem bothAlgDataT'_both_snd_both (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 = p''.1)
    (h2t : p'.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_both_snd hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'').inv ≫
        (mapSpfIso hI
          ((τX p.1 p'.1 h1').trans
            ((awaySelfMulA hI (gX p'.1 p.1)).trans (awayCongrEltA (by rw [h1'']))))
          ((awayCongrEltB (mul_comm _ _)).trans
            (σY p.2 p'.2 p''.2 h2' (fun eq => hpp'' (Prod.ext h1'' eq)) h2t))).hom ≫
        (bothAlgDataSrcIso_both_both hI gX gY p' p'' p hp'p'' hpp'.symm
          (fun e => h1' (h1''.trans e.symm)) h2t (fun e => h1' e.symm)
          (fun e => h2' e.symm)).hom := by
  unfold bothAlgDataT'; rw [dif_neg h1', dif_neg h2', dif_pos h1'', dif_neg h2t]

/-- Reduction, leaf `(both, fst)`, target `snd`. -/
theorem bothAlgDataT'_both_fst_snd (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 = p''.2) (h1t : p'.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_both_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        (mapSpfIso hI
          ((awayCongrEltA (by rw [h1t])).trans
            ((awaySelfMulA hI (gX p.1 p'.1)).symm.trans (τX p.1 p'.1 h1')))
          ((τY p.2 p'.2 h2').trans
            ((awaySelfMulB hI (gY p'.2 p.2)).trans (awayCongrEltB (by rw [h2'']))))).hom ≫
        (bothAlgDataSrcIso_snd_both hI gX gY p' p'' p hp'p'' hpp'.symm
          h1t (fun e => h1' e.symm) (fun e => h2' e.symm)).hom := by
  unfold bothAlgDataT'; rw [dif_neg h1', dif_neg h2', dif_neg h1'', dif_pos h2'', dif_pos h1t]

/-- Reduction, leaf `(both, fst)`, target `both`. -/
theorem bothAlgDataT'_both_fst_both (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 = p''.2) (h1t : p'.1 ≠ p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_both_fst hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        (mapSpfIso hI ((awayCongrEltA (mul_comm _ _)).trans (σX p.1 p'.1 p''.1 h1' h1'' h1t))
          ((τY p.2 p'.2 h2').trans
            ((awaySelfMulB hI (gY p'.2 p.2)).trans (awayCongrEltB (by rw [h2'']))))).hom ≫
        (bothAlgDataSrcIso_both_both hI gX gY p' p'' p hp'p'' hpp'.symm
          h1t (fun e => h2' (h2''.trans e.symm)) (fun e => h1' e.symm)
          (fun e => h2' e.symm)).hom := by
  unfold bothAlgDataT'; rw [dif_neg h1', dif_neg h2', dif_neg h1'', dif_pos h2'', dif_neg h1t]

/-- Reduction, leaf `(both, both)`, target `snd`. -/
theorem bothAlgDataT'_both_both_snd (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 ≠ p''.2) (h1t : p'.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_both_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        (mapSpfIso hI
          ((awayCongrEltA (by rw [h1t])).trans
            ((awaySelfMulA hI (gX p.1 p'.1)).symm.trans (τX p.1 p'.1 h1')))
          (σY p.2 p'.2 p''.2 h2' h2'' (fun eq => hp'p'' (Prod.ext h1t eq)))).hom ≫
        (bothAlgDataSrcIso_snd_both hI gX gY p' p'' p hp'p'' hpp'.symm
          h1t (fun e => h1' e.symm) (fun e => h2' e.symm)).hom := by
  unfold bothAlgDataT'
  rw [dif_neg h1', dif_neg h2', dif_neg h1'', dif_neg h2'', dif_pos h1t]

/-- Reduction, leaf `(both, both)`, target `fst`. -/
theorem bothAlgDataT'_both_both_fst (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 ≠ p''.2) (h1t : p'.1 ≠ p''.1) (h2t : p'.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_both_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        (mapSpfIso hI (σX p.1 p'.1 p''.1 h1' h1'' h1t)
          ((awayCongrEltB (by rw [h2t])).trans
            ((awaySelfMulB hI (gY p.2 p'.2)).symm.trans (τY p.2 p'.2 h2')))).hom ≫
        (bothAlgDataSrcIso_fst_both hI gX gY p' p'' p hp'p'' hpp'.symm
          h1t h2t (fun e => h1' e.symm) (fun e => h2' e.symm)).hom := by
  unfold bothAlgDataT'
  rw [dif_neg h1', dif_neg h2', dif_neg h1'', dif_neg h2'', dif_neg h1t, dif_pos h2t]

/-- Reduction, leaf `(both, both)`, target `both`. -/
theorem bothAlgDataT'_both_both_both (h1' : p.1 ≠ p'.1) (h2' : p.2 ≠ p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 ≠ p''.2) (h1t : p'.1 ≠ p''.1) (h2t : p'.2 ≠ p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' =
      (bothAlgDataSrcIso_both_both hI gX gY p p' p'' hpp' hpp'' h1' h2' h1'' h2'').inv ≫
        (mapSpfIso hI (σX p.1 p'.1 p''.1 h1' h1'' h1t)
          (σY p.2 p'.2 p''.2 h2' h2'' h2t)).hom ≫
        (bothAlgDataSrcIso_both_both hI gX gY p' p'' p hp'p'' hpp'.symm
          h1t h2t (fun e => h1' e.symm) (fun e => h2' e.symm)).hom := by
  unfold bothAlgDataT'
  rw [dif_neg h1', dif_neg h2', dif_neg h1'', dif_neg h2'', dif_neg h1t, dif_neg h2t]

end AlgebraicGeometry
