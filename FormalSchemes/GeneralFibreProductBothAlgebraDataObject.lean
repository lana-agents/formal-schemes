import FormalSchemes.GeneralFibreProductBothObject
import FormalSchemes.CompletedTensorAwayInterchangeBoth

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Object-level dispatch for the two-sided fibre product `X ×_{Spf R} Y` from algebra data

Fix an adic base `(R, I)` with `I` finitely generated, index types `JX`, `JY`, chart `R`-algebras
`A : JX → Type u`, `B : JY → Type u`, overlap away-elements `gX i i' : A i`, `gY j j' : B j`, and
single-overlap `R`-algebra transitions `τX`, `τY` (with symmetries). This file assembles the
**object-level** fields of the two-sided smart constructor `BothChartedFibreDatum.ofAlgebraData`
(sibling brick 332b): the coordinate-difference-dispatched overlap object `bothAlgDataV`, the
overlap immersion `bothAlgDataF` with its open-immersion witness `bothAlgDataHf`, the transition
`bothAlgDataT`, and the self-inverse law `bothAlgDataT_inv`. The triple-overlap fields
`t'`/`t_fac`/`cocycle` (which genuinely use `⊗̂`-associativity) are deferred to brick 332b.

## The 3-way dispatch

For distinct `p p' : JX × JY`, at least one coordinate differs. The overlap chart of `(p, p')` in
`Spf(A_{p.1} ⊗̂_R B_{p.2})` dispatches on which coordinate differs:

* `p.1 = p'.1` (so the second differs): localize the `B` factor —
  `rightInterchangeOpenImmersion`, domain `Spf(A_{p.1} ⊗̂_R B_{p.2}{1/g_Y})`;
* `p.1 ≠ p'.1`, `p.2 = p'.2`: localize the `A` factor — `interchangeOpenImmersion`, domain
  `Spf(A_{p.1}{1/g_X} ⊗̂_R B_{p.2})`;
* both differ: localize both factors — `bothInterchangeOpenImmersion`, domain
  `Spf(A_{p.1}{1/g_X} ⊗̂_R B_{p.2}{1/g_Y})`.

## The object-defeq wall

The overlap object `bothAlgDataV p p' h` has a *type* depending on the dispatch branch, and the
`Classical` decidability of the coordinate equalities is opaque, so the branch `dite`s do not reduce
by `rfl`. We reduce them propositionally through the reduction lemmas
`bothAlgDataV_snd`/`_fst`/`_both`, and cross the reductions with `eqToHom`. The *shared-coordinate*
mismatch in the swap `V p p' → V p' p` (e.g. `A_{p.1}` versus `A_{p'.1}` when `p.1 = p'.1`) is
absorbed into an algebra isomorphism `eqAlgEquivA`/`eqAlgEquivB` (transport of `AlgEquiv.refl` along
the coordinate equality), so that the `mapSpfIso` codomains match `V p' p` exactly and the
self-inverse law reduces uniformly to `mapSpfIso`'s `hom`-then-`symm.hom` cancellation.

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

/-! ### The shared-coordinate transport isomorphisms -/

/-- Transport of the identity algebra isomorphism along an equality of `X`-chart indices; used to
absorb the shared first-coordinate mismatch of the swap `V p p' → V p' p` into a clean algebra
isomorphism. -/
def eqAlgEquivA {i i' : JX} (h : i = i') : A i ≃ₐ[R] A i' := by
  subst h; exact AlgEquiv.refl

/-- Transport of the identity algebra isomorphism along an equality of `Y`-chart indices. -/
def eqAlgEquivB {j j' : JY} (h : j = j') : B j ≃ₐ[R] B j' := by
  subst h; exact AlgEquiv.refl

theorem eqAlgEquivA_symm {i i' : JX} (h : i = i') :
    (eqAlgEquivA (A := A) (R := R) h).symm = eqAlgEquivA h.symm := by
  subst h; rfl

theorem eqAlgEquivB_symm {j j' : JY} (h : j = j') :
    (eqAlgEquivB (B := B) (R := R) h).symm = eqAlgEquivB h.symm := by
  subst h; rfl

/-! ### The dispatched overlap object -/

set_option linter.unusedVariables false in
/-- **The coordinate-difference-dispatched overlap object** of two distinct product-index charts of
`X ×_{Spf R} Y`, over the concrete double-tensor charts. The finite-generation witness `hI` is
carried only to pin the base ideal `I` (hence `R`) at use sites. -/
def bothAlgDataV (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' : JX × JY) (h : p ≠ p') : LocallyRingedSpace.{u} :=
  if h1 : p.1 = p'.1 then
    locallyRingedSpaceObj (idealOfDefinition R I (A p.1)
      (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2)))
  else if h2 : p.2 = p'.2 then
    locallyRingedSpaceObj (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1)) (B p.2))
  else
    locallyRingedSpaceObj (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1))
      (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2)))

/-- Reduction of `bothAlgDataV` in the *second-coordinate-differs* shape (`p.1 = p'.1`). -/
theorem bothAlgDataV_snd (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' : JX × JY) (h : p ≠ p') (h1 : p.1 = p'.1) :
    bothAlgDataV hI gX gY p p' h =
      locallyRingedSpaceObj (idealOfDefinition R I (A p.1)
        (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2))) := by
  unfold bothAlgDataV; exact dif_pos h1

/-- Reduction of `bothAlgDataV` in the *first-coordinate-differs* shape (`p.1 ≠ p'.1`,
`p.2 = p'.2`). -/
theorem bothAlgDataV_fst (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' : JX × JY) (h : p ≠ p') (h1 : p.1 ≠ p'.1) (h2 : p.2 = p'.2) :
    bothAlgDataV hI gX gY p p' h =
      locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1)) (B p.2)) := by
  unfold bothAlgDataV; rw [dif_neg h1, dif_pos h2]

/-- Reduction of `bothAlgDataV` in the *both-coordinates-differ* shape. -/
theorem bothAlgDataV_both (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' : JX × JY) (h : p ≠ p') (h1 : p.1 ≠ p'.1) (h2 : p.2 ≠ p'.2) :
    bothAlgDataV hI gX gY p p' h =
      locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (A p.1))) (gX p.1 p'.1))
        (awayCompletion (I.map (algebraMap R (B p.2))) (gY p.2 p'.2))) := by
  unfold bothAlgDataV; rw [dif_neg h1, dif_neg h2]

/-! ### The dispatched overlap immersion and its open-immersion witness -/

/-- **The coordinate-difference-dispatched overlap immersion** `bothAlgDataV p p' → Spf(A ⊗̂ B)`. -/
def bothAlgDataF (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' : JX × JY) (h : p ≠ p') :
    bothAlgDataV hI gX gY p p' h ⟶
      locallyRingedSpaceObj (idealOfDefinition R I (A p.1) (B p.2)) :=
  if h1 : p.1 = p'.1 then
    eqToHom (bothAlgDataV_snd hI gX gY p p' h h1) ≫
      rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p'.2) hI
  else if h2 : p.2 = p'.2 then
    eqToHom (bothAlgDataV_fst hI gX gY p p' h h1 h2) ≫
      interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI
  else
    eqToHom (bothAlgDataV_both hI gX gY p p' h h1 h2) ≫
      bothInterchangeOpenImmersion I (gX p.1 p'.1) (gY p.2 p'.2) hI

/-- **The overlap immersion `bothAlgDataF` is an open immersion.** -/
theorem bothAlgDataHf (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (p p' : JX × JY) (h : p ≠ p') :
    LocallyRingedSpace.IsOpenImmersion (bothAlgDataF hI gX gY p p' h) := by
  unfold bothAlgDataF
  split_ifs with h1 h2
  · haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := A p.1) I (gY p.2 p'.2) hI
    infer_instance
  · haveI := isOpenImmersion_interchangeOpenImmersion (B := B p.2) I (gX p.1 p'.1) hI
    infer_instance
  · haveI := isOpenImmersion_bothInterchangeOpenImmersion I (gX p.1 p'.1) (gY p.2 p'.2) hI
    infer_instance

/-! ### The dispatched transition and its self-inverse law -/

/-- **The coordinate-difference-dispatched transition** `bothAlgDataV p p' → bothAlgDataV p' p` of
the two overlap objects of a pair of distinct charts. The shared coordinate is carried by
`eqAlgEquivA`/`eqAlgEquivB`, the differing one(s) by `τX`/`τY`. -/
def bothAlgDataT (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (τX : ∀ (i i' : JX), i ≠ i' →
      (awayCompletion (I.map (algebraMap R (A i))) (gX i i') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A i'))) (gX i' i)))
    (τY : ∀ (j j' : JY), j ≠ j' →
      (awayCompletion (I.map (algebraMap R (B j))) (gY j j') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (B j'))) (gY j' j)))
    (p p' : JX × JY) (h : p ≠ p') :
    bothAlgDataV hI gX gY p p' h ⟶ bothAlgDataV hI gX gY p' p h.symm :=
  if h1 : p.1 = p'.1 then
    eqToHom (bothAlgDataV_snd hI gX gY p p' h h1) ≫
      (mapSpfIso hI (eqAlgEquivA h1) (τY p.2 p'.2 (fun e => h (Prod.ext h1 e)))).hom ≫
      eqToHom (bothAlgDataV_snd hI gX gY p' p h.symm h1.symm).symm
  else if h2 : p.2 = p'.2 then
    eqToHom (bothAlgDataV_fst hI gX gY p p' h h1 h2) ≫
      (mapSpfIso hI (τX p.1 p'.1 h1) (eqAlgEquivB h2)).hom ≫
      eqToHom (bothAlgDataV_fst hI gX gY p' p h.symm (fun e => h1 e.symm) h2.symm).symm
  else
    eqToHom (bothAlgDataV_both hI gX gY p p' h h1 h2) ≫
      (mapSpfIso hI (τX p.1 p'.1 h1) (τY p.2 p'.2 h2)).hom ≫
      eqToHom (bothAlgDataV_both hI gX gY p' p h.symm (fun e => h1 e.symm)
        (fun e => h2 e.symm)).symm

/-- Cancellation of `mapSpfIso`'s forward leg against the forward leg of the inverse pair. -/
theorem mapSpfIso_hom_symm_hom (hI : I.FG) {A₀ B₀ A₀' B₀' : Type u} [CommRing A₀] [CommRing B₀]
    [Algebra R A₀] [Algebra R B₀] [CommRing A₀'] [CommRing B₀'] [Algebra R A₀'] [Algebra R B₀']
    (e₁ : A₀ ≃ₐ[R] A₀') (e₂ : B₀ ≃ₐ[R] B₀') :
    haveI := isAdicRing R I A₀ B₀ hI
    haveI := isAdicRing R I A₀' B₀' hI
    (mapSpfIso hI e₁ e₂).hom ≫ (mapSpfIso hI e₁.symm e₂.symm).hom = 𝟙 _ := by
  haveI := isAdicRing R I A₀ B₀ hI
  haveI := isAdicRing R I A₀' B₀' hI
  rw [mapSpfIso_symm, Iso.symm_hom]
  exact (mapSpfIso hI e₁ e₂).hom_inv_id

/-- **The dispatched transitions are mutually inverse.** -/
theorem bothAlgDataT_inv (hI : I.FG) (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
    (τX : ∀ (i i' : JX), i ≠ i' →
      (awayCompletion (I.map (algebraMap R (A i))) (gX i i') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A i'))) (gX i' i)))
    (τY : ∀ (j j' : JY), j ≠ j' →
      (awayCompletion (I.map (algebraMap R (B j))) (gY j j') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (B j'))) (gY j' j)))
    (τX_symm : ∀ (i i' : JX) (h : i ≠ i'), τX i' i h.symm = (τX i i' h).symm)
    (τY_symm : ∀ (j j' : JY) (h : j ≠ j'), τY j' j h.symm = (τY j j' h).symm)
    (p p' : JX × JY) (h : p ≠ p') :
    bothAlgDataT hI gX gY τX τY p p' h ≫ bothAlgDataT hI gX gY τX τY p' p h.symm = 𝟙 _ := by
  unfold bothAlgDataT
  by_cases h1 : p.1 = p'.1
  · -- second-coordinate differs
    have hb : p.2 ≠ p'.2 := fun e => h (Prod.ext h1 e)
    rw [dif_pos h1, dif_pos h1.symm, τY_symm p.2 p'.2 hb, ← eqAlgEquivA_symm h1]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% (mapSpfIso_hom_symm_hom hI (eqAlgEquivA h1) (τY p.2 p'.2 hb))]
    simp
  · by_cases h2 : p.2 = p'.2
    · -- first-coordinate differs
      rw [dif_neg h1, dif_pos h2, dif_neg (fun e => h1 e.symm), dif_pos h2.symm,
        τX_symm p.1 p'.1 h1, ← eqAlgEquivB_symm h2]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [reassoc_of% (mapSpfIso_hom_symm_hom hI (τX p.1 p'.1 h1) (eqAlgEquivB h2))]
      simp
    · -- both coordinates differ
      rw [dif_neg h1, dif_neg h2, dif_neg (fun e => h1 e.symm), dif_neg (fun e => h2 e.symm),
        τX_symm p.1 p'.1 h1, τY_symm p.2 p'.2 h2]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [reassoc_of% (mapSpfIso_hom_symm_hom hI (τX p.1 p'.1 h1) (τY p.2 p'.2 h2))]
      simp

/-! ### Validation: the object-level fields plug into `BothChartedFibreDatum`

We check the five object-level helpers typecheck against the corresponding `BothChartedFibreDatum`
fields, by re-deriving a subsingleton-index datum whose off-diagonal `V`/`f`/`hf`/`t`/`t_inv` are
the dispatched helpers (and whose triple-overlap fields are vacuous). This yields a real
`generalFibreProduct : FormalScheme` built through the dispatch. -/

/-- **A subsingleton-index witness whose object-level fields are the dispatched helpers.** On
`JX = JY = PUnit` no two charts are distinct, so the triple-overlap fields are vacuous, but the
`V`/`f`/`hf`/`t`/`t_inv` fields are the genuine 3-way-dispatched helpers, validating that they have
the right types. -/
def punitBothAlgDataDatum (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG) :
    BothChartedFibreDatum R I hI where
  JX := PUnit
  JY := PUnit
  A := fun _ => R
  B := fun _ => R
  gX := fun _ _ => 1
  gY := fun _ _ => 1
  τX := fun i i' h => (h (Subsingleton.elim i i')).elim
  τX_symm := fun i i' h => (h (Subsingleton.elim i i')).elim
  τY := fun j j' h => (h (Subsingleton.elim j j')).elim
  τY_symm := fun j j' h => (h (Subsingleton.elim j j')).elim
  V := bothAlgDataV hI (fun _ _ => 1) (fun _ _ => 1)
  f := bothAlgDataF hI (fun _ _ => 1) (fun _ _ => 1)
  hf := bothAlgDataHf hI (fun _ _ => 1) (fun _ _ => 1)
  t := bothAlgDataT hI (fun _ _ => 1) (fun _ _ => 1)
    (fun i i' h => (h (Subsingleton.elim i i')).elim)
    (fun j j' h => (h (Subsingleton.elim j j')).elim)
  t_inv := bothAlgDataT_inv hI (fun _ _ => 1) (fun _ _ => 1)
    (fun i i' h => (h (Subsingleton.elim i i')).elim)
    (fun j j' h => (h (Subsingleton.elim j j')).elim)
    (fun i i' h => (h (Subsingleton.elim i i')).elim)
    (fun j j' h => (h (Subsingleton.elim j j')).elim)
  t' := fun p p' _ hpp' _ _ => (hpp' (Subsingleton.elim p p')).elim
  t_fac := fun p p' _ hpp' _ _ => (hpp' (Subsingleton.elim p p')).elim
  cocycle := fun p p' _ hpp' _ _ => (hpp' (Subsingleton.elim p p')).elim

end AlgebraicGeometry
