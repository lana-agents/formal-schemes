import FormalSchemes.GeneralFibreProductAffineBase
import FormalSchemes.CompletedTensorAwayInterchangePullbackLegs

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# A smart constructor for `AffineChartedFibreDatum` from pure algebra data

Fix an adic base `(R, I)` with `I` finitely generated and an affine base change `Spf B`. The
structure `AlgebraicGeometry.AffineChartedFibreDatum`
(`FormalSchemes.GeneralFibreProductAffineBase`) packages a general affine-charted glued `X` over
`Spf R` together with the *geometric* triple-overlap datum `t'`, `t_fac`, `cocycle` of the fibre
product `X ×_{Spf R} Spf B`. Those geometric fields are stated at the level of *pullbacks* of the
interchange open immersions, and are tedious to provide by hand.

This file provides `AlgebraicGeometry.AffineChartedFibreDatum.ofAlgebraData`, a smart constructor
which **derives** the geometric fields `t'`, `t_fac`, `cocycle` from purely algebraic data:

* the non-geometric fields of the structure — the index `J`, chart algebras `A`, away elements `g`,
  single-overlap transitions `τ` with the symmetry `τ_symm`;
* the double-overlap transitions
  `σ i j k : A_i{1/(g_ij·g_ik)} ≃ₐ[R] A_j{1/(g_jk·g_ji)}`;
* the σ/τ restriction compatibility `hστ` and σ's algebra triple cocycle `hσc`.

The derived transition is
`t' i j k := (interchangePullbackIso I g_ij g_ik hI).inv ≫ (mapSpfIso σ (refl B)).hom ≫
  (interchangePullbackIso I g_jk g_ji hI).hom`,
and its two laws reduce, via the leg identifications `interchangePullbackIso_hom_fst`/`_snd`
(`FormalSchemes.CompletedTensorAwayInterchangePullbackLegs`) and the `⊗̂_R B` transport
`CompletedTensorProduct.mapSpf_comp₃`, to the algebra identities `hστ` and `hσc`.

The two-patch template `AlgebraicGeometry.twoPatchFibreProductDatum` is re-exhibited through the
smart constructor in `AlgebraicGeometry.twoPatchFibreProductDatumOfAlg`, with `σ`, `hστ`, `hσc`
all vacuous (no pairwise-distinct triple exists on `ULift Bool`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

namespace AffineChartedFibreDatum

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable {B : Type u} [CommRing B] [Algebra R B]
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable (g : ∀ (i : J), J → A i)

/-- **The derived geometric triple-overlap transition of the fibre product.** From the algebra
double-overlap transition `σ i j k : A_i{1/(g_ij·g_ik)} ≃ₐ[R] A_j{1/(g_jk·g_ji)}` we build the
pullback-level map `pullback (f g_ij) (f g_ik) ⟶ pullback (f g_jk) (f g_ji)` by transporting
`mapSpfIso σ (refl B)` through the two interchange-pullback identifications. -/
def algDataT'
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i j) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i k) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j k) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j i) hI
    (pullback (interchangeOpenImmersion (B := B) I (g i j) hI)
        (interchangeOpenImmersion (B := B) I (g i k) hI) ⟶
      pullback (interchangeOpenImmersion (B := B) I (g j k) hI)
        (interchangeOpenImmersion (B := B) I (g j i) hI)) :=
  (interchangePullbackIso (B := B) I (g i j) (g i k) hI).inv ≫
    (mapSpfIso hI (σ i j k hij hik hjk) (AlgEquiv.refl (R := R) (A₁ := B))).hom ≫
    (interchangePullbackIso (B := B) I (g j k) (g j i) hI).hom

/-- **`t_fac` for the derived transition.** The derived `t'` is compatible with the base-changed
single-overlap transition `t = (mapSpfIso τ (refl B)).hom`; this reduces to the σ/τ compatibility
`hστ` at the algebra level via the interchange-pullback leg identifications. -/
theorem algDataT'_fac
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toAlgHom.comp (furtherLocSnd I (g j k) (g j i) hI) =
        (furtherLocFst I (g i j) (g i k) hI).comp (τ i j hij).symm.toAlgHom)
    (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i j) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i k) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j k) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j i) hI
    algDataT' hI A g σ i j k hij hik hjk ≫
        pullback.snd (interchangeOpenImmersion (B := B) I (g j k) hI)
          (interchangeOpenImmersion (B := B) I (g j i) hI) =
      pullback.fst (interchangeOpenImmersion (B := B) I (g i j) hI)
          (interchangeOpenImmersion (B := B) I (g i k) hI) ≫
        (mapSpfIso hI (τ i j hij) (AlgEquiv.refl (R := R) (A₁ := B))).hom := by
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i j) hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i k) hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j k) hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j i) hI
  have hrefl : (AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom = AlgHom.id R B := by
    ext x
    simp
  have hfst : pullback.fst (interchangeOpenImmersion (B := B) I (g i j) hI)
        (interchangeOpenImmersion (B := B) I (g i k) hI) =
      (interchangePullbackIso (B := B) I (g i j) (g i k) hI).inv ≫
        mapSpf hI (furtherLocFst I (g i j) (g i k) hI) (AlgHom.id R B) := by
    rw [← interchangePullbackIso_hom_fst (B := B) I (g i j) (g i k) hI, Iso.inv_hom_id_assoc]
  simp only [algDataT', Category.assoc]
  rw [interchangePullbackIso_hom_snd (B := B) I (g j k) (g j i) hI, hfst, Category.assoc,
    Iso.cancel_iso_inv_left]
  simp only [mapSpfIso_hom]
  rw [hrefl, ← mapSpf_comp, ← mapSpf_comp, hστ i j k hij hik hjk]

/-- **`cocycle` for the derived transition.** The three derived transitions around a distinct triple
compose to the identity: adjacent interchange-pullback isomorphisms cancel, leaving the three
`mapSpf σ.symm` which compose to the identity by `mapSpf_comp₃` and σ's algebra cocycle `hσc`. -/
theorem algDataT'_cocycle
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))
    (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i j) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i k) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j k) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j i) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g k i) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g k j) hI
    algDataT' (B := B) hI A g σ i j k hij hik hjk ≫
        algDataT' (B := B) hI A g σ j k i hjk hij.symm hik.symm ≫
      algDataT' (B := B) hI A g σ k i j hik.symm hjk.symm hij = 𝟙 _ := by
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i j) hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i k) hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j k) hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j i) hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g k i) hI
  haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g k j) hI
  -- the algebra cocycle for the three `σ.symm` (from `hσc` by inverting the equation)
  have hf : (σ i j k hij hik hjk).symm.toAlgHom.comp
        ((σ j k i hjk hij.symm hik.symm).symm.toAlgHom.comp
          (σ k i j hik.symm hjk.symm hij).symm.toAlgHom) =
      AlgHom.id R (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)) := by
    have h2 : ((σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij))).symm = AlgEquiv.refl (R := R) := by
      rw [hσc i j k hij hik hjk, AlgEquiv.refl_symm]
    refine AlgHom.ext fun x => ?_
    have hx := AlgEquiv.ext_iff.mp h2 x
    simp only [AlgEquiv.symm_trans_apply, AlgEquiv.coe_refl, id_eq] at hx
    simpa using hx
  -- the base factor cocycle is trivial (all identities)
  have hg : (AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom.comp
        ((AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom.comp
          (AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom) = AlgHom.id R B := by
    ext x
    simp
  -- the three `mapSpfIso σ` collapse to the identity
  have hmid : (mapSpfIso hI (σ i j k hij hik hjk) (AlgEquiv.refl (R := R) (A₁ := B))).hom ≫
      (mapSpfIso hI (σ j k i hjk hij.symm hik.symm) (AlgEquiv.refl (R := R) (A₁ := B))).hom ≫
      (mapSpfIso hI (σ k i j hik.symm hjk.symm hij) (AlgEquiv.refl (R := R) (A₁ := B))).hom
      = 𝟙 _ := by
    rw [mapSpfIso_hom, mapSpfIso_hom, mapSpfIso_hom]
    exact mapSpf_comp₃ hI _ _ _ _ _ _ hf hg
  simp only [algDataT', Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, reassoc_of% hmid, Iso.inv_hom_id]

/-- **The smart constructor for `AffineChartedFibreDatum` from algebra data.** The caller supplies
only the non-geometric fields (`J`, `A`, `g`, `τ`, `τ_symm`) together with the double-overlap
transitions `σ`, their σ/τ compatibility `hστ` and their algebra cocycle `hσc`; the geometric fields
`t'`, `t_fac`, `cocycle` are derived by `algDataT'`, `algDataT'_fac`, `algDataT'_cocycle`. -/
def ofAlgebraData
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toAlgHom.comp (furtherLocSnd I (g j k) (g j i) hI) =
        (furtherLocFst I (g i j) (g i k) hI).comp (τ i j hij).symm.toAlgHom)
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k))) :
    AffineChartedFibreDatum R I hI B where
  J := J
  A := A
  g := g
  τ := τ
  τ_symm := τ_symm
  t' := algDataT' hI A g σ
  t_fac := algDataT'_fac hI A g τ σ hστ
  cocycle := algDataT'_cocycle hI A g σ hσc

end AffineChartedFibreDatum

/-! ### Validation: the two-patch template through the smart constructor -/

/-- On the two-element index type `ULift Bool`, no triple is pairwise distinct; this discharges the
vacuous algebra data `σ`, `hστ`, `hσc` for the two-patch datum built via `ofAlgebraData`. -/
private theorem uliftBool_not_pairwise_distinct' {i j k : ULift.{u} Bool}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : False := by
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  obtain ⟨k⟩ := k
  cases i <;> cases j <;> cases k <;> simp_all

/-- **The two-chart Tate fibre product through `ofAlgebraData`.** Re-exhibits
`twoPatchFibreProductDatum` via the smart constructor, reusing the same chart/overlap/transition
data. Because no triple of `ULift Bool` indices is pairwise distinct, the double-overlap data `σ`,
`hστ`, `hσc` are all vacuous. -/
def twoPatchFibreProductDatumOfAlg (R : Type u) [CommRing R] (I : Ideal R) (q : R) (hI : I.FG)
    (B : Type u) [CommRing B] [Algebra R B] : AffineChartedFibreDatum R I hI B :=
  AffineChartedFibreDatum.ofAlgebraData hI
    (A := fun _ : ULift.{u} Bool => annulusAlgebra R I q)
    (g := fun i _ => cond i.down (overlapY R I q) (overlapX R I q))
    (τ := fun i j h => match i, j, h with
      | ⟨false⟩, ⟨true⟩, _ => annulusFibreChartTransitionAlg R I q hI
      | ⟨true⟩, ⟨false⟩, _ => (annulusFibreChartTransitionAlg R I q hI).symm
      | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
      | ⟨true⟩, ⟨true⟩, h => (h rfl).elim)
    (τ_symm := by
      rintro ⟨_ | _⟩ ⟨_ | _⟩ h
      · exact absurd rfl h
      · rfl
      · exact ((annulusFibreChartTransitionAlg R I q hI).symm_symm).symm
      · exact absurd rfl h)
    (σ := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct' hij hik hjk).elim)
    (hστ := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct' hij hik hjk).elim)
    (hσc := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct' hij hik hjk).elim)

end AlgebraicGeometry
