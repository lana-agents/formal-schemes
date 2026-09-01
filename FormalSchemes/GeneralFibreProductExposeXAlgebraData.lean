import FormalSchemes.BasicOpenChartOverlapLegs
import FormalSchemes.GeneralFibreProductAlgebraData
import FormalSchemes.GeneralFibreProductExposeX

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# A smart constructor for `AffineChartedFibreDatumX` from pure algebra data

Fix an adic base `(R, I)` with `I` finitely generated and an affine base change `Spf B`. The
structure `AlgebraicGeometry.AffineChartedFibreDatumX`
(`FormalSchemes.GeneralFibreProductExposeX`) packages a general affine-charted glued `X` over
`Spf R` together with **two** geometric triple-overlap triples: `t'` / `t_fac` / `cocycle` over the
fibre-product charts `Spf(A_i ⊗̂_R B)`, and `xt'` / `xt_fac` / `xcocycle` over `X`'s own charts
`Spf(A_i)`.

The first triple already has a smart constructor,
`AlgebraicGeometry.AffineChartedFibreDatum.ofAlgebraData`
(`FormalSchemes.GeneralFibreProductAlgebraData`), deriving it from purely algebraic data: the
double-overlap transitions `σ i j k : A_i{1/(g_ij·g_ik)} ≃ₐ[R] A_j{1/(g_jk·g_ji)}`, their σ/τ
restriction compatibility `hστ`, and their algebra triple cocycle `hσc`. This file supplies the
`X`-side counterpart and the combined constructor.

## What is new

The `X`-side transition is built over `FormalSpectrum.basicOpenChart` rather than the fibre-product
`interchangeOpenImmersion`, so the geometric input is the basic-open chart overlap identification
`FormalSpectrum.basicOpenChartOverlapIso` together with its leg identifications
`basicOpenChartOverlapIso_hom_fst` / `_hom_snd`, and the transported map is
`AlgebraicGeometry.awayCompletionTransition` rather than `CompletedTensorProduct.mapSpfIso`.

Crucially the **same** `σ` / `hστ` / `hσc` feed both triples. The compatibility `hστ` is phrased
with the further-localization algebra maps `furtherLocFst` / `furtherLocSnd`, whereas the basic-open
leg identifications are phrased with `awayCompletionMulHomLeft` / `awayCompletionMulHomRight`; these
are the *same* ring maps (`furtherLocFst_toRingHom`, `furtherLocSnd_toRingHom`, both `rfl` — each
side is `AdicCompletion.mapCompletion` of `IsLocalization.Away.lift`, differing only in the `IsUnit`
proof). That is what lets one algebra datum produce a whole `AffineChartedFibreDatumX`.

## Main definitions

* `AlgebraicGeometry.awayCompletionTransition_comp₃`: three `X`-side transitions whose underlying
  ring maps compose to the identity compose to `𝟙` — the `X`-side analogue of
  `CompletedTensorProduct.mapSpf_comp₃`.
* `AlgebraicGeometry.AffineChartedFibreDatumX.xAlgDataT'` and its two laws `xAlgDataT'_fac`,
  `xAlgDataT'_cocycle`: the derived `X`-side geometric triple-overlap datum.
* `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData`: the combined smart constructor.
* `AlgebraicGeometry.twoPatchExposeXDatumOfAlg`: the two-chart Tate datum re-exhibited through it.

Note that no ≥3-chart datum is built here — this file only makes one possible, by removing the need
to provide the six geometric fields by hand.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

/-! ### The `furtherLoc` / `awayCompletionMulHom` bridge -/

section Bridge

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A : Type u} [CommRing A] [Algebra R A]

/-- **The `furtherLoc` / `awayCompletionMulHom` bridge, left.** The further-localization algebra
map `furtherLocFst` of the fibre-product layer and the further completed localization
`awayCompletionMulHomLeft` of the basic-open chart layer are the same ring map: both are
`AdicCompletion.mapCompletion` of `IsLocalization.Away.lift g₁ _`, and the two `IsUnit` witnesses
are proofs of the same proposition. -/
theorem furtherLocFst_toRingHom (g₁ g₂ : A) (hI : I.FG) :
    (furtherLocFst I g₁ g₂ hI).toRingHom =
      awayCompletionMulHomLeft (I.map (algebraMap R A)) g₁ g₂ (hI.map _) :=
  rfl

/-- **The `furtherLoc` / `awayCompletionMulHom` bridge, right.** -/
theorem furtherLocSnd_toRingHom (g₁ g₂ : A) (hI : I.FG) :
    (furtherLocSnd I g₁ g₂ hI).toRingHom =
      awayCompletionMulHomRight (I.map (algebraMap R A)) g₁ g₂ (hI.map _) :=
  rfl

end Bridge

/-! ### The threefold composition law for the `X`-side transition -/

section Transition3

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {S S' S'' : Type u} [CommRing S] [CommRing S'] [CommRing S'']
variable [Algebra R S] [Algebra R S'] [Algebra R S'']

/-- **Threefold composition law for the `X`-side transition.** If the three underlying ring maps
compose (cyclically) to the identity, the three induced morphisms of formal spectra compose to the
identity morphism. This is the `X`-side analogue of `CompletedTensorProduct.mapSpf_comp₃`, and the
threefold companion of `awayCompletionTransition_comp`; it is the reduction that turns `σ`'s algebra
cocycle into the geometric `xcocycle`. -/
theorem awayCompletionTransition_comp₃ (s : S) (s' : S') (s'' : S'')
    (e₁ : awayCompletion (I.map (algebraMap R S)) s ≃ₐ[R]
      awayCompletion (I.map (algebraMap R S')) s')
    (e₂ : awayCompletion (I.map (algebraMap R S')) s' ≃ₐ[R]
      awayCompletion (I.map (algebraMap R S'')) s'')
    (e₃ : awayCompletion (I.map (algebraMap R S'')) s'' ≃ₐ[R]
      awayCompletion (I.map (algebraMap R S)) s)
    (h : e₁.symm.toRingHom.comp (e₂.symm.toRingHom.comp e₃.symm.toRingHom) = RingHom.id _) :
    awayCompletionTransition s s' e₁ ≫ awayCompletionTransition s' s'' e₂ ≫
      awayCompletionTransition s'' s e₃ = 𝟙 _ := by
  have hc12 : awayCompletionIdeal (I.map (algebraMap R S'')) s'' ≤
      (awayCompletionIdeal (I.map (algebraMap R S)) s).comap
        (e₁.symm.toRingHom.comp e₂.symm.toRingHom) := by
    intro x hx
    exact awayCompletionTransition_le_comap s s' e₁
      (awayCompletionTransition_le_comap s' s'' e₂ hx)
  have hcomp : (e₁.symm.toRingHom.comp e₂.symm.toRingHom).comp e₃.symm.toRingHom =
      RingHom.id _ := by
    rw [RingHom.comp_assoc]
    exact h
  have hc123 : awayCompletionIdeal (I.map (algebraMap R S)) s ≤
      (awayCompletionIdeal (I.map (algebraMap R S)) s).comap
        ((e₁.symm.toRingHom.comp e₂.symm.toRingHom).comp e₃.symm.toRingHom) := by
    rw [hcomp]
    exact (Ideal.comap_id _).ge
  have h12 := FormalSpectrum.locallyRingedSpaceMap_comp
    (awayCompletionIdeal (I.map (algebraMap R S'')) s'')
    (awayCompletionIdeal (I.map (algebraMap R S')) s')
    (awayCompletionIdeal (I.map (algebraMap R S)) s)
    e₂.symm.toRingHom e₁.symm.toRingHom
    (awayCompletionTransition_le_comap s' s'' e₂)
    (awayCompletionTransition_le_comap s s' e₁) hc12
  have h123 := FormalSpectrum.locallyRingedSpaceMap_comp
    (awayCompletionIdeal (I.map (algebraMap R S)) s)
    (awayCompletionIdeal (I.map (algebraMap R S'')) s'')
    (awayCompletionIdeal (I.map (algebraMap R S)) s)
    e₃.symm.toRingHom (e₁.symm.toRingHom.comp e₂.symm.toRingHom)
    (awayCompletionTransition_le_comap s'' s e₃) hc12 hc123
  rw [awayCompletionTransition, awayCompletionTransition, awayCompletionTransition,
    ← Category.assoc, ← h12, ← h123]
  exact (FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ (RingHom.id _) _
    (Ideal.comap_id _).ge hcomp).trans (FormalSpectrum.locallyRingedSpaceMap_id _)

end Transition3

/-! ### The derived `X`-side geometric triple-overlap datum -/

namespace AffineChartedFibreDatumX

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable (g : ∀ (i : J), J → A i)

/-- **The derived geometric triple-overlap transition of `X` itself.** From the algebra
double-overlap transition `σ i j k : A_i{1/(g_ij·g_ik)} ≃ₐ[R] A_j{1/(g_jk·g_ji)}` we build the
pullback-level map `pullback (bOC g_ij) (bOC g_ik) ⟶ pullback (bOC g_jk) (bOC g_ji)` by transporting
the `X`-side transition `awayCompletionTransition σ` through the two basic-open chart overlap
identifications of issue 553. This is the `X`-side analogue of
`AlgebraicGeometry.AffineChartedFibreDatum.algDataT'`. -/
def xAlgDataT'
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j i) (hI.map _)
    (pullback (basicOpenChart (I.map (algebraMap R (A i))) (g i j))
        (basicOpenChart (I.map (algebraMap R (A i))) (g i k)) ⟶
      pullback (basicOpenChart (I.map (algebraMap R (A j))) (g j k))
        (basicOpenChart (I.map (algebraMap R (A j))) (g j i))) :=
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i j) (hI.map _)
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i k) (hI.map _)
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j k) (hI.map _)
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j i) (hI.map _)
  (basicOpenChartOverlapIso (I.map (algebraMap R (A i))) (g i j) (g i k) (hI.map _)).inv ≫
    awayCompletionTransition (g i j * g i k) (g j k * g j i) (σ i j k hij hik hjk) ≫
    (basicOpenChartOverlapIso (I.map (algebraMap R (A j))) (g j k) (g j i) (hI.map _)).hom

/-- **`xt_fac` for the derived transition.** The derived `xt'` is compatible with the `X`-side
single-overlap transition `awayCompletionTransition τ`; this reduces to the very same σ/τ
compatibility `hστ` that `AffineChartedFibreDatum.algDataT'_fac` consumes, via the basic-open chart
overlap leg identifications of issue 555. -/
theorem xAlgDataT'_fac
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
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j i) (hI.map _)
    xAlgDataT' hI A g σ i j k hij hik hjk ≫
        pullback.snd (basicOpenChart (I.map (algebraMap R (A j))) (g j k))
          (basicOpenChart (I.map (algebraMap R (A j))) (g j i)) =
      pullback.fst (basicOpenChart (I.map (algebraMap R (A i))) (g i j))
          (basicOpenChart (I.map (algebraMap R (A i))) (g i k)) ≫
        awayCompletionTransition (g i j) (g j i) (τ i j hij) := by
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i j) (hI.map _)
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i k) (hI.map _)
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j k) (hI.map _)
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j i) (hI.map _)
  have hfst : pullback.fst (basicOpenChart (I.map (algebraMap R (A i))) (g i j))
        (basicOpenChart (I.map (algebraMap R (A i))) (g i k)) =
      (basicOpenChartOverlapIso (I.map (algebraMap R (A i))) (g i j) (g i k) (hI.map _)).inv ≫
        basicOpenChartFurtherLeft (I.map (algebraMap R (A i))) (g i j) (g i k) (hI.map _) :=
    (basicOpenChartOverlapIso_inv_comp_furtherLeft
      (I.map (algebraMap R (A i))) (g i j) (g i k) (hI.map _)).symm
  simp only [xAlgDataT', Category.assoc]
  rw [basicOpenChartOverlapIso_hom_snd (I.map (algebraMap R (A j))) (g j k) (g j i) (hI.map _),
    hfst, Category.assoc, Iso.cancel_iso_inv_left]
  have hφ : (σ i j k hij hik hjk).symm.toRingHom.comp
        (awayCompletionMulHomRight (I.map (algebraMap R (A j))) (g j k) (g j i) (hI.map _)) =
      (awayCompletionMulHomLeft (I.map (algebraMap R (A i))) (g i j) (g i k) (hI.map _)).comp
        (τ i j hij).symm.toRingHom :=
    RingHom.ext fun x => AlgHom.congr_fun (hστ i j k hij hik hjk) x
  have hcL : awayCompletionIdeal (I.map (algebraMap R (A j))) (g j i) ≤
      (awayCompletionIdeal (I.map (algebraMap R (A i))) (g i j * g i k)).comap
        ((σ i j k hij hik hjk).symm.toRingHom.comp
          (awayCompletionMulHomRight (I.map (algebraMap R (A j))) (g j k) (g j i)
            (hI.map _))) := by
    intro x hx
    exact awayCompletionTransition_le_comap (g i j * g i k) (g j k * g j i)
      (σ i j k hij hik hjk)
      (le_comap_awayCompletionMulHomRight (I.map (algebraMap R (A j))) (g j k) (g j i)
        (hI.map _) hx)
  have hcR : awayCompletionIdeal (I.map (algebraMap R (A j))) (g j i) ≤
      (awayCompletionIdeal (I.map (algebraMap R (A i))) (g i j * g i k)).comap
        ((awayCompletionMulHomLeft (I.map (algebraMap R (A i))) (g i j) (g i k)
          (hI.map _)).comp (τ i j hij).symm.toRingHom) := by
    rw [← hφ]
    exact hcL
  rw [awayCompletionTransition, basicOpenChartFurtherRight,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (awayCompletionIdeal (I.map (algebraMap R (A j))) (g j i))
      (awayCompletionIdeal (I.map (algebraMap R (A j))) (g j k * g j i))
      (awayCompletionIdeal (I.map (algebraMap R (A i))) (g i j * g i k))
      (awayCompletionMulHomRight (I.map (algebraMap R (A j))) (g j k) (g j i) (hI.map _))
      (σ i j k hij hik hjk).symm.toRingHom
      (le_comap_awayCompletionMulHomRight (I.map (algebraMap R (A j))) (g j k) (g j i)
        (hI.map _))
      (awayCompletionTransition_le_comap (g i j * g i k) (g j k * g j i)
        (σ i j k hij hik hjk)) hcL,
    basicOpenChartFurtherLeft, awayCompletionTransition,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (awayCompletionIdeal (I.map (algebraMap R (A j))) (g j i))
      (awayCompletionIdeal (I.map (algebraMap R (A i))) (g i j))
      (awayCompletionIdeal (I.map (algebraMap R (A i))) (g i j * g i k))
      (τ i j hij).symm.toRingHom
      (awayCompletionMulHomLeft (I.map (algebraMap R (A i))) (g i j) (g i k) (hI.map _))
      (awayCompletionTransition_le_comap (g i j) (g j i) (τ i j hij))
      (le_comap_awayCompletionMulHomLeft (I.map (algebraMap R (A i))) (g i j) (g i k)
        (hI.map _)) hcR]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ hcL hcR hφ

/-- **`xcocycle` for the derived transition.** The three derived `X`-side transitions around a
distinct triple compose to the identity: adjacent basic-open overlap identifications cancel, leaving
the three `awayCompletionTransition σ`, which compose to the identity by
`awayCompletionTransition_comp₃` and σ's algebra cocycle `hσc`. -/
theorem xAlgDataT'_cocycle
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))
    (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j i) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A k))) (g k i) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A k))) (g k j) (hI.map _)
    xAlgDataT' hI A g σ i j k hij hik hjk ≫
        xAlgDataT' hI A g σ j k i hjk hij.symm hik.symm ≫
      xAlgDataT' hI A g σ k i j hik.symm hjk.symm hij = 𝟙 _ := by
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i j) (hI.map _)
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i k) (hI.map _)
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j k) (hI.map _)
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j i) (hI.map _)
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A k))) (g k i) (hI.map _)
  letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A k))) (g k j) (hI.map _)
  have hf : (σ i j k hij hik hjk).symm.toRingHom.comp
        ((σ j k i hjk hij.symm hik.symm).symm.toRingHom.comp
          (σ k i j hik.symm hjk.symm hij).symm.toRingHom) = RingHom.id _ := by
    have h2 : ((σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij))).symm = AlgEquiv.refl (R := R) := by
      rw [hσc i j k hij hik hjk, AlgEquiv.refl_symm]
    refine RingHom.ext fun x => ?_
    have hx := AlgEquiv.ext_iff.mp h2 x
    simp only [AlgEquiv.symm_trans_apply, AlgEquiv.coe_refl, id_eq] at hx
    simpa using hx
  have hmid : awayCompletionTransition (g i j * g i k) (g j k * g j i) (σ i j k hij hik hjk) ≫
      awayCompletionTransition (g j k * g j i) (g k i * g k j)
        (σ j k i hjk hij.symm hik.symm) ≫
      awayCompletionTransition (g k i * g k j) (g i j * g i k)
        (σ k i j hik.symm hjk.symm hij) = 𝟙 _ :=
    awayCompletionTransition_comp₃ _ _ _ _ _ _ hf
  simp only [xAlgDataT', Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, reassoc_of% hmid, Iso.inv_hom_id]

variable {B : Type u} [CommRing B] [Algebra R B]

/-- **The smart constructor for `AffineChartedFibreDatumX` from algebra data.** The caller supplies
only the non-geometric fields (`J`, `A`, `g`, `τ`, `τ_symm`, and the per-chart topology / adic-ring
data) together with the double-overlap transitions `σ`, their σ/τ compatibility `hστ` and their
algebra cocycle `hσc`; **both** geometric triples are derived — the fibre-product one by
`AffineChartedFibreDatum.ofAlgebraData` and the `X`-side one by `xAlgDataT'`, `xAlgDataT'_fac`,
`xAlgDataT'_cocycle`.

Note that a single `σ` / `hστ` / `hσc` feeds both: the `X`-side compatibility is literally the same
algebra identity as the fibre-product one, because `furtherLocFst`/`furtherLocSnd` and
`awayCompletionMulHomLeft`/`awayCompletionMulHomRight` are the same ring maps
(`furtherLocFst_toRingHom`, `furtherLocSnd_toRingHom`). -/
def ofAlgebraData
    [topology : ∀ i : J, TopologicalSpace (A i)]
    [isAdic : ∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]
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
    AffineChartedFibreDatumX R I hI B :=
  { AffineChartedFibreDatum.ofAlgebraData hI A g τ τ_symm σ hστ hσc with
    topology := topology
    isAdic := isAdic
    xt' := xAlgDataT' hI A g σ
    xt_fac := xAlgDataT'_fac hI A g τ σ hστ
    xcocycle := xAlgDataT'_cocycle hI A g σ hσc }

end AffineChartedFibreDatumX

/-! ### Validation: the two-patch `X`-expose datum through the smart constructor -/

/-- **The two-chart Tate `X`-expose datum through `ofAlgebraData`.** Re-exhibits
`twoPatchExposeXDatum` via the smart constructor, reusing the same chart/overlap/transition data and
the same per-chart topology / adic-ring witnesses. Because no triple of `ULift Bool` indices is
pairwise distinct, the double-overlap data `σ`, `hστ`, `hσc` — and hence both derived geometric
triples — are vacuous; this only witnesses that the constructor's signature is instantiable. -/
def twoPatchExposeXDatumOfAlg (R : Type u) [CommRing R] (I : Ideal R) (q : R) (hI : I.FG)
    (B : Type u) [CommRing B] [Algebra R B] [IsNoetherianRing R] :
    AffineChartedFibreDatumX R I hI B :=
  AffineChartedFibreDatumX.ofAlgebraData hI
    (A := fun _ : ULift.{u} Bool => annulusAlgebra R I q)
    (g := fun i _ => cond i.down (overlapY R I q) (overlapX R I q))
    (topology := fun _ => annulusTopologicalSpace R I q)
    (isAdic := fun _ => annulus_map_eq R I q ▸ annulus_isAdicRing R I q hI)
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
    (σ := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim)
    (hστ := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim)
    (hσc := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim)

end AlgebraicGeometry

end
