import FormalSchemes.GeneralFibreProductAffineBase
import FormalSchemes.TwoPatchFibreProductProjectionLeft
import FormalSchemes.GlueMorphisms

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Exposing the glued affine-charted scheme `X` inside the fibre-product datum

`AlgebraicGeometry.AffineChartedFibreDatum` (`FormalSchemes.GeneralFibreProductAffineBase`)
packages a general affine-charted glued `X` over `Spf R` together with an affine base `Spf B`, but
only through its **algebra data** (the chart `R`-algebras `A i`, the away elements `g i j`, the
transitions `τ i j`) and the *fibre-product* geometric cocycle triple `t'` / `t_fac` / `cocycle`.
It never builds the glued `X` object itself.

This file builds `X`'s own glue pipeline, mirroring the fibre-product pipeline
`AffineChartedFibreDatum.glueData' → lrsGlueData → formalGlueData → fibreProduct`, but for `X` alone
(no `⊗̂_R B`), cleanly in the `I·A_i = I.map (algebraMap R (A i))` convention. The key
simplification is `CompletedTensorAwayInterchange.idealOfDef_base_eq`, which identifies the ideal of
definition `I·(A_i{1/g})` of the away completion with `FormalSpectrum.awayCompletionIdeal`, so `X`'s
overlaps live over `FormalSpectrum.basicOpenChart` with no ideal-convention bridges.

## Main definitions

* `AlgebraicGeometry.AffineChartedFibreDatumX`: extends `AffineChartedFibreDatum` with `X`'s own
  geometric triple-overlap cocycle `xt'` / `xt_fac` / `xcocycle` over the basic-open charts, plus
  the per-chart topology and adic-ring data needed to see each `Spf (A i)` as a formal scheme.
* `AffineChartedFibreDatumX.xGlueData'` / `xLrsGlueData` / `xFormalGlueData`: the glue datum of `X`
  as a `CategoryTheory.GlueData'`, a `LocallyRingedSpace.GlueData`, and a `FormalScheme.GlueData`.
* `AffineChartedFibreDatumX.xGlued`: the glued formal scheme `X`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

/-! ### The X-side transition of two away-completion charts -/

section AwayTransition

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {S S' : Type u} [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']

/-- **The `le_comap` datum for the `X`-side transition of two away-completion charts.** For an
`R`-algebra isomorphism `e` between the away completions `A{1/s}` and `A'{1/s'}`, the underlying
ring hom of `e.symm` carries the ideal of definition of `A'{1/s'}` into that of `A{1/s}`; phrased in
the `awayCompletionIdeal` convention via `idealOfDef_base_eq`. -/
theorem awayCompletionTransition_le_comap (s : S) (s' : S')
    (e : awayCompletion (I.map (algebraMap R S)) s ≃ₐ[R]
      awayCompletion (I.map (algebraMap R S')) s') :
    awayCompletionIdeal (I.map (algebraMap R S')) s' ≤
      (awayCompletionIdeal (I.map (algebraMap R S)) s).comap e.symm.toRingHom := by
  have key := CompletedTensorProduct.algHom_mapIdeal_isAdicHom (I := I) e.symm.toAlgHom
  rw [CompletedTensorAwayInterchange.idealOfDef_base_eq,
    CompletedTensorAwayInterchange.idealOfDef_base_eq] at key
  exact key.le_comap

/-- **The `X`-side transition** `Spf(A{1/s}) ⟶ Spf(A'{1/s'})` of two away-completion charts induced
by an `R`-algebra isomorphism `e : A{1/s} ≃ₐ[R] A'{1/s'}`. It is `Spf` of the underlying ring hom of
`e.symm` (the formal spectrum is contravariant), phrased in the `awayCompletionIdeal` convention. -/
def awayCompletionTransition (s : S) (s' : S')
    (e : awayCompletion (I.map (algebraMap R S)) s ≃ₐ[R]
      awayCompletion (I.map (algebraMap R S')) s') :
    locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R S)) s) ⟶
      locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R S')) s') :=
  locallyRingedSpaceMap (awayCompletionIdeal (I.map (algebraMap R S')) s')
    (awayCompletionIdeal (I.map (algebraMap R S)) s) e.symm.toRingHom
    (awayCompletionTransition_le_comap s s' e)

/-- **Self-inverse law of the `X`-side transition.** The transition of `e` followed by the
transition of `e.symm` is the identity, because the two underlying ring homs compose to the
identity. This is the input to the `t_inv` field of the `X` glue datum. -/
theorem awayCompletionTransition_comp (s : S) (s' : S')
    (e : awayCompletion (I.map (algebraMap R S)) s ≃ₐ[R]
      awayCompletion (I.map (algebraMap R S')) s') :
    awayCompletionTransition s s' e ≫ awayCompletionTransition s' s e.symm = 𝟙 _ := by
  have hcomp : e.symm.toRingHom.comp e.symm.symm.toRingHom = RingHom.id _ := by
    rw [AlgEquiv.symm_symm]
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    exact e.symm_apply_apply x
  rw [awayCompletionTransition, awayCompletionTransition,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (φ := e.symm.symm.toRingHom) (ψ := e.symm.toRingHom)
      (hIJ := awayCompletionTransition_le_comap s' s e.symm)
      (hJK := awayCompletionTransition_le_comap s s' e)
      (hIK := by rw [hcomp]; exact (Ideal.comap_id _).ge)]
  exact (FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ (RingHom.id _) _
    (Ideal.comap_id _).ge hcomp).trans (FormalSpectrum.locallyRingedSpaceMap_id _)

end AwayTransition

/-! ### The general affine-charted `X` input datum -/

set_option linter.unusedVariables false in
/-- **A general affine-charted glued `X` over `Spf R`, exposed as a glueable object.** This extends
`AffineChartedFibreDatum` (which packages `X` only through its algebra data and the fibre-product
cocycle) with `X`'s **own** geometric triple-overlap cocycle over the basic-open charts, together
with the per-chart topology and adic-ring data needed to view each `Spf (A i)` as a formal scheme.

The fields `xt'`, `xt_fac`, `xcocycle` are the direct analogues of `t'`, `t_fac`, `cocycle` of the
base datum, but living over `FormalSpectrum.basicOpenChart (I·A_i) (g i j)` (rather than the
fibre-product `interchangeOpenImmersion`) with transition the `X`-side transition map. -/
structure AffineChartedFibreDatumX (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
    (B : Type u) [CommRing B] [Algebra R B]
    extends AffineChartedFibreDatum R I hI B where
  /-- The `I·A_i`-adic topology on each chart algebra `A i`. -/
  [topology : ∀ i : J, TopologicalSpace (A i)]
  /-- Each chart `A i` is a complete adic ring with ideal of definition `I·A_i`. -/
  [isAdic : ∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]
  /-- The geometric triple-overlap transition of `X`'s own glue. -/
  xt' : ∀ (i j k : J) (_hij : i ≠ j) (_hik : i ≠ k) (_hjk : j ≠ k),
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j i) (hI.map _)
    (pullback (basicOpenChart (I.map (algebraMap R (A i))) (g i j))
        (basicOpenChart (I.map (algebraMap R (A i))) (g i k)) ⟶
      pullback (basicOpenChart (I.map (algebraMap R (A j))) (g j k))
        (basicOpenChart (I.map (algebraMap R (A j))) (g j i)))
  /-- Compatibility of `xt'` with the `X`-side transition (the `t_fac` law). -/
  xt_fac : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j i) (hI.map _)
    xt' i j k hij hik hjk ≫
        pullback.snd (basicOpenChart (I.map (algebraMap R (A j))) (g j k))
          (basicOpenChart (I.map (algebraMap R (A j))) (g j i)) =
      pullback.fst (basicOpenChart (I.map (algebraMap R (A i))) (g i j))
          (basicOpenChart (I.map (algebraMap R (A i))) (g i k)) ≫
        awayCompletionTransition (g i j) (g j i) (τ i j hij)
  /-- The triple cocycle of `X`'s own glue. -/
  xcocycle : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i j) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A i))) (g i k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j k) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A j))) (g j i) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A k))) (g k i) (hI.map _)
    letI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (A k))) (g k j) (hI.map _)
    xt' i j k hij hik hjk ≫ xt' j k i hjk hij.symm hik.symm ≫
      xt' k i j hik.symm hjk.symm hij = 𝟙 _

namespace AffineChartedFibreDatumX

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable {B : Type u} [CommRing B] [Algebra R B]
variable (D : AffineChartedFibreDatumX R I hI B)

/-- **The affine-charted `X` glue datum** as a `CategoryTheory.GlueData'` on `D.J`: the `i`-th chart
is `Spf(A i)`, the overlap immersion `f i j` is `basicOpenChart (I·A_i) (g i j)`, the transition
`t i j` is the `X`-side `awayCompletionTransition`, and the cocycle fields `t'`, `t_fac`, `cocycle`
are the carried geometric datum of `D`. The structural laws `f_mono`, `f_hasPullback`, `t_inv` are
discharged uniformly. -/
def xGlueData' : CategoryTheory.GlueData' LocallyRingedSpace.{u} :=
  letI := D.commRing
  letI := D.algebra
  { J := D.J
    U := fun i => locallyRingedSpaceObj (I.map (algebraMap R (D.A i)))
    V := fun i j _ =>
      locallyRingedSpaceObj (awayCompletionIdeal (I.map (algebraMap R (D.A i))) (D.g i j))
    f := fun i j _ => basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i j)
    f_mono := fun i j _ => by
      haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i j) (hI.map _)
      infer_instance
    f_hasPullback := fun i j k _ _ => by
      haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i j) (hI.map _)
      haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i k) (hI.map _)
      infer_instance
    t := fun i j h => awayCompletionTransition (D.g i j) (D.g j i) (D.τ i j h)
    t' := D.xt'
    t_fac := D.xt_fac
    t_inv := fun i j h => by
      rw [D.τ_symm i j h]
      exact awayCompletionTransition_comp (D.g i j) (D.g j i) (D.τ i j h)
    cocycle := D.xcocycle }

/-- **The affine-charted `X` glue datum as a `LocallyRingedSpace.GlueData`**, via
`GlueData.ofGlueData'` and the open-immersion field `f_open`. -/
def xLrsGlueData : LocallyRingedSpace.GlueData.{u} :=
  letI := D.commRing
  letI := D.algebra
  { CategoryTheory.GlueData.ofGlueData' D.xGlueData' with
    f_open := by
      rintro i j
      simp only [xGlueData', CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · haveI := isOpenImmersion_basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i j) (hI.map _)
        exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
          (eqToHom _ ≫ basicOpenChart (I.map (algebraMap R (D.A i))) (D.g i j))) }

/-- **The affine-charted `X` glue datum as a `FormalScheme.GlueData`**: each chart is the affine
formal scheme `Spf(A i)`. -/
def xFormalGlueData : FormalScheme.GlueData.{u} :=
  letI := D.commRing
  letI := D.algebra
  letI := D.topology
  letI := D.isAdic
  { toLocallyRingedSpaceGlueData := D.xLrsGlueData
    isFormalScheme := fun i =>
      ⟨FormalScheme.Spf (I.map (algebraMap R (D.A i))), ⟨Iso.refl _⟩⟩ }

/-- **The glued affine-charted formal scheme `X`.** -/
def xGlued : FormalScheme.{u} :=
  D.xFormalGlueData.gluedFormalScheme

end AffineChartedFibreDatumX

/-! ### Validation: the two-patch template as a special case -/

/-- On the two-element index type `ULift Bool`, no triple is pairwise distinct; this discharges the
vacuous geometric cocycle fields of the two-patch `X`-expose datum. -/
private theorem uliftBool_not_pairwise_distinct {i j k : ULift.{u} Bool}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : False := by
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  obtain ⟨k⟩ := k
  cases i <;> cases j <;> cases k <;> simp_all

/-- **The two-chart Tate `X`-expose datum.** Extends `twoPatchFibreProductDatum` with the per-chart
topology and adic-ring data of the Tate annulus and the (vacuous, since `ULift Bool` has no pairwise
distinct triple) geometric cocycle fields. This witnesses that `AffineChartedFibreDatumX` is
inhabitable. -/
def twoPatchExposeXDatum (R : Type u) [CommRing R] (I : Ideal R) (q : R) (hI : I.FG)
    (B : Type u) [CommRing B] [Algebra R B] [IsNoetherianRing R] :
    AffineChartedFibreDatumX R I hI B :=
  { twoPatchFibreProductDatum R I q hI B with
    topology := fun _ => annulusTopologicalSpace R I q
    isAdic := fun _ =>
      annulus_map_eq R I q ▸ annulus_isAdicRing R I q hI
    xt' := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim
    xt_fac := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim
    xcocycle := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim }

end AlgebraicGeometry
