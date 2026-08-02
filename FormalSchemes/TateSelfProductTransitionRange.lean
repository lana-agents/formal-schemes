import FormalSchemes.TateSelfProductTripleOverlap
import FormalSchemes.TateSelfProductTransition
import FormalSchemes.TwoPatchFibreProductProjection

set_option linter.style.header false
-- The completed-tensor interchange morphisms range over the nested localization/completion
-- towers of the completed tensor product, which are slow for the elaborator and the kernel;
-- raise the budgets (matching `TateSelfProductTripleOverlap.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Base-map / range tracking of the Tate self-product overlap transitions

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. The four-chart Tate self-fibre-product `𝔈_q ×_{Spf R} 𝔈_q` glue is built from three
overlap charts fixing a source chart (`TateSelfProductTripleOverlap`): `firstFactorOverlapChart`
(first factor differs, range `D(x⊗1) ∪ D(y⊗1)`), `secondFactorOverlapChart` (second factor differs,
range `D(1⊗x) ∪ D(1⊗y)`), `bothFactorOverlapChart` (both differ, range the intersection of the two),
together with the summand-swap transition involutions (`TateSelfProductTransition`).

The genuine `Bool × Bool` cocycle (issue 301 / 237 brick c2) is built via
`glueTPrimeOfLift (f i j) (f i k) (f j k) (f j i) (t i j) (H i j k)` whose only remaining obligation
per pairwise-distinct triple is the range inclusion
`H : (t i j).base '' ( (f i j).base ⁻¹' range (f i k).base ) ⊆ (f i j).base ⁻¹' range (f j k).base`.
This file discharges `H`, reduced by Klein-four symmetry to three shape classes.

## The reduction

Since `range (bothFactorOverlapChart) = range (firstFactorOverlapChart) ∩
range (secondFactorOverlapChart)` (`range_bothFactorOverlapChart_eq_inter_first_second`) and
`chart ⁻¹' range chart = univ` (`Set.preimage_range`), the target region always collapses:

* **first shape** (`t = t_first`, source region `f_first ⁻¹' range f_second`, target
  `f_first ⁻¹' range f_both = f_first ⁻¹' range f_second`): the inclusion is the statement that
  `t_first` *preserves* the second-factor-membership region. This holds because `t_first` is a
  morphism over the second projection `Spf(inr) : Spf(A ⊗̂_R A) ⟶ Spf A`
  (`firstTransition_comp_secondProj`, built from `twoPatchFibreProduct_pr₂_naturality`), and
  `range f_second` is `pr₂`-saturated (`secondFactorOverlapChart_range_eq_preimage`).
* **both shape** (`t = t_both`): trivial — `range f_both ⊆ range f_first` and
  `range f_both ⊆ range f_second`, so both preimage regions are `Set.univ`.

## Main results

* `tateSelfProductFirstTransition_image_subset`, `tateSelfProductBothTransition_image_subset`:
  the range inclusions closing `H` for the first-factor and both-factor source-chart shapes.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- If a self-map `h` of `α` commutes with `g` over the target (`g ∘ h = g`), then `h` preserves
every `g`-saturated region: `h '' (g ⁻¹' W) ⊆ g ⁻¹' W`. A purely set-theoretic fact, used to turn a
morphism-level "over the projection" identity into the range inclusion `H`. -/
theorem image_preimage_subset_of_comp_eq {α β : Type*} {h : α → α} {g : α → β} {W : Set β}
    (hg : g ∘ h = g) : h '' (g ⁻¹' W) ⊆ g ⁻¹' W := by
  rintro _ ⟨x, hx, rfl⟩
  have hgx : g (h x) = g x := congrFun hg x
  rw [Set.mem_preimage, hgx]
  exact hx

/-! ### First shape: the first-factor transition is a morphism over the second projection -/

/-- **The first-factor transition is a morphism over the second projection.** Composing the
first-factor overlap chart with the second projection `Spf(inr) : Spf(A ⊗̂_R A) ⟶ Spf A` is
invariant under the summand-swap transition `tateSelfProductFirstTransition`, since that transition
only touches the first tensor factor. Assembled by `coprod.hom_ext` from the two-patch second
projection naturality squares (`twoPatchFibreProduct_pr₂_naturality{,'}` with `B := A`); note
`tateSelfProductFirstTransition`'s per-summand map is definitionally
`twoPatchFibreProductTransition R I q (annulusAlgebra R I q) hI`. -/
theorem firstTransition_comp_secondProj (hI : I.FG) :
    (tateSelfProductFirstTransition R I q hI).hom ≫
        firstFactorOverlapChart R I q hI ≫
          pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) =
      firstFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q) := by
  refine coprod.hom_ext ?_ ?_
  · simp only [tateSelfProductFirstTransition, firstFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact (twoPatchFibreProduct_pr₂_naturality R I q (annulusAlgebra R I q) hI).symm
  · simp only [tateSelfProductFirstTransition, firstFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact (twoPatchFibreProduct_pr₂_naturality' R I q (annulusAlgebra R I q) hI).symm

/-- The preimage under the second projection `Spf(inr) : Spf(A ⊗̂_R A) ⟶ Spf A` of a basic open
`D(g) ⊆ Spf A` is the basic open `D(inr g) ⊆ Spf(A ⊗̂_R A)`: `pr₂Chart.base` is the model `mapTop`
of `inr`, so this is the general basic-open preimage law `FormalSpectrum.map_preimage_basicOpen`. -/
private theorem pr₂Chart_base_preimage_basicOpen (g : annulusAlgebra R I q) :
    ⇑(pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q)).base ⁻¹'
        (↑(FormalSpectrum.basicOpen (I.map (algebraMap R (annulusAlgebra R I q))) g) :
          Set (FormalSpectrum (I.map (algebraMap R (annulusAlgebra R I q))))) =
      (↑(FormalSpectrum.basicOpen
          (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
            (annulusAlgebra R I q))
          (CompletedTensorProduct.inr R I (annulusAlgebra R I q) (annulusAlgebra R I q) g)) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I
          (annulusAlgebra R I q) (annulusAlgebra R I q)))) := by
  have hval : (CompletedTensorProduct.inr R I (annulusAlgebra R I q)
        (annulusAlgebra R I q)).toRingHom g =
      CompletedTensorProduct.inr R I (annulusAlgebra R I q) (annulusAlgebra R I q) g :=
    rfl
  have hpre := FormalSpectrum.map_preimage_basicOpen
    (I.map (algebraMap R (annulusAlgebra R I q)))
    (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
    (CompletedTensorProduct.inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)).toRingHom
    CompletedTensorProduct.inr_isAdicHom.le_comap g
  rw [hval] at hpre
  exact congrArg SetLike.coe hpre

/-- **`range f_second` is saturated for the second projection.** The range of the second-factor
overlap chart is the `pr₂`-preimage of `D(overlapX) ∪ D(overlapY) ⊆ Spf A`. From
`range_secondFactorOverlapChart` (`= D(inr x) ∪ D(inr y)`) and the basic-open preimage law
`FormalSpectrum.map_preimage_basicOpen` (`pr₂ ⁻¹' D(g) = D(inr g)`, since `pr₂Chart.base` is the
model `mapTop` of `inr`). -/
theorem secondFactorOverlapChart_range_eq_preimage (hI : I.FG) :
    Set.range (secondFactorOverlapChart R I q hI).base =
      (pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q)).base ⁻¹'
        (↑(FormalSpectrum.basicOpen (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q)) ∪
          ↑(FormalSpectrum.basicOpen (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q)) :
          Set (FormalSpectrum (I.map (algebraMap R (annulusAlgebra R I q))))) := by
  rw [range_secondFactorOverlapChart R I q hI]
  exact (congrArg₂ (· ∪ ·)
      (pr₂Chart_base_preimage_basicOpen R I q (overlapX R I q)).symm
      (pr₂Chart_base_preimage_basicOpen R I q (overlapY R I q)).symm).trans
    (Set.preimage_union
      (f := ⇑(pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q)).base)
      (s := (↑(FormalSpectrum.basicOpen (I.map (algebraMap R (annulusAlgebra R I q)))
              (overlapX R I q)) :
            Set (FormalSpectrum (I.map (algebraMap R (annulusAlgebra R I q))))))
      (t := (↑(FormalSpectrum.basicOpen (I.map (algebraMap R (annulusAlgebra R I q)))
              (overlapY R I q)) :
            Set (FormalSpectrum (I.map (algebraMap R (annulusAlgebra R I q))))))).symm

/-- **First shape.** `tateSelfProductFirstTransition` carries the source triple-overlap region
`f_first ⁻¹' range f_second` into the target region `f_first ⁻¹' range f_both`. This is the range
inclusion `H` for the four-chart cocycle where the source chart transition is the first-factor swap.
Since `range f_both = range f_first ∩ range f_second`, the target region equals the source region,
and the inclusion is exactly that the transition (a morphism over the second projection) preserves
second-factor membership. -/
theorem tateSelfProductFirstTransition_image_subset (hI : I.FG) :
    (tateSelfProductFirstTransition R I q hI).hom.base ''
        (⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (secondFactorOverlapChart R I q hI).base) ⊆
      ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (bothFactorOverlapChart R I q hI).base := by
  rw [range_bothFactorOverlapChart_eq_inter_first_second R I q hI, Set.preimage_inter,
    Set.preimage_range, Set.univ_inter, secondFactorOverlapChart_range_eq_preimage R I q hI,
    ← Set.preimage_comp]
  apply image_preimage_subset_of_comp_eq
  have h1 : ⇑((tateSelfProductFirstTransition R I q hI).hom ≫
        firstFactorOverlapChart R I q hI ≫
          pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q)).base =
      ⇑(firstFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q)).base := by
    rw [firstTransition_comp_secondProj R I q hI]
  simpa only [LocallyRingedSpace.comp_base, TopCat.coe_comp] using h1

/-! ### Both shape: trivial, the both-overlap range sits inside both single-factor ranges -/

/-- **Both shape.** `tateSelfProductBothTransition` carries the source region
`f_both ⁻¹' range f_first` into `f_both ⁻¹' range f_second`. Trivial: every point of the
both-overlap object maps under `f_both` into `range f_both ⊆ range f_second`
(`range_bothFactorOverlapChart_subset_second`), so the target region is all of `Set.univ`. -/
theorem tateSelfProductBothTransition_image_subset (hI : I.FG) :
    (tateSelfProductBothTransition R I q hI).hom.base ''
        (⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (firstFactorOverlapChart R I q hI).base) ⊆
      ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (secondFactorOverlapChart R I q hI).base := by
  have huniv : ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
      Set.range (secondFactorOverlapChart R I q hI).base = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    exact fun y =>
      range_bothFactorOverlapChart_subset_second R I q hI (Set.mem_range_self y)
  rw [huniv]
  exact Set.subset_univ _

end AlgebraicGeometry
