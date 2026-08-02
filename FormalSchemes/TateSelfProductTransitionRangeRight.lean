import FormalSchemes.TateSelfProductTransitionRange
import FormalSchemes.TwoPatchFibreProductProjectionLeft
import FormalSchemes.CompletedTensorAwayInterchangePr
import FormalSchemes.CompletedTensorAwayInterchangeRight

set_option linter.style.header false
-- The completed-tensor interchange morphisms range over the nested localization/completion
-- towers of the completed tensor product, which are slow for the elaborator and the kernel;
-- raise the budgets (matching `TateSelfProductTransitionRange.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Base-map / range tracking of the Tate self-product overlap transitions — the right shape

This file completes `FormalSchemes/TateSelfProductTransitionRange.lean` (issue 312, 237 brick
c2-infra), which discharged the range inclusion `H` of the four-chart Tate self-product cocycle
`tateSelfProductGlueT'` for the **first** and **both** source-chart shapes. Here we deliver the
remaining **second (right) shape** `tateSelfProductRightTransition_image_subset`, the exact mirror
of the first shape over the *first* projection `Spf(inl) : Spf(A ⊗̂_R A) ⟶ Spf A` (the first shape
runs over the second projection `Spf(inr)`).

## The missing prerequisite

The first shape reduced to the merged fact that the first-factor interchange chart is a morphism
over the affine base's **second** projection
(`interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr`, `CompletedTensorAwayInterchangePr`). The
right shape needs the mirror over the **first** projection:
the second-factor interchange chart `rightInterchangeOpenImmersion` is a morphism over
`Spf(inl : A → A ⊗̂_R B)`, i.e.

`rightInterchangeOpenImmersion g ≫ Spf(inl_{A,B}) = Spf(inl_{A, B{1/g}})`.

Since `rightInterchangeOpenImmersion` is *defined* by conjugating the first-factor interchange with
the completed-tensor commutativity isomorphism `commSpfIso` (`CompletedTensorAwayInterchangeRight`),
we obtain this by transporting the merged `inr`-naturality through `commSpfIso`, using that
`commSpfIso` *swaps the two projections*:

* `commSpfIso_hom_comp_inlMap` : `commSpfIso(A,B).hom ≫ Spf(inl_{B,A}) = Spf(inr_{A,B})`,
* `commSpfIso_hom_comp_inrMap` : `commSpfIso(A,B).hom ≫ Spf(inr_{B,A}) = Spf(inl_{A,B})`,

each reducing (through `locallyRingedSpaceMap_comp`) to the ring-level `commEquiv_inr` /
`commEquiv_inl`.

## The reduction (right shape)

With `range f_both = range f_first ∩ range f_second`
(`range_bothFactorOverlapChart_eq_inter_first_second`) and `chart ⁻¹' range chart = univ`
(`Set.preimage_range`), the target region `f_second ⁻¹' range f_both` collapses to the source region
`f_second ⁻¹' range f_first`, and the inclusion is exactly that `t_right` *preserves* the
first-factor-membership region. This holds because `t_right` is a morphism over the first projection
`Spf(inl)` (`rightTransition_comp_firstProj`, built from the naturality above) and `range f_first`
is `pr₁`-saturated (`firstFactorOverlapChart_range_eq_preimage`).

## Main results

* `CompletedTensorAwayInterchange.rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inl`:
  the second-factor interchange chart is a morphism over the first projection `Spf(inl)`.
* `AlgebraicGeometry.tateSelfProductRightTransition_image_subset`: the range inclusion closing `H`
  for the second-factor source-chart shape.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace CompletedTensorAwayInterchange

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The `hom` leg of the commutativity isomorphism of formal spectra, unfolded to the raw
`locallyRingedSpaceMap` of `commEquiv.symm`. -/
theorem commSpfIso_hom_eq (hI : I.FG) :
    (commSpfIso (A := A) (B := B) I hI).hom =
      FormalSpectrum.locallyRingedSpaceMap (CompletedTensorProduct.idealOfDefinition R I B A)
        (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A) (B := B) hI).symm.toRingHom
        (FormalSpectrum.isAdicHom_ringEquiv_symm _ (isAdicHom_commEquiv I hI)).le_comap :=
  rfl

/-- **The commutativity isomorphism swaps the first projection into the second.** Composing
`commSpfIso(A,B).hom : Spf(A ⊗̂_R B) ⟶ Spf(B ⊗̂_R A)` with the first projection
`Spf(inl_{B,A}) : Spf(B ⊗̂_R A) ⟶ Spf B` recovers the second projection
`Spf(inr_{A,B}) : Spf(A ⊗̂_R B) ⟶ Spf B`, since `commEquiv` sends `inr_{A,B} b` to `inl_{B,A} b`
(`commEquiv_inr`). -/
theorem commSpfIso_hom_comp_inlMap (hI : I.FG) :
    (commSpfIso (A := A) (B := B) I hI).hom ≫
        FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R B))
          (CompletedTensorProduct.idealOfDefinition R I B A)
          (CompletedTensorProduct.inl R I B A).toRingHom
          CompletedTensorProduct.inl_isAdicHom.le_comap =
      FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R B))
        (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inr R I A B).toRingHom
        CompletedTensorProduct.inr_isAdicHom.le_comap := by
  rw [commSpfIso_hom_eq I hI,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (I := I.map (algebraMap R B))
      (J := CompletedTensorProduct.idealOfDefinition R I B A)
      (K := CompletedTensorProduct.idealOfDefinition R I A B)
      (φ := (CompletedTensorProduct.inl R I B A).toRingHom)
      (ψ := (CompletedTensorProduct.commEquiv (A := A) (B := B) hI).symm.toRingHom)
      (hIJ := CompletedTensorProduct.inl_isAdicHom.le_comap)
      (hJK := (FormalSpectrum.isAdicHom_ringEquiv_symm _ (isAdicHom_commEquiv I hI)).le_comap)
      (hIK := (CompletedTensorProduct.inl_isAdicHom.comp
        (FormalSpectrum.isAdicHom_ringEquiv_symm _ (isAdicHom_commEquiv I hI))).le_comap)]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  refine RingHom.ext fun b => ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  change (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A) (B := B) hI).symm
      (CompletedTensorProduct.inl R I B A b) = CompletedTensorProduct.inr R I A B b
  rw [← CompletedTensorProduct.commEquiv_inr (R := R) (I := I) (A := A) (B := B) hI b,
    RingEquiv.symm_apply_apply]

/-- **The commutativity isomorphism swaps the second projection into the first.** Composing
`commSpfIso(A,B).hom : Spf(A ⊗̂_R B) ⟶ Spf(B ⊗̂_R A)` with the second projection
`Spf(inr_{B,A}) : Spf(B ⊗̂_R A) ⟶ Spf A` recovers the first projection
`Spf(inl_{A,B}) : Spf(A ⊗̂_R B) ⟶ Spf A`, since `commEquiv` sends `inl_{A,B} a` to `inr_{B,A} a`
(`commEquiv_inl`). -/
theorem commSpfIso_hom_comp_inrMap (hI : I.FG) :
    (commSpfIso (A := A) (B := B) I hI).hom ≫
        FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R A))
          (CompletedTensorProduct.idealOfDefinition R I B A)
          (CompletedTensorProduct.inr R I B A).toRingHom
          CompletedTensorProduct.inr_isAdicHom.le_comap =
      FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R A))
        (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B).toRingHom
        CompletedTensorProduct.inl_isAdicHom.le_comap := by
  rw [commSpfIso_hom_eq I hI,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (I := I.map (algebraMap R A))
      (J := CompletedTensorProduct.idealOfDefinition R I B A)
      (K := CompletedTensorProduct.idealOfDefinition R I A B)
      (φ := (CompletedTensorProduct.inr R I B A).toRingHom)
      (ψ := (CompletedTensorProduct.commEquiv (A := A) (B := B) hI).symm.toRingHom)
      (hIJ := CompletedTensorProduct.inr_isAdicHom.le_comap)
      (hJK := (FormalSpectrum.isAdicHom_ringEquiv_symm _ (isAdicHom_commEquiv I hI)).le_comap)
      (hIK := (CompletedTensorProduct.inr_isAdicHom.comp
        (FormalSpectrum.isAdicHom_ringEquiv_symm _ (isAdicHom_commEquiv I hI))).le_comap)]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  change (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A) (B := B) hI).symm
      (CompletedTensorProduct.inr R I B A a) = CompletedTensorProduct.inl R I A B a
  rw [← CompletedTensorProduct.commEquiv_inl (R := R) (I := I) (A := A) (B := B) hI a,
    RingEquiv.symm_apply_apply]

/-- **The second-factor interchange open immersion is a morphism over the first projection
`Spf(inl)`.** Composing the second-factor interchange chart
`Spf(A ⊗̂_R (B{1/g})) ⟶ Spf(A ⊗̂_R B)` with the first projection
`Spf(inl_{A,B}) : Spf(A ⊗̂_R B) ⟶ Spf A` recovers the first projection of the localised chart
`Spf(A ⊗̂_R (B{1/g})) ⟶ Spf A` (the first factor `A` is untouched by localising the second factor).
This is the `inl`/second-factor mirror of the merged
`interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr`, obtained by conjugating it through the
commutativity isomorphism `commSpfIso` (the two `commSpfIso`-swaps-projection lemmas above). -/
theorem rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inl (g : B) (hI : I.FG) :
    rightInterchangeOpenImmersion (A := A) I g hI ≫
        FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R A))
          (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B).toRingHom
          CompletedTensorProduct.inl_isAdicHom.le_comap =
      FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R A))
        (CompletedTensorProduct.idealOfDefinition R I A
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) g))
        (CompletedTensorProduct.inl R I A
          (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) g)).toRingHom
        CompletedTensorProduct.inl_isAdicHom.le_comap := by
  rw [rightInterchangeOpenImmersion, Category.assoc, Category.assoc,
    commSpfIso_hom_comp_inlMap (A := B) (B := A) I hI,
    interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr (A := B) (B := A) I g hI,
    commSpfIso_hom_comp_inrMap (A := A)
      (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) g) I hI]

end CompletedTensorAwayInterchange

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The affine first projection `Spf(A ⊗̂_R A) ⟶ Spf A`, as the raw `locallyRingedSpaceMap` of
`inl : A → A ⊗̂_R A`, with `A = annulusAlgebra R I q`. Written raw (no ideal-convention bridge) to
match the interchange/`mapSpf` first-projection naturality lemmas. -/
def pr₁ChartSelf :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q)) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (annulusAlgebra R I q))) :=
  FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R (annulusAlgebra R I q)))
    (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
    (CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)).toRingHom
    CompletedTensorProduct.inl_isAdicHom.le_comap

/-! ### Right shape: the second-factor transition is a morphism over the first projection -/

/-- The double-overlap compatibility of the second-factor interchange charts over the first
projection `Spf(inl)`: the `x`-overlap chart followed by `pr₁` equals the second-factor summand
transition `rightSummand` (`mapSpfIso (refl A) (annulus chart transition)`) followed by the
`y`-overlap chart and `pr₁`. Mirror of `twoPatchFibreProduct_pr₂_naturality` over the first factor:
reduces through `rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inl` on both legs and
`mapSpf_comp_inlMap` on the transition, the residual `Spf(refl A)` collapsing to `𝟙`. -/
theorem rightInterchange_pr₁_naturality (hI : I.FG) :
    rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI ≫
        pr₁ChartSelf R I q =
      (CompletedTensorProduct.mapSpfIso hI (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q))
          (annulusFibreChartTransitionAlg R I q hI)).hom ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI ≫
          pr₁ChartSelf R I q := by
  simp only [pr₁ChartSelf]
  rw [rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inl
      (A := annulusAlgebra R I q) I (overlapX R I q) hI,
    rightInterchangeOpenImmersion_comp_locallyRingedSpaceMap_inl
      (A := annulusAlgebra R I q) I (overlapY R I q) hI,
    CompletedTensorProduct.mapSpfIso_hom,
    CompletedTensorProduct.mapSpf_comp_inlMap hI
      (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom
      (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom]
  have hf : (((AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).symm.toAlgHom :
        annulusAlgebra R I q →ₐ[R] annulusAlgebra R I q)).toRingHom =
      RingHom.id (annulusAlgebra R I q) := by
    ext a; simp
  rw [FormalSpectrum.locallyRingedSpaceMap_congr (φ₂ := RingHom.id (annulusAlgebra R I q))
      (h₂ := (Ideal.comap_id (I.map (algebraMap R (annulusAlgebra R I q)))).ge) (hφ := hf),
    FormalSpectrum.locallyRingedSpaceMap_id, Category.comp_id]

/-- The reverse double-overlap compatibility square (`y`-side): derived from
`rightInterchange_pr₁_naturality` by cancelling `t.inv ≫ t.hom`. -/
theorem rightInterchange_pr₁_naturality' (hI : I.FG) :
    rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI ≫
        pr₁ChartSelf R I q =
      (CompletedTensorProduct.mapSpfIso hI (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q))
          (annulusFibreChartTransitionAlg R I q hI)).inv ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI ≫
          pr₁ChartSelf R I q := by
  rw [rightInterchange_pr₁_naturality R I q hI, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- **The second-factor transition is a morphism over the first projection.** Composing the
second-factor overlap chart with the first projection `Spf(inl) : Spf(A ⊗̂_R A) ⟶ Spf A` is
invariant under the summand-swap transition `tateSelfProductRightTransition`, since that transition
only touches the second tensor factor. Assembled by `coprod.hom_ext` from the two double-overlap
compatibility squares above; note `tateSelfProductRightTransition`'s per-summand map is
definitionally `mapSpfIso hI (refl A) (annulusFibreChartTransitionAlg)`. -/
theorem rightTransition_comp_firstProj (hI : I.FG) :
    (tateSelfProductRightTransition R I q hI).hom ≫
        secondFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q =
      secondFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q := by
  refine coprod.hom_ext ?_ ?_
  · simp only [tateSelfProductRightTransition, secondFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact (rightInterchange_pr₁_naturality R I q hI).symm
  · simp only [tateSelfProductRightTransition, secondFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc]
    exact (rightInterchange_pr₁_naturality' R I q hI).symm

/-- The preimage under the first projection `Spf(inl) : Spf(A ⊗̂_R A) ⟶ Spf A` of a basic open
`D(g) ⊆ Spf A` is the basic open `D(inl g) ⊆ Spf(A ⊗̂_R A)`: `pr₁ChartSelf.base` is the model
`mapTop` of `inl`, so this is the general basic-open preimage law
`FormalSpectrum.map_preimage_basicOpen`. -/
private theorem pr₁ChartSelf_base_preimage_basicOpen (g : annulusAlgebra R I q) :
    ⇑(pr₁ChartSelf R I q).base ⁻¹'
        (↑(FormalSpectrum.basicOpen (I.map (algebraMap R (annulusAlgebra R I q))) g) :
          Set (FormalSpectrum (I.map (algebraMap R (annulusAlgebra R I q))))) =
      (↑(FormalSpectrum.basicOpen
          (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
            (annulusAlgebra R I q))
          (CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q) g)) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I
          (annulusAlgebra R I q) (annulusAlgebra R I q)))) := by
  have hval : (CompletedTensorProduct.inl R I (annulusAlgebra R I q)
        (annulusAlgebra R I q)).toRingHom g =
      CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q) g :=
    rfl
  have hpre := FormalSpectrum.map_preimage_basicOpen
    (I.map (algebraMap R (annulusAlgebra R I q)))
    (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
    (CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)).toRingHom
    CompletedTensorProduct.inl_isAdicHom.le_comap g
  rw [hval] at hpre
  exact congrArg SetLike.coe hpre

/-- **`range f_first` is saturated for the first projection.** The range of the first-factor overlap
chart is the `pr₁`-preimage of `D(overlapX) ∪ D(overlapY) ⊆ Spf A`. From
`range_firstFactorOverlapChart` (`= D(inl x) ∪ D(inl y)`) and the basic-open preimage law
`pr₁ChartSelf_base_preimage_basicOpen` (`pr₁ ⁻¹' D(g) = D(inl g)`). -/
theorem firstFactorOverlapChart_range_eq_preimage (hI : I.FG) :
    Set.range (firstFactorOverlapChart R I q hI).base =
      (pr₁ChartSelf R I q).base ⁻¹'
        (↑(FormalSpectrum.basicOpen (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q)) ∪
          ↑(FormalSpectrum.basicOpen (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q)) :
          Set (FormalSpectrum (I.map (algebraMap R (annulusAlgebra R I q))))) := by
  rw [range_firstFactorOverlapChart R I q hI]
  exact (congrArg₂ (· ∪ ·)
      (pr₁ChartSelf_base_preimage_basicOpen R I q (overlapX R I q)).symm
      (pr₁ChartSelf_base_preimage_basicOpen R I q (overlapY R I q)).symm).trans
    (Set.preimage_union
      (f := ⇑(pr₁ChartSelf R I q).base)
      (s := (↑(FormalSpectrum.basicOpen (I.map (algebraMap R (annulusAlgebra R I q)))
              (overlapX R I q)) :
            Set (FormalSpectrum (I.map (algebraMap R (annulusAlgebra R I q))))))
      (t := (↑(FormalSpectrum.basicOpen (I.map (algebraMap R (annulusAlgebra R I q)))
              (overlapY R I q)) :
            Set (FormalSpectrum (I.map (algebraMap R (annulusAlgebra R I q))))))).symm

/-- **Right shape.** `tateSelfProductRightTransition` carries the source triple-overlap region
`f_second ⁻¹' range f_first` into the target region `f_second ⁻¹' range f_both`. This is the range
inclusion `H` for the four-chart cocycle where the source chart transition is the second-factor
swap. Since `range f_both = range f_first ∩ range f_second`, the target region equals the source
region, and the inclusion is exactly that the transition (a morphism over the first projection)
preserves first-factor membership. -/
theorem tateSelfProductRightTransition_image_subset (hI : I.FG) :
    (tateSelfProductRightTransition R I q hI).hom.base ''
        (⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (firstFactorOverlapChart R I q hI).base) ⊆
      ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (bothFactorOverlapChart R I q hI).base := by
  rw [range_bothFactorOverlapChart_eq_inter_first_second R I q hI, Set.preimage_inter,
    Set.preimage_range, Set.inter_univ, firstFactorOverlapChart_range_eq_preimage R I q hI,
    ← Set.preimage_comp]
  apply image_preimage_subset_of_comp_eq
  have h1 : ⇑((tateSelfProductRightTransition R I q hI).hom ≫
        secondFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q).base =
      ⇑(secondFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q).base := by
    rw [rightTransition_comp_firstProj R I q hI]
  simpa only [LocallyRingedSpace.comp_base, TopCat.coe_comp] using h1

end AlgebraicGeometry

end
