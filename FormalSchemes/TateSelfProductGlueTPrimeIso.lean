import FormalSchemes.TateSelfProductGlueTPrime

set_option linter.style.header false
-- The completed-tensor interchange charts range over the nested localization/completion towers of
-- the completed tensor product, which are slow for the elaborator and the kernel; raise the budgets
-- (matching `TateSelfProductGlueTPrime.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# `tateSelfProductGlueT'` is an isomorphism (the cocycle input for brick c3)

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. Brick c2 (`TateSelfProductGlueTPrime.lean`, issue 301) built the
transition-of-transitions `tateSelfProductGlueT'` of the four-chart `Bool × Bool` Tate self-product
glue via the lift mechanism `glueTPrimeOfLift`, discharging the range **inclusion** `H`. The cocycle
brick c3 (issue 302) needs each `t'` to be an **isomorphism**; by `isIso_glueTPrimeOfLift`
(`GlueTPrimeOfLift.lean`) that requires the range inclusion to be an **equality**.

This file upgrades the three shape range-tracking lemmas (`TateSelfProductTransitionRange`,
`...Right`, and the swapped variants in `TateSelfProductGlueTPrime`) from `⊆` to `=`, assembles the
reduced range **equality** for every pairwise-distinct triple, and concludes
`isIso_tateSelfProductGlueT'`.

## The equality upgrade

Each shape range-tracking obligation has the form `t '' (g ⁻¹' W) ⊆ g ⁻¹' W` for the transition
base map `t` and a projection-saturated region `g ⁻¹' W` (with `g ∘ t = g`, the transition being a
morphism over the relevant projection). The reverse inclusion is automatic once `t` is surjective:
`g ∘ t = g` and surjectivity of `t` give `g ⁻¹' W ⊆ t '' (g ⁻¹' W)`
(`image_preimage_eq_of_comp_eq`). The transition base maps are surjective because they are the `hom`
legs of isomorphisms (`bijective_hom_base`). For the both-source shape both regions are `Set.univ`,
and `t '' univ = univ` is exactly surjectivity.

## Main results

* `AlgebraicGeometry.tateSelfProductGlueT'_range_eq`: the range **equality** `H` per triple.
* `AlgebraicGeometry.isIso_tateSelfProductGlueT'`: each `t'` is an isomorphism.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* Mathlib `CategoryTheory.GlueData'` (the `cocycle` field consumes iso `t'`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### Generic upgrades from `⊆` to `=` -/

/-- The `hom` base map of a locally-ringed-space isomorphism is bijective: its two-sided inverse is
the `Iso.inv` base map (the two `iso_..._base_..._base_apply` lemmas). -/
theorem bijective_hom_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) :
    Function.Bijective ⇑e.hom.base :=
  Function.bijective_iff_has_inverse.mpr
    ⟨⇑e.inv.base, LocallyRingedSpace.iso_hom_base_inv_base_apply e,
      LocallyRingedSpace.iso_inv_base_hom_base_apply e⟩

/-- **Equality upgrade of `image_preimage_subset_of_comp_eq`.** If a *surjective* self-map `h`
commutes with `g` over the target (`g ∘ h = g`), then `h` maps every `g`-saturated region onto
itself: `h '' (g ⁻¹' W) = g ⁻¹' W`. The `⊆` half is `image_preimage_subset_of_comp_eq`; the reverse
uses surjectivity to lift each point of the region back through `h`, `g ∘ h = g` keeping it in the
region. -/
theorem image_preimage_eq_of_comp_eq {α β : Type*} {h : α → α} {g : α → β} {W : Set β}
    (hsurj : Function.Surjective h) (hg : g ∘ h = g) : h '' (g ⁻¹' W) = g ⁻¹' W := by
  refine Set.Subset.antisymm (image_preimage_subset_of_comp_eq hg) fun y hy => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨x, by rw [Set.mem_preimage, ← congrFun hg x]; exact hy, rfl⟩

/-! ### The three shape equalities (and their two swapped variants) -/

/-- **First shape, equality.** The `⊆` version `tateSelfProductFirstTransition_image_subset`
upgraded to `=` via surjectivity of the transition base map. -/
theorem tateSelfProductFirstTransition_image_eq (hI : I.FG) :
    (tateSelfProductFirstTransition R I q hI).hom.base ''
        (⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (secondFactorOverlapChart R I q hI).base) =
      ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (bothFactorOverlapChart R I q hI).base := by
  rw [range_bothFactorOverlapChart_eq_inter_first_second R I q hI, Set.preimage_inter,
    Set.preimage_range, Set.univ_inter, secondFactorOverlapChart_range_eq_preimage R I q hI,
    ← Set.preimage_comp]
  refine image_preimage_eq_of_comp_eq
    (bijective_hom_base (tateSelfProductFirstTransition R I q hI)).surjective ?_
  have h1 : ⇑((tateSelfProductFirstTransition R I q hI).hom ≫
        firstFactorOverlapChart R I q hI ≫
          pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q)).base =
      ⇑(firstFactorOverlapChart R I q hI ≫
        pr₂Chart R I (annulusAlgebra R I q) (annulusAlgebra R I q)).base := by
    rw [firstTransition_comp_secondProj R I q hI]
  simpa only [LocallyRingedSpace.comp_base, TopCat.coe_comp] using h1

/-- **Right shape, equality.** The `⊆` version `tateSelfProductRightTransition_image_subset`
upgraded to `=`. -/
theorem tateSelfProductRightTransition_image_eq (hI : I.FG) :
    (tateSelfProductRightTransition R I q hI).hom.base ''
        (⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (firstFactorOverlapChart R I q hI).base) =
      ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (bothFactorOverlapChart R I q hI).base := by
  rw [range_bothFactorOverlapChart_eq_inter_first_second R I q hI, Set.preimage_inter,
    Set.preimage_range, Set.inter_univ, firstFactorOverlapChart_range_eq_preimage R I q hI,
    ← Set.preimage_comp]
  refine image_preimage_eq_of_comp_eq
    (bijective_hom_base (tateSelfProductRightTransition R I q hI)).surjective ?_
  have h1 : ⇑((tateSelfProductRightTransition R I q hI).hom ≫
        secondFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q).base =
      ⇑(secondFactorOverlapChart R I q hI ≫ pr₁ChartSelf R I q).base := by
    rw [rightTransition_comp_firstProj R I q hI]
  simpa only [LocallyRingedSpace.comp_base, TopCat.coe_comp] using h1

/-- **Both shape, equality.** Both regions are `Set.univ` (the both-overlap range sits inside each
single-factor range), and `t_both '' univ = univ` is surjectivity of the transition base map. -/
theorem tateSelfProductBothTransition_image_eq (hI : I.FG) :
    (tateSelfProductBothTransition R I q hI).hom.base ''
        (⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (firstFactorOverlapChart R I q hI).base) =
      ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (secondFactorOverlapChart R I q hI).base := by
  have hs : ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
      Set.range (firstFactorOverlapChart R I q hI).base = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    exact fun y => range_bothFactorOverlapChart_subset_first R I q hI (Set.mem_range_self y)
  have ht : ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
      Set.range (secondFactorOverlapChart R I q hI).base = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    exact fun y => range_bothFactorOverlapChart_subset_second R I q hI (Set.mem_range_self y)
  rw [hs, ht, Set.image_univ, Set.range_eq_univ]
  exact (bijective_hom_base (tateSelfProductBothTransition R I q hI)).surjective

/-- **First shape, swapped ordering, equality.** Cf. `tateSelfProductFirstTransition_image_subset'`;
both regions equal `f_first ⁻¹' range f_second`, so this is the base first-shape equality with the
`range f_both` region rewritten. -/
theorem tateSelfProductFirstTransition_image_eq' (hI : I.FG) :
    (tateSelfProductFirstTransition R I q hI).hom.base ''
        (⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (bothFactorOverlapChart R I q hI).base) =
      ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (secondFactorOverlapChart R I q hI).base := by
  have hset : ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (bothFactorOverlapChart R I q hI).base =
      ⇑(firstFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (secondFactorOverlapChart R I q hI).base := by
    rw [range_bothFactorOverlapChart_eq_inter_first_second R I q hI, Set.preimage_inter,
      Set.preimage_range, Set.univ_inter]
  rw [hset, tateSelfProductFirstTransition_image_eq R I q hI]
  exact hset

/-- **Right shape, swapped ordering, equality.** Cf. `tateSelfProductRightTransition_image_subset'`.
-/
theorem tateSelfProductRightTransition_image_eq' (hI : I.FG) :
    (tateSelfProductRightTransition R I q hI).hom.base ''
        (⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (bothFactorOverlapChart R I q hI).base) =
      ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (firstFactorOverlapChart R I q hI).base := by
  have hset : ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (bothFactorOverlapChart R I q hI).base =
      ⇑(secondFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (firstFactorOverlapChart R I q hI).base := by
    rw [range_bothFactorOverlapChart_eq_inter_first_second R I q hI, Set.preimage_inter,
      Set.preimage_range, Set.inter_univ]
  rw [hset, tateSelfProductRightTransition_image_eq R I q hI]
  exact hset

/-- **Both shape, swapped ordering, equality.** Both regions are `Set.univ`; cf.
`tateSelfProductBothTransition_image_subset'`. -/
theorem tateSelfProductBothTransition_image_eq' (hI : I.FG) :
    (tateSelfProductBothTransition R I q hI).hom.base ''
        (⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
          Set.range (secondFactorOverlapChart R I q hI).base) =
      ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
        Set.range (firstFactorOverlapChart R I q hI).base := by
  have hs : ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
      Set.range (secondFactorOverlapChart R I q hI).base = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    exact fun y => range_bothFactorOverlapChart_subset_second R I q hI (Set.mem_range_self y)
  have ht : ⇑(bothFactorOverlapChart R I q hI).base ⁻¹'
      Set.range (firstFactorOverlapChart R I q hI).base = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    exact fun y => range_bothFactorOverlapChart_subset_first R I q hI (Set.mem_range_self y)
  rw [hs, ht, Set.image_univ, Set.range_eq_univ]
  exact (bijective_hom_base (tateSelfProductBothTransition R I q hI)).surjective

/-! ### The reduced range equality, and the pullback-form `H` as an equality -/

/-- **The reduced range equality** for every pairwise-distinct triple: the transition `t i j` maps
the source triple-overlap region `(f i j) ⁻¹' range (f i k)` *onto* the target region
`(f j i) ⁻¹' range (f j k)`. Same single `Bool × Bool` case split as
`tateSelfProductGlueT'_range_reduced`, dispatching onto the six shape *equalities* above. -/
theorem tateSelfProductGlueT'_range_reduced_eq (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (tateSelfProductGlueT R I q hI i j hij).base ''
        (⇑(tateSelfProductGlueF R I q hI i j hij).base ⁻¹'
          Set.range (tateSelfProductGlueF R I q hI i k hik).base) =
      ⇑(tateSelfProductGlueF R I q hI j i hij.symm).base ⁻¹'
        Set.range (tateSelfProductGlueF R I q hI j k hjk).base := by
  revert hij hik hjk
  rcases i with ⟨(_ | _), (_ | _)⟩ <;> rcases j with ⟨(_ | _), (_ | _)⟩ <;>
    rcases k with ⟨(_ | _), (_ | _)⟩ <;> intro hij hik hjk <;>
    first
      | exact absurd rfl hij
      | exact absurd rfl hik
      | exact absurd rfl hjk
      | (simp only [tateSelfProductGlueF, tateSelfProductGlueT]
         first
           | exact tateSelfProductFirstTransition_image_eq R I q hI
           | exact tateSelfProductRightTransition_image_eq R I q hI
           | exact tateSelfProductBothTransition_image_eq R I q hI
           | exact tateSelfProductFirstTransition_image_eq' R I q hI
           | exact tateSelfProductRightTransition_image_eq' R I q hI
           | exact tateSelfProductBothTransition_image_eq' R I q hI)

/-- **The range inclusion `H` as an equality**, in the `pullback` form `isIso_glueTPrimeOfLift`
consumes. Same leg cancellation as `tateSelfProductGlueT'_range`, now an equality. -/
theorem tateSelfProductGlueT'_range_eq (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)] :
    Set.range (pullback.fst (tateSelfProductGlueF R I q hI i j hij)
          (tateSelfProductGlueF R I q hI i k hik) ≫
        tateSelfProductGlueT R I q hI i j hij).base =
      Set.range (pullback.snd (tateSelfProductGlueF R I q hI j k hjk)
        (tateSelfProductGlueF R I q hI j i hij.symm)).base := by
  rw [LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp,
    range_pullback_fst, range_pullback_snd]
  exact tateSelfProductGlueT'_range_reduced_eq R I q hI i j k hij hik hjk

/-! ### `IsIso` of the transitions and of `t'` -/

/-- Each transition `tateSelfProductGlueT i j` is an isomorphism: it is the `hom` leg of one of the
three named transition isos (`Iso.isIso_hom`). -/
theorem isIso_tateSelfProductGlueT (hI : I.FG) (i j : Bool × Bool) (hij : i ≠ j) :
    IsIso (tateSelfProductGlueT R I q hI i j hij) := by
  revert hij
  rcases i with ⟨(_ | _), (_ | _)⟩ <;> rcases j with ⟨(_ | _), (_ | _)⟩ <;> intro hij <;>
    first
      | exact absurd rfl hij
      | (simp only [tateSelfProductGlueT]; infer_instance)

/-- **`tateSelfProductGlueT'` is an isomorphism.** Fed the range **equality**
`tateSelfProductGlueT'_range_eq` (plus `IsIso (t i j)` and `IsOpenImmersion (f i k)`) into
`isIso_glueTPrimeOfLift`. This is the input the `GlueData'.cocycle` of brick c3 (issue 302)
consumes. Takes the chart open-immersion instances as arguments (as `tateSelfProductGlueT'` does),
supplied at the `GlueData'` assembly by `f_hasPullback` / `f_open`. -/
theorem isIso_tateSelfProductGlueT' (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)] :
    IsIso (tateSelfProductGlueT' R I q hI i j k hij hik hjk) := by
  haveI := isIso_tateSelfProductGlueT R I q hI i j hij
  exact isIso_glueTPrimeOfLift _ _ _ _ _
    (tateSelfProductGlueT'_range R I q hI i j k hij hik hjk)
    (tateSelfProductGlueT'_range_eq R I q hI i j k hij hik hjk)

end AlgebraicGeometry

end
