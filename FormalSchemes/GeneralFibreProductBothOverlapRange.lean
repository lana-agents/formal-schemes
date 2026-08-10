import FormalSchemes.GeneralFibreProductBothAlgebraDataObject

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Range of the dispatched product-overlap immersion of `X ×_{Spf R} Y`

For the two-sided fibre product `X ×_{Spf R} Y` built from algebra data, the overlap chart of two
distinct product-index charts `p = (i, j)`, `p' = (i', j')` is the coordinate-difference-dispatched
open immersion `bothAlgDataF hI gX gY p p' h : bothAlgDataV … ⟶ Spf(A_i ⊗̂_R B_j)`
(`GeneralFibreProductBothAlgebraDataObject`). This file computes its underlying-space **range** as
an intersection of localization basic opens:

* when the first coordinate agrees (`i = i'`) the `X`-factor is unconstrained (`Set.univ`);
  otherwise it is `D(inl (gX i i'))`, the basic open of the first-factor localization element;
* symmetrically for the second coordinate and `D(inr (gY j j'))`.

This is the pure range computation extracted from issue 426; the geometric assembly
`range_ι_eq_pr_preimage_inter` (product chart = preimage intersection of the two projections,
issue 426b) consumes it.

## Main results

* `AlgebraicGeometry.range_bothAlgDataF_base`: the range formula above.
* `AlgebraicGeometry.range_eqToHom_comp_base`: precomposition with `eqToHom` preserves the range of
  the underlying base map (a small helper).

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

/-- Precomposition with an `eqToHom` does not change the range of the underlying base map: the
`eqToHom` is an isomorphism, so its base map is a bijection. -/
theorem range_eqToHom_comp_base {X Y Z : LocallyRingedSpace.{u}} (pf : X = Y) (h : Y ⟶ Z) :
    Set.range ⇑(eqToHom pf ≫ h).base = Set.range ⇑h.base := by
  subst pf
  rw [eqToHom_refl, Category.id_comp]

/-- **The underlying-space range of the dispatched product-overlap immersion.** For distinct
product-index charts `p`, `p'` of `X ×_{Spf R} Y`, the range of the overlap immersion
`bothAlgDataF hI gX gY p p' h` in the chart `Spf(A_{p.1} ⊗̂_R B_{p.2})` is the intersection of the
first-factor localization basic open `D(inl (gX p.1 p'.1))` (unconstrained when `p.1 = p'.1`) and
the second-factor localization basic open `D(inr (gY p.2 p'.2))` (unconstrained when `p.2 = p'.2`).
-/
theorem range_bothAlgDataF_base (hI : I.FG) (gX : ∀ i _ : JX, A i) (gY : ∀ j _ : JY, B j)
    (p p' : JX × JY) (h : p ≠ p') :
    Set.range ⇑(bothAlgDataF hI gX gY p p' h).base =
      (if p.1 = p'.1 then Set.univ
        else (↑(basicOpen (idealOfDefinition R I (A p.1) (B p.2))
          (inl R I (A p.1) (B p.2) (gX p.1 p'.1))) :
            Set (FormalSpectrum (idealOfDefinition R I (A p.1) (B p.2))))) ∩
      (if p.2 = p'.2 then Set.univ
        else (↑(basicOpen (idealOfDefinition R I (A p.1) (B p.2))
          (inr R I (A p.1) (B p.2) (gY p.2 p'.2))) :
            Set (FormalSpectrum (idealOfDefinition R I (A p.1) (B p.2))))) := by
  unfold bothAlgDataF
  by_cases h1 : p.1 = p'.1
  · rw [dif_pos h1, if_pos h1, Set.univ_inter]
    by_cases h2 : p.2 = p'.2
    · exact absurd (Prod.ext h1 h2) h
    · rw [if_neg h2, range_eqToHom_comp_base, range_rightInterchangeOpenImmersion_base]
  · rw [dif_neg h1, if_neg h1]
    by_cases h2 : p.2 = p'.2
    · rw [dif_pos h2, if_pos h2, Set.inter_univ, range_eqToHom_comp_base,
        range_interchangeOpenImmersion_base]
    · rw [dif_neg h2, if_neg h2, range_eqToHom_comp_base,
        range_bothInterchangeOpenImmersion_base, TopologicalSpace.Opens.coe_inf]

end AlgebraicGeometry

end
