import FormalSchemes.TateSelfProductTransition
import FormalSchemes.TateOverlapInversion

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The 𝔾m-inversion overlap transition isomorphisms of the Tate self-fibre-product

This file is the 𝔾m-**inversion** (issue 435c) analogue of `TateSelfProductTransition`. Where the
swap transitions there are built from the coordinate-swap overlap transition
`annulusOverlapTransition` (`X ↦ Y`), the transitions here are built from the honest 𝔾m-inversion
overlap transition `annulusOverlapInversion` (`X ↦ Y⁻¹`, the geometrically-correct Tate 2-gon
gluing). The two families share the same endpoints, so every declaration below is byte-for-byte the
corresponding swap definition with the overlap transition replaced by the inversion one.

Assembled purely additively for issue 442a: it reuses all the chart-domain objects (`dXA`, `dYA`,
…), the summand types and the transition-packaging proofs of the imported swap file.

## Main definitions

* `AlgebraicGeometry.tateSelfProductFirstTransitionInv`: the first-factor inversion overlap
  transition.
* `AlgebraicGeometry.tateSelfProductRightTransitionInv`: the second-factor inversion overlap
  transition.
* `AlgebraicGeometry.tateSelfProductBothTransitionInv`: the both-factors inversion overlap
  transition.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The 𝔾m-inversion chart transitions -/

/-- **The 𝔾m-inversion overlap transition** `A[x⁻¹]^∧ ≃ₐ[R] A[y⁻¹]^∧` as an `R`-algebra
isomorphism: the `R`-algebra upgrade of `annulusOverlapInversion`; `R`-linearity comes from
`annulusOverlapInversion_algebraMap`. The inversion analogue of `annulusOverlapTransitionAlg`. -/
def annulusOverlapInversionAlg (hI : I.FG) : annulusOverlap R I q ≃ₐ[R] annulusOverlapY R I q :=
  AlgEquiv.ofRingEquiv (f := annulusOverlapInversion R I q hI)
    (fun r => annulusOverlapInversion_algebraMap R I q hI r)

/-- **The 𝔾m-inversion `R`-algebra chart transition** `A{1/x} ≃ₐ[R] A{1/y}`: the composite of the
two chart-domain identifications with the inversion overlap transition. The inversion analogue of
`annulusChartTransitionAlg`. -/
def annulusChartTransitionInvAlg (hI : I.FG) :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) ≃ₐ[R]
      awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q) :=
  (annulusChartOverlapAlgX R I q).trans
    ((annulusOverlapInversionAlg R I q hI).trans (annulusChartOverlapAlgY R I q).symm)

/-- **The 𝔾m-inversion `R`-algebra chart transition `A{1/x} ≃ₐ[R] A{1/y}`, over the
`I.map (algebraMap R A)` ideal convention** the interchange immersions use: the composite of the two
ideal-convention bridges with `annulusChartTransitionInvAlg`. The inversion analogue of
`annulusFibreChartTransitionAlg`. -/
def annulusFibreChartTransitionInvAlg (hI : I.FG) :
    awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q) :=
  (annulusFibreChartBridgeX R I q).trans
    ((annulusChartTransitionInvAlg R I q hI).trans (annulusFibreChartBridgeY R I q).symm)

/-- **The base-changed 𝔾m-inversion chart transition of `X ×_{Spf R} Spf B`**:
`Spf(A{1/x} ⊗̂_R B) ≅ Spf(A{1/y} ⊗̂_R B)`, obtained by feeding `annulusFibreChartTransitionInvAlg`
(and `AlgEquiv.refl R B`) to `CompletedTensorProduct.mapSpfIso`. The inversion analogue of
`twoPatchFibreProductTransition`. -/
def twoPatchFibreProductInvTransition (B : Type u) [CommRing B] [Algebra R B] (hI : I.FG) :
    haveI := CompletedTensorProduct.isAdicRing R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) B hI
    haveI := CompletedTensorProduct.isAdicRing R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) B hI
    FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) B) ≅
      FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) B) :=
  CompletedTensorProduct.mapSpfIso hI (annulusFibreChartTransitionInvAlg R I q hI)
    (AlgEquiv.refl (R := R) (A₁ := B))

/-! ### The per-summand 𝔾m-inversion transition isomorphisms -/

/-- The first-factor per-summand inversion transition `Spf(A{1/x} ⊗̂_R A) ≅ Spf(A{1/y} ⊗̂_R A)`: the
base-changed 𝔾m-inversion chart transition with `B := A`. The inversion analogue of
`firstSummand`. -/
abbrev firstSummandInv (hI : I.FG) : dXA R I q ≅ dYA R I q :=
  twoPatchFibreProductInvTransition R I q (A R I q) hI

/-- The second-factor per-summand inversion transition `Spf(A ⊗̂_R A{1/x}) ≅ Spf(A ⊗̂_R A{1/y})`:
`mapSpfIso` of the identity on the fixed first factor and the 𝔾m-inversion chart transition on the
second. The inversion analogue of `rightSummand`. -/
abbrev rightSummandInv (hI : I.FG) : dAX R I q ≅ dAY R I q :=
  mapSpfIso hI (AlgEquiv.refl (R := R) (A₁ := A R I q))
    (annulusFibreChartTransitionInvAlg R I q hI)

/-- The `(x, x) ≅ (y, y)` per-summand inversion transition
`Spf(A{1/x} ⊗̂_R A{1/x}) ≅ Spf(A{1/y} ⊗̂_R A{1/y})`:
`mapSpfIso` of the 𝔾m-inversion chart transition on *both* factors. The inversion analogue of
`bothSummandDiag`. -/
abbrev bothSummandDiagInv (hI : I.FG) : dXX R I q ≅ dYY R I q :=
  mapSpfIso hI (annulusFibreChartTransitionInvAlg R I q hI)
    (annulusFibreChartTransitionInvAlg R I q hI)

/-- The `(x, y) ≅ (y, x)` per-summand inversion transition
`Spf(A{1/x} ⊗̂_R A{1/y}) ≅ Spf(A{1/y} ⊗̂_R A{1/x})`:
`mapSpfIso` of the 𝔾m-inversion chart transition on the first factor and its inverse on the second.
The inversion analogue of `bothSummandAnti`. -/
abbrev bothSummandAntiInv (hI : I.FG) : dXY R I q ≅ dYX R I q :=
  mapSpfIso hI (annulusFibreChartTransitionInvAlg R I q hI)
    (annulusFibreChartTransitionInvAlg R I q hI).symm

/-! ### The 𝔾m-inversion overlap transition isomorphisms -/

/-- **The first-factor 𝔾m-inversion overlap transition.** The summand-swap involution of the
first-factor overlap object `Spf(A{1/x} ⊗̂_R A) ⨿ Spf(A{1/y} ⊗̂_R A)`, sending the `x`-summand to
the `y`-summand through the base-changed 𝔾m-inversion chart transition `firstSummandInv` and back
through its inverse. The inversion analogue of `tateSelfProductFirstTransition`; its own inverse. -/
def tateSelfProductFirstTransitionInv (hI : I.FG) :
    (dXA R I q ⨿ dYA R I q) ≅ (dXA R I q ⨿ dYA R I q) where
  hom := coprod.desc ((firstSummandInv R I q hI).hom ≫ coprod.inr)
    ((firstSummandInv R I q hI).inv ≫ coprod.inl)
  inv := coprod.desc ((firstSummandInv R I q hI).hom ≫ coprod.inr)
    ((firstSummandInv R I q hI).inv ≫ coprod.inl)
  hom_inv_id := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, coprod.inl_desc, Category.assoc, coprod.inr_desc,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, coprod.inr_desc, Category.assoc, coprod.inl_desc,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, coprod.inl_desc, Category.assoc, coprod.inr_desc,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, coprod.inr_desc, Category.assoc, coprod.inl_desc,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]

/-- **The second-factor 𝔾m-inversion overlap transition.** The summand-swap involution of the
second-factor overlap object `Spf(A ⊗̂_R A{1/x}) ⨿ Spf(A ⊗̂_R A{1/y})`, sending the `x`-summand to
the `y`-summand through `rightSummandInv` and back. The inversion analogue of
`tateSelfProductRightTransition`; its own inverse. -/
def tateSelfProductRightTransitionInv (hI : I.FG) :
    (dAX R I q ⨿ dAY R I q) ≅ (dAX R I q ⨿ dAY R I q) where
  hom := coprod.desc ((rightSummandInv R I q hI).hom ≫ coprod.inr)
    ((rightSummandInv R I q hI).inv ≫ coprod.inl)
  inv := coprod.desc ((rightSummandInv R I q hI).hom ≫ coprod.inr)
    ((rightSummandInv R I q hI).inv ≫ coprod.inl)
  hom_inv_id := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, coprod.inl_desc, Category.assoc, coprod.inr_desc,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, coprod.inr_desc, Category.assoc, coprod.inl_desc,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, coprod.inl_desc, Category.assoc, coprod.inr_desc,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, coprod.inr_desc, Category.assoc, coprod.inl_desc,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]

/-- **The both-factors 𝔾m-inversion overlap transition.** The four-summand permuting involution of
the both-factors overlap object
`(Spf(A{1/x} ⊗̂ A{1/x}) ⨿ Spf(A{1/x} ⊗̂ A{1/y})) ⨿ (Spf(A{1/y} ⊗̂ A{1/x}) ⨿ Spf(A{1/y} ⊗̂ A{1/y}))`,
realising the coordinate 𝔾m-inversion `(a, b) ↦ (inv a, inv b)`: it sends `(x, x) ↦ (y, y)` and
`(x, y) ↦ (y, x)` through `bothSummandDiagInv`/`bothSummandAntiInv`, and back via their inverses.
The inversion analogue of `tateSelfProductBothTransition`; its own inverse. -/
def tateSelfProductBothTransitionInv (hI : I.FG) :
    ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ≅
      ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) where
  hom := coprod.desc
    (coprod.desc ((bothSummandDiagInv R I q hI).hom ≫ coprod.inr ≫ coprod.inr)
      ((bothSummandAntiInv R I q hI).hom ≫ coprod.inl ≫ coprod.inr))
    (coprod.desc ((bothSummandAntiInv R I q hI).inv ≫ coprod.inr ≫ coprod.inl)
      ((bothSummandDiagInv R I q hI).inv ≫ coprod.inl ≫ coprod.inl))
  inv := coprod.desc
    (coprod.desc ((bothSummandDiagInv R I q hI).hom ≫ coprod.inr ≫ coprod.inr)
      ((bothSummandAntiInv R I q hI).hom ≫ coprod.inl ≫ coprod.inr))
    (coprod.desc ((bothSummandAntiInv R I q hI).inv ≫ coprod.inr ≫ coprod.inl)
      ((bothSummandDiagInv R I q hI).inv ≫ coprod.inl ≫ coprod.inl))
  hom_inv_id := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Category.comp_id]
  inv_hom_id := by
    refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_) <;>
      simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc,
        coprod.inr_desc_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Category.comp_id]

end AlgebraicGeometry
