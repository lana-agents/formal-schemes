import FormalSchemes.CompletedTensorMapSpf

set_option linter.style.header false

/-!
# The fibre-product map of algebra isomorphisms is an isomorphism of formal spectra

`FormalSchemes.CompletedTensorMapSpf` lifts the ring-level functoriality of the completed tensor
product to the geometric functor laws `CompletedTensorProduct.mapSpf_id` /
`CompletedTensorProduct.mapSpf_comp` for the fibre-product map
`mapSpf hI f g : Spf (A' ⊗̂_R B') ⟶ Spf (A ⊗̂_R B)`.

This file records the immediate consequence of those two laws: when the two `R`-algebra maps are
*isomorphisms* `e₁ : A ≃ₐ[R] A'`, `e₂ : B ≃ₐ[R] B'`, the induced map of formal spectra is an
**isomorphism**

`mapSpfIso hI e₁ e₂ : Spf (A ⊗̂_R B) ≅ Spf (A' ⊗̂_R B')`,

with the two directions `mapSpf` of `(e₁.symm, e₂.symm)` and `(e₁, e₂)`, mutually inverse by the
composition law (each composite is `mapSpf` of `(e₁.symm ∘ e₁, …)` resp. `(e₁ ∘ e₁.symm, …)`, i.e.
`mapSpf` of the identity pair, which is `𝟙` by the identity law).

This is exactly the **transition-map datum** the *glued* fibre-product constructions consume: when a
general fibre product `X ×_S Y`, or the Tate self-product `𝔈_q ×_{Spf R} 𝔈_q`, is glued from the
affine charts `Spf (A_i ⊗̂_R B_j)`, the double-overlap transition isomorphisms `t` of the glue datum
are `mapSpfIso` of the chart-transition isomorphisms, and the self-inverse condition
`t i j ≫ t j i = 𝟙` is precisely `mapSpfIso.hom_inv_id` / `mapSpfIso.inv_hom_id` below.

## Main definitions

* `CompletedTensorProduct.mapSpfIso`: the isomorphism `Spf (A ⊗̂_R B) ≅ Spf (A' ⊗̂_R B')` induced
  by a pair of `R`-algebra isomorphisms, with `@[simp]` unfolding lemmas
  `mapSpfIso_hom` / `mapSpfIso_inv` for its two legs.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.2, §10.7.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A B A' B' : Type u}
variable [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [CommRing A'] [CommRing B'] [Algebra R A'] [Algebra R B']

/-- **The fibre-product map of a pair of `R`-algebra isomorphisms is an isomorphism of formal
spectra** `Spf (A ⊗̂_R B) ≅ Spf (A' ⊗̂_R B')`. The forward leg is `mapSpf` of `(e₁.symm, e₂.symm)`
and the backward leg is `mapSpf` of `(e₁, e₂)`; they are mutually inverse by the geometric
composition law `mapSpf_comp` (collapsing each composite to `mapSpf` of the identity pair) and the
identity law `mapSpf_id`. -/
def mapSpfIso (hI : I.FG) (e₁ : A ≃ₐ[R] A') (e₂ : B ≃ₐ[R] B') :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B' hI
    FormalSpectrum.locallyRingedSpaceObj (idealOfDefinition R I A B) ≅
      FormalSpectrum.locallyRingedSpaceObj (idealOfDefinition R I A' B') :=
  haveI := isAdicRing R I A B hI
  haveI := isAdicRing R I A' B' hI
  have h₁ : e₁.symm.toAlgHom.comp e₁.toAlgHom = AlgHom.id R A :=
    AlgHom.ext e₁.symm_apply_apply
  have h₂ : e₂.symm.toAlgHom.comp e₂.toAlgHom = AlgHom.id R B :=
    AlgHom.ext e₂.symm_apply_apply
  have h₁' : e₁.toAlgHom.comp e₁.symm.toAlgHom = AlgHom.id R A' :=
    AlgHom.ext e₁.apply_symm_apply
  have h₂' : e₂.toAlgHom.comp e₂.symm.toAlgHom = AlgHom.id R B' :=
    AlgHom.ext e₂.apply_symm_apply
  { hom := mapSpf hI e₁.symm.toAlgHom e₂.symm.toAlgHom
    inv := mapSpf hI e₁.toAlgHom e₂.toAlgHom
    hom_inv_id := by
      rw [← mapSpf_comp hI e₁.toAlgHom e₂.toAlgHom e₁.symm.toAlgHom e₂.symm.toAlgHom, h₁, h₂,
        mapSpf_id]
    inv_hom_id := by
      rw [← mapSpf_comp hI e₁.symm.toAlgHom e₂.symm.toAlgHom e₁.toAlgHom e₂.toAlgHom, h₁', h₂',
        mapSpf_id] }

@[simp]
theorem mapSpfIso_hom (hI : I.FG) (e₁ : A ≃ₐ[R] A') (e₂ : B ≃ₐ[R] B') :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B' hI
    (mapSpfIso hI e₁ e₂).hom = mapSpf hI e₁.symm.toAlgHom e₂.symm.toAlgHom :=
  rfl

@[simp]
theorem mapSpfIso_inv (hI : I.FG) (e₁ : A ≃ₐ[R] A') (e₂ : B ≃ₐ[R] B') :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B' hI
    (mapSpfIso hI e₁ e₂).inv = mapSpf hI e₁.toAlgHom e₂.toAlgHom :=
  rfl

end CompletedTensorProduct
