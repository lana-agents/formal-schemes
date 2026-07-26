import FormalSchemes.CompletedTensorFunctor
import FormalSchemes.SpfFunctorial

set_option linter.style.header false

/-!
# Functor laws for the geometric fibre-product map `mapSpf`

`FormalSchemes.CompletedTensorFunctor` records the *ring-level* functoriality of the completed
tensor product (`CompletedTensorProduct.map_id`, `CompletedTensorProduct.map_comp`) and packages
the induced morphism of affine formal spectra
`CompletedTensorProduct.mapSpf hI f g : Spf (A' ⊗̂_R B') ⟶ Spf (A ⊗̂_R B)`.

This file lifts the two functor laws to the *geometric* level:

* `CompletedTensorProduct.mapSpf_id`: `mapSpf` of the pair of identity `R`-algebra maps is the
  identity morphism of formal spectra.
* `CompletedTensorProduct.mapSpf_comp`: `mapSpf` of a pair of composites is the composite
  (contravariantly) of the two `mapSpf`'s.

Together these say that `Spf (- ⊗̂_R -)` is a (contravariant, in each argument) functor on affine
formal schemes. They are the transition-map cocycle inputs the *glued* fibre-product constructions
consume: when a general fibre product `X ×_S Y` (or the Tate self-product `𝔈_q ×_{Spf R} 𝔈_q`) is
glued from the affine charts `Spf (A_i ⊗̂_R B_j)`, the double-overlap transition isomorphisms are
`mapSpf` of the chart-transition isomorphisms, and the glue-datum conditions
`t i j ≫ t j i = 𝟙` / the triple cocycle reduce, via these laws, to the corresponding identities
of the chart transitions.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.2, §10.7.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A B A' B' A'' B'' : Type u}
variable [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [CommRing A'] [CommRing B'] [Algebra R A'] [Algebra R B']
variable [CommRing A''] [CommRing B''] [Algebra R A''] [Algebra R B'']

/-- Auxiliary: `FormalSpectrum.locallyRingedSpaceMap` depends only on the underlying ring
homomorphism, not on the (propositional) continuity witness — two witnesses for equal ring
homomorphisms give the same morphism of locally ringed spaces. -/
private theorem locallyRingedSpaceMap_congr {P Q : Type u} [CommRing P] [CommRing Q]
    [TopologicalSpace P] [TopologicalSpace Q] {I₀ : Ideal P} {J₀ : Ideal Q}
    [IsAdicRing I₀] [IsAdicRing J₀] {φ ψ : P →+* Q}
    (hφ : I₀ ≤ J₀.comap φ) (hψ : I₀ ≤ J₀.comap ψ) (h : φ = ψ) :
    FormalSpectrum.locallyRingedSpaceMap I₀ J₀ φ hφ =
      FormalSpectrum.locallyRingedSpaceMap I₀ J₀ ψ hψ := by
  subst h
  rfl

/-- Unfolding lemma: `mapSpf` is the morphism of locally ringed spaces induced by the ring-level
functorial map `map`, with continuity witness `(map_isAdicHom …).le_comap`. -/
theorem mapSpf_eq (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B' hI
    mapSpf hI f g = FormalSpectrum.locallyRingedSpaceMap (idealOfDefinition R I A B)
      (idealOfDefinition R I A' B') (map hI f g) (map_isAdicHom hI f g).le_comap :=
  rfl

/-- **Geometric functoriality (identity law).** The induced morphism of formal spectra of the pair
of identity `R`-algebra maps is the identity morphism of `Spf (A ⊗̂_R B)`. -/
theorem mapSpf_id (hI : I.FG) :
    haveI := isAdicRing R I A B hI
    mapSpf hI (AlgHom.id R A) (AlgHom.id R B) = 𝟙 _ := by
  haveI := isAdicRing R I A B hI
  refine Eq.trans ?_ (FormalSpectrum.locallyRingedSpaceMap_id (idealOfDefinition R I A B))
  exact locallyRingedSpaceMap_congr _ _ (map_id (A := A) (B := B) hI)

/-- **Geometric functoriality (composition law).** The induced morphism of formal spectra of a
pair of composites is the composite (contravariantly) of the induced morphisms. -/
theorem mapSpf_comp (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') (f' : A' →ₐ[R] A'')
    (g' : B' →ₐ[R] B'') :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B' hI
    haveI := isAdicRing R I A'' B'' hI
    mapSpf hI (f'.comp f) (g'.comp g) = mapSpf hI f' g' ≫ mapSpf hI f g := by
  haveI := isAdicRing R I A B hI
  haveI := isAdicRing R I A' B' hI
  haveI := isAdicRing R I A'' B'' hI
  rw [mapSpf_eq, mapSpf_eq, mapSpf_eq]
  refine (locallyRingedSpaceMap_congr _
    (((map_isAdicHom hI f g).comp (map_isAdicHom hI f' g')).le_comap)
    (map_comp hI f g f' g')).trans ?_
  exact FormalSpectrum.locallyRingedSpaceMap_comp
    (idealOfDefinition R I A B) (idealOfDefinition R I A' B') (idealOfDefinition R I A'' B'')
    (map hI f g) (map hI f' g')
    (map_isAdicHom hI f g).le_comap (map_isAdicHom hI f' g').le_comap
    ((map_isAdicHom hI f g).comp (map_isAdicHom hI f' g')).le_comap

end CompletedTensorProduct
