import FormalSchemes.CompletedTensor
import FormalSchemes.AdicMorphism

set_option linter.style.header false

/-!
# Functoriality of the completed tensor product and base change of adic morphisms

The completed tensor product `A ⊗̂_R B` (`FormalSchemes.CompletedTensor`) is the coordinate ring
of the fibre product `Spf A ×_{Spf R} Spf B`. This file records that the functorial map
`CompletedTensorProduct.map` — a pair of `R`-algebra homomorphisms `f : A →ₐ[R] A'`,
`g : B →ₐ[R] B'` inducing `A ⊗̂_R B →+* A' ⊗̂_R B'` — is a genuine functor and is an **adic
morphism** in the sense of `FormalSchemes.AdicMorphism`. The consequence is the stability of
adic morphisms under base change (EGA I, 10.12), the piece of the fibre-product/relative theory
that the completed tensor product exists to provide.

## Main results

* `CompletedTensorProduct.map_id`, `CompletedTensorProduct.map_comp`: the functor laws, so
  `A ⊗̂_R (-)` (and `(-) ⊗̂_R B`) is a functor on adic `R`-algebras.
* `CompletedTensorProduct.map_comp_algebraMap`: the functorial map is an `R`-algebra
  homomorphism (it commutes with the structure maps).
* `CompletedTensorProduct.map_isAdicHom`: the functorial map carries the ideal of definition
  onto the ideal of definition of the target — i.e. it is an `IsAdicHom`. Its geometric
  incarnation `CompletedTensorProduct.mapSpf` is the induced morphism of formal spectra.
* `CompletedTensorProduct.baseChange_isAdicHom`: **base change of an adic morphism is adic**
  (EGA I 10.12): given `φ : B →ₐ[R] A` (a morphism `Spf A ⟶ Spf B` over `Spf R`), its base
  change `id_S ⊗̂ φ : S ⊗̂_R B →+* S ⊗̂_R A` along `Spf S ⟶ Spf R` is adic.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.12.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open Ideal AlgebraicGeometry

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A B A' B' A'' B'' : Type u}
variable [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [CommRing A'] [CommRing B'] [Algebra R A'] [Algebra R B']
variable [CommRing A''] [CommRing B''] [Algebra R A''] [Algebra R B'']

/-- **Functoriality (identity law)**: the completed-tensor map of the two identity maps is the
identity homomorphism. -/
theorem map_id (hI : I.FG) :
    map hI (AlgHom.id R A) (AlgHom.id R B) = RingHom.id (CompletedTensorProduct R I A B) := by
  haveI : IsAdicComplete (idealOfDefinition R I A B) (CompletedTensorProduct R I A B) :=
    (isAdicRing R I A B hI).toIsAdicComplete
  refine hom_ext (idealOfDefinition R I A B) hI
    (fun m x hx => map_mem_pow hI _ _ m hx) (fun _ _ hx => hx) (fun a => by simp) (fun b => by simp)

/-- **Functoriality (composition law)**: the completed-tensor map of a pair of composites is the
composite of the completed-tensor maps. -/
theorem map_comp (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') (f' : A' →ₐ[R] A'')
    (g' : B' →ₐ[R] B'') :
    map hI (f'.comp f) (g'.comp g) = (map hI f' g').comp (map hI f g) := by
  haveI : IsAdicComplete (idealOfDefinition R I A'' B'') (CompletedTensorProduct R I A'' B'') :=
    (isAdicRing R I A'' B'' hI).toIsAdicComplete
  refine hom_ext (idealOfDefinition R I A'' B'') hI
    (fun m x hx => map_mem_pow hI _ _ m hx)
    (fun m x hx => map_mem_pow hI f' g' m (map_mem_pow hI f g m hx))
    (fun a => by simp) (fun b => by simp)

/-- The functorial map is an `R`-algebra homomorphism: it commutes with the structure maps
`algebraMap R (A ⊗̂_R B)` and `algebraMap R (A' ⊗̂_R B')`. -/
theorem map_comp_algebraMap (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') :
    (map hI f g).comp (algebraMap R (CompletedTensorProduct R I A B)) =
      algebraMap R (CompletedTensorProduct R I A' B') := by
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, ← (inl R I A B).commutes r, map_inl, f.commutes r,
    (inl R I A' B').commutes r]

/-- **The functorial map is an adic morphism** (EGA I 10.12): it carries the ideal of definition
of `A ⊗̂_R B` onto the ideal of definition of `A' ⊗̂_R B'`. -/
theorem map_isAdicHom (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') :
    IsAdicHom (idealOfDefinition R I A B) (idealOfDefinition R I A' B') (map hI f g) := by
  have : Ideal.map (map hI f g) (idealOfDefinition R I A B) = idealOfDefinition R I A' B' := by
    rw [idealOfDefinition_eq_map (A := A) (B := B), Ideal.map_map, map_comp_algebraMap,
      idealOfDefinition_eq_map (A := A') (B := B')]
  exact this

/-- The morphism of formal spectra `Spf (A' ⊗̂_R B') ⟶ Spf (A ⊗̂_R B)` induced by a pair of
`R`-algebra homomorphisms — the functoriality of the fibre product on affine formal schemes. -/
def mapSpf (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B' hI
    FormalSpectrum.locallyRingedSpaceObj (idealOfDefinition R I A' B') ⟶
      FormalSpectrum.locallyRingedSpaceObj (idealOfDefinition R I A B) :=
  haveI := isAdicRing R I A B hI
  haveI := isAdicRing R I A' B' hI
  (map_isAdicHom hI f g).spfMap

/-!
### Base change

Fixing the first factor to be a base-change base `S` and letting `φ : B →ₐ[R] A` present a
morphism `Spf A ⟶ Spf B` over `Spf R`, the completed-tensor functoriality specialises to base
change along `Spf S ⟶ Spf R`.
-/

variable {S : Type u} [CommRing S] [Algebra R S]

/-- **Base change of an adic morphism is adic** (EGA I 10.12). Given `φ : B →ₐ[R] A` — a
morphism `Spf A ⟶ Spf B` over `Spf R` — its base change along any `Spf S ⟶ Spf R`, namely
`id_S ⊗̂ φ : S ⊗̂_R B →+* S ⊗̂_R A`, is again an adic morphism. -/
theorem baseChange_isAdicHom (hI : I.FG) (φ : B →ₐ[R] A) :
    IsAdicHom (idealOfDefinition R I S B) (idealOfDefinition R I S A)
      (map hI (AlgHom.id R S) φ) :=
  map_isAdicHom hI (AlgHom.id R S) φ

end CompletedTensorProduct
