import FormalSchemes.CompletedTensorFunctor
import FormalSchemes.AffineFibreProduct

set_option linter.style.header false

/-!
# Naturality of the affine fibre-product projections under `mapSpf`

The affine fibre product `Spf (A ⊗̂_R B)` (`FormalSchemes.AffineFibreProduct`) carries the two
projections `fibrePr₁ = Spf (inl) : Spf (A ⊗̂_R B) ⟶ Spf A` and
`fibrePr₂ = Spf (inr) : Spf (A ⊗̂_R B) ⟶ Spf B`, and a pair of `R`-algebra maps
`f : A →ₐ[R] A'`, `g : B →ₐ[R] B'` induces the functorial morphism of formal spectra
`CompletedTensorProduct.mapSpf hI f g : Spf (A' ⊗̂_R B') ⟶ Spf (A ⊗̂_R B)`
(`FormalSchemes.CompletedTensorFunctor`).

This file records that the functorial map is **natural in the two projections**:

* `mapSpf_comp_fibrePr₁ : mapSpf hI f g ≫ fibrePr₁ = fibrePr₁ ≫ Spf f`,
* `mapSpf_comp_fibrePr₂ : mapSpf hI f g ≫ fibrePr₂ = fibrePr₂ ≫ Spf g`,

where `Spf f` / `Spf g` are the morphisms of formal spectra induced by `f`, `g` between the ideals
of definition `I·A → I·A'` and `I·B → I·B'` (`algHom_isAdicHom_map`). Both squares reduce, via the
contravariant composition law `FormalSpectrum.locallyRingedSpaceMap_comp` and
`locallyRingedSpaceMap_congr`, to the ring-level identities `map hI f g ∘ inl = inl ∘ f` and
`map hI f g ∘ inr = inr ∘ g` (`map_inl` / `map_inr`).

These naturality squares are the datum the *glued* general fibre product `X ×_S Y` (EGA I §10.7)
consumes on double overlaps: when an overlap-chart transition of a factor is `mapSpf` of a chart
transition, this naturality is exactly what makes the glued projections `pr₁ : X ×_S Y ⟶ X`,
`pr₂ : X ×_S Y ⟶ Y` well-defined across charts. Unlike the away-localization interchange, they are
pure functoriality of `Spf` and do not touch the completed-localization bookkeeping.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.2, §10.7.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory FormalSpectrum

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I]
variable {A B A' B' : Type u}
variable [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [CommRing A'] [CommRing B'] [Algebra R A'] [Algebra R B']
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
variable [TopologicalSpace B] [IsAdicRing (I.map (algebraMap R B))]
variable [TopologicalSpace A'] [IsAdicRing (I.map (algebraMap R A'))]
variable [TopologicalSpace B'] [IsAdicRing (I.map (algebraMap R B'))]

set_option linter.unusedSectionVars false in
/-- An `R`-algebra homomorphism `f : A →ₐ[R] A'` is an adic morphism for the ideals of definition
`I·A` and `I·A'`: it carries `I·A` onto `I·A'`. This packages the structural morphism
`Spf A' ⟶ Spf A` of an `R`-algebra map, `(algHom_isAdicHom_map f).spfMap`. -/
theorem algHom_isAdicHom_map (f : A →ₐ[R] A') :
    IsAdicHom (I.map (algebraMap R A)) (I.map (algebraMap R A')) f.toRingHom := by
  unfold IsAdicHom
  rw [Ideal.map_map,
    show f.toRingHom.comp (algebraMap R A) = algebraMap R A' from AlgHom.comp_algebraMap f]

set_option linter.unusedSectionVars false in
/-- **Naturality of the first projection under `mapSpf`.** The functorial morphism of formal
spectra commutes with the first projections and the induced map `Spf f` of the first factor. -/
theorem mapSpf_comp_fibrePr₁ (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B' hI
    mapSpf hI f g ≫ fibrePr₁ (R := R) (A := A) (B := B) =
      fibrePr₁ (R := R) (A := A') (B := B') ≫ (algHom_isAdicHom_map (I := I) f).spfMap := by
  haveI := isAdicRing R I A B hI
  haveI := isAdicRing R I A' B' hI
  simp only [mapSpf, fibrePr₁, IsAdicHom.spfMap]
  rw [← locallyRingedSpaceMap_comp (I := I.map (algebraMap R A))
      (J := idealOfDefinition R I A B) (K := idealOfDefinition R I A' B')
      (φ := (inl R I A B).toRingHom) (ψ := map hI f g)
      (hIJ := inl_isAdicHom.le_comap) (hJK := (map_isAdicHom hI f g).le_comap)
      (hIK := (inl_isAdicHom.comp (map_isAdicHom hI f g)).le_comap),
    ← locallyRingedSpaceMap_comp (I := I.map (algebraMap R A))
      (J := I.map (algebraMap R A')) (K := idealOfDefinition R I A' B')
      (φ := f.toRingHom) (ψ := (inl R I A' B').toRingHom)
      (hIJ := (algHom_isAdicHom_map f).le_comap) (hJK := inl_isAdicHom.le_comap)
      (hIK := ((algHom_isAdicHom_map f).comp inl_isAdicHom).le_comap)]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _
    (RingHom.ext fun a => map_inl hI f g a)

set_option linter.unusedSectionVars false in
/-- **Naturality of the second projection under `mapSpf`.** The functorial morphism of formal
spectra commutes with the second projections and the induced map `Spf g` of the second factor. -/
theorem mapSpf_comp_fibrePr₂ (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B' hI
    mapSpf hI f g ≫ fibrePr₂ (R := R) (A := A) (B := B) =
      fibrePr₂ (R := R) (A := A') (B := B') ≫ (algHom_isAdicHom_map (I := I) g).spfMap := by
  haveI := isAdicRing R I A B hI
  haveI := isAdicRing R I A' B' hI
  simp only [mapSpf, fibrePr₂, IsAdicHom.spfMap]
  rw [← locallyRingedSpaceMap_comp (I := I.map (algebraMap R B))
      (J := idealOfDefinition R I A B) (K := idealOfDefinition R I A' B')
      (φ := (inr R I A B).toRingHom) (ψ := map hI f g)
      (hIJ := inr_isAdicHom.le_comap) (hJK := (map_isAdicHom hI f g).le_comap)
      (hIK := (inr_isAdicHom.comp (map_isAdicHom hI f g)).le_comap),
    ← locallyRingedSpaceMap_comp (I := I.map (algebraMap R B))
      (J := I.map (algebraMap R B')) (K := idealOfDefinition R I A' B')
      (φ := g.toRingHom) (ψ := (inr R I A' B').toRingHom)
      (hIJ := (algHom_isAdicHom_map g).le_comap) (hJK := inr_isAdicHom.le_comap)
      (hIK := ((algHom_isAdicHom_map g).comp inr_isAdicHom).le_comap)]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _
    (RingHom.ext fun b => map_inr hI f g b)

end CompletedTensorProduct
