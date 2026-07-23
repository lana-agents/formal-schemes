import FormalSchemes.AffineFibreProduct
import FormalSchemes.SpfGamma

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Uniqueness of the mediating morphism of the affine fibre product

For a base adic ring `(R, I)` (with `I` finitely generated) and two complete adic `R`-algebras
`A`, `B`, the completed tensor product `A ⊗̂_R B` is the coordinate ring of the fibre product
`Spf A ×_{Spf R} Spf B` (EGA I, 10.7). `FormalSchemes.AffineFibreProduct` (issue 202) delivered the
existence and commutativity halves of the universal property — the projection cone `fibrePr₁`,
`fibrePr₂` and the mediating morphism `fibreLift`. This file adds the **uniqueness** half, in the
regime that is actually available before the Spf–Γ adjunction (issue 96): among morphisms of the
form `Spf φ` for a ring homomorphism `φ`, the mediating morphism into `Spf (A ⊗̂_R B)` is unique.

The obstruction to *full* uniqueness in the category of locally ringed spaces is exactly the
recognition of an arbitrary locally-ringed-space morphism into `Spf (A ⊗̂_R B)` as `Spf` of a ring
homomorphism, which needs the Spf–Γ adjunction (issue 96). Restricted to `Spf`-of-ring-map
morphisms, uniqueness is the geometric shadow of `CompletedTensorProduct.hom_ext`, established here
by combining that ring-level universal property with the faithfulness of `Spf`
(`FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap`).

## Main results

* `CompletedTensorProduct.spfMap_comp_fibrePr₁` / `spfMap_comp_fibrePr₂`: composing `Spf φ` with a
  projection collapses to `Spf` of the corresponding composite ring homomorphism `φ ∘ inl` (resp.
  `φ ∘ inr`), via the merged functor law `locallyRingedSpaceMap_comp`.
* `CompletedTensorProduct.fibreLift_unique`: two morphisms `Spf φ₁`, `Spf φ₂` into
  `Spf (A ⊗̂_R B)` (for adic ring homomorphisms `φ₁, φ₂ : A ⊗̂_R B →+* S`) that agree after both
  projections are equal. In particular `fibreLift` is the unique such mediating morphism.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory FormalSpectrum

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [TopologicalSpace R] [IsAdicRing I]
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
variable [TopologicalSpace B] [IsAdicRing (I.map (algebraMap R B))]
variable [TopologicalSpace (CompletedTensorProduct R I A B)]
  [IsAdicRing (idealOfDefinition R I A B)]
variable {S : Type u} [CommRing S] [TopologicalSpace S] {L : Ideal S} [IsAdicRing L]

/-- The composite `φ ∘ inl` carries `I·A` into `L`, given that `φ` carries the ideal of definition
of `A ⊗̂_R B` into `L`. -/
theorem comp_inl_le_comap (φ : CompletedTensorProduct R I A B →+* S)
    (hφ : idealOfDefinition R I A B ≤ L.comap φ) :
    I.map (algebraMap R A) ≤ L.comap (φ.comp (inl R I A B).toRingHom) := by
  rw [← Ideal.comap_comap, ← Ideal.map_le_iff_le_comap,
    show Ideal.map (inl R I A B).toRingHom (I.map (algebraMap R A)) =
      idealOfDefinition R I A B from inl_isAdicHom]
  exact hφ

/-- The composite `φ ∘ inr` carries `I·B` into `L`. -/
theorem comp_inr_le_comap (φ : CompletedTensorProduct R I A B →+* S)
    (hφ : idealOfDefinition R I A B ≤ L.comap φ) :
    I.map (algebraMap R B) ≤ L.comap (φ.comp (inr R I A B).toRingHom) := by
  rw [← Ideal.comap_comap, ← Ideal.map_le_iff_le_comap,
    show Ideal.map (inr R I A B).toRingHom (I.map (algebraMap R B)) =
      idealOfDefinition R I A B from inr_isAdicHom]
  exact hφ

/-- Composing `Spf φ` with the first projection `fibrePr₁` collapses to `Spf` of the composite
ring homomorphism `φ ∘ inl : A → S`. -/
theorem spfMap_comp_fibrePr₁ (φ : CompletedTensorProduct R I A B →+* S)
    (hφ : idealOfDefinition R I A B ≤ L.comap φ) :
    locallyRingedSpaceMap (idealOfDefinition R I A B) L φ hφ ≫ fibrePr₁ =
      locallyRingedSpaceMap (I.map (algebraMap R A)) L
        (φ.comp (inl R I A B).toRingHom) (comp_inl_le_comap φ hφ) := by
  rw [fibrePr₁, IsAdicHom.spfMap,
    ← locallyRingedSpaceMap_comp (I := I.map (algebraMap R A))
      (J := idealOfDefinition R I A B) (K := L) (φ := (inl R I A B).toRingHom) (ψ := φ)
      (hIJ := inl_isAdicHom.le_comap) (hJK := hφ) (hIK := comp_inl_le_comap φ hφ)]

/-- Composing `Spf φ` with the second projection `fibrePr₂` collapses to `Spf` of `φ ∘ inr`. -/
theorem spfMap_comp_fibrePr₂ (φ : CompletedTensorProduct R I A B →+* S)
    (hφ : idealOfDefinition R I A B ≤ L.comap φ) :
    locallyRingedSpaceMap (idealOfDefinition R I A B) L φ hφ ≫ fibrePr₂ =
      locallyRingedSpaceMap (I.map (algebraMap R B)) L
        (φ.comp (inr R I A B).toRingHom) (comp_inr_le_comap φ hφ) := by
  rw [fibrePr₂, IsAdicHom.spfMap,
    ← locallyRingedSpaceMap_comp (I := I.map (algebraMap R B))
      (J := idealOfDefinition R I A B) (K := L) (φ := (inr R I A B).toRingHom) (ψ := φ)
      (hIJ := inr_isAdicHom.le_comap) (hJK := hφ) (hIK := comp_inr_le_comap φ hφ)]

/-- A ring homomorphism `φ` carrying the ideal of definition into `L` is continuous in the
filtration sense: it carries every power `(I·(A ⊗̂_R B))^m` into `L^m`. -/
theorem pow_mem_of_le_comap (φ : CompletedTensorProduct R I A B →+* S)
    (hφ : idealOfDefinition R I A B ≤ L.comap φ) (m : ℕ) (x : CompletedTensorProduct R I A B)
    (hx : x ∈ (idealOfDefinition R I A B) ^ m) : φ x ∈ L ^ m := by
  have hmap : Ideal.map φ (idealOfDefinition R I A B) ≤ L := Ideal.map_le_iff_le_comap.mpr hφ
  have hpow : Ideal.map φ ((idealOfDefinition R I A B) ^ m) ≤ L ^ m := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hmap m
  exact hpow (Ideal.mem_map_of_mem φ hx)

/-- **Uniqueness of the mediating morphism, among `Spf`-of-ring-map morphisms** (the uniqueness
half of the affine fibre-product universal property, EGA I 10.7). Two morphisms `Spf φ₁`,
`Spf φ₂ : Spf S ⟶ Spf (A ⊗̂_R B)` induced by adic ring homomorphisms `φ₁, φ₂ : A ⊗̂_R B →+* S` that
agree after both projections `fibrePr₁`, `fibrePr₂` are equal. In particular `fibreLift` is the
unique such mediating morphism. Full uniqueness in the category of locally ringed spaces
additionally requires the Spf–Γ adjunction (issue 96) to recognise an arbitrary morphism as `Spf`
of a ring map. -/
theorem fibreLift_unique (hI : I.FG) (φ₁ φ₂ : CompletedTensorProduct R I A B →+* S)
    (h₁ : idealOfDefinition R I A B ≤ L.comap φ₁) (h₂ : idealOfDefinition R I A B ≤ L.comap φ₂)
    (hpr₁ : locallyRingedSpaceMap (idealOfDefinition R I A B) L φ₁ h₁ ≫ fibrePr₁ =
      locallyRingedSpaceMap (idealOfDefinition R I A B) L φ₂ h₂ ≫ fibrePr₁)
    (hpr₂ : locallyRingedSpaceMap (idealOfDefinition R I A B) L φ₁ h₁ ≫ fibrePr₂ =
      locallyRingedSpaceMap (idealOfDefinition R I A B) L φ₂ h₂ ≫ fibrePr₂) :
    locallyRingedSpaceMap (idealOfDefinition R I A B) L φ₁ h₁ =
      locallyRingedSpaceMap (idealOfDefinition R I A B) L φ₂ h₂ := by
  -- Reduce the projection equalities to ring-level agreement on `inl` and `inr`, via faithfulness.
  rw [spfMap_comp_fibrePr₁ φ₁ h₁, spfMap_comp_fibrePr₁ φ₂ h₂] at hpr₁
  rw [spfMap_comp_fibrePr₂ φ₁ h₁, spfMap_comp_fibrePr₂ φ₂ h₂] at hpr₂
  have hl : φ₁.comp (inl R I A B).toRingHom = φ₂.comp (inl R I A B).toRingHom := by
    have := congrArg (globalSectionsMap (I.map (algebraMap R A)) L) hpr₁
    rwa [globalSectionsMap_locallyRingedSpaceMap, globalSectionsMap_locallyRingedSpaceMap] at this
  have hr : φ₁.comp (inr R I A B).toRingHom = φ₂.comp (inr R I A B).toRingHom := by
    have := congrArg (globalSectionsMap (I.map (algebraMap R B)) L) hpr₂
    rwa [globalSectionsMap_locallyRingedSpaceMap, globalSectionsMap_locallyRingedSpaceMap] at this
  -- Conclude equality of the ring homs via the completed-tensor universal property, then transport.
  have hφ : φ₁ = φ₂ :=
    hom_ext L hI (pow_mem_of_le_comap φ₁ h₁) (pow_mem_of_le_comap φ₂ h₂)
      (fun a => RingHom.congr_fun hl a) (fun b => RingHom.congr_fun hr b)
  subst hφ
  rfl

end CompletedTensorProduct
