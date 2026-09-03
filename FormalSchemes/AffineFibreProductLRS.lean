import FormalSchemes.AffineFibreProductUniqueness
import FormalSchemes.SpfGammaRoundTrip

set_option linter.style.header false

/-!
# Full locally-ringed-space uniqueness for the affine fibre product

For a base adic ring `(R, I)` (with `I` finitely generated) and two complete adic `R`-algebras
`A`, `B`, the completed tensor product `A ⊗̂_R B` is the coordinate ring of the fibre product
`Spf A ×_{Spf R} Spf B` (EGA I, 10.7). `FormalSchemes.AffineFibreProduct` (issue 202) delivered the
existence and commutativity halves of the universal property, and
`FormalSchemes.AffineFibreProductUniqueness` delivered uniqueness **among `Spf`-of-ring-map
morphisms** — the regime available before the Spf–Γ adjunction.

This file removes that restriction for **affine-formal-spectrum sources**. The obstruction, flagged
throughout the fibre-product development, was exactly the recognition of an arbitrary
locally-ringed-space morphism into `Spf (A ⊗̂_R B)` as `Spf` of a ring homomorphism. That is now the
merged Spf–Γ round-trip `FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap` (`Spf ∘ Γ = id`,
issue 96): every morphism `Spf S ⟶ Spf (A ⊗̂_R B)` with continuous global-sections map is `Spf` of
its global-sections map. Feeding it into `CompletedTensorProduct.fibreLift_unique` upgrades
uniqueness to *all* locally-ringed-space morphisms from an affine formal spectrum `Spf S`.

## Main results

* `CompletedTensorProduct.fibreLift_unique_lrs`: two **arbitrary** morphisms `f₁, f₂ : Spf S ⟶
  Spf (A ⊗̂_R B)` with continuous global-sections maps that agree after both projections `fibrePr₁`,
  `fibrePr₂` are equal. This is the full locally-ringed-space uniqueness of the fibre-product
  mediating morphism, for affine-formal-spectrum test objects.
* `CompletedTensorProduct.eq_fibreLift`: `fibreLift hIL f g hI` is the **unique** morphism
  `Spf S ⟶ Spf (A ⊗̂_R B)` (with continuous global-sections map) whose composites with the two
  projections are `Spf f` and `Spf g`.

Both remain in the continuity-restricted regime (morphisms carrying the ideal of definition into `L`
under their global-sections map), which is the correct level of generality: continuity is not
derivable from an arbitrary locally-ringed-space morphism (issue 156). A genuine
`CategoryTheory.Limits.IsLimit` — which would assert the universal property for *every* object of
`LocallyRingedSpace`, including non-affine and non-continuity-restricted ones — does not hold and is
not attempted here.

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

/-- **Full locally-ringed-space uniqueness of the fibre-product mediating morphism** (EGA I 10.7,
for affine-formal-spectrum sources). Two *arbitrary* morphisms of locally ringed spaces
`f₁, f₂ : Spf S ⟶ Spf (A ⊗̂_R B)` with continuous global-sections maps
(`idealOfDefinition R I A B ≤ L.comap (globalSectionsMap …)`) that agree after both projections
`fibrePr₁`, `fibrePr₂` coincide.

Compared with `fibreLift_unique`, no assumption that `fᵢ` is `Spf` of a ring homomorphism is made:
the merged Spf–Γ round-trip `locallyRingedSpaceMap_globalSectionsMap` (issue 96) rewrites each `fᵢ`
as `Spf (globalSectionsMap fᵢ)`, after which `fibreLift_unique` applies. -/
theorem fibreLift_unique_lrs (hI : I.FG) (hL : L.FG)
    (f₁ f₂ : locallyRingedSpaceObj L ⟶ locallyRingedSpaceObj (idealOfDefinition R I A B))
    (hf₁ : idealOfDefinition R I A B ≤
      L.comap (globalSectionsMap (idealOfDefinition R I A B) L f₁))
    (hf₂ : idealOfDefinition R I A B ≤
      L.comap (globalSectionsMap (idealOfDefinition R I A B) L f₂))
    (hpr₁ : f₁ ≫ fibrePr₁ = f₂ ≫ fibrePr₁)
    (hpr₂ : f₁ ≫ fibrePr₂ = f₂ ≫ fibrePr₂) :
    f₁ = f₂ := by
  have hK : (idealOfDefinition R I A B).FG := idealOfDefinition_fg R I A B hI
  -- Recognise each `fᵢ` as `Spf` of its global-sections map (`Spf ∘ Γ = id`, issue 96).
  have e₁ := locallyRingedSpaceMap_globalSectionsMap
    (idealOfDefinition R I A B) L hK hL f₁ hf₁
  have e₂ := locallyRingedSpaceMap_globalSectionsMap
    (idealOfDefinition R I A B) L hK hL f₂ hf₂
  rw [← e₁, ← e₂] at hpr₁ hpr₂ ⊢
  exact fibreLift_unique hI _ _ hf₁ hf₂ hpr₁ hpr₂

section Characterisation

variable [Algebra R S]

/-- **`fibreLift` is the unique mediating morphism**, now among *all* locally-ringed-space morphisms
from `Spf S` with continuous global-sections map. Given `R`-algebra maps `f : A →ₐ[R] S`,
`g : B →ₐ[R] S` (into a complete adic `R`-algebra `S` with `I·S ≤ L`), any morphism `m : Spf S ⟶
Spf (A ⊗̂_R B)` (with continuous global-sections map) satisfying `m ≫ fibrePr₁ = Spf f`
and `m ≫ fibrePr₂ = Spf g` equals `fibreLift hIL f g hI`. Combined with `fibreLift_comp_pr₁`,
`fibreLift_comp_pr₂` (existence), this is the fibre-product universal property for
affine-formal-spectrum sources. -/
theorem eq_fibreLift (hI : I.FG) (hL : L.FG) (hIL : I.map (algebraMap R S) ≤ L)
    (f : A →ₐ[R] S) (g : B →ₐ[R] S)
    (m : locallyRingedSpaceObj L ⟶ locallyRingedSpaceObj (idealOfDefinition R I A B))
    (hm : idealOfDefinition R I A B ≤
      L.comap (globalSectionsMap (idealOfDefinition R I A B) L m))
    (hmpr₁ : m ≫ fibrePr₁ = locallyRingedSpaceMap (I.map (algebraMap R A)) L
      f.toRingHom (algHom_le_comap f hIL))
    (hmpr₂ : m ≫ fibrePr₂ = locallyRingedSpaceMap (I.map (algebraMap R B)) L
      g.toRingHom (algHom_le_comap g hIL)) :
    m = fibreLift hIL f g hI := by
  -- Continuity of `fibreLift`'s global-sections map: it is `lift`, continuous by `lift_le_comap`.
  have h_fl : idealOfDefinition R I A B ≤
      L.comap (globalSectionsMap (idealOfDefinition R I A B) L (fibreLift hIL f g hI)) := by
    have hglob : globalSectionsMap (idealOfDefinition R I A B) L (fibreLift hIL f g hI) =
        lift L hIL f g := by
      rw [fibreLift, globalSectionsMap_locallyRingedSpaceMap]
    rw [hglob]
    exact lift_le_comap hIL f g hI
  refine fibreLift_unique_lrs hI hL m (fibreLift hIL f g hI) hm h_fl ?_ ?_
  · rw [hmpr₁, fibreLift_comp_pr₁]
  · rw [hmpr₂, fibreLift_comp_pr₂]

end Characterisation

end CompletedTensorProduct
