import FormalSchemes.SpfGamma
import FormalSchemes.SpfFunctorial

set_option linter.style.header false

/-!
# Global sections is functorial on formal spectra

`FormalSchemes/SpfGamma.lean` constructs, for adic rings `(R, I)` and `(S, J)`, the ring
homomorphism `FormalSpectrum.globalSectionsMap : (Spf S ⟶ Spf R) → (R →+* S)` obtained by taking
global sections of a morphism of formal spectra and using the identifications
`Γ(⊤, O_{Spf R}) ≃+* R`, and proves the half `globalSectionsMap (Spf φ) = φ` of the universal
property EGA I 10.4.6.

This file upgrades that bare map to a **functor**: taking global sections respects the identity
and (contravariantly) composition of morphisms of formal spectra.

* `FormalSpectrum.globalSectionsMap_id`: `Γ(𝟙 (Spf R)) = RingHom.id R`.
* `FormalSpectrum.globalSectionsMap_comp`: the contravariant composition law
  `globalSectionsMap I K (g ≫ f) = (globalSectionsMap J K g).comp (globalSectionsMap I J f)`.

Together with `globalSectionsMap_locallyRingedSpaceMap` (`Γ ∘ Spf = id`) and the functor laws
`FormalSpectrum.locallyRingedSpaceMap_id`/`_comp` (`Spf` is a functor, `SpfFunctorial.lean`),
these make `Γ` and `Spf` a pair of (contravariant) functors between adic rings with continuous
homomorphisms and formal spectra, with `Γ ∘ Spf` the identity — the categorical backbone of the
`Spf`–`Γ` correspondence of EGA I 10.4.6.

Both proofs stay at the single global-section component `f.c.app (op ⊤)`: the composition law is
just the `rfl` lemma `LocallyRingedSpace.comp_c_app` at `⊤` (whose preimage under `f.base` is again
`⊤`), so no structure-sheaf limit or `eqToHom` transport is involved.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable (I : Ideal R) (J : Ideal S) (K : Ideal T)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]
  [TopologicalSpace T] [IsAdicRing K]

/-- **Taking global sections respects the identity** (EGA I, 10.4.6): the ring homomorphism
recovered from the identity morphism of `Spf R` is the identity of `R`. -/
theorem globalSectionsMap_id :
    globalSectionsMap I I (𝟙 (locallyRingedSpaceObj I)) = RingHom.id R := by
  rw [← locallyRingedSpaceMap_id I]
  exact globalSectionsMap_locallyRingedSpaceMap I I (RingHom.id R) (Ideal.comap_id I).ge

/-- **Taking global sections respects composition** (EGA I, 10.4.6), contravariantly: the ring
homomorphism recovered from a composite `g ≫ f` of morphisms of formal spectra is the composite
(in the opposite order) of the recovered homomorphisms. -/
theorem globalSectionsMap_comp
    (g : locallyRingedSpaceObj K ⟶ locallyRingedSpaceObj J)
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) :
    globalSectionsMap I K (g ≫ f) =
      (globalSectionsMap J K g).comp (globalSectionsMap I J f) := by
  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, globalSectionsMap_apply, RingEquiv.symm_apply_apply]
  congr 1

end FormalSpectrum

end
