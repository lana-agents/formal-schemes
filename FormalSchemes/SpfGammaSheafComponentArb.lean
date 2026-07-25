import FormalSchemes.SpfGammaBase
import FormalSchemes.SpfGammaSheafComponent

set_option linter.style.header false

/-!
# The sheaf component of an arbitrary morphism of formal spectra on a basic open

For adic rings `(R, I)` and `(S, J)` and an **arbitrary** morphism of formal spectra
`f : Spf S ⟶ Spf R` (a morphism of locally ringed spaces, *not* assumed to be a reconstructed
model morphism `Spf φ`), this file sets up the sheaf `c`-component of `f` on a basic open
`D(g) ⊆ Spf R`, conjugated by `FormalSpectrum.sectionsBasicOpenEquiv` on both sides, as a single
ring homomorphism between completed localizations
`R{1/g} →+* S{1/φ g}`, where `φ = FormalSpectrum.globalSectionsMap I J f`.

This is the arbitrary-morphism analogue of the setup performed by
`FormalSchemes/SpfGammaSheafComponent.lean` for the reconstructed model morphism
`Spf φ = locallyRingedSpaceMap I J φ hφ`, whose conjugated component
`FormalSpectrum.modelSheafComponent` was identified there with a completed localization. It is the
entry point for the still-open hard half of step (b) of the converse of EGA I 10.4.6 (issue 157):
matching `f.c` on `D(g)` for an arbitrary `f` with the completed localization of its induced ring
map, using locality (`f.prop`) together with the step-(a) base identification.

The key preliminary is that the target open of `f.c` on `D(g)` is again a basic open: the preimage
of `D(g)` under the (a priori free) base map `f.base` is `D(φ g)`. This is forced by the action of
`f` on global sections and is *containment-free* — it needs no continuity hypothesis, only the
step-(a) identification `FormalSpectrum.base_toPrimeSpectrum_eq` — so it upgrades the model-morphism
target-open lemma `map_preimage_basicOpen` (which is stated for the induced `mapTop`) to an
arbitrary morphism.

## Main results

* `FormalSpectrum.base_preimage_basicOpen`: for an arbitrary morphism `f : Spf S ⟶ Spf R`, the
  preimage of the basic open `D(g)` under `f.base` is the basic open `D(φ g)`, where
  `φ = globalSectionsMap I J f`.
* `FormalSpectrum.arbSheafComponent`: the sheaf `c`-component of `f` on `D(g)`, conjugated by
  `sectionsBasicOpenEquiv` on both sides, as a ring hom `R{1/g} →+* S{1/φ g}`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

/-- **The preimage of a basic open under an arbitrary morphism of formal spectra is a basic open.**
For any morphism `f : Spf S ⟶ Spf R` of locally ringed spaces, the preimage under the base map
`f.base` of the basic open `D(g)` is the basic open `D(φ g)`, where `φ = globalSectionsMap I J f`
is the induced homomorphism on global sections. This is containment-free — it needs no continuity
hypothesis — and generalises `map_preimage_basicOpen` (stated for the induced `mapTop`) to an
arbitrary `f`, using the step-(a) base identification `base_toPrimeSpectrum_eq`. -/
theorem base_preimage_basicOpen
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (g : R) :
    (Opens.map f.base).obj (basicOpen I g) = basicOpen J (globalSectionsMap I J f g) := by
  apply Opens.ext
  ext y
  change Ideal.Quotient.mk I g ∉ (f.base y).asIdeal ↔
    Ideal.Quotient.mk J (globalSectionsMap I J f g) ∉ y.asIdeal
  have hI : (Ideal.Quotient.mk I g ∈ (f.base y).asIdeal) ↔
      (g ∈ (toPrimeSpectrum I (f.base y)).asIdeal) := by
    rw [toPrimeSpectrum, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have hJ : (Ideal.Quotient.mk J (globalSectionsMap I J f g) ∈ y.asIdeal) ↔
      (g ∈ (toPrimeSpectrum I (f.base y)).asIdeal) := by
    rw [base_toPrimeSpectrum_eq I J f y, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      toPrimeSpectrum, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  rw [not_iff_not, hI, hJ]

/-- The sheaf `c`-component of an arbitrary morphism `f : Spf S ⟶ Spf R` on the basic open `D(g)`,
conjugated by `sectionsBasicOpenEquiv` on both sides (the target open `f.base⁻¹ D(g) = D(φ g)`
identified by `base_preimage_basicOpen` and transported by the structure-sheaf restriction along
that equality of opens), as a ring hom `R{1/g} →+* S{1/φ g}`, where `φ = globalSectionsMap I J f`.
This is the arbitrary-morphism analogue of `modelSheafComponent`. -/
def arbSheafComponent
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (g : R) :
    awayCompletion I g →+* awayCompletion J (globalSectionsMap I J f g) :=
  (sectionsBasicOpenEquiv J (globalSectionsMap I J f g)).toRingHom.comp
    ((((structureSheaf J).presheaf.map
        (eqToHom (congrArg op (base_preimage_basicOpen I J f g)))).hom).comp
      (((f.c.app (op (basicOpen I g))).hom).comp
        (sectionsBasicOpenEquiv I g).symm.toRingHom))

end FormalSpectrum

end
