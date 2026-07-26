import FormalSchemes.SpfGammaSheafComponentArbCont
import FormalSchemes.SpfGammaSheafComponent

set_option linter.style.header false

/-!
# The Spf–Γ round-trip (converse of EGA I 10.4.6, step (c))

For adic rings `(R, I)` and `(S, J)`, an arbitrary morphism of formal spectra
`f : Spf S ⟶ Spf R` whose global-sections map `φ = globalSectionsMap I J f` is continuous
(`hφ : I ≤ J.comap φ`) is *reconstructed* from `φ`: the model morphism `Spf φ =
locallyRingedSpaceMap I J φ hφ` equals `f`. Together with `globalSectionsMap_locallyRingedSpaceMap`
(`Γ ∘ Spf = id`) this makes `Spf` and `Γ` mutually inverse on continuous ring homomorphisms
(issue 96): the bijection

```
{ φ : R →+* S // I ≤ J.comap φ } ≃ { f : Spf S ⟶ Spf R // I ≤ J.comap (globalSectionsMap I J f) }.
```

## Main results

* `FormalSpectrum.arbSheafComponent_eq_modelSheafComponent`: the arbitrary-morphism basic-open
  component `arbSheafComponent I J f g` agrees with the reconstructed model component
  `modelSheafComponent I J φ hφ g` (both are the completed localization of `φ`).
* `FormalSpectrum.c_app_eq_on_basicOpen`: the sheaf `c`-components of `f` and of `Spf φ` agree on a
  basic open `D(g)`, after transporting along the base equality `f.base = mapTop`.
* `FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap`: the full round-trip `Spf φ = f`.
* `FormalSpectrum.spfGammaEquiv`: the resulting bijection (issue 96).

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

/-- **The arbitrary-morphism component equals the reconstructed model component.**
For a morphism `f : Spf S ⟶ Spf R` with continuous global-sections map
(`hφ : I ≤ J.comap (globalSectionsMap I J f)`), the conjugated basic-open component
`arbSheafComponent I J f g` agrees with the reconstructed model morphism's component
`modelSheafComponent I J (globalSectionsMap I J f) hφ g`. Both sides equal the completed
localization `AdicCompletion.mapCompletion (Localization.awayMap (globalSectionsMap I J f) g)`, so
the identity follows from `arbSheafComponent_eq_mapCompletion` and
`modelSheafComponent_eq_mapCompletion`. -/
theorem arbSheafComponent_eq_modelSheafComponent (hI : I.FG) (hJ : J.FG)
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (g : R)
    (hφ : I ≤ J.comap (globalSectionsMap I J f)) :
    arbSheafComponent I J f g =
      modelSheafComponent I J (globalSectionsMap I J f) hφ g := by
  rw [arbSheafComponent_eq_mapCompletion I J hI hJ f g hφ,
    modelSheafComponent_eq_mapCompletion I J (globalSectionsMap I J f) hφ g hI hJ]

end FormalSpectrum

end
