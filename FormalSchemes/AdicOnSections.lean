import FormalSchemes.BasicOpenImmersion
import FormalSchemes.SpfGammaFunctorial

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Adicity of charts on global sections

The general statement "an open immersion of affine adic formal spectra is *adic* on global
sections" (`K ≤ L.comap (globalSectionsMap K L φ)`) is **false**: `IsAdicRing L` only fixes the
topology, not the ideal `L`, so an open immersion can match incompatible filtration levels
(see issue 460 / project memory `2026-08-16-issue460-general-adicity-FALSE-corrected-plan.md`).

However, the *specific* charts produced by the fibre-product assembly (EGA I §10.7) are composites
of **basic-open charts** `FormalSpectrum.basicOpenChart`, and each of those is adic on global
sections because it is `Spf` of the structural ring map `R → R{1/f}`, which carries the ideal of
definition into the ideal of definition (`le_comap_awayCompletionHom`). This file records that fact
in `globalSectionsMap` form together with the composition law "a composite of maps that are adic on
global sections is adic on global sections", so downstream assemblies can discharge their continuity
obligations by chasing an explicit basic-open decomposition rather than appealing to the false
general statement.

## Main results

* `FormalSpectrum.globalSectionsMap_basicOpenChart`: the global-sections map of `basicOpenChart I f`
  is the structural ring map `awayCompletionHom I f`.
* `FormalSpectrum.basicOpenChart_le_comap_globalSectionsMap`: `basicOpenChart I f` is adic on global
  sections.
* `FormalSpectrum.le_comap_globalSectionsMap_comp`: composing two morphisms that are adic on global
  sections yields a morphism adic on global sections.
* `FormalSpectrum.le_comap_globalSectionsMap_basicOpenChart_comp`: pre-composing an adic-on-sections
  morphism with a basic-open chart stays adic on global sections.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §§10.4.6, 10.12.
-/

noncomputable section

open CategoryTheory

universe u

namespace FormalSpectrum

section BasicOpenChart

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I] (f : R)
  [IsAdicRing (awayCompletionIdeal I f)]

/-- **The global-sections map of a basic-open chart is its structural ring map.** Since
`basicOpenChart I f` is by definition `Spf` of `awayCompletionHom I f` (the map `R → R{1/f}`),
taking global sections recovers `awayCompletionHom I f` (`Γ ∘ Spf = id`, EGA I 10.4.6). -/
@[simp]
theorem globalSectionsMap_basicOpenChart :
    globalSectionsMap I (awayCompletionIdeal I f) (basicOpenChart I f) = awayCompletionHom I f :=
  globalSectionsMap_locallyRingedSpaceMap I (awayCompletionIdeal I f) (awayCompletionHom I f)
    (le_comap_awayCompletionHom I f)

/-- **A basic-open chart is adic on global sections**: the ideal of definition `I` of the target is
carried into the ideal of definition `awayCompletionIdeal I f` of the source. This is the
`globalSectionsMap`-level restatement of `le_comap_awayCompletionHom`. -/
theorem basicOpenChart_le_comap_globalSectionsMap :
    I ≤ (awayCompletionIdeal I f).comap
      (globalSectionsMap I (awayCompletionIdeal I f) (basicOpenChart I f)) := by
  rw [globalSectionsMap_basicOpenChart]
  exact le_comap_awayCompletionHom I f

end BasicOpenChart

section Comp

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (I : Ideal R) (J : Ideal S) (K : Ideal T)
  [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]
  [TopologicalSpace T] [IsAdicRing K]

/-- **A composite of morphisms adic on global sections is adic on global sections.** If
`φ : Spf J ⟶ Spf I` and `ψ : Spf K ⟶ Spf J` each carry the target ideal of definition into the
source ideal of definition on global sections, then so does `ψ ≫ φ : Spf K ⟶ Spf I`. Contravariant
functoriality of `globalSectionsMap` (`globalSectionsMap_comp`) plus monotonicity of `comap`. -/
theorem le_comap_globalSectionsMap_comp
    (φ : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (ψ : locallyRingedSpaceObj K ⟶ locallyRingedSpaceObj J)
    (hφ : I ≤ J.comap (globalSectionsMap I J φ))
    (hψ : J ≤ K.comap (globalSectionsMap J K ψ)) :
    I ≤ K.comap (globalSectionsMap I K (ψ ≫ φ)) := by
  rw [globalSectionsMap_comp, ← Ideal.comap_comap]
  exact hφ.trans (Ideal.comap_mono hψ)

end Comp

section BasicOpenChartComp

variable {R S : Type u} [CommRing R] [CommRing S]
  (I : Ideal R) (J : Ideal S) (g : S)
  [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]
  [IsAdicRing (awayCompletionIdeal J g)]

/-- **Pre-composing an adic-on-sections morphism with a basic-open chart stays adic on global
sections.** For `φ : Spf J ⟶ Spf I` adic on global sections, the composite
`basicOpenChart J g ≫ φ : Spf J{1/g} ⟶ Spf I` is again adic on global sections. This is the exact
shape consumed by the fibre-product overlap continuity obligation, where the overlap chart factors
as a composite of two basic-open charts. -/
theorem le_comap_globalSectionsMap_basicOpenChart_comp
    (φ : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (hφ : I ≤ J.comap (globalSectionsMap I J φ)) :
    I ≤ (awayCompletionIdeal J g).comap
      (globalSectionsMap I (awayCompletionIdeal J g) (basicOpenChart J g ≫ φ)) :=
  le_comap_globalSectionsMap_comp I J (awayCompletionIdeal J g) φ (basicOpenChart J g) hφ
    (basicOpenChart_le_comap_globalSectionsMap J g)

end BasicOpenChartComp

end FormalSpectrum

end
