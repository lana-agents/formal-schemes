import FormalSchemes.AdicOnSections
import FormalSchemes.LiftedBasicOpenCover

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Adicity on global sections is local on the source

The general statement "an open immersion of affine adic formal spectra is adic on global sections"
is FALSE (issue 460): `IsAdicRing L` fixes only the topology, not the ideal `L`. But adicity on
global sections is a *local* condition on the source: if a morphism `φ : Spf J ⟶ Spf I` becomes
adic on global sections after restriction to an open cover of the source, then `φ` itself is adic on
global sections. This is the structure-sheaf-separatedness content behind the fibre-product
diagonal's continuity witnesses (issue 235c) and the general §10.15 separatedness program (issue 62).

## Main result

* `FormalSpectrum.le_comap_globalSectionsMap_of_cover`: adicity on global sections descends along an
  open cover of the source.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §§10.4.6, 10.12.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology AlgebraicGeometry

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
  (I : Ideal R) (J : Ideal S)
  [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

/-- **Adicity on global sections descends along an open cover of the source.**
Let `φ : Spf J ⟶ Spf I` and let `{wᵥ : Spf Lᵥ ⟶ Spf J}` be a family of morphisms whose base images
cover `Spf J`. If every composite `wᵥ ≫ φ` is adic on global sections, then so is `φ`. -/
theorem le_comap_globalSectionsMap_of_cover
    (φ : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    {ιidx : Type u} {Sv : ιidx → Type u} [∀ v, CommRing (Sv v)] [∀ v, TopologicalSpace (Sv v)]
    (Lv : ∀ v, Ideal (Sv v)) [∀ v, IsAdicRing (Lv v)]
    (wv : ∀ v, locallyRingedSpaceObj (Lv v) ⟶ locallyRingedSpaceObj J)
    [∀ v, LocallyRingedSpace.IsOpenImmersion (wv v)]
    (hcover : ⋃ v, Set.range (wv v).base = Set.univ)
    (hadic : ∀ v, I ≤ (Lv v).comap (globalSectionsMap I (Lv v) (wv v ≫ φ))) :
    I ≤ J.comap (globalSectionsMap I J φ) := by
  sorry

end FormalSpectrum

end
