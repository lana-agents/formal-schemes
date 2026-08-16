import FormalSchemes.OpenImmersionReflectsIdeal
import FormalSchemes.SpfGammaSheafComponentArb
import Mathlib.Geometry.RingedSpace.OpenImmersion

set_option linter.style.header false
set_option linter.style.setOption false

/-!
# The sheaf component of an open immersion is a ring iso over its range

Let `w : Spf S ⟶ Spf R` be an **open immersion** of formal spectra
(`w : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I` with
`[LocallyRingedSpace.IsOpenImmersion w]`), and let `g : R` with the basic open `D(g)` contained in
the range of `w.base`. Then the sheaf `c`-component of `w` on `D(g)` is an isomorphism
(`isIso_c_app_basicOpen_of_le_range`), and hence the conjugated ring hom on completed localizations
`arbSheafComponent I J w g : R{1/g} →+* S{1/Ψ g}` (`SpfGammaSheafComponentArb.lean`) is
**bijective** (`bijective_arbSheafComponent`).

This is crux `(A)` of the adic-source-descent reduction (issue 471a / 480): it is the missing,
reusable topological content behind `reflects_awayCompletionIdeal_of_bijective`
(`OpenImmersionReflectsIdeal.lean`) — an open immersion restricts to an isomorphism onto its (open)
image, so its structure-sheaf component over any open contained in the range is invertible. It feeds
the adic-on-sections descent `le_comap_globalSectionsMap_of_cover` (471c / 482) and the general
§10.15 separatedness program (issue 62).

## Main results

* `FormalSpectrum.isIso_c_app_basicOpen_of_le_range`: `w.c.app (op D(g))` is an isomorphism when
  `D(g) ⊆ range w.base`.
* `FormalSpectrum.bijective_arbSheafComponent`: `arbSheafComponent I J w g` is bijective under the
  same hypothesis.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6, §10.12.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Opposite

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J] in
/-- **The sheaf component of an open immersion over its range is an isomorphism.**
For an open immersion `w : Spf S ⟶ Spf R` and `g : R` with `D(g) ⊆ range w.base`, the structure
sheaf `c`-component `w.c.app (op D(g))` is an isomorphism in `CommRingCat`. This is the
`PresheafedSpace.IsOpenImmersion.c_iso'` fact — an open immersion's component over the image of an
open is invertible — applied to the open `D(g)`, which is the image of its own preimage because it
lies in the range. -/
theorem isIso_c_app_basicOpen_of_le_range
    (w : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion w] (g : R)
    (hg : (basicOpen I g : Set (FormalSpectrum I)) ⊆ Set.range w.base) :
    IsIso (w.c.app (op (basicOpen I g))) := by
  refine PresheafedSpace.IsOpenImmersion.c_iso' (f := w.toHom)
    ((Opens.map w.base).obj (basicOpen I g)) ?_
  apply Opens.ext
  simp only [PresheafedSpace.IsOpenImmersion.opensFunctor]
  exact (Set.image_preimage_eq_of_subset hg).symm

/-- **`arbSheafComponent` of an open immersion over its range is bijective.**
For an open immersion `w : Spf S ⟶ Spf R` and `g : R` with `D(g) ⊆ range w.base`, the conjugated
ring hom `arbSheafComponent I J w g : R{1/g} →+* S{1/Ψ g}` (`Ψ = globalSectionsMap I J w`) is
bijective — it is the composite of the sheaf-component isomorphism `w.c.app (op D(g))`
(`isIso_c_app_basicOpen_of_le_range`) with the two `sectionsBasicOpenEquiv` ring equivalences and
the structure-sheaf restriction along the basic-open-preimage identification, all bijective. This is
crux `(A)` supplying the `hbij` hypothesis of `reflects_awayCompletionIdeal_of_bijective`. -/
theorem bijective_arbSheafComponent
    (w : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion w] (g : R)
    (hg : (basicOpen I g : Set (FormalSpectrum I)) ⊆ Set.range w.base) :
    Function.Bijective (arbSheafComponent I J w g) := by
  have hCiso : IsIso (w.c.app (op (basicOpen I g))) :=
    isIso_c_app_basicOpen_of_le_range I J w g hg
  have hA := (sectionsBasicOpenEquiv J (globalSectionsMap I J w g)).bijective
  have hD := (sectionsBasicOpenEquiv I g).symm.bijective
  have hB : Function.Bijective ⇑(CommRingCat.Hom.hom
      ((structureSheaf J).presheaf.map
        (eqToHom (congrArg op (base_preimage_basicOpen I J w g))))) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hC : Function.Bijective ⇑(CommRingCat.Hom.hom (w.c.app (op (basicOpen I g)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mp hCiso
  rw [arbSheafComponent]
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact hA.comp (hB.comp (hC.comp hD))

/-- **The sheaf component of an open immersion reflects the ideal of definition over its range.**
For an open immersion `w : Spf S ⟶ Spf R` and `g t : R` with `D(g) ⊆ range w.base`, if the source
ideal of definition `J` is contained in the restriction of `I` over the range
(`hres : J ≤ Ideal.map (globalSectionsMap I J w) I` — hypothesis `(B)`) and `Ψ t ∈ J`
(`Ψ = globalSectionsMap I J w`), then `awayCompletionHom I g t ∈ awayCompletionIdeal I g`.

This is the end-to-end adic-source reflection of issue 471a: it supplies the `(A)` bijectivity input
(`bijective_arbSheafComponent`) to the merged reduction `reflects_awayCompletionIdeal_of_bijective`,
leaving only the containment `(B)` for the caller. The bare form without `(B)` is *false* — an open
immersion may shrink the ideal of definition the wrong way (the reversed cofinal iso
`Spf₍y₎ ⟶ Spf₍y²₎`); `(B)` holds for the concrete completed-localization pieces the descent
`le_comap_globalSectionsMap_of_cover` (471c / 482) covers with. -/
theorem reflects_awayCompletionIdeal
    (w : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion w] (g t : R)
    (hg : (basicOpen I g : Set (FormalSpectrum I)) ⊆ Set.range w.base)
    (hres : J ≤ Ideal.map (globalSectionsMap I J w) I)
    (ht : globalSectionsMap I J w t ∈ J) :
    awayCompletionHom I g t ∈ awayCompletionIdeal I g :=
  reflects_awayCompletionIdeal_of_bijective I J w g t
    (bijective_arbSheafComponent I J w g hg) hres ht

end FormalSpectrum

end
