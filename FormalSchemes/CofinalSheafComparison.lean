import FormalSchemes.SpfFunctorial
import FormalSchemes.Sections
import FormalSchemes.CofinalCompletionFunctorial

set_option linter.style.header false

/-!
# Comparing the formal spectra for two ideals of definition (EGA I, §10.3)

For an adic ring `R` with two ideals of definition `I J : Ideal R` (both `IsAdicRing`, hence both
inducing the same, `I`-adic = `J`-adic, topology), the affine formal scheme `Spf R` should not
depend on the chosen ideal of definition: at the level of locally ringed spaces one expects
`Spf_I R ≅ Spf_J R` (EGA I, 10.3). This file assembles the pieces of that comparison that are
reachable from the already-merged commutative-algebra core, in the *nested cofinal* case `I ≤ J`.

Two directions of content are provided.

* **The base map is an isomorphism.** When `I ≤ J`, the identity ring homomorphism satisfies
  `I ≤ J.comap (RingHom.id R)`, so `FormalSpectrum.mapTop` gives a continuous map
  `Spf_J R ⟶ Spf_I R`. We identify this map with the canonical homeomorphism
  `IsAdic.homeomorphFormalSpectrum` (both send a point over the same prime of `R`), and conclude
  that `mapTop` is an isomorphism in `TopCat` — packaged as `FormalSpectrum.mapTopIsoId`. This is
  the base component of the sought locally-ringed-space isomorphism.

* **The rings of sections agree on basic opens.** On a basic open `D(f)`, the sections of the two
  structure sheaves are `AdicCompletion (I·R_f) R_f` and `AdicCompletion (J·R_f) R_f`
  (`FormalSpectrum.sectionsBasicOpenEquiv`), and these are canonically isomorphic through the
  cofinal comparison isomorphism `AdicCompletion.cofinalRingEquiv` (the merged ring-level core).
  This yields, for every `f`, a ring isomorphism
  `Γ(D(f), O_{Spf_I R}) ≃+* Γ(D(f), O_{Spf_J R})` (`FormalSpectrum.basicOpenSectionsComparison`),
  and on global sections the identification `Γ(⊤, O_{Spf_I R}) ≃+* Γ(⊤, O_{Spf_J R})`
  (`FormalSpectrum.globalSectionsComparison`), both descriptions recovering `R`. The naturality of
  these section isomorphisms with respect to the restriction maps between basic opens is the merged
  lemma `AdicCompletion.mapCompletion_comp_cofinalHom`; wiring that compatibility through the
  structure-sheaf restriction maps to glue the pointwise isomorphisms into a single
  `PresheafedSpace`/`LocallyRingedSpace` isomorphism over the base homeomorphism is the remaining,
  category-theoretically heavy, step towards the full `Spf_I R ≅ Spf_J R`.

## Main definitions and results

* `FormalSpectrum.mapId_eq_homeomorphFormalSpectrum`: the identity-induced base map equals the
  canonical homeomorphism of formal spectra.
* `FormalSpectrum.isIso_mapTopId` / `FormalSpectrum.mapTopIsoId`: the identity-induced base map is
  an isomorphism in `TopCat`.
* `FormalSpectrum.basicOpenSectionsComparison`: the ring-of-sections isomorphism on each basic open.
* `FormalSpectrum.globalSectionsComparison`: the ring-of-sections isomorphism on global sections.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], §10.3.
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I J : Ideal R)
  [IsAdicRing I] [IsAdicRing J]

/-!
### The base map is an isomorphism

When `I ≤ J`, the identity ring homomorphism is a continuous map of pairs `(R, I) → (R, J)`, and
the induced base map `Spf_J R ⟶ Spf_I R` is the canonical homeomorphism identifying the two
underlying spaces of `Spf R`.
-/

section BaseMap

omit [TopologicalSpace R] [IsAdicRing I] [IsAdicRing J] in
/-- The continuity hypothesis `I ≤ J.comap (RingHom.id R)` extracted from `I ≤ J`. -/
theorem le_comap_id_of_le (hIJ : I ≤ J) : I ≤ J.comap (RingHom.id R) :=
  le_trans hIJ (Ideal.comap_id J).ge

/-- The identity-induced base map `Spf_J R → Spf_I R` sends a point to the point of `Spf_I R`
lying over the same prime of `R`; this is exactly the canonical homeomorphism
`IsAdic.homeomorphFormalSpectrum` between the two descriptions of the underlying space of
`Spf R`. -/
theorem mapId_eq_homeomorphFormalSpectrum (hIJ : I ≤ J) (x : FormalSpectrum J) :
    map I J (RingHom.id R) (le_comap_id_of_le I J hIJ) x =
      (IsAdicRing.isAdic (I := J)).homeomorphFormalSpectrum (IsAdicRing.isAdic (I := I)) x := by
  apply (isClosedEmbedding_toPrimeSpectrum I).injective
  rw [IsAdic.toPrimeSpectrum_homeomorphFormalSpectrum,
    toPrimeSpectrum_map I J (RingHom.id R) (le_comap_id_of_le I J hIJ) x,
    PrimeSpectrum.comap_id]

/-- The identity-induced base map `Spf_J R ⟶ Spf_I R` equals `TopCat`-image of the canonical
homeomorphism of formal spectra. -/
theorem mapTopId_eq (hIJ : I ≤ J) :
    mapTop I J (RingHom.id R) (le_comap_id_of_le I J hIJ) =
      (TopCat.isoOfHomeo
        ((IsAdicRing.isAdic (I := J)).homeomorphFormalSpectrum
          (IsAdicRing.isAdic (I := I)))).hom := by
  refine TopCat.ext fun x => ?_
  exact mapId_eq_homeomorphFormalSpectrum I J hIJ x

/-- **The base map of the comparison is an isomorphism.** For two ideals of definition `I ≤ J`,
the identity-induced continuous map `Spf_J R ⟶ Spf_I R` is an isomorphism in `TopCat`, being the
canonical homeomorphism of the two descriptions of the underlying space of `Spf R`. -/
theorem isIso_mapTopId (hIJ : I ≤ J) :
    IsIso (mapTop I J (RingHom.id R) (le_comap_id_of_le I J hIJ)) := by
  rw [mapTopId_eq I J hIJ]
  infer_instance

/-- **The base isomorphism** `Spf_J R ≅ Spf_I R` in `TopCat`, packaging `isIso_mapTopId`. -/
def mapTopIsoId (hIJ : I ≤ J) : TopCat.of (FormalSpectrum J) ≅ TopCat.of (FormalSpectrum I) :=
  haveI := isIso_mapTopId I J hIJ
  asIso (mapTop I J (RingHom.id R) (le_comap_id_of_le I J hIJ))

end BaseMap

/-!
### The rings of sections agree on basic opens

On each basic open `D(f)`, the sections of the two structure sheaves are the two cofinal adic
completions of `R_f`, canonically isomorphic through `AdicCompletion.cofinalRingEquiv`.
-/

section Sections

/-- **The rings of sections on a basic open agree.** For two ideals of definition `I ≤ J` with `J`
cofinal in `I` (`J ^ a ≤ I`), the rings of sections of the two structure sheaves over a basic open
`D(f)` are canonically isomorphic: both are adic completions of the localization `R_f` for the
cofinal ideals `I · R_f`, `J · R_f`, and `AdicCompletion.cofinalRingEquiv` identifies them. -/
def basicOpenSectionsComparison (hIJ : I ≤ J) {a : ℕ} (hcof : J ^ a ≤ I) (f : R) :
    ((structureSheaf I).presheaf.obj (op (basicOpen I f)) : Type u) ≃+*
      ((structureSheaf J).presheaf.obj (op (basicOpen J f)) : Type u) :=
  (sectionsBasicOpenEquiv I f).trans
    (((AdicCompletion.cofinalRingEquiv
        (K := I.map (algebraMap R (Localization.Away f)))
        (L := J.map (algebraMap R (Localization.Away f)))
        (b := 1) (a := a)
        (by rw [pow_one]; exact Ideal.map_mono hIJ)
        (by rw [← Ideal.map_pow]; exact Ideal.map_mono hcof))).trans
      (sectionsBasicOpenEquiv J f).symm)

/-- **The rings of global sections agree**: both descriptions of `Γ(⊤, O_{Spf R})` recover `R`
itself (EGA I, 10.1.3), so the two structure sheaves have canonically isomorphic global sections,
independently of the chosen ideal of definition. -/
def globalSectionsComparison :
    ((structureSheaf I).presheaf.obj (op (⊤ : Opens (FormalSpectrum I))) : Type u) ≃+*
      ((structureSheaf J).presheaf.obj (op (⊤ : Opens (FormalSpectrum J))) : Type u) :=
  (globalSectionsEquiv I).trans (globalSectionsEquiv J).symm

end Sections

end FormalSpectrum

end
