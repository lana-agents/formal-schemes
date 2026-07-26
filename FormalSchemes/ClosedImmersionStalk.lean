import FormalSchemes.DiagonalClosedEmbedding

set_option linter.style.header false

/-!
# Closed immersions of formal spectra: reducing the sheaf half to sections (EGA I §10.14, §10.15)

A morphism of locally ringed spaces is a **closed immersion** when its underlying map is a closed
topological embedding and its map of structure sheaves is surjective on stalks (Stacks Tag 01HJ;
this is how `AlgebraicGeometry.IsClosedImmersion` is defined for schemes, via `SurjectiveOnStalks`).
For a morphism of formal spectra `Spf S ⟶ Spf R` induced by a **surjective**
ring homomorphism `φ : R →+* S` the closed-embedding half is already available
(`FormalSpectrum.isClosedEmbedding_map_of_surjective`, in `DiagonalClosedEmbedding.lean`).
This file supplies the reduction that isolates the **remaining sheaf-level input**:

* `FormalSpectrum.surjective_stalkMap_of_surjective_sections`: the stalk maps of
  `FormalSpectrum.locallyRingedSpaceMap` are **surjective** as soon as the induced map of structure
  sheaves `mapSheafHom` is **surjective on the sections over every basic open** `D(f₀) ⊆ Spf R` (and
  `φ` is surjective, so that every basic open of `Spf S` is the preimage of one of `Spf R`).

The proof is a direct germ chase: a target germ at `y ∈ Spf S` is represented by a section over a
basic open `D(g') ∋ y`; surjectivity of `φ` writes `g' = φ f₀`, so `D(g') = mapTop⁻¹ D(f₀)`
(`FormalSpectrum.map_preimage_basicOpen`); the section-level surjectivity lifts that section to a
section over `D(f₀)`, whose germ maps to the target germ by
`AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply`. This mirrors the germ chase of
`FormalSpectrum.isLocalHom_stalkMap`, but for surjectivity instead of unit-detection — and,
crucially, it does **not** reduce to the level-`0` thickening (units are detected at level `0`, but
surjectivity is not), so it consumes the full section-level surjectivity as its hypothesis.

The remaining hypothesis — surjectivity of `mapSheafHom` on basic-open sections — is the adic
completion of the surjection `R_{f₀} → S_{φ f₀}`, which is surjective over a Noetherian base
(Artin–Rees / Mittag-Leffler on the kernel filtration); discharging it is a separate,
Noetherian-specific step.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.14, §10.15.
* [The Stacks Project, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Topology

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S) (φ : R →+* S) (hφ : I ≤ J.comap φ)

/-- **The stalk maps of `Spf φ` are surjective once its sheaf component is surjective on
basic-open sections.** For a surjective ring homomorphism `φ : R →+* S` between adic rings, if the
induced map of structure sheaves `mapSheafHom I J φ hφ` is surjective on the sections over every
basic open `D(f₀) ⊆ Spf R`, then every stalk map of the morphism of formal spectra `Spf S ⟶ Spf R`
is surjective. Together with the closed topological embedding of the base
(`FormalSpectrum.isClosedEmbedding_map_of_surjective`), this exhibits `Spf φ` as a closed immersion
(EGA I §10.14, §10.15). -/
theorem surjective_stalkMap_of_surjective_sections (hφsurj : Function.Surjective φ)
    (hsec : ∀ f₀ : R, Function.Surjective
      ⇑((mapSheafHom I J φ hφ).hom.app (op (basicOpen I f₀))).hom)
    (y : FormalSpectrum J) :
    Function.Surjective ((presheafedSpaceMap I J φ hφ).stalkMap y).hom := by
  intro t
  -- represent the target germ by a section over an open `V ∋ y`
  obtain ⟨V, hyV, t₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ t
  -- shrink `V` to a basic open `D(g') ∋ y`
  obtain ⟨w, hw, hyw, hwV⟩ := (isTopologicalBasis_basicOpen J).exists_subset_of_mem_open hyV V.2
  obtain ⟨g', rfl⟩ := hw
  -- surjectivity of `φ` writes `g' = φ f₀`, so `D(g') = mapTop⁻¹ D(f₀)`
  obtain ⟨f₀, rfl⟩ := hφsurj g'
  have hyw' : y ∈ basicOpen J (φ f₀) := hyw
  have hwV' : basicOpen J (φ f₀) ≤ V := hwV
  rw [← map_preimage_basicOpen I J φ hφ f₀] at hyw' hwV'
  -- lift the restricted section `t₀|_{D(g')}` through the section-level surjectivity
  obtain ⟨s', hs'⟩ := hsec f₀ ((structureSheaf J).presheaf.map (homOfLE hwV').op t₀)
  -- the stalk map sends the germ of `s'` to the germ of `mapSheafHom … s' = t₀|_{D(g')}`
  have key : ((presheafedSpaceMap I J φ hφ).stalkMap y).hom
        (((structureSheaf I).presheaf.germ (basicOpen I f₀) (mapTop I J φ hφ y) hyw').hom s') =
      ((structureSheaf J).presheaf.germ ((Opens.map (mapTop I J φ hφ)).obj (basicOpen I f₀))
          y hyw').hom (((mapSheafHom I J φ hφ).hom.app (op (basicOpen I f₀))).hom s') :=
    PresheafedSpace.stalkMap_germ_apply (presheafedSpaceMap I J φ hφ) (basicOpen I f₀) y hyw' s'
  refine ⟨((structureSheaf I).presheaf.germ (basicOpen I f₀) (mapTop I J φ hφ y) hyw').hom s', ?_⟩
  rw [key, hs']
  exact TopCat.Presheaf.germ_res_apply _ (homOfLE hwV') y hyw' t₀

/-- **`Spf φ` of a surjective ring homomorphism is a closed immersion**, provided its induced map
of structure sheaves is surjective on basic-open sections. The two conjuncts are exactly the
defining conditions of a closed immersion of locally ringed spaces (Stacks Tag 01HJ): the base map
is a closed topological embedding (`isClosedEmbedding_map_of_surjective`), and every stalk map is
surjective (`surjective_stalkMap_of_surjective_sections`). This is the sheaf-level completion of the
topological `base_closed` halves already recorded for the closed formal subscheme (EGA I §10.14) and
the affine diagonal (EGA I §10.15). -/
theorem isClosedEmbedding_base_and_surjective_stalkMap_of_surjective_sections
    (hφsurj : Function.Surjective φ)
    (hsec : ∀ f₀ : R, Function.Surjective
      ⇑((mapSheafHom I J φ hφ).hom.app (op (basicOpen I f₀))).hom) :
    IsClosedEmbedding (map I J φ hφ) ∧
      ∀ y, Function.Surjective ((presheafedSpaceMap I J φ hφ).stalkMap y).hom :=
  ⟨isClosedEmbedding_map_of_surjective I J φ hφ hφsurj,
    surjective_stalkMap_of_surjective_sections I J φ hφ hφsurj hsec⟩

end FormalSpectrum
