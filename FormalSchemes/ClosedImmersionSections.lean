import FormalSchemes.ClosedImmersionStalk
import FormalSchemes.SpfGammaSheafComponent
import FormalSchemes.AdicMorphism
import FormalSchemes.AffineSeparated
import FormalSchemes.DiagonalClosedEmbedding

set_option linter.style.header false

/-!
# Closed immersions of formal spectra: section-level surjectivity (EGA I §10.14, §10.15)

`FormalSchemes/ClosedImmersionStalk.lean` reduced "`Spf φ` is a closed immersion" (for a surjective
ring hom `φ`) to a single sheaf-level input `hsec`: surjectivity of the induced structure-sheaf map
`mapSheafHom I J φ hφ` on the sections over every basic open `D(f₀) ⊆ Spf R`. This file discharges
`hsec` and assembles the unconditional closed-immersion statements.

The section over `D(f₀)` is the `I`-adic completion of the localization `R_{f₀}`
(`sectionsBasicOpenEquiv`), and the component of `mapSheafHom` there is the completion of the
localized map `R_{f₀} → S_{φ f₀}` (`modelSheafComponent_eq_mapCompletion`). Surjectivity of a
completed ring map that is surjective (with the ideal of definition pulled back to the ideal of
definition) is `AdicCompletion.mapCompletion_surjective` below, an instance of Mathlib's
`AdicCompletion.surjective_of_mk_map_comp_surjective` (a continuous ring map out of a precomplete
ring, surjective modulo the ideal of definition into a Hausdorff target, is surjective — no
Noetherian input is needed once the completions are complete, which holds for `I.FG`).

## Main results

* `AdicCompletion.mapCompletion_surjective`: `mapCompletion f` is surjective when `f` is surjective
  and `I.map f = J`.
* `FormalSpectrum.surjective_mapSheafHom_app_basicOpen`: the section-level surjectivity `hsec`.
* `FormalSpectrum.isClosedEmbedding_base_and_surjective_stalkMap_of_surjective`: the unconditional
  closed-immersion conjunction (closed embedding of the base + surjective stalk maps) for a
  surjective `φ` with `I.map φ = J`.
* `FormalSpectrum.closedFormalSubscheme_isClosedImmersion` and
  `CompletedTensorProduct.diagonal_isClosedImmersion`: the two concrete cases (§10.14 / §10.15).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.14, §10.15.
* [The Stacks Project, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Topology

universe u

namespace AdicCompletion

variable {R S : Type u} [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}

/-- **The completion of a surjection is surjective.** If `f : R →+* S` is surjective and carries the
ideal `I` exactly onto `J` (`I.map f = J`), then the induced map on `I`- and `J`-adic completions
`mapCompletion f` is surjective. Both ideals are finitely generated so that the completions are
complete adic rings; the surjectivity is Mathlib's `surjective_of_mk_map_comp_surjective` applied to
the level-`1` surjection `R ⧸ I → S ⧸ J`. -/
theorem mapCompletion_surjective (hI : I.FG) (hJ : J.FG) {f : R →+* S}
    (hf : I.map f ≤ J) (hfs : Function.Surjective f) (hIJ : I.map f = J) :
    Function.Surjective (mapCompletion f hf hJ) := by
  haveI hsc : IsAdicComplete (idealOfDefinition I) (AdicCompletion I R) :=
    (isAdicRing_map I hI).toIsAdicComplete
  haveI htc : IsAdicComplete (idealOfDefinition J) (AdicCompletion J S) :=
    (isAdicRing_map J hJ).toIsAdicComplete
  -- the ideal of definition maps onto the ideal of definition
  have hmap : (idealOfDefinition I).map (mapCompletion f hf hJ) = idealOfDefinition J := by
    rw [idealOfDefinition, Ideal.map_map, mapCompletion_comp_algebraMap, ← Ideal.map_map, hIJ]
  haveI hhaus : IsHausdorff ((idealOfDefinition I).map (mapCompletion f hf hJ))
      (AdicCompletion J S) := by rw [hmap]; infer_instance
  refine surjective_of_mk_map_comp_surjective
    (I := idealOfDefinition I) (f := mapCompletion f hf hJ) ?_
  -- surjectivity modulo the ideal of definition, computed at level 1
  intro ybar
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective ybar
  -- represent `evalₐ 1 y ∈ S ⧸ J` by an element of `S`, then lift through the surjection `f`
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (evalₐ J 1 y)
  obtain ⟨r, rfl⟩ := hfs s
  refine ⟨AdicCompletion.of I R r, ?_⟩
  -- both `mapCompletion (of r)` and `y` have the same first thickening, so differ by the ideal
  have hc : I ^ 1 ≤ (J ^ 1).comap f := by
    rw [pow_one, pow_one, ← Ideal.map_le_iff_le_comap]; exact hf
  have hev : evalₐ J 1 (mapCompletion f hf hJ (AdicCompletion.of I R r)) = evalₐ J 1 y := by
    rw [evalₐ_mapCompletion f hf hJ hI 1 hc, evalₐ_of, Ideal.quotientMap_mk, hs]
  have hker : y - mapCompletion f hf hJ (AdicCompletion.of I R r) ∈ idealOfDefinition J := by
    have hmem : y - mapCompletion f hf hJ (AdicCompletion.of I R r) ∈
        RingHom.ker (evalₐ J 1).toRingHom := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact (hev).symm
    rwa [ker_evalₐ _ hJ 1, pow_one] at hmem
  rw [RingHom.coe_comp, Function.comp_apply, Ideal.Quotient.mk_eq_mk_iff_sub_mem, hmap]
  have hneg := neg_mem hker
  rwa [neg_sub] at hneg

end AdicCompletion

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]
variable (φ : R →+* S) (hφ : I ≤ J.comap φ) (g : R)

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J] in
/-- **The model morphism's sheaf `c`-component on `D(g)` is surjective**, for a surjective ring hom
`φ` carrying `I` exactly onto `J`. Via `modelSheafComponent_eq_mapCompletion` the component is the
completion of the localized surjection `R_g → S_{φ g}`, and `mapCompletion_surjective` applies. -/
theorem surjective_modelSheafComponent (hI : I.FG) (hφsurj : Function.Surjective φ)
    (hIJ : I.map φ = J) :
    Function.Surjective (modelSheafComponent I J φ hφ g) := by
  have hJ : J.FG := hIJ ▸ hI.map φ
  rw [modelSheafComponent_eq_mapCompletion I J φ hφ g hI hJ]
  apply AdicCompletion.mapCompletion_surjective (hI.map _) (hJ.map _)
  · -- `Localization.awayMap φ g` is surjective since `φ` is
    rw [Localization.awayMap_surjective_iff]
    intro a
    obtain ⟨b, rfl⟩ := hφsurj a
    exact ⟨b, 0, by rw [pow_zero, one_mul]⟩
  · -- the ideal of definition of `R_g` maps exactly onto that of `S_{φ g}`
    rw [Ideal.map_map, awayMap_comp_algebraMap, ← Ideal.map_map, hIJ]

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J] in
/-- **The section-level surjectivity `hsec`.** For a surjective `φ` with `I.map φ = J`, the induced
structure-sheaf map `mapSheafHom I J φ hφ` is surjective on the sections over every basic open
`D(g) ⊆ Spf R`. This is exactly the `hsec` hypothesis that
`isClosedEmbedding_base_and_surjective_stalkMap_of_surjective_sections` consumes. -/
theorem surjective_mapSheafHom_app_basicOpen (hI : I.FG) (hφsurj : Function.Surjective φ)
    (hIJ : I.map φ = J) :
    Function.Surjective ((mapSheafHom I J φ hφ).hom.app (op (basicOpen I g))).hom := by
  have hmodel := surjective_modelSheafComponent I J φ hφ g hI hφsurj hIJ
  -- `modelSheafComponent u = e_J (restrict (M (e_I.symm u)))` definitionally
  have hcomp : ∀ u, modelSheafComponent I J φ hφ g u =
      (sectionsBasicOpenEquiv J (φ g))
        (((structureSheaf J).presheaf.map
            (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g)))).hom
          (((mapSheafHom I J φ hφ).hom.app (op (basicOpen I g))).hom
            ((sectionsBasicOpenEquiv I g).symm u))) := fun _ => rfl
  -- the flanking `sectionsBasicOpenEquiv` and the `eqToHom` restriction are injective
  have hrestrict_inj : Function.Injective
      (((structureSheaf J).presheaf.map
        (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g)))).hom) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).injective
  intro t
  obtain ⟨u, hu⟩ := hmodel ((sectionsBasicOpenEquiv J (φ g))
    (((structureSheaf J).presheaf.map
        (eqToHom (congrArg op (map_preimage_basicOpen I J φ hφ g)))).hom t))
  refine ⟨(sectionsBasicOpenEquiv I g).symm u, ?_⟩
  rw [hcomp u] at hu
  exact hrestrict_inj ((sectionsBasicOpenEquiv J (φ g)).injective hu)

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J] in
/-- **`Spf φ` of a surjective ring homomorphism `φ` with `I.map φ = J` is a closed immersion.**
Both defining conditions of a closed immersion of locally ringed spaces (Stacks Tag 01HJ) hold: the
base map is a closed topological embedding (`isClosedEmbedding_map_of_surjective`, §10.14/§10.15
topological half) and every stalk map is surjective — the latter now unconditional, its sheaf-level
input `hsec` discharged by `surjective_mapSheafHom_app_basicOpen`. -/
theorem isClosedEmbedding_base_and_surjective_stalkMap_of_surjective
    (hI : I.FG) (hφsurj : Function.Surjective φ) (hIJ : I.map φ = J) :
    IsClosedEmbedding (map I J φ hφ) ∧
      ∀ y, Function.Surjective ((presheafedSpaceMap I J φ hφ).stalkMap y).hom :=
  isClosedEmbedding_base_and_surjective_stalkMap_of_surjective_sections I J φ hφ hφsurj
    (fun g => surjective_mapSheafHom_app_basicOpen I J φ hφ g hI hφsurj hIJ)

end FormalSpectrum
