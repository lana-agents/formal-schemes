import FormalSchemes.CofinalIdeal
import FormalSchemes.SpfGammaBase
import FormalSchemes.SpfGammaFunctorial

set_option linter.style.header false

/-!
# What an isomorphism of formal spectra recovers about the ideal of definition

An isomorphism `Spf J₁ ≅ Spf J₂` of affine formal schemes gives a ring isomorphism of the two
global-section rings for free — global sections are a functor, and no fullness of `Spf` is
involved. The question this file settles is what that isomorphism does to the ideals.

## The answer, and the statement it replaces

It carries `J₂` to an ideal **cofinal** with `J₁` (`FormalSpectrum.isCofinal_map_spfIsoRingEquiv`),
and no more. The stronger statement — that it carries `J₂` *onto* `J₁` — is **false**: the space of
`Spf J` is `Spec (A ⧸ J)`, so an isomorphism sees `J` only through `V (J)`, hence only through its
radical, and `L` versus `L ^ 2` is the counterexample. Concretely,
`FormalSpectrum.cofinalSpfIso` (`FormalSchemes.CofinalSheafComparisonIso`) builds an isomorphism
`Spf I ≅ Spf J` for two *different* ideals of definition of one ring, over the identity ring map.

This matters because `IsTopologicallyFiniteType` pins the ideal of a tf-type
algebra to `I · A` on the nose (`IsTopologicallyFiniteType.map_eq`), so a
transport along such an isomorphism cannot be a transport of the predicate as stated. It is
`IsTopologicallyFiniteType.ofCofinal` (`FormalSchemes.CofinalTopFiniteType`)
that absorbs the discrepancy, and this file is what feeds it.

## Why no continuity hypothesis is needed

`AdicRingCat.spfHomEquiv` (`FormalSchemes.SpfFullyFaithful`) recovers a morphism of formal spectra
from a ring map only under the *strict* containment `R.ideal ≤ S.ideal.comap _`, and that condition
is not an isomorphism invariant — that is the same `L` versus `L ^ 2` phenomenon, recorded for open
immersions in `FormalSchemes.AdicOnSections`. None of it is needed here: the whole proof runs
through `FormalSpectrum.base_toPrimeSpectrum_eq` (`FormalSchemes.SpfGammaBase`), which is stated
with **no** containment hypothesis and says that the base map of any morphism of formal spectra is
`Spec` of its action on global sections. So the underlying-space argument is available
unconditionally, and it is exactly enough to pin the radicals.

## Main definitions and results

* `FormalSpectrum.spfIsoRingEquiv`: the ring isomorphism `A₂ ≃+* A₁` underlying an isomorphism
  `Spf J₁ ≅ Spf J₂`, from `FormalSpectrum.globalSectionsMap` and its functoriality.
* `FormalSpectrum.zeroLocus_map_spfIsoRingEquiv`: it identifies `V (J₂ · A₁)` with `V (J₁)`.
* `FormalSpectrum.isCofinal_map_spfIsoRingEquiv`: **the recovery lemma.** For finitely generated
  ideals of definition, `J₂ · A₁` is cofinal with `J₁`.
* `FormalSpectrum.exists_ringEquiv_isCofinal_of_iso`: the packaged existential form, which is what
  a consumer assembling a tower out of two independently witnessed charts wants.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.3, §10.5.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace FormalSpectrum

variable {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
variable {J₁ : Ideal A₁} {J₂ : Ideal A₂}
variable [TopologicalSpace A₁] [IsAdicRing J₁] [TopologicalSpace A₂] [IsAdicRing J₂]
variable (e : locallyRingedSpaceObj J₁ ≅ locallyRingedSpaceObj J₂)

/-- **The ring isomorphism underlying an isomorphism of formal spectra.** Global sections of the
two structure sheaves are `A₁` and `A₂` (`FormalSpectrum.globalSectionsEquiv`), and
`FormalSpectrum.globalSectionsMap` is functorial
(`FormalSpectrum.globalSectionsMap_id`, `FormalSpectrum.globalSectionsMap_comp`), so the two
directions of `e` give mutually inverse ring homomorphisms.

Contravariant: `e : Spf J₁ ≅ Spf J₂` yields `A₂ ≃+* A₁`. Nothing here needs `Spf` to be full — this
is the free half, and the module docstring explains which half is not. -/
def spfIsoRingEquiv : A₂ ≃+* A₁ :=
  RingEquiv.ofRingHom (globalSectionsMap J₂ J₁ e.hom) (globalSectionsMap J₁ J₂ e.inv)
    (by rw [← globalSectionsMap_comp, e.hom_inv_id, globalSectionsMap_id])
    (by rw [← globalSectionsMap_comp, e.inv_hom_id, globalSectionsMap_id])

@[simp]
theorem spfIsoRingEquiv_apply (a : A₂) : spfIsoRingEquiv e a = globalSectionsMap J₂ J₁ e.hom a :=
  rfl

theorem spfIsoRingEquiv_toRingHom :
    (spfIsoRingEquiv e).toRingHom = globalSectionsMap J₂ J₁ e.hom :=
  rfl

theorem spfIsoRingEquiv_symm_toRingHom :
    (spfIsoRingEquiv e).symm.toRingHom = globalSectionsMap J₁ J₂ e.inv :=
  rfl

/-- The two `PrimeSpectrum.comap`s of `FormalSpectrum.spfIsoRingEquiv` and its inverse cancel,
because the ring map they come from is an isomorphism. Stated pointwise: an equality of the two
`comap` *functions* would have to be transported through `ContinuousMap`, and only the values are
needed below. -/
theorem comap_spfIsoRingEquiv_symm_comap (q : PrimeSpectrum A₁) :
    PrimeSpectrum.comap (globalSectionsMap J₁ J₂ e.inv)
        (PrimeSpectrum.comap (spfIsoRingEquiv e).toRingHom q) = q := by
  apply PrimeSpectrum.ext
  ext a
  change spfIsoRingEquiv e ((spfIsoRingEquiv e).symm a) ∈ q.asIdeal ↔ a ∈ q.asIdeal
  rw [RingEquiv.apply_symm_apply]

/-- Membership of `V (J₂ · A₁)` is membership of `V (J₂)` after `PrimeSpectrum.comap`. This is
`Ideal.map_le_iff_le_comap` read in the spectrum, and it is the only place the extended ideal
`J₂ · A₁` is unfolded. -/
theorem mem_zeroLocus_map_spfIsoRingEquiv (q : PrimeSpectrum A₁) :
    q ∈ PrimeSpectrum.zeroLocus (J₂.map (spfIsoRingEquiv e).toRingHom : Set A₁) ↔
      PrimeSpectrum.comap (spfIsoRingEquiv e).toRingHom q ∈
        PrimeSpectrum.zeroLocus (J₂ : Set A₂) := by
  simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, PrimeSpectrum.comap_asIdeal]
  exact Ideal.map_le_iff_le_comap

/-- **The isomorphism identifies the two closed subsets of the respective spectra.** Extending `J₂`
along `FormalSpectrum.spfIsoRingEquiv` cuts out, inside `Spec A₁`, exactly `V (J₁)`.

Both inclusions run the same way: `FormalSpectrum.range_toPrimeSpectrum` identifies `V (J)` with
the image of `Spf J` in `Spec`, and `FormalSpectrum.base_toPrimeSpectrum_eq` says the base map of
`e.hom` (respectively `e.inv`) becomes `PrimeSpectrum.comap` of the recovered ring map. No
containment hypothesis on `e` is used anywhere; see the module docstring. -/
theorem zeroLocus_map_spfIsoRingEquiv :
    PrimeSpectrum.zeroLocus (J₂.map (spfIsoRingEquiv e).toRingHom : Set A₁) =
      PrimeSpectrum.zeroLocus (J₁ : Set A₁) := by
  ext q
  rw [mem_zeroLocus_map_spfIsoRingEquiv]
  constructor
  · intro hq
    -- `comap σ q` comes from a point `z` of `Spf J₂`; carry `z` back along `e.inv`.
    rw [← range_toPrimeSpectrum J₂] at hq
    obtain ⟨z, hz⟩ := hq
    have hkey := base_toPrimeSpectrum_eq J₁ J₂ e.inv z
    rw [hz, comap_spfIsoRingEquiv_symm_comap] at hkey
    rw [← range_toPrimeSpectrum J₁]
    exact ⟨e.inv.base z, hkey⟩
  · intro hq
    rw [← range_toPrimeSpectrum J₁] at hq
    obtain ⟨y, rfl⟩ := hq
    rw [← range_toPrimeSpectrum J₂]
    refine ⟨e.hom.base y, ?_⟩
    rw [base_toPrimeSpectrum_eq J₂ J₁ e.hom y, spfIsoRingEquiv_toRingHom]

/-- **The recovery lemma.** For finitely generated ideals of definition, an isomorphism of formal
spectra `Spf J₁ ≅ Spf J₂` recovers a ring isomorphism `A₂ ≃+* A₁` carrying `J₂` to an ideal
**cofinal** with `J₁` — and, as the module docstring explains, that is the strongest true form.

`FormalSpectrum.zeroLocus_map_spfIsoRingEquiv` gives the equality of the two closed subsets;
`PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical` turns that into an equality of radicals; and
`Ideal.IsCofinal.of_radical_eq` turns *that* into cofinality, which is precisely where finite
generation is used. -/
theorem isCofinal_map_spfIsoRingEquiv (hJ₁ : J₁.FG) (hJ₂ : J₂.FG) :
    Ideal.IsCofinal (J₂.map (spfIsoRingEquiv e).toRingHom) J₁ := by
  refine Ideal.IsCofinal.of_radical_eq (hJ₂.map _) hJ₁ ?_
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
    ← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, zeroLocus_map_spfIsoRingEquiv]

include e in
/-- The packaged existential form of `FormalSpectrum.isCofinal_map_spfIsoRingEquiv`, for a caller
that wants a ring isomorphism together with the cofinality and does not care how either was
produced. -/
theorem exists_ringEquiv_isCofinal_of_iso (hJ₁ : J₁.FG) (hJ₂ : J₂.FG) :
    ∃ σ : A₂ ≃+* A₁, Ideal.IsCofinal (J₂.map σ.toRingHom) J₁ :=
  ⟨spfIsoRingEquiv e, isCofinal_map_spfIsoRingEquiv e hJ₁ hJ₂⟩

end FormalSpectrum
