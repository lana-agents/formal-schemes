import FormalSchemes.SpfFunctorial
import FormalSchemes.AdicMorphism

set_option linter.style.header false

/-!
# Isomorphic adic rings have isomorphic formal spectra

`FormalSchemes/SpfMap.lean` builds the morphism `Spf S ⟶ Spf R` induced by a continuous ring
homomorphism, and `FormalSchemes/SpfFunctorial.lean` proves it respects identities and
composition (EGA I, 10.2). Those three facts contain the statement that `Spf` carries a ring
**isomorphism** to an isomorphism of formal spectra, and this file is where that statement lives.

## Main results

* `FormalSpectrum.isoOfAdicRingEquiv`: from `e : R ≃+* S` with `IsAdicHom I J e.toRingHom` — that
  is, `I.map e = J`, so `e` carries the ideal of definition of the source *onto* that of the
  target — an isomorphism `Spf R ≅ Spf S` of locally ringed spaces.
* `FormalSpectrum.isAdicHom_ringEquiv_symm`: the hypothesis is symmetric, so the inverse is adic
  too. `FormalSpectrum.ringEquiv_symm_toRingHom_comp` and
  `FormalSpectrum.ringEquiv_toRingHom_comp_symm` are the two round-trip identities the proof runs
  on.

## History, and why this file exists at all

These four declarations were written for `FormalSchemes/CompletedTensorAwayInterchangeSpf.lean`,
whose `CompletedTensorAwayInterchange.equivSpfIso` is their original consumer, and they sat there
behind a **32**-module transitive import closure. Nothing about them is specific to completed tensor
products, so they are here instead, behind **18** modules (both counts include the module itself),
where a consumer that has no business importing the completed-tensor tower can still reach them.

They are stated for arbitrary rings and ideals deliberately: the mutual-inverse laws then reduce to
the identity and composition functoriality of `Spf` on *abstract* terms, and the elaborator never
has to `whnf` a large concrete ring at the instantiation site.

## What is *not* proved

Nothing here is stated at `AlgebraicGeometry.FormalScheme.Spf`; the isomorphism is of locally
ringed spaces. That is the form the consumers on this tree need, since
`FormalSpectrum.locallyRingedSpaceObj` is what `LocallyRingedSpace.IsOpenImmersion` and the chart
criteria are stated about. The converse direction — an isomorphism of formal spectra giving a ring
isomorphism — is `FormalSpectrum.spfIsoRingEquiv` (`FormalSchemes.SpfIsoIdealRecovery`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.2.
-/

noncomputable section

open CategoryTheory

universe u

namespace FormalSpectrum

/-- The underlying ring homomorphisms of `e` and `e.symm` are mutually inverse. -/
theorem ringEquiv_symm_toRingHom_comp {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    e.symm.toRingHom.comp e.toRingHom = RingHom.id R :=
  RingHom.ext e.symm_apply_apply

/-- The underlying ring homomorphisms of `e` and `e.symm` are mutually inverse (other order). -/
theorem ringEquiv_toRingHom_comp_symm {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    e.toRingHom.comp e.symm.toRingHom = RingHom.id S :=
  RingHom.ext e.apply_symm_apply

/-- If a ring isomorphism `e` is adic (`I·e = J`), then its inverse is adic (`J·e⁻¹ = I`). -/
theorem isAdicHom_ringEquiv_symm {R S : Type u} [CommRing R] [CommRing S]
    {I : Ideal R} {J : Ideal S} (e : R ≃+* S) (h : IsAdicHom I J e.toRingHom) :
    IsAdicHom J I e.symm.toRingHom := by
  have hgoal : J.map e.symm.toRingHom = I := by
    rw [← h, Ideal.map_map, ringEquiv_symm_toRingHom_comp, Ideal.map_id]
  exact hgoal

/-- **Isomorphism of affine formal spectra from an adic ring isomorphism** `e : R ≃+* S` with
`IsAdicHom I J e` (`I·e = J`): the two half-morphisms are the maps of formal spectra induced by `e`
and `e.symm`, and the mutual-inverse laws come from the identity/composition functoriality of `Spf`
(`locallyRingedSpaceMap_id`, `locallyRingedSpaceMap_comp`). -/
def isoOfAdicRingEquiv {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S) (h : IsAdicHom I J e.toRingHom) :
    locallyRingedSpaceObj I ≅ locallyRingedSpaceObj J where
  hom := locallyRingedSpaceMap J I e.symm.toRingHom (isAdicHom_ringEquiv_symm e h).le_comap
  inv := locallyRingedSpaceMap I J e.toRingHom h.le_comap
  hom_inv_id := by
    rw [← locallyRingedSpaceMap_comp I J I e.toRingHom e.symm.toRingHom h.le_comap
        (isAdicHom_ringEquiv_symm e h).le_comap
        (h.comp (isAdicHom_ringEquiv_symm e h)).le_comap,
      locallyRingedSpaceMap_congr I I (e.symm.toRingHom.comp e.toRingHom) (RingHom.id R) _
        (Ideal.comap_id I).ge (ringEquiv_symm_toRingHom_comp e),
      locallyRingedSpaceMap_id]
  inv_hom_id := by
    rw [← locallyRingedSpaceMap_comp J I J e.symm.toRingHom e.toRingHom
        (isAdicHom_ringEquiv_symm e h).le_comap h.le_comap
        ((isAdicHom_ringEquiv_symm e h).comp h).le_comap,
      locallyRingedSpaceMap_congr J J (e.toRingHom.comp e.symm.toRingHom) (RingHom.id S) _
        (Ideal.comap_id J).ge (ringEquiv_toRingHom_comp_symm e),
      locallyRingedSpaceMap_id]

end FormalSpectrum

end
