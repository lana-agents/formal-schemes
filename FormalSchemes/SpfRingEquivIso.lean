import FormalSchemes.SpfFunctorial

set_option linter.style.header false

/-!
# Isomorphic adic rings have isomorphic formal spectra

`FormalSchemes/SpfMap.lean` builds the morphism `Spf S ⟶ Spf R` induced by a continuous ring
homomorphism, and `FormalSchemes/SpfFunctorial.lean` proves it respects identities and
composition (EGA I, 10.2). Those three facts already contain the statement that `Spf` carries a
ring **isomorphism** to an isomorphism of formal spectra, but nothing on the tree had said so, so
every place that wanted to move a result from one presentation of an adic ring to another had to
stop at the ring and could not follow it to the space.

This file supplies the missing direction. It is the converse of
`FormalSpectrum.spfIsoRingEquiv` (`FormalSchemes.SpfIsoIdealRecovery`), which goes from an
isomorphism of formal spectra to a ring isomorphism; here a ring isomorphism produces the
isomorphism of formal spectra.

## Main results

* `FormalSpectrum.locallyRingedSpaceMapIso`: from `e : R ≃+* S` continuous in both directions
  (`I ≤ J.comap e` and `J ≤ I.comap e.symm`), an isomorphism
  `Spf R ≅ Spf S` of locally ringed spaces, with
  `FormalSpectrum.locallyRingedSpaceMapIso_hom` and
  `FormalSpectrum.locallyRingedSpaceMapIso_inv` its two legs.
* `FormalSpectrum.locallyRingedSpaceMapIsoOfMapEq`: the same from the single hypothesis
  `I.map e = J`, which is the form the hypothesis usually arrives in — an ideal transported along
  an isomorphism. Both continuity conditions are then automatic.

## The proof

`locallyRingedSpaceMap_comp` turns each round trip into the map induced by `e.symm.comp e`
(respectively `e.comp e.symm`), `locallyRingedSpaceMap_congr` replaces that composite by
`RingHom.id`, and `locallyRingedSpaceMap_id` finishes. Neither functoriality lemma carries an
`eqToHom` transport, so there is nothing to conjugate and the two round trips are three rewrites
each.

## What is *not* proved

Nothing here is stated at `AlgebraicGeometry.FormalScheme.Spf`; the isomorphism is of locally
ringed spaces. That is the form the consumers on this tree need, since
`FormalSpectrum.locallyRingedSpaceObj` is what `LocallyRingedSpace.IsOpenImmersion` and the chart
criteria are stated about.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.2.
-/

noncomputable section

open CategoryTheory

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

/-- **A ring isomorphism of adic rings induces an isomorphism of their formal spectra.** The two
legs are `FormalSpectrum.locallyRingedSpaceMap` at `e.symm` and at `e`; the round trips are
`FormalSpectrum.locallyRingedSpaceMap_comp` followed by
`FormalSpectrum.locallyRingedSpaceMap_congr` and `FormalSpectrum.locallyRingedSpaceMap_id`.

Note the two continuity hypotheses are genuinely two: `I ≤ J.comap e` does not by itself give
`J ≤ I.comap e.symm` — that is the statement that `e` carries `I` *onto* `J` rather than merely
into it. `FormalSpectrum.locallyRingedSpaceMapIsoOfMapEq` packages the usual case. -/
def locallyRingedSpaceMapIso (e : R ≃+* S) (h : I ≤ J.comap (e : R →+* S))
    (h' : J ≤ I.comap (e.symm : S →+* R)) :
    locallyRingedSpaceObj I ≅ locallyRingedSpaceObj J where
  hom := locallyRingedSpaceMap J I (e.symm : S →+* R) h'
  inv := locallyRingedSpaceMap I J (e : R →+* S) h
  hom_inv_id := by
    have hid : (e.symm : S →+* R).comp (e : R →+* S) = RingHom.id R := by
      ext x; simp
    have hIK : I ≤ I.comap ((e.symm : S →+* R).comp (e : R →+* S)) := by
      rw [hid]; exact (Ideal.comap_id I).ge
    rw [← locallyRingedSpaceMap_comp I J I (e : R →+* S) (e.symm : S →+* R) h h' hIK,
      locallyRingedSpaceMap_congr I I _ (RingHom.id R) hIK (Ideal.comap_id I).ge hid,
      locallyRingedSpaceMap_id]
  inv_hom_id := by
    have hid : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S := by
      ext x; simp
    have hJK : J ≤ J.comap ((e : R →+* S).comp (e.symm : S →+* R)) := by
      rw [hid]; exact (Ideal.comap_id J).ge
    rw [← locallyRingedSpaceMap_comp J I J (e.symm : S →+* R) (e : R →+* S) h' h hJK,
      locallyRingedSpaceMap_congr J J _ (RingHom.id S) hJK (Ideal.comap_id J).ge hid,
      locallyRingedSpaceMap_id]

@[simp]
theorem locallyRingedSpaceMapIso_hom (e : R ≃+* S) (h : I ≤ J.comap (e : R →+* S))
    (h' : J ≤ I.comap (e.symm : S →+* R)) :
    (locallyRingedSpaceMapIso I J e h h').hom =
      locallyRingedSpaceMap J I (e.symm : S →+* R) h' :=
  rfl

@[simp]
theorem locallyRingedSpaceMapIso_inv (e : R ≃+* S) (h : I ≤ J.comap (e : R →+* S))
    (h' : J ≤ I.comap (e.symm : S →+* R)) :
    (locallyRingedSpaceMapIso I J e h h').inv = locallyRingedSpaceMap I J (e : R →+* S) h :=
  rfl

/-- **The same, from the one hypothesis it usually arrives with.** An ideal of definition
transported along a ring isomorphism satisfies `I.map e = J`, and both continuity conditions
follow: the forward one from `Ideal.le_comap_map`, the backward one from
`Ideal.map_le_iff_le_comap` together with `RingEquiv.symm_apply_apply`. (Mathlib's
`Ideal.comap_symm` is the same fact, but it is stated at the `RingEquiv` coercion of `Ideal.comap`
rather than the `RingHom` one this file's hypotheses use, so it does not `rw` here.) -/
def locallyRingedSpaceMapIsoOfMapEq (e : R ≃+* S) (he : I.map (e : R →+* S) = J) :
    locallyRingedSpaceObj I ≅ locallyRingedSpaceObj J :=
  locallyRingedSpaceMapIso I J e (he ▸ Ideal.le_comap_map)
    (by
      rw [← he, Ideal.map_le_iff_le_comap]
      intro x hx
      simpa using hx)

end FormalSpectrum
