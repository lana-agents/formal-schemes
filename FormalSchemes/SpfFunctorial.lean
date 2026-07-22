import FormalSchemes.SpfMap

set_option linter.style.header false

/-!
# Functoriality of the formal spectrum: identity and composition laws

`FormalSchemes/SpfMap.lean` constructs, for a continuous ring homomorphism `φ : R →+* S`
between adic rings (`I ≤ J.comap φ`), the induced morphism of locally ringed spaces
`FormalSpectrum.locallyRingedSpaceMap I J φ hφ : Spf S ⟶ Spf R` and the affine-formal-scheme
morphism `FormalSpectrum.spfMap`. This file develops the functoriality of `Spf` (EGA I, 10.2),
towards exhibiting it as a (contravariant) functor on adic rings and continuous ring homs.

## Main results

* `levelRingHom_id`/`levelRingHom_comp`: the induced maps of thickenings `R ⧸ Iⁿ⁺¹ → S ⧸ Jⁿ⁺¹`
  respect identity and composition.
* `mapTop_id`/`mapTop_comp`: the underlying continuous maps `Spf S → Spf R` respect identity and
  composition (contravariantly).
* `locallyRingedSpaceMap_congr`: the induced morphism of locally ringed spaces depends only on the
  ring homomorphism, not on the chosen continuity proof.
* `levelSheafHom_id`: the level-`n` map of thickening sheaves induced by the identity is the
  canonical transport `eqToHom` (the identity up to the propositional equality `mapTop_id`).

The remaining, harder identity/composition laws **at the level of locally ringed spaces**
(`locallyRingedSpaceMap_id : Spf (id R) = 𝟙 (Spf R)` and the composition law) are left as a
follow-up: since the underlying base maps are only *propositionally* equal (`mapTop_id`/
`mapTop_comp`), the equality of the sheaf components carries the `eqToHom`/`whiskerRight`
conjugation that `FormalSchemes/Thickenings.lean` (lines 161-186) deliberately sidesteps for the
thickening cocone. `levelSheafHom_id` and the pushforward-transport lemmas
`thickeningSheaf_pushforward_mapTop_id`/`structureSheaf_pushforward_mapTop_id` below are the
first steps of that argument; the outstanding piece is the `eqToHom`-naturality square relating
`mapSheafHom_π` at each level to the transport (see the module comment before
`levelSheafHom_id`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.2.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable (I : Ideal R) (J : Ideal S) (K : Ideal T)

/-!
### Functoriality of the induced maps of thickenings
-/

section LevelMaps

/-- The map of thickenings induced by the identity is the identity. -/
theorem levelRingHom_id (n : ℕ) :
    levelRingHom I I (RingHom.id R) (Ideal.comap_id I).ge n = RingHom.id (R ⧸ I ^ (n + 1)) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
  simp [levelRingHom_mk]

/-- The map of thickenings induced by a composite is the composite of the induced maps. -/
theorem levelRingHom_comp (φ : R →+* S) (ψ : S →+* T) (hIJ : I ≤ J.comap φ)
    (hJK : J ≤ K.comap ψ) (hIK : I ≤ K.comap (ψ.comp φ)) (n : ℕ) :
    levelRingHom I K (ψ.comp φ) hIK n =
      (levelRingHom J K ψ hJK n).comp (levelRingHom I J φ hIJ n) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
  simp [levelRingHom_mk]

end LevelMaps

/-!
### Functoriality of the underlying continuous maps
-/

section BaseMap

/-- The underlying continuous map induced by the identity is the identity. -/
theorem mapTop_id :
    mapTop I I (RingHom.id R) (Ideal.comap_id I).ge = 𝟙 (TopCat.of (FormalSpectrum I)) := by
  refine TopCat.ext fun x => ?_
  exact congrFun (map_id I) x

/-- The underlying continuous map induced by a composite is the composite (contravariantly) of
the induced maps. -/
theorem mapTop_comp (φ : R →+* S) (ψ : S →+* T) (hIJ : I ≤ J.comap φ) (hJK : J ≤ K.comap ψ)
    (hIK : I ≤ K.comap (ψ.comp φ)) :
    mapTop I K (ψ.comp φ) hIK = mapTop J K ψ hJK ≫ mapTop I J φ hIJ := by
  refine TopCat.ext fun x => ?_
  change map I K (ψ.comp φ) hIK x = map I J φ hIJ (map J K ψ hJK x)
  rw [map_comp I J K φ ψ hIJ hJK hIK]
  rfl

end BaseMap

/-!
### Congruence in the ring homomorphism
-/

section Congr

variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J] in
/-- The induced morphism of locally ringed spaces depends only on the ring homomorphism, not on
the proof of continuity. -/
theorem locallyRingedSpaceMap_congr (φ₁ φ₂ : R →+* S) (h₁ : I ≤ J.comap φ₁)
    (h₂ : I ≤ J.comap φ₂) (hφ : φ₁ = φ₂) :
    locallyRingedSpaceMap I J φ₁ h₁ = locallyRingedSpaceMap I J φ₂ h₂ := by
  subst hφ
  rfl

end Congr

/-!
### Transport lemmas for the identity, towards `locallyRingedSpaceMap_id`

Since `mapTop I I (id) = 𝟙` only *propositionally* (`mapTop_id`), pushing a thickening / structure
sheaf forward along the identity map recovers it, but only up to a transport `eqToHom`. These
lemmas record those transports and identify the level-`n` sheaf map of the identity with the
transport. The one outstanding step for the full `locallyRingedSpaceMap_id : Spf (id) = 𝟙` is the
`eqToHom`-naturality square matching `mapSheafHom_π` at each level against
`structureSheaf_pushforward_mapTop_id` — the same `eqToHom`/`whiskerRight` conjugation flagged in
`FormalSchemes/Thickenings.lean` (lines 161-186).
-/

section IdentityTransport

/-- Pushing forward the `n`-th thickening sheaf along the identity map recovers it. -/
theorem thickeningSheaf_pushforward_mapTop_id (n : ℕ) :
    thickeningSheaf I n =
      (TopCat.Sheaf.pushforward CommRingCat (mapTop I I (RingHom.id R) (Ideal.comap_id I).ge)).obj
        (thickeningSheaf I n) := by
  rw [mapTop_id]
  rfl

/-- Pushing forward the structure sheaf along the identity map recovers it. -/
theorem structureSheaf_pushforward_mapTop_id :
    structureSheaf I =
      (TopCat.Sheaf.pushforward CommRingCat (mapTop I I (RingHom.id R) (Ideal.comap_id I).ge)).obj
        (structureSheaf I) := by
  rw [mapTop_id]
  rfl

/-- The level-`n` sheaf map induced by the identity is the canonical transport isomorphism. -/
theorem levelSheafHom_id (n : ℕ) :
    levelSheafHom I I (RingHom.id R) (Ideal.comap_id I).ge n =
      eqToHom (thickeningSheaf_pushforward_mapTop_id I n) := by
  refine InducedCategory.Hom.ext (NatTrans.ext (funext fun U => ?_))
  induction U using Opposite.rec with
  | op V =>
    rw [levelSheafHom_hom_app]
    simp only [levelRingHom_id]
    rw [StructureSheaf.comap_id (show thickeningOpen I n V =
      thickeningOpen I n ((Opens.map (mapTop I I (RingHom.id R) (Ideal.comap_id I).ge)).obj V)
        by rw [mapTop_id, Opens.map_id_obj])]
    rw [show (eqToHom (thickeningSheaf_pushforward_mapTop_id I n)
          : thickeningSheaf I n ⟶ _).hom =
        eqToHom (congrArg ObjectProperty.FullSubcategory.obj
          (thickeningSheaf_pushforward_mapTop_id I n)) from by
      rw [← ObjectProperty.ι_map]
      exact eqToHom_map _ _]
    rw [eqToHom_app, CommRingCat.ofHom_hom]
    rfl

end IdentityTransport

end FormalSpectrum
