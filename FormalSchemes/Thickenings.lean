import FormalSchemes.Spf

set_option linter.style.header false

/-!
# The infinitesimal thickenings inside the formal spectrum

The formal spectrum `Spf R` of an adic ring contains each of its infinitesimal thickenings
`Spec (R ⧸ I ^ (n + 1))` as a closed subscheme, and is the union ("inductive limit") of them:
EGA I, 10.6.3. This file constructs the canonical morphisms of locally ringed spaces

```
Spec (R ⧸ I ^ (n + 1)) ⟶ Spf R
```

— a homeomorphism on spaces, the level-`n` projection of the defining limit on structure
sheaves — and shows they form a cocone over the tower of thickenings, i.e. are compatible with
the closed immersions `Spec (R ⧸ I ^ (n + 1)) ↪ Spec (R ⧸ I ^ (n + 2))`.

The essential point for the locally-ringed structure is that the stalk maps are local. This
follows from a general fact about the tower proved here: a germ of `O_{Spf R}` whose image in
the level-`n` sheaf is invertible is invertible (`FormalSpectrum.isUnit_of_isUnit_stalkProj`),
since the level-`n` germ maps onto the level-`0` germ and `isUnit_stalk_of_isUnit_zero`
applies. The stalk map of the thickening morphism is exactly `stalkProj` followed by an
isomorphism (pushforward along a homeomorphism), so locality follows.

## Main definitions and results

* `FormalSpectrum.isUnit_of_isUnit_stalkProj`: invertibility of a germ is detected at any
  level of the tower.
* `FormalSpectrum.thickeningMap I n : Spec.locallyRingedSpaceObj (R ⧸ I ^ (n + 1)) ⟶
  locallyRingedSpaceObj I`: the canonical morphism of locally ringed spaces.
* `FormalSpectrum.thickeningMap_base_comp`, `FormalSpectrum.thickeningMap_c_comp`: the
  morphisms are compatible with the tower (the cocone conditions, on spaces and on sheaves).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

namespace FormalSpectrum

omit [TopologicalSpace R] [IsAdicRing I]

/-!
### Invertibility is detected at any level of the tower
-/

section StalkProj

variable (x : FormalSpectrum I) (n : ℕ)

/-- **Invertibility of a germ of `O_{Spf R}` is detected at any level of the tower**: if the
image of a germ in the level-`n` thickening sheaf is a unit, the germ is a unit. -/
theorem isUnit_of_isUnit_stalkProj (a : (structureSheaf I).presheaf.stalk x)
    (h : IsUnit ((stalkProj I x n).hom a)) : IsUnit a := by
  refine isUnit_stalk_of_isUnit_zero I x a ?_
  -- the level-`n` projection factors the level-`0` one, along the tower
  have hw : limit.π (structureSheafFunctor I) ⟨n⟩ ≫
      (structureSheafFunctor I).map (homOfLE (Nat.zero_le n)).op =
      limit.π (structureSheafFunctor I) ⟨0⟩ :=
    limit.w (structureSheafFunctor I) (homOfLE (Nat.zero_le n)).op
  have hfun : stalkProj I x 0 =
      stalkProj I x n ≫ (TopCat.Presheaf.stalkFunctor CommRingCat x).map
        ((structureSheafFunctor I).map (homOfLE (Nat.zero_le n)).op).hom := by
    rw [stalkProj, stalkProj, ← hw]
    exact (Functor.map_comp _ _ _)
  have happ : (stalkProj I x 0).hom a =
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        ((structureSheafFunctor I).map (homOfLE (Nat.zero_le n)).op).hom).hom
        ((stalkProj I x n).hom a) := by
    rw [hfun]
    rfl
  rw [happ]
  exact h.map _

end StalkProj

/-!
### The canonical morphisms from the thickenings
-/

section ThickeningMap

variable (n : ℕ)

/-- The morphism of presheafed spaces `Spec (R ⧸ I ^ (n + 1)) ⟶ Spf R`: the thickening
homeomorphism on spaces, the level-`n` projection of the defining limit on sheaves. -/
def thickeningPresheafedSpaceMap :
    (Spec.sheafedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).toPresheafedSpace ⟶
      (sheafedSpaceObj I).toPresheafedSpace where
  base := (thickeningTopIso I n).inv
  c := (limit.π (structureSheafFunctor I) ⟨n⟩).hom

@[simp]
theorem thickeningPresheafedSpaceMap_base :
    (thickeningPresheafedSpaceMap I n).base = (thickeningTopIso I n).inv :=
  rfl

/-- The stalk map of the thickening morphism is the level-`n` projection on stalks, followed by
the isomorphism given by pushforward along the thickening homeomorphism. -/
theorem stalkMap_eq (y : Spec.topObj (CommRingCat.of (R ⧸ I ^ (n + 1))))
    (a : (structureSheaf I).presheaf.stalk ((thickeningTopIso I n).inv y)) :
    ((thickeningPresheafedSpaceMap I n).stalkMap y).hom a =
      (TopCat.Presheaf.stalkPushforward CommRingCat (thickeningTopIso I n).inv
        (Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf y).hom
        ((stalkProj I ((thickeningTopIso I n).inv y) n).hom a) :=
  rfl

/-- The stalk maps of the thickening morphism are local ring homomorphisms. -/
theorem isLocalHom_thickening_stalkMap
    (y : Spec.topObj (CommRingCat.of (R ⧸ I ^ (n + 1)))) :
    IsLocalHom ((thickeningPresheafedSpaceMap I n).stalkMap y).hom := by
  haveI hiso : IsIso (TopCat.Presheaf.stalkPushforward CommRingCat (thickeningTopIso I n).inv
      (Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf y) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      (C := CommRingCat) (f := (thickeningTopIso I n).inv)
      ((thickeningHomeomorph I (n + 1) n.succ_ne_zero).symm.isInducing)
      ((Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf) y
  constructor
  intro a ha
  rw [stalkMap_eq] at ha
  -- the pushforward factor is an isomorphism, so the level-`n` projection of `a` is a unit
  refine isUnit_of_isUnit_stalkProj I _ n a ?_
  have h2 := ha.map (CategoryTheory.inv (TopCat.Presheaf.stalkPushforward CommRingCat
    (thickeningTopIso I n).inv (Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf y)).hom
  have hid : (CategoryTheory.inv (TopCat.Presheaf.stalkPushforward CommRingCat
        (thickeningTopIso I n).inv
        (Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf y)).hom
      ((TopCat.Presheaf.stalkPushforward CommRingCat (thickeningTopIso I n).inv
        (Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf y).hom
        ((stalkProj I ((thickeningTopIso I n).inv y) n).hom a)) =
      (stalkProj I ((thickeningTopIso I n).inv y) n).hom a := by
    simp
  change IsUnit ((stalkProj I ((thickeningTopIso I n).inv y) n).hom a)
  rw [← hid]
  exact h2

/-- **The canonical morphism from a thickening into the formal spectrum** (EGA I, 10.6):
`Spec (R ⧸ I ^ (n + 1)) ⟶ Spf R`, as a morphism of locally ringed spaces. -/
def thickeningMap :
    Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶
      locallyRingedSpaceObj I where
  toHom := thickeningPresheafedSpaceMap I n
  prop y := isLocalHom_thickening_stalkMap I n y

@[simp]
theorem thickeningMap_base :
    (thickeningMap I n).base = (thickeningTopIso I n).inv :=
  rfl

/-!
### Compatibility with the tower

The canonical morphisms are compatible with the closed immersions of the thickenings into one
another, i.e. they form a cocone over the tower (EGA I, 10.6.3). We state the two components
separately: the underlying continuous maps compose correctly, and so do the maps of structure
sheaves. Packaging these into a single equation of morphisms of presheafed spaces requires
transporting the sheaf component along the equality of base maps (an `eqToHom` conjugation),
which is not needed for the applications.
-/

/-- Cocone condition on spaces: the transition map of the tower, followed by the thickening
homeomorphism at level `n + 1`, is the thickening homeomorphism at level `n`. -/
theorem thickeningMap_base_comp :
    Spec.topMap (stepRingHom I n) ≫ (thickeningPresheafedSpaceMap I (n + 1)).base =
      (thickeningPresheafedSpaceMap I n).base :=
  topMap_stepRingHom_comp_inv I n

/-- Cocone condition on structure sheaves: the level-`(n + 1)` projection of the defining
limit, followed by the transition map of the tower of thickening sheaves, is the level-`n`
projection. -/
theorem thickeningMap_c_comp :
    limit.π (structureSheafFunctor I) ⟨n + 1⟩ ≫ stepSheafHom I n =
      limit.π (structureSheafFunctor I) ⟨n⟩ := by
  have h := limit.w (structureSheafFunctor I) (homOfLE (Nat.le_add_right n 1)).op
  rwa [structureSheafFunctor_map_succ] at h

end ThickeningMap

end FormalSpectrum
