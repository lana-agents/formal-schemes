import FormalSchemes.ThickeningCocone

set_option linter.style.header false

/-!
# The thickening morphisms are natural in the adic ring (EGA I, 10.6.3)

`FormalSchemes/Thickenings.lean` builds the canonical morphism
`FormalSpectrum.thickeningMap I n : Spec (R ⧸ Iⁿ⁺¹) ⟶ Spf R`, and
`FormalSchemes/ThickeningCocone.lean` proves it is compatible with the transition maps *of one
tower*. This file proves the other compatibility: it is compatible with a **map of adic rings**.

For `φ : R →+* S` with `I ≤ J.comap φ`, the square

```
Spec (S ⧸ Jⁿ⁺¹)  ──────────────→  Spf S
      │  Spec (levelRingHom)          │  Spf φ
      ↓                               ↓
Spec (R ⧸ Iⁿ⁺¹)  ──────────────→  Spf R
```

commutes (`thickeningMap_comp_locallyRingedSpaceMap`). This is what turns a morphism of formal
spectra that is `Spf` of a *ring map* into something a statement about thickenings can consume,
and nothing on the tree said it: no lemma in `FormalSchemes/` mentioned both `thickeningMap` and
`locallyRingedSpaceMap`.

The immediate consumer is the overlap agreement of `FormalSchemes/ChartSpfHomOverlap.lean`, where
the two legs `Spf A{1/(r·s)} ⟶ Spf A{1/r}`, `⟶ Spf A{1/s}` of the basic-open chart overlap are
`FormalSpectrum.locallyRingedSpaceMap` of concrete ring maps while `chartSpfHomAmbient` is
characterised by its restrictions to thickenings. This square is the only bridge between the two
descriptions.

## Route

Both halves are already on the tree and neither is re-proved here:

* on spaces, `comap_levelRingHom_toThickening` (`SpfMap.lean`) is the square, pointwise;
* on structure sheaves, `mapSheafHom_π` (`SpfMap.lean`) says `mapSheafHom` commutes with the limit
  projections, and the sheaf component of `thickeningMap` **is** the projection (`Thickenings.lean`,
  definitionally, recorded as `thickeningMap_c_app`).

What is left is the reconciliation of the two sheaf components across the propositional equality of
the base maps, and that is done exactly as `ThickeningCocone.lean` does it — `PresheafedSpace.ext`,
`Functor.whiskerRight_eqToHom_aux`, and `StructureSheaf.comap_ofHom_target_eq` to absorb the
resulting `eqToHom` into the target open of a `StructureSheaf.comap`. Both of those helpers come
from `SpfFunctorial.lean`.

## Implementation notes

`ThickeningCocone.lean`'s rule applies verbatim here and is why
`thickeningMap_c_app_levelSheafHom` takes its containment proof as a **hypothesis** rather than
naming `thickeningOpen_map_le`: handing the kernel a second spelling of that proof makes it
reconcile two `StructureSheaf.comap` types, which it can only do by unfolding the section rings of
`Spec`'s structure sheaf. Read that module's docstring before touching this one; the measured cost
there was 11.5 GB for a single argument. Applying the lemma with `_` in that position keeps the
goal's own proof term in place, and this module elaborates in a few seconds.

`thickeningMap_comp_locallyRingedSpaceMap` needs `backward.isDefEq.respectTransparency false` for
the same reason `thickeningMap_comp` does: after `PresheafedSpace.ext` the goal mixes the
`TopCat.Presheaf` spelling of `(locallyRingedSpaceObj I).presheaf` with the plain functor-category
one, which are `rfl` but not at `instances` transparency, so `rw` refuses to build a motive.

## Main results

* `FormalSpectrum.thickeningMap_comp_locallyRingedSpaceMap`: **the square**, `@[reassoc]`.
* `FormalSpectrum.thickeningTopIso_inv_comp_mapTop` and
  `FormalSpectrum.map_topMap_thickeningOpen_levelRingHom`: its base-map half, as a morphism of
  `TopCat` and as an equality of opens.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.2 (10.2.2), §10.6 (10.6.3).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S) (φ : R →+* S) (hφ : I ≤ J.comap φ) (n : ℕ)

/-- **The base-map half of the square**, in `TopCat`: the thickening homeomorphism of `Spf S`
followed by `Spf φ` is `Spec` of the induced map of thickenings followed by the thickening
homeomorphism of `Spf R`. This is `comap_levelRingHom_toThickening` bundled. -/
theorem thickeningTopIso_inv_comp_mapTop :
    (thickeningTopIso J n).inv ≫ mapTop I J φ hφ =
      Spec.topMap (CommRingCat.ofHom (levelRingHom I J φ hφ n)) ≫ (thickeningTopIso I n).inv := by
  ext y
  exact (comap_levelRingHom_toThickening I J φ hφ n y).symm

/-- **The base-map half, read on opens**: the preimage under `Spec (levelRingHom)` of the open of
the `n`-th thickening of `Spf R` cut out by `V` is the open of the `n`-th thickening of `Spf S` cut
out by the preimage of `V`. Compare `thickeningOpen_map_le`, which is the containment this refines
to an equality, and `map_topMap_thickeningOpen`, which is the same statement for the transition map
of one tower. -/
theorem map_topMap_thickeningOpen_levelRingHom (V : Opens (FormalSpectrum I)) :
    (Opens.map (Spec.topMap (CommRingCat.ofHom (levelRingHom I J φ hφ n)))).obj
        (thickeningOpen I n V) =
      thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj V) := by
  apply Opens.ext
  ext y
  exact Iff.of_eq (congrArg (· ∈ V) (comap_levelRingHom_toThickening I J φ hφ n y))

/-- **The sheaf half of the square**, over a single open `V ⊆ Spf R`: `mapSheafHom` followed by the
level-`n` projection of `Spf S` is the level-`n` projection of `Spf R` followed by the map on
sections induced by `levelRingHom`. This is `mapSheafHom_π` read through `thickeningMap_c_app`.

The containment proof `h` is deliberately a hypothesis rather than `thickeningOpen_map_le`; see
the module docstring and, at length, `ThickeningCocone.lean`'s. -/
theorem thickeningMap_c_app_levelSheafHom (V : Opens (FormalSpectrum I))
    (h : (thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj V) :
        Set (PrimeSpectrum (S ⧸ J ^ (n + 1)))) ⊆
      PrimeSpectrum.comap (levelRingHom I J φ hφ n) ⁻¹'
        (thickeningOpen I n V : Set (PrimeSpectrum (R ⧸ I ^ (n + 1))))) :
    (mapSheafHom I J φ hφ).hom.app (op V) ≫
        (thickeningMap J n).c.app (op ((Opens.map (mapTop I J φ hφ)).obj V)) =
      (thickeningMap I n).c.app (op V) ≫
        CommRingCat.ofHom (StructureSheaf.comap (levelRingHom I J φ hφ n)
          (thickeningOpen I n V) (thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj V)) h) := by
  rw [thickeningMap_c_app, thickeningMap_c_app]
  exact congrArg (fun t => t.hom.app (op V)) (mapSheafHom_π I J φ hφ n)

set_option linter.style.setOption false in
-- Splitting the composite `NatTrans` along the base-map `eqToHom` transport requires relaxing the
-- transparency at which `rw` builds its motive; see the module docstring.
set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of the thickening morphisms in the adic ring** (EGA I, 10.2.2 against 10.6.3): the
`n`-th thickening of `Spf S` maps to the `n`-th thickening of `Spf R` compatibly with `Spf φ`,

```
thickeningMap J n ≫ Spf φ = Spec (levelRingHom I J φ hφ n) ≫ thickeningMap I n.
```

The base maps agree by `comap_levelRingHom_toThickening` and the sheaf maps by `mapSheafHom_π`;
the whole proof is the reconciliation of the two across the base-map transport. -/
@[reassoc]
theorem thickeningMap_comp_locallyRingedSpaceMap :
    thickeningMap J n ≫ locallyRingedSpaceMap I J φ hφ =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom (levelRingHom I J φ hφ n)) ≫
        thickeningMap I n := by
  symm
  apply LocallyRingedSpace.Hom.ext'
  rw [LocallyRingedSpace.comp_toHom, LocallyRingedSpace.comp_toHom,
    Spec.locallyRingedSpaceMap_toHom]
  refine PresheafedSpace.ext _ _ (thickeningTopIso_inv_comp_mapTop I J φ hφ n).symm ?_
  rw [CategoryTheory.Functor.whiskerRight_eqToHom_aux]
  refine NatTrans.ext (funext fun U => ?_)
  induction U using Opposite.rec with
  | op V =>
    rw [NatTrans.comp_app, PresheafedSpace.comp_c_app, PresheafedSpace.comp_c_app, eqToHom_app,
      Spec.sheafedSpaceMap_hom_c_app, Category.assoc]
    erw [StructureSheaf.comap_ofHom_target_eq (levelRingHom I J φ hφ n) (thickeningOpen I n V)
      (map_topMap_thickeningOpen_levelRingHom I J φ hφ n V)]
    exact (thickeningMap_c_app_levelSheafHom I J φ hφ n V _).symm

end FormalSpectrum
