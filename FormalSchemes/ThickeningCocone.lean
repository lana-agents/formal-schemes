import FormalSchemes.Thickenings
import FormalSchemes.SpfFunctorial

set_option linter.style.header false

/-!
# The thickening morphisms form a cocone over the tower (EGA I, 10.6.3), packaged

`FormalSchemes/Thickenings.lean` builds the canonical morphisms of locally ringed spaces
`FormalSpectrum.thickeningMap I n : Spec (R ⧸ I ^ (n + 1)) ⟶ Spf R` and states their
compatibility with the tower transition maps only *componentwise*
(`thickeningMap_base_comp` on spaces, `thickeningMap_c_comp` on structure sheaves), noting that
packaging them into a single equation of morphisms requires transporting the sheaf component along
the equality of base maps (an `eqToHom` conjugation).

That conjugation technique is now available (`FormalSchemes/SpfFunctorial.lean`, issue 60). This
file assembles the two components into the single cocone equation

```
Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ thickeningMap I (n + 1) = thickeningMap I n
```

exhibiting `n ↦ Spec (R ⧸ I ^ (n + 1))` with `thickeningMap` as a genuine cocone over the tower in
`LocallyRingedSpace`.

## References

* [Grothendieck, *EGA I*][EGA1], §10.6 (10.6.3)
-/

noncomputable section

open CategoryTheory Limits TopCat AlgebraicGeometry

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I] (n : ℕ)

-- The `c`-component reconciliation compares the pushed-forward `StructureSheaf.comap` of the Spec
-- transition map against `stepSheafHom`, which unfolds the section rings; splitting the composite
-- `NatTrans` along the base-map `eqToHom` transport requires relaxing the transparency at which
-- `rw` builds its motive, and unfolding the section rings is slow for the kernel.
omit [TopologicalSpace R] [IsAdicRing I] in
set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
-- unfolding the section rings in the `c`-component reconciliation (see the comment above) is slow
-- for the kernel, so we raise the heartbeat limit generously.
/-- **Cocone condition, packaged** (EGA I, 10.6.3): the transition map of the tower of thickenings
`Spec (R ⧸ I ^ (n + 1)) ⟶ Spec (R ⧸ I ^ (n + 2))`, followed by the canonical morphism
`thickeningMap I (n + 1)` into the formal spectrum, equals `thickeningMap I n`. The two morphisms of
locally ringed spaces agree — their underlying continuous maps by `thickeningMap_base_comp` and
their structure-sheaf components by `thickeningMap_c_comp`, reconciled through the base-map
transport (an `eqToHom` conjugation). -/
theorem thickeningMap_comp :
    Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ thickeningMap I (n + 1) = thickeningMap I n := by
  apply LocallyRingedSpace.Hom.ext'
  rw [LocallyRingedSpace.comp_toHom, Spec.locallyRingedSpaceMap_toHom]
  refine PresheafedSpace.ext _ _ (topMap_stepRingHom_comp_inv I n) ?_
  rw [CategoryTheory.Functor.whiskerRight_eqToHom_aux]
  refine NatTrans.ext (funext fun U => ?_)
  induction U using Opposite.rec with
  | op V =>
    rw [NatTrans.comp_app, PresheafedSpace.comp_c_app, eqToHom_app,
      Spec.sheafedSpaceMap_hom_c_app, Category.assoc]
    erw [StructureSheaf.comap_ofHom_target_eq (stepRingHom I n).hom
      (thickeningOpen I (n + 1) V) (map_topMap_thickeningOpen I n V)]
    rw [← stepSheafHom_hom_app]
    exact congrArg (fun f => f.hom.app (Opposite.op V)) (thickeningMap_c_comp I n)

end FormalSpectrum

