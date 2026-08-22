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

## Implementation notes: never write down the containment proof of a `StructureSheaf.comap`

Read this before touching the proof of `thickeningMap_comp` (issue 711). As originally written,
this module cost **310 s and 14.25 GB of kernel type-checking** against 9 s of elaboration, which
put it at the memory ceiling of the build box. All of that cost came from a *single argument*.

`StructureSheaf.comap f U W h` takes, as its last argument, a proof `h` that `W` is contained in
the preimage of `U`. Whenever a proof term hands the kernel its own spelling of that `h` — as
`rw [← stepSheafHom_hom_app]` does, and as `exact` against any freshly stated auxiliary lemma
does — the kernel has to reconcile that spelling with the one already sitting in the goal. Proof
irrelevance does not make this free: it first has to decide that the two proofs' *types* agree,
and those types mention the section rings of `Spec`'s structure sheaf, which it can only compare
by unfolding them. That single reconciliation is the whole 11.5 GB. It is not the limit, not the
`eqToHom` transport, and not the opens: bisecting the final `show` one sub-term at a time gives

| sub-term spelled explicitly, rest left as `_` | peak |
| :-- | --: |
| `CommRingCat.ofHom _` | 2.77 GB |
| the ring map `(stepRingHom I n).hom` | 2.80 GB |
| both opens `thickeningOpen I (n + 1) V`, `thickeningOpen I n V` | 2.78 GB |
| **the containment proof `thickeningOpen_le_comap I n V`** | **14.26 GB** |

So the rule for this file, and for anything else reconciling `StructureSheaf.comap`s:

> Keep the containment proof an *opaque variable*. State the auxiliary lemma with `h` as a
> hypothesis and apply it with `_` in that position, so the goal's own proof term is what gets
> substituted and no cross-spelling comparison ever happens.

That is what `thickeningMap_c_app_comp` below does, and it takes the module to **9 s / 2.78 GB**
— the cost of its imports. The companion `thickeningMap_c_app` is the same idea applied to the
bundled `thickeningMap`: hoisting its one delta-unfolding into a top-level `rfl` lemma, where the
kernel compares two morphisms rather than two equations (issue 737).

## References

* [Grothendieck, *EGA I*][EGA1], §10.6 (10.6.3)
-/

noncomputable section

open CategoryTheory Limits TopCat AlgebraicGeometry

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I] (n : ℕ)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The sheaf component of `thickeningMap I n` over an open `V ⊆ Spf R` is the level-`n`
projection of the defining limit. True by definition; stating it separately is what keeps the
kernel from delta-unfolding the bundled `thickeningMap` inside an equation (see the module
docstring). -/
theorem thickeningMap_c_app (V : TopologicalSpace.Opens (FormalSpectrum I)) :
    (thickeningMap I n).c.app (Opposite.op V) =
      (limit.π (structureSheafFunctor I) ⟨n⟩).hom.app (Opposite.op V) :=
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `c`-component of the cocone condition**, over a single open `V ⊆ Spf R`: the
level-`(n + 1)` sheaf component of `thickeningMap`, followed by the map on sections induced by the
surjection `R ⧸ I ^ (n + 2) →+* R ⧸ I ^ (n + 1)`, is the level-`n` sheaf component. This is
`thickeningMap_c_comp` read through `thickeningMap_c_app` and the definition of `stepSheafHom`.

The containment proof `h` is deliberately a hypothesis rather than `thickeningOpen_le_comap I n V`:
see the module docstring — supplying it here instead of letting the caller's own proof term be
substituted costs the kernel 11.5 GB. -/
theorem thickeningMap_c_app_comp (V : TopologicalSpace.Opens (FormalSpectrum I))
    (h : (thickeningOpen I n V : Set (PrimeSpectrum (R ⧸ I ^ (n + 1)))) ⊆
      PrimeSpectrum.comap (stepRingHom I n).hom ⁻¹'
        (thickeningOpen I (n + 1) V : Set (PrimeSpectrum (R ⧸ I ^ (n + 1 + 1))))) :
    (thickeningMap I (n + 1)).c.app (Opposite.op V) ≫
        CommRingCat.ofHom (StructureSheaf.comap (stepRingHom I n).hom
          (thickeningOpen I (n + 1) V) (thickeningOpen I n V) h) =
      (thickeningMap I n).c.app (Opposite.op V) := by
  rw [thickeningMap_c_app, thickeningMap_c_app]
  exact congrArg (fun f => f.hom.app (Opposite.op V)) (thickeningMap_c_comp I n)

-- Splitting the composite `NatTrans` along the base-map `eqToHom` transport requires relaxing the
-- transparency at which `rw` builds its motive.
omit [TopologicalSpace R] [IsAdicRing I] in
set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
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
    exact thickeningMap_c_app_comp I n V _

end FormalSpectrum
