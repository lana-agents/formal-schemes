/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial

set_option linter.style.header false

/-!
# The empty / initial object in `LocallyRingedSpace`

Mathlib records the empty locally ringed space `∅ : LocallyRingedSpace` together with the initial
witness `LocallyRingedSpace.emptyIsInitial`, but — unlike the situation for `Scheme`
(`AlgebraicGeometry.Limits`) — it does not register the surrounding infrastructure: that a morphism
out of a space with empty carrier is an open immersion, that `LocallyRingedSpace` has an initial
object, or that the initial object is strict. This file supplies exactly that, mirroring the
`Scheme`-level proofs.

The motivation is gluing: an `AlgebraicGeometry.LocallyRingedSpace.GlueData` (hence a
`FormalScheme.GlueData`) indexed by a poset such as `ℤ` in which only *some* pairs of patches
overlap must use the initial object as the overlap `V (i, j)` for the non-overlapping pairs, with
the structural map `V (i, j) ⟶ U i` an open immersion. The flagship example is the Tate chain
(issue 208): consecutive formal annuli overlap, non-consecutive ones do not, so the ℤ-indexed glue
datum needs `∅` as the overlap of non-adjacent patches.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_of_isEmpty`: a morphism whose source has
  empty carrier is an open immersion.
* `AlgebraicGeometry.LocallyRingedSpace.isIso_of_isEmpty`: a morphism whose *target* has empty
  carrier is an isomorphism.
* `AlgebraicGeometry.LocallyRingedSpace.isInitialOfIsEmpty`: a locally ringed space with empty
  carrier is initial.
* `CategoryTheory.Limits.HasInitial LocallyRingedSpace` and
  `CategoryTheory.Limits.HasStrictInitialObjects LocallyRingedSpace` instances.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}}

/-- A morphism out of a locally ringed space with **empty carrier** is an open immersion: the base
map is an open embedding (its domain is empty) and every stalk map is (vacuously) an isomorphism.
This is the `LocallyRingedSpace` analogue of `AlgebraicGeometry.isOpenImmersion_of_isEmpty`. -/
instance (priority := 100) isOpenImmersion_of_isEmpty (f : X ⟶ Y) [he : IsEmpty X] :
    LocallyRingedSpace.IsOpenImmersion f := by
  haveI : IsEmpty (↑↑X.toPresheafedSpace) := he
  haveI : ∀ x : X.toTopCat, IsIso (f.stalkMap x) := fun x => isEmptyElim (α := X) x
  exact LocallyRingedSpace.IsOpenImmersion.of_stalk_iso f (Topology.IsOpenEmbedding.of_isEmpty _)

/-- The empty locally ringed space has empty carrier. -/
instance instIsEmptyEmpty : IsEmpty (∅ : LocallyRingedSpace.{u}) :=
  show IsEmpty PEmpty from inferInstance

/-- A morphism into a locally ringed space with **empty carrier** is an isomorphism: the source is
then empty too, the base map is an open immersion (empty source) and surjective (empty target), and
a surjective open immersion is an isomorphism. The `LocallyRingedSpace` analogue of
`AlgebraicGeometry.isIso_of_isEmpty`. -/
instance (priority := 100) isIso_of_isEmpty (f : X ⟶ Y) [hY : IsEmpty Y] : IsIso f := by
  haveI : IsEmpty (↑↑Y.toPresheafedSpace) := hY
  haveI : IsEmpty X := Function.isEmpty (⇑f.base)
  haveI : Epi f.base := by
    rw [TopCat.epi_iff_surjective]; rintro (y : Y); exact isEmptyElim y
  exact LocallyRingedSpace.IsOpenImmersion.to_iso f

/-- A locally ringed space with **empty carrier** is initial (isomorphic to `∅`). -/
noncomputable def isInitialOfIsEmpty [IsEmpty X] : IsInitial X :=
  emptyIsInitial.ofIso (asIso (emptyIsInitial.to X))

/-- `LocallyRingedSpace` has an initial object, namely the empty locally ringed space `∅`. -/
instance : HasInitial LocallyRingedSpace.{u} :=
  hasInitial_of_unique ∅

instance initial_isEmpty : IsEmpty (⊥_ LocallyRingedSpace.{u}) := by
  haveI : IsEmpty (↑↑(∅ : LocallyRingedSpace.{u}).toPresheafedSpace) := instIsEmptyEmpty
  exact Function.isEmpty (⇑(initialIsInitial.to (∅ : LocallyRingedSpace.{u})).base)

/-- The initial object of `LocallyRingedSpace` is **strict**: every morphism into it is an
isomorphism. The `LocallyRingedSpace` analogue of the strict-initial instance for `Scheme`. -/
instance : HasStrictInitialObjects LocallyRingedSpace.{u} :=
  hasStrictInitialObjects_of_initial_is_strict fun _ f => isIso_of_isEmpty f

section DisjointRange

variable {W S : LocallyRingedSpace.{u}}

/-- The tip of a commuting square over `S` whose two legs `f`, `g` have **disjoint ranges** on the
underlying spaces has empty carrier: a point of the tip would map to a point lying in both ranges.
The `LocallyRingedSpace` analogue of `AlgebraicGeometry.Scheme.isEmpty_of_commSq`. -/
theorem isEmpty_of_commSq {f : X ⟶ S} {g : Y ⟶ S} {i : W ⟶ X} {j : W ⟶ Y}
    (sq : CommSq i j f g) (H : Disjoint (Set.range f.base) (Set.range g.base)) : IsEmpty W := by
  refine ⟨fun w => ?_⟩
  have hx : f.base (i.base w) = g.base (j.base w) := by
    have e : (i ≫ f).base w = (j ≫ g).base w := by rw [sq.w]
    rwa [comp_base, comp_base] at e
  have h1 : f.base (i.base w) ∈ Set.range f.base := Set.mem_range_self (i.base w)
  have h2 : g.base (j.base w) ∈ Set.range g.base := Set.mem_range_self (j.base w)
  rw [← hx] at h2
  exact Set.disjoint_left.mp H h1 h2

/-- The **pullback of two morphisms with disjoint ranges is empty**. The `LocallyRingedSpace`
analogue of `AlgebraicGeometry.Scheme.isEmpty_pullback`; note no open-immersion hypothesis is
needed. -/
theorem isEmpty_pullback (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
    (H : Disjoint (Set.range f.base) (Set.range g.base)) :
    IsEmpty (pullback f g : LocallyRingedSpace.{u}) :=
  isEmpty_of_commSq (IsPullback.of_hasPullback f g).toCommSq H

/-- The **pullback of two morphisms with disjoint ranges is initial**. This is the tool that
degenerates the cocycle of a glue datum indexed by a poset in which some patches do not overlap:
the triple-overlap pullback is initial, so the cocycle equations hold by initiality. -/
noncomputable def isInitialPullbackOfDisjointRange (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
    (H : Disjoint (Set.range f.base) (Set.range g.base)) :
    IsInitial (pullback f g : LocallyRingedSpace.{u}) :=
  haveI := isEmpty_pullback f g H
  isInitialOfIsEmpty

end DisjointRange

end AlgebraicGeometry.LocallyRingedSpace
