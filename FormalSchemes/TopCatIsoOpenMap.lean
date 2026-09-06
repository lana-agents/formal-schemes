import Mathlib.Topology.Category.TopCat.Basic

set_option linter.style.header false

/-!
# An isomorphism of topological spaces, unbundled into bijective and open

`TopCat.isIso_iff_bijective_and_isOpenMap` turns `IsIso` of a morphism of `TopCat` into two
conditions on the underlying function. It is wanted whenever a morphism of locally ringed spaces is
decided by `AlgebraicGeometry.LocallyRingedSpace.isIso_iff_isIso_base_and_isIso_c_app`
(`FormalSchemes.ActionQuotientRestrictQuotient`) and its base map is reached one clause at a time.

## What Mathlib already has, and what this adds

**Mathlib decides this, and the statement below is a repackaging rather than a missing direction.**
`TopCat.isIso_iff_isHomeomorph` is the `↔`, stated with the structure `IsHomeomorph` whose three
fields are `IsHomeomorph.continuous`, `IsHomeomorph.isOpenMap` and `IsHomeomorph.bijective`; and
`TopCat.isIso_of_bijective_of_isOpenMap` is the direction that builds the isomorphism, through
`Equiv.toHomeomorphOfContinuousOpen`. What is added here is only the unbundling: an `∧` of the two
fields a caller supplies, with the third dropped because a morphism of `TopCat` carries its
continuity.

That is worth a name because it is the form `rw` wants. A caller that has separate `↔`s for
injectivity, surjectivity and openness of one map can rewrite straight through this and
`Function.Bijective`; against `IsHomeomorph` it would have to build and destructure a structure at
each use.

## Why this file exists, and why it is this low

The statement mentions no ring, ideal, spectrum, formal scheme or group action. Following
`FormalSchemes/LocallyRingedSpaceHomExt.lean`,
`FormalSchemes/LocallyRingedSpaceBasisComponent.lean` and
`FormalSchemes/LocallyRingedSpaceStalkSurjective.lean`, which make the same argument for the same
reason, it sits directly on Mathlib rather than beside the one consumer that motivated it
(`FormalSchemes.TateInvNodeChartSpaceHalf`, issue 1775). That consumer's forward closure is 263
project modules; the statement placed there would be unreachable from anywhere else.

## Main results

* `TopCat.isIso_iff_bijective_and_isOpenMap`: a morphism of `TopCat` is an isomorphism exactly when
  its underlying function is bijective and open.

## What is *not* here

**No general-topology lemma about openness descending along a surjection.** An earlier draft of
this file carried one; it is `IsOpenMap.of_comp` (`Mathlib/Topology/Maps/Basic.lean`), which has
the same hypotheses in the same order and the same proof, so it was deleted rather than landed.
A library search on the goal finds it directly; the earlier draft stated the lemma in term mode and
so never put a goal in front of one.

**No closed-map companion.** `TopCat.isIso_iff_isHomeomorph` composed with
`isHomeomorph_iff_continuous_isClosedMap_bijective` gives the closed-map `↔` in the same two lines
as the one below, so it is absent because nothing on this tree wants it and not because it would
cost anything.

**Nothing about `Topology.IsOpenEmbedding`.** `TopCat.isIso_iff_bijective_and_isOpenMap` decides
`IsIso`, not any weaker property, and injectivity is one of the two halves of its bijectivity
clause rather than a separate conclusion.
-/

universe u

open CategoryTheory

/-- **A morphism of topological spaces is an isomorphism exactly when it is bijective and open.**

`TopCat.isIso_iff_isHomeomorph` with `IsHomeomorph` unbundled into an `∧` of two of its three
fields; the third, continuity, is carried by the morphism. Mathlib decides `IsIso` here already and
this adds no direction — it supplies the shape a `rw` through separate injectivity, surjectivity
and openness criteria needs. -/
theorem TopCat.isIso_iff_bijective_and_isOpenMap {X Y : TopCat.{u}} (f : X ⟶ Y) :
    IsIso f ↔ Function.Bijective ⇑(ConcreteCategory.hom f) ∧
      IsOpenMap ⇑(ConcreteCategory.hom f) :=
  (TopCat.isIso_iff_isHomeomorph f).trans
    ⟨fun h => ⟨h.bijective, h.isOpenMap⟩, fun ⟨hb, ho⟩ => ⟨f.hom.continuous, ho, hb⟩⟩
