import Mathlib.Topology.Category.TopCat.Basic

set_option linter.style.header false

/-!
# An isomorphism of topological spaces is a bijective open map

One piece of bookkeeping about `IsOpenMap`, wanted whenever a morphism of locally ringed spaces is
decided by `AlgebraicGeometry.LocallyRingedSpace.isIso_iff_isIso_base_and_isIso_c_app`
(`FormalSchemes.ActionQuotientRestrictQuotient`) and the clauses of its base map are stated
separately.

`TopCat.isIso_iff_bijective_and_isOpenMap` turns `IsIso` of a morphism of `TopCat` into two
conditions on the underlying function. **Mathlib has this equivalence already, in another
packaging.** `TopCat.isIso_iff_isHomeomorph` states it against `IsHomeomorph`, whose three fields
are continuity, openness and bijectivity, and the proof below is that `↔` with the structure
unfolded — continuity is not a third condition, since it is carried by the morphism. What the
unfolded form buys is a `rw` into a conjunction of the clauses a consumer states one at a time;
destructuring `IsHomeomorph` does not rewrite a goal.

## Why this file exists, and why it is this low

The statement mentions no ring, ideal, spectrum, formal scheme or group action. Following
`FormalSchemes/LocallyRingedSpaceHomExt.lean`,
`FormalSchemes/LocallyRingedSpaceBasisComponent.lean` and
`FormalSchemes/LocallyRingedSpaceStalkSurjective.lean`, which make the same argument for the same
reason, it sits directly on Mathlib rather than beside the one consumer that motivated it
(`FormalSchemes.TateInvNodeChartSpaceHalf`, issue 1775). That consumer is a leaf 262 project
modules deep; placed there the statement would be unreachable from anywhere else.

## Main results

* `TopCat.isIso_iff_bijective_and_isOpenMap`: a morphism of `TopCat` is an isomorphism exactly
  when its underlying function is bijective and open.

## What is *not* here

**No openness-descent lemma.** That openness of `h` follows from openness of `h ∘ p` along a
continuous surjection `p` is Mathlib's `IsOpenMap.of_comp`; it is used directly at its consumer and
is not restated here. Its converse for open `p` is `IsOpenMap.comp`, so along an open surjection
the two are equivalent, and `IsOpenQuotientMap.isOpenMap_iff` is that equivalence packaged.

**No closed-map companion.** Mathlib's `TopCat.isIso_of_bijective_of_isClosedMap` gives the same
service for closed maps, and the `↔` for it is not stated because nothing on this tree wants it.

**Nothing about `Topology.IsOpenEmbedding`.** `TopCat.isIso_iff_bijective_and_isOpenMap` decides
`IsIso`, not any weaker property, and injectivity is one of the two halves of its bijectivity
clause rather than a separate conclusion.
-/

universe u

open CategoryTheory

/-- **A morphism of topological spaces is an isomorphism exactly when it is bijective and open.**

`TopCat.isIso_iff_isHomeomorph` with `IsHomeomorph` unfolded into its fields: Mathlib states the
same equivalence against that structure, and this is the form that rewrites a goal into the two
clauses separately. Continuity is not a third condition — it is carried by the morphism. -/
theorem TopCat.isIso_iff_bijective_and_isOpenMap {X Y : TopCat.{u}} (f : X ⟶ Y) :
    IsIso f ↔ Function.Bijective ⇑(ConcreteCategory.hom f) ∧
      IsOpenMap ⇑(ConcreteCategory.hom f) :=
  (TopCat.isIso_iff_isHomeomorph f).trans
    ⟨fun h => ⟨h.bijective, h.isOpenMap⟩,
      fun ⟨hb, ho⟩ => ⟨(ConcreteCategory.hom f).continuous, ho, hb⟩⟩
