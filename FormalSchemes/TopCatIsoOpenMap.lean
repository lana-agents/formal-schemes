import Mathlib.Topology.Category.TopCat.Basic

set_option linter.style.header false

/-!
# An isomorphism of topological spaces is a bijective open map, and openness descends

Two pieces of bookkeeping about `IsOpenMap`, wanted whenever a morphism of locally ringed spaces
is decided by `AlgebraicGeometry.LocallyRingedSpace.isIso_iff_isIso_base_and_isIso_c_app`
(`FormalSchemes.ActionQuotientRestrictQuotient`) and its base map is only reachable through a
surjection.

* `TopCat.isIso_iff_bijective_and_isOpenMap` turns `IsIso` of a morphism of `TopCat` into two
  conditions on the underlying function. Mathlib has the direction that builds the isomorphism,
  `TopCat.isIso_of_bijective_of_isOpenMap`, and no `↔`.
* `IsOpenMap.of_comp_of_surjective` moves openness of a composite `h ∘ p` onto `h`, for `p`
  continuous and surjective. The image of an open `V` under `h` is the image of `p ⁻¹' V` under
  `h ∘ p`, because `p` surjective makes `p '' (p ⁻¹' V) = V`.

Together with `IsOpenMap.comp` — which supplies the converse when `p` is itself open — the second
is what makes openness of `h` *equivalent* to openness of `h ∘ p` along an open surjection, which
is the shape a quotient projection has.

## Why this file exists, and why it is this low

Neither statement mentions a ring, an ideal, a spectrum, a formal scheme or a group action.
Following `FormalSchemes/LocallyRingedSpaceHomExt.lean`,
`FormalSchemes/LocallyRingedSpaceBasisComponent.lean` and
`FormalSchemes/LocallyRingedSpaceStalkSurjective.lean`, which make the same argument for the same
reason, they sit directly on Mathlib rather than beside the one consumer that motivated them
(`FormalSchemes.TateInvNodeChartSpaceHalf`, issue 1775). The consumer is a leaf 262 project
modules deep; either statement placed there would be unreachable from anywhere else.

Both were confirmed absent from Mathlib and from this project by trying to produce them rather
than by grep, which is the only reliable check: a declaration can exist with no `theorem` line
anywhere declaring it, and under a namespace its call sites do not suggest.

## Main results

* `TopCat.isIso_iff_bijective_and_isOpenMap`: a morphism of `TopCat` is an isomorphism exactly
  when its underlying function is bijective and open.
* `IsOpenMap.of_comp_of_surjective`: if `h ∘ p` is open and `p` is continuous and surjective, then
  `h` is open.

## What is *not* here

**No closed-map companion.** Mathlib's `TopCat.isIso_of_bijective_of_isClosedMap` gives the same
service for closed maps, and the `↔` for it is not stated because nothing on this tree wants it —
`IsClosedMap` of a composite does not descend along a surjection under the hypotheses above.

**Nothing about `Topology.IsOpenEmbedding`.** `TopCat.isIso_iff_bijective_and_isOpenMap` decides
`IsIso`, not any weaker property, and injectivity is one of the two halves of its bijectivity
clause rather than a separate conclusion.
-/

universe u

open CategoryTheory

/-- **Openness descends along a continuous surjection.** If `h ∘ p` is an open map and `p` is
continuous and surjective, then `h` is an open map: the image of an open `V` under `h` is the
image of `p ⁻¹' V` under `h ∘ p`, since `p '' (p ⁻¹' V) = V` for surjective `p`.

The converse — `h` open and `p` open give `h ∘ p` open — is `IsOpenMap.comp` and needs `p` open
rather than surjective, so along an open surjection the two are equivalent. -/
theorem IsOpenMap.of_comp_of_surjective {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {p : X → Y} {h : Y → Z} (hcont : Continuous p)
    (hsurj : Function.Surjective p) (hc : IsOpenMap (h ∘ p)) : IsOpenMap h := fun V hV => by
  rw [← Set.image_preimage_eq V hsurj, ← Set.image_comp]
  exact hc _ (hV.preimage hcont)

/-- **A morphism of topological spaces is an isomorphism exactly when it is bijective and open.**

The forward direction reads the two properties off `TopCat.homeoOfIso`; the backward direction is
Mathlib's `TopCat.isIso_of_bijective_of_isOpenMap`, which builds the homeomorphism from
`Equiv.toHomeomorphOfContinuousOpen`. Mathlib has the backward direction only.

Continuity is not a third condition: it is carried by the morphism. -/
theorem TopCat.isIso_iff_bijective_and_isOpenMap {X Y : TopCat.{u}} (f : X ⟶ Y) :
    IsIso f ↔ Function.Bijective ⇑(ConcreteCategory.hom f) ∧
      IsOpenMap ⇑(ConcreteCategory.hom f) :=
  ⟨fun _ => ⟨(TopCat.homeoOfIso (asIso f)).bijective, (TopCat.homeoOfIso (asIso f)).isOpenMap⟩,
    fun ⟨hb, ho⟩ => TopCat.isIso_of_bijective_of_isOpenMap f hb ho⟩
