import FormalSchemes.ClosedImmersion

set_option linter.style.header false

/-!
# Isomorphisms are closed immersions

This file completes the basic stability API of `FormalScheme.IsClosedImmersion` requested in the
§10.14/§10.15 closed-immersion infrastructure: an **isomorphism of formal schemes is a closed
immersion**, and closed immersions are consequently stable under composition with an isomorphism on
either side.

The identity case (`FormalScheme.isClosedImmersion_id`) and stability under composition of two
closed immersions (`FormalScheme.IsClosedImmersion.comp`) are already in
`FormalSchemes/ClosedImmersion.lean`. The genuinely new content here is that a categorical
isomorphism satisfies the predicate at all: its base map is (the coercion of) a homeomorphism —
hence a closed topological embedding — and each stalk map is a ring isomorphism, hence surjective.

## Main results

* `FormalScheme.isClosedImmersion_of_isIso`: an isomorphism `f : X ⟶ Y` is a closed immersion.
* `FormalScheme.IsClosedImmersion.comp_iso`: a closed immersion followed by an isomorphism is a
  closed immersion.
* `FormalScheme.IsClosedImmersion.iso_comp`: an isomorphism followed by a closed immersion is a
  closed immersion.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.14, §10.15.
* [The Stacks Project, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.FormalScheme

variable {X Y Z : FormalScheme.{u}}

/-- The underlying locally-ringed-space morphism of a categorical isomorphism of formal schemes is
itself an isomorphism (the forgetful functor to `LocallyRingedSpace` preserves isomorphisms). -/
instance isIso_toLRSHom (f : X ⟶ Y) [IsIso f] : IsIso f.toLRSHom := by
  change IsIso (forgetToLocallyRingedSpace.map f)
  infer_instance

/-- **An isomorphism of formal schemes is a closed immersion.** Its base map is (the coercion of) a
homeomorphism — hence a closed topological embedding — and each stalk map is a ring isomorphism,
hence surjective. -/
theorem isClosedImmersion_of_isIso (f : X ⟶ Y) [IsIso f] : IsClosedImmersion f where
  base_closedEmbedding := by
    haveI : IsIso f.toLRSHom.base := by
      change IsIso (LocallyRingedSpace.forgetToTop.map f.toLRSHom)
      infer_instance
    exact (TopCat.homeoOfIso (asIso f.toLRSHom.base)).isClosedEmbedding
  surjective_stalkMap y := by
    haveI : IsIso f.toLRSHom.toShHom.hom := by
      change IsIso (SheafedSpace.forgetToPresheafedSpace.map f.toLRSHom.toShHom)
      infer_instance
    haveI : IsIso (f.toLRSHom.stalkMap y) :=
      inferInstanceAs (IsIso (f.toLRSHom.toShHom.hom.stalkMap y))
    exact (ConcreteCategory.bijective_of_isIso (f.toLRSHom.stalkMap y)).surjective

/-- A closed immersion followed by an isomorphism is a closed immersion. -/
theorem IsClosedImmersion.comp_iso {f : X ⟶ Y} (hf : IsClosedImmersion f) (g : Y ⟶ Z) [IsIso g] :
    IsClosedImmersion (f ≫ g) :=
  hf.comp (isClosedImmersion_of_isIso g)

/-- An isomorphism followed by a closed immersion is a closed immersion. -/
theorem IsClosedImmersion.iso_comp (f : X ⟶ Y) [IsIso f] {g : Y ⟶ Z} (hg : IsClosedImmersion g) :
    IsClosedImmersion (f ≫ g) :=
  (isClosedImmersion_of_isIso f).comp hg

end AlgebraicGeometry.FormalScheme

end
