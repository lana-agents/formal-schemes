import FormalSchemes.ClosedImmersionSections
import FormalSchemes.OpenCover
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Sets.OpenCover

set_option linter.style.header false

/-!
# Closed immersions of formal schemes

This file introduces a reusable predicate `FormalScheme.IsClosedImmersion` on a morphism of
formal schemes `f : X ⟶ Y`, mirroring the Stacks-Project definition of a closed immersion of
locally ringed spaces (Tag 01HJ): the underlying continuous map is a closed topological embedding
and every stalk map is surjective.

The affine building blocks are already proved in `FormalSchemes/ClosedImmersionSections.lean`
(phrased as the raw conjunction on `FormalSpectrum.map` / `presheafedSpaceMap`); here we package
the two conditions into a structure, establish the basic stability API (identity, composition),
and prove that being a closed immersion is **local on the target**: it can be checked after
restricting to the members of an open cover of `Y`.

## Main definitions and results

* `FormalScheme.IsClosedImmersion f`: the predicate (closed embedding of the base map, surjective
  stalk maps).
* `FormalScheme.isClosedImmersion_id`: the identity is a closed immersion.
* `FormalScheme.IsClosedImmersion.comp`: closed immersions are stable under composition.
* `FormalScheme.isClosedImmersion_of_openCover`: the base half of the closed-immersion condition
  descends along an open cover of the target (the stalk half is already a global pointwise
  condition), yielding a closed immersion.

The stalk half is a *global* pointwise condition, so it is not re-derived from the cover here.
The fully target-local variant is `FormalScheme.isClosedImmersion_iff_restrictOpen`
(`FormalSchemes.ClosedImmersionTargetLocal`): an `↔` over an arbitrary family of opens covering
`Y`, whose per-chart hypothesis is a genuine `IsClosedImmersion` of the restricted morphism
`X|_{f⁻¹(V i)} ⟶ Y|_{V i}`, with no global hypothesis left over. That hypothesis is strictly weaker
per chart, so `isClosedImmersion_of_openCover` below is the special case in which the stalk half is
supplied globally; it is kept because it has consumers.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.14, §10.15.
* [The Stacks Project, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.FormalScheme

variable {X Y Z : FormalScheme.{u}}

/-- The underlying locally-ringed-space morphism of the identity is the identity. -/
theorem id_toLRSHom (X : FormalScheme.{u}) :
    Hom.toLRSHom (𝟙 X) = 𝟙 X.toLocallyRingedSpace := rfl

/-- The underlying locally-ringed-space morphism of a composite is the composite. -/
theorem comp_toLRSHom (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.toLRSHom (f ≫ g) = f.toLRSHom ≫ g.toLRSHom := rfl

/-- A morphism of formal schemes `f : X ⟶ Y` is a **closed immersion** when its underlying
continuous map is a closed topological embedding and every stalk map is surjective (Stacks Project
Tag 01HJ, for locally ringed spaces). -/
structure IsClosedImmersion (f : X ⟶ Y) : Prop where
  /-- The underlying base map is a closed topological embedding. -/
  base_closedEmbedding : IsClosedEmbedding ⇑f.toLRSHom.base
  /-- Every stalk map is surjective. -/
  surjective_stalkMap : ∀ y, Function.Surjective ⇑(f.toLRSHom.stalkMap y).hom

/-- The identity morphism of a formal scheme is a closed immersion: its base map is the identity
(a closed embedding) and each of its stalk maps is the identity (hence surjective). -/
theorem isClosedImmersion_id (X : FormalScheme.{u}) : IsClosedImmersion (𝟙 X) where
  base_closedEmbedding := by
    have h : ⇑(Hom.toLRSHom (𝟙 X)).base = id := rfl
    rw [h]
    exact IsClosedEmbedding.id
  surjective_stalkMap y := by
    rw [id_toLRSHom, LocallyRingedSpace.stalkMap_id]
    exact Function.surjective_id

/-- Closed immersions of formal schemes are stable under composition: the base map of `f ≫ g` is
the composite of two closed embeddings, and each stalk map of `f ≫ g` factors as a composite of
two surjective stalk maps (via `LocallyRingedSpace.stalkMap_comp`). -/
theorem IsClosedImmersion.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsClosedImmersion f) (hg : IsClosedImmersion g) :
    IsClosedImmersion (f ≫ g) where
  base_closedEmbedding := by
    have h : ⇑(f ≫ g).toLRSHom.base = ⇑g.toLRSHom.base ∘ ⇑f.toLRSHom.base := rfl
    rw [h]
    exact hg.base_closedEmbedding.comp hf.base_closedEmbedding
  surjective_stalkMap y := by
    have hAB : Function.Surjective
        ⇑(g.toLRSHom.stalkMap (f.toLRSHom.base y) ≫ f.toLRSHom.stalkMap y).hom := by
      rw [CommRingCat.hom_comp, RingHom.coe_comp]
      exact (hf.surjective_stalkMap y).comp (hg.surjective_stalkMap (f.toLRSHom.base y))
    have e : (f ≫ g).toLRSHom.stalkMap y
        = g.toLRSHom.stalkMap (f.toLRSHom.base y) ≫ f.toLRSHom.stalkMap y :=
      LocallyRingedSpace.stalkMap_comp f.toLRSHom g.toLRSHom y
    rw [e]
    exact hAB

/-- **Being a closed immersion is local on the target.** Let `f : X ⟶ Y` be a morphism of formal
schemes and `𝒰` an open cover of `Y`. If, for every member `j` of the cover, the restriction of the
base map of `f` to the preimage of the chart `range (𝒰.map j).base` is a closed topological
embedding, and every stalk map of `f` is surjective, then `f` is a closed immersion.

The base half is the honest content: it descends from the cover via Mathlib's
`isClosedEmbedding_iff_restrictPreimage`, using that each chart `range (𝒰.map j).base` is open (the
`𝒰.map j` are open immersions) and that the charts cover `Y` (`𝒰.iUnion_range`). The stalk half is
already a global pointwise condition and is passed through unchanged. -/
theorem isClosedImmersion_of_openCover (f : X ⟶ Y) (𝒰 : OpenCover Y)
    (hbase : ∀ j, IsClosedEmbedding
      (Set.restrictPreimage (Set.range (𝒰.map j).toLRSHom.base) f.toLRSHom.base))
    (hstalk : ∀ y, Function.Surjective ⇑(f.toLRSHom.stalkMap y).hom) :
    IsClosedImmersion f where
  base_closedEmbedding :=
    (TopologicalSpace.IsOpenCover.isClosedEmbedding_iff_restrictPreimage
      (TopologicalSpace.IsOpenCover.of_sets
        (fun j => (𝒰.isOpenImmersion j).base_open.isOpen_range) 𝒰.iUnion_range)
      f.toLRSHom.base.hom.continuous).mpr hbase
  surjective_stalkMap := hstalk

end AlgebraicGeometry.FormalScheme

end
