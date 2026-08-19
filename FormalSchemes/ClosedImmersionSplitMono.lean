import FormalSchemes.ClosedImmersion

set_option linter.style.header false

/-!
# Sections are closed immersions as soon as their base map is a closed embedding

`FormalSchemes/ClosedImmersion.lean` (issue 492) defines a closed immersion of formal schemes as the
conjunction of a *topological* condition (the base map is a closed embedding) and an *algebraic* one
(every stalk map is surjective). This file observes that for a **split monomorphism** the algebraic
half is automatic, so the predicate collapses to its topological half.

The reason is elementary functoriality of stalks. If `f : X ⟶ Y` has a retraction `r : Y ⟶ X`, then
`LocallyRingedSpace.stalkMap_comp` factors the stalk map of `f ≫ r = 𝟙 X` at a point `x` as
`r.stalkMap (f.base x) ≫ f.stalkMap x`; the stalk map of the identity is the identity, so this
composite is surjective, and a surjective composite has a surjective *outer* factor — which is
exactly `f.stalkMap x`.

The intended consumer is the §10.15 diagonal, which is always a section of the first projection
(`BothChartedFibreDatumXY.diagonal'_comp_pr₁`): separatedness therefore never owes a stalk
obligation. See `FormalSchemes/GeneralSeparatedTopological.lean`.

## Main results

* `AlgebraicGeometry.surjective_stalkMap_of_retraction`: a morphism of locally ringed spaces
  with a retraction has surjective stalk maps.
* `AlgebraicGeometry.FormalScheme.isClosedImmersion_of_retraction`: a section of a morphism of
  formal schemes is a closed immersion as soon as its base map is a closed embedding.
* `AlgebraicGeometry.FormalScheme.isClosedImmersion_iff_isClosedEmbedding_base_of_isSplitMono`: for
  a split monomorphism, being a closed immersion *is* the topological condition.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.14, §10.15.
* [The Stacks Project, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry

/-- **A morphism of locally ringed spaces with a retraction has surjective stalk maps.** The
stalk map of `f ≫ r = 𝟙 X` at `x` factors as `r.stalkMap (f.base x) ≫ f.stalkMap x` and is the
identity, so its outer factor `f.stalkMap x` is surjective. -/
theorem surjective_stalkMap_of_retraction {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (r : Y ⟶ X)
    (h : f ≫ r = 𝟙 X) (x : X) : Function.Surjective (f.stalkMap x).hom := by
  -- Generalising over the composite avoids rewriting `f ≫ r` to `𝟙 X` under `stalkMap`, where the
  -- motive is not type correct: the stalk's *index* `(f ≫ r).base x` mentions the morphism.
  have key : ∀ {g : X ⟶ X}, g = 𝟙 X → Function.Surjective (g.stalkMap x).hom := by
    rintro g rfl
    rw [LocallyRingedSpace.stalkMap_id]
    exact Function.surjective_id
  have hs := key h
  rw [LocallyRingedSpace.stalkMap_comp] at hs
  exact Function.Surjective.of_comp (g := ⇑(r.stalkMap (f.base x)).hom) hs

namespace FormalScheme

variable {X Y : FormalScheme.{u}}

/-- **A section of a morphism of formal schemes is a closed immersion as soon as its base map is a
closed embedding.** The stalk half of `FormalScheme.IsClosedImmersion` is supplied by the retraction
via `surjective_stalkMap_of_retraction`. -/
theorem isClosedImmersion_of_retraction (f : X ⟶ Y) (r : Y ⟶ X) (h : f ≫ r = 𝟙 X)
    (hbase : IsClosedEmbedding ⇑f.toLRSHom.base) : IsClosedImmersion f where
  base_closedEmbedding := hbase
  surjective_stalkMap x :=
    surjective_stalkMap_of_retraction f.toLRSHom r.toLRSHom
      (by rw [← comp_toLRSHom, h, id_toLRSHom]) x

/-- A split monomorphism of formal schemes has surjective stalk maps. -/
theorem surjective_stalkMap_of_isSplitMono (f : X ⟶ Y) [IsSplitMono f] (x : X) :
    Function.Surjective ⇑(f.toLRSHom.stalkMap x).hom :=
  surjective_stalkMap_of_retraction f.toLRSHom (retraction f).toLRSHom
    (by rw [← comp_toLRSHom, IsSplitMono.id f, id_toLRSHom]) x

/-- A split monomorphism of formal schemes whose base map is a closed embedding is a closed
immersion. -/
theorem isClosedImmersion_of_isSplitMono (f : X ⟶ Y) [IsSplitMono f]
    (hbase : IsClosedEmbedding ⇑f.toLRSHom.base) : IsClosedImmersion f :=
  isClosedImmersion_of_retraction f (retraction f) (IsSplitMono.id f) hbase

/-- **For a split monomorphism, being a closed immersion is a purely topological condition.** This
is the shape in which the §10.15 diagonal consumes the predicate: only the base map has to be
examined. -/
theorem isClosedImmersion_iff_isClosedEmbedding_base_of_isSplitMono (f : X ⟶ Y) [IsSplitMono f] :
    IsClosedImmersion f ↔ IsClosedEmbedding ⇑f.toLRSHom.base :=
  ⟨fun hf => hf.base_closedEmbedding, isClosedImmersion_of_isSplitMono f⟩

end FormalScheme

end AlgebraicGeometry

end
