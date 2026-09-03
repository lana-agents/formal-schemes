import FormalSchemes.ClosedImmersion

set_option linter.style.header false

/-!
# Sections are closed immersions as soon as their image is closed

`FormalSchemes/ClosedImmersion.lean` (issue 492) defines a closed immersion of formal schemes as the
conjunction of a *topological* condition (the base map is a closed embedding) and an *algebraic* one
(every stalk map is surjective). This file observes that a morphism admitting a **retraction** — in
particular a split monomorphism — owes neither condition beyond closedness of its image.

Both halves are elementary functoriality of one retraction `r : Y ⟶ X` with `f ≫ r = 𝟙 X`.

*The algebraic half.* `LocallyRingedSpace.stalkMap_comp` factors the stalk map of `f ≫ r = 𝟙 X` at a
point `x` as `r.stalkMap (f.base x) ≫ f.stalkMap x`; the stalk map of the identity is the identity,
so this composite is surjective, and a surjective composite has a surjective *outer* factor — which
is exactly `f.stalkMap x`.

*The topological half.* The base map of `f ≫ r = 𝟙 X` is `⇑r.base ∘ ⇑f.base = id`, so `⇑f.base` is
injective and `⇑r.base` restricts to a continuous inverse on its image
(`Function.LeftInverse.isEmbedding`): a continuous map with a continuous retraction is always a
topological embedding.

A closed embedding is exactly an embedding with closed range, so nothing is left of
`FormalScheme.IsClosedImmersion` but closedness of the range:

```
IsClosedImmersion f ↔ IsClosed (Set.range ⇑f.toLRSHom.base)      -- `f` a split monomorphism
```

The closed-*embedding* forms of the criteria are kept, each as a one-line application of its
closed-*range* counterpart: a closed embedding is what `FormalScheme.IsClosedImmersion` stores, and
it is the form a topological argument about a diagonal produces, so it is how the hypothesis usually
arrives.

The intended consumer is the §10.15 diagonal, which is always a section of the first projection
(`BothChartedFibreDatumXY.diagonal'_comp_pr₁`): separatedness therefore never owes a stalk
obligation, and its topological obligation is a closed image.  The specialisation to the diagonal is
in `FormalSchemes/GeneralSeparatedTopological.lean` and `FormalSchemes/GeneralSeparatedRange.lean`,
both of which import this file.

## Main results

* `AlgebraicGeometry.surjective_stalkMap_of_retraction`: a morphism of locally ringed spaces
  with a retraction has surjective stalk maps.
* `AlgebraicGeometry.isEmbedding_base_of_retraction`: such a morphism has a base map which is a
  topological embedding.
* `AlgebraicGeometry.FormalScheme.isClosedImmersion_of_isClosed_range_of_retraction`: a section of a
  morphism of formal schemes is a closed immersion as soon as its image is closed.
  `FormalScheme.isClosedImmersion_of_retraction` is its closed-embedding form.
* `AlgebraicGeometry.FormalScheme.isClosedImmersion_iff_isClosed_range_of_isSplitMono`: for a split
  monomorphism, being a closed immersion *is* closedness of the image.
  `FormalScheme.isClosedImmersion_iff_isClosedEmbedding_base_of_isSplitMono` is the same equivalence
  with the topological side left unsharpened.
* `AlgebraicGeometry.FormalScheme.isClosedImmersion_of_openCover_isClosed_range`: the same
  criterion chart by chart over an open cover of the target.

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

/-- **A morphism of locally ringed spaces with a retraction has a base map which is a topological
embedding.** The base map of `f ≫ r = 𝟙 X` is `⇑r.base ∘ ⇑f.base = id`, so `⇑f.base` is injective
and `⇑r.base` restricts to a continuous inverse on its image.

This is the topological companion of `surjective_stalkMap_of_retraction`: between them the two
leave `FormalScheme.IsClosedImmersion` owing nothing but closedness of the image. -/
theorem isEmbedding_base_of_retraction {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (r : Y ⟶ X)
    (h : f ≫ r = 𝟙 X) : IsEmbedding ⇑f.base := by
  have key : ⇑r.base ∘ ⇑f.base = id :=
    congrArg (fun g : X ⟶ X => ⇑g.base) h
  exact Function.LeftInverse.isEmbedding (congrFun key) r.base.hom.continuous f.base.hom.continuous

namespace FormalScheme

variable {X Y : FormalScheme.{u}}

/-- **A section of a morphism of formal schemes has a base map which is a topological
embedding.** -/
theorem isEmbedding_base_of_retraction (f : X ⟶ Y) (r : Y ⟶ X) (h : f ≫ r = 𝟙 X) :
    IsEmbedding ⇑f.toLRSHom.base :=
  _root_.AlgebraicGeometry.isEmbedding_base_of_retraction f.toLRSHom r.toLRSHom
    (by rw [← comp_toLRSHom, h, id_toLRSHom])

/-- A split monomorphism of formal schemes has a base map which is a topological embedding. -/
theorem isEmbedding_base_of_isSplitMono (f : X ⟶ Y) [IsSplitMono f] :
    IsEmbedding ⇑f.toLRSHom.base :=
  isEmbedding_base_of_retraction f (retraction f) (IsSplitMono.id f)

/-- **A section of a morphism of formal schemes is a closed immersion as soon as its image is
closed.** Everything `FormalScheme.IsClosedImmersion` asks for beyond closedness of the image is
supplied by the retraction: the stalk maps by `surjective_stalkMap_of_retraction` and the embedding
by `isEmbedding_base_of_retraction`. -/
theorem isClosedImmersion_of_isClosed_range_of_retraction (f : X ⟶ Y) (r : Y ⟶ X)
    (h : f ≫ r = 𝟙 X) (hrange : IsClosed (Set.range ⇑f.toLRSHom.base)) :
    IsClosedImmersion f where
  base_closedEmbedding := ⟨isEmbedding_base_of_retraction f r h, hrange⟩
  surjective_stalkMap x :=
    surjective_stalkMap_of_retraction f.toLRSHom r.toLRSHom
      (by rw [← comp_toLRSHom, h, id_toLRSHom]) x

/-- **A section of a morphism of formal schemes is a closed immersion as soon as its base map is a
closed embedding.** This is `FormalScheme.isClosedImmersion_of_isClosed_range_of_retraction` at the
range of a closed embedding: the embedding half of the hypothesis is redundant, the retraction
having already supplied it. It is kept because a closed embedding is the form in which the
topological hypothesis usually arrives. -/
theorem isClosedImmersion_of_retraction (f : X ⟶ Y) (r : Y ⟶ X) (h : f ≫ r = 𝟙 X)
    (hbase : IsClosedEmbedding ⇑f.toLRSHom.base) : IsClosedImmersion f :=
  isClosedImmersion_of_isClosed_range_of_retraction f r h hbase.isClosed_range

/-- A split monomorphism of formal schemes has surjective stalk maps. -/
theorem surjective_stalkMap_of_isSplitMono (f : X ⟶ Y) [IsSplitMono f] (x : X) :
    Function.Surjective ⇑(f.toLRSHom.stalkMap x).hom :=
  surjective_stalkMap_of_retraction f.toLRSHom (retraction f).toLRSHom
    (by rw [← comp_toLRSHom, IsSplitMono.id f, id_toLRSHom]) x

/-- A split monomorphism of formal schemes whose image is closed is a closed immersion. -/
theorem isClosedImmersion_of_isClosed_range_of_isSplitMono (f : X ⟶ Y) [IsSplitMono f]
    (hrange : IsClosed (Set.range ⇑f.toLRSHom.base)) : IsClosedImmersion f :=
  isClosedImmersion_of_isClosed_range_of_retraction f (retraction f) (IsSplitMono.id f) hrange

/-- A split monomorphism of formal schemes whose base map is a closed embedding is a closed
immersion. This is `FormalScheme.isClosedImmersion_of_isClosed_range_of_isSplitMono` at the range of
a closed embedding. -/
theorem isClosedImmersion_of_isSplitMono (f : X ⟶ Y) [IsSplitMono f]
    (hbase : IsClosedEmbedding ⇑f.toLRSHom.base) : IsClosedImmersion f :=
  isClosedImmersion_of_isClosed_range_of_isSplitMono f hbase.isClosed_range

/-- **For a split monomorphism, being a closed immersion is exactly having a closed image.** This is
the sharp form of `FormalScheme.isClosedImmersion_iff_isClosedEmbedding_base_of_isSplitMono`: not
only is the stalk condition free, so is the embedding half of the topological one. -/
theorem isClosedImmersion_iff_isClosed_range_of_isSplitMono (f : X ⟶ Y) [IsSplitMono f] :
    IsClosedImmersion f ↔ IsClosed (Set.range ⇑f.toLRSHom.base) :=
  ⟨fun hf => hf.base_closedEmbedding.isClosed_range,
    isClosedImmersion_of_isClosed_range_of_isSplitMono f⟩

/-- **For a split monomorphism, being a closed immersion is a purely topological condition.** This
is the shape in which the §10.15 diagonal consumes the predicate: only the base map has to be
examined. `FormalScheme.isClosedImmersion_iff_isClosed_range_of_isSplitMono` sharpens the
right-hand side further, to closedness of the image. -/
theorem isClosedImmersion_iff_isClosedEmbedding_base_of_isSplitMono (f : X ⟶ Y) [IsSplitMono f] :
    IsClosedImmersion f ↔ IsClosedEmbedding ⇑f.toLRSHom.base :=
  ⟨fun hf => hf.base_closedEmbedding, isClosedImmersion_of_isSplitMono f⟩

/-- **Local on the target, for a section**: a morphism of formal schemes with a retraction is a
closed immersion as soon as its image meets each chart of an open cover of the target in a closed
set. This is the closed-range form of `FormalScheme.isClosedImmersion_of_openCover`; both of that
lemma's other hypotheses — the per-chart embedding and the global stalk surjectivity — are supplied
by the retraction. -/
theorem isClosedImmersion_of_openCover_isClosed_range (f : X ⟶ Y) (r : Y ⟶ X)
    (h : f ≫ r = 𝟙 X) (𝒰 : OpenCover Y)
    (hrange : ∀ j, IsClosed (Set.range (Set.restrictPreimage
      (Set.range (𝒰.map j).toLRSHom.base) f.toLRSHom.base))) :
    IsClosedImmersion f :=
  isClosedImmersion_of_openCover f 𝒰
    (fun j => ⟨(isEmbedding_base_of_retraction f r h).restrictPreimage _, hrange j⟩)
    (fun y => surjective_stalkMap_of_retraction f.toLRSHom r.toLRSHom
      (by rw [← comp_toLRSHom, h, id_toLRSHom]) y)

end FormalScheme

end AlgebraicGeometry

end
