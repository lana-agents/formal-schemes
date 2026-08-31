import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

set_option linter.style.header false

/-!
# Mapping out of a glued locally ringed space

`AlgebraicGeometry.LocallyRingedSpace.GlueData` glues a family of locally ringed spaces `U i`
along open immersions `f i j : V i j ⟶ U i`. Mathlib builds the glued space
(`CategoryTheory.GlueData.glued`) and the chart inclusions (`CategoryTheory.GlueData.ι`), and
proves the charts are jointly surjective open immersions — all statements about maps *into* the
glued space. This file supplies the statements about maps *out* of it.

The glued space is the multicoequalizer of the gluing diagram
(`CategoryTheory.GlueData.glued = multicoequalizer D.diagram`), so a morphism out of it is exactly
a compatible cocone; the compatibility is the one the diagram imposes on the overlap `V (i, j)`,
whose two legs are `f i j` and `t i j ≫ f j i`:
```
f i j ≫ k i = t i j ≫ f j i ≫ k j    for all i, j.
```

## Relation to `FormalSchemes.GlueMorphisms` and `FormalSchemes.GlueMorphismsOpenImmersion`

Those two files state the same results for `AlgebraicGeometry.FormalScheme.GlueData`, whose pieces
are required to be formal schemes. **Every proof there uses only the underlying
`LocallyRingedSpace.GlueData`**, so the statements here are strictly more general and the formal
ones are corollaries — `FormalScheme.GlueData.ι` is by definition
`D.toLocallyRingedSpaceGlueData.toGlueData.ι`, and `(D.gluedFormalScheme).toLocallyRingedSpace` is
`D.toLocallyRingedSpaceGlueData.toGlueData.glued`.

They are stated here rather than reused from there because the consumer that motivated this file,
`AlgebraicGeometry.ChartedSchemeDatum.specGlued`, glues **affine schemes**, which are not formal
schemes, so `FormalScheme.GlueData` does not apply to it at all. Repointing the two formal-side
files at this one is a mechanical follow-up; it is deliberately not done in the same change,
because `glueMorphisms` has upwards of forty consumers across the Tate cluster.

## Main definitions and results

* `AlgebraicGeometry.LocallyRingedSpace.GlueData.desc`: the morphism out of the glued space,
  with `ι_desc` its computation rule and `hom_ext` its uniqueness.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.range_desc`,
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.image_desc`: the range of the glued morphism is
  the union of the ranges of the pieces, and images are computed chartwise.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.injective_desc`: injectivity, from injectivity of
  the pieces **and** the hypothesis that the pieces meet in the target only along their glue
  overlap. That hypothesis is not removable: the line with two origins is glued from two copies of
  `𝔸¹` whose images in `𝔸¹` meet in more than the overlap accounts for. It is asked for only at
  `i ≠ j`; the diagonal instance follows from injectivity of the piece alone, so a caller never
  has to supply it.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.isOpenImmersion_desc`: **the criterion.** A
  morphism glued from open immersions that meet only along the glue overlaps is an open immersion.
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.isIso_desc` adds surjectivity on points and
  concludes an isomorphism.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* Mathlib `CategoryTheory.GlueData`, `CategoryTheory.Limits.Multicoequalizer.desc`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

namespace LocallyRingedSpace.GlueData

variable (D : LocallyRingedSpace.GlueData.{u}) {Y : LocallyRingedSpace.{u}}
variable (k : ∀ i, D.toGlueData.U i ⟶ Y)
variable (h : ∀ i j, D.toGlueData.f i j ≫ k i =
  D.toGlueData.t i j ≫ D.toGlueData.f j i ≫ k j)

/-! ### The universal property -/

/-- **Gluing a family of morphisms out of the glued space.** Given morphisms `k i : U i ⟶ Y` from
the pieces to a common target that agree on the overlaps
(`f i j ≫ k i = t i j ≫ f j i ≫ k j`), the induced morphism out of the glued space. -/
def desc : D.toGlueData.glued ⟶ Y :=
  Multicoequalizer.desc D.toGlueData.diagram Y k <| by
    rintro ⟨i, j⟩
    change D.toGlueData.f i j ≫ k i = (D.toGlueData.t i j ≫ D.toGlueData.f j i) ≫ k j
    rw [Category.assoc]
    exact h i j

@[reassoc (attr := simp)]
theorem ι_desc (i : D.J) : D.toGlueData.ι i ≫ D.desc k h = k i :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- **Uniqueness of the glued morphism**: two morphisms out of the glued space that agree after
restriction along every chart inclusion are equal (the `ι i` are jointly epimorphic). -/
theorem hom_ext {f g : D.toGlueData.glued ⟶ Y}
    (hfg : ∀ i, D.toGlueData.ι i ≫ f = D.toGlueData.ι i ≫ g) : f = g :=
  Multicoequalizer.hom_ext _ _ _ hfg

/-! ### Points, ranges and images -/

/-- (Helper) The glued morphism sends `ι i z` to `k i z`.

This is `ι_desc` read on points. The last step is term-mode rather than a `rw`: rewriting with
`ConcreteCategory.comp_apply` in the goal fails at `instances` transparency, because the index `i`
lives at `D.J` while the pieces are indexed through `toGlueData.U`, and the two agree only after
unfolding. -/
private theorem base_ι_desc (i : D.J) (z : D.toGlueData.U i) :
    (D.desc k h).base ((D.toGlueData.ι i).base z) = (k i).base z := by
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun φ : D.toGlueData.U i ⟶ Y => φ.base) (D.ι_desc k h i)) z
  rw [LocallyRingedSpace.comp_base] at hc
  exact (ConcreteCategory.comp_apply _ _ z).symm.trans hc

/-- **The range of the glued morphism is the union of the ranges of the pieces.** One inclusion is
`ι_desc`; the other is joint surjectivity of the chart inclusions. -/
theorem range_desc : Set.range (D.desc k h).base = ⋃ i, Set.range (k i).base := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨p, rfl⟩
    obtain ⟨i, z, rfl⟩ := D.ι_jointly_surjective p
    exact Set.mem_iUnion.2 ⟨i, z, (D.base_ι_desc k h i z).symm⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨z, rfl⟩ := hi
    exact ⟨(D.toGlueData.ι i).base z, D.base_ι_desc k h i z⟩

/-- **The image of a set under the glued morphism, computed chartwise.** Every point of the glued
space lies on some chart, so the image of `U` is the union over the charts of the images of its
chart-local traces. This is what makes the open-map property free once each `k i` is open. -/
theorem image_desc (U : Set D.toGlueData.glued) :
    (D.desc k h).base '' U = ⋃ i, (k i).base '' ((D.toGlueData.ι i).base ⁻¹' U) := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨i, z, rfl⟩ := D.ι_jointly_surjective p
    exact Set.mem_iUnion.2 ⟨i, z, hp, (D.base_ι_desc k h i z).symm⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨z, hz, rfl⟩ := hi
    exact ⟨(D.toGlueData.ι i).base z, hz, D.base_ι_desc k h i z⟩

/-! ### The open-immersion criterion -/

/-- **The glued morphism is injective on points**, provided each piece is and the pieces meet in
`Y` only along their glue overlap.

This is the one step with content. Two points of the glued space are `ι i x` and `ι j y`; if their
images agree then that common image lies in `range (k i) ∩ range (k j)`, so by hypothesis it is
`(f i j ≫ k i) z` for some point `z` of the overlap. Injectivity of `k i` and of `k j` identifies
`x` with `f i j z` and `y` with `(t i j ≫ f j i) z`, and the glue condition then says the two glued
points are equal. Dropping the overlap hypothesis breaks exactly here, and the line with two
origins is the standard counterexample. -/
theorem injective_desc (hinj : ∀ i, Function.Injective (k i).base)
    (hmeet : ∀ i j, i ≠ j → Set.range (k i).base ∩ Set.range (k j).base ⊆
      Set.range (D.toGlueData.f i j ≫ k i).base) :
    Function.Injective (D.desc k h).base := by
  intro p q hpq
  obtain ⟨i, x, rfl⟩ := D.ι_jointly_surjective p
  obtain ⟨j, y, rfl⟩ := D.ι_jointly_surjective q
  rw [D.base_ι_desc k h i x, D.base_ι_desc k h j y] at hpq
  obtain rfl | hij := eq_or_ne i j
  · exact congrArg (D.toGlueData.ι i).base (hinj i hpq)
  obtain ⟨z, hz⟩ := hmeet i j hij ⟨⟨x, rfl⟩, ⟨y, hpq.symm⟩⟩
  rw [LocallyRingedSpace.comp_base, ConcreteCategory.comp_apply] at hz
  have hzx : (D.toGlueData.f i j).base z = x := hinj i hz
  have hzy : (D.toGlueData.t i j ≫ D.toGlueData.f j i).base z = y := by
    refine hinj j ?_
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun φ : D.toGlueData.V (i, j) ⟶ Y => φ.base) (h i j)) z
    rw [LocallyRingedSpace.comp_base, LocallyRingedSpace.comp_base,
      LocallyRingedSpace.comp_base] at hh
    rw [LocallyRingedSpace.comp_base, ConcreteCategory.comp_apply]
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply] at hh
    rw [← hh, hz, hpq]
  have hgc := ConcreteCategory.congr_hom
    (congrArg (fun φ : D.toGlueData.V (i, j) ⟶ D.toGlueData.glued => φ.base)
      (D.toGlueData.glue_condition i j)) z
  rw [LocallyRingedSpace.comp_base, LocallyRingedSpace.comp_base,
    LocallyRingedSpace.comp_base, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply] at hgc
  rw [← hzx, ← hzy, LocallyRingedSpace.comp_base, ConcreteCategory.comp_apply]
  exact hgc.symm

/-- **The glued morphism is an open map** as soon as every piece is: the image of an open set is
the union of the images of its chart-local traces (`image_desc`). -/
theorem isOpenMap_desc (hopen : ∀ i, IsOpenMap (k i).base) :
    IsOpenMap (D.desc k h).base := by
  intro U hU
  rw [D.image_desc k h U]
  exact isOpen_iUnion fun i =>
    hopen i _ ((D.toGlueData.ι i).base.hom.continuous.isOpen_preimage U hU)

/-- **The glued morphism is a topological open embedding.** -/
theorem isOpenEmbedding_desc (hopen : ∀ i, IsOpenMap (k i).base)
    (hinj : ∀ i, Function.Injective (k i).base)
    (hmeet : ∀ i j, i ≠ j → Set.range (k i).base ∩ Set.range (k j).base ⊆
      Set.range (D.toGlueData.f i j ≫ k i).base) :
    IsOpenEmbedding (D.desc k h).base :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (by fun_prop)
    (D.injective_desc k h hinj hmeet) (D.isOpenMap_desc k h hopen)

/-- **The glued morphism induces isomorphisms on stalks**, by two-out-of-three against the chart
inclusion `ι i`, which is an open immersion, and the piece `k i`, which is one by hypothesis. -/
theorem isIso_stalkMap_desc (hoi : ∀ i, LocallyRingedSpace.IsOpenImmersion (k i))
    (x : D.toGlueData.glued) : IsIso ((D.desc k h).stalkMap x) := by
  obtain ⟨i, z, rfl⟩ := D.ι_jointly_surjective x
  haveI := hoi i
  haveI hki : IsIso ((k i).stalkMap z) := inferInstance
  haveI hcomp : IsIso ((D.toGlueData.ι i ≫ D.desc k h).stalkMap z) := by
    rw [D.ι_desc k h i]; exact hki
  rw [LocallyRingedSpace.stalkMap_comp] at hcomp
  exact (CategoryTheory.isIso_comp_right_iff ((D.desc k h).stalkMap _)
    ((D.toGlueData.ι i).stalkMap z)).mp hcomp

/-- **The criterion: a morphism glued from open immersions that meet only along the glue overlaps
is an open immersion.** An open topological embedding with isomorphisms on stalks, via
`LocallyRingedSpace.IsOpenImmersion.of_stalk_iso`. -/
theorem isOpenImmersion_desc (hoi : ∀ i, LocallyRingedSpace.IsOpenImmersion (k i))
    (hmeet : ∀ i j, i ≠ j → Set.range (k i).base ∩ Set.range (k j).base ⊆
      Set.range (D.toGlueData.f i j ≫ k i).base) :
    LocallyRingedSpace.IsOpenImmersion (D.desc k h) := by
  haveI : ∀ x, IsIso ((D.desc k h).stalkMap x) := D.isIso_stalkMap_desc k h hoi
  exact LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _
    (D.isOpenEmbedding_desc k h (fun i => (hoi i).base_open.isOpenMap)
      (fun i => (hoi i).base_open.injective) hmeet)

/-- **A glued morphism that is an open immersion and surjective on points is an isomorphism.** -/
theorem isIso_desc (hoi : ∀ i, LocallyRingedSpace.IsOpenImmersion (k i))
    (hmeet : ∀ i j, i ≠ j → Set.range (k i).base ∩ Set.range (k j).base ⊆
      Set.range (D.toGlueData.f i j ≫ k i).base)
    (hsurj : Function.Surjective (D.desc k h).base) : IsIso (D.desc k h) := by
  haveI := D.isOpenImmersion_desc k h hoi hmeet
  haveI : Epi (D.desc k h).base := (TopCat.epi_iff_surjective _).2 hsurj
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

end LocallyRingedSpace.GlueData

end AlgebraicGeometry

end
