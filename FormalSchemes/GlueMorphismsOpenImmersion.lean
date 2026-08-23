import FormalSchemes.GlueMorphisms

set_option linter.style.header false

/-!
# When a morphism glued out of a formal scheme is an open immersion

`AlgebraicGeometry.FormalScheme.GlueData.glueMorphisms` (`FormalSchemes.GlueMorphisms`) assembles a
family `k i : U i ⟶ Y` of morphisms out of the pieces of a glue datum, agreeing on the double
overlaps, into a single morphism `glued ⟶ Y`. This file gives the criterion under which that glued
morphism is an **open immersion**, i.e. under which the glued object is an open subspace of `Y`:

> each `k i` is an open immersion, **and** the pieces meet in `Y` only where the glue datum says
> they do — `range (k i) ∩ range (k j) ⊆ range (f i j ≫ k i)`.

The second condition is the whole content. Without it the glued object can map onto the union of
the `range (k i)` while identifying too few points: the line with two origins is glued from two
copies of `𝔸¹` whose images in `𝔸¹` meet in all of `𝔸¹ ∖ {0}` *plus* the origin, which is more
than the overlap accounts for. The hypothesis is exactly what rules that out, and it is what makes
the proof of injectivity go through — everything else here is formal.

## Comparison with `FormalScheme.OpenCover.fromGlued`

`FormalSchemes.OpenCoverGlueMorphisms` proves the special case where the `k i` are the members of an
open cover *of `Y` itself*: there `fromGlued` is not merely an open immersion but an isomorphism,
because the cover is jointly surjective. The argument there routes injectivity through the pullback
`U i ×_Y U j` and openness through `GlueData.isOpen_iff`. Neither is needed here: the overlap
hypothesis above is weaker than "the overlap *is* the pullback" and is checked directly, and the
image of an open set is computed chartwise as `⋃ i, k i '' (ι i ⁻¹' U)`, which is open because each
`k i` is. The two files are therefore independent rather than one generalising the other.

## Main results

* `AlgebraicGeometry.FormalScheme.GlueData.range_glueMorphisms`: the range of the glued morphism is
  the union of the ranges of the `k i`.
* `AlgebraicGeometry.FormalScheme.GlueData.image_glueMorphisms`: the image of a set, computed
  chartwise.
* `AlgebraicGeometry.FormalScheme.GlueData.injective_glueMorphisms`: injectivity on points, from the
  overlap hypothesis.
* `AlgebraicGeometry.FormalScheme.GlueData.isOpenMap_glueMorphisms`,
  `isOpenEmbedding_glueMorphisms`, `isIso_stalkMap_glueMorphisms`.
* `AlgebraicGeometry.FormalScheme.GlueData.isOpenImmersion_glueMorphisms`: **the criterion.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6, §10.15.
* `AlgebraicGeometry.Scheme.GlueData` (Mathlib), the scheme analogue of the gluing bookkeeping.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

namespace FormalScheme.GlueData

variable (D : FormalScheme.GlueData.{u}) {Y : LocallyRingedSpace.{u}}
variable (k : ∀ i, D.toLocallyRingedSpaceGlueData.toGlueData.U i ⟶ Y)
variable (h : ∀ i j, D.toLocallyRingedSpaceGlueData.toGlueData.f i j ≫ k i =
  D.toLocallyRingedSpaceGlueData.toGlueData.t i j ≫
    D.toLocallyRingedSpaceGlueData.toGlueData.f j i ≫ k j)

/-- (Helper) The glued morphism sends `ι i z` to `k i z`.

This is `ι_glueMorphisms` read on points. The last step is term-mode rather than a `rw`: rewriting
with `ConcreteCategory.comp_apply` in the goal fails at `instances` transparency, because the index
`i` lives at `D.toLocallyRingedSpaceGlueData.J` while the pieces are indexed through
`toGlueData.U`, and the two agree only after unfolding. -/
private theorem base_ι_glueMorphisms (i : D.toLocallyRingedSpaceGlueData.J)
    (z : D.toLocallyRingedSpaceGlueData.U i) :
    (D.glueMorphisms k h).base ((D.ι i).base z) = (k i).base z := by
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun φ : D.toLocallyRingedSpaceGlueData.U i ⟶ Y => φ.base)
      (D.ι_glueMorphisms k h i)) z
  rw [LocallyRingedSpace.comp_base] at hc
  exact (ConcreteCategory.comp_apply _ _ z).symm.trans hc

/-- **The range of the glued morphism is the union of the ranges of the chart morphisms.** One
inclusion is `ι_glueMorphisms`; the other is joint surjectivity of the glue inclusions. -/
theorem range_glueMorphisms :
    Set.range (D.glueMorphisms k h).base = ⋃ i, Set.range (k i).base := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨p, rfl⟩
    obtain ⟨i, z, rfl⟩ := D.ι_jointly_surjective p
    exact Set.mem_iUnion.2 ⟨i, z, (D.base_ι_glueMorphisms k h i z).symm⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨z, rfl⟩ := hi
    exact ⟨(D.ι i).base z, D.base_ι_glueMorphisms k h i z⟩

/-- **The image of a set under the glued morphism, computed chartwise.** Every point of the glued
space lies on some chart, so the image of `U` is the union over the charts of the images of its
chart-local traces. This is what makes the open-map property free once each `k i` is open. -/
theorem image_glueMorphisms (U : Set (D.gluedFormalScheme).toLocallyRingedSpace) :
    (D.glueMorphisms k h).base '' U = ⋃ i, (k i).base '' ((D.ι i).base ⁻¹' U) := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨i, z, rfl⟩ := D.ι_jointly_surjective p
    exact Set.mem_iUnion.2 ⟨i, z, hp, (D.base_ι_glueMorphisms k h i z).symm⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨z, hz, rfl⟩ := hi
    exact ⟨(D.ι i).base z, hz, D.base_ι_glueMorphisms k h i z⟩

/-- **The glued morphism is injective on points**, provided each chart morphism is and the charts
meet in `Y` only along their glue overlap.

This is the one step with content. Two points of the glued space are `ι i x` and `ι j y`; if their
images agree then that common image lies in `range (k i) ∩ range (k j)`, so by hypothesis it is
`(f i j ≫ k i) z` for some point `z` of the overlap. Injectivity of `k i` and of `k j` identifies
`x` with `f i j z` and `y` with `(t i j ≫ f j i) z`, and the glue condition then says the two glued
points are equal. Dropping the overlap hypothesis breaks exactly here, and the line with two origins
is the standard counterexample. -/
theorem injective_glueMorphisms
    (hinj : ∀ i, Function.Injective (k i).base)
    (hmeet : ∀ i j, Set.range (k i).base ∩ Set.range (k j).base ⊆
      Set.range (D.toLocallyRingedSpaceGlueData.toGlueData.f i j ≫ k i).base) :
    Function.Injective (D.glueMorphisms k h).base := by
  intro p q hpq
  obtain ⟨i, x, rfl⟩ := D.ι_jointly_surjective p
  obtain ⟨j, y, rfl⟩ := D.ι_jointly_surjective q
  rw [D.base_ι_glueMorphisms k h i x, D.base_ι_glueMorphisms k h j y] at hpq
  obtain ⟨z, hz⟩ := hmeet i j ⟨⟨x, rfl⟩, ⟨y, hpq.symm⟩⟩
  rw [LocallyRingedSpace.comp_base, ConcreteCategory.comp_apply] at hz
  have hzx : (D.toLocallyRingedSpaceGlueData.toGlueData.f i j).base z = x := hinj i hz
  have hzy : (D.toLocallyRingedSpaceGlueData.toGlueData.t i j ≫
      D.toLocallyRingedSpaceGlueData.toGlueData.f j i).base z = y := by
    refine hinj j ?_
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun φ : D.toLocallyRingedSpaceGlueData.toGlueData.V (i, j) ⟶ Y => φ.base)
        (h i j)) z
    rw [LocallyRingedSpace.comp_base, LocallyRingedSpace.comp_base,
      LocallyRingedSpace.comp_base] at hh
    rw [LocallyRingedSpace.comp_base, ConcreteCategory.comp_apply]
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply] at hh
    rw [← hh, hz, hpq]
  have hgc := ConcreteCategory.congr_hom
    (congrArg (fun φ : D.toLocallyRingedSpaceGlueData.toGlueData.V (i, j) ⟶
        D.toLocallyRingedSpaceGlueData.toGlueData.glued => φ.base)
      (D.toLocallyRingedSpaceGlueData.toGlueData.glue_condition i j)) z
  rw [LocallyRingedSpace.comp_base, LocallyRingedSpace.comp_base,
    LocallyRingedSpace.comp_base, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply] at hgc
  rw [← hzx, ← hzy, LocallyRingedSpace.comp_base, ConcreteCategory.comp_apply]
  exact hgc.symm

/-- **The glued morphism is an open map** as soon as every chart morphism is: the image of an open
set is the union of the images of its chart-local traces (`image_glueMorphisms`). -/
theorem isOpenMap_glueMorphisms (hopen : ∀ i, IsOpenMap (k i).base) :
    IsOpenMap (D.glueMorphisms k h).base := by
  intro U hU
  rw [D.image_glueMorphisms k h U]
  exact isOpen_iUnion fun i => hopen i _ ((D.ι i).base.hom.continuous.isOpen_preimage U hU)

/-- **The glued morphism is a topological open embedding.** -/
theorem isOpenEmbedding_glueMorphisms (hopen : ∀ i, IsOpenMap (k i).base)
    (hinj : ∀ i, Function.Injective (k i).base)
    (hmeet : ∀ i j, Set.range (k i).base ∩ Set.range (k j).base ⊆
      Set.range (D.toLocallyRingedSpaceGlueData.toGlueData.f i j ≫ k i).base) :
    IsOpenEmbedding (D.glueMorphisms k h).base :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (by fun_prop)
    (D.injective_glueMorphisms k h hinj hmeet) (D.isOpenMap_glueMorphisms k h hopen)

/-- **The glued morphism induces isomorphisms on stalks**, by two-out-of-three against the glue
inclusion `ι i`, which is an open immersion, and the chart morphism `k i`, which is one by
hypothesis. Mirrors `FormalScheme.OpenCover.isIso_fromGlued_stalkMap`. -/
theorem isIso_stalkMap_glueMorphisms (hoi : ∀ i, LocallyRingedSpace.IsOpenImmersion (k i))
    (x : (D.gluedFormalScheme).toLocallyRingedSpace) :
    IsIso ((D.glueMorphisms k h).stalkMap x) := by
  obtain ⟨i, z, rfl⟩ := D.ι_jointly_surjective x
  haveI := hoi i
  haveI hki : IsIso ((k i).stalkMap z) := inferInstance
  haveI hcomp : IsIso ((D.ι i ≫ D.glueMorphisms k h).stalkMap z) := by
    rw [D.ι_glueMorphisms k h i]; exact hki
  rw [LocallyRingedSpace.stalkMap_comp] at hcomp
  exact (CategoryTheory.isIso_comp_right_iff ((D.glueMorphisms k h).stalkMap _)
    ((D.ι i).stalkMap z)).mp hcomp

/-- **The criterion: a morphism glued from open immersions that meet only along the glue overlaps is
an open immersion.** An open topological embedding with isomorphisms on stalks, via
`LocallyRingedSpace.IsOpenImmersion.of_stalk_iso`. -/
theorem isOpenImmersion_glueMorphisms (hoi : ∀ i, LocallyRingedSpace.IsOpenImmersion (k i))
    (hmeet : ∀ i j, Set.range (k i).base ∩ Set.range (k j).base ⊆
      Set.range (D.toLocallyRingedSpaceGlueData.toGlueData.f i j ≫ k i).base) :
    LocallyRingedSpace.IsOpenImmersion (D.glueMorphisms k h) := by
  haveI : ∀ x, IsIso ((D.glueMorphisms k h).stalkMap x) := D.isIso_stalkMap_glueMorphisms k h hoi
  exact LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _
    (D.isOpenEmbedding_glueMorphisms k h (fun i => (hoi i).base_open.isOpenMap)
      (fun i => (hoi i).base_open.injective) hmeet)

end FormalScheme.GlueData

end AlgebraicGeometry

end
