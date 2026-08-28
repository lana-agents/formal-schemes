import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
import Mathlib.Geometry.RingedSpace.PresheafedSpace.HasColimits

set_option linter.style.header false

/-!
# Sections of a coequalizer of sheafed spaces are determined by their pullback

Mathlib computes the sections of a colimit of presheafed spaces as a componentwise limit
(`PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit`), but the only place it is put to work
is `PresheafedSpace.GlueData.ιIsOpenImmersion`, which rests on two hundred-odd lines of machinery
specific to the `WalkingMultispan` diagram of a glue datum. Nothing is said about the sections of a
**coequalizer**, which is the shape a quotient by a group action has.

This file records the first thing that route gives, and it is cheap: **the comparison map on
sections is a monomorphism.** A section of the coequalizer is determined by its pullback along the
projection.

## The three ingredients

* `CategoryTheory.Limits.mono_π_op_one`: the leg at `op one` of a limit cone over
  `WalkingParallelPairᵒᵖ` — which is the shape `componentwiseDiagram` takes on a coequalizer — is a
  monomorphism, because the leg at `op zero` factors through it. This is the abstract content of
  "the equaliser injects into the first object", stated where the limit is not presented as an
  equaliser fork.
* `AlgebraicGeometry.PresheafedSpace.mono_coequalizer_π_c_app`: for presheafed spaces this is
  immediate from `colimitPresheafObjIsoComponentwiseLimit_hom_π`, which says the comparison map on
  sections *is* that projection up to an isomorphism.
* `AlgebraicGeometry.SheafedSpace.mono_coequalizer_π_c_app`: one layer up, along the rewrite chain
  `ι_comp_coequalizerComparison` → `PreservesCoequalizer.iso` →
  `colimitPresheafObjIsoComponentwiseLimit_hom_π`. That chain is not invented here: it is exactly
  the one Mathlib performs in `LocallyRingedSpace.HasCoequalizer.coequalizer_π_app_isLocalHom`
  (`Mathlib/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`), which is the demonstration
  that the componentwise-limit description reaches a coequalizer's sections through the
  `SheafedSpace`/`PresheafedSpace` layers.

## What this does not do

It does not identify the image. For a quotient by a group action the expected statement is that
the image is exactly the invariant sections, and that is a genuine surjectivity claim about the
componentwise limit which nothing here supplies. Monomorphy is the half that follows formally.

It also stops at `SheafedSpace`. Transporting to `LocallyRingedSpace` — so that the statement reads
directly about `CategoryTheory.actionQuotientπ` — needs the `PreservesCoequalizer.iso` for
`LocallyRingedSpace.forgetToSheafedSpace` together with the fact that `Opens.map` along that
isomorphism is a bijection on opens. That is bookkeeping rather than mathematics, but it was not
run, and saying so is cheaper than a statement whose proof is asserted.

## References

* [The Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- **The leg at `op one` of a limit cone over `WalkingParallelPairᵒᵖ` is a monomorphism.**

Such a cone is determined by that leg: the leg at `op zero` is it followed by `F.map (op left)`.
So two maps into the cone point agreeing after the `op one` leg agree after both legs, hence are
equal. This is the abstract content of "the equaliser injects into the first object", stated where
the limit is not presented as an equaliser fork. -/
theorem mono_π_op_one {F : WalkingParallelPairᵒᵖ ⥤ C} {c : Cone F} (hc : IsLimit c) :
    Mono (c.π.app (op WalkingParallelPair.one)) := by
  constructor
  intro Z p q hpq
  refine hc.hom_ext fun j => ?_
  obtain ⟨j⟩ := j
  cases j with
  | zero =>
    have hw : c.π.app (op WalkingParallelPair.one) ≫ F.map (op WalkingParallelPairHom.left) =
        c.π.app (op WalkingParallelPair.zero) := c.w (op WalkingParallelPairHom.left)
    calc p ≫ c.π.app (op WalkingParallelPair.zero)
        = (p ≫ c.π.app (op WalkingParallelPair.one)) ≫
            F.map (op WalkingParallelPairHom.left) := by rw [Category.assoc, hw]
      _ = (q ≫ c.π.app (op WalkingParallelPair.one)) ≫
            F.map (op WalkingParallelPairHom.left) := by rw [hpq]
      _ = q ≫ c.π.app (op WalkingParallelPair.zero) := by rw [Category.assoc, hw]
  | one => exact hpq

/-- The `limit.π` phrasing of `mono_π_op_one`. -/
instance mono_limit_π_op_one (F : WalkingParallelPairᵒᵖ ⥤ C) [HasLimit F] :
    Mono (limit.π F (op WalkingParallelPair.one)) :=
  mono_π_op_one (limit.isLimit F)

end CategoryTheory.Limits

namespace AlgebraicGeometry.PresheafedSpace

variable {C : Type u} [Category.{v} C] [Limits.HasLimits C]

/-- **A section of a coequalizer of presheafed spaces is determined by its pullback along the
projection.**

`PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π` says the comparison map on
sections *is* the componentwise limit's projection, up to an isomorphism; for a coequalizer the
componentwise diagram is indexed by `WalkingParallelPairᵒᵖ` and the projection in question is the
one at `op one`, which is a monomorphism by `mono_π_op_one`. -/
theorem mono_coequalizer_π_c_app {X Y : PresheafedSpace C} (f g : X ⟶ Y)
    (V : Opens (Limits.coequalizer f g).carrier) :
    Mono ((Limits.coequalizer.π f g).c.app (op V)) := by
  have h : Limits.coequalizer.π f g =
      Limits.colimit.ι (Limits.parallelPair f g) WalkingParallelPair.one := rfl
  rw [h, ← PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
  exact mono_comp' inferInstance (mono_π_op_one (Limits.limit.isLimit _))

end AlgebraicGeometry.PresheafedSpace

namespace AlgebraicGeometry.SheafedSpace

set_option linter.style.setOption false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- The same two transparency options `coequalizer_π_app_isLocalHom` needs, for the same reason: the
-- rewrite identifies the coequalizer's `c.app` with a composite through the componentwise limit,
-- and matching the two sides is a defeq check across the `SheafedSpace`/`PresheafedSpace` layers.
/-- **A section of a coequalizer of sheafed spaces is determined by its pullback along the
projection.** The comparison map on sections is a monomorphism.

The proof is the rewrite chain of `LocallyRingedSpace.HasCoequalizer.coequalizer_π_app_isLocalHom`,
which exhibits `(coequalizer.π f g).c.app (op V)` as an isomorphism followed by the componentwise
limit's projection at `op one`; that projection is a monomorphism by `mono_limit_π_op_one` and the
other two factors are isomorphisms. -/
theorem mono_coequalizer_π_c_app {X Y : SheafedSpace CommRingCat.{u}} (f g : X ⟶ Y)
    (V : Opens (Limits.coequalizer f g).carrier) :
    Mono ((Limits.coequalizer.π f g :).hom.c.app (op V)) := by
  have h := ι_comp_coequalizerComparison f g SheafedSpace.forgetToPresheafedSpace
  dsimp at h
  rw [← PreservesCoequalizer.iso_hom] at h
  rw [← h, PresheafedSpace.comp_c_app,
    ← PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
  haveI : IsIso (PreservesCoequalizer.iso
      SheafedSpace.forgetToPresheafedSpace f g).hom.c := inferInstance
  infer_instance

/-- **The section-comparison map of a coequalizer of sheafed spaces is injective.** The
`CommRingCat`-flavoured restatement of `mono_coequalizer_π_c_app`. -/
theorem injective_coequalizer_π_c_app {X Y : SheafedSpace CommRingCat.{u}} (f g : X ⟶ Y)
    (V : Opens (Limits.coequalizer f g).carrier) :
    Function.Injective ((Limits.coequalizer.π f g :).hom.c.app (op V)) :=
  haveI := mono_coequalizer_π_c_app f g V
  CategoryTheory.ConcreteCategory.injective_of_mono_of_preservesPullback _

end AlgebraicGeometry.SheafedSpace
