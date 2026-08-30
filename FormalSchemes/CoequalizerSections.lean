import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
import Mathlib.Geometry.RingedSpace.PresheafedSpace.HasColimits

set_option linter.style.header false

/-!
# The sections of a coequalizer of presheafed spaces are the equalised sections

Mathlib computes the sections of a colimit of presheafed spaces as a componentwise limit
(`PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit`), but it is put to work in only three
places: `PresheafedSpace.GlueData.ιIsOpenImmersion`, which rests on two hundred-odd lines of
machinery specific to the `WalkingMultispan` diagram of a glue datum;
`SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion`, for a coproduct; and
`LocallyRingedSpace.HasCoequalizer.coequalizer_π_app_isLocalHom`, which is the navigation reused
below. Nothing was said about what the sections of a **coequalizer** *are*, and that is the shape a
quotient by a group action has.

This file says it:

> `s : 𝒪_Y(π⁻¹ V)` is the pullback of a section of the coequalizer over `V` **if and only if**
> the two componentwise pullbacks of `s` to `X` agree.

Both halves are here. Injectivity is formal — it is the abstract "an equaliser injects into the
first object", and needs nothing but the cone identities. Surjectivity is the half that has to
descend to elements, and it is where the componentwise-limit description earns its keep.

## How the two halves are proved

The index category of `componentwiseDiagram` on a coequalizer is `WalkingParallelPairᵒᵖ`, whose
two arrows run `op one ⟶ op zero`. So a cone over it is exactly a fork, and the leg at `op one`
is the equaliser inclusion. That is `mono_π_op_one` (injectivity) and `exists_eq_π_app_op_one`
(surjectivity), and neither knows anything about spaces.

`exists_eq_π_app_op_one` is where concreteness enters: to *produce* a section of the coequalizer
one has to name an element of a limit, and that is `Types.isLimitEquivSections` applied to
`isLimitOfPreserves (forget C)`. The compatible family it needs has two entries — `x` at `op one`
and `F.map (op left) x` at `op zero` — and the hypothesis is exactly what makes the `op right`
component of the compatibility square commute.

Transporting to spaces is then the four-line rewrite chain that Mathlib itself performs in
`LocallyRingedSpace.HasCoequalizer.coequalizer_π_app_isLocalHom`
(`Mathlib/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`).

## Main results

* `CategoryTheory.Limits.exists_eq_π_app_op_one_iff`: the abstract statement — the image of the
  `op one` leg of a limit cone over `WalkingParallelPairᵒᵖ` is exactly the equalised elements.
* `AlgebraicGeometry.PresheafedSpace.exists_c_app_eq_iff`: the same for a coequalizer of
  presheafed spaces, with the condition phrased by `componentwiseDiagram`.
* `AlgebraicGeometry.PresheafedSpace.exists_c_app_eq_iff_map_eq`: the same with the condition
  written out as "the pullback along `f` equals the pullback along `g`", which is the form a
  geometric argument wants.
* `AlgebraicGeometry.PresheafedSpace.injective_coequalizer_π_c_app`,
  `AlgebraicGeometry.SheafedSpace.injective_coequalizer_π_c_app`: the injectivity half.
* `AlgebraicGeometry.PresheafedSpace.colimit_section_ext`: a section of a colimit of presheafed
  spaces is determined by its pullbacks along the legs — general in the diagram shape, and the
  tool the *coproduct* case needs.

## What this does not do

**The surjectivity half stops at `PresheafedSpace`.** The `SheafedSpace` statements below are the
injectivity half only. The obstacle is not that the transport is unavailable — it is
`ι_comp_coequalizerComparison` followed by `PreservesCoequalizer.iso`, exactly as in the
monomorphy proof, and running that on a `SheafedSpace` coequalizer gives

```
h : coequalizer.π f.hom g.hom ≫ (PreservesCoequalizer.iso forgetToPresheafedSpace f g).hom
      = (coequalizer.π f g).hom
```

— the obstacle is that this transport moves the **open** as well as the section: the
`PresheafedSpace` statement then lives at `(Opens.map (PreservesCoequalizer.iso …).hom.base).obj V`
rather than at `V`, and identifying the two costs an `eqToHom` transport of `s` itself. That was
measured, not run, and it is the successor to this file rather than a gap in it.

**Nothing here reaches `LocallyRingedSpace` either.** Transporting so that the statement reads
directly about `CategoryTheory.actionQuotientπ` needs the `PreservesCoequalizer.iso` for
`LocallyRingedSpace.forgetToSheafedSpace` together with the fact that `Opens.map` along that
isomorphism is a bijection on opens. That is bookkeeping rather than mathematics, but it was not
run, and saying so is cheaper than a statement whose proof is asserted.

It also does not identify the equalised sections geometrically. For a quotient by a group action,
`f` and `g` are `CategoryTheory.actionQuotientLeft` and `actionQuotientRight`, whose common source
is the coproduct `∐_{g : G} X`; turning "equalised" into "invariant under every `a g`" needs the
sections of that coproduct to be detected by the coproduct legs. That step *is* here, as
`colimit_section_ext`; what is not here is the identification of each leg's pullback with the
action of the corresponding `a g`, which is a statement about `actionQuotientLeft`/`Right` and
belongs with them. Nor is the step after it, that a separating open
carries the invariant sections isomorphically, which is where the disjointness of the translates
finally enters.

## References

* [The Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open WalkingParallelPair WalkingParallelPairHom

universe w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- **The leg at `op one` of a limit cone over `WalkingParallelPairᵒᵖ` is a monomorphism.**

Such a cone is determined by that leg: the leg at `op zero` is it followed by `F.map (op left)`.
So two maps into the cone point agreeing after the `op one` leg agree after both legs, hence are
equal. This is the abstract content of "the equaliser injects into the first object", stated where
the limit is not presented as an equaliser fork. -/
theorem mono_π_op_one {F : WalkingParallelPairᵒᵖ ⥤ C} {c : Cone F} (hc : IsLimit c) :
    Mono (c.π.app (op one)) := by
  constructor
  intro Z p q hpq
  refine hc.hom_ext fun j => ?_
  obtain ⟨j⟩ := j
  cases j with
  | zero =>
    have hw : c.π.app (op one) ≫ F.map (op left) = c.π.app (op zero) := c.w (op left)
    calc p ≫ c.π.app (op zero)
        = (p ≫ c.π.app (op one)) ≫ F.map (op left) := by rw [Category.assoc, hw]
      _ = (q ≫ c.π.app (op one)) ≫ F.map (op left) := by rw [hpq]
      _ = q ≫ c.π.app (op zero) := by rw [Category.assoc, hw]
  | one => exact hpq

/-- The `limit.π` phrasing of `mono_π_op_one`. -/
instance mono_limit_π_op_one (F : WalkingParallelPairᵒᵖ ⥤ C) [HasLimit F] :
    Mono (limit.π F (op one)) :=
  mono_π_op_one (limit.isLimit F)

/-- **The `op one` leg of any cone over `WalkingParallelPairᵒᵖ` is equalised by the two arrows.**
Both composites are the leg at `op zero`. This is the trivial half of the description of the image
of that leg, and it holds for a cone, not only for a limit cone. -/
theorem π_app_op_one_map_op_left {F : WalkingParallelPairᵒᵖ ⥤ C} (c : Cone F) :
    c.π.app (op one) ≫ F.map (op left) = c.π.app (op one) ≫ F.map (op right) := by
  have hl : c.π.app (op one) ≫ F.map (op left) = c.π.app (op zero) := c.w (op left)
  have hr : c.π.app (op one) ≫ F.map (op right) = c.π.app (op zero) := c.w (op right)
  rw [hl, hr]

variable {FC : C → C → Type*} {CC : C → Type w}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

/-- **An element equalised by the two arrows lifts to the limit.** The converse of
`π_app_op_one_map_op_left`, and the half that needs elements: the lift is produced by naming the
compatible family `op one ↦ x`, `op zero ↦ F.map (op left) x` and feeding it to
`Types.isLimitEquivSections` for the limit cone that `forget C` preserves. The hypothesis is used
exactly once, for the `op right` leg of the compatibility square. -/
theorem exists_eq_π_app_op_one {F : WalkingParallelPairᵒᵖ ⥤ C} {c : Cone F} (hc : IsLimit c)
    [PreservesLimit F (CategoryTheory.forget C)] (x : ToType (F.obj (op one)))
    (h : (F.map (op left)) x = (F.map (op right)) x) :
    ∃ y : ToType c.pt, (c.π.app (op one)) y = x := by
  have hT : IsLimit ((CategoryTheory.forget C).mapCone c) :=
    isLimitOfPreserves (CategoryTheory.forget C) hc
  refine ⟨(Types.isLimitEquivSections hT).symm ⟨fun j => ?_, ?_⟩, ?_⟩
  · exact match j with
      | ⟨WalkingParallelPair.one⟩ => x
      | ⟨WalkingParallelPair.zero⟩ => (F.map (op left)) x
  · rintro ⟨j⟩ ⟨j'⟩ ⟨φ⟩
    cases φ with
    | left => exact rfl
    | right => exact h.symm
    | id j =>
      cases j <;>
      · change ((F ⋙ CategoryTheory.forget C).map (𝟙 _)) _ = _
        rw [Functor.map_id]
        rfl
  · exact Types.isLimitEquivSections_symm_apply hT _ (op one)

/-- **The image of the `op one` leg of a limit cone is exactly the equalised elements.** -/
theorem exists_eq_π_app_op_one_iff {F : WalkingParallelPairᵒᵖ ⥤ C} {c : Cone F} (hc : IsLimit c)
    [PreservesLimit F (CategoryTheory.forget C)] (x : ToType (F.obj (op one))) :
    (∃ y : ToType c.pt, (c.π.app (op one)) y = x) ↔
      (F.map (op left)) x = (F.map (op right)) x := by
  refine ⟨?_, exists_eq_π_app_op_one hc x⟩
  rintro ⟨y, rfl⟩
  have := ConcreteCategory.congr_hom (π_app_op_one_map_op_left c) y
  simpa only [ConcreteCategory.comp_apply] using this

end CategoryTheory.Limits

namespace AlgebraicGeometry.PresheafedSpace

section Mono

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
      Limits.colimit.ι (Limits.parallelPair f g) one := rfl
  rw [h, ← PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
  exact mono_comp' inferInstance (mono_π_op_one (Limits.limit.isLimit _))

end Mono

section ColimitExt

/-- **A section of a colimit of presheafed spaces is determined by its pullbacks along the legs.**

General in the diagram shape, and the exact tool the *coproduct* case wants: to compare two
sections of `∐ᵢ Xᵢ` it is enough to compare them on each summand. It is
`Concrete.limit_ext` for the componentwise limit, moved across
`colimitPresheafObjIsoComponentwiseLimit` — which is injective because it is an isomorphism.

For a coequalizer this is weaker than `injective_coequalizer_π_c_app` (two legs rather than one),
so it is stated here for the shapes where there is no single mono leg.

The diagram shape `J` lives in its own universe, unrelated to the space's. That matters because the
shape a group action produces is `Discrete G` for the acting group `G`, which has no reason to sit
in the same universe as the space it acts on — `AlgebraicGeometry.tateInvPeriodAction` acts by
`Multiplicative ℤ` on a space over an arbitrary `R : Type u`. The three `Limits` instance arguments
are exactly what `SmallCategory J` used to supply silently; the proof is unchanged by the
generalisation, because `CategoryTheory.Limits.colimitPresheafObjIsoComponentwiseLimit` and
`AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π` are already
polymorphic in the shape. -/
theorem colimit_section_ext {J : Type w} [Category.{v} J]
    [Limits.HasColimitsOfShape J TopCat.{u}]
    [∀ X : TopCat.{u}, Limits.HasLimitsOfShape Jᵒᵖ (X.Presheaf CommRingCat.{u})]
    [Limits.HasLimitsOfShape Jᵒᵖ CommRingCat.{u}]
    (F : J ⥤ PresheafedSpace.{u, u + 1, u} CommRingCat.{u}) [Limits.HasColimit F]
    (U : Opens (Limits.colimit F).carrier)
    (s t : ToType ((Limits.colimit F).presheaf.obj (op U)))
    (h : ∀ j, ((Limits.colimit.ι F j).c.app (op U)) s = ((Limits.colimit.ι F j).c.app (op U)) t) :
    s = t := by
  have hiso : Function.Injective ((colimitPresheafObjIsoComponentwiseLimit F U).hom) :=
    (ConcreteCategory.bijective_of_isIso _).1
  apply hiso
  refine Limits.Concrete.limit_ext _ _ _ fun j => ?_
  obtain ⟨j⟩ := j
  have a := ConcreteCategory.congr_hom
    (colimitPresheafObjIsoComponentwiseLimit_hom_π F U j) s
  have b := ConcreteCategory.congr_hom
    (colimitPresheafObjIsoComponentwiseLimit_hom_π F U j) t
  simp only [ConcreteCategory.comp_apply] at a b
  rw [a, b]
  exact h j

end ColimitExt

section Sections

variable {X Y : PresheafedSpace.{u} CommRingCat.{u}} (f g : X ⟶ Y)
variable (V : Opens (Limits.coequalizer f g).carrier)

/-- The componentwise diagram of a coequalizer, at `op one`, is the sections of `Y` over the
preimage of `V` — by definition, not up to an isomorphism. -/
theorem componentwiseDiagram_parallelPair_obj_op_one :
    (componentwiseDiagram (Limits.parallelPair f g) V).obj (op one) =
      Y.presheaf.obj (op ((Opens.map (Limits.coequalizer.π f g).base).obj V)) :=
  rfl

/-- The componentwise diagram of a coequalizer, at `op zero`, is the sections of `X` over the
preimage of `V` along either composite. -/
theorem componentwiseDiagram_parallelPair_obj_op_zero :
    (componentwiseDiagram (Limits.parallelPair f g) V).obj (op zero) =
      X.presheaf.obj (op ((Opens.map (Limits.colimit.ι (Limits.parallelPair f g) zero).base).obj
        V)) :=
  rfl

/-- **The `op left` arrow of the componentwise diagram is `f` on sections**, followed by the
`eqToHom` identifying `f⁻¹ π⁻¹ V` with `(f ≫ π)⁻¹ V`. Stated so that the hypothesis of
`exists_c_app_eq_iff` can be checked against `f` rather than against `componentwiseDiagram`. -/
theorem componentwiseDiagram_parallelPair_map_op_left :
    (componentwiseDiagram (Limits.parallelPair f g) V).map (op left) =
      f.c.app (op ((Opens.map (Limits.coequalizer.π f g).base).obj V)) ≫
        X.presheaf.map (eqToHom (by
          rw [← Limits.colimit.w (Limits.parallelPair f g) left, comp_base]; rfl)) :=
  rfl

/-- **The `op right` arrow of the componentwise diagram is `g` on sections.** -/
theorem componentwiseDiagram_parallelPair_map_op_right :
    (componentwiseDiagram (Limits.parallelPair f g) V).map (op right) =
      g.c.app (op ((Opens.map (Limits.coequalizer.π f g).base).obj V)) ≫
        X.presheaf.map (eqToHom (by
          rw [← Limits.colimit.w (Limits.parallelPair f g) right, comp_base]; rfl)) :=
  rfl

/-- **An equalised section descends to the coequalizer.** The surjectivity half: if the two
componentwise pullbacks of `s` to `X` agree, then `s` is the pullback of a section of the
coequalizer over `V`. -/
theorem exists_c_app_eq
    (s : ToType (Y.presheaf.obj (op ((Opens.map (Limits.coequalizer.π f g).base).obj V))))
    (h : ((componentwiseDiagram (Limits.parallelPair f g) V).map (op left)) s =
      ((componentwiseDiagram (Limits.parallelPair f g) V).map (op right)) s) :
    ∃ t, ((Limits.coequalizer.π f g).c.app (op V)) t = s := by
  obtain ⟨y, hy⟩ := CategoryTheory.Limits.exists_eq_π_app_op_one
    (Limits.limit.isLimit (componentwiseDiagram (Limits.parallelPair f g) V)) s h
  refine ⟨(colimitPresheafObjIsoComponentwiseLimit (Limits.parallelPair f g) V).inv y, ?_⟩
  refine Eq.trans (ConcreteCategory.congr_hom
    (colimitPresheafObjIsoComponentwiseLimit_hom_π (Limits.parallelPair f g) V one)
    ((colimitPresheafObjIsoComponentwiseLimit (Limits.parallelPair f g) V).inv y)).symm ?_
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  exact hy

/-- **The sections of a coequalizer of presheafed spaces, exactly.** A section of `Y` over `π⁻¹ V`
descends to the coequalizer if and only if its two componentwise pullbacks to `X` agree; and by
`mono_coequalizer_π_c_app` the section it descends from is unique. -/
theorem exists_c_app_eq_iff
    (s : ToType (Y.presheaf.obj (op ((Opens.map (Limits.coequalizer.π f g).base).obj V)))) :
    (∃ t, ((Limits.coequalizer.π f g).c.app (op V)) t = s) ↔
      ((componentwiseDiagram (Limits.parallelPair f g) V).map (op left)) s =
        ((componentwiseDiagram (Limits.parallelPair f g) V).map (op right)) s := by
  refine ⟨?_, exists_c_app_eq f g V s⟩
  rintro ⟨t, rfl⟩
  refine (CategoryTheory.Limits.exists_eq_π_app_op_one_iff
    (Limits.limit.isLimit (componentwiseDiagram (Limits.parallelPair f g) V)) _).mp
    ⟨(colimitPresheafObjIsoComponentwiseLimit (Limits.parallelPair f g) V).hom t, ?_⟩
  have key := ConcreteCategory.congr_hom
    (colimitPresheafObjIsoComponentwiseLimit_hom_π (Limits.parallelPair f g) V one) t
  simp only [ConcreteCategory.comp_apply] at key
  exact key

/-- Pulling `π⁻¹ V` back along `f` gives the preimage of `V` under the colimit leg at `zero`,
because `f ≫ π` **is** that leg. -/
theorem preimage_preimage_coequalizer_π_left :
    (Opens.map f.base).obj ((Opens.map (Limits.coequalizer.π f g).base).obj V) =
      (Opens.map (Limits.colimit.ι (Limits.parallelPair f g) zero).base).obj V := by
  rw [← Limits.colimit.w (Limits.parallelPair f g) left, comp_base]
  rfl

/-- Pulling `π⁻¹ V` back along `g` gives the same open, because `g ≫ π` is also that leg. This
and `preimage_preimage_coequalizer_π_left` are what let the two pullbacks of a section be
compared at all. -/
theorem preimage_preimage_coequalizer_π_right :
    (Opens.map g.base).obj ((Opens.map (Limits.coequalizer.π f g).base).obj V) =
      (Opens.map (Limits.colimit.ι (Limits.parallelPair f g) zero).base).obj V := by
  rw [← Limits.colimit.w (Limits.parallelPair f g) right, comp_base]
  rfl

/-- **The sections of a coequalizer of presheafed spaces, with the condition written out.** The
same statement as `exists_c_app_eq_iff` with `componentwiseDiagram` unfolded: `s` descends exactly
when its pullbacks along `f` and along `g` — which live on the same open, by the two lemmas above
— agree. This is the form a geometric argument wants; the `componentwiseDiagram` form is the one
the proof is by. -/
theorem exists_c_app_eq_iff_map_eq
    (s : ToType (Y.presheaf.obj (op ((Opens.map (Limits.coequalizer.π f g).base).obj V)))) :
    (∃ t, ((Limits.coequalizer.π f g).c.app (op V)) t = s) ↔
      (X.presheaf.map (eqToHom (congrArg op (preimage_preimage_coequalizer_π_left f g V))))
          ((f.c.app (op ((Opens.map (Limits.coequalizer.π f g).base).obj V))) s) =
        (X.presheaf.map (eqToHom (congrArg op (preimage_preimage_coequalizer_π_right f g V))))
          ((g.c.app (op ((Opens.map (Limits.coequalizer.π f g).base).obj V))) s) := by
  rw [exists_c_app_eq_iff, componentwiseDiagram_parallelPair_map_op_left,
    componentwiseDiagram_parallelPair_map_op_right]
  exact Iff.rfl

/-- **The section-comparison map of a coequalizer of presheafed spaces is injective.** -/
theorem injective_coequalizer_π_c_app :
    Function.Injective ((Limits.coequalizer.π f g).c.app (op V)) :=
  haveI := mono_coequalizer_π_c_app f g V
  CategoryTheory.ConcreteCategory.injective_of_mono_of_preservesPullback _

/-- **The coequalizer of `f` with itself has exactly the sections of `Y`.** Both halves are used:
injectivity from `injective_coequalizer_π_c_app`, surjectivity from `exists_c_app_eq_iff_map_eq`,
whose condition is satisfied by *every* section when the two maps coincide. This is the universal
property's own prediction — `coequalizer f f` is `Y` — so it is the check that the description
above is not vacuous. -/
theorem bijective_coequalizer_self_π_c_app (W : Opens (Limits.coequalizer f f).carrier) :
    Function.Bijective ((Limits.coequalizer.π f f).c.app (op W)) := by
  refine ⟨injective_coequalizer_π_c_app f f W, fun s => ?_⟩
  refine (exists_c_app_eq_iff_map_eq f f W s).mpr ?_
  congr 1

end Sections

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
