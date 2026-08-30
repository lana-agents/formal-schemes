import FormalSchemes.GlobalSectionsHomGlue

set_option linter.style.header false

/-!
# Sections of a glued formal scheme are determined chart by chart

`AlgebraicGeometry.FormalScheme.OpenCover.eq_of_chart_c_app_eq`
(`FormalSchemes.GlobalSectionsHomGlue`) says a **global** section of a formal scheme is determined
by its pullbacks along the charts of an open cover. That is the only section-level statement the
tree has about a glued object, and the restriction to `⊤` is not incidental: its input,
`AlgebraicGeometry.LocallyRingedSpace.restrict_eq_of_c_app_top_eq`, is stated at `⊤` as well.

This file removes the restriction, and states the result for the patches of a
`AlgebraicGeometry.FormalScheme.GlueData` rather than for the charts of an
`AlgebraicGeometry.FormalScheme.OpenCover`. Both changes are wanted by any argument that computes
`Γ (X, U)` for a glued `X` and a *proper* open `U` — for instance the sections of the period-`q`
Tate quotient over the image of a saturation, which is what this file was written for.

## What is here

* `AlgebraicGeometry.LocallyRingedSpace.restrict_eq_of_c_app_eq`: the naturality step at an
  arbitrary pair `V ≤ W` instead of `V ≤ ⊤`. Same three-line proof as the `⊤` case — naturality of
  `f.c` along `V ≤ W`, then cancel the isomorphism `f.c.app (op V)`.
* `AlgebraicGeometry.FormalScheme.GlueData.eq_of_ι_c_app_eq`: **the extensionality statement.** Two
  sections of the glued space over any open `W` agreeing after every `(D.ι i).c.app (op W)` are
  equal.

## Why the patch version is not the cover version

`AlgebraicGeometry.FormalScheme.GlueData.openCover` presents the patches through
`(D.isFormalScheme i).choose`, an existential witness merely *isomorphic* to `D.U i`, and its
`map` is `(that isomorphism).hom ≫ D.ι i` rather than `D.ι i`. So specialising
`OpenCover.eq_of_chart_c_app_eq` to a glue datum leaves a `choose` in the statement and an
isomorphism in front of every `ι`. Going through
`AlgebraicGeometry.FormalScheme.GlueData.ι_jointly_surjective` directly avoids both, and
`AlgebraicGeometry.FormalScheme.GlueData.ι_isOpenImmersion` supplies the same `IsIso` that the
cover version gets from `PresheafedSpace.IsOpenImmersion.c_iso`.

The `IsIso` needed here is at `W ⊓ (range of ι i)` rather than at the whole range, so it comes
from `PresheafedSpace.IsOpenImmersion.c_iso'` and not from the instance:
`PresheafedSpace.IsOpenImmersion.c_iso` fires only on opens *syntactically* of the form
`(opensFunctor f).obj U`, and `W ⊓ (opensFunctor f).obj ⊤` is not one until
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inf_opensFunctor_top` rewrites it.

## References

* [The Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA) — gluing sheaves.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry CategoryTheory.Limits

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **A `c`-component that is invertible over `V` sees the restriction to `V`.** If two sections of
`𝒪_X` over an open `W` have the same image under `f.c.app (op W)`, and `f.c.app (op V)` is an
isomorphism for some `V ≤ W`, then the two sections already agree after restriction to `V`.

This is `AlgebraicGeometry.LocallyRingedSpace.restrict_eq_of_c_app_top_eq`
(`FormalSchemes.GlobalSectionsHomGlue`) with `⊤` replaced by an arbitrary `W`; the proof is
unchanged, being naturality of `f.c` along `V ≤ W` followed by cancelling the isomorphism. It is
*not* injectivity of `f.c.app (op W)`, which is false — one chart does not see all of `W`. -/
theorem restrict_eq_of_c_app_eq {Y X : LocallyRingedSpace.{u}} (f : Y ⟶ X) {W : Opens X}
    (V : Opens X) (hVW : V ≤ W) (hV : IsIso (f.c.app (op V)))
    (s t : X.presheaf.obj (op W))
    (h : (f.c.app (op W)).hom s = (f.c.app (op W)).hom t) :
    (X.presheaf.map (homOfLE hVW).op).hom s = (X.presheaf.map (homOfLE hVW).op).hom t := by
  have hnat := f.c.naturality (homOfLE hVW).op
  -- Naturality of `f.c` along `V ≤ W`, read on elements; the composite-morphism spelling is
  -- definitional, but `simp` will not reach it.
  have key : ∀ u : X.presheaf.obj (op W),
      (f.c.app (op V)).hom ((X.presheaf.map (homOfLE hVW).op).hom u) =
        ((f.base _* Y.presheaf).map (homOfLE hVW).op).hom ((f.c.app (op W)).hom u) := fun u =>
    congrArg (fun φ : X.presheaf.obj (op W) ⟶ _ => φ.hom u) hnat
  have := hV
  apply ConcreteCategory.injective_of_mono_of_preservesPullback (f.c.app (op V))
  rw [key, key, h]

end AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion

/-- **Meeting an open with the range of an open immersion is the image of its preimage.** The
rewrite that puts `W ⊓ (range f)` into the shape `PresheafedSpace.IsOpenImmersion.c_iso'` wants.

`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.opensFunctor` is an `abbrev` for
`H.base_open.functor`, so Mathlib's `TopologicalSpace.Opens.functor_obj_map_obj` applies on the
nose; only the order of the meet differs. -/
theorem inf_opensFunctor_top {X Y : PresheafedSpace.{u} CommRingCat.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (W : Opens Y) :
    W ⊓ (opensFunctor f).obj ⊤ = (opensFunctor f).obj ((Opens.map f.base).obj W) :=
  ((TopologicalSpace.Opens.functor_obj_map_obj _ W).trans (inf_comm _ _)).symm

end AlgebraicGeometry.PresheafedSpace.IsOpenImmersion

namespace AlgebraicGeometry.FormalScheme

open PresheafedSpace.IsOpenImmersion in
/-- **Sections of a glued formal scheme over an arbitrary open are determined patch by patch.** Two
sections of `𝒪_X` over `W` whose pullbacks along every patch inclusion `D.ι i` agree are equal.

The `⊤` case is `AlgebraicGeometry.FormalScheme.OpenCover.eq_of_chart_c_app_eq`
(`FormalSchemes.GlobalSectionsHomGlue`); this is the same argument with
`AlgebraicGeometry.FormalScheme.GlueData.ι_jointly_surjective` in place of
`OpenCover.exists_preimage`, run at a general `W`. `TopCat.Presheaf.IsSheaf.section_ext`'s covering
hypothesis is pointwise, so no `iSup`-form restatement of the cover is needed; the open produced
at a point is `W ⊓ (range of the patch through it)`, and
`PresheafedSpace.IsOpenImmersion.c_iso'` makes the `c`-component there an isomorphism.

This is the separation half of the sheaf axiom only. It says nothing about which patch-wise
families of sections glue — that is the existence half, and it is not proved here. -/
theorem GlueData.eq_of_ι_c_app_eq (D : FormalScheme.GlueData.{u})
    (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (s t : (D.gluedFormalScheme).presheaf.obj (op W))
    (h : ∀ i, ((D.ι i).c.app (op W)).hom s = ((D.ι i).c.app (op W)).hom t) :
    s = t := by
  refine (D.gluedFormalScheme).toSheafedSpace.IsSheaf.section_ext (U := op W) ?_
  intro x hx
  obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
  have hiso : IsIso ((D.ι i).c.app (op (W ⊓ (opensFunctor (D.ι i).toHom).obj ⊤))) :=
    c_iso' (D.ι i).toHom _ (inf_opensFunctor_top (D.ι i).toHom W)
  exact ⟨W ⊓ (opensFunctor (D.ι i).toHom).obj ⊤, inf_le_left, ⟨hx, y, trivial, rfl⟩,
    LocallyRingedSpace.restrict_eq_of_c_app_eq (D.ι i) _ inf_le_left hiso s t (h i)⟩

end AlgebraicGeometry.FormalScheme
